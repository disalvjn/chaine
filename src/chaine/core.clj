(ns chaine.core
  (:require [clojure.core.match :refer [match]]
            [clojure.walk :as walk]
            [clojure.pprint :as pprint]
            [clojure.set :as set]
            [clojure.algo.generic.functor :refer [fmap]]))

(defn has-pending-message?
  [port]
  (not-empty @(:queue port)))

(defn spy [x] (pprint/pprint x) x)
(defn reply
  ([p]
   (deliver p nil))
  ([p v]
   (deliver p v)))

(defn pop!
  [ref-stack]
  (dosync
   (let [top (first @ref-stack)]
     (alter ref-stack rest)
     top)))

(defn reset-states!
  [port]
  (dosync
   (let [ports (conj (vals @(:relatives port)) port)]
     (if (has-pending-message? port)
       (doseq [p ports]
         (alter (:state p) conj (:id port)))
       (doseq [p ports]
         (alter (:state p) disj (:id port)))))))

(defn add-message!
  [port message]
  (dosync
   (alter (:queue port) conj message)
   (reset-states! port)))

(defn fire!
  [port]
  (let [go! (ref (fn []))]
    (dosync
     (when-let [{:keys [order action]}
                (get @(:state->action port) @(:state port))]
       (let [involved (assoc @(:relatives port) (:id port) port)]
         (let [port-id->message (fmap (comp pop! :queue) involved)
               ordered-messages (mapv port-id->message order)
               arguments (into (mapv :contents ordered-messages)
                               (mapv :response ordered-messages))]
           (doseq [p (vals involved)]
             (reset-states! p)
             (let [parent-molecule (:molecule p)
                   msg-id->ports @(:msg-id->ports parent-molecule)
                   msg (port-id->message (:id p))
                   ports-containing-msg (msg-id->ports (:id msg))]
               (doseq [q ports-containing-msg]
                 (alter (:queue q) (partial remove #(= (:id %) (:id msg))))
                 (reset-states! q))))
           (ref-set go! #(apply action arguments))))))
    (@go!)))

(defn inject
  [& messages]
  (future
    (let [updated-ports (ref #{})]
      (dosync
       (doseq [{:keys [molecule contents] :as message} messages]
         (let [message->ports @(:message->ports molecule)]
           (when-let [ports (message->ports contents)]
             (alter (:msg-id->ports molecule)
                    assoc (:id message) ports)
             (alter updated-ports set/union ports)
             (doseq [port ports]
               (add-message! port message)
               (alter updated-ports set/union (vals @(:relatives port))))))))
      (doseq [port @updated-ports]
        (future (fire! port))))))



(defn message
  [molecule & contents]
  ;; get a :type so we can &, maybe?
  {:molecule molecule
   :contents (vec contents)
   :id (java.util.UUID/randomUUID)
   :response (promise)
   :synchronous (ref false)})

(defrecord Molecule [norm-pat->port msg-id->ports message->ports id]
  clojure.lang.IFn
  ;; only for asynchronous ones... gotta do some dispatching eventually
  (invoke [this] (message this))
  (invoke [this a] (message this a))
  (invoke [this a b] (message this a b))
  (invoke [this a b c] (message this a b c))
  (invoke [this a b c d] (message this a b c d))
  (invoke [this a b c d e] (message this a b c d e))
  (invoke [this a b c d e f] (message this a b c d e f))
  (invoke [this a b c d e f g] (message this a b c d e f g))
  (invoke [this a b c d e f g h] (message this a b c d e f g h))
  (invoke [this a b c d e f g h i] (message this a b c d e f g h i))
  (applyTo [this args] (apply message this args)))

(defn molecule
  []
  (Molecule. (ref {}) (ref {}) (ref {}) (java.util.UUID/randomUUID)))

(defn molecules
  [n]
  (mapv (fn [_] (molecule)) (range 0 n)))

;; todo: guards
(defn normalize-pattern
  [pat]
  (let [count (atom 0)
        replacements (atom {})]
    (walk/postwalk #(if (and (symbol? %) (not= % '&))
                      (if-let [replacement (@replacements %)]
                        replacement
                        (let [replacement
                              (symbol (str "s_" (swap! count inc)))]
                          (swap! replacements assoc % replacement)
                          replacement))
                      %)
                   pat)))

(defn port
  [molecule]
  {:queue (ref [])  ;; just for prototyping I promise
   :state (ref #{}) ;; set of port IDs
   :id (java.util.UUID/randomUUID)
   :state->action (ref {})
   :relatives (ref {}) ;; id -> port
   :molecule molecule})

(defn link-ports!
  [p q]
  (dosync
   (alter (:relatives p) assoc (:id q) q)
   (alter (:relatives q) assoc (:id p) p)
   (when (has-pending-message? p)
     (alter (:state q) conj (:id p)))
   (when (has-pending-message? q)
     (alter (:state p) conj (:id q)))))

(defn pairs
  [[x & xs :as list]]
  (if list
    (concat (map (partial vector x) xs)
            (pairs xs))))

(defn build-matcher
  [patterns]
  (let [content (gensym "content")
        matched (gensym "patterns")]
    `(fn [~content]
       (let [~matched (atom [])]
         ~@(for [pat patterns]
             `(match ~content
                ~pat (swap! ~matched conj (quote ~pat))
                ~(quote _) nil))
         (deref ~matched)))))

(defn build-message->ports
  [norm-pat->port]
  (let [matcher (build-matcher (keys norm-pat->port))
        ;; "you [Joe] like LISPs because you like to do filthy things"
        ;; -- ojw
        matcher-fn (eval matcher)]
    (fn [content]
      (->> (matcher-fn content)
           (mapv norm-pat->port)))))

(defn add-port!
  [molecule normalized-pattern]
  (let [p (port molecule)]
    (dosync
     (alter (:norm-pat->port molecule) assoc normalized-pattern p)
     (ref-set (:message->ports molecule) (build-message->ports
                                          @(:norm-pat->port molecule))))
    p))

(defn resolve-ports
  [molecule-pattern-pairs]
  (dosync
   (mapv (fn [[mol pat]]
           (let [normalized-pattern (normalize-pattern pat)]
             (or (get @(:norm-pat->port mol)
                      normalized-pattern)
               (add-port! mol normalized-pattern))))
         molecule-pattern-pairs)))

(defn effect->action
  [patterns effect]
  (let [fn-args (mapv (fn [_] (gensym)) patterns)
        msg-args (mapv (fn [_] (gensym)) patterns)
        match-wrapped
        (loop [[p & ps :as patterns] patterns
               [arg & args] fn-args
               effect `(~effect ~@msg-args)]
          (if (empty? patterns)
            effect
            (recur ps args
                   `(match ~arg
                      ~p ~effect
                      ~(quote [_]) (throw (Exception. "AAAAAAHHHHH"))))))]
    `(fn ~(into fn-args msg-args) ~match-wrapped)))

(defn create-reaction
  [molecule-pattern-pairs effect action]
  (dosync
   (let [ports (resolve-ports molecule-pattern-pairs)
         reaction-fire-ids (mapv :id ports)
         reaction-fire-state (set reaction-fire-ids)]
     (doseq [[p q] (pairs ports)]
       (link-ports! p q))
     (doseq [p ports]
       (alter (:state->action p)
              assoc reaction-fire-state {:order reaction-fire-ids
                                         :action action})))))

(defn untangle-cause-and-effect
  [cause effect]
  ;; cause is like [(<molecule> <pattern>*)*]
  (let [molecules (mapv first cause)
        patterns (mapv (comp vec rest) cause)
        molecule-pattern-pairs
        (mapv (fn [mol pats] [mol `(quote ~(vec pats))])
              molecules patterns)
        action (effect->action patterns effect)]
    `(create-reaction
      ~molecule-pattern-pairs
      (quote ~effect)
      ~action)))

(defmacro |>
  [& causes-and-effects]
  `(do ~@(map (partial apply untangle-cause-and-effect)
              (partition 2 causes-and-effects))))

(defmacro reaction
  [& body]
  `(fn [& _#] ~@body))

(defn dining-philosophers
  [n]
  (let [philosophers (molecules n)
        chopsticks (molecules n)]
    (dotimes [i n]
      (let [phil (get philosophers i)
            lchop (get chopsticks i)
            rchop (get chopsticks (mod (inc i) n))]

        (|> [(phil name :hungry) (lchop) (rchop)]
            (reaction
             (println "Philosopher" name "picks up the sticks and eats.")
             (Thread/sleep (rand 1000))
             (println "Philosopher" name "puts down the chopsticks.")
             (inject (lchop) (rchop) (phil name :thinking)))

            [(phil name :thinking)]
            (reaction
             (println "Philosopher" name "is thinking.")
             (Thread/sleep (rand 1000))
             (inject (phil name :hungry))))))

    (let [phil-init (map (fn [phil i] (phil i :hungry))
                         philosophers (range))
          chop-init (map (fn [chop] (chop))
                         chopsticks)]
      (apply inject (concat phil-init chop-init)))))

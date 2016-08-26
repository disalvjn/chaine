(ns chaine.core
  (:require [clojure.core.match :refer [match]]
            [clojure.walk :as walk]
            [clojure.pprint :as pprint]
            [clojure.set :as set]
            [clojure.algo.generic.functor :refer [fmap]]))


(defn pairs
  [[x & xs :as list]]
  (if list
    (concat (map (partial vector x) xs)
            (pairs xs))))

(defn index
  [kf vf coll]
  (zipmap (mapv kf coll) (mapv vf coll)))

;; fire! loop
;; change "queue" data structure

(defn has-pending-message?
  [port]
  (not-empty @(:queue port)))

(defn spy [x] (pprint/pprint x) x)

(def ^:dynamic *molecule-id->message-response*)
(defn reply
  ([molecule]
   (reply molecule nil))
  ([molecule v]
   (let [result (-> molecule :id *molecule-id->message-response*)]
     (deliver result v))))

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
               molecule-id->message-response
               (index (comp :id :molecule) :response ordered-messages)
               arguments (mapv :contents ordered-messages)]
           (doseq [p (vals involved)]
             (reset-states! p)
             (let [parent-molecule (:molecule p)
                   msg-id->ports @(:msg-id->ports parent-molecule)
                   msg (port-id->message (:id p))
                   ports-containing-msg (msg-id->ports (:id msg))]
               (doseq [q ports-containing-msg]
                 (alter (:queue q) (partial remove #(= (:id %) (:id msg))))
                 (reset-states! q))))
           (ref-set go! #(binding [*molecule-id->message-response*
                                   molecule-id->message-response]
                           (apply action arguments)))))))
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



(defn apply-molecule
  [molecule & contents]
  (let [async-message {:molecule molecule
                       :contents (vec contents)
                       :id (java.util.UUID/randomUUID)}]
    (case (:synchronous? molecule)
      false async-message

      true (let [sync-message (assoc async-message :response (promise))]
             (inject sync-message)
             @(:response sync-message)))))

(defrecord Molecule
    [norm-pat->port msg-id->ports message->ports synchronous? id]
  clojure.lang.IFn
  (invoke [this] (apply-molecule this))
  (invoke [this a] (apply-molecule this a))
  (invoke [this a b] (apply-molecule this a b))
  (invoke [this a b c] (apply-molecule this a b c))
  (invoke [this a b c d] (apply-molecule this a b c d))
  (invoke [this a b c d e] (apply-molecule this a b c d e))
  (invoke [this a b c d e f] (apply-molecule this a b c d e f))
  (invoke [this a b c d e f g] (apply-molecule this a b c d e f g))
  (invoke [this a b c d e f g h] (apply-molecule this a b c d e f g h))
  (invoke [this a b c d e f g h i] (apply-molecule this a b c d e f g h i))
  (applyTo [this args] (apply apply-molecule this args)))

(defn molecule
  []
  (Molecule. (ref {}) (ref {}) (ref {}) false (java.util.UUID/randomUUID)))

(defn synchronous-molecule
  []
  (assoc (molecule) :synchronous? true))

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

(defn create-reaction
  [molecule-pattern-pairs action]
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

(defn gensyms [n] (mapv (fn [_] (gensym)) (range 0 n)))
(defn effect->action
  [patterns effect]
  (let [fn-args (gensyms (count patterns))
        match-wrapped
        (loop [[p & ps :as patterns] patterns
               [arg & args] fn-args
               effect effect]
          (if (empty? patterns)
            effect
            (recur ps args
                   `(match ~arg
                      ~p ~effect
                      ~(quote [_]) (throw (Exception. "AAAAAAHHHHH"))))))]
    `(fn ~fn-args ~match-wrapped)))

(defn untangle-cause-and-effect
  [cause effect]
  ;; cause is like [(<molecule> <pattern>*)*]
  (let [molecules (mapv first cause)
        patterns (mapv (comp vec rest) cause)
        molecule-pattern-pairs
        (mapv (fn [mol pats] [mol `(quote ~(vec pats))])
              molecules patterns)
        action (effect->action patterns effect)]
    ;; (pprint/pprint action)
    `(create-reaction
      ~molecule-pattern-pairs
      ~action)))

(defmacro reactions!
  [& causes-and-effects]
  `(do ~@(map (partial apply untangle-cause-and-effect)
              (partition 2 causes-and-effects))))

(defn make-concurrent-stack
  []
  (let [stack (molecule)
        pop (synchronous-molecule)
        push (synchronous-molecule)]
    (reactions!
     [(stack xs) (push x)]
     (do
       (inject (stack (conj xs x)))
       (reply push))

     [(stack ([x & xs] :seq)) (pop)]
     (do
       (inject (stack xs))
       (reply pop x)))

    (inject (stack (list)))
    {:pop pop :push push}))

(defn dining-philosophers
  [n]
  (let [philosophers (molecules n)
        chopsticks (molecules n)]
    (dotimes [i n]
      (let [phil (get philosophers i)
            lchop (get chopsticks i)
            rchop (get chopsticks (mod (inc i) n))]

        (reactions!
         [(phil name :hungry) (lchop) (rchop)]
         (do
           (println "Philosopher" name "picks up the sticks and eats.")
           (Thread/sleep (rand 1000))
           (println "Philosopher" name "puts down the chopsticks.")
           (inject (lchop) (rchop) (phil name :thinking)))

         [(phil name :thinking)]
         (do
           (println "Philosopher" name "is thinking.")
           (Thread/sleep (rand 1000))
           (inject (phil name :hungry))))))

    (let [phil-init (map (fn [phil i] (phil i :hungry))
                         philosophers (range))
          chop-init (map (fn [chop] (chop))
                         chopsticks)]
      (apply inject (concat phil-init chop-init)))))

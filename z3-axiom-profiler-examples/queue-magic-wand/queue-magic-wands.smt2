(get-info :version)
; (:version "4.4.0")
; Input file is C:\Users\scmalte\AppData\Local\Temp\queue-magic-wands.sil
; Started: 2015-11-17 10:34:07
; Silicon.buildVersion: 0.1-SNAPSHOT 6e6bffd1761c default 2015/11/17 10:31:11
; ------------------------------------------------------------
; Preamble start
; 
; ; /z3config.smt2
(set-option :print-success true) ; Boogie: false
(set-option :global-decls true) ; Boogie: default
(set-option :auto_config false) ; Usually a good idea
(set-option :smt.mbqi false)
(set-option :model.v2 true)
(set-option :smt.phase_selection 0)
(set-option :smt.restart_strategy 0)
(set-option :smt.restart_factor |1.5|)
(set-option :smt.arith.random_initial_value true)
(set-option :smt.case_split 3)
(set-option :smt.delay_units true)
(set-option :smt.delay_units_threshold 16)
(set-option :nnf.sk_hack true)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.qi.cost "(+ weight generation)")
(set-option :type_check true)
(set-option :smt.bv.reflect true)
; 
; ; /preamble.smt2
(declare-datatypes () ((
    $Snap ($Snap.unit)
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))
(declare-sort $Ref 0)
(declare-const $Ref.null $Ref)
(define-sort $Perm () Real)
(define-const $Perm.Write $Perm 1.0)
(define-const $Perm.No $Perm 0.0)
(define-fun $Perm.isValidVar ((p $Perm)) Bool
	(<= $Perm.No p))
(define-fun $Perm.isReadVar ((p $Perm) (ub $Perm)) Bool
    (and ($Perm.isValidVar p)
         (not (= p $Perm.No))
         (< p $Perm.Write)))
(define-fun $Perm.min ((p1 $Perm) (p2 $Perm)) Real
    (ite (<= p1 p2) p1 p2))
(define-fun $Math.min ((a Int) (b Int)) Int
    (ite (<= a b) a b))
(define-fun $Math.clip ((a Int)) Int
    (ite (< a 0) 0 a))
(push) ; 1
(declare-sort $Seq<$Ref>)
; /dafny_axioms/sequences_declarations_dafny.smt2 [Ref]
(declare-fun $Seq.length ($Seq<$Ref>) Int)
(declare-fun $Seq.empty<$Ref> () $Seq<$Ref>)
(declare-fun $Seq.singleton ($Ref) $Seq<$Ref>)
(declare-fun $Seq.build ($Seq<$Ref> $Ref) $Seq<$Ref>)
(declare-fun $Seq.index ($Seq<$Ref> Int) $Ref)
(declare-fun $Seq.append ($Seq<$Ref> $Seq<$Ref>) $Seq<$Ref>)
(declare-fun $Seq.update ($Seq<$Ref> Int $Ref) $Seq<$Ref>)
(declare-fun $Seq.contains ($Seq<$Ref> $Ref) Bool)
(declare-fun $Seq.take ($Seq<$Ref> Int) $Seq<$Ref>)
(declare-fun $Seq.drop ($Seq<$Ref> Int) $Seq<$Ref>)
(declare-fun $Seq.equal ($Seq<$Ref> $Seq<$Ref>) Bool)
(declare-fun $Seq.sameuntil ($Seq<$Ref> $Seq<$Ref> Int) Bool)
(assert true)
; /dafny_axioms/sequences_axioms_dafny.smt2 [Ref]
(assert (forall ((s $Seq<$Ref>) ) (! (<= 0 ($Seq.length s))
  :pattern ( ($Seq.length s))
  )))
(assert (= ($Seq.length $Seq.empty<$Ref>) 0))
(assert (forall ((s $Seq<$Ref>) ) (! (=> (= ($Seq.length s) 0) (= s $Seq.empty<$Ref>))
  :pattern ( ($Seq.length s))
  )))
(assert (forall ((t $Ref) ) (! (= ($Seq.length ($Seq.singleton t)) 1)
  :pattern ( ($Seq.length ($Seq.singleton t)))
  )))
(assert (forall ((s $Seq<$Ref>) (v $Ref) ) (! (= ($Seq.length ($Seq.build s v)) (+ 1 ($Seq.length s)))
  :pattern ( ($Seq.length ($Seq.build s v)))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) ) (! (and
  (=> (= i ($Seq.length s)) (= ($Seq.index ($Seq.build s v) i) v))
  (=> (not (= i ($Seq.length s))) (= ($Seq.index ($Seq.build s v) i) ($Seq.index s i))))
  :pattern ( ($Seq.index ($Seq.build s v) i))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) ) (! (= ($Seq.length ($Seq.append s0 s1)) (+ ($Seq.length s0) ($Seq.length s1)))
  :pattern ( ($Seq.length ($Seq.append s0 s1)))
  )))
(assert (forall ((t $Ref) ) (! (= ($Seq.index ($Seq.singleton t) 0) t)
  :pattern ( ($Seq.index ($Seq.singleton t) 0))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) (n Int) ) (! (and
  (=> (< n ($Seq.length s0)) (= ($Seq.index ($Seq.append s0 s1) n) ($Seq.index s0 n)))
  (=> (<= ($Seq.length s0) n) (= ($Seq.index ($Seq.append s0 s1) n) ($Seq.index s1 (- n ($Seq.length s0))))))
  :pattern ( ($Seq.index ($Seq.append s0 s1) n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) ) (! (=> (and
  (<= 0 i)
  (< i ($Seq.length s))) (= ($Seq.length ($Seq.update s i v)) ($Seq.length s)))
  :pattern ( ($Seq.length ($Seq.update s i v)))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 n)
  (< n ($Seq.length s))) (and
  (=> (= i n) (= ($Seq.index ($Seq.update s i v) n) v))
  (=> (not (= i n)) (= ($Seq.index ($Seq.update s i v) n) ($Seq.index s n)))))
  :pattern ( ($Seq.index ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (x $Ref) ) (!
  (and
    (=>
      ($Seq.contains s x)
      (exists ((i Int) ) (!
        (and
  (<= 0 i)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
  )))
    (=>
      (exists ((i Int) ) (!
        (and
  (<= 0 i)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
      ))
      ($Seq.contains s x)))
  :pattern ( ($Seq.contains s x))
  )))
(assert (forall ((x $Ref) ) (! (not ($Seq.contains $Seq.empty<$Ref> x))
  :pattern ( ($Seq.contains $Seq.empty<$Ref> x))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) (x $Ref) ) (! (and
  (=> ($Seq.contains ($Seq.append s0 s1) x) (or
  ($Seq.contains s0 x)
  ($Seq.contains s1 x)))
  (=> (or
  ($Seq.contains s0 x)
  ($Seq.contains s1 x)) ($Seq.contains ($Seq.append s0 s1) x)))
  :pattern ( ($Seq.contains ($Seq.append s0 s1) x))
  )))
(assert (forall ((s $Seq<$Ref>) (v $Ref) (x $Ref) ) (! (and
  (=> ($Seq.contains ($Seq.build s v) x) (or
  (= v x)
  ($Seq.contains s x)))
  (=> (or
  (= v x)
  ($Seq.contains s x)) ($Seq.contains ($Seq.build s v) x)))
  :pattern ( ($Seq.contains ($Seq.build s v) x))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (x $Ref) ) (!
  (and
    (=>
      ($Seq.contains ($Seq.take s n) x)
      (exists ((i Int) ) (!
        (and
  (<= 0 i)
  (< i n)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
  )))
    (=>
      (exists ((i Int) ) (!
        (and
  (<= 0 i)
  (< i n)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
      ))
      ($Seq.contains ($Seq.take s n) x)))
  :pattern ( ($Seq.contains ($Seq.take s n) x))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (x $Ref) ) (!
  (and
    (=>
      ($Seq.contains ($Seq.drop s n) x)
      (exists ((i Int) ) (!
        (and
  (<= 0 n)
  (<= n i)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
  )))
    (=>
      (exists ((i Int) ) (!
        (and
  (<= 0 n)
  (<= n i)
  (< i ($Seq.length s))
  (= ($Seq.index s i) x))
  :pattern ( ($Seq.index s i))
      ))
      ($Seq.contains ($Seq.drop s n) x)))
  :pattern ( ($Seq.contains ($Seq.drop s n) x))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) ) (! (and
  (=> ($Seq.equal s0 s1) (and
  (= ($Seq.length s0) ($Seq.length s1))
  (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j ($Seq.length s0))) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  ))))
  (=> (and
  (= ($Seq.length s0) ($Seq.length s1))
  (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j ($Seq.length s0))) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  ))) ($Seq.equal s0 s1)))
  :pattern ( ($Seq.equal s0 s1))
  )))
(assert (forall ((a $Seq<$Ref>) (b $Seq<$Ref>) ) (! (=> ($Seq.equal a b) (= a b))
  :pattern ( ($Seq.equal a b))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) (n Int) ) (! (and
  (=> ($Seq.sameuntil s0 s1 n) (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j n)) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  )))
  (=> (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j n)) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  )) ($Seq.sameuntil s0 s1 n)))
  :pattern ( ($Seq.sameuntil s0 s1 n))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) ) (! (=> (<= 0 n) (and
  (=> (<= n ($Seq.length s)) (= ($Seq.length ($Seq.take s n)) n))
  (=> (< ($Seq.length s) n) (= ($Seq.length ($Seq.take s n)) ($Seq.length s)))))
  :pattern ( ($Seq.length ($Seq.take s n)))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (j Int) ) (! (=> (and
  (<= 0 j)
  (< j n)
  (< j ($Seq.length s))) (= ($Seq.index ($Seq.take s n) j) ($Seq.index s j)))
  :pattern ( ($Seq.index ($Seq.take s n) j))
  :pattern (($Seq.index s j) ($Seq.take s n)) ; [XXX] Added 29-10-2015
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) ) (! (=> (<= 0 n) (and
  (=> (<= n ($Seq.length s)) (= ($Seq.length ($Seq.drop s n)) (- ($Seq.length s) n)))
  (=> (< ($Seq.length s) n) (= ($Seq.length ($Seq.drop s n)) 0))))
  :pattern ( ($Seq.length ($Seq.drop s n)))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (j Int) ) (! (=> (and
  (<= 0 n)
  (<= 0 j)
  (< j (- ($Seq.length s) n))) (= ($Seq.index ($Seq.drop s n) j) ($Seq.index s (+ j n))))
  :pattern ( ($Seq.index ($Seq.drop s n) j))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (k Int) ) (! ; [XXX] Added 29-10-2015
  (=>
    (and
      (<= 0 n)
      (<= n k)
      (< k ($Seq.length s)))
    (=
      ($Seq.index ($Seq.drop s n) (- k n))
      ($Seq.index s k)))
  :pattern (($Seq.index s k) ($Seq.drop s n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 i)
  (< i n)
  (<= n ($Seq.length s))) (= ($Seq.take ($Seq.update s i v) n) ($Seq.update ($Seq.take s n) i v)))
  :pattern ( ($Seq.take ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= n i)
  (< i ($Seq.length s))) (= ($Seq.take ($Seq.update s i v) n) ($Seq.take s n)))
  :pattern ( ($Seq.take ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 n)
  (<= n i)
  (< i ($Seq.length s))) (= ($Seq.drop ($Seq.update s i v) n) ($Seq.update ($Seq.drop s n) (- i n) v)))
  :pattern ( ($Seq.drop ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 i)
  (< i n)
  (< n ($Seq.length s))) (= ($Seq.drop ($Seq.update s i v) n) ($Seq.drop s n)))
  :pattern ( ($Seq.drop ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 n)
  (<= n ($Seq.length s))) (= ($Seq.drop ($Seq.build s v) n) ($Seq.build ($Seq.drop s n) v)))
  :pattern ( ($Seq.drop ($Seq.build s v) n))
  )))
(assert (forall ((x $Ref) (y $Ref)) (!
  (iff
    ($Seq.contains ($Seq.singleton x) y)
    (= x y))
  :pattern (($Seq.contains ($Seq.singleton x) y))
  )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$PermTo$Snap ($Perm) $Snap)
(declare-fun $SortWrappers.$SnapTo$Perm ($Snap) $Perm)
(assert (forall ((x $Perm)) (!
    (= x ($SortWrappers.$SnapTo$Perm($SortWrappers.$PermTo$Snap x)))
    :pattern (($SortWrappers.$PermTo$Snap x))
    :qid |$Snap.$Perm|
    )))
(declare-fun $SortWrappers.$RefTo$Snap ($Ref) $Snap)
(declare-fun $SortWrappers.$SnapTo$Ref ($Snap) $Ref)
(assert (forall ((x $Ref)) (!
    (= x ($SortWrappers.$SnapTo$Ref($SortWrappers.$RefTo$Snap x)))
    :pattern (($SortWrappers.$RefTo$Snap x))
    :qid |$Snap.$Ref|
    )))
(declare-fun $SortWrappers.BoolTo$Snap (Bool) $Snap)
(declare-fun $SortWrappers.$SnapToBool ($Snap) Bool)
(assert (forall ((x Bool)) (!
    (= x ($SortWrappers.$SnapToBool($SortWrappers.BoolTo$Snap x)))
    :pattern (($SortWrappers.BoolTo$Snap x))
    :qid |$Snap.Bool|
    )))
(declare-fun $SortWrappers.IntTo$Snap (Int) $Snap)
(declare-fun $SortWrappers.$SnapToInt ($Snap) Int)
(assert (forall ((x Int)) (!
    (= x ($SortWrappers.$SnapToInt($SortWrappers.IntTo$Snap x)))
    :pattern (($SortWrappers.IntTo$Snap x))
    :qid |$Snap.Int|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$Seq<$Ref>To$Snap ($Seq<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Seq<$Ref> ($Snap) $Seq<$Ref>)
(assert (forall ((x $Seq<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$Seq<$Ref>($SortWrappers.$Seq<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$Seq<$Ref>To$Snap x))
    :qid |$Snap.$Seq<$Ref>|
    )))
; Preamble end
; ------------------------------------------------------------
(declare-const xs@1 $Ref)
(declare-const this@2 $Ref)
(declare-const xs@3 $Ref)
(declare-const xs@4 $Ref)
(declare-const xs@5 $Ref)
(declare-const xs@6 $Ref)
(declare-const xs@7 $Ref)
(declare-const i@8 Int)
; ------------------------------------------------------------
; Declaring program functions
(declare-const s@$ $Snap)
(declare-fun $nodesLength ($Snap $Ref) Int)
(declare-fun $nodesLength$ ($Snap $Ref) Int)
(declare-fun $prio ($Snap $Ref) Int)
(declare-fun $prio$ ($Snap $Ref) Int)
(declare-fun $length ($Snap $Ref) Int)
(declare-fun $length$ ($Snap $Ref) Int)
(declare-fun $nodesContent ($Snap $Ref) $Seq<$Ref>)
(declare-fun $nodesContent$ ($Snap $Ref) $Seq<$Ref>)
(declare-fun $content ($Snap $Ref) $Seq<$Ref>)
(declare-fun $content$ ($Snap $Ref) $Seq<$Ref>)
(declare-fun $peek ($Snap $Ref) $Ref)
(declare-fun $peek$ ($Snap $Ref) $Ref)
(declare-fun $itemAt ($Snap $Ref Int) $Ref)
(declare-fun $itemAt$ ($Snap $Ref Int) $Ref)
; ---------- FUNCTION nodesLength (specs well-defined) ----------
(declare-const result@9 Int)
(push) ; 2
; [eval] result > 0
(pop) ; 2
(assert (forall ((s@$ $Snap) (xs@1 $Ref)) (!
  (= ($nodesLength$ s@$ xs@1) ($nodesLength s@$ xs@1))
  :pattern (($nodesLength s@$ xs@1))
  )))
(assert (forall ((s@$ $Snap) (xs@1 $Ref)) (!
  (> ($nodesLength$ s@$ xs@1) 0)
  :pattern (($nodesLength$ s@$ xs@1))
  )))
; ---------- FUNCTION nodesLength----------
(declare-const result@10 Int)
(push) ; 2
; [eval] 1 + (unfolding acc(PQueue(xs), write) in (xs.next == null ? 0 : nodesLength(xs.next)))
; [eval] (unfolding acc(PQueue(xs), write) in (xs.next == null ? 0 : nodesLength(xs.next)))
(push) ; 3
(assert (not (= xs@1 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (not (= xs@1 $Ref.null)))
(push) ; 3
(assert (not (= xs@1 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
; [eval] xs.next != null
(set-option :timeout 250)
(push) ; 3
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
(assert (not (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
; [then-branch 1] First(Second(s@$)) != Null
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)))
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 4
(push) ; 5
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 2] First(Second(s@$)) != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 5
; [dead else-branch 2] First(Second(s@$)) == Null
(pop) ; 4
(assert (implies
  (not
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
  (<=
    ($prio $Snap.unit ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)))
    ($prio $Snap.unit ($Seq.index
      ($nodesContent ($Snap.first ($Snap.second ($Snap.second s@$))) ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))))
      0)))))
; [eval] (xs.next == null ? 0 : nodesLength(xs.next))
; [eval] xs.next == null
; [dead then-branch 3] First(Second(s@$)) == Null
(push) ; 4
; [else-branch 3] First(Second(s@$)) != Null
; [eval] nodesLength(xs.next)
(pop) ; 4
(declare-const $deadThen@11 Int)
(pop) ; 3
(push) ; 3
; [else-branch 1] First(Second(s@$)) == Null
(assert (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 4
; [dead then-branch 4] First(Second(s@$)) != Null
(push) ; 5
; [else-branch 4] First(Second(s@$)) == Null
(pop) ; 5
(pop) ; 4
; [eval] (xs.next == null ? 0 : nodesLength(xs.next))
; [eval] xs.next == null
(push) ; 4
(assert (not (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 5] First(Second(s@$)) == Null
(pop) ; 4
; [dead else-branch 5] First(Second(s@$)) != Null
(declare-const $deadElse@12 Int)
(pop) ; 3
(declare-fun joinedIn@13 () Int)
(assert (implies
  (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)
  (and
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)
    (not (= xs@1 $Ref.null)))))
(assert (implies
  (not
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
  (and
    (implies
      (not
        (=
          ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$)))
          $Ref.null))
      (<=
        ($prio $Snap.unit ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)))
        ($prio $Snap.unit ($Seq.index
          ($nodesContent ($Snap.first ($Snap.second ($Snap.second s@$))) ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))))
          0))))
    (not
      (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
    (not (= xs@1 $Ref.null)))))
(assert (and
  (implies
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)
    (=
      joinedIn@13
      (ite
        (=
          ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$)))
          $Ref.null)
        0
        $deadElse@12)))
  (implies
    (not
      (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
    (=
      joinedIn@13
      (ite
        (=
          ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$)))
          $Ref.null)
        $deadThen@11
        ($nodesLength ($Snap.first ($Snap.second ($Snap.second s@$))) ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$)))))))))
; [eval] result > 0
(set-option :timeout 0)
(push) ; 3
(assert (not (> (+ 1 joinedIn@13) 0)))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (> (+ 1 joinedIn@13) 0))
(pop) ; 2
(assert (forall ((s@$ $Snap) (xs@1 $Ref)) (!
  (=
    ($nodesLength s@$ xs@1)
    (+
      1
      (ite
        (=
          ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$)))
          $Ref.null)
        0
        ($nodesLength$ ($Snap.first ($Snap.second ($Snap.second s@$))) ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$)))))))
  :pattern (($nodesLength s@$ xs@1))
  )))
; ---------- FUNCTION prio (specs well-defined) ----------
(declare-const result@14 Int)
(push) ; 2
(pop) ; 2
(assert (forall ((s@$ $Snap) (this@2 $Ref)) (!
  (= ($prio$ s@$ this@2) ($prio s@$ this@2))
  :pattern (($prio s@$ this@2))
  )))
(assert true)
; ---------- FUNCTION prio----------
(declare-const result@15 Int)
(push) ; 2
(pop) ; 2
; ---------- FUNCTION length (specs well-defined) ----------
(declare-const result@16 Int)
(push) ; 2
; [eval] result >= 0
(pop) ; 2
(assert (forall ((s@$ $Snap) (xs@3 $Ref)) (!
  (= ($length$ s@$ xs@3) ($length s@$ xs@3))
  :pattern (($length s@$ xs@3))
  )))
(assert (forall ((s@$ $Snap) (xs@3 $Ref)) (!
  (>= ($length$ s@$ xs@3) 0)
  :pattern (($length$ s@$ xs@3))
  )))
; ---------- FUNCTION length----------
(declare-const result@17 Int)
(push) ; 2
; [eval] (unfolding acc(List(xs), write) in (xs.head == null ? 0 : nodesLength(xs.head)))
(push) ; 3
(assert (not (= xs@3 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (not (= xs@3 $Ref.null)))
; [eval] xs.head != null
(set-option :timeout 250)
(push) ; 3
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
(assert (not (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null))))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
; [then-branch 6] First(s@$) != Null
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)))
; [eval] (xs.head == null ? 0 : nodesLength(xs.head))
; [eval] xs.head == null
; [dead then-branch 7] First(s@$) == Null
(push) ; 4
; [else-branch 7] First(s@$) != Null
; [eval] nodesLength(xs.head)
(pop) ; 4
(declare-const $deadThen@18 Int)
(pop) ; 3
(push) ; 3
; [else-branch 6] First(s@$) == Null
(assert (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null))
; [eval] (xs.head == null ? 0 : nodesLength(xs.head))
; [eval] xs.head == null
(push) ; 4
(assert (not (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 8] First(s@$) == Null
(pop) ; 4
; [dead else-branch 8] First(s@$) != Null
(declare-const $deadElse@19 Int)
(pop) ; 3
(declare-fun joinedIn@20 () Int)
(assert (implies
  (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)
  (and
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)
    (not (= xs@3 $Ref.null)))))
(assert (implies
  (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null))
  (and
    (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null))
    (not (= xs@3 $Ref.null)))))
(assert (and
  (implies
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)
    (=
      joinedIn@20
      (ite
        (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)
        0
        $deadElse@19)))
  (implies
    (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null))
    (=
      joinedIn@20
      (ite
        (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)
        $deadThen@18
        ($nodesLength ($Snap.second s@$) ($SortWrappers.$SnapTo$Ref ($Snap.first s@$))))))))
; [eval] result >= 0
(set-option :timeout 0)
(push) ; 3
(assert (not (>= joinedIn@20 0)))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (>= joinedIn@20 0))
(pop) ; 2
(assert (forall ((s@$ $Snap) (xs@3 $Ref)) (!
  (=
    ($length s@$ xs@3)
    (ite
      (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)
      0
      ($nodesLength ($Snap.second s@$) ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)))))
  :pattern (($length s@$ xs@3))
  )))
; ---------- FUNCTION nodesContent (specs well-defined) ----------
(declare-const result@21 $Seq<$Ref>)
(push) ; 2
; [eval] (forall i: Int, j: Int :: { prio(result[i]),prio(result[j]) } (0 <= i) && ((i < j) && (j < nodesLength(xs))) ==> (prio(result[i]) <= prio(result[j])))
(declare-const i@22 Int)
(declare-const j@23 Int)
(push) ; 3
; [eval] (0 <= i) && ((i < j) && (j < nodesLength(xs))) ==> (prio(result[i]) <= prio(result[j]))
; [eval] (0 <= i) && ((i < j) && (j < nodesLength(xs)))
; [eval] 0 <= i
(push) ; 4
(set-option :timeout 250)
(push) ; 5
(assert (not (not (<= 0 i@22))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= 0 i@22)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 9] 0 <= i@22
(assert (<= 0 i@22))
; [eval] (i < j) && (j < nodesLength(xs))
; [eval] i < j
(push) ; 6
(push) ; 7
(assert (not (not (< i@22 j@23))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (< i@22 j@23)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 10] i@22 < j@23
(assert (< i@22 j@23))
; [eval] j < nodesLength(xs)
; [eval] nodesLength(xs)
(pop) ; 7
(push) ; 7
; [else-branch 10] !i@22 < j@23
(assert (not (< i@22 j@23)))
(pop) ; 7
(pop) ; 6
(pop) ; 5
(push) ; 5
; [else-branch 9] !0 <= i@22
(assert (not (<= 0 i@22)))
(pop) ; 5
(pop) ; 4
(push) ; 4
(push) ; 5
(assert (not (not (and (<= 0 i@22) (and (< i@22 j@23) (< j@23 ($nodesLength s@$ xs@4)))))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (and (<= 0 i@22) (and (< i@22 j@23) (< j@23 ($nodesLength s@$ xs@4))))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 11] 0 <= i@22 && i@22 < j@23 && j@23 < nodesLength(xs@4;s@$)
(assert (and (<= 0 i@22) (and (< i@22 j@23) (< j@23 ($nodesLength s@$ xs@4)))))
; [eval] prio(result[i]) <= prio(result[j])
; [eval] prio(result[i])
; [eval] result[i]
; [eval] prio(result[j])
; [eval] result[j]
(pop) ; 5
(push) ; 5
; [else-branch 11] !0 <= i@22 && i@22 < j@23 && j@23 < nodesLength(xs@4;s@$)
(assert (not (and (<= 0 i@22) (and (< i@22 j@23) (< j@23 ($nodesLength s@$ xs@4))))))
(pop) ; 5
(pop) ; 4
(pop) ; 3
(pop) ; 2
(assert (forall ((s@$ $Snap) (xs@4 $Ref)) (!
  ($Seq.equal ($nodesContent$ s@$ xs@4) ($nodesContent s@$ xs@4))
  :pattern (($nodesContent s@$ xs@4))
  )))
(assert (forall ((s@$ $Snap) (xs@4 $Ref)) (!
  (forall (($i Int) ($j Int)) (!
    (implies
      (and (<= 0 $i) (and (< $i $j) (< $j ($nodesLength s@$ xs@4))))
      (<=
        ($prio $Snap.unit ($Seq.index ($nodesContent$ s@$ xs@4) $i))
        ($prio $Snap.unit ($Seq.index ($nodesContent$ s@$ xs@4) $j))))
    :pattern (($prio$ $Snap.unit ($Seq.index ($nodesContent$ s@$ xs@4) $i)) ($prio$ $Snap.unit ($Seq.index
      ($nodesContent$ s@$ xs@4)
      $j)))
    ))
  :pattern (($nodesContent$ s@$ xs@4))
  )))
; ---------- FUNCTION nodesContent----------
(declare-const result@24 $Seq<$Ref>)
(push) ; 2
; [eval] (unfolding acc(PQueue(xs), write) in Seq(xs.data) ++ (xs.next == null ? Seq[Ref]() : nodesContent(xs.next)))
(set-option :timeout 0)
(push) ; 3
(assert (not (= xs@4 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (not (= xs@4 $Ref.null)))
(push) ; 3
(assert (not (= xs@4 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
; [eval] xs.next != null
(set-option :timeout 250)
(push) ; 3
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
(assert (not (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
; [then-branch 12] First(Second(s@$)) != Null
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)))
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 4
(push) ; 5
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 13] First(Second(s@$)) != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 5
; [dead else-branch 13] First(Second(s@$)) == Null
(pop) ; 4
(assert (implies
  (not
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
  (<=
    ($prio $Snap.unit ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)))
    ($prio $Snap.unit ($Seq.index
      ($nodesContent ($Snap.first ($Snap.second ($Snap.second s@$))) ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))))
      0)))))
; [eval] Seq(xs.data) ++ (xs.next == null ? Seq[Ref]() : nodesContent(xs.next))
; [eval] Seq(xs.data)
(assert (=
  ($Seq.length ($Seq.singleton ($SortWrappers.$SnapTo$Ref ($Snap.first s@$))))
  1))
; [eval] (xs.next == null ? Seq[Ref]() : nodesContent(xs.next))
; [eval] xs.next == null
; [dead then-branch 14] First(Second(s@$)) == Null
(push) ; 4
; [else-branch 14] First(Second(s@$)) != Null
; [eval] nodesContent(xs.next)
(pop) ; 4
(declare-const $deadThen@25 $Seq<$Ref>)
(pop) ; 3
(push) ; 3
; [else-branch 12] First(Second(s@$)) == Null
(assert (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 4
; [dead then-branch 15] First(Second(s@$)) != Null
(push) ; 5
; [else-branch 15] First(Second(s@$)) == Null
(pop) ; 5
(pop) ; 4
; [eval] Seq(xs.data) ++ (xs.next == null ? Seq[Ref]() : nodesContent(xs.next))
; [eval] Seq(xs.data)
(assert (=
  ($Seq.length ($Seq.singleton ($SortWrappers.$SnapTo$Ref ($Snap.first s@$))))
  1))
; [eval] (xs.next == null ? Seq[Ref]() : nodesContent(xs.next))
; [eval] xs.next == null
(push) ; 4
(assert (not (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 16] First(Second(s@$)) == Null
; [eval] Seq[Ref]()
(pop) ; 4
; [dead else-branch 16] First(Second(s@$)) != Null
(declare-const $deadElse@26 $Seq<$Ref>)
(pop) ; 3
(declare-fun joinedIn@27 () $Seq<$Ref>)
(assert (implies
  (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)
  (and
    (=
      ($Seq.length
        ($Seq.singleton ($SortWrappers.$SnapTo$Ref ($Snap.first s@$))))
      1)
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)
    (not (= xs@4 $Ref.null)))))
(assert (implies
  (not
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
  (and
    (=
      ($Seq.length
        ($Seq.singleton ($SortWrappers.$SnapTo$Ref ($Snap.first s@$))))
      1)
    (implies
      (not
        (=
          ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$)))
          $Ref.null))
      (<=
        ($prio $Snap.unit ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)))
        ($prio $Snap.unit ($Seq.index
          ($nodesContent ($Snap.first ($Snap.second ($Snap.second s@$))) ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))))
          0))))
    (not
      (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
    (not (= xs@4 $Ref.null)))))
(assert (and
  (implies
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)
    ($Seq.equal
      joinedIn@27
      ($Seq.append
        ($Seq.singleton ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)))
        (ite
          (=
            ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$)))
            $Ref.null)
          $Seq.empty<$Ref>
          $deadElse@26))))
  (implies
    (not
      (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
    ($Seq.equal
      joinedIn@27
      ($Seq.append
        ($Seq.singleton ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)))
        (ite
          (=
            ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$)))
            $Ref.null)
          $deadThen@25
          ($nodesContent ($Snap.first ($Snap.second ($Snap.second s@$))) ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))))))))))
; [eval] (forall i: Int, j: Int :: { prio(result[i]),prio(result[j]) } (0 <= i) && ((i < j) && (j < nodesLength(xs))) ==> (prio(result[i]) <= prio(result[j])))
(declare-const i@28 Int)
(declare-const j@29 Int)
(push) ; 3
; [eval] (0 <= i) && ((i < j) && (j < nodesLength(xs))) ==> (prio(result[i]) <= prio(result[j]))
; [eval] (0 <= i) && ((i < j) && (j < nodesLength(xs)))
; [eval] 0 <= i
(push) ; 4
(push) ; 5
(assert (not (not (<= 0 i@28))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= 0 i@28)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 17] 0 <= i@28
(assert (<= 0 i@28))
; [eval] (i < j) && (j < nodesLength(xs))
; [eval] i < j
(push) ; 6
(push) ; 7
(assert (not (not (< i@28 j@29))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (< i@28 j@29)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 18] i@28 < j@29
(assert (< i@28 j@29))
; [eval] j < nodesLength(xs)
; [eval] nodesLength(xs)
(pop) ; 7
(push) ; 7
; [else-branch 18] !i@28 < j@29
(assert (not (< i@28 j@29)))
(pop) ; 7
(pop) ; 6
(pop) ; 5
(push) ; 5
; [else-branch 17] !0 <= i@28
(assert (not (<= 0 i@28)))
(pop) ; 5
(pop) ; 4
(push) ; 4
(push) ; 5
(assert (not (not (and (<= 0 i@28) (and (< i@28 j@29) (< j@29 ($nodesLength s@$ xs@4)))))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (and (<= 0 i@28) (and (< i@28 j@29) (< j@29 ($nodesLength s@$ xs@4))))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 19] 0 <= i@28 && i@28 < j@29 && j@29 < nodesLength(xs@4;s@$)
(assert (and (<= 0 i@28) (and (< i@28 j@29) (< j@29 ($nodesLength s@$ xs@4)))))
; [eval] prio(result[i]) <= prio(result[j])
; [eval] prio(result[i])
; [eval] result[i]
; [eval] prio(result[j])
; [eval] result[j]
(pop) ; 5
(push) ; 5
; [else-branch 19] !0 <= i@28 && i@28 < j@29 && j@29 < nodesLength(xs@4;s@$)
(assert (not (and (<= 0 i@28) (and (< i@28 j@29) (< j@29 ($nodesLength s@$ xs@4))))))
(pop) ; 5
(pop) ; 4
(pop) ; 3
(set-option :timeout 0)
(push) ; 3
(assert (not (forall ((i@28 Int) (j@29 Int)) (!
  (implies
    (and (<= 0 i@28) (and (< i@28 j@29) (< j@29 ($nodesLength s@$ xs@4))))
    (<=
      ($prio $Snap.unit ($Seq.index joinedIn@27 i@28))
      ($prio $Snap.unit ($Seq.index joinedIn@27 j@29))))
  :pattern (($prio$ $Snap.unit ($Seq.index joinedIn@27 i@28)) ($prio$ $Snap.unit ($Seq.index
    joinedIn@27
    j@29)))
  :qid |prog.l32|))))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (forall ((i@28 Int) (j@29 Int)) (!
  (implies
    (and (<= 0 i@28) (and (< i@28 j@29) (< j@29 ($nodesLength s@$ xs@4))))
    (<=
      ($prio $Snap.unit ($Seq.index joinedIn@27 i@28))
      ($prio $Snap.unit ($Seq.index joinedIn@27 j@29))))
  :pattern (($prio$ $Snap.unit ($Seq.index joinedIn@27 i@28)) ($prio$ $Snap.unit ($Seq.index
    joinedIn@27
    j@29)))
  :qid |prog.l32|)))
(pop) ; 2
(assert (forall ((s@$ $Snap) (xs@4 $Ref)) (!
  ($Seq.equal
    ($nodesContent s@$ xs@4)
    ($Seq.append
      ($Seq.singleton ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)))
      (ite
        (=
          ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$)))
          $Ref.null)
        $Seq.empty<$Ref>
        ($nodesContent$ ($Snap.first ($Snap.second ($Snap.second s@$))) ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$)))))))
  :pattern (($nodesContent s@$ xs@4))
  )))
; ---------- FUNCTION content (specs well-defined) ----------
(declare-const result@30 $Seq<$Ref>)
(push) ; 2
; [eval] (forall i: Int, j: Int :: { prio(result[i]),prio(result[j]) } (0 <= i) && ((i < j) && (j < length(xs))) ==> (prio(result[i]) <= prio(result[j])))
(declare-const i@31 Int)
(declare-const j@32 Int)
(push) ; 3
; [eval] (0 <= i) && ((i < j) && (j < length(xs))) ==> (prio(result[i]) <= prio(result[j]))
; [eval] (0 <= i) && ((i < j) && (j < length(xs)))
; [eval] 0 <= i
(push) ; 4
(set-option :timeout 250)
(push) ; 5
(assert (not (not (<= 0 i@31))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= 0 i@31)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 20] 0 <= i@31
(assert (<= 0 i@31))
; [eval] (i < j) && (j < length(xs))
; [eval] i < j
(push) ; 6
(push) ; 7
(assert (not (not (< i@31 j@32))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (< i@31 j@32)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 21] i@31 < j@32
(assert (< i@31 j@32))
; [eval] j < length(xs)
; [eval] length(xs)
(pop) ; 7
(push) ; 7
; [else-branch 21] !i@31 < j@32
(assert (not (< i@31 j@32)))
(pop) ; 7
(pop) ; 6
(pop) ; 5
(push) ; 5
; [else-branch 20] !0 <= i@31
(assert (not (<= 0 i@31)))
(pop) ; 5
(pop) ; 4
(push) ; 4
(push) ; 5
(assert (not (not (and (<= 0 i@31) (and (< i@31 j@32) (< j@32 ($length s@$ xs@5)))))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (and (<= 0 i@31) (and (< i@31 j@32) (< j@32 ($length s@$ xs@5))))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 22] 0 <= i@31 && i@31 < j@32 && j@32 < length(xs@5;s@$)
(assert (and (<= 0 i@31) (and (< i@31 j@32) (< j@32 ($length s@$ xs@5)))))
; [eval] prio(result[i]) <= prio(result[j])
; [eval] prio(result[i])
; [eval] result[i]
; [eval] prio(result[j])
; [eval] result[j]
(pop) ; 5
(push) ; 5
; [else-branch 22] !0 <= i@31 && i@31 < j@32 && j@32 < length(xs@5;s@$)
(assert (not (and (<= 0 i@31) (and (< i@31 j@32) (< j@32 ($length s@$ xs@5))))))
(pop) ; 5
(pop) ; 4
(pop) ; 3
(pop) ; 2
(assert (forall ((s@$ $Snap) (xs@5 $Ref)) (!
  ($Seq.equal ($content$ s@$ xs@5) ($content s@$ xs@5))
  :pattern (($content s@$ xs@5))
  )))
(assert (forall ((s@$ $Snap) (xs@5 $Ref)) (!
  (forall (($i Int) ($j Int)) (!
    (implies
      (and (<= 0 $i) (and (< $i $j) (< $j ($length s@$ xs@5))))
      (<=
        ($prio $Snap.unit ($Seq.index ($content$ s@$ xs@5) $i))
        ($prio $Snap.unit ($Seq.index ($content$ s@$ xs@5) $j))))
    :pattern (($prio$ $Snap.unit ($Seq.index ($content$ s@$ xs@5) $i)) ($prio$ $Snap.unit ($Seq.index
      ($content$ s@$ xs@5)
      $j)))
    ))
  :pattern (($content$ s@$ xs@5))
  )))
; ---------- FUNCTION content----------
(declare-const result@33 $Seq<$Ref>)
(push) ; 2
; [eval] (unfolding acc(List(xs), write) in (xs.head == null ? Seq[Ref]() : nodesContent(xs.head)))
(set-option :timeout 0)
(push) ; 3
(assert (not (= xs@5 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (not (= xs@5 $Ref.null)))
; [eval] xs.head != null
(set-option :timeout 250)
(push) ; 3
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
(assert (not (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null))))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
; [then-branch 23] First(s@$) != Null
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)))
; [eval] (xs.head == null ? Seq[Ref]() : nodesContent(xs.head))
; [eval] xs.head == null
; [dead then-branch 24] First(s@$) == Null
(push) ; 4
; [else-branch 24] First(s@$) != Null
; [eval] nodesContent(xs.head)
(pop) ; 4
(declare-const $deadThen@34 $Seq<$Ref>)
(pop) ; 3
(push) ; 3
; [else-branch 23] First(s@$) == Null
(assert (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null))
; [eval] (xs.head == null ? Seq[Ref]() : nodesContent(xs.head))
; [eval] xs.head == null
(push) ; 4
(assert (not (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 25] First(s@$) == Null
; [eval] Seq[Ref]()
(pop) ; 4
; [dead else-branch 25] First(s@$) != Null
(declare-const $deadElse@35 $Seq<$Ref>)
(pop) ; 3
(declare-fun joinedIn@36 () $Seq<$Ref>)
(assert (implies
  (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)
  (and
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)
    (not (= xs@5 $Ref.null)))))
(assert (implies
  (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null))
  (and
    (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null))
    (not (= xs@5 $Ref.null)))))
(assert (and
  (implies
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)
    ($Seq.equal
      joinedIn@36
      (ite
        (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)
        $Seq.empty<$Ref>
        $deadElse@35)))
  (implies
    (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null))
    ($Seq.equal
      joinedIn@36
      (ite
        (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)
        $deadThen@34
        ($nodesContent ($Snap.second s@$) ($SortWrappers.$SnapTo$Ref ($Snap.first s@$))))))))
; [eval] (forall i: Int, j: Int :: { prio(result[i]),prio(result[j]) } (0 <= i) && ((i < j) && (j < length(xs))) ==> (prio(result[i]) <= prio(result[j])))
(declare-const i@37 Int)
(declare-const j@38 Int)
(push) ; 3
; [eval] (0 <= i) && ((i < j) && (j < length(xs))) ==> (prio(result[i]) <= prio(result[j]))
; [eval] (0 <= i) && ((i < j) && (j < length(xs)))
; [eval] 0 <= i
(push) ; 4
(push) ; 5
(assert (not (not (<= 0 i@37))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= 0 i@37)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 26] 0 <= i@37
(assert (<= 0 i@37))
; [eval] (i < j) && (j < length(xs))
; [eval] i < j
(push) ; 6
(push) ; 7
(assert (not (not (< i@37 j@38))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (< i@37 j@38)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 27] i@37 < j@38
(assert (< i@37 j@38))
; [eval] j < length(xs)
; [eval] length(xs)
(pop) ; 7
(push) ; 7
; [else-branch 27] !i@37 < j@38
(assert (not (< i@37 j@38)))
(pop) ; 7
(pop) ; 6
(pop) ; 5
(push) ; 5
; [else-branch 26] !0 <= i@37
(assert (not (<= 0 i@37)))
(pop) ; 5
(pop) ; 4
(push) ; 4
(push) ; 5
(assert (not (not (and (<= 0 i@37) (and (< i@37 j@38) (< j@38 ($length s@$ xs@5)))))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (and (<= 0 i@37) (and (< i@37 j@38) (< j@38 ($length s@$ xs@5))))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 28] 0 <= i@37 && i@37 < j@38 && j@38 < length(xs@5;s@$)
(assert (and (<= 0 i@37) (and (< i@37 j@38) (< j@38 ($length s@$ xs@5)))))
; [eval] prio(result[i]) <= prio(result[j])
; [eval] prio(result[i])
; [eval] result[i]
; [eval] prio(result[j])
; [eval] result[j]
(pop) ; 5
(push) ; 5
; [else-branch 28] !0 <= i@37 && i@37 < j@38 && j@38 < length(xs@5;s@$)
(assert (not (and (<= 0 i@37) (and (< i@37 j@38) (< j@38 ($length s@$ xs@5))))))
(pop) ; 5
(pop) ; 4
(pop) ; 3
(set-option :timeout 0)
(push) ; 3
(assert (not (forall ((i@37 Int) (j@38 Int)) (!
  (implies
    (and (<= 0 i@37) (and (< i@37 j@38) (< j@38 ($length s@$ xs@5))))
    (<=
      ($prio $Snap.unit ($Seq.index joinedIn@36 i@37))
      ($prio $Snap.unit ($Seq.index joinedIn@36 j@38))))
  :pattern (($prio$ $Snap.unit ($Seq.index joinedIn@36 i@37)) ($prio$ $Snap.unit ($Seq.index
    joinedIn@36
    j@38)))
  :qid |prog.l25|))))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (forall ((i@37 Int) (j@38 Int)) (!
  (implies
    (and (<= 0 i@37) (and (< i@37 j@38) (< j@38 ($length s@$ xs@5))))
    (<=
      ($prio $Snap.unit ($Seq.index joinedIn@36 i@37))
      ($prio $Snap.unit ($Seq.index joinedIn@36 j@38))))
  :pattern (($prio$ $Snap.unit ($Seq.index joinedIn@36 i@37)) ($prio$ $Snap.unit ($Seq.index
    joinedIn@36
    j@38)))
  :qid |prog.l25|)))
(pop) ; 2
(assert (forall ((s@$ $Snap) (xs@5 $Ref)) (!
  ($Seq.equal
    ($content s@$ xs@5)
    (ite
      (= ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)) $Ref.null)
      $Seq.empty<$Ref>
      ($nodesContent ($Snap.second s@$) ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)))))
  :pattern (($content s@$ xs@5))
  )))
; ---------- FUNCTION peek (specs well-defined) ----------
(declare-const result@39 $Ref)
(push) ; 2
; [eval] result == nodesContent(xs)[0]
; [eval] nodesContent(xs)[0]
; [eval] nodesContent(xs)
(pop) ; 2
(assert (forall ((s@$ $Snap) (xs@6 $Ref)) (!
  (= ($peek$ s@$ xs@6) ($peek s@$ xs@6))
  :pattern (($peek s@$ xs@6))
  )))
(assert (forall ((s@$ $Snap) (xs@6 $Ref)) (!
  (= ($peek$ s@$ xs@6) ($Seq.index ($nodesContent s@$ xs@6) 0))
  :pattern (($peek$ s@$ xs@6))
  )))
; ---------- FUNCTION peek----------
(declare-const result@40 $Ref)
(push) ; 2
; [eval] (unfolding acc(PQueue(xs), write) in xs.data)
(push) ; 3
(assert (not (= xs@6 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (not (= xs@6 $Ref.null)))
(push) ; 3
(assert (not (= xs@6 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
; [eval] xs.next != null
(set-option :timeout 250)
(push) ; 3
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
(assert (not (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
; [then-branch 29] First(Second(s@$)) != Null
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)))
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 4
(push) ; 5
(assert (not (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 30] First(Second(s@$)) != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 5
; [dead else-branch 30] First(Second(s@$)) == Null
(pop) ; 4
(assert (implies
  (not
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
  (<=
    ($prio $Snap.unit ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)))
    ($prio $Snap.unit ($Seq.index
      ($nodesContent ($Snap.first ($Snap.second ($Snap.second s@$))) ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))))
      0)))))
(pop) ; 3
(push) ; 3
; [else-branch 29] First(Second(s@$)) == Null
(assert (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 4
; [dead then-branch 31] First(Second(s@$)) != Null
(push) ; 5
; [else-branch 31] First(Second(s@$)) == Null
(pop) ; 5
(pop) ; 4
(pop) ; 3
(declare-fun joinedIn@41 () $Ref)
(assert (implies
  (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)
  (and
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)
    (not (= xs@6 $Ref.null)))))
(assert (implies
  (not
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
  (and
    (implies
      (not
        (=
          ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$)))
          $Ref.null))
      (<=
        ($prio $Snap.unit ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)))
        ($prio $Snap.unit ($Seq.index
          ($nodesContent ($Snap.first ($Snap.second ($Snap.second s@$))) ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))))
          0))))
    (not
      (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
    (not (= xs@6 $Ref.null)))))
(assert (and
  (implies
    (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null)
    (= joinedIn@41 ($SortWrappers.$SnapTo$Ref ($Snap.first s@$))))
  (implies
    (not
      (= ($SortWrappers.$SnapTo$Ref ($Snap.first ($Snap.second s@$))) $Ref.null))
    (= joinedIn@41 ($SortWrappers.$SnapTo$Ref ($Snap.first s@$))))))
; [eval] result == nodesContent(xs)[0]
; [eval] nodesContent(xs)[0]
; [eval] nodesContent(xs)
(set-option :timeout 0)
(push) ; 3
(assert (not (= joinedIn@41 ($Seq.index ($nodesContent s@$ xs@6) 0))))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (= joinedIn@41 ($Seq.index ($nodesContent s@$ xs@6) 0)))
(pop) ; 2
(assert (forall ((s@$ $Snap) (xs@6 $Ref)) (!
  (= ($peek s@$ xs@6) ($SortWrappers.$SnapTo$Ref ($Snap.first s@$)))
  :pattern (($peek s@$ xs@6))
  )))
; ---------- FUNCTION itemAt (specs well-defined) ----------
(declare-const result@42 $Ref)
(push) ; 2
; [eval] (0 <= i) && (i < length(xs))
; [eval] 0 <= i
(push) ; 3
(set-option :timeout 250)
(push) ; 4
(assert (not (not (<= 0 i@8))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not (<= 0 i@8)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 32] 0 <= i@8
(assert (<= 0 i@8))
; [eval] i < length(xs)
; [eval] length(xs)
(pop) ; 4
(push) ; 4
; [else-branch 32] !0 <= i@8
(assert (not (<= 0 i@8)))
(pop) ; 4
(pop) ; 3
(assert (and (<= 0 i@8) (< i@8 ($length ($Snap.first s@$) xs@7))))
; [eval] result == content(xs)[i]
; [eval] content(xs)[i]
; [eval] content(xs)
(pop) ; 2
(assert (forall ((s@$ $Snap) (xs@7 $Ref) (i@8 Int)) (!
  (= ($itemAt$ s@$ xs@7 i@8) ($itemAt s@$ xs@7 i@8))
  :pattern (($itemAt s@$ xs@7 i@8))
  )))
(assert (forall ((s@$ $Snap) (xs@7 $Ref) (i@8 Int)) (!
  (implies
    (and (<= 0 i@8) (< i@8 ($length ($Snap.first s@$) xs@7)))
    (=
      ($itemAt$ s@$ xs@7 i@8)
      ($Seq.index ($content ($Snap.first s@$) xs@7) i@8)))
  :pattern (($itemAt$ s@$ xs@7 i@8))
  )))
; ---------- FUNCTION itemAt----------
(declare-const result@43 $Ref)
(push) ; 2
; [eval] (0 <= i) && (i < length(xs))
; [eval] 0 <= i
(push) ; 3
(push) ; 4
(assert (not (not (<= 0 i@8))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not (<= 0 i@8)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 33] 0 <= i@8
(assert (<= 0 i@8))
; [eval] i < length(xs)
; [eval] length(xs)
(pop) ; 4
(push) ; 4
; [else-branch 33] !0 <= i@8
(assert (not (<= 0 i@8)))
(pop) ; 4
(pop) ; 3
(assert (and (<= 0 i@8) (< i@8 ($length ($Snap.first s@$) xs@7))))
; [eval] content(xs)[i]
; [eval] content(xs)
; [eval] result == content(xs)[i]
; [eval] content(xs)[i]
; [eval] content(xs)
(pop) ; 2
(assert (forall ((s@$ $Snap) (xs@7 $Ref) (i@8 Int)) (!
  (implies
    (and (<= 0 i@8) (< i@8 ($length ($Snap.first s@$) xs@7)))
    (= ($itemAt s@$ xs@7 i@8) ($Seq.index ($content ($Snap.first s@$) xs@7) i@8)))
  :pattern (($itemAt s@$ xs@7 i@8))
  )))
; ---------- List ----------
(declare-const xs@44 $Ref)
(push) ; 2
(pop) ; 2
(push) ; 2
(declare-const $t@45 $Snap)
(declare-const $t@46 $Ref)
(declare-const $t@47 $Snap)
(assert (= $t@45 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@46) $t@47)))
(set-option :timeout 0)
(push) ; 3
(assert (not (= xs@44 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (not (= xs@44 $Ref.null)))
; [eval] xs.head != null
(set-option :timeout 250)
(push) ; 3
(assert (not (= $t@46 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
(assert (not (not (= $t@46 $Ref.null))))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
; [then-branch 34] $t@46 != Null
(assert (not (= $t@46 $Ref.null)))
(pop) ; 3
(push) ; 3
; [else-branch 34] $t@46 == Null
(assert (= $t@46 $Ref.null))
(pop) ; 3
(pop) ; 2
; ---------- PQueue ----------
(declare-const xs@48 $Ref)
(push) ; 2
(pop) ; 2
(push) ; 2
(declare-const $t@49 $Snap)
(declare-const $t@50 $Ref)
(declare-const $t@51 $Snap)
(assert (= $t@49 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@50) $t@51)))
(set-option :timeout 0)
(push) ; 3
(assert (not (= xs@48 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (not (= xs@48 $Ref.null)))
(declare-const $t@52 $Ref)
(declare-const $t@53 $Snap)
(assert (= $t@51 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@52) $t@53)))
(push) ; 3
(assert (not (= xs@48 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(declare-const $t@54 $Snap)
(assert (= $t@53 ($Snap.combine $t@54 $Snap.unit)))
; [eval] xs.next != null
(set-option :timeout 250)
(push) ; 3
(assert (not (= $t@52 $Ref.null)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
(assert (not (not (= $t@52 $Ref.null))))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
; [then-branch 35] $t@52 != Null
(assert (not (= $t@52 $Ref.null)))
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 4
(push) ; 5
(assert (not (= $t@52 $Ref.null)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 36] $t@52 != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 5
; [dead else-branch 36] $t@52 == Null
(pop) ; 4
(assert (implies
  (not (= $t@52 $Ref.null))
  (<=
    ($prio $Snap.unit $t@50)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@54 $t@52) 0)))))
(pop) ; 3
(push) ; 3
; [else-branch 35] $t@52 == Null
(assert (= $t@52 $Ref.null))
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 4
; [dead then-branch 37] $t@52 != Null
(push) ; 5
; [else-branch 37] $t@52 == Null
(pop) ; 5
(pop) ; 4
(pop) ; 3
(pop) ; 2
; ---------- insert ----------
(declare-const xs@55 $Ref)
(declare-const x@56 $Ref)
(declare-const i@57 Int)
(declare-const tmp@58 $Ref)
(declare-const crt@59 $Ref)
(declare-const nxt@60 $Ref)
(declare-const hd@61 $Ref)
(declare-const node@62 $Ref)
(push) ; 2
(declare-const $t@63 $Snap)
(push) ; 3
(declare-const crt@64 $Ref)
(declare-const crt@65 $Ref)
(declare-const xs@66 $Ref)
(declare-const i@67 Int)
(declare-const hd@68 $Ref)
(declare-const hd@69 $Ref)
(declare-const xs@70 $Ref)
(declare-const i@71 Int)
(declare-const crt@72 $Ref)
(push) ; 4
(declare-const $t@73 $Snap)
(declare-const $t@74 $Snap)
(assert (= $t@73 ($Snap.combine $t@74 $Snap.unit)))
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= ($peek $t@74 crt@59) ($Seq.index ($content $t@63 xs@55) i@57)))
(pop) ; 4
(push) ; 4
(declare-const $t@75 $Snap)
(declare-const $t@76 $Snap)
(assert (= $t@75 ($Snap.combine $t@76 $Snap.unit)))
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(assert ($Seq.equal
  ($nodesContent $t@76 hd@61)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) i@57) 0)
    ($nodesContent $t@74 crt@59))))
(pop) ; 4
(declare-const crt@77 $Ref)
(declare-const crt@78 $Ref)
(declare-const xs@79 $Ref)
(declare-const i@80 Int)
(declare-const hd@81 $Ref)
(declare-const hd@82 $Ref)
(declare-const xs@83 $Ref)
(declare-const i@84 Int)
(declare-const crt@85 $Ref)
(push) ; 4
(declare-const $t@86 $Snap)
(declare-const $t@87 $Snap)
(assert (= $t@86 ($Snap.combine $t@87 $Snap.unit)))
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= ($peek $t@87 crt@59) ($Seq.index ($content $t@63 xs@55) i@57)))
(pop) ; 4
(push) ; 4
(declare-const $t@88 $Snap)
(declare-const $t@89 $Snap)
(assert (= $t@88 ($Snap.combine $t@89 $Snap.unit)))
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(assert ($Seq.equal
  ($nodesContent $t@89 hd@61)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) i@57) 0)
    ($nodesContent $t@87 crt@59))))
(pop) ; 4
(declare-const crt@90 $Ref)
(declare-const crt@91 $Ref)
(declare-const xs@92 $Ref)
(declare-const i@93 Int)
(declare-const hd@94 $Ref)
(declare-const hd@95 $Ref)
(declare-const xs@96 $Ref)
(declare-const i@97 Int)
(declare-const crt@98 $Ref)
(push) ; 4
(declare-const $t@99 $Snap)
(declare-const $t@100 $Snap)
(assert (= $t@99 ($Snap.combine $t@100 $Snap.unit)))
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= ($peek $t@100 crt@59) ($Seq.index ($content $t@63 xs@55) i@57)))
(pop) ; 4
(push) ; 4
(declare-const $t@101 $Snap)
(declare-const $t@102 $Snap)
(assert (= $t@101 ($Snap.combine $t@102 $Snap.unit)))
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(assert ($Seq.equal
  ($nodesContent $t@102 hd@61)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) i@57) 0)
    ($nodesContent $t@100 crt@59))))
(pop) ; 4
(declare-const crt@103 $Ref)
(declare-const crt@104 $Ref)
(declare-const xs@105 $Ref)
(declare-const i@106 Int)
(declare-const hd@107 $Ref)
(declare-const hd@108 $Ref)
(declare-const xs@109 $Ref)
(declare-const i@110 Int)
(declare-const crt@111 $Ref)
(push) ; 4
(declare-const $t@112 $Snap)
(declare-const $t@113 $Snap)
(assert (= $t@112 ($Snap.combine $t@113 $Snap.unit)))
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= ($peek $t@113 crt@59) ($Seq.index ($content $t@63 xs@55) i@57)))
(pop) ; 4
(push) ; 4
(declare-const $t@114 $Snap)
(declare-const $t@115 $Snap)
(assert (= $t@114 ($Snap.combine $t@115 $Snap.unit)))
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(assert ($Seq.equal
  ($nodesContent $t@115 hd@61)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) i@57) 0)
    ($nodesContent $t@113 crt@59))))
(pop) ; 4
(declare-const crt@116 $Ref)
(declare-const crt@117 $Ref)
(declare-const xs@118 $Ref)
(declare-const i@119 Int)
(declare-const hd@120 $Ref)
(declare-const hd@121 $Ref)
(declare-const xs@122 $Ref)
(declare-const i@123 Int)
(declare-const crt@124 $Ref)
(push) ; 4
(declare-const $t@125 $Snap)
(declare-const $t@126 $Snap)
(assert (= $t@125 ($Snap.combine $t@126 $Snap.unit)))
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= ($peek $t@126 crt@59) ($Seq.index ($content $t@63 xs@55) i@57)))
(pop) ; 4
(push) ; 4
(declare-const $t@127 $Snap)
(declare-const $t@128 $Snap)
(assert (= $t@127 ($Snap.combine $t@128 $Snap.unit)))
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(assert ($Seq.equal
  ($nodesContent $t@128 hd@61)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) i@57) 0)
    ($nodesContent $t@126 crt@59))))
(pop) ; 4
(pop) ; 3
(push) ; 3
(declare-const $t@129 $Snap)
; [eval] content(xs) == old(content(xs))[0..i] ++ Seq(x) ++ old(content(xs))[i..]
; [eval] content(xs)
; [eval] old(content(xs))[0..i] ++ Seq(x) ++ old(content(xs))[i..]
; [eval] old(content(xs))[0..i] ++ Seq(x)
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] Seq(x)
(assert (= ($Seq.length ($Seq.singleton x@56)) 1))
; [eval] old(content(xs))[i..]
; [eval] old(content(xs))
; [eval] content(xs)
(assert ($Seq.equal
  ($content $t@129 xs@55)
  ($Seq.append
    ($Seq.append
      ($Seq.drop ($Seq.take ($content $t@63 xs@55) i@57) 0)
      ($Seq.singleton x@56))
    ($Seq.drop ($content $t@63 xs@55) i@57))))
(pop) ; 3
(push) ; 3
; [exec]
; unfold acc(List(xs), write)
(declare-const $t@130 $Ref)
(declare-const $t@131 $Snap)
(assert (= $t@63 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@130) $t@131)))
(set-option :timeout 0)
(push) ; 4
(assert (not (= xs@55 $Ref.null)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (not (= xs@55 $Ref.null)))
; [eval] xs.head != null
(set-option :timeout 250)
(push) ; 4
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not (not (= $t@130 $Ref.null))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 38] $t@130 != Null
(assert (not (= $t@130 $Ref.null)))
; [exec]
; i := 0
; [exec]
; hd := xs.head
; [eval] (hd == null) || (prio(x) <= (unfolding acc(PQueue(hd), write) in prio(hd.data)))
; [eval] hd == null
(push) ; 5
(push) ; 6
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 39] $t@130 != Null
; [eval] prio(x) <= (unfolding acc(PQueue(hd), write) in prio(hd.data))
; [eval] prio(x)
; [eval] (unfolding acc(PQueue(hd), write) in prio(hd.data))
(declare-const $t@132 $Ref)
(declare-const $t@133 $Snap)
(assert (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@132) $t@133)))
(set-option :timeout 0)
(push) ; 7
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const $t@134 $Ref)
(declare-const $t@135 $Snap)
(assert (= $t@133 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@134) $t@135)))
(push) ; 7
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const $t@136 $Snap)
(assert (= $t@135 ($Snap.combine $t@136 $Snap.unit)))
; [eval] hd.next != null
(set-option :timeout 250)
(push) ; 7
(assert (not (= $t@134 $Ref.null)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (not (= $t@134 $Ref.null))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 40] $t@134 != Null
(assert (not (= $t@134 $Ref.null)))
; [eval] (hd.next != null) ==> (prio(hd.data) <= prio(nodesContent(hd.next)[0]))
; [eval] hd.next != null
(push) ; 8
(push) ; 9
(assert (not (= $t@134 $Ref.null)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 41] $t@134 != Null
; [eval] prio(hd.data) <= prio(nodesContent(hd.next)[0])
; [eval] prio(hd.data)
; [eval] prio(nodesContent(hd.next)[0])
; [eval] nodesContent(hd.next)[0]
; [eval] nodesContent(hd.next)
(pop) ; 9
; [dead else-branch 41] $t@134 == Null
(pop) ; 8
(assert (implies
  (not (= $t@134 $Ref.null))
  (<=
    ($prio $Snap.unit $t@132)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@136 $t@134) 0)))))
; [eval] prio(hd.data)
(pop) ; 7
(push) ; 7
; [else-branch 40] $t@134 == Null
(assert (= $t@134 $Ref.null))
; [eval] (hd.next != null) ==> (prio(hd.data) <= prio(nodesContent(hd.next)[0]))
; [eval] hd.next != null
(push) ; 8
; [dead then-branch 42] $t@134 != Null
(push) ; 9
; [else-branch 42] $t@134 == Null
(pop) ; 9
(pop) ; 8
; [eval] prio(hd.data)
(pop) ; 7
(declare-fun joinedIn@137 () Int)
(assert (implies
  (= $t@134 $Ref.null)
  (and
    (= $t@134 $Ref.null)
    (= $t@135 ($Snap.combine $t@136 $Snap.unit))
    (= $t@133 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@134) $t@135))
    (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@132) $t@133)))))
(assert (implies
  (not (= $t@134 $Ref.null))
  (and
    (implies
      (not (= $t@134 $Ref.null))
      (<=
        ($prio $Snap.unit $t@132)
        ($prio $Snap.unit ($Seq.index ($nodesContent $t@136 $t@134) 0))))
    (not (= $t@134 $Ref.null))
    (= $t@135 ($Snap.combine $t@136 $Snap.unit))
    (= $t@133 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@134) $t@135))
    (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@132) $t@133)))))
(assert (and
  (implies (= $t@134 $Ref.null) (= joinedIn@137 ($prio $Snap.unit $t@132)))
  (implies (not (= $t@134 $Ref.null)) (= joinedIn@137 ($prio $Snap.unit $t@132)))))
(pop) ; 6
; [dead else-branch 39] $t@130 == Null
(pop) ; 5
(assert (implies
  (not (= $t@130 $Ref.null))
  (and
    (and
      (implies (= $t@134 $Ref.null) (= joinedIn@137 ($prio $Snap.unit $t@132)))
      (implies
        (not (= $t@134 $Ref.null))
        (= joinedIn@137 ($prio $Snap.unit $t@132))))
    (implies
      (not (= $t@134 $Ref.null))
      (and
        (implies
          (not (= $t@134 $Ref.null))
          (<=
            ($prio $Snap.unit $t@132)
            ($prio $Snap.unit ($Seq.index ($nodesContent $t@136 $t@134) 0))))
        (not (= $t@134 $Ref.null))
        (= $t@135 ($Snap.combine $t@136 $Snap.unit))
        (= $t@133 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@134) $t@135))
        (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@132) $t@133))))
    (implies
      (= $t@134 $Ref.null)
      (and
        (= $t@134 $Ref.null)
        (= $t@135 ($Snap.combine $t@136 $Snap.unit))
        (= $t@133 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@134) $t@135))
        (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@132) $t@133))))
    (= $t@135 ($Snap.combine $t@136 $Snap.unit))
    (= $t@133 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@134) $t@135))
    (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@132) $t@133)))))
(push) ; 5
(assert (not (not (or (= $t@130 $Ref.null) (<= ($prio $Snap.unit x@56) joinedIn@137)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (or (= $t@130 $Ref.null) (<= ($prio $Snap.unit x@56) joinedIn@137))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 43] $t@130 == Null || prio(x@56;_) <= joinedIn@137()
(assert (or (= $t@130 $Ref.null) (<= ($prio $Snap.unit x@56) joinedIn@137)))
; [exec]
; inhale hd != null
; [eval] hd != null
; [exec]
; tmp := new(data, next)
(declare-const tmp@138 $Ref)
(assert (not (= tmp@138 $Ref.null)))
(declare-const data@139 $Ref)
(declare-const next@140 $Ref)
(assert (and
  (not (= xs@55 tmp@138))
  (not (= x@56 tmp@138))
  (not (= crt@59 tmp@138))
  (not (= nxt@60 tmp@138))
  (not (= node@62 tmp@138))
  (not (= $t@130 tmp@138))
  (not (= data@139 tmp@138))
  (not (= next@140 tmp@138))))
; [exec]
; tmp.data := x
; [exec]
; tmp.next := hd
; [exec]
; fold acc(PQueue(tmp), write)
; [eval] xs.next != null
(push) ; 6
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 44] $t@130 != Null
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 7
(push) ; 8
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 45] $t@130 != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 8
; [dead else-branch 45] $t@130 == Null
(pop) ; 7
(set-option :timeout 0)
(push) ; 7
(assert (not (implies
  (not (= $t@130 $Ref.null))
  (<=
    ($prio $Snap.unit x@56)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@131 $t@130) 0))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (implies
  (not (= $t@130 $Ref.null))
  (<=
    ($prio $Snap.unit x@56)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@131 $t@130) 0)))))
; [exec]
; xs.head := tmp
; [exec]
; fold acc(List(xs), write)
; [eval] xs.head != null
(set-option :timeout 250)
(push) ; 7
(assert (not (= tmp@138 $Ref.null)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 46] tmp@138 != Null
; [eval] content(xs) == old(content(xs))[0..i] ++ Seq(x) ++ old(content(xs))[i..]
; [eval] content(xs)
; [eval] old(content(xs))[0..i] ++ Seq(x) ++ old(content(xs))[i..]
; [eval] old(content(xs))[0..i] ++ Seq(x)
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] Seq(x)
(assert (= ($Seq.length ($Seq.singleton x@56)) 1))
; [eval] old(content(xs))[i..]
; [eval] old(content(xs))
; [eval] content(xs)
(set-option :timeout 0)
(push) ; 8
(assert (not ($Seq.equal
  ($content ($Snap.combine
    ($SortWrappers.$RefTo$Snap tmp@138)
    ($Snap.combine
      ($SortWrappers.$RefTo$Snap x@56)
      ($Snap.combine
        ($SortWrappers.$RefTo$Snap $t@130)
        ($Snap.combine $t@131 $Snap.unit)))) xs@55)
  ($Seq.append
    ($Seq.append
      ($Seq.drop ($Seq.take ($content $t@63 xs@55) 0) 0)
      ($Seq.singleton x@56))
    ($Seq.drop ($content $t@63 xs@55) 0)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert ($Seq.equal
  ($content ($Snap.combine
    ($SortWrappers.$RefTo$Snap tmp@138)
    ($Snap.combine
      ($SortWrappers.$RefTo$Snap x@56)
      ($Snap.combine
        ($SortWrappers.$RefTo$Snap $t@130)
        ($Snap.combine $t@131 $Snap.unit)))) xs@55)
  ($Seq.append
    ($Seq.append
      ($Seq.drop ($Seq.take ($content $t@63 xs@55) 0) 0)
      ($Seq.singleton x@56))
    ($Seq.drop ($content $t@63 xs@55) 0))))
(pop) ; 7
; [dead else-branch 46] tmp@138 == Null
(pop) ; 6
; [dead else-branch 44] $t@130 == Null
(pop) ; 5
(push) ; 5
; [else-branch 43] !$t@130 == Null || prio(x@56;_) <= joinedIn@137()
(assert (not (or (= $t@130 $Ref.null) (<= ($prio $Snap.unit x@56) joinedIn@137))))
(pop) ; 5
; [eval] !((hd == null) || (prio(x) <= (unfolding acc(PQueue(hd), write) in prio(hd.data))))
; [eval] (hd == null) || (prio(x) <= (unfolding acc(PQueue(hd), write) in prio(hd.data)))
; [eval] hd == null
(push) ; 5
(set-option :timeout 250)
(push) ; 6
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 47] $t@130 != Null
; [eval] prio(x) <= (unfolding acc(PQueue(hd), write) in prio(hd.data))
; [eval] prio(x)
; [eval] (unfolding acc(PQueue(hd), write) in prio(hd.data))
(declare-const $t@141 $Ref)
(declare-const $t@142 $Snap)
(assert (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@141) $t@142)))
(set-option :timeout 0)
(push) ; 7
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const $t@143 $Ref)
(declare-const $t@144 $Snap)
(assert (= $t@142 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@143) $t@144)))
(push) ; 7
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const $t@145 $Snap)
(assert (= $t@144 ($Snap.combine $t@145 $Snap.unit)))
; [eval] hd.next != null
(set-option :timeout 250)
(push) ; 7
(assert (not (= $t@143 $Ref.null)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (not (= $t@143 $Ref.null))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 48] $t@143 != Null
(assert (not (= $t@143 $Ref.null)))
; [eval] (hd.next != null) ==> (prio(hd.data) <= prio(nodesContent(hd.next)[0]))
; [eval] hd.next != null
(push) ; 8
(push) ; 9
(assert (not (= $t@143 $Ref.null)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 49] $t@143 != Null
; [eval] prio(hd.data) <= prio(nodesContent(hd.next)[0])
; [eval] prio(hd.data)
; [eval] prio(nodesContent(hd.next)[0])
; [eval] nodesContent(hd.next)[0]
; [eval] nodesContent(hd.next)
(pop) ; 9
; [dead else-branch 49] $t@143 == Null
(pop) ; 8
(assert (implies
  (not (= $t@143 $Ref.null))
  (<=
    ($prio $Snap.unit $t@141)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@145 $t@143) 0)))))
; [eval] prio(hd.data)
(pop) ; 7
(push) ; 7
; [else-branch 48] $t@143 == Null
(assert (= $t@143 $Ref.null))
; [eval] (hd.next != null) ==> (prio(hd.data) <= prio(nodesContent(hd.next)[0]))
; [eval] hd.next != null
(push) ; 8
; [dead then-branch 50] $t@143 != Null
(push) ; 9
; [else-branch 50] $t@143 == Null
(pop) ; 9
(pop) ; 8
; [eval] prio(hd.data)
(pop) ; 7
(declare-fun joinedIn@146 () Int)
(assert (implies
  (= $t@143 $Ref.null)
  (and
    (= $t@143 $Ref.null)
    (= $t@144 ($Snap.combine $t@145 $Snap.unit))
    (= $t@142 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@143) $t@144))
    (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@141) $t@142)))))
(assert (implies
  (not (= $t@143 $Ref.null))
  (and
    (implies
      (not (= $t@143 $Ref.null))
      (<=
        ($prio $Snap.unit $t@141)
        ($prio $Snap.unit ($Seq.index ($nodesContent $t@145 $t@143) 0))))
    (not (= $t@143 $Ref.null))
    (= $t@144 ($Snap.combine $t@145 $Snap.unit))
    (= $t@142 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@143) $t@144))
    (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@141) $t@142)))))
(assert (and
  (implies (= $t@143 $Ref.null) (= joinedIn@146 ($prio $Snap.unit $t@141)))
  (implies (not (= $t@143 $Ref.null)) (= joinedIn@146 ($prio $Snap.unit $t@141)))))
(pop) ; 6
; [dead else-branch 47] $t@130 == Null
(pop) ; 5
(assert (implies
  (not (= $t@130 $Ref.null))
  (and
    (and
      (implies (= $t@143 $Ref.null) (= joinedIn@146 ($prio $Snap.unit $t@141)))
      (implies
        (not (= $t@143 $Ref.null))
        (= joinedIn@146 ($prio $Snap.unit $t@141))))
    (implies
      (not (= $t@143 $Ref.null))
      (and
        (implies
          (not (= $t@143 $Ref.null))
          (<=
            ($prio $Snap.unit $t@141)
            ($prio $Snap.unit ($Seq.index ($nodesContent $t@145 $t@143) 0))))
        (not (= $t@143 $Ref.null))
        (= $t@144 ($Snap.combine $t@145 $Snap.unit))
        (= $t@142 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@143) $t@144))
        (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@141) $t@142))))
    (implies
      (= $t@143 $Ref.null)
      (and
        (= $t@143 $Ref.null)
        (= $t@144 ($Snap.combine $t@145 $Snap.unit))
        (= $t@142 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@143) $t@144))
        (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@141) $t@142))))
    (= $t@144 ($Snap.combine $t@145 $Snap.unit))
    (= $t@142 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@143) $t@144))
    (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@141) $t@142)))))
(push) ; 5
(assert (not (or (= $t@130 $Ref.null) (<= ($prio $Snap.unit x@56) joinedIn@146))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (not (or (= $t@130 $Ref.null) (<= ($prio $Snap.unit x@56) joinedIn@146)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 51] !$t@130 == Null || prio(x@56;_) <= joinedIn@146()
(assert (not (or (= $t@130 $Ref.null) (<= ($prio $Snap.unit x@56) joinedIn@146))))
; [exec]
; unfold acc(PQueue(hd), write)
(declare-const $t@147 $Ref)
(declare-const $t@148 $Snap)
(assert (= $t@131 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@147) $t@148)))
(set-option :timeout 0)
(push) ; 6
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const $t@149 $Ref)
(declare-const $t@150 $Snap)
(assert (= $t@148 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@149) $t@150)))
(push) ; 6
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const $t@151 $Snap)
(assert (= $t@150 ($Snap.combine $t@151 $Snap.unit)))
; [eval] hd.next != null
(set-option :timeout 250)
(push) ; 6
(assert (not (= $t@149 $Ref.null)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (not (= $t@149 $Ref.null))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 52] $t@149 != Null
(assert (not (= $t@149 $Ref.null)))
; [eval] (hd.next != null) ==> (prio(hd.data) <= prio(nodesContent(hd.next)[0]))
; [eval] hd.next != null
(push) ; 7
(push) ; 8
(assert (not (= $t@149 $Ref.null)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 53] $t@149 != Null
; [eval] prio(hd.data) <= prio(nodesContent(hd.next)[0])
; [eval] prio(hd.data)
; [eval] prio(nodesContent(hd.next)[0])
; [eval] nodesContent(hd.next)[0]
; [eval] nodesContent(hd.next)
(pop) ; 8
; [dead else-branch 53] $t@149 == Null
(pop) ; 7
(assert (implies
  (not (= $t@149 $Ref.null))
  (<=
    ($prio $Snap.unit $t@147)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@151 $t@149) 0)))))
; [exec]
; crt := hd
; [exec]
; nxt := hd.next
; [exec]
; package acc(PQueue(crt), write) && (peek(crt) == old(content(xs))[i]) --* acc(PQueue(hd), write) && (nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt)))
(push) ; 7
(declare-const $t@152 $Snap)
(declare-const $t@153 $Snap)
(assert (= $t@152 ($Snap.combine $t@153 $Snap.unit)))
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= ($peek $t@153 $t@130) ($Seq.index ($content $t@63 xs@55) 0)))
(set-option :timeout 0)
(push) ; 8
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(push) ; 8
(assert (not ($Seq.equal
  ($nodesContent $t@153 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) 0) 0)
    ($nodesContent $t@153 $t@130)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert ($Seq.equal
  ($nodesContent $t@153 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) 0) 0)
    ($nodesContent $t@153 $t@130))))
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 7
; loop at queue-magic-wands.sil,97:3
(declare-const prev@154 $Ref)
(declare-const i@155 Int)
(declare-const nxt@156 $Ref)
(declare-const crt@157 $Ref)
(push) ; 7
; Verify loop body
(declare-const $t@158 $Snap)
(declare-const $t@159 $Snap)
(assert (= $t@158 ($Snap.combine $t@159 $Snap.unit)))
(declare-const $t@160 $Snap)
(declare-const $t@161 $Snap)
(assert (= $t@159 ($Snap.combine $t@160 $t@161)))
(declare-const $t@162 $Snap)
(assert (= $t@160 ($Snap.combine $t@162 $Snap.unit)))
(declare-const $t@163 $Snap)
(assert (= $t@162 ($Snap.combine $t@163 $Snap.unit)))
(declare-const $t@164 $Snap)
(declare-const $t@165 $Snap)
(assert (= $t@163 ($Snap.combine $t@164 $t@165)))
(declare-const $t@166 $Snap)
(assert (= $t@164 ($Snap.combine $t@166 $Snap.unit)))
(declare-const $t@167 $Snap)
(assert (= $t@166 ($Snap.combine $t@167 $Snap.unit)))
(declare-const $t@168 $Snap)
(assert (= $t@167 ($Snap.combine $Snap.unit $t@168)))
; [eval] (0 <= i) && (i < |old(content(xs))|) && ((nxt == null) ==> (i == |old(content(xs))| - 1))
; [eval] (0 <= i) && (i < |old(content(xs))|)
; [eval] 0 <= i
(push) ; 8
(set-option :timeout 250)
(push) ; 9
(assert (not (not (<= 0 i@155))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (<= 0 i@155)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 54] 0 <= i@155
(assert (<= 0 i@155))
; [eval] i < |old(content(xs))|
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 9
(push) ; 9
; [else-branch 54] !0 <= i@155
(assert (not (<= 0 i@155)))
(pop) ; 9
(pop) ; 8
(push) ; 8
(push) ; 9
(assert (not (not (and (<= 0 i@155) (< i@155 ($Seq.length ($content $t@63 xs@55)))))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (and (<= 0 i@155) (< i@155 ($Seq.length ($content $t@63 xs@55))))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 55] 0 <= i@155 && i@155 < |content(xs@55;$t@63)|
(assert (and (<= 0 i@155) (< i@155 ($Seq.length ($content $t@63 xs@55)))))
; [eval] (nxt == null) ==> (i == |old(content(xs))| - 1)
; [eval] nxt == null
(push) ; 10
(push) ; 11
(assert (not (not (= nxt@156 $Ref.null))))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (= nxt@156 $Ref.null)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 56] nxt@156 == Null
(assert (= nxt@156 $Ref.null))
; [eval] i == |old(content(xs))| - 1
; [eval] |old(content(xs))| - 1
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 11
(push) ; 11
; [else-branch 56] nxt@156 != Null
(assert (not (= nxt@156 $Ref.null)))
(pop) ; 11
(pop) ; 10
(pop) ; 9
(push) ; 9
; [else-branch 55] !0 <= i@155 && i@155 < |content(xs@55;$t@63)|
(assert (not (and (<= 0 i@155) (< i@155 ($Seq.length ($content $t@63 xs@55))))))
(pop) ; 9
(pop) ; 8
(assert (and
  (and (<= 0 i@155) (< i@155 ($Seq.length ($content $t@63 xs@55))))
  (implies
    (= nxt@156 $Ref.null)
    (= i@155 (- ($Seq.length ($content $t@63 xs@55)) 1)))))
(declare-const $t@169 $Ref)
(declare-const $t@170 $Ref)
(assert (=
  $t@168
  ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@169)
    ($SortWrappers.$RefTo$Snap $t@170))))
(set-option :timeout 0)
(push) ; 8
(assert (not (= crt@157 $Ref.null)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert (not (= crt@157 $Ref.null)))
(push) ; 8
(assert (not (= crt@157 $Ref.null)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
; [eval] nxt == crt.next
(assert (= nxt@156 $t@170))
; [eval] crt.data == old(content(xs))[i]
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= $t@169 ($Seq.index ($content $t@63 xs@55) i@155)))
; [eval] nxt != null
(set-option :timeout 250)
(push) ; 8
(assert (not (= nxt@156 $Ref.null)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
(assert (not (not (= nxt@156 $Ref.null))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 57] nxt@156 != Null
(assert (not (= nxt@156 $Ref.null)))
(declare-const $t@171 $Snap)
(assert (= $t@165 ($Snap.combine $t@171 $Snap.unit)))
; [eval] nodesContent(nxt) == old(content(xs))[i + 1..]
; [eval] nodesContent(nxt)
; [eval] old(content(xs))[i + 1..]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] i + 1
(assert ($Seq.equal
  ($nodesContent $t@171 nxt@156)
  ($Seq.drop ($content $t@63 xs@55) (+ i@155 1))))
; [eval] prio(crt.data) < prio(x)
; [eval] prio(crt.data)
; [eval] prio(x)
(assert (< ($prio $Snap.unit $t@169) ($prio $Snap.unit x@56)))
; [eval] (nxt != null) ==> (prio(crt.data) <= prio(peek(nxt)))
; [eval] nxt != null
(push) ; 9
(push) ; 10
(assert (not (= nxt@156 $Ref.null)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 58] nxt@156 != Null
; [eval] prio(crt.data) <= prio(peek(nxt))
; [eval] prio(crt.data)
; [eval] prio(peek(nxt))
; [eval] peek(nxt)
(pop) ; 10
; [dead else-branch 58] nxt@156 == Null
(pop) ; 9
(assert (implies
  (not (= nxt@156 $Ref.null))
  (<= ($prio $Snap.unit $t@169) ($prio $Snap.unit ($peek $t@171 nxt@156)))))
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] (nxt != null) && (prio(peek(nxt)) < prio(x))
; [eval] nxt != null
(push) ; 9
(push) ; 10
(assert (not (= nxt@156 $Ref.null)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 59] nxt@156 != Null
; [eval] prio(peek(nxt)) < prio(x)
; [eval] prio(peek(nxt))
; [eval] peek(nxt)
; [eval] prio(x)
(pop) ; 10
; [dead else-branch 59] nxt@156 == Null
(pop) ; 9
(assert (and
  (not (= nxt@156 $Ref.null))
  (< ($prio $Snap.unit ($peek $t@171 nxt@156)) ($prio $Snap.unit x@56))))
(check-sat)
; unknown
; [exec]
; prev := crt
; [exec]
; w := acc(PQueue(crt), write) && (peek(crt) == old(content(xs))[i]) --* acc(PQueue(hd), write) && (nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt)))
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
; [exec]
; unfold acc(PQueue(nxt), write)
(declare-const $t@172 $Ref)
(declare-const $t@173 $Snap)
(assert (= $t@171 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@172) $t@173)))
(set-option :timeout 0)
(push) ; 9
(assert (not (= nxt@156 $Ref.null)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (= crt@157 nxt@156)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(declare-const $t@174 $Ref)
(declare-const $t@175 $Snap)
(assert (= $t@173 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@174) $t@175)))
(push) ; 9
(assert (not (= nxt@156 $Ref.null)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (= crt@157 nxt@156)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(declare-const $t@176 $Snap)
(assert (= $t@175 ($Snap.combine $t@176 $Snap.unit)))
; [eval] nxt.next != null
(set-option :timeout 250)
(push) ; 9
(assert (not (= $t@174 $Ref.null)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (not (= $t@174 $Ref.null))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 60] $t@174 != Null
(assert (not (= $t@174 $Ref.null)))
; [eval] (nxt.next != null) ==> (prio(nxt.data) <= prio(nodesContent(nxt.next)[0]))
; [eval] nxt.next != null
(push) ; 10
(push) ; 11
(assert (not (= $t@174 $Ref.null)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 61] $t@174 != Null
; [eval] prio(nxt.data) <= prio(nodesContent(nxt.next)[0])
; [eval] prio(nxt.data)
; [eval] prio(nodesContent(nxt.next)[0])
; [eval] nodesContent(nxt.next)[0]
; [eval] nodesContent(nxt.next)
(pop) ; 11
; [dead else-branch 61] $t@174 == Null
(pop) ; 10
(assert (implies
  (not (= $t@174 $Ref.null))
  (<=
    ($prio $Snap.unit $t@172)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@176 $t@174) 0)))))
; [exec]
; crt := nxt
; [exec]
; nxt := nxt.next
; [exec]
; i := i + 1
; [eval] i + 1
; [exec]
; package acc(PQueue(crt), write) && (peek(crt) == old(content(xs))[i]) --* (folding acc(PQueue(prev), write) in (applying w in acc(PQueue(hd), write) && (nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt)))))
(push) ; 10
(declare-const $t@177 $Snap)
(declare-const $t@178 $Snap)
(assert (= $t@177 ($Snap.combine $t@178 $Snap.unit)))
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= ($peek $t@178 nxt@156) ($Seq.index ($content $t@63 xs@55) (+ i@155 1))))
(set-option :timeout 0)
(push) ; 11
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
; [eval] xs.next != null
(set-option :timeout 250)
(push) ; 11
(assert (not (= $t@170 $Ref.null)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (not (= $t@170 $Ref.null))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 62] $t@170 != Null
(assert (not (= $t@170 $Ref.null)))
(set-option :timeout 0)
(push) ; 12
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(push) ; 12
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 12
(set-option :timeout 250)
(push) ; 13
(assert (not (= $t@170 $Ref.null)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(push) ; 13
; [then-branch 63] $t@170 != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 13
; [dead else-branch 63] $t@170 == Null
(pop) ; 12
(set-option :timeout 0)
(push) ; 12
(assert (not (implies
  (not (= $t@170 $Ref.null))
  (<=
    ($prio $Snap.unit $t@169)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@178 $t@170) 0))))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(assert (implies
  (not (= $t@170 $Ref.null))
  (<=
    ($prio $Snap.unit $t@169)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@178 $t@170) 0)))))
; [eval] xs.next != null
(set-option :timeout 250)
(push) ; 12
(assert (not (= $t@170 $Ref.null)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(push) ; 12
; [then-branch 64] $t@170 != Null
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 13
(push) ; 14
(assert (not (= $t@170 $Ref.null)))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
(push) ; 14
; [then-branch 65] $t@170 != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 14
; [dead else-branch 65] $t@170 == Null
(pop) ; 13
(set-option :timeout 0)
(push) ; 13
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(push) ; 13
(assert (not (=
  ($peek ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@169)
    ($Snap.combine
      ($SortWrappers.$RefTo$Snap $t@170)
      ($Snap.combine $t@178 $Snap.unit))) crt@157)
  ($Seq.index ($content $t@63 xs@55) i@155))))
(check-sat)
; unsat
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(assert (=
  ($peek ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@169)
    ($Snap.combine
      ($SortWrappers.$RefTo$Snap $t@170)
      ($Snap.combine $t@178 $Snap.unit))) crt@157)
  ($Seq.index ($content $t@63 xs@55) i@155)))
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(declare-const $t@179 $Snap)
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(declare-const $t@180 $Snap)
(declare-const $t@181 $Snap)
(declare-const $t@182 $Snap)
(assert (= $t@181 ($Snap.combine $t@182 $Snap.unit)))
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(assert ($Seq.equal
  ($nodesContent $t@182 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) i@155) 0)
    ($nodesContent ($Snap.combine
      ($SortWrappers.$RefTo$Snap $t@169)
      ($Snap.combine
        ($SortWrappers.$RefTo$Snap $t@170)
        ($Snap.combine $t@178 $Snap.unit))) crt@157))))
(push) ; 13
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 13
; 0.63s
; (get-info :all-statistics)
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(push) ; 13
(assert (not ($Seq.equal
  ($nodesContent $t@182 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) (+ i@155 1)) 0)
    ($nodesContent $t@178 nxt@156)))))
(check-sat)
; unsat
(pop) ; 13
; 0.03s
; (get-info :all-statistics)
(assert ($Seq.equal
  ($nodesContent $t@182 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) (+ i@155 1)) 0)
    ($nodesContent $t@178 nxt@156))))
(declare-const $t@183 $Snap)
(declare-const $t@184 $Snap)
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 12
; [dead else-branch 64] $t@170 == Null
(pop) ; 11
; [dead else-branch 62] $t@170 == Null
(pop) ; 10
; [eval] (0 <= i) && (i < |old(content(xs))|)
; [eval] 0 <= i
(push) ; 10
(set-option :timeout 250)
(push) ; 11
(assert (not (not (<= 0 (+ i@155 1)))))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (<= 0 (+ i@155 1))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 66] 0 <= i@155 + 1
(assert (<= 0 (+ i@155 1)))
; [eval] i < |old(content(xs))|
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 11
; [dead else-branch 66] !0 <= i@155 + 1
(pop) ; 10
(set-option :timeout 0)
(push) ; 10
(assert (not (and (<= 0 (+ i@155 1)) (< (+ i@155 1) ($Seq.length ($content $t@63 xs@55))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 (+ i@155 1)) (< (+ i@155 1) ($Seq.length ($content $t@63 xs@55)))))
; [eval] (nxt == null) ==> (i == |old(content(xs))| - 1)
; [eval] nxt == null
(push) ; 10
; [dead then-branch 67] $t@174 == Null
(push) ; 11
; [else-branch 67] $t@174 != Null
(pop) ; 11
(pop) ; 10
; [eval] nxt == crt.next
; [eval] crt.data == old(content(xs))[i]
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(push) ; 10
(assert (not (= $t@172 ($Seq.index ($content $t@63 xs@55) (+ i@155 1)))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(assert (= $t@172 ($Seq.index ($content $t@63 xs@55) (+ i@155 1))))
; [eval] nxt != null
(set-option :timeout 250)
(push) ; 10
(assert (not (= $t@174 $Ref.null)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 68] $t@174 != Null
; [eval] nodesContent(nxt) == old(content(xs))[i + 1..]
; [eval] nodesContent(nxt)
; [eval] old(content(xs))[i + 1..]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] i + 1
(set-option :timeout 0)
(push) ; 11
(assert (not ($Seq.equal
  ($nodesContent $t@176 $t@174)
  ($Seq.drop ($content $t@63 xs@55) (+ (+ i@155 1) 1)))))
(check-sat)
; unsat
(pop) ; 11
; 0.01s
; (get-info :all-statistics)
(assert ($Seq.equal
  ($nodesContent $t@176 $t@174)
  ($Seq.drop ($content $t@63 xs@55) (+ (+ i@155 1) 1))))
; [eval] prio(crt.data) < prio(x)
; [eval] prio(crt.data)
; [eval] prio(x)
(push) ; 11
(assert (not (< ($prio $Snap.unit $t@172) ($prio $Snap.unit x@56))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(assert (< ($prio $Snap.unit $t@172) ($prio $Snap.unit x@56)))
; [eval] (nxt != null) ==> (prio(crt.data) <= prio(peek(nxt)))
; [eval] nxt != null
(push) ; 11
(set-option :timeout 250)
(push) ; 12
(assert (not (= $t@174 $Ref.null)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(push) ; 12
; [then-branch 69] $t@174 != Null
; [eval] prio(crt.data) <= prio(peek(nxt))
; [eval] prio(crt.data)
; [eval] prio(peek(nxt))
; [eval] peek(nxt)
(pop) ; 12
; [dead else-branch 69] $t@174 == Null
(pop) ; 11
(set-option :timeout 0)
(push) ; 11
(assert (not (implies
  (not (= $t@174 $Ref.null))
  (<= ($prio $Snap.unit $t@172) ($prio $Snap.unit ($peek $t@176 $t@174))))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(assert (implies
  (not (= $t@174 $Ref.null))
  (<= ($prio $Snap.unit $t@172) ($prio $Snap.unit ($peek $t@176 $t@174)))))
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(push) ; 11
(assert (not (and (= nxt@156 crt@157) (= (+ i@155 1) i@155))))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(declare-const $t@185 $Snap)
(pop) ; 10
; [dead else-branch 68] $t@174 == Null
(pop) ; 9
(push) ; 9
; [else-branch 60] $t@174 == Null
(assert (= $t@174 $Ref.null))
; [eval] (nxt.next != null) ==> (prio(nxt.data) <= prio(nodesContent(nxt.next)[0]))
; [eval] nxt.next != null
(push) ; 10
; [dead then-branch 70] $t@174 != Null
(push) ; 11
; [else-branch 70] $t@174 == Null
(pop) ; 11
(pop) ; 10
; [exec]
; crt := nxt
; [exec]
; nxt := nxt.next
; [exec]
; i := i + 1
; [eval] i + 1
; [exec]
; package acc(PQueue(crt), write) && (peek(crt) == old(content(xs))[i]) --* (folding acc(PQueue(prev), write) in (applying w in acc(PQueue(hd), write) && (nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt)))))
(push) ; 10
(declare-const $t@186 $Snap)
(declare-const $t@187 $Snap)
(assert (= $t@186 ($Snap.combine $t@187 $Snap.unit)))
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= ($peek $t@187 nxt@156) ($Seq.index ($content $t@63 xs@55) (+ i@155 1))))
(push) ; 11
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
; [eval] xs.next != null
(set-option :timeout 250)
(push) ; 11
(assert (not (= $t@170 $Ref.null)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (not (= $t@170 $Ref.null))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 71] $t@170 != Null
(assert (not (= $t@170 $Ref.null)))
(set-option :timeout 0)
(push) ; 12
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(push) ; 12
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 12
(set-option :timeout 250)
(push) ; 13
(assert (not (= $t@170 $Ref.null)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(push) ; 13
; [then-branch 72] $t@170 != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 13
; [dead else-branch 72] $t@170 == Null
(pop) ; 12
(set-option :timeout 0)
(push) ; 12
(assert (not (implies
  (not (= $t@170 $Ref.null))
  (<=
    ($prio $Snap.unit $t@169)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@187 $t@170) 0))))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(assert (implies
  (not (= $t@170 $Ref.null))
  (<=
    ($prio $Snap.unit $t@169)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@187 $t@170) 0)))))
; [eval] xs.next != null
(set-option :timeout 250)
(push) ; 12
(assert (not (= $t@170 $Ref.null)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(push) ; 12
; [then-branch 73] $t@170 != Null
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 13
(push) ; 14
(assert (not (= $t@170 $Ref.null)))
(check-sat)
; unknown
(pop) ; 14
; 0.00s
; (get-info :all-statistics)
(push) ; 14
; [then-branch 74] $t@170 != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 14
; [dead else-branch 74] $t@170 == Null
(pop) ; 13
(set-option :timeout 0)
(push) ; 13
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(push) ; 13
(assert (not (=
  ($peek ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@169)
    ($Snap.combine
      ($SortWrappers.$RefTo$Snap $t@170)
      ($Snap.combine $t@187 $Snap.unit))) crt@157)
  ($Seq.index ($content $t@63 xs@55) i@155))))
(check-sat)
; unsat
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(assert (=
  ($peek ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@169)
    ($Snap.combine
      ($SortWrappers.$RefTo$Snap $t@170)
      ($Snap.combine $t@187 $Snap.unit))) crt@157)
  ($Seq.index ($content $t@63 xs@55) i@155)))
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(declare-const $t@188 $Snap)
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(declare-const $t@189 $Snap)
(declare-const $t@190 $Snap)
(declare-const $t@191 $Snap)
(assert (= $t@190 ($Snap.combine $t@191 $Snap.unit)))
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(assert ($Seq.equal
  ($nodesContent $t@191 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) i@155) 0)
    ($nodesContent ($Snap.combine
      ($SortWrappers.$RefTo$Snap $t@169)
      ($Snap.combine
        ($SortWrappers.$RefTo$Snap $t@170)
        ($Snap.combine $t@187 $Snap.unit))) crt@157))))
(push) ; 13
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 13
; 0.02s
; (get-info :all-statistics)
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(push) ; 13
(assert (not ($Seq.equal
  ($nodesContent $t@191 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) (+ i@155 1)) 0)
    ($nodesContent $t@187 nxt@156)))))
(check-sat)
; unsat
(pop) ; 13
; 0.06s
; (get-info :all-statistics)
(assert ($Seq.equal
  ($nodesContent $t@191 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) (+ i@155 1)) 0)
    ($nodesContent $t@187 nxt@156))))
(declare-const $t@192 $Snap)
(declare-const $t@193 $Snap)
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 12
; [dead else-branch 73] $t@170 == Null
(pop) ; 11
; [dead else-branch 71] $t@170 == Null
(pop) ; 10
; [eval] (0 <= i) && (i < |old(content(xs))|)
; [eval] 0 <= i
(push) ; 10
(set-option :timeout 250)
(push) ; 11
(assert (not (not (<= 0 (+ i@155 1)))))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (<= 0 (+ i@155 1))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 75] 0 <= i@155 + 1
(assert (<= 0 (+ i@155 1)))
; [eval] i < |old(content(xs))|
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 11
; [dead else-branch 75] !0 <= i@155 + 1
(pop) ; 10
(set-option :timeout 0)
(push) ; 10
(assert (not (and (<= 0 (+ i@155 1)) (< (+ i@155 1) ($Seq.length ($content $t@63 xs@55))))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 (+ i@155 1)) (< (+ i@155 1) ($Seq.length ($content $t@63 xs@55)))))
; [eval] (nxt == null) ==> (i == |old(content(xs))| - 1)
; [eval] nxt == null
(push) ; 10
(set-option :timeout 250)
(push) ; 11
(assert (not (not (= $t@174 $Ref.null))))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 76] $t@174 == Null
; [eval] i == |old(content(xs))| - 1
; [eval] |old(content(xs))| - 1
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 11
; [dead else-branch 76] $t@174 != Null
(pop) ; 10
(set-option :timeout 0)
(push) ; 10
(assert (not (implies
  (= $t@174 $Ref.null)
  (= (+ i@155 1) (- ($Seq.length ($content $t@63 xs@55)) 1)))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(assert (implies
  (= $t@174 $Ref.null)
  (= (+ i@155 1) (- ($Seq.length ($content $t@63 xs@55)) 1))))
; [eval] nxt == crt.next
; [eval] crt.data == old(content(xs))[i]
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(push) ; 10
(assert (not (= $t@172 ($Seq.index ($content $t@63 xs@55) (+ i@155 1)))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(assert (= $t@172 ($Seq.index ($content $t@63 xs@55) (+ i@155 1))))
; [eval] nxt != null
; [dead then-branch 77] $t@174 != Null
(push) ; 10
; [else-branch 77] $t@174 == Null
; [eval] prio(crt.data) < prio(x)
; [eval] prio(crt.data)
; [eval] prio(x)
(push) ; 11
(assert (not (< ($prio $Snap.unit $t@172) ($prio $Snap.unit x@56))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(assert (< ($prio $Snap.unit $t@172) ($prio $Snap.unit x@56)))
; [eval] (nxt != null) ==> (prio(crt.data) <= prio(peek(nxt)))
; [eval] nxt != null
(push) ; 11
; [dead then-branch 78] $t@174 != Null
(push) ; 12
; [else-branch 78] $t@174 == Null
(pop) ; 12
(pop) ; 11
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(push) ; 11
(assert (not (and (= nxt@156 crt@157) (= (+ i@155 1) i@155))))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(declare-const $t@194 $Snap)
(pop) ; 10
(pop) ; 9
(pop) ; 8
(push) ; 8
; [else-branch 57] nxt@156 == Null
(assert (= nxt@156 $Ref.null))
; [eval] prio(crt.data) < prio(x)
; [eval] prio(crt.data)
; [eval] prio(x)
(assert (< ($prio $Snap.unit $t@169) ($prio $Snap.unit x@56)))
; [eval] (nxt != null) ==> (prio(crt.data) <= prio(peek(nxt)))
; [eval] nxt != null
(push) ; 9
; [dead then-branch 79] nxt@156 != Null
(push) ; 10
; [else-branch 79] nxt@156 == Null
(pop) ; 10
(pop) ; 9
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] (nxt != null) && (prio(peek(nxt)) < prio(x))
; [eval] nxt != null
(push) ; 9
; [dead then-branch 80] nxt@156 != Null
(push) ; 10
; [else-branch 80] nxt@156 == Null
(pop) ; 10
(pop) ; 9
(assert (not (= nxt@156 $Ref.null)))
(set-option :timeout 250)
(check-sat)
; unsat
(pop) ; 8
(pop) ; 7
(push) ; 7
; Establish loop invariant
; [eval] (0 <= i) && (i < |old(content(xs))|)
; [eval] 0 <= i
(push) ; 8
(push) ; 9
(assert (not false))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 81] True
; [eval] i < |old(content(xs))|
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 9
; [dead else-branch 81] False
(pop) ; 8
(set-option :timeout 0)
(push) ; 8
(assert (not (< 0 ($Seq.length ($content $t@63 xs@55)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert (< 0 ($Seq.length ($content $t@63 xs@55))))
; [eval] (nxt == null) ==> (i == |old(content(xs))| - 1)
; [eval] nxt == null
(push) ; 8
; [dead then-branch 82] $t@149 == Null
(push) ; 9
; [else-branch 82] $t@149 != Null
(pop) ; 9
(pop) ; 8
; [eval] nxt == crt.next
; [eval] crt.data == old(content(xs))[i]
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(push) ; 8
(assert (not (= $t@147 ($Seq.index ($content $t@63 xs@55) 0))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert (= $t@147 ($Seq.index ($content $t@63 xs@55) 0)))
; [eval] nxt != null
(set-option :timeout 250)
(push) ; 8
(assert (not (= $t@149 $Ref.null)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 83] $t@149 != Null
; [eval] nodesContent(nxt) == old(content(xs))[i + 1..]
; [eval] nodesContent(nxt)
; [eval] old(content(xs))[i + 1..]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] i + 1
(set-option :timeout 0)
(push) ; 9
(assert (not ($Seq.equal ($nodesContent $t@151 $t@149) ($Seq.drop ($content $t@63 xs@55) 1))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(assert ($Seq.equal ($nodesContent $t@151 $t@149) ($Seq.drop ($content $t@63 xs@55) 1)))
; [eval] prio(crt.data) < prio(x)
; [eval] prio(crt.data)
; [eval] prio(x)
(push) ; 9
(assert (not (< ($prio $Snap.unit $t@147) ($prio $Snap.unit x@56))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(assert (< ($prio $Snap.unit $t@147) ($prio $Snap.unit x@56)))
; [eval] (nxt != null) ==> (prio(crt.data) <= prio(peek(nxt)))
; [eval] nxt != null
(push) ; 9
(set-option :timeout 250)
(push) ; 10
(assert (not (= $t@149 $Ref.null)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 84] $t@149 != Null
; [eval] prio(crt.data) <= prio(peek(nxt))
; [eval] prio(crt.data)
; [eval] prio(peek(nxt))
; [eval] peek(nxt)
(pop) ; 10
; [dead else-branch 84] $t@149 == Null
(pop) ; 9
(set-option :timeout 0)
(push) ; 9
(assert (not (implies
  (not (= $t@149 $Ref.null))
  (<= ($prio $Snap.unit $t@147) ($prio $Snap.unit ($peek $t@151 $t@149))))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(assert (implies
  (not (= $t@149 $Ref.null))
  (<= ($prio $Snap.unit $t@147) ($prio $Snap.unit ($peek $t@151 $t@149)))))
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(declare-const $t@195 $Snap)
; Continue after loop
(declare-const $t@196 $Snap)
(declare-const $t@197 $Snap)
(assert (= $t@196 ($Snap.combine $t@197 $Snap.unit)))
(declare-const $t@198 $Snap)
(declare-const $t@199 $Snap)
(assert (= $t@197 ($Snap.combine $t@198 $t@199)))
(declare-const $t@200 $Snap)
(assert (= $t@198 ($Snap.combine $t@200 $Snap.unit)))
(declare-const $t@201 $Snap)
(assert (= $t@200 ($Snap.combine $t@201 $Snap.unit)))
(declare-const $t@202 $Snap)
(declare-const $t@203 $Snap)
(assert (= $t@201 ($Snap.combine $t@202 $t@203)))
(declare-const $t@204 $Snap)
(assert (= $t@202 ($Snap.combine $t@204 $Snap.unit)))
(declare-const $t@205 $Snap)
(assert (= $t@204 ($Snap.combine $t@205 $Snap.unit)))
(declare-const $t@206 $Snap)
(assert (= $t@205 ($Snap.combine $Snap.unit $t@206)))
; [eval] (0 <= i) && (i < |old(content(xs))|) && ((nxt == null) ==> (i == |old(content(xs))| - 1))
; [eval] (0 <= i) && (i < |old(content(xs))|)
; [eval] 0 <= i
(push) ; 9
(set-option :timeout 250)
(push) ; 10
(assert (not (not (<= 0 i@155))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
(assert (not (<= 0 i@155)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 85] 0 <= i@155
(assert (<= 0 i@155))
; [eval] i < |old(content(xs))|
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 10
(push) ; 10
; [else-branch 85] !0 <= i@155
(assert (not (<= 0 i@155)))
(pop) ; 10
(pop) ; 9
(push) ; 9
(push) ; 10
(assert (not (not (and (<= 0 i@155) (< i@155 ($Seq.length ($content $t@63 xs@55)))))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
(assert (not (and (<= 0 i@155) (< i@155 ($Seq.length ($content $t@63 xs@55))))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 86] 0 <= i@155 && i@155 < |content(xs@55;$t@63)|
(assert (and (<= 0 i@155) (< i@155 ($Seq.length ($content $t@63 xs@55)))))
; [eval] (nxt == null) ==> (i == |old(content(xs))| - 1)
; [eval] nxt == null
(push) ; 11
(push) ; 12
(assert (not (not (= nxt@156 $Ref.null))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(push) ; 12
(assert (not (= nxt@156 $Ref.null)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(push) ; 12
; [then-branch 87] nxt@156 == Null
(assert (= nxt@156 $Ref.null))
; [eval] i == |old(content(xs))| - 1
; [eval] |old(content(xs))| - 1
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 12
(push) ; 12
; [else-branch 87] nxt@156 != Null
(assert (not (= nxt@156 $Ref.null)))
(pop) ; 12
(pop) ; 11
(pop) ; 10
(push) ; 10
; [else-branch 86] !0 <= i@155 && i@155 < |content(xs@55;$t@63)|
(assert (not (and (<= 0 i@155) (< i@155 ($Seq.length ($content $t@63 xs@55))))))
(pop) ; 10
(pop) ; 9
(assert (and
  (and (<= 0 i@155) (< i@155 ($Seq.length ($content $t@63 xs@55))))
  (implies
    (= nxt@156 $Ref.null)
    (= i@155 (- ($Seq.length ($content $t@63 xs@55)) 1)))))
(declare-const $t@207 $Ref)
(declare-const $t@208 $Ref)
(assert (=
  $t@206
  ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@207)
    ($SortWrappers.$RefTo$Snap $t@208))))
(set-option :timeout 0)
(push) ; 9
(assert (not (= crt@157 $Ref.null)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(assert (not (= crt@157 $Ref.null)))
(push) ; 9
(assert (not (= crt@157 $Ref.null)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [eval] nxt == crt.next
(assert (= nxt@156 $t@208))
; [eval] crt.data == old(content(xs))[i]
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= $t@207 ($Seq.index ($content $t@63 xs@55) i@155)))
; [eval] nxt != null
(set-option :timeout 250)
(push) ; 9
(assert (not (= nxt@156 $Ref.null)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (not (= nxt@156 $Ref.null))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 88] nxt@156 != Null
(assert (not (= nxt@156 $Ref.null)))
(declare-const $t@209 $Snap)
(assert (= $t@203 ($Snap.combine $t@209 $Snap.unit)))
; [eval] nodesContent(nxt) == old(content(xs))[i + 1..]
; [eval] nodesContent(nxt)
; [eval] old(content(xs))[i + 1..]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] i + 1
(assert ($Seq.equal
  ($nodesContent $t@209 nxt@156)
  ($Seq.drop ($content $t@63 xs@55) (+ i@155 1))))
; [eval] prio(crt.data) < prio(x)
; [eval] prio(crt.data)
; [eval] prio(x)
(assert (< ($prio $Snap.unit $t@207) ($prio $Snap.unit x@56)))
; [eval] (nxt != null) ==> (prio(crt.data) <= prio(peek(nxt)))
; [eval] nxt != null
(push) ; 10
(push) ; 11
(assert (not (= nxt@156 $Ref.null)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 89] nxt@156 != Null
; [eval] prio(crt.data) <= prio(peek(nxt))
; [eval] prio(crt.data)
; [eval] prio(peek(nxt))
; [eval] peek(nxt)
(pop) ; 11
; [dead else-branch 89] nxt@156 == Null
(pop) ; 10
(assert (implies
  (not (= nxt@156 $Ref.null))
  (<= ($prio $Snap.unit $t@207) ($prio $Snap.unit ($peek $t@209 nxt@156)))))
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] !((nxt != null) && (prio(peek(nxt)) < prio(x)))
; [eval] (nxt != null) && (prio(peek(nxt)) < prio(x))
; [eval] nxt != null
(push) ; 10
(push) ; 11
(assert (not (= nxt@156 $Ref.null)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 90] nxt@156 != Null
; [eval] prio(peek(nxt)) < prio(x)
; [eval] prio(peek(nxt))
; [eval] peek(nxt)
; [eval] prio(x)
(pop) ; 11
; [dead else-branch 90] nxt@156 == Null
(pop) ; 10
(assert (not
  (and
    (not (= nxt@156 $Ref.null))
    (< ($prio $Snap.unit ($peek $t@209 nxt@156)) ($prio $Snap.unit x@56)))))
(check-sat)
; unknown
; [exec]
; node := new(data, next)
(declare-const node@210 $Ref)
(assert (not (= node@210 $Ref.null)))
(declare-const data@211 $Ref)
(declare-const next@212 $Ref)
(assert (and
  (not (= xs@55 node@210))
  (not (= x@56 node@210))
  (not (= tmp@58 node@210))
  (not (= $t@130 node@210))
  (not (= prev@154 node@210))
  (not (= nxt@156 node@210))
  (not (= crt@157 node@210))
  (not (= data@211 node@210))
  (not (= next@212 node@210))
  (not (= $t@207 node@210))
  (not (= $t@208 node@210))))
; [exec]
; node.data := x
; [exec]
; node.next := nxt
; [exec]
; fold acc(PQueue(node), write)
; [eval] xs.next != null
(push) ; 10
(assert (not (= nxt@156 $Ref.null)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 91] nxt@156 != Null
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 11
(push) ; 12
(assert (not (= nxt@156 $Ref.null)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(push) ; 12
; [then-branch 92] nxt@156 != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 12
; [dead else-branch 92] nxt@156 == Null
(pop) ; 11
(set-option :timeout 0)
(push) ; 11
(assert (not (implies
  (not (= nxt@156 $Ref.null))
  (<=
    ($prio $Snap.unit x@56)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@209 nxt@156) 0))))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(assert (implies
  (not (= nxt@156 $Ref.null))
  (<=
    ($prio $Snap.unit x@56)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@209 nxt@156) 0)))))
; [exec]
; crt.next := node
; [exec]
; fold acc(PQueue(crt), write)
; [eval] xs.next != null
(set-option :timeout 250)
(push) ; 11
(assert (not (= node@210 $Ref.null)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 93] node@210 != Null
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 12
(push) ; 13
(assert (not (= node@210 $Ref.null)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(push) ; 13
; [then-branch 94] node@210 != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 13
; [dead else-branch 94] node@210 == Null
(pop) ; 12
(set-option :timeout 0)
(push) ; 12
(assert (not (implies
  (not (= node@210 $Ref.null))
  (<=
    ($prio $Snap.unit $t@207)
    ($prio $Snap.unit ($Seq.index
      ($nodesContent ($Snap.combine
        ($SortWrappers.$RefTo$Snap x@56)
        ($Snap.combine
          ($SortWrappers.$RefTo$Snap nxt@156)
          ($Snap.combine $t@209 $Snap.unit))) node@210)
      0))))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(assert (implies
  (not (= node@210 $Ref.null))
  (<=
    ($prio $Snap.unit $t@207)
    ($prio $Snap.unit ($Seq.index
      ($nodesContent ($Snap.combine
        ($SortWrappers.$RefTo$Snap x@56)
        ($Snap.combine
          ($SortWrappers.$RefTo$Snap nxt@156)
          ($Snap.combine $t@209 $Snap.unit))) node@210)
      0)))))
; [exec]
; apply acc(PQueue(crt), write) && (peek(crt) == old(content(xs))[i]) --* acc(PQueue(hd), write) && (nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt)))
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(declare-const $t@213 $Snap)
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(push) ; 12
(assert (not (=
  ($peek ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@207)
    ($Snap.combine
      ($SortWrappers.$RefTo$Snap node@210)
      ($Snap.combine
        ($Snap.combine
          ($SortWrappers.$RefTo$Snap x@56)
          ($Snap.combine
            ($SortWrappers.$RefTo$Snap nxt@156)
            ($Snap.combine $t@209 $Snap.unit)))
        $Snap.unit))) crt@157)
  ($Seq.index ($content $t@63 xs@55) i@155))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(assert (=
  ($peek ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@207)
    ($Snap.combine
      ($SortWrappers.$RefTo$Snap node@210)
      ($Snap.combine
        ($Snap.combine
          ($SortWrappers.$RefTo$Snap x@56)
          ($Snap.combine
            ($SortWrappers.$RefTo$Snap nxt@156)
            ($Snap.combine $t@209 $Snap.unit)))
        $Snap.unit))) crt@157)
  ($Seq.index ($content $t@63 xs@55) i@155)))
(declare-const $t@214 $Snap)
(declare-const $t@215 $Snap)
(assert (= $t@214 ($Snap.combine $t@215 $Snap.unit)))
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(assert ($Seq.equal
  ($nodesContent $t@215 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) i@155) 0)
    ($nodesContent ($Snap.combine
      ($SortWrappers.$RefTo$Snap $t@207)
      ($Snap.combine
        ($SortWrappers.$RefTo$Snap node@210)
        ($Snap.combine
          ($Snap.combine
            ($SortWrappers.$RefTo$Snap x@56)
            ($Snap.combine
              ($SortWrappers.$RefTo$Snap nxt@156)
              ($Snap.combine $t@209 $Snap.unit)))
          $Snap.unit))) crt@157))))
(push) ; 12
(pop) ; 12
; [exec]
; i := i + 1
; [eval] i + 1
; [exec]
; fold acc(List(xs), write)
; [eval] xs.head != null
(set-option :timeout 250)
(push) ; 12
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(push) ; 12
; [then-branch 95] $t@130 != Null
; [eval] content(xs) == old(content(xs))[0..i] ++ Seq(x) ++ old(content(xs))[i..]
; [eval] content(xs)
; [eval] old(content(xs))[0..i] ++ Seq(x) ++ old(content(xs))[i..]
; [eval] old(content(xs))[0..i] ++ Seq(x)
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] Seq(x)
(assert (= ($Seq.length ($Seq.singleton x@56)) 1))
; [eval] old(content(xs))[i..]
; [eval] old(content(xs))
; [eval] content(xs)
(set-option :timeout 0)
(push) ; 13
(assert (not ($Seq.equal
  ($content ($Snap.combine ($SortWrappers.$RefTo$Snap $t@130) $t@215) xs@55)
  ($Seq.append
    ($Seq.append
      ($Seq.drop ($Seq.take ($content $t@63 xs@55) (+ i@155 1)) 0)
      ($Seq.singleton x@56))
    ($Seq.drop ($content $t@63 xs@55) (+ i@155 1))))))
(check-sat)
; unsat
(pop) ; 13
; 1.11s
; (get-info :all-statistics)
(assert ($Seq.equal
  ($content ($Snap.combine ($SortWrappers.$RefTo$Snap $t@130) $t@215) xs@55)
  ($Seq.append
    ($Seq.append
      ($Seq.drop ($Seq.take ($content $t@63 xs@55) (+ i@155 1)) 0)
      ($Seq.singleton x@56))
    ($Seq.drop ($content $t@63 xs@55) (+ i@155 1)))))
(pop) ; 12
; [dead else-branch 95] $t@130 == Null
(pop) ; 11
; [dead else-branch 93] node@210 == Null
(pop) ; 10
; [dead else-branch 91] nxt@156 == Null
(pop) ; 9
(push) ; 9
; [else-branch 88] nxt@156 == Null
(assert (= nxt@156 $Ref.null))
; [eval] prio(crt.data) < prio(x)
; [eval] prio(crt.data)
; [eval] prio(x)
(assert (< ($prio $Snap.unit $t@207) ($prio $Snap.unit x@56)))
; [eval] (nxt != null) ==> (prio(crt.data) <= prio(peek(nxt)))
; [eval] nxt != null
(push) ; 10
; [dead then-branch 96] nxt@156 != Null
(push) ; 11
; [else-branch 96] nxt@156 == Null
(pop) ; 11
(pop) ; 10
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] !((nxt != null) && (prio(peek(nxt)) < prio(x)))
; [eval] (nxt != null) && (prio(peek(nxt)) < prio(x))
; [eval] nxt != null
(push) ; 10
; [dead then-branch 97] nxt@156 != Null
(push) ; 11
; [else-branch 97] nxt@156 == Null
(pop) ; 11
(pop) ; 10
(set-option :timeout 250)
(check-sat)
; unknown
; [exec]
; node := new(data, next)
(declare-const node@216 $Ref)
(assert (not (= node@216 $Ref.null)))
(declare-const data@217 $Ref)
(declare-const next@218 $Ref)
(assert (and
  (not (= xs@55 node@216))
  (not (= x@56 node@216))
  (not (= tmp@58 node@216))
  (not (= $t@130 node@216))
  (not (= prev@154 node@216))
  (not (= nxt@156 node@216))
  (not (= crt@157 node@216))
  (not (= data@217 node@216))
  (not (= next@218 node@216))
  (not (= $t@207 node@216))
  (not (= $t@208 node@216))))
; [exec]
; node.data := x
; [exec]
; node.next := nxt
; [exec]
; fold acc(PQueue(node), write)
; [eval] xs.next != null
; [dead then-branch 98] nxt@156 != Null
(push) ; 10
; [else-branch 98] nxt@156 == Null
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 11
; [dead then-branch 99] nxt@156 != Null
(push) ; 12
; [else-branch 99] nxt@156 == Null
(pop) ; 12
(pop) ; 11
; [exec]
; crt.next := node
; [exec]
; fold acc(PQueue(crt), write)
; [eval] xs.next != null
(push) ; 11
(assert (not (= node@216 $Ref.null)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 100] node@216 != Null
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 12
(push) ; 13
(assert (not (= node@216 $Ref.null)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(push) ; 13
; [then-branch 101] node@216 != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 13
; [dead else-branch 101] node@216 == Null
(pop) ; 12
(set-option :timeout 0)
(push) ; 12
(assert (not (implies
  (not (= node@216 $Ref.null))
  (<=
    ($prio $Snap.unit $t@207)
    ($prio $Snap.unit ($Seq.index
      ($nodesContent ($Snap.combine
        ($SortWrappers.$RefTo$Snap x@56)
        ($Snap.combine
          ($SortWrappers.$RefTo$Snap nxt@156)
          ($Snap.combine $Snap.unit $Snap.unit))) node@216)
      0))))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(assert (implies
  (not (= node@216 $Ref.null))
  (<=
    ($prio $Snap.unit $t@207)
    ($prio $Snap.unit ($Seq.index
      ($nodesContent ($Snap.combine
        ($SortWrappers.$RefTo$Snap x@56)
        ($Snap.combine
          ($SortWrappers.$RefTo$Snap nxt@156)
          ($Snap.combine $Snap.unit $Snap.unit))) node@216)
      0)))))
; [exec]
; apply acc(PQueue(crt), write) && (peek(crt) == old(content(xs))[i]) --* acc(PQueue(hd), write) && (nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt)))
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(declare-const $t@219 $Snap)
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(push) ; 12
(assert (not (=
  ($peek ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@207)
    ($Snap.combine
      ($SortWrappers.$RefTo$Snap node@216)
      ($Snap.combine
        ($Snap.combine
          ($SortWrappers.$RefTo$Snap x@56)
          ($Snap.combine
            ($SortWrappers.$RefTo$Snap nxt@156)
            ($Snap.combine $Snap.unit $Snap.unit)))
        $Snap.unit))) crt@157)
  ($Seq.index ($content $t@63 xs@55) i@155))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(assert (=
  ($peek ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@207)
    ($Snap.combine
      ($SortWrappers.$RefTo$Snap node@216)
      ($Snap.combine
        ($Snap.combine
          ($SortWrappers.$RefTo$Snap x@56)
          ($Snap.combine
            ($SortWrappers.$RefTo$Snap nxt@156)
            ($Snap.combine $Snap.unit $Snap.unit)))
        $Snap.unit))) crt@157)
  ($Seq.index ($content $t@63 xs@55) i@155)))
(declare-const $t@220 $Snap)
(declare-const $t@221 $Snap)
(assert (= $t@220 ($Snap.combine $t@221 $Snap.unit)))
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(assert ($Seq.equal
  ($nodesContent $t@221 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) i@155) 0)
    ($nodesContent ($Snap.combine
      ($SortWrappers.$RefTo$Snap $t@207)
      ($Snap.combine
        ($SortWrappers.$RefTo$Snap node@216)
        ($Snap.combine
          ($Snap.combine
            ($SortWrappers.$RefTo$Snap x@56)
            ($Snap.combine
              ($SortWrappers.$RefTo$Snap nxt@156)
              ($Snap.combine $Snap.unit $Snap.unit)))
          $Snap.unit))) crt@157))))
(push) ; 12
(pop) ; 12
; [exec]
; i := i + 1
; [eval] i + 1
; [exec]
; fold acc(List(xs), write)
; [eval] xs.head != null
(set-option :timeout 250)
(push) ; 12
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 12
; 0.01s
; (get-info :all-statistics)
(push) ; 12
; [then-branch 102] $t@130 != Null
; [eval] content(xs) == old(content(xs))[0..i] ++ Seq(x) ++ old(content(xs))[i..]
; [eval] content(xs)
; [eval] old(content(xs))[0..i] ++ Seq(x) ++ old(content(xs))[i..]
; [eval] old(content(xs))[0..i] ++ Seq(x)
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] Seq(x)
(assert (= ($Seq.length ($Seq.singleton x@56)) 1))
; [eval] old(content(xs))[i..]
; [eval] old(content(xs))
; [eval] content(xs)
(set-option :timeout 0)
(push) ; 13
(assert (not ($Seq.equal
  ($content ($Snap.combine ($SortWrappers.$RefTo$Snap $t@130) $t@221) xs@55)
  ($Seq.append
    ($Seq.append
      ($Seq.drop ($Seq.take ($content $t@63 xs@55) (+ i@155 1)) 0)
      ($Seq.singleton x@56))
    ($Seq.drop ($content $t@63 xs@55) (+ i@155 1))))))
(check-sat)
; unsat
(pop) ; 13
; 0.56s
; (get-info :all-statistics)
(assert ($Seq.equal
  ($content ($Snap.combine ($SortWrappers.$RefTo$Snap $t@130) $t@221) xs@55)
  ($Seq.append
    ($Seq.append
      ($Seq.drop ($Seq.take ($content $t@63 xs@55) (+ i@155 1)) 0)
      ($Seq.singleton x@56))
    ($Seq.drop ($content $t@63 xs@55) (+ i@155 1)))))
(pop) ; 12
; [dead else-branch 102] $t@130 == Null
(pop) ; 11
; [dead else-branch 100] node@216 == Null
(pop) ; 10
(pop) ; 9
(pop) ; 8
; [dead else-branch 83] $t@149 == Null
(pop) ; 7
(pop) ; 6
(push) ; 6
; [else-branch 52] $t@149 == Null
(assert (= $t@149 $Ref.null))
; [eval] (hd.next != null) ==> (prio(hd.data) <= prio(nodesContent(hd.next)[0]))
; [eval] hd.next != null
(push) ; 7
; [dead then-branch 103] $t@149 != Null
(push) ; 8
; [else-branch 103] $t@149 == Null
(pop) ; 8
(pop) ; 7
; [exec]
; crt := hd
; [exec]
; nxt := hd.next
; [exec]
; package acc(PQueue(crt), write) && (peek(crt) == old(content(xs))[i]) --* acc(PQueue(hd), write) && (nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt)))
(push) ; 7
(declare-const $t@222 $Snap)
(declare-const $t@223 $Snap)
(assert (= $t@222 ($Snap.combine $t@223 $Snap.unit)))
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= ($peek $t@223 $t@130) ($Seq.index ($content $t@63 xs@55) 0)))
(push) ; 8
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
(assert (not (< $Perm.Write $Perm.No)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(push) ; 8
(assert (not ($Seq.equal
  ($nodesContent $t@223 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) 0) 0)
    ($nodesContent $t@223 $t@130)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert ($Seq.equal
  ($nodesContent $t@223 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) 0) 0)
    ($nodesContent $t@223 $t@130))))
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 7
; loop at queue-magic-wands.sil,97:3
(declare-const prev@224 $Ref)
(declare-const i@225 Int)
(declare-const nxt@226 $Ref)
(declare-const crt@227 $Ref)
(push) ; 7
; Verify loop body
(declare-const $t@228 $Snap)
(declare-const $t@229 $Snap)
(assert (= $t@228 ($Snap.combine $t@229 $Snap.unit)))
(declare-const $t@230 $Snap)
(declare-const $t@231 $Snap)
(assert (= $t@229 ($Snap.combine $t@230 $t@231)))
(declare-const $t@232 $Snap)
(assert (= $t@230 ($Snap.combine $t@232 $Snap.unit)))
(declare-const $t@233 $Snap)
(assert (= $t@232 ($Snap.combine $t@233 $Snap.unit)))
(declare-const $t@234 $Snap)
(declare-const $t@235 $Snap)
(assert (= $t@233 ($Snap.combine $t@234 $t@235)))
(declare-const $t@236 $Snap)
(assert (= $t@234 ($Snap.combine $t@236 $Snap.unit)))
(declare-const $t@237 $Snap)
(assert (= $t@236 ($Snap.combine $t@237 $Snap.unit)))
(declare-const $t@238 $Snap)
(assert (= $t@237 ($Snap.combine $Snap.unit $t@238)))
; [eval] (0 <= i) && (i < |old(content(xs))|) && ((nxt == null) ==> (i == |old(content(xs))| - 1))
; [eval] (0 <= i) && (i < |old(content(xs))|)
; [eval] 0 <= i
(push) ; 8
(set-option :timeout 250)
(push) ; 9
(assert (not (not (<= 0 i@225))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (<= 0 i@225)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 104] 0 <= i@225
(assert (<= 0 i@225))
; [eval] i < |old(content(xs))|
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 9
(push) ; 9
; [else-branch 104] !0 <= i@225
(assert (not (<= 0 i@225)))
(pop) ; 9
(pop) ; 8
(push) ; 8
(push) ; 9
(assert (not (not (and (<= 0 i@225) (< i@225 ($Seq.length ($content $t@63 xs@55)))))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (and (<= 0 i@225) (< i@225 ($Seq.length ($content $t@63 xs@55))))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 105] 0 <= i@225 && i@225 < |content(xs@55;$t@63)|
(assert (and (<= 0 i@225) (< i@225 ($Seq.length ($content $t@63 xs@55)))))
; [eval] (nxt == null) ==> (i == |old(content(xs))| - 1)
; [eval] nxt == null
(push) ; 10
(push) ; 11
(assert (not (not (= nxt@226 $Ref.null))))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
(assert (not (= nxt@226 $Ref.null)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 106] nxt@226 == Null
(assert (= nxt@226 $Ref.null))
; [eval] i == |old(content(xs))| - 1
; [eval] |old(content(xs))| - 1
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 11
(push) ; 11
; [else-branch 106] nxt@226 != Null
(assert (not (= nxt@226 $Ref.null)))
(pop) ; 11
(pop) ; 10
(pop) ; 9
(push) ; 9
; [else-branch 105] !0 <= i@225 && i@225 < |content(xs@55;$t@63)|
(assert (not (and (<= 0 i@225) (< i@225 ($Seq.length ($content $t@63 xs@55))))))
(pop) ; 9
(pop) ; 8
(assert (and
  (and (<= 0 i@225) (< i@225 ($Seq.length ($content $t@63 xs@55))))
  (implies
    (= nxt@226 $Ref.null)
    (= i@225 (- ($Seq.length ($content $t@63 xs@55)) 1)))))
(declare-const $t@239 $Ref)
(declare-const $t@240 $Ref)
(assert (=
  $t@238
  ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@239)
    ($SortWrappers.$RefTo$Snap $t@240))))
(set-option :timeout 0)
(push) ; 8
(assert (not (= crt@227 $Ref.null)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert (not (= crt@227 $Ref.null)))
(push) ; 8
(assert (not (= crt@227 $Ref.null)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
; [eval] nxt == crt.next
(assert (= nxt@226 $t@240))
; [eval] crt.data == old(content(xs))[i]
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= $t@239 ($Seq.index ($content $t@63 xs@55) i@225)))
; [eval] nxt != null
(set-option :timeout 250)
(push) ; 8
(assert (not (= nxt@226 $Ref.null)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
(assert (not (not (= nxt@226 $Ref.null))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 107] nxt@226 != Null
(assert (not (= nxt@226 $Ref.null)))
(declare-const $t@241 $Snap)
(assert (= $t@235 ($Snap.combine $t@241 $Snap.unit)))
; [eval] nodesContent(nxt) == old(content(xs))[i + 1..]
; [eval] nodesContent(nxt)
; [eval] old(content(xs))[i + 1..]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] i + 1
(assert ($Seq.equal
  ($nodesContent $t@241 nxt@226)
  ($Seq.drop ($content $t@63 xs@55) (+ i@225 1))))
; [eval] prio(crt.data) < prio(x)
; [eval] prio(crt.data)
; [eval] prio(x)
(assert (< ($prio $Snap.unit $t@239) ($prio $Snap.unit x@56)))
; [eval] (nxt != null) ==> (prio(crt.data) <= prio(peek(nxt)))
; [eval] nxt != null
(push) ; 9
(push) ; 10
(assert (not (= nxt@226 $Ref.null)))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [dead then-branch 108] nxt@226 != Null
(push) ; 10
; [else-branch 108] nxt@226 == Null
(assert (= nxt@226 $Ref.null))
(pop) ; 10
(pop) ; 9
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] (nxt != null) && (prio(peek(nxt)) < prio(x))
; [eval] nxt != null
(push) ; 9
(push) ; 10
(assert (not (= nxt@226 $Ref.null)))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
; [dead then-branch 109] nxt@226 != Null
(push) ; 10
; [else-branch 109] nxt@226 == Null
(assert (= nxt@226 $Ref.null))
(pop) ; 10
(pop) ; 9
(check-sat)
; unsat
(pop) ; 8
(push) ; 8
; [else-branch 107] nxt@226 == Null
(assert (= nxt@226 $Ref.null))
; [eval] prio(crt.data) < prio(x)
; [eval] prio(crt.data)
; [eval] prio(x)
(assert (< ($prio $Snap.unit $t@239) ($prio $Snap.unit x@56)))
; [eval] (nxt != null) ==> (prio(crt.data) <= prio(peek(nxt)))
; [eval] nxt != null
(push) ; 9
; [dead then-branch 110] nxt@226 != Null
(push) ; 10
; [else-branch 110] nxt@226 == Null
(pop) ; 10
(pop) ; 9
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] (nxt != null) && (prio(peek(nxt)) < prio(x))
; [eval] nxt != null
(push) ; 9
; [dead then-branch 111] nxt@226 != Null
(push) ; 10
; [else-branch 111] nxt@226 == Null
(pop) ; 10
(pop) ; 9
(assert (not (= nxt@226 $Ref.null)))
(check-sat)
; unsat
(pop) ; 8
(pop) ; 7
(push) ; 7
; Establish loop invariant
; [eval] (0 <= i) && (i < |old(content(xs))|)
; [eval] 0 <= i
(push) ; 8
(push) ; 9
(assert (not false))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 112] True
; [eval] i < |old(content(xs))|
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 9
; [dead else-branch 112] False
(pop) ; 8
(set-option :timeout 0)
(push) ; 8
(assert (not (< 0 ($Seq.length ($content $t@63 xs@55)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert (< 0 ($Seq.length ($content $t@63 xs@55))))
; [eval] (nxt == null) ==> (i == |old(content(xs))| - 1)
; [eval] nxt == null
(push) ; 8
(set-option :timeout 250)
(push) ; 9
(assert (not (not (= $t@149 $Ref.null))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 113] $t@149 == Null
; [eval] i == |old(content(xs))| - 1
; [eval] |old(content(xs))| - 1
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 9
; [dead else-branch 113] $t@149 != Null
(pop) ; 8
(set-option :timeout 0)
(push) ; 8
(assert (not (implies (= $t@149 $Ref.null) (= 0 (- ($Seq.length ($content $t@63 xs@55)) 1)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert (implies (= $t@149 $Ref.null) (= 0 (- ($Seq.length ($content $t@63 xs@55)) 1))))
; [eval] nxt == crt.next
; [eval] crt.data == old(content(xs))[i]
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(push) ; 8
(assert (not (= $t@147 ($Seq.index ($content $t@63 xs@55) 0))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert (= $t@147 ($Seq.index ($content $t@63 xs@55) 0)))
; [eval] nxt != null
; [dead then-branch 114] $t@149 != Null
(push) ; 8
; [else-branch 114] $t@149 == Null
; [eval] prio(crt.data) < prio(x)
; [eval] prio(crt.data)
; [eval] prio(x)
(push) ; 9
(assert (not (< ($prio $Snap.unit $t@147) ($prio $Snap.unit x@56))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(assert (< ($prio $Snap.unit $t@147) ($prio $Snap.unit x@56)))
; [eval] (nxt != null) ==> (prio(crt.data) <= prio(peek(nxt)))
; [eval] nxt != null
(push) ; 9
; [dead then-branch 115] $t@149 != Null
(push) ; 10
; [else-branch 115] $t@149 == Null
(pop) ; 10
(pop) ; 9
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(declare-const $t@242 $Snap)
; Continue after loop
(declare-const $t@243 $Snap)
(declare-const $t@244 $Snap)
(assert (= $t@243 ($Snap.combine $t@244 $Snap.unit)))
(declare-const $t@245 $Snap)
(declare-const $t@246 $Snap)
(assert (= $t@244 ($Snap.combine $t@245 $t@246)))
(declare-const $t@247 $Snap)
(assert (= $t@245 ($Snap.combine $t@247 $Snap.unit)))
(declare-const $t@248 $Snap)
(assert (= $t@247 ($Snap.combine $t@248 $Snap.unit)))
(declare-const $t@249 $Snap)
(declare-const $t@250 $Snap)
(assert (= $t@248 ($Snap.combine $t@249 $t@250)))
(declare-const $t@251 $Snap)
(assert (= $t@249 ($Snap.combine $t@251 $Snap.unit)))
(declare-const $t@252 $Snap)
(assert (= $t@251 ($Snap.combine $t@252 $Snap.unit)))
(declare-const $t@253 $Snap)
(assert (= $t@252 ($Snap.combine $Snap.unit $t@253)))
; [eval] (0 <= i) && (i < |old(content(xs))|) && ((nxt == null) ==> (i == |old(content(xs))| - 1))
; [eval] (0 <= i) && (i < |old(content(xs))|)
; [eval] 0 <= i
(push) ; 9
(set-option :timeout 250)
(push) ; 10
(assert (not (not (<= 0 i@225))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
(assert (not (<= 0 i@225)))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 116] 0 <= i@225
(assert (<= 0 i@225))
; [eval] i < |old(content(xs))|
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 10
(push) ; 10
; [else-branch 116] !0 <= i@225
(assert (not (<= 0 i@225)))
(pop) ; 10
(pop) ; 9
(push) ; 9
(push) ; 10
(assert (not (not (and (<= 0 i@225) (< i@225 ($Seq.length ($content $t@63 xs@55)))))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
(assert (not (and (<= 0 i@225) (< i@225 ($Seq.length ($content $t@63 xs@55))))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 117] 0 <= i@225 && i@225 < |content(xs@55;$t@63)|
(assert (and (<= 0 i@225) (< i@225 ($Seq.length ($content $t@63 xs@55)))))
; [eval] (nxt == null) ==> (i == |old(content(xs))| - 1)
; [eval] nxt == null
(push) ; 11
(push) ; 12
(assert (not (not (= nxt@226 $Ref.null))))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(push) ; 12
(assert (not (= nxt@226 $Ref.null)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(push) ; 12
; [then-branch 118] nxt@226 == Null
(assert (= nxt@226 $Ref.null))
; [eval] i == |old(content(xs))| - 1
; [eval] |old(content(xs))| - 1
; [eval] |old(content(xs))|
; [eval] old(content(xs))
; [eval] content(xs)
(pop) ; 12
(push) ; 12
; [else-branch 118] nxt@226 != Null
(assert (not (= nxt@226 $Ref.null)))
(pop) ; 12
(pop) ; 11
(pop) ; 10
(push) ; 10
; [else-branch 117] !0 <= i@225 && i@225 < |content(xs@55;$t@63)|
(assert (not (and (<= 0 i@225) (< i@225 ($Seq.length ($content $t@63 xs@55))))))
(pop) ; 10
(pop) ; 9
(assert (and
  (and (<= 0 i@225) (< i@225 ($Seq.length ($content $t@63 xs@55))))
  (implies
    (= nxt@226 $Ref.null)
    (= i@225 (- ($Seq.length ($content $t@63 xs@55)) 1)))))
(declare-const $t@254 $Ref)
(declare-const $t@255 $Ref)
(assert (=
  $t@253
  ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@254)
    ($SortWrappers.$RefTo$Snap $t@255))))
(set-option :timeout 0)
(push) ; 9
(assert (not (= crt@227 $Ref.null)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(assert (not (= crt@227 $Ref.null)))
(push) ; 9
(assert (not (= crt@227 $Ref.null)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [eval] nxt == crt.next
(assert (= nxt@226 $t@255))
; [eval] crt.data == old(content(xs))[i]
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(assert (= $t@254 ($Seq.index ($content $t@63 xs@55) i@225)))
; [eval] nxt != null
(set-option :timeout 250)
(push) ; 9
(assert (not (= nxt@226 $Ref.null)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (not (= nxt@226 $Ref.null))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 119] nxt@226 != Null
(assert (not (= nxt@226 $Ref.null)))
(declare-const $t@256 $Snap)
(assert (= $t@250 ($Snap.combine $t@256 $Snap.unit)))
; [eval] nodesContent(nxt) == old(content(xs))[i + 1..]
; [eval] nodesContent(nxt)
; [eval] old(content(xs))[i + 1..]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] i + 1
(assert ($Seq.equal
  ($nodesContent $t@256 nxt@226)
  ($Seq.drop ($content $t@63 xs@55) (+ i@225 1))))
; [eval] prio(crt.data) < prio(x)
; [eval] prio(crt.data)
; [eval] prio(x)
(assert (< ($prio $Snap.unit $t@254) ($prio $Snap.unit x@56)))
; [eval] (nxt != null) ==> (prio(crt.data) <= prio(peek(nxt)))
; [eval] nxt != null
(push) ; 10
(push) ; 11
(assert (not (= nxt@226 $Ref.null)))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
; [dead then-branch 120] nxt@226 != Null
(push) ; 11
; [else-branch 120] nxt@226 == Null
(assert (= nxt@226 $Ref.null))
(pop) ; 11
(pop) ; 10
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] !((nxt != null) && (prio(peek(nxt)) < prio(x)))
; [eval] (nxt != null) && (prio(peek(nxt)) < prio(x))
; [eval] nxt != null
(push) ; 10
(push) ; 11
(assert (not (= nxt@226 $Ref.null)))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
; [dead then-branch 121] nxt@226 != Null
(push) ; 11
; [else-branch 121] nxt@226 == Null
(assert (= nxt@226 $Ref.null))
(pop) ; 11
(pop) ; 10
(assert (= nxt@226 $Ref.null))
(check-sat)
; unsat
(pop) ; 9
(push) ; 9
; [else-branch 119] nxt@226 == Null
(assert (= nxt@226 $Ref.null))
; [eval] prio(crt.data) < prio(x)
; [eval] prio(crt.data)
; [eval] prio(x)
(assert (< ($prio $Snap.unit $t@254) ($prio $Snap.unit x@56)))
; [eval] (nxt != null) ==> (prio(crt.data) <= prio(peek(nxt)))
; [eval] nxt != null
(push) ; 10
; [dead then-branch 122] nxt@226 != Null
(push) ; 11
; [else-branch 122] nxt@226 == Null
(pop) ; 11
(pop) ; 10
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] !((nxt != null) && (prio(peek(nxt)) < prio(x)))
; [eval] (nxt != null) && (prio(peek(nxt)) < prio(x))
; [eval] nxt != null
(push) ; 10
; [dead then-branch 123] nxt@226 != Null
(push) ; 11
; [else-branch 123] nxt@226 == Null
(pop) ; 11
(pop) ; 10
(check-sat)
; unknown
; [exec]
; node := new(data, next)
(declare-const node@257 $Ref)
(assert (not (= node@257 $Ref.null)))
(declare-const data@258 $Ref)
(declare-const next@259 $Ref)
(assert (and
  (not (= xs@55 node@257))
  (not (= x@56 node@257))
  (not (= tmp@58 node@257))
  (not (= $t@130 node@257))
  (not (= prev@224 node@257))
  (not (= nxt@226 node@257))
  (not (= crt@227 node@257))
  (not (= data@258 node@257))
  (not (= next@259 node@257))
  (not (= $t@254 node@257))
  (not (= $t@255 node@257))))
; [exec]
; node.data := x
; [exec]
; node.next := nxt
; [exec]
; fold acc(PQueue(node), write)
; [eval] xs.next != null
; [dead then-branch 124] nxt@226 != Null
(push) ; 10
; [else-branch 124] nxt@226 == Null
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 11
; [dead then-branch 125] nxt@226 != Null
(push) ; 12
; [else-branch 125] nxt@226 == Null
(pop) ; 12
(pop) ; 11
; [exec]
; crt.next := node
; [exec]
; fold acc(PQueue(crt), write)
; [eval] xs.next != null
(push) ; 11
(assert (not (= node@257 $Ref.null)))
(check-sat)
; unknown
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(push) ; 11
; [then-branch 126] node@257 != Null
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 12
(push) ; 13
(assert (not (= node@257 $Ref.null)))
(check-sat)
; unknown
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(push) ; 13
; [then-branch 127] node@257 != Null
; [eval] prio(xs.data) <= prio(nodesContent(xs.next)[0])
; [eval] prio(xs.data)
; [eval] prio(nodesContent(xs.next)[0])
; [eval] nodesContent(xs.next)[0]
; [eval] nodesContent(xs.next)
(pop) ; 13
; [dead else-branch 127] node@257 == Null
(pop) ; 12
(set-option :timeout 0)
(push) ; 12
(assert (not (implies
  (not (= node@257 $Ref.null))
  (<=
    ($prio $Snap.unit $t@254)
    ($prio $Snap.unit ($Seq.index
      ($nodesContent ($Snap.combine
        ($SortWrappers.$RefTo$Snap x@56)
        ($Snap.combine
          ($SortWrappers.$RefTo$Snap nxt@226)
          ($Snap.combine $Snap.unit $Snap.unit))) node@257)
      0))))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(assert (implies
  (not (= node@257 $Ref.null))
  (<=
    ($prio $Snap.unit $t@254)
    ($prio $Snap.unit ($Seq.index
      ($nodesContent ($Snap.combine
        ($SortWrappers.$RefTo$Snap x@56)
        ($Snap.combine
          ($SortWrappers.$RefTo$Snap nxt@226)
          ($Snap.combine $Snap.unit $Snap.unit))) node@257)
      0)))))
; [exec]
; apply acc(PQueue(crt), write) && (peek(crt) == old(content(xs))[i]) --* acc(PQueue(hd), write) && (nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt)))
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] old(content(xs))
; [eval] content(xs)
(declare-const $t@260 $Snap)
; [eval] peek(crt) == old(content(xs))[i]
; [eval] peek(crt)
; [eval] old(content(xs))[i]
; [eval] old(content(xs))
; [eval] content(xs)
(push) ; 12
(assert (not (=
  ($peek ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@254)
    ($Snap.combine
      ($SortWrappers.$RefTo$Snap node@257)
      ($Snap.combine
        ($Snap.combine
          ($SortWrappers.$RefTo$Snap x@56)
          ($Snap.combine
            ($SortWrappers.$RefTo$Snap nxt@226)
            ($Snap.combine $Snap.unit $Snap.unit)))
        $Snap.unit))) crt@227)
  ($Seq.index ($content $t@63 xs@55) i@225))))
(check-sat)
; unsat
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(assert (=
  ($peek ($Snap.combine
    ($SortWrappers.$RefTo$Snap $t@254)
    ($Snap.combine
      ($SortWrappers.$RefTo$Snap node@257)
      ($Snap.combine
        ($Snap.combine
          ($SortWrappers.$RefTo$Snap x@56)
          ($Snap.combine
            ($SortWrappers.$RefTo$Snap nxt@226)
            ($Snap.combine $Snap.unit $Snap.unit)))
        $Snap.unit))) crt@227)
  ($Seq.index ($content $t@63 xs@55) i@225)))
(declare-const $t@261 $Snap)
(declare-const $t@262 $Snap)
(assert (= $t@261 ($Snap.combine $t@262 $Snap.unit)))
; [eval] nodesContent(hd) == old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] nodesContent(hd)
; [eval] old(content(xs))[0..i] ++ given(nodesContent(crt))
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] given(nodesContent(crt))
; [eval] nodesContent(crt)
(assert ($Seq.equal
  ($nodesContent $t@262 $t@130)
  ($Seq.append
    ($Seq.drop ($Seq.take ($content $t@63 xs@55) i@225) 0)
    ($nodesContent ($Snap.combine
      ($SortWrappers.$RefTo$Snap $t@254)
      ($Snap.combine
        ($SortWrappers.$RefTo$Snap node@257)
        ($Snap.combine
          ($Snap.combine
            ($SortWrappers.$RefTo$Snap x@56)
            ($Snap.combine
              ($SortWrappers.$RefTo$Snap nxt@226)
              ($Snap.combine $Snap.unit $Snap.unit)))
          $Snap.unit))) crt@227))))
(push) ; 12
(pop) ; 12
; [exec]
; i := i + 1
; [eval] i + 1
; [exec]
; fold acc(List(xs), write)
; [eval] xs.head != null
(set-option :timeout 250)
(push) ; 12
(assert (not (= $t@130 $Ref.null)))
(check-sat)
; unknown
(pop) ; 12
; 0.00s
; (get-info :all-statistics)
(push) ; 12
; [then-branch 128] $t@130 != Null
; [eval] content(xs) == old(content(xs))[0..i] ++ Seq(x) ++ old(content(xs))[i..]
; [eval] content(xs)
; [eval] old(content(xs))[0..i] ++ Seq(x) ++ old(content(xs))[i..]
; [eval] old(content(xs))[0..i] ++ Seq(x)
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] Seq(x)
(assert (= ($Seq.length ($Seq.singleton x@56)) 1))
; [eval] old(content(xs))[i..]
; [eval] old(content(xs))
; [eval] content(xs)
(set-option :timeout 0)
(push) ; 13
(assert (not ($Seq.equal
  ($content ($Snap.combine ($SortWrappers.$RefTo$Snap $t@130) $t@262) xs@55)
  ($Seq.append
    ($Seq.append
      ($Seq.drop ($Seq.take ($content $t@63 xs@55) (+ i@225 1)) 0)
      ($Seq.singleton x@56))
    ($Seq.drop ($content $t@63 xs@55) (+ i@225 1))))))
(check-sat)
; unsat
(pop) ; 13
; 0.00s
; (get-info :all-statistics)
(assert ($Seq.equal
  ($content ($Snap.combine ($SortWrappers.$RefTo$Snap $t@130) $t@262) xs@55)
  ($Seq.append
    ($Seq.append
      ($Seq.drop ($Seq.take ($content $t@63 xs@55) (+ i@225 1)) 0)
      ($Seq.singleton x@56))
    ($Seq.drop ($content $t@63 xs@55) (+ i@225 1)))))
(pop) ; 12
; [dead else-branch 128] $t@130 == Null
(pop) ; 11
; [dead else-branch 126] node@257 == Null
(pop) ; 10
(pop) ; 9
(pop) ; 8
(pop) ; 7
(pop) ; 6
(pop) ; 5
(push) ; 5
; [else-branch 51] $t@130 == Null || prio(x@56;_) <= joinedIn@146()
(assert (or (= $t@130 $Ref.null) (<= ($prio $Snap.unit x@56) joinedIn@146)))
(pop) ; 5
(pop) ; 4
(push) ; 4
; [else-branch 38] $t@130 == Null
(assert (= $t@130 $Ref.null))
; [exec]
; i := 0
; [exec]
; hd := xs.head
; [eval] (hd == null) || (prio(x) <= (unfolding acc(PQueue(hd), write) in prio(hd.data)))
; [eval] hd == null
(push) ; 5
; [dead then-branch 129] $t@130 != Null
(push) ; 6
; [else-branch 129] $t@130 == Null
(pop) ; 6
(pop) ; 5
(set-option :timeout 250)
(push) ; 5
(assert (not (not (or (= $t@130 $Ref.null) true))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (or (= $t@130 $Ref.null) true)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 130] $t@130 == Null || True
(assert (or (= $t@130 $Ref.null) true))
; [exec]
; inhale hd != null
; [eval] hd != null
(assert (not (= $t@130 $Ref.null)))
; [exec]
; tmp := new(data, next)
(declare-const tmp@263 $Ref)
(assert (not (= tmp@263 $Ref.null)))
(declare-const data@264 $Ref)
(declare-const next@265 $Ref)
(assert (and
  (not (= xs@55 tmp@263))
  (not (= x@56 tmp@263))
  (not (= crt@59 tmp@263))
  (not (= nxt@60 tmp@263))
  (not (= node@62 tmp@263))
  (not (= $t@130 tmp@263))
  (not (= data@264 tmp@263))
  (not (= next@265 tmp@263))))
; [exec]
; tmp.data := x
; [exec]
; tmp.next := hd
; [exec]
; fold acc(PQueue(tmp), write)
; [eval] xs.next != null
; [dead then-branch 131] $t@130 != Null
(push) ; 6
; [else-branch 131] $t@130 == Null
; [eval] (xs.next != null) ==> (prio(xs.data) <= prio(nodesContent(xs.next)[0]))
; [eval] xs.next != null
(push) ; 7
; [dead then-branch 132] $t@130 != Null
(push) ; 8
; [else-branch 132] $t@130 == Null
(pop) ; 8
(pop) ; 7
; [exec]
; xs.head := tmp
; [exec]
; fold acc(List(xs), write)
; [eval] xs.head != null
(push) ; 7
(assert (not (= tmp@263 $Ref.null)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [dead then-branch 133] tmp@263 != Null
(push) ; 7
; [else-branch 133] tmp@263 == Null
(assert (= tmp@263 $Ref.null))
; [eval] content(xs) == old(content(xs))[0..i] ++ Seq(x) ++ old(content(xs))[i..]
; [eval] content(xs)
; [eval] old(content(xs))[0..i] ++ Seq(x) ++ old(content(xs))[i..]
; [eval] old(content(xs))[0..i] ++ Seq(x)
; [eval] old(content(xs))[0..i]
; [eval] old(content(xs))[..i]
; [eval] old(content(xs))
; [eval] content(xs)
; [eval] Seq(x)
(assert (= ($Seq.length ($Seq.singleton x@56)) 1))
; [eval] old(content(xs))[i..]
; [eval] old(content(xs))
; [eval] content(xs)
(set-option :timeout 0)
(push) ; 8
(assert (not ($Seq.equal
  ($content ($Snap.combine ($SortWrappers.$RefTo$Snap tmp@263) $Snap.unit) xs@55)
  ($Seq.append
    ($Seq.append
      ($Seq.drop ($Seq.take ($content $t@63 xs@55) 0) 0)
      ($Seq.singleton x@56))
    ($Seq.drop ($content $t@63 xs@55) 0)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert ($Seq.equal
  ($content ($Snap.combine ($SortWrappers.$RefTo$Snap tmp@263) $Snap.unit) xs@55)
  ($Seq.append
    ($Seq.append
      ($Seq.drop ($Seq.take ($content $t@63 xs@55) 0) 0)
      ($Seq.singleton x@56))
    ($Seq.drop ($content $t@63 xs@55) 0))))
(pop) ; 7
(pop) ; 6
(pop) ; 5
; [dead else-branch 130] !$t@130 == Null || True
; [eval] !((hd == null) || (prio(x) <= (unfolding acc(PQueue(hd), write) in prio(hd.data))))
; [eval] (hd == null) || (prio(x) <= (unfolding acc(PQueue(hd), write) in prio(hd.data)))
; [eval] hd == null
(push) ; 5
; [dead then-branch 134] $t@130 != Null
(push) ; 6
; [else-branch 134] $t@130 == Null
(pop) ; 6
(pop) ; 5
(set-option :timeout 250)
(push) ; 5
(assert (not (or (= $t@130 $Ref.null) true)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; [dead then-branch 135] !$t@130 == Null || True
(push) ; 5
; [else-branch 135] $t@130 == Null || True
(assert (or (= $t@130 $Ref.null) true))
(pop) ; 5
(pop) ; 4
(pop) ; 3
(pop) ; 2
; ---------- dequeue ----------
(declare-const xs@266 $Ref)
(declare-const x@267 $Ref)
(push) ; 2
(declare-const $t@268 $Snap)
; [eval] length(xs) > 0
; [eval] length(xs)
(assert (> ($length $t@268 xs@266) 0))
(push) ; 3
(pop) ; 3
(push) ; 3
; [eval] x == old(content(xs)[0])
; [eval] old(content(xs)[0])
; [eval] content(xs)[0]
; [eval] content(xs)
(assert (= x@267 ($Seq.index ($content $t@268 xs@266) 0)))
(declare-const $t@269 $Snap)
; [eval] content(xs) == old(content(xs)[1..])
; [eval] content(xs)
; [eval] old(content(xs)[1..])
; [eval] content(xs)[1..]
; [eval] content(xs)
(assert ($Seq.equal ($content $t@269 xs@266) ($Seq.drop ($content $t@268 xs@266) 1)))
(pop) ; 3
(push) ; 3
; [exec]
; unfold acc(List(xs), write)
(declare-const $t@270 $Ref)
(declare-const $t@271 $Snap)
(assert (= $t@268 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@270) $t@271)))
(set-option :timeout 0)
(push) ; 4
(assert (not (= xs@266 $Ref.null)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (not (= xs@266 $Ref.null)))
; [eval] xs.head != null
(set-option :timeout 250)
(push) ; 4
(assert (not (= $t@270 $Ref.null)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not (not (= $t@270 $Ref.null))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 136] $t@270 != Null
(assert (not (= $t@270 $Ref.null)))
; [exec]
; unfold acc(PQueue(xs.head), write)
(declare-const $t@272 $Ref)
(declare-const $t@273 $Snap)
(assert (= $t@271 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@272) $t@273)))
(set-option :timeout 0)
(push) ; 5
(assert (not (= $t@270 $Ref.null)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(declare-const $t@274 $Ref)
(declare-const $t@275 $Snap)
(assert (= $t@273 ($Snap.combine ($SortWrappers.$RefTo$Snap $t@274) $t@275)))
(push) ; 5
(assert (not (= $t@270 $Ref.null)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(declare-const $t@276 $Snap)
(assert (= $t@275 ($Snap.combine $t@276 $Snap.unit)))
; [eval] xs.head.next != null
(set-option :timeout 250)
(push) ; 5
(assert (not (= $t@274 $Ref.null)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (not (= $t@274 $Ref.null))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 137] $t@274 != Null
(assert (not (= $t@274 $Ref.null)))
; [eval] (xs.head.next != null) ==> (prio(xs.head.data) <= prio(nodesContent(xs.head.next)[0]))
; [eval] xs.head.next != null
(push) ; 6
(push) ; 7
(assert (not (= $t@274 $Ref.null)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 138] $t@274 != Null
; [eval] prio(xs.head.data) <= prio(nodesContent(xs.head.next)[0])
; [eval] prio(xs.head.data)
; [eval] prio(nodesContent(xs.head.next)[0])
; [eval] nodesContent(xs.head.next)[0]
; [eval] nodesContent(xs.head.next)
(pop) ; 7
; [dead else-branch 138] $t@274 == Null
(pop) ; 6
(assert (implies
  (not (= $t@274 $Ref.null))
  (<=
    ($prio $Snap.unit $t@272)
    ($prio $Snap.unit ($Seq.index ($nodesContent $t@276 $t@274) 0)))))
; [exec]
; x := xs.head.data
; [exec]
; xs.head := xs.head.next
; [exec]
; fold acc(List(xs), write)
; [eval] xs.head != null
(push) ; 6
(assert (not (= $t@274 $Ref.null)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 139] $t@274 != Null
; [eval] x == old(content(xs)[0])
; [eval] old(content(xs)[0])
; [eval] content(xs)[0]
; [eval] content(xs)
(set-option :timeout 0)
(push) ; 7
(assert (not (= $t@272 ($Seq.index ($content $t@268 xs@266) 0))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (= $t@272 ($Seq.index ($content $t@268 xs@266) 0)))
; [eval] content(xs) == old(content(xs)[1..])
; [eval] content(xs)
; [eval] old(content(xs)[1..])
; [eval] content(xs)[1..]
; [eval] content(xs)
(push) ; 7
(assert (not ($Seq.equal
  ($content ($Snap.combine ($SortWrappers.$RefTo$Snap $t@274) $t@276) xs@266)
  ($Seq.drop ($content $t@268 xs@266) 1))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert ($Seq.equal
  ($content ($Snap.combine ($SortWrappers.$RefTo$Snap $t@274) $t@276) xs@266)
  ($Seq.drop ($content $t@268 xs@266) 1)))
(pop) ; 6
; [dead else-branch 139] $t@274 == Null
(pop) ; 5
(push) ; 5
; [else-branch 137] $t@274 == Null
(assert (= $t@274 $Ref.null))
; [eval] (xs.head.next != null) ==> (prio(xs.head.data) <= prio(nodesContent(xs.head.next)[0]))
; [eval] xs.head.next != null
(push) ; 6
; [dead then-branch 140] $t@274 != Null
(push) ; 7
; [else-branch 140] $t@274 == Null
(pop) ; 7
(pop) ; 6
; [exec]
; x := xs.head.data
; [exec]
; xs.head := xs.head.next
; [exec]
; fold acc(List(xs), write)
; [eval] xs.head != null
; [dead then-branch 141] $t@274 != Null
(push) ; 6
; [else-branch 141] $t@274 == Null
; [eval] x == old(content(xs)[0])
; [eval] old(content(xs)[0])
; [eval] content(xs)[0]
; [eval] content(xs)
(push) ; 7
(assert (not (= $t@272 ($Seq.index ($content $t@268 xs@266) 0))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (= $t@272 ($Seq.index ($content $t@268 xs@266) 0)))
; [eval] content(xs) == old(content(xs)[1..])
; [eval] content(xs)
; [eval] old(content(xs)[1..])
; [eval] content(xs)[1..]
; [eval] content(xs)
(push) ; 7
(assert (not ($Seq.equal
  ($content ($Snap.combine ($SortWrappers.$RefTo$Snap $t@274) $Snap.unit) xs@266)
  ($Seq.drop ($content $t@268 xs@266) 1))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert ($Seq.equal
  ($content ($Snap.combine ($SortWrappers.$RefTo$Snap $t@274) $Snap.unit) xs@266)
  ($Seq.drop ($content $t@268 xs@266) 1)))
(pop) ; 6
(pop) ; 5
(pop) ; 4
; [dead else-branch 136] $t@270 == Null
(pop) ; 3
(pop) ; 2
; ---------- client ----------
(declare-const xs@277 $Ref)
(declare-const x@278 $Ref)
(push) ; 2
(push) ; 3
(pop) ; 3
(push) ; 3
(pop) ; 3
(push) ; 3
; [exec]
; inhale acc(List(xs), write)
(declare-const $t@279 $Snap)
; [exec]
; inhale acc(xs.held, write)
(push) ; 4
(assert (not (= xs@277 $Ref.null)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (not (= xs@277 $Ref.null)))
(declare-const $t@280 Int)
; [eval] length(xs) > 0
; [eval] length(xs)
(set-option :timeout 250)
(push) ; 4
(assert (not (not (> ($length $t@279 xs@277) 0))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not (> ($length $t@279 xs@277) 0)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 142] length(xs@277;$t@279) > 0
(assert (> ($length $t@279 xs@277) 0))
; [exec]
; x := dequeue(xs)
; [eval] length(xs) > 0
; [eval] length(xs)
(declare-const x@281 $Ref)
(declare-const $t@282 $Snap)
(declare-const $t@283 $Snap)
(assert (= $t@282 ($Snap.combine $t@283 $Snap.unit)))
(declare-const $t@284 $Snap)
(assert (= $t@283 ($Snap.combine $Snap.unit $t@284)))
; [eval] x == old(content(xs)[0])
; [eval] old(content(xs)[0])
; [eval] content(xs)[0]
; [eval] content(xs)
(assert (= x@281 ($Seq.index ($content $t@279 xs@277) 0)))
; [eval] content(xs) == old(content(xs)[1..])
; [eval] content(xs)
; [eval] old(content(xs)[1..])
; [eval] content(xs)[1..]
; [eval] content(xs)
(assert ($Seq.equal ($content $t@284 xs@277) ($Seq.drop ($content $t@279 xs@277) 1)))
; [exec]
; exhale acc(List(xs), write)
; [exec]
; exhale acc(xs.held, write)
(pop) ; 4
(push) ; 4
; [else-branch 142] !length(xs@277;$t@279) > 0
(assert (not (> ($length $t@279 xs@277) 0)))
(pop) ; 4
; [eval] !(length(xs) > 0)
; [eval] length(xs) > 0
; [eval] length(xs)
(push) ; 4
(assert (not (> ($length $t@279 xs@277) 0)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not (not (> ($length $t@279 xs@277) 0))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 143] !length(xs@277;$t@279) > 0
(assert (not (> ($length $t@279 xs@277) 0)))
; [exec]
; exhale acc(List(xs), write)
; [exec]
; exhale acc(xs.held, write)
(pop) ; 4
(push) ; 4
; [else-branch 143] length(xs@277;$t@279) > 0
(assert (> ($length $t@279 xs@277) 0))
(pop) ; 4
(pop) ; 3
(pop) ; 2

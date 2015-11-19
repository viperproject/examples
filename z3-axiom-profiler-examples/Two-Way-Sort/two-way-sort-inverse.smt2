(get-info :version)
; (:version "4.4.2")
; Input file is Two-Way-Sort-Slow-Inverse.sil
; Started: 2015-11-05 09:02:54
; Silicon.buildVersion: 0.1-SNAPSHOT b5ec6a10556f cvc4-integration 2015/11/05 09:02:32
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
(declare-sort $Set<Bool> 0)
(declare-sort $Set<$Ref> 0)
(declare-sort $Array 0)
(declare-sort $FVF<$Ref> 0)
(declare-sort $FVF<Bool> 0)
; /dafny_axioms/sets_declarations_dafny.smt2 [Bool]
(declare-fun $Set.in_Bool (Bool $Set<Bool>) Bool)
(declare-fun $Set.card_Bool ($Set<Bool>) Int)
(declare-fun $Set.empty<Bool> () $Set<Bool>)
(declare-fun $Set.singleton_Bool (Bool) $Set<Bool>)
(declare-fun $Set.unionone_Bool ($Set<Bool> Bool) $Set<Bool>)
(declare-fun $Set.union_Bool ($Set<Bool> $Set<Bool>) $Set<Bool>)
(declare-fun $Set.disjoint_Bool ($Set<Bool> $Set<Bool>) Bool)
(declare-fun $Set.difference_Bool ($Set<Bool> $Set<Bool>) $Set<Bool>)
(declare-fun $Set.intersection_Bool ($Set<Bool> $Set<Bool>) $Set<Bool>)
(declare-fun $Set.subset_Bool ($Set<Bool> $Set<Bool>) Bool)
(declare-fun $Set.equal_Bool ($Set<Bool> $Set<Bool>) Bool)
; /dafny_axioms/sets_declarations_dafny.smt2 [Ref]
(declare-fun $Set.in_$Ref ($Ref $Set<$Ref>) Bool)
(declare-fun $Set.card_$Ref ($Set<$Ref>) Int)
(declare-fun $Set.empty<$Ref> () $Set<$Ref>)
(declare-fun $Set.singleton_$Ref ($Ref) $Set<$Ref>)
(declare-fun $Set.unionone_$Ref ($Set<$Ref> $Ref) $Set<$Ref>)
(declare-fun $Set.union_$Ref ($Set<$Ref> $Set<$Ref>) $Set<$Ref>)
(declare-fun $Set.disjoint_$Ref ($Set<$Ref> $Set<$Ref>) Bool)
(declare-fun $Set.difference_$Ref ($Set<$Ref> $Set<$Ref>) $Set<$Ref>)
(declare-fun $Set.intersection_$Ref ($Set<$Ref> $Set<$Ref>) $Set<$Ref>)
(declare-fun $Set.subset_$Ref ($Set<$Ref> $Set<$Ref>) Bool)
(declare-fun $Set.equal_$Ref ($Set<$Ref> $Set<$Ref>) Bool)
(declare-fun second<Ref~Int> ($Ref) Int)
(declare-fun first<Ref~Array> ($Ref) $Array)
(declare-fun length<Array~Int> ($Array) Int)
(declare-fun loc<Array~Int~Ref> ($Array Int) $Ref)
(assert true)
; /field_value_functions_declarations.smt2 [val: Bool]
(declare-fun $FVF.domain_val ($FVF<Bool>) $Set<$Ref>)
(declare-fun $FVF.lookup_val ($FVF<Bool> $Ref) Bool)
(declare-fun $FVF.after_val ($FVF<Bool> $FVF<Bool>) Bool)
(declare-const $fvfTOP_val $FVF<Bool>)
; /dafny_axioms/sets_axioms_dafny.smt2 [Bool]
(assert (forall ((s $Set<Bool>)) (!
  (<= 0 ($Set.card_Bool s))
  :pattern (($Set.card_Bool s))
  )))
(assert (forall ((o Bool)) (!
  (not ($Set.in_Bool o $Set.empty<Bool>))
  :pattern (($Set.in_Bool o $Set.empty<Bool>))
  )))
(assert (forall ((s $Set<Bool>)) (!
  (and
    (not (xor
      (= ($Set.card_Bool s) 0)
      (= s $Set.empty<Bool>)))
    (=>
      (not (= ($Set.card_Bool s) 0))
      (exists ((x Bool)) (!
        ($Set.in_Bool x s)
        :pattern (($Set.in_Bool x s))
      ))))
  :pattern (($Set.card_Bool s))
  )))
(assert (forall ((r Bool)) (!
  ($Set.in_Bool r ($Set.singleton_Bool r))
  :pattern (($Set.in_Bool r ($Set.singleton_Bool r)))
  )))
(assert (forall ((r Bool) (o Bool)) (!
  (not (xor
    ($Set.in_Bool o ($Set.singleton_Bool r))
    (= r o)))
  :pattern (($Set.in_Bool o ($Set.singleton_Bool r)))
  )))
(assert (forall ((r Bool)) (!
  (= ($Set.card_Bool ($Set.singleton_Bool r)) 1)
  :pattern (($Set.card_Bool ($Set.singleton_Bool r)))
  )))
(assert (forall ((a $Set<Bool>) (x Bool) (o Bool)) (!
  (not (xor
    ($Set.in_Bool o ($Set.unionone_Bool a x))
    (or
      (= o x)
      ($Set.in_Bool o a))))
  :pattern (($Set.in_Bool o ($Set.unionone_Bool a x)))
  )))
(assert (forall ((a $Set<Bool>) (x Bool)) (!
  ($Set.in_Bool x ($Set.unionone_Bool a x))
  :pattern (($Set.in_Bool x ($Set.unionone_Bool a x)))
  )))
(assert (forall ((a $Set<Bool>) (x Bool) (y Bool)) (!
  (=>
    ($Set.in_Bool y a)
    ($Set.in_Bool y ($Set.unionone_Bool a x)))
  :pattern (($Set.in_Bool y a) ($Set.in_Bool y ($Set.unionone_Bool a x)))
  )))
(assert (forall ((a $Set<Bool>) (x Bool)) (!
  (=>
    ($Set.in_Bool x a)
    (= ($Set.card_Bool ($Set.unionone_Bool a x)) ($Set.card_Bool a)))
  :pattern (($Set.card_Bool ($Set.unionone_Bool a x)))
  )))
(assert (forall ((a $Set<Bool>) (x Bool)) (!
  (=>
    (not ($Set.in_Bool x a))
    (= ($Set.card_Bool ($Set.unionone_Bool a x)) (+ ($Set.card_Bool a) 1)))
  :pattern (($Set.card_Bool ($Set.unionone_Bool a x)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>) (o Bool)) (!
  (not (xor
    ($Set.in_Bool o ($Set.union_Bool a b))
    (or
      ($Set.in_Bool o a)
      ($Set.in_Bool o b))))
  :pattern (($Set.in_Bool o ($Set.union_Bool a b)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>) (y Bool)) (!
  (=>
    ($Set.in_Bool y a)
    ($Set.in_Bool y ($Set.union_Bool a b)))
  :pattern (($Set.in_Bool y ($Set.union_Bool a b)) ($Set.in_Bool y a))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>) (y Bool)) (!
  (=>
    ($Set.in_Bool y b)
    ($Set.in_Bool y ($Set.union_Bool a b)))
  :pattern (($Set.in_Bool y ($Set.union_Bool a b)) ($Set.in_Bool y b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>) (o Bool)) (!
  (not (xor
    ($Set.in_Bool o ($Set.intersection_Bool a b))
    (and
      ($Set.in_Bool o a)
      ($Set.in_Bool o b))))
  :pattern (($Set.in_Bool o ($Set.intersection_Bool a b)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (=
    ($Set.union_Bool ($Set.union_Bool a b) b)
    ($Set.union_Bool a b))
  :pattern (($Set.union_Bool ($Set.union_Bool a b) b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (=
    ($Set.union_Bool a ($Set.union_Bool a b))
    ($Set.union_Bool a b))
    :pattern (($Set.union_Bool a ($Set.union_Bool a b)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (=
    ($Set.intersection_Bool ($Set.intersection_Bool a b) b)
    ($Set.intersection_Bool a b))
  :pattern (($Set.intersection_Bool ($Set.intersection_Bool a b) b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (=
    ($Set.intersection_Bool a ($Set.intersection_Bool a b))
    ($Set.intersection_Bool a b))
  :pattern (($Set.intersection_Bool a ($Set.intersection_Bool a b)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (=
    (+
      ($Set.card_Bool ($Set.union_Bool a b))
      ($Set.card_Bool ($Set.intersection_Bool a b)))
    (+
      ($Set.card_Bool a)
      ($Set.card_Bool b)))
  :pattern (($Set.card_Bool ($Set.union_Bool a b)))
  :pattern (($Set.card_Bool ($Set.intersection_Bool a b)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>) (o Bool)) (!
  (not (xor
    ($Set.in_Bool o ($Set.difference_Bool a b))
    (and
      ($Set.in_Bool o a)
      (not ($Set.in_Bool o b)))))
  :pattern (($Set.in_Bool o ($Set.difference_Bool a b)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>) (y Bool)) (!
  (=>
    ($Set.in_Bool y b)
    (not ($Set.in_Bool y ($Set.difference_Bool a b))))
  :pattern (($Set.in_Bool y ($Set.difference_Bool a b)) ($Set.in_Bool y b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (not (xor
    ($Set.subset_Bool a b)
    (forall ((o Bool)) (!
      (=>
        ($Set.in_Bool o a)
        ($Set.in_Bool o b))
      :pattern (($Set.in_Bool o a))
      :pattern (($Set.in_Bool o b))
    ))))
  :pattern (($Set.subset_Bool a b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (not (xor
    ($Set.equal_Bool a b)
    (forall ((o Bool)) (!
      (not (xor
        ($Set.in_Bool o a)
        ($Set.in_Bool o b)))
      :pattern (($Set.in_Bool o a))
      :pattern (($Set.in_Bool o b))
      :qid |$Set<Bool>.ext-inner|
      ))))
  :pattern (($Set.equal_Bool a b))
  :qid |$Set<Bool>.ext-outer|
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (=>
    ($Set.equal_Bool a b)
    (= a b))
  :pattern (($Set.equal_Bool a b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (not (xor
    ($Set.disjoint_Bool a b)
    (forall ((o Bool)) (!
      (or
        (not ($Set.in_Bool o a))
        (not ($Set.in_Bool o b)))
      :pattern (($Set.in_Bool o a))
      :pattern (($Set.in_Bool o b))
      ))))
  :pattern (($Set.disjoint_Bool a b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (and
    (=
      (+
        (+
          ($Set.card_Bool ($Set.difference_Bool a b))
          ($Set.card_Bool ($Set.difference_Bool b a)))
        ($Set.card_Bool ($Set.intersection_Bool a b)))
      ($Set.card_Bool ($Set.union_Bool a b)))
    (=
      ($Set.card_Bool ($Set.difference_Bool a b))
      (-
        ($Set.card_Bool a)
        ($Set.card_Bool ($Set.intersection_Bool a b)))))
  :pattern (($Set.card_Bool ($Set.difference_Bool a b)) ($Set.card_Bool ($Set.intersection_Bool a b)))
  )))
; /dafny_axioms/sets_axioms_dafny.smt2 [Ref]
(assert (forall ((s $Set<$Ref>)) (!
  (<= 0 ($Set.card_$Ref s))
  :pattern (($Set.card_$Ref s))
  )))
(assert (forall ((o $Ref)) (!
  (not ($Set.in_$Ref o $Set.empty<$Ref>))
  :pattern (($Set.in_$Ref o $Set.empty<$Ref>))
  )))
(assert (forall ((s $Set<$Ref>)) (!
  (and
    (not (xor
      (= ($Set.card_$Ref s) 0)
      (= s $Set.empty<$Ref>)))
    (=>
      (not (= ($Set.card_$Ref s) 0))
      (exists ((x $Ref)) (!
        ($Set.in_$Ref x s)
        :pattern (($Set.in_$Ref x s))
      ))))
  :pattern (($Set.card_$Ref s))
  )))
(assert (forall ((r $Ref)) (!
  ($Set.in_$Ref r ($Set.singleton_$Ref r))
  :pattern (($Set.in_$Ref r ($Set.singleton_$Ref r)))
  )))
(assert (forall ((r $Ref) (o $Ref)) (!
  (not (xor
    ($Set.in_$Ref o ($Set.singleton_$Ref r))
    (= r o)))
  :pattern (($Set.in_$Ref o ($Set.singleton_$Ref r)))
  )))
(assert (forall ((r $Ref)) (!
  (= ($Set.card_$Ref ($Set.singleton_$Ref r)) 1)
  :pattern (($Set.card_$Ref ($Set.singleton_$Ref r)))
  )))
(assert (forall ((a $Set<$Ref>) (x $Ref) (o $Ref)) (!
  (not (xor
    ($Set.in_$Ref o ($Set.unionone_$Ref a x))
    (or
      (= o x)
      ($Set.in_$Ref o a))))
  :pattern (($Set.in_$Ref o ($Set.unionone_$Ref a x)))
  )))
(assert (forall ((a $Set<$Ref>) (x $Ref)) (!
  ($Set.in_$Ref x ($Set.unionone_$Ref a x))
  :pattern (($Set.in_$Ref x ($Set.unionone_$Ref a x)))
  )))
(assert (forall ((a $Set<$Ref>) (x $Ref) (y $Ref)) (!
  (=>
    ($Set.in_$Ref y a)
    ($Set.in_$Ref y ($Set.unionone_$Ref a x)))
  :pattern (($Set.in_$Ref y a) ($Set.in_$Ref y ($Set.unionone_$Ref a x)))
  )))
(assert (forall ((a $Set<$Ref>) (x $Ref)) (!
  (=>
    ($Set.in_$Ref x a)
    (= ($Set.card_$Ref ($Set.unionone_$Ref a x)) ($Set.card_$Ref a)))
  :pattern (($Set.card_$Ref ($Set.unionone_$Ref a x)))
  )))
(assert (forall ((a $Set<$Ref>) (x $Ref)) (!
  (=>
    (not ($Set.in_$Ref x a))
    (= ($Set.card_$Ref ($Set.unionone_$Ref a x)) (+ ($Set.card_$Ref a) 1)))
  :pattern (($Set.card_$Ref ($Set.unionone_$Ref a x)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>) (o $Ref)) (!
  (not (xor
    ($Set.in_$Ref o ($Set.union_$Ref a b))
    (or
      ($Set.in_$Ref o a)
      ($Set.in_$Ref o b))))
  :pattern (($Set.in_$Ref o ($Set.union_$Ref a b)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>) (y $Ref)) (!
  (=>
    ($Set.in_$Ref y a)
    ($Set.in_$Ref y ($Set.union_$Ref a b)))
  :pattern (($Set.in_$Ref y ($Set.union_$Ref a b)) ($Set.in_$Ref y a))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>) (y $Ref)) (!
  (=>
    ($Set.in_$Ref y b)
    ($Set.in_$Ref y ($Set.union_$Ref a b)))
  :pattern (($Set.in_$Ref y ($Set.union_$Ref a b)) ($Set.in_$Ref y b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>) (o $Ref)) (!
  (not (xor
    ($Set.in_$Ref o ($Set.intersection_$Ref a b))
    (and
      ($Set.in_$Ref o a)
      ($Set.in_$Ref o b))))
  :pattern (($Set.in_$Ref o ($Set.intersection_$Ref a b)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (=
    ($Set.union_$Ref ($Set.union_$Ref a b) b)
    ($Set.union_$Ref a b))
  :pattern (($Set.union_$Ref ($Set.union_$Ref a b) b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (=
    ($Set.union_$Ref a ($Set.union_$Ref a b))
    ($Set.union_$Ref a b))
    :pattern (($Set.union_$Ref a ($Set.union_$Ref a b)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (=
    ($Set.intersection_$Ref ($Set.intersection_$Ref a b) b)
    ($Set.intersection_$Ref a b))
  :pattern (($Set.intersection_$Ref ($Set.intersection_$Ref a b) b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (=
    ($Set.intersection_$Ref a ($Set.intersection_$Ref a b))
    ($Set.intersection_$Ref a b))
  :pattern (($Set.intersection_$Ref a ($Set.intersection_$Ref a b)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (=
    (+
      ($Set.card_$Ref ($Set.union_$Ref a b))
      ($Set.card_$Ref ($Set.intersection_$Ref a b)))
    (+
      ($Set.card_$Ref a)
      ($Set.card_$Ref b)))
  :pattern (($Set.card_$Ref ($Set.union_$Ref a b)))
  :pattern (($Set.card_$Ref ($Set.intersection_$Ref a b)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>) (o $Ref)) (!
  (not (xor
    ($Set.in_$Ref o ($Set.difference_$Ref a b))
    (and
      ($Set.in_$Ref o a)
      (not ($Set.in_$Ref o b)))))
  :pattern (($Set.in_$Ref o ($Set.difference_$Ref a b)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>) (y $Ref)) (!
  (=>
    ($Set.in_$Ref y b)
    (not ($Set.in_$Ref y ($Set.difference_$Ref a b))))
  :pattern (($Set.in_$Ref y ($Set.difference_$Ref a b)) ($Set.in_$Ref y b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (not (xor
    ($Set.subset_$Ref a b)
    (forall ((o $Ref)) (!
      (=>
        ($Set.in_$Ref o a)
        ($Set.in_$Ref o b))
      :pattern (($Set.in_$Ref o a))
      :pattern (($Set.in_$Ref o b))
    ))))
  :pattern (($Set.subset_$Ref a b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (not (xor
    ($Set.equal_$Ref a b)
    (forall ((o $Ref)) (!
      (not (xor
        ($Set.in_$Ref o a)
        ($Set.in_$Ref o b)))
      :pattern (($Set.in_$Ref o a))
      :pattern (($Set.in_$Ref o b))
      :qid |$Set<$Ref>.ext-inner|
      ))))
  :pattern (($Set.equal_$Ref a b))
  :qid |$Set<$Ref>.ext-outer|
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (=>
    ($Set.equal_$Ref a b)
    (= a b))
  :pattern (($Set.equal_$Ref a b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (not (xor
    ($Set.disjoint_$Ref a b)
    (forall ((o $Ref)) (!
      (or
        (not ($Set.in_$Ref o a))
        (not ($Set.in_$Ref o b)))
      :pattern (($Set.in_$Ref o a))
      :pattern (($Set.in_$Ref o b))
      ))))
  :pattern (($Set.disjoint_$Ref a b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (and
    (=
      (+
        (+
          ($Set.card_$Ref ($Set.difference_$Ref a b))
          ($Set.card_$Ref ($Set.difference_$Ref b a)))
        ($Set.card_$Ref ($Set.intersection_$Ref a b)))
      ($Set.card_$Ref ($Set.union_$Ref a b)))
    (=
      ($Set.card_$Ref ($Set.difference_$Ref a b))
      (-
        ($Set.card_$Ref a)
        ($Set.card_$Ref ($Set.intersection_$Ref a b)))))
  :pattern (($Set.card_$Ref ($Set.difference_$Ref a b)) ($Set.card_$Ref ($Set.intersection_$Ref a b)))
  )))
(assert (forall (($a $Array)) (!
  (>= (length<Array~Int> $a) 0)
  :pattern ((length<Array~Int> $a))
  :qid |prog.length_nonneg|)))
(assert (forall (($a $Array) ($i Int)) (!
  (and
    (= (first<Ref~Array> (loc<Array~Int~Ref> $a $i)) $a)
    (= (second<Ref~Int> (loc<Array~Int~Ref> $a $i)) $i))
  :pattern ((loc<Array~Int~Ref> $a $i))
  :qid |prog.all_diff|)))
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
(declare-fun $SortWrappers.$Set<$Ref>To$Snap ($Set<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Set<$Ref> ($Snap) $Set<$Ref>)
(assert (forall ((x $Set<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$Set<$Ref>($SortWrappers.$Set<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$Set<$Ref>To$Snap x))
    :qid |$Snap.$Set<$Ref>|
    )))
(declare-fun $SortWrappers.$Set<Bool>To$Snap ($Set<Bool>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Set<Bool> ($Snap) $Set<Bool>)
(assert (forall ((x $Set<Bool>)) (!
    (= x ($SortWrappers.$SnapTo$Set<Bool>($SortWrappers.$Set<Bool>To$Snap x)))
    :pattern (($SortWrappers.$Set<Bool>To$Snap x))
    :qid |$Snap.$Set<Bool>|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$ArrayTo$Snap ($Array) $Snap)
(declare-fun $SortWrappers.$SnapTo$Array ($Snap) $Array)
(assert (forall ((x $Array)) (!
    (= x ($SortWrappers.$SnapTo$Array($SortWrappers.$ArrayTo$Snap x)))
    :pattern (($SortWrappers.$ArrayTo$Snap x))
    :qid |$Snap.$Array|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$FVF<Bool>To$Snap ($FVF<Bool>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<Bool> ($Snap) $FVF<Bool>)
(assert (forall ((x $FVF<Bool>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<Bool>($SortWrappers.$FVF<Bool>To$Snap x)))
    :pattern (($SortWrappers.$FVF<Bool>To$Snap x))
    :qid |$Snap.$FVF<Bool>|
    )))
(declare-fun $SortWrappers.$FVF<$Ref>To$Snap ($FVF<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<$Ref> ($Snap) $FVF<$Ref>)
(assert (forall ((x $FVF<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<$Ref>($SortWrappers.$FVF<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$FVF<$Ref>To$Snap x))
    :qid |$Snap.$FVF<$Ref>|
    )))
; /field_value_functions_axioms.smt2 [val: Bool]
(assert (forall ((vs $FVF<Bool>) (ws $FVF<Bool>)) (!
    (=>
      (and
        ($Set.equal_$Ref ($FVF.domain_val vs) ($FVF.domain_val ws))
        (forall ((x $Ref)) (!
          (=>
            ($Set.in_$Ref x ($FVF.domain_val vs))
            (= ($FVF.lookup_val vs x) ($FVF.lookup_val ws x)))
          :pattern (($FVF.lookup_val vs x) ($FVF.lookup_val ws x))
          :qid |qp.$FVF<Bool>-eq-inner|
          )))
      (= vs ws))
    :pattern (($SortWrappers.$FVF<Bool>To$Snap vs)
              ($SortWrappers.$FVF<Bool>To$Snap ws)
              ($FVF.after_val vs ws))
    :qid |qp.$FVF<Bool>-eq-outer|
    )))
(assert (forall ((fvf1 $FVF<Bool>) (fvf2 $FVF<Bool>) (fvf3 $FVF<Bool>)) (!
    (=>
      (and
        ($FVF.after_val fvf3 fvf2)
        ($FVF.after_val fvf2 fvf1))
      ($FVF.after_val fvf3 fvf1))
    :pattern (($FVF.after_val fvf3 fvf2) ($FVF.after_val fvf2 fvf1))
    :qid |qp.$FVF<Bool>-after_val|
    )))
(assert (forall ((fvf1 $FVF<Bool>) (fvf2 $FVF<Bool>)) (!
    (=>
      (and
        ($FVF.after_val fvf1 $fvfTOP_val)
        ($FVF.after_val fvf2 $fvfTOP_val))
      (or
        (= fvf1 fvf2)
        ($FVF.after_val fvf1 fvf2)
        ($FVF.after_val fvf2 fvf1)
      )
    )
    :pattern (($FVF.after_val fvf1 $fvfTOP_val) ($FVF.after_val fvf2 $fvfTOP_val))
    :qid |qp.$FVF<Bool>-top|
    )))
; Preamble end
; ------------------------------------------------------------
(declare-const b1@1 Bool)
(declare-const b2@2 Bool)
(declare-const a@3 $Array)
(declare-const from@4 Int)
(declare-const to@5 Int)
; ------------------------------------------------------------
; Declaring program functions
(declare-const s@$ $Snap)
(declare-fun $lte ($Snap Bool Bool) Bool)
(declare-fun $lte$ ($Snap Bool Bool) Bool)
(declare-fun $countFalse ($Snap $Array Int Int) Int)
(declare-fun $countFalse$ ($Snap $Array Int Int) Int)
; ---------- FUNCTION lte (specs well-defined) ----------
(declare-const result@6 Bool)
(push) ; 2
(pop) ; 2
(assert (forall ((s@$ $Snap) (b1@1 Bool) (b2@2 Bool)) (!
  (= ($lte$ s@$ b1@1 b2@2) ($lte s@$ b1@1 b2@2))
  :pattern (($lte s@$ b1@1 b2@2))
  )))
(assert true)
; ---------- FUNCTION lte----------
(declare-const result@7 Bool)
(push) ; 2
; [eval] !b1 || b2
; [eval] !b1
(push) ; 3
(set-option :timeout 250)
(push) ; 4
(assert (not (not b1@1)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not b1@1))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 1] b1@1
(assert b1@1)
(pop) ; 4
(push) ; 4
; [else-branch 1] !b1@1
(assert (not b1@1))
(pop) ; 4
(pop) ; 3
(pop) ; 2
(assert (forall ((s@$ $Snap) (b1@1 Bool) (b2@2 Bool)) (!
  (= ($lte s@$ b1@1 b2@2) (or (not b1@1) b2@2))
  :pattern (($lte s@$ b1@1 b2@2))
  )))
; ---------- FUNCTION countFalse (specs well-defined) ----------
(declare-const result@8 Int)
(push) ; 2
; [eval] (0 <= from) && ((from <= to) && (to <= length(a)))
; [eval] 0 <= from
(push) ; 3
(push) ; 4
(assert (not (not (<= 0 from@4))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not (<= 0 from@4)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 2] 0 <= from@4
(assert (<= 0 from@4))
; [eval] (from <= to) && (to <= length(a))
; [eval] from <= to
(push) ; 5
(push) ; 6
(assert (not (not (<= from@4 to@5))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= from@4 to@5)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 3] from@4 <= to@5
(assert (<= from@4 to@5))
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 6
(push) ; 6
; [else-branch 3] !from@4 <= to@5
(assert (not (<= from@4 to@5)))
(pop) ; 6
(pop) ; 5
(pop) ; 4
(push) ; 4
; [else-branch 2] !0 <= from@4
(assert (not (<= 0 from@4)))
(pop) ; 4
(pop) ; 3
(assert (and (<= 0 from@4) (and (<= from@4 to@5) (<= to@5 (length<Array~Int> a@3)))))
(declare-const z@9 Int)
(push) ; 3
; [eval] (from <= z) && (z < to)
; [eval] from <= z
(push) ; 4
(push) ; 5
(assert (not (not (<= from@4 z@9))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= from@4 z@9)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 4] from@4 <= z@9
(assert (<= from@4 z@9))
; [eval] z < to
(pop) ; 5
(push) ; 5
; [else-branch 4] !from@4 <= z@9
(assert (not (<= from@4 z@9)))
(pop) ; 5
(pop) ; 4
(assert (and (<= from@4 z@9) (< z@9 to@5)))
; [eval] loc(a, z)
(pop) ; 3
(declare-fun inv@10 ($Snap $Array Int Int $Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (<= from@4 (inv@10 s@$ a@3 from@4 to@5 $r))
      (< (inv@10 s@$ a@3 from@4 to@5 $r) to@5))
    (= (loc<Array~Int~Ref> a@3 (inv@10 s@$ a@3 from@4 to@5 $r)) $r))
  :pattern ((inv@10 s@$ a@3 from@4 to@5 $r))
  :qid |qp.inv@10-imp|)))
(assert (forall ((z@9 Int)) (!
  (=>
    (and (<= from@4 z@9) (< z@9 to@5))
    (= (inv@10 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 z@9)) z@9))
  :pattern ((loc<Array~Int~Ref> a@3 z@9))
  :qid |qp.inv@10-exp|)))
(assert (forall ((z@9 Int)) (!
  (=>
    (and (<= from@4 z@9) (< z@9 to@5))
    (not (= (loc<Array~Int~Ref> a@3 z@9) $Ref.null)))
  :pattern ((loc<Array~Int~Ref> a@3 z@9))
  :qid |qp.null1|)))
(pop) ; 2
(assert (forall ((s@$ $Snap) (a@3 $Array) (from@4 Int) (to@5 Int)) (!
  (= ($countFalse$ s@$ a@3 from@4 to@5) ($countFalse s@$ a@3 from@4 to@5))
  :pattern (($countFalse s@$ a@3 from@4 to@5))
  )))
(assert true)
; ---------- FUNCTION countFalse----------
(declare-const result@11 Int)
(push) ; 2
; [eval] (0 <= from) && ((from <= to) && (to <= length(a)))
; [eval] 0 <= from
(push) ; 3
(push) ; 4
(assert (not (not (<= 0 from@4))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not (<= 0 from@4)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 5] 0 <= from@4
(assert (<= 0 from@4))
; [eval] (from <= to) && (to <= length(a))
; [eval] from <= to
(push) ; 5
(push) ; 6
(assert (not (not (<= from@4 to@5))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= from@4 to@5)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 6] from@4 <= to@5
(assert (<= from@4 to@5))
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 6
(push) ; 6
; [else-branch 6] !from@4 <= to@5
(assert (not (<= from@4 to@5)))
(pop) ; 6
(pop) ; 5
(pop) ; 4
(push) ; 4
; [else-branch 5] !0 <= from@4
(assert (not (<= 0 from@4)))
(pop) ; 4
(pop) ; 3
(assert (and (<= 0 from@4) (and (<= from@4 to@5) (<= to@5 (length<Array~Int> a@3)))))
(declare-const z@12 Int)
(push) ; 3
; [eval] (from <= z) && (z < to)
; [eval] from <= z
(push) ; 4
(push) ; 5
(assert (not (not (<= from@4 z@12))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= from@4 z@12)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 7] from@4 <= z@12
(assert (<= from@4 z@12))
; [eval] z < to
(pop) ; 5
(push) ; 5
; [else-branch 7] !from@4 <= z@12
(assert (not (<= from@4 z@12)))
(pop) ; 5
(pop) ; 4
(assert (and (<= from@4 z@12) (< z@12 to@5)))
; [eval] loc(a, z)
(pop) ; 3
(declare-fun inv@13 ($Snap $Array Int Int $Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (<= from@4 (inv@13 s@$ a@3 from@4 to@5 $r))
      (< (inv@13 s@$ a@3 from@4 to@5 $r) to@5))
    (= (loc<Array~Int~Ref> a@3 (inv@13 s@$ a@3 from@4 to@5 $r)) $r))
  :pattern ((inv@13 s@$ a@3 from@4 to@5 $r))
  :qid |qp.inv@13-imp|)))
(assert (forall ((z@12 Int)) (!
  (=>
    (and (<= from@4 z@12) (< z@12 to@5))
    (= (inv@13 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 z@12)) z@12))
  :pattern ((loc<Array~Int~Ref> a@3 z@12))
  :qid |qp.inv@13-exp|)))
(assert (forall ((z@12 Int)) (!
  (=>
    (and (<= from@4 z@12) (< z@12 to@5))
    (not (= (loc<Array~Int~Ref> a@3 z@12) $Ref.null)))
  :pattern ((loc<Array~Int~Ref> a@3 z@12))
  :qid |qp.null2|)))
; [eval] (from == to ? 0 : (loc(a, from).val ? 0 : 1) + countFalse(a, from + 1, to))
; [eval] from == to
(push) ; 3
(assert (not (not (= from@4 to@5))))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
(assert (not (= from@4 to@5)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
; [then-branch 8] from@4 == to@5
(assert (= from@4 to@5))
(pop) ; 3
(push) ; 3
; [else-branch 8] from@4 != to@5
(assert (not (= from@4 to@5)))
; [eval] (loc(a, from).val ? 0 : 1) + countFalse(a, from + 1, to)
; [eval] (loc(a, from).val ? 0 : 1)
; [eval] loc(a, from)
(set-option :timeout 0)
(push) ; 4
(assert (not (not (= (loc<Array~Int~Ref> a@3 from@4) $Ref.null))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not (and
  (<= from@4 (inv@13 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 from@4)))
  (< (inv@13 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 from@4)) to@5))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@14 $FVF<Bool>)
(assert ($FVF.after_val fvf@14 $fvfTOP_val))
(assert (=>
  (and
    (<= from@4 (inv@13 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 from@4)))
    (< (inv@13 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 from@4)) to@5))
  (=
    ($FVF.lookup_val fvf@14 (loc<Array~Int~Ref> a@3 from@4))
    ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Bool> ($Snap.second s@$)) (loc<Array~Int~Ref> a@3 from@4)))))
(assert (=
  ($FVF.domain_val fvf@14)
  ($Set.singleton_$Ref (loc<Array~Int~Ref> a@3 from@4))))
(set-option :timeout 250)
(push) ; 4
(assert (not (not ($FVF.lookup_val fvf@14 (loc<Array~Int~Ref> a@3 from@4)))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not ($FVF.lookup_val fvf@14 (loc<Array~Int~Ref> a@3 from@4))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 9] Lookup(val,fvf@14,loc[Array,Int,Ref](a@3, from@4))
(assert ($FVF.lookup_val fvf@14 (loc<Array~Int~Ref> a@3 from@4)))
(pop) ; 4
(push) ; 4
; [else-branch 9] !Lookup(val,fvf@14,loc[Array,Int,Ref](a@3, from@4))
(assert (not ($FVF.lookup_val fvf@14 (loc<Array~Int~Ref> a@3 from@4))))
(pop) ; 4
(assert (ite
  ($FVF.lookup_val fvf@14 (loc<Array~Int~Ref> a@3 from@4))
  true
  (not ($FVF.lookup_val fvf@14 (loc<Array~Int~Ref> a@3 from@4)))))
; [eval] countFalse(a, from + 1, to)
; [eval] from + 1
; [eval] (0 <= from + 1) && ((from + 1 <= to) && (to <= length(a)))
; [eval] 0 <= from + 1
; [eval] from + 1
(push) ; 4
(push) ; 5
(assert (not (not (<= 0 (+ from@4 1)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= 0 (+ from@4 1))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 10] 0 <= from@4 + 1
(assert (<= 0 (+ from@4 1)))
; [eval] (from + 1 <= to) && (to <= length(a))
; [eval] from + 1 <= to
; [eval] from + 1
(push) ; 6
(push) ; 7
(assert (not (not (<= (+ from@4 1) to@5))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= (+ from@4 1) to@5)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 11] from@4 + 1 <= to@5
(assert (<= (+ from@4 1) to@5))
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 7
; [dead else-branch 11] !from@4 + 1 <= to@5
(pop) ; 6
(pop) ; 5
; [dead else-branch 10] !0 <= from@4 + 1
(pop) ; 4
(set-option :timeout 0)
(push) ; 4
(assert (not (and
  (<= 0 (+ from@4 1))
  (and (<= (+ from@4 1) to@5) (<= to@5 (length<Array~Int> a@3))))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (and
  (<= 0 (+ from@4 1))
  (and (<= (+ from@4 1) to@5) (<= to@5 (length<Array~Int> a@3)))))
(declare-const z@15 Int)
(push) ; 4
; [eval] (from + 1 <= z) && (z < to)
; [eval] from + 1 <= z
; [eval] from + 1
(push) ; 5
(set-option :timeout 250)
(push) ; 6
(assert (not (not (<= (+ from@4 1) z@15))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= (+ from@4 1) z@15)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 12] from@4 + 1 <= z@15
(assert (<= (+ from@4 1) z@15))
; [eval] z < to
(pop) ; 6
(push) ; 6
; [else-branch 12] !from@4 + 1 <= z@15
(assert (not (<= (+ from@4 1) z@15)))
(pop) ; 6
(pop) ; 5
(push) ; 5
(assert (not (not (and (<= (+ from@4 1) z@15) (< z@15 to@5)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (and (<= (+ from@4 1) z@15) (< z@15 to@5)))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 5
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= (+ from@4 1) $x) (< $x to@5))
      (and (<= (+ from@4 1) $y) (< $y to@5))
      (= (loc<Array~Int~Ref> a@3 $x) (loc<Array~Int~Ref> a@3 $y)))
    (= $x $y))
  
  :qid |qp.inj3|))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(pop) ; 4
(declare-fun inv@16 ($Snap $Array Int Int $Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (<= (+ from@4 1) (inv@16 s@$ a@3 from@4 to@5 $r))
      (< (inv@16 s@$ a@3 from@4 to@5 $r) to@5))
    (= (loc<Array~Int~Ref> a@3 (inv@16 s@$ a@3 from@4 to@5 $r)) $r))
  :pattern ((inv@16 s@$ a@3 from@4 to@5 $r))
  :qid |qp.inv@16-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= (+ from@4 1) $z) (< $z to@5))
    (= (inv@16 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@3 $z))
  :qid |qp.inv@16-exp|)))
(declare-const fvf@17 $FVF<Bool>)
(assert ($FVF.after_val fvf@17 fvf@14))
; Precomputing split data for loc[Array,Int,Ref](a@3, $z).val # W
(define-fun $pTaken1 (($r $Ref)) $Perm
  (ite
    (and
      (<= (+ from@4 1) (inv@16 s@$ a@3 from@4 to@5 $r))
      (< (inv@16 s@$ a@3 from@4 to@5 $r) to@5))
    ($Perm.min
      (ite
        (and
          (<= from@4 (inv@13 s@$ a@3 from@4 to@5 $r))
          (< (inv@13 s@$ a@3 from@4 to@5 $r) to@5))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 4
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and
          (<= from@4 (inv@13 s@$ a@3 from@4 to@5 $r))
          (< (inv@13 s@$ a@3 from@4 to@5 $r) to@5))
        $Perm.Write
        $Perm.No)
      ($pTaken1 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 4
(assert (not (forall (($r $Ref)) (!
  (=>
    (and
      (<= (+ from@4 1) (inv@16 s@$ a@3 from@4 to@5 $r))
      (< (inv@16 s@$ a@3 from@4 to@5 $r) to@5))
    (= (- $Perm.Write ($pTaken1 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and
        (<= from@4 (inv@13 s@$ a@3 from@4 to@5 $r))
        (< (inv@13 s@$ a@3 from@4 to@5 $r) to@5))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@17)))
    (=
      ($FVF.lookup_val fvf@17 $r)
      ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Bool> ($Snap.second s@$)) $r)))
  :pattern (($FVF.lookup_val fvf@17 $r) (inv@13 s@$ a@3 from@4 to@5 $r))
  :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Bool> ($Snap.second s@$)) $r) (inv@13 s@$ a@3 from@4 to@5 $r))
  :qid |qp.fvf@17-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@17))
    (and
      (<= (+ from@4 1) (inv@16 s@$ a@3 from@4 to@5 $r))
      (< (inv@16 s@$ a@3 from@4 to@5 $r) to@5))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@17)))
  :qid |qp.fvf@17-dom-inv@16|)))
(pop) ; 3
(assert (ite
  (= from@4 to@5)
  true
  (and
    (forall (($r $Ref)) (!
      (not (xor
        ($Set.in_$Ref $r ($FVF.domain_val fvf@17))
        (and
          (<= (+ from@4 1) (inv@16 s@$ a@3 from@4 to@5 $r))
          (< (inv@16 s@$ a@3 from@4 to@5 $r) to@5))))
      :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@17)))
      :qid |qp.fvf@17-dom-inv@16|))
    (forall (($r $Ref)) (!
      (=>
        (and
          (and
            (<= from@4 (inv@13 s@$ a@3 from@4 to@5 $r))
            (< (inv@13 s@$ a@3 from@4 to@5 $r) to@5))
          ($Set.in_$Ref $r ($FVF.domain_val fvf@17)))
        (=
          ($FVF.lookup_val fvf@17 $r)
          ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Bool> ($Snap.second s@$)) $r)))
      :pattern (($FVF.lookup_val fvf@17 $r) (inv@13 s@$ a@3 from@4 to@5 $r))
      :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Bool> ($Snap.second s@$)) $r) (inv@13 s@$ a@3 from@4 to@5 $r))
      :qid |qp.fvf@17-lookup-1|))
    ($FVF.after_val fvf@17 fvf@14)
    (forall (($z Int)) (!
      (=>
        (and (<= (+ from@4 1) $z) (< $z to@5))
        (= (inv@16 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 $z)) $z))
      :pattern ((loc<Array~Int~Ref> a@3 $z))
      :qid |qp.inv@16-exp|))
    (forall (($r $Ref)) (!
      (=>
        (and
          (<= (+ from@4 1) (inv@16 s@$ a@3 from@4 to@5 $r))
          (< (inv@16 s@$ a@3 from@4 to@5 $r) to@5))
        (= (loc<Array~Int~Ref> a@3 (inv@16 s@$ a@3 from@4 to@5 $r)) $r))
      :pattern ((inv@16 s@$ a@3 from@4 to@5 $r))
      :qid |qp.inv@16-imp|))
    (and
      (<= 0 (+ from@4 1))
      (and (<= (+ from@4 1) to@5) (<= to@5 (length<Array~Int> a@3))))
    (ite
      ($FVF.lookup_val fvf@14 (loc<Array~Int~Ref> a@3 from@4))
      true
      (not ($FVF.lookup_val fvf@14 (loc<Array~Int~Ref> a@3 from@4))))
    (=
      ($FVF.domain_val fvf@14)
      ($Set.singleton_$Ref (loc<Array~Int~Ref> a@3 from@4)))
    (=>
      (and
        (<= from@4 (inv@13 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 from@4)))
        (< (inv@13 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 from@4)) to@5))
      (=
        ($FVF.lookup_val fvf@14 (loc<Array~Int~Ref> a@3 from@4))
        ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Bool> ($Snap.second s@$)) (loc<Array~Int~Ref> a@3 from@4))))
    ($FVF.after_val fvf@14 $fvfTOP_val)
    (not (= from@4 to@5)))))
(pop) ; 2
(assert ($FVF.after_val fvf@17 fvf@14))
(assert ($FVF.after_val fvf@14 $fvfTOP_val))
(assert (forall ((s@$ $Snap) (a@3 $Array) (from@4 Int) (to@5 Int)) (!
  (exists ((fvf@17 $FVF<Bool>) (fvf@14 $FVF<Bool>)) (!
    (and
      (=>
        (and
          (<= 0 from@4)
          (and (<= from@4 to@5) (<= to@5 (length<Array~Int> a@3))))
        (=
          ($countFalse s@$ a@3 from@4 to@5)
          (ite
            (= from@4 to@5)
            0
            (+
              (ite ($FVF.lookup_val fvf@14 (loc<Array~Int~Ref> a@3 from@4)) 0 1)
              ($countFalse$ ($Snap.combine
                $Snap.unit
                ($SortWrappers.$FVF<Bool>To$Snap fvf@17)) a@3 (+ from@4 1) to@5)))))
      (=>
        (not (= from@4 to@5))
        (and
          (=
            ($FVF.domain_val fvf@14)
            ($Set.singleton_$Ref (loc<Array~Int~Ref> a@3 from@4)))
          (=>
            (and
              (<=
                from@4
                (inv@13 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 from@4)))
              (<
                (inv@13 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 from@4))
                to@5))
            (=
              ($FVF.lookup_val fvf@14 (loc<Array~Int~Ref> a@3 from@4))
              ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Bool> ($Snap.second s@$)) (loc<Array~Int~Ref> a@3 from@4))))))
      (=>
        (not (= from@4 to@5))
        (and
          (forall (($z Int)) (!
            (=>
              (and (<= (+ from@4 1) $z) (< $z to@5))
              (= (inv@16 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 $z)) $z))
            :pattern ((loc<Array~Int~Ref> a@3 $z))
            :qid |qp.inv@16-exp|))
          (forall (($r $Ref)) (!
            (=>
              (and
                (<= (+ from@4 1) (inv@16 s@$ a@3 from@4 to@5 $r))
                (< (inv@16 s@$ a@3 from@4 to@5 $r) to@5))
              (= (loc<Array~Int~Ref> a@3 (inv@16 s@$ a@3 from@4 to@5 $r)) $r))
            :pattern ((inv@16 s@$ a@3 from@4 to@5 $r))
            :qid |qp.inv@16-imp|))
          (forall (($r $Ref)) (!
            (not (xor
              ($Set.in_$Ref $r ($FVF.domain_val fvf@17))
              (and
                (<= (+ from@4 1) (inv@16 s@$ a@3 from@4 to@5 $r))
                (< (inv@16 s@$ a@3 from@4 to@5 $r) to@5))))
            :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@17)))
            :qid |qp.fvf@17-dom-inv@16|))
          (forall (($r $Ref)) (!
            (=>
              (and
                (and
                  (<= from@4 (inv@13 s@$ a@3 from@4 to@5 $r))
                  (< (inv@13 s@$ a@3 from@4 to@5 $r) to@5))
                ($Set.in_$Ref $r ($FVF.domain_val fvf@17)))
              (=
                ($FVF.lookup_val fvf@17 $r)
                ($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Bool> ($Snap.second s@$)) $r)))
            :pattern (($FVF.lookup_val fvf@17 $r) (inv@13 s@$ a@3 from@4 to@5 $r))
            :pattern (($FVF.lookup_val ($SortWrappers.$SnapTo$FVF<Bool> ($Snap.second s@$)) $r) (inv@13 s@$ a@3 from@4 to@5 $r))
            :qid |qp.fvf@17-lookup-1|))))
      (and
        (forall ((z@12 Int)) (!
          (=>
            (and (<= from@4 z@12) (< z@12 to@5))
            (= (inv@13 s@$ a@3 from@4 to@5 (loc<Array~Int~Ref> a@3 z@12)) z@12))
          :pattern ((loc<Array~Int~Ref> a@3 z@12))
          :qid |qp.inv@13-exp|))
        (forall (($r $Ref)) (!
          (=>
            (and
              (<= from@4 (inv@13 s@$ a@3 from@4 to@5 $r))
              (< (inv@13 s@$ a@3 from@4 to@5 $r) to@5))
            (= (loc<Array~Int~Ref> a@3 (inv@13 s@$ a@3 from@4 to@5 $r)) $r))
          :pattern ((inv@13 s@$ a@3 from@4 to@5 $r))
          :qid |qp.inv@13-imp|)))
      ($FVF.after_val fvf@17 fvf@14)
      ($FVF.after_val fvf@14 $fvfTOP_val))
    
    ))
  :pattern (($countFalse s@$ a@3 from@4 to@5))
  )))
; ---------- swap ----------
(declare-const a@18 $Array)
(declare-const i@19 Int)
(declare-const j@20 Int)
(declare-const t@21 Bool)
(push) ; 2
(declare-const $t@22 $Snap)
(declare-const $t@23 Bool)
(declare-const $t@24 Bool)
(assert (=
  $t@22
  ($Snap.combine
    ($SortWrappers.BoolTo$Snap $t@23)
    ($SortWrappers.BoolTo$Snap $t@24))))
; [eval] loc(a, i)
(assert (not (= (loc<Array~Int~Ref> a@18 i@19) $Ref.null)))
; [eval] loc(a, j)
(assert (not (= (loc<Array~Int~Ref> a@18 j@20) $Ref.null)))
(set-option :timeout 0)
(push) ; 3
(assert (not (= (loc<Array~Int~Ref> a@18 i@19) (loc<Array~Int~Ref> a@18 j@20))))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
(declare-const $t@25 $Snap)
(declare-const $t@26 Bool)
(declare-const $t@27 Bool)
(assert (=
  $t@25
  ($Snap.combine
    ($SortWrappers.BoolTo$Snap $t@26)
    ($SortWrappers.BoolTo$Snap $t@27))))
; [eval] loc(a, i)
; [eval] loc(a, j)
(push) ; 4
(assert (not (= (loc<Array~Int~Ref> a@18 i@19) (loc<Array~Int~Ref> a@18 j@20))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; [eval] loc(a, i).val == old(loc(a, j).val)
; [eval] loc(a, i)
; [eval] old(loc(a, j).val)
; [eval] loc(a, j)
(assert (= $t@26 $t@24))
; [eval] loc(a, j).val == old(loc(a, i).val)
; [eval] loc(a, j)
; [eval] old(loc(a, i).val)
; [eval] loc(a, i)
(assert (= $t@27 $t@23))
(pop) ; 3
(push) ; 3
; [exec]
; t := loc(a, i).val
; [eval] loc(a, i)
; [exec]
; loc(a, i).val := loc(a, j).val
; [eval] loc(a, i)
; [eval] loc(a, j)
; [exec]
; loc(a, j).val := t
; [eval] loc(a, j)
; [eval] loc(a, i)
; [eval] loc(a, j)
; [eval] loc(a, i).val == old(loc(a, j).val)
; [eval] loc(a, i)
; [eval] old(loc(a, j).val)
; [eval] loc(a, j)
; [eval] loc(a, j).val == old(loc(a, i).val)
; [eval] loc(a, j)
; [eval] old(loc(a, i).val)
; [eval] loc(a, i)
(pop) ; 3
(pop) ; 2
; ---------- lemmaFront ----------
(declare-const a@28 $Array)
(declare-const from@29 Int)
(declare-const to@30 Int)
(push) ; 2
; [eval] (0 <= from) && ((from < to) && (to <= length(a)))
; [eval] 0 <= from
(push) ; 3
(set-option :timeout 250)
(push) ; 4
(assert (not (not (<= 0 from@29))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
(assert (not (<= 0 from@29)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 13] 0 <= from@29
(assert (<= 0 from@29))
; [eval] (from < to) && (to <= length(a))
; [eval] from < to
(push) ; 5
(push) ; 6
(assert (not (not (< from@29 to@30))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (< from@29 to@30)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 14] from@29 < to@30
(assert (< from@29 to@30))
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 6
(push) ; 6
; [else-branch 14] !from@29 < to@30
(assert (not (< from@29 to@30)))
(pop) ; 6
(pop) ; 5
(pop) ; 4
(push) ; 4
; [else-branch 13] !0 <= from@29
(assert (not (<= 0 from@29)))
(pop) ; 4
(pop) ; 3
(assert (and (<= 0 from@29) (and (< from@29 to@30) (<= to@30 (length<Array~Int> a@28)))))
(declare-const z@31 Int)
(push) ; 3
; [eval] (from <= z) && (z < to)
; [eval] from <= z
(push) ; 4
(push) ; 5
(assert (not (not (<= from@29 z@31))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= from@29 z@31)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 15] from@29 <= z@31
(assert (<= from@29 z@31))
; [eval] z < to
(pop) ; 5
(push) ; 5
; [else-branch 15] !from@29 <= z@31
(assert (not (<= from@29 z@31)))
(pop) ; 5
(pop) ; 4
(assert (and (<= from@29 z@31) (< z@31 to@30)))
; [eval] loc(a, z)
(pop) ; 3
(declare-const $t@32 $FVF<Bool>)
(assert ($FVF.after_val $t@32 fvf@17))
(declare-fun inv@33 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
    (= (loc<Array~Int~Ref> a@28 (inv@33 $r)) $r))
  :pattern ((inv@33 $r))
  :qid |qp.inv@33-imp|)))
(assert (forall ((z@31 Int)) (!
  (=>
    (and (<= from@29 z@31) (< z@31 to@30))
    (= (inv@33 (loc<Array~Int~Ref> a@28 z@31)) z@31))
  :pattern ((loc<Array~Int~Ref> a@28 z@31))
  :qid |qp.inv@33-exp|)))
(assert (forall ((z@31 Int)) (!
  (=>
    (and (<= from@29 z@31) (< z@31 to@30))
    (not (= (loc<Array~Int~Ref> a@28 z@31) $Ref.null)))
  :pattern ((loc<Array~Int~Ref> a@28 z@31))
  :qid |qp.null4|)))
; [eval] !loc(a, from).val
; [eval] loc(a, from)
(set-option :timeout 0)
(push) ; 3
(assert (not (not (= (loc<Array~Int~Ref> a@28 from@29) $Ref.null))))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(push) ; 3
(assert (not (and
  (<= from@29 (inv@33 (loc<Array~Int~Ref> a@28 from@29)))
  (< (inv@33 (loc<Array~Int~Ref> a@28 from@29)) to@30))))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@34 $FVF<Bool>)
(assert ($FVF.after_val fvf@34 $t@32))
(assert (=>
  (and
    (<= from@29 (inv@33 (loc<Array~Int~Ref> a@28 from@29)))
    (< (inv@33 (loc<Array~Int~Ref> a@28 from@29)) to@30))
  (=
    ($FVF.lookup_val fvf@34 (loc<Array~Int~Ref> a@28 from@29))
    ($FVF.lookup_val $t@32 (loc<Array~Int~Ref> a@28 from@29)))))
(assert (=
  ($FVF.domain_val fvf@34)
  ($Set.singleton_$Ref (loc<Array~Int~Ref> a@28 from@29))))
(assert (not ($FVF.lookup_val fvf@34 (loc<Array~Int~Ref> a@28 from@29))))
(push) ; 3
(declare-const z@35 Int)
(push) ; 4
; [eval] (from <= z) && (z < to)
; [eval] from <= z
(push) ; 5
(set-option :timeout 250)
(push) ; 6
(assert (not (not (<= from@29 z@35))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= from@29 z@35)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 16] from@29 <= z@35
(assert (<= from@29 z@35))
; [eval] z < to
(pop) ; 6
(push) ; 6
; [else-branch 16] !from@29 <= z@35
(assert (not (<= from@29 z@35)))
(pop) ; 6
(pop) ; 5
(assert (and (<= from@29 z@35) (< z@35 to@30)))
; [eval] loc(a, z)
(pop) ; 4
(declare-const $t@36 $FVF<Bool>)
(assert ($FVF.after_val $t@36 fvf@34))
(declare-fun inv@37 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= from@29 (inv@37 $r)) (< (inv@37 $r) to@30))
    (= (loc<Array~Int~Ref> a@28 (inv@37 $r)) $r))
  :pattern ((inv@37 $r))
  :qid |qp.inv@37-imp|)))
(assert (forall ((z@35 Int)) (!
  (=>
    (and (<= from@29 z@35) (< z@35 to@30))
    (= (inv@37 (loc<Array~Int~Ref> a@28 z@35)) z@35))
  :pattern ((loc<Array~Int~Ref> a@28 z@35))
  :qid |qp.inv@37-exp|)))
(assert (forall ((z@35 Int)) (!
  (=>
    (and (<= from@29 z@35) (< z@35 to@30))
    (not (= (loc<Array~Int~Ref> a@28 z@35) $Ref.null)))
  :pattern ((loc<Array~Int~Ref> a@28 z@35))
  :qid |qp.null5|)))
; [eval] 1 + countFalse(a, from + 1, to) == countFalse(a, from, to)
; [eval] 1 + countFalse(a, from + 1, to)
; [eval] countFalse(a, from + 1, to)
; [eval] from + 1
; [eval] (0 <= from + 1) && ((from + 1 <= to) && (to <= length(a)))
; [eval] 0 <= from + 1
; [eval] from + 1
(push) ; 4
(push) ; 5
(assert (not (not (<= 0 (+ from@29 1)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= 0 (+ from@29 1))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 17] 0 <= from@29 + 1
(assert (<= 0 (+ from@29 1)))
; [eval] (from + 1 <= to) && (to <= length(a))
; [eval] from + 1 <= to
; [eval] from + 1
(push) ; 6
(push) ; 7
(assert (not (not (<= (+ from@29 1) to@30))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= (+ from@29 1) to@30)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 18] from@29 + 1 <= to@30
(assert (<= (+ from@29 1) to@30))
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 7
; [dead else-branch 18] !from@29 + 1 <= to@30
(pop) ; 6
(pop) ; 5
; [dead else-branch 17] !0 <= from@29 + 1
(pop) ; 4
(set-option :timeout 0)
(push) ; 4
(assert (not (and
  (<= 0 (+ from@29 1))
  (and (<= (+ from@29 1) to@30) (<= to@30 (length<Array~Int> a@28))))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (and
  (<= 0 (+ from@29 1))
  (and (<= (+ from@29 1) to@30) (<= to@30 (length<Array~Int> a@28)))))
(declare-const z@38 Int)
(push) ; 4
; [eval] (from + 1 <= z) && (z < to)
; [eval] from + 1 <= z
; [eval] from + 1
(push) ; 5
(set-option :timeout 250)
(push) ; 6
(assert (not (not (<= (+ from@29 1) z@38))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= (+ from@29 1) z@38)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 19] from@29 + 1 <= z@38
(assert (<= (+ from@29 1) z@38))
; [eval] z < to
(pop) ; 6
(push) ; 6
; [else-branch 19] !from@29 + 1 <= z@38
(assert (not (<= (+ from@29 1) z@38)))
(pop) ; 6
(pop) ; 5
(push) ; 5
(assert (not (not (and (<= (+ from@29 1) z@38) (< z@38 to@30)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (and (<= (+ from@29 1) z@38) (< z@38 to@30)))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 5
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= (+ from@29 1) $x) (< $x to@30))
      (and (<= (+ from@29 1) $y) (< $y to@30))
      (= (loc<Array~Int~Ref> a@28 $x) (loc<Array~Int~Ref> a@28 $y)))
    (= $x $y))
  
  :qid |qp.inj6|))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(pop) ; 4
(declare-fun inv@39 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= (+ from@29 1) (inv@39 $r)) (< (inv@39 $r) to@30))
    (= (loc<Array~Int~Ref> a@28 (inv@39 $r)) $r))
  :pattern ((inv@39 $r))
  :qid |qp.inv@39-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= (+ from@29 1) $z) (< $z to@30))
    (= (inv@39 (loc<Array~Int~Ref> a@28 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@28 $z))
  :qid |qp.inv@39-exp|)))
(declare-const fvf@40 $FVF<Bool>)
(assert ($FVF.after_val fvf@40 $t@36))
; Precomputing split data for loc[Array,Int,Ref](a@28, $z).val # W
(define-fun $pTaken2 (($r $Ref)) $Perm
  (ite
    (and (<= (+ from@29 1) (inv@39 $r)) (< (inv@39 $r) to@30))
    ($Perm.min
      (ite
        (and (<= from@29 (inv@37 $r)) (< (inv@37 $r) to@30))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 4
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= from@29 (inv@37 $r)) (< (inv@37 $r) to@30))
        $Perm.Write
        $Perm.No)
      ($pTaken2 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 4
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= (+ from@29 1) (inv@39 $r)) (< (inv@39 $r) to@30))
    (= (- $Perm.Write ($pTaken2 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= from@29 (inv@37 $r)) (< (inv@37 $r) to@30))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@40)))
    (= ($FVF.lookup_val fvf@40 $r) ($FVF.lookup_val $t@36 $r)))
  :pattern (($FVF.lookup_val fvf@40 $r) (inv@37 $r))
  :pattern (($FVF.lookup_val $t@36 $r) (inv@37 $r))
  :qid |qp.fvf@40-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@40))
    (and (<= (+ from@29 1) (inv@39 $r)) (< (inv@39 $r) to@30))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@40)))
  :qid |qp.fvf@40-dom-inv@39|)))
; [eval] countFalse(a, from, to)
; [eval] (0 <= from) && ((from <= to) && (to <= length(a)))
; [eval] 0 <= from
(push) ; 4
(set-option :timeout 250)
(push) ; 5
(assert (not (not (<= 0 from@29))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= 0 from@29)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 20] 0 <= from@29
(assert (<= 0 from@29))
; [eval] (from <= to) && (to <= length(a))
; [eval] from <= to
(push) ; 6
(push) ; 7
(assert (not (not (<= from@29 to@30))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= from@29 to@30)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 21] from@29 <= to@30
(assert (<= from@29 to@30))
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 7
; [dead else-branch 21] !from@29 <= to@30
(pop) ; 6
(pop) ; 5
; [dead else-branch 20] !0 <= from@29
(pop) ; 4
(set-option :timeout 0)
(push) ; 4
(assert (not (and (<= 0 from@29) (and (<= from@29 to@30) (<= to@30 (length<Array~Int> a@28))))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 from@29) (and (<= from@29 to@30) (<= to@30 (length<Array~Int> a@28)))))
(declare-const z@41 Int)
(push) ; 4
; [eval] (from <= z) && (z < to)
; [eval] from <= z
(push) ; 5
(set-option :timeout 250)
(push) ; 6
(assert (not (not (<= from@29 z@41))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= from@29 z@41)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 22] from@29 <= z@41
(assert (<= from@29 z@41))
; [eval] z < to
(pop) ; 6
(push) ; 6
; [else-branch 22] !from@29 <= z@41
(assert (not (<= from@29 z@41)))
(pop) ; 6
(pop) ; 5
(push) ; 5
(assert (not (not (and (<= from@29 z@41) (< z@41 to@30)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (and (<= from@29 z@41) (< z@41 to@30)))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 5
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= from@29 $x) (< $x to@30))
      (and (<= from@29 $y) (< $y to@30))
      (= (loc<Array~Int~Ref> a@28 $x) (loc<Array~Int~Ref> a@28 $y)))
    (= $x $y))
  
  :qid |qp.inj7|))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(pop) ; 4
(declare-fun inv@42 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= from@29 (inv@42 $r)) (< (inv@42 $r) to@30))
    (= (loc<Array~Int~Ref> a@28 (inv@42 $r)) $r))
  :pattern ((inv@42 $r))
  :qid |qp.inv@42-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= from@29 $z) (< $z to@30))
    (= (inv@42 (loc<Array~Int~Ref> a@28 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@28 $z))
  :qid |qp.inv@42-exp|)))
(declare-const fvf@43 $FVF<Bool>)
(assert ($FVF.after_val fvf@43 fvf@40))
; Precomputing split data for loc[Array,Int,Ref](a@28, $z).val # W
(define-fun $pTaken3 (($r $Ref)) $Perm
  (ite
    (and (<= from@29 (inv@42 $r)) (< (inv@42 $r) to@30))
    ($Perm.min
      (ite
        (and (<= from@29 (inv@37 $r)) (< (inv@37 $r) to@30))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 4
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= from@29 (inv@37 $r)) (< (inv@37 $r) to@30))
        $Perm.Write
        $Perm.No)
      ($pTaken3 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 4
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= from@29 (inv@42 $r)) (< (inv@42 $r) to@30))
    (= (- $Perm.Write ($pTaken3 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= from@29 (inv@37 $r)) (< (inv@37 $r) to@30))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@43)))
    (= ($FVF.lookup_val fvf@43 $r) ($FVF.lookup_val $t@36 $r)))
  :pattern (($FVF.lookup_val fvf@43 $r) (inv@37 $r))
  :pattern (($FVF.lookup_val $t@36 $r) (inv@37 $r))
  :qid |qp.fvf@43-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@43))
    (and (<= from@29 (inv@42 $r)) (< (inv@42 $r) to@30))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@43)))
  :qid |qp.fvf@43-dom-inv@42|)))
(assert (=
  (+
    1
    ($countFalse ($Snap.combine
      $Snap.unit
      ($SortWrappers.$FVF<Bool>To$Snap fvf@40)) a@28 (+ from@29 1) to@30))
  ($countFalse ($Snap.combine
    $Snap.unit
    ($SortWrappers.$FVF<Bool>To$Snap fvf@43)) a@28 from@29 to@30)))
(pop) ; 3
(push) ; 3
; [exec]
; assert countFalse(a, from, to) == (from == to ? 0 : (loc(a, from).val ? 0 : 1) + countFalse(a, from + 1, to))
; [eval] countFalse(a, from, to) == (from == to ? 0 : (loc(a, from).val ? 0 : 1) + countFalse(a, from + 1, to))
; [eval] countFalse(a, from, to)
; [eval] (0 <= from) && ((from <= to) && (to <= length(a)))
; [eval] 0 <= from
(push) ; 4
(set-option :timeout 250)
(push) ; 5
(assert (not (not (<= 0 from@29))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= 0 from@29)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 23] 0 <= from@29
(assert (<= 0 from@29))
; [eval] (from <= to) && (to <= length(a))
; [eval] from <= to
(push) ; 6
(push) ; 7
(assert (not (not (<= from@29 to@30))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= from@29 to@30)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 24] from@29 <= to@30
(assert (<= from@29 to@30))
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 7
; [dead else-branch 24] !from@29 <= to@30
(pop) ; 6
(pop) ; 5
; [dead else-branch 23] !0 <= from@29
(pop) ; 4
(set-option :timeout 0)
(push) ; 4
(assert (not (and (<= 0 from@29) (and (<= from@29 to@30) (<= to@30 (length<Array~Int> a@28))))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 from@29) (and (<= from@29 to@30) (<= to@30 (length<Array~Int> a@28)))))
(declare-const z@44 Int)
(push) ; 4
; [eval] (from <= z) && (z < to)
; [eval] from <= z
(push) ; 5
(set-option :timeout 250)
(push) ; 6
(assert (not (not (<= from@29 z@44))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= from@29 z@44)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 25] from@29 <= z@44
(assert (<= from@29 z@44))
; [eval] z < to
(pop) ; 6
(push) ; 6
; [else-branch 25] !from@29 <= z@44
(assert (not (<= from@29 z@44)))
(pop) ; 6
(pop) ; 5
(push) ; 5
(assert (not (not (and (<= from@29 z@44) (< z@44 to@30)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (and (<= from@29 z@44) (< z@44 to@30)))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 5
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= from@29 $x) (< $x to@30))
      (and (<= from@29 $y) (< $y to@30))
      (= (loc<Array~Int~Ref> a@28 $x) (loc<Array~Int~Ref> a@28 $y)))
    (= $x $y))
  
  :qid |qp.inj8|))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(pop) ; 4
(declare-fun inv@45 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= from@29 (inv@45 $r)) (< (inv@45 $r) to@30))
    (= (loc<Array~Int~Ref> a@28 (inv@45 $r)) $r))
  :pattern ((inv@45 $r))
  :qid |qp.inv@45-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= from@29 $z) (< $z to@30))
    (= (inv@45 (loc<Array~Int~Ref> a@28 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@28 $z))
  :qid |qp.inv@45-exp|)))
(declare-const fvf@46 $FVF<Bool>)
(assert ($FVF.after_val fvf@46 fvf@43))
; Precomputing split data for loc[Array,Int,Ref](a@28, $z).val # W
(define-fun $pTaken4 (($r $Ref)) $Perm
  (ite
    (and (<= from@29 (inv@45 $r)) (< (inv@45 $r) to@30))
    ($Perm.min
      (ite
        (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 4
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
        $Perm.Write
        $Perm.No)
      ($pTaken4 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 4
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= from@29 (inv@45 $r)) (< (inv@45 $r) to@30))
    (= (- $Perm.Write ($pTaken4 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@46)))
    (= ($FVF.lookup_val fvf@46 $r) ($FVF.lookup_val $t@32 $r)))
  :pattern (($FVF.lookup_val fvf@46 $r) (inv@33 $r))
  :pattern (($FVF.lookup_val $t@32 $r) (inv@33 $r))
  :qid |qp.fvf@46-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@46))
    (and (<= from@29 (inv@45 $r)) (< (inv@45 $r) to@30))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@46)))
  :qid |qp.fvf@46-dom-inv@45|)))
; [eval] (from == to ? 0 : (loc(a, from).val ? 0 : 1) + countFalse(a, from + 1, to))
; [eval] from == to
(set-option :timeout 250)
(push) ; 4
(assert (not (not (= from@29 to@30))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; [dead then-branch 26] from@29 == to@30
(push) ; 4
; [else-branch 26] from@29 != to@30
(assert (not (= from@29 to@30)))
; [eval] (loc(a, from).val ? 0 : 1) + countFalse(a, from + 1, to)
; [eval] (loc(a, from).val ? 0 : 1)
; [eval] loc(a, from)
(set-option :timeout 0)
(push) ; 5
(assert (not (not (= (loc<Array~Int~Ref> a@28 from@29) $Ref.null))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (and
  (<= from@29 (inv@33 (loc<Array~Int~Ref> a@28 from@29)))
  (< (inv@33 (loc<Array~Int~Ref> a@28 from@29)) to@30))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@47 $FVF<Bool>)
(assert ($FVF.after_val fvf@47 fvf@46))
; [dead then-branch 27] Lookup(val,fvf@34,loc[Array,Int,Ref](a@28, from@29))
(push) ; 5
; [else-branch 27] !Lookup(val,fvf@34,loc[Array,Int,Ref](a@28, from@29))
(pop) ; 5
(declare-const $deadThen@48 Int)
; [eval] countFalse(a, from + 1, to)
; [eval] from + 1
; [eval] (0 <= from + 1) && ((from + 1 <= to) && (to <= length(a)))
; [eval] 0 <= from + 1
; [eval] from + 1
(push) ; 5
(set-option :timeout 250)
(push) ; 6
(assert (not (not (<= 0 (+ from@29 1)))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= 0 (+ from@29 1))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 28] 0 <= from@29 + 1
(assert (<= 0 (+ from@29 1)))
; [eval] (from + 1 <= to) && (to <= length(a))
; [eval] from + 1 <= to
; [eval] from + 1
(push) ; 7
(push) ; 8
(assert (not (not (<= (+ from@29 1) to@30))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
(assert (not (<= (+ from@29 1) to@30)))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 29] from@29 + 1 <= to@30
(assert (<= (+ from@29 1) to@30))
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 8
; [dead else-branch 29] !from@29 + 1 <= to@30
(pop) ; 7
(pop) ; 6
; [dead else-branch 28] !0 <= from@29 + 1
(pop) ; 5
(set-option :timeout 0)
(push) ; 5
(assert (not (and
  (<= 0 (+ from@29 1))
  (and (<= (+ from@29 1) to@30) (<= to@30 (length<Array~Int> a@28))))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (and
  (<= 0 (+ from@29 1))
  (and (<= (+ from@29 1) to@30) (<= to@30 (length<Array~Int> a@28)))))
(declare-const z@49 Int)
(push) ; 5
; [eval] (from + 1 <= z) && (z < to)
; [eval] from + 1 <= z
; [eval] from + 1
(push) ; 6
(set-option :timeout 250)
(push) ; 7
(assert (not (not (<= (+ from@29 1) z@49))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= (+ from@29 1) z@49)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 30] from@29 + 1 <= z@49
(assert (<= (+ from@29 1) z@49))
; [eval] z < to
(pop) ; 7
(push) ; 7
; [else-branch 30] !from@29 + 1 <= z@49
(assert (not (<= (+ from@29 1) z@49)))
(pop) ; 7
(pop) ; 6
(push) ; 6
(assert (not (not (and (<= (+ from@29 1) z@49) (< z@49 to@30)))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and (<= (+ from@29 1) z@49) (< z@49 to@30)))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= (+ from@29 1) $x) (< $x to@30))
      (and (<= (+ from@29 1) $y) (< $y to@30))
      (= (loc<Array~Int~Ref> a@28 $x) (loc<Array~Int~Ref> a@28 $y)))
    (= $x $y))
  
  :qid |qp.inj9|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(pop) ; 5
(declare-fun inv@50 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= (+ from@29 1) (inv@50 $r)) (< (inv@50 $r) to@30))
    (= (loc<Array~Int~Ref> a@28 (inv@50 $r)) $r))
  :pattern ((inv@50 $r))
  :qid |qp.inv@50-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= (+ from@29 1) $z) (< $z to@30))
    (= (inv@50 (loc<Array~Int~Ref> a@28 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@28 $z))
  :qid |qp.inv@50-exp|)))
(declare-const fvf@51 $FVF<Bool>)
(assert ($FVF.after_val fvf@51 fvf@47))
; Precomputing split data for loc[Array,Int,Ref](a@28, $z).val # W
(define-fun $pTaken5 (($r $Ref)) $Perm
  (ite
    (and (<= (+ from@29 1) (inv@50 $r)) (< (inv@50 $r) to@30))
    ($Perm.min
      (ite
        (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
        $Perm.Write
        $Perm.No)
      ($pTaken5 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= (+ from@29 1) (inv@50 $r)) (< (inv@50 $r) to@30))
    (= (- $Perm.Write ($pTaken5 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@51)))
    (= ($FVF.lookup_val fvf@51 $r) ($FVF.lookup_val $t@32 $r)))
  :pattern (($FVF.lookup_val fvf@51 $r) (inv@33 $r))
  :pattern (($FVF.lookup_val $t@32 $r) (inv@33 $r))
  :qid |qp.fvf@51-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@51))
    (and (<= (+ from@29 1) (inv@50 $r)) (< (inv@50 $r) to@30))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@51)))
  :qid |qp.fvf@51-dom-inv@50|)))
(pop) ; 4
(assert (ite
  (= from@29 to@30)
  true
  (and
    (forall (($r $Ref)) (!
      (not (xor
        ($Set.in_$Ref $r ($FVF.domain_val fvf@51))
        (and (<= (+ from@29 1) (inv@50 $r)) (< (inv@50 $r) to@30))))
      :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@51)))
      :qid |qp.fvf@51-dom-inv@50|))
    (forall (($r $Ref)) (!
      (=>
        (and
          (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
          ($Set.in_$Ref $r ($FVF.domain_val fvf@51)))
        (= ($FVF.lookup_val fvf@51 $r) ($FVF.lookup_val $t@32 $r)))
      :pattern (($FVF.lookup_val fvf@51 $r) (inv@33 $r))
      :pattern (($FVF.lookup_val $t@32 $r) (inv@33 $r))
      :qid |qp.fvf@51-lookup-1|))
    ($FVF.after_val fvf@51 fvf@47)
    (forall (($z Int)) (!
      (=>
        (and (<= (+ from@29 1) $z) (< $z to@30))
        (= (inv@50 (loc<Array~Int~Ref> a@28 $z)) $z))
      :pattern ((loc<Array~Int~Ref> a@28 $z))
      :qid |qp.inv@50-exp|))
    (forall (($r $Ref)) (!
      (=>
        (and (<= (+ from@29 1) (inv@50 $r)) (< (inv@50 $r) to@30))
        (= (loc<Array~Int~Ref> a@28 (inv@50 $r)) $r))
      :pattern ((inv@50 $r))
      :qid |qp.inv@50-imp|))
    (and
      (<= 0 (+ from@29 1))
      (and (<= (+ from@29 1) to@30) (<= to@30 (length<Array~Int> a@28))))
    ($FVF.after_val fvf@47 fvf@46)
    (not (= from@29 to@30)))))
(declare-const $deadThen@52 Int)
(set-option :timeout 0)
(push) ; 4
(assert (not (=
  ($countFalse ($Snap.combine
    $Snap.unit
    ($SortWrappers.$FVF<Bool>To$Snap fvf@46)) a@28 from@29 to@30)
  (ite
    (= from@29 to@30)
    $deadThen@52
    (+
      (ite
        ($FVF.lookup_val fvf@34 (loc<Array~Int~Ref> a@28 from@29))
        $deadThen@48
        1)
      ($countFalse ($Snap.combine
        $Snap.unit
        ($SortWrappers.$FVF<Bool>To$Snap fvf@51)) a@28 (+ from@29 1) to@30))))))
(check-sat)
; unknown
(pop) ; 4
; 0.02s
; (get-info :all-statistics)
(push) ; 4
(pop) ; 4
; [eval] countFalse(a, from, to) == (from == to ? 0 : (loc(a, from).val ? 0 : 1) + countFalse(a, from + 1, to))
; [eval] countFalse(a, from, to)
; [eval] (0 <= from) && ((from <= to) && (to <= length(a)))
; [eval] 0 <= from
(push) ; 4
(set-option :timeout 250)
(push) ; 5
(assert (not (not (<= 0 from@29))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= 0 from@29)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 31] 0 <= from@29
(assert (<= 0 from@29))
(push) ; 6
(pop) ; 6
; [eval] (from <= to) && (to <= length(a))
; [eval] from <= to
(push) ; 6
(push) ; 7
(assert (not (not (<= from@29 to@30))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= from@29 to@30)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 32] from@29 <= to@30
(assert (<= from@29 to@30))
(push) ; 8
(pop) ; 8
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 7
; [dead else-branch 32] !from@29 <= to@30
(pop) ; 6
(pop) ; 5
; [dead else-branch 31] !0 <= from@29
(pop) ; 4
(declare-const z@53 Int)
(push) ; 4
; [eval] (from <= z) && (z < to)
; [eval] from <= z
(push) ; 5
(push) ; 6
(assert (not (not (<= from@29 z@53))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= from@29 z@53)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 33] from@29 <= z@53
(assert (<= from@29 z@53))
(push) ; 7
(pop) ; 7
; [eval] z < to
(pop) ; 6
(push) ; 6
; [else-branch 33] !from@29 <= z@53
(assert (not (<= from@29 z@53)))
(pop) ; 6
(pop) ; 5
(push) ; 5
(assert (not (not (and (<= from@29 z@53) (< z@53 to@30)))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (and (<= from@29 z@53) (< z@53 to@30)))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 5
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= from@29 $x) (< $x to@30))
      (and (<= from@29 $y) (< $y to@30))
      (= (loc<Array~Int~Ref> a@28 $x) (loc<Array~Int~Ref> a@28 $y)))
    (= $x $y))
  
  :qid |qp.inj10|))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(pop) ; 4
(declare-fun inv@54 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= from@29 (inv@54 $r)) (< (inv@54 $r) to@30))
    (= (loc<Array~Int~Ref> a@28 (inv@54 $r)) $r))
  :pattern ((inv@54 $r))
  :qid |qp.inv@54-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= from@29 $z) (< $z to@30))
    (= (inv@54 (loc<Array~Int~Ref> a@28 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@28 $z))
  :qid |qp.inv@54-exp|)))
(declare-const fvf@55 $FVF<Bool>)
(assert ($FVF.after_val fvf@55 fvf@51))
; Precomputing split data for loc[Array,Int,Ref](a@28, $z).val # W
(define-fun $pTaken6 (($r $Ref)) $Perm
  (ite
    (and (<= from@29 (inv@54 $r)) (< (inv@54 $r) to@30))
    ($Perm.min
      (ite
        (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 4
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
        $Perm.Write
        $Perm.No)
      ($pTaken6 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 4
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= from@29 (inv@54 $r)) (< (inv@54 $r) to@30))
    (= (- $Perm.Write ($pTaken6 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@55)))
    (= ($FVF.lookup_val fvf@55 $r) ($FVF.lookup_val $t@32 $r)))
  :pattern (($FVF.lookup_val fvf@55 $r) (inv@33 $r))
  :pattern (($FVF.lookup_val $t@32 $r) (inv@33 $r))
  :qid |qp.fvf@55-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@55))
    (and (<= from@29 (inv@54 $r)) (< (inv@54 $r) to@30))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@55)))
  :qid |qp.fvf@55-dom-inv@54|)))
; [eval] (from == to ? 0 : (loc(a, from).val ? 0 : 1) + countFalse(a, from + 1, to))
; [eval] from == to
(set-option :timeout 250)
(push) ; 4
(assert (not (not (= from@29 to@30))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
; [dead then-branch 34] from@29 == to@30
(push) ; 4
; [else-branch 34] from@29 != to@30
(assert (not (= from@29 to@30)))
; [eval] (loc(a, from).val ? 0 : 1) + countFalse(a, from + 1, to)
; [eval] (loc(a, from).val ? 0 : 1)
; [eval] loc(a, from)
(set-option :timeout 0)
(push) ; 5
(assert (not (not (= (loc<Array~Int~Ref> a@28 from@29) $Ref.null))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (and
  (<= from@29 (inv@33 (loc<Array~Int~Ref> a@28 from@29)))
  (< (inv@33 (loc<Array~Int~Ref> a@28 from@29)) to@30))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@56 $FVF<Bool>)
(assert ($FVF.after_val fvf@56 fvf@55))
; [dead then-branch 35] Lookup(val,fvf@34,loc[Array,Int,Ref](a@28, from@29))
(push) ; 5
; [else-branch 35] !Lookup(val,fvf@34,loc[Array,Int,Ref](a@28, from@29))
(pop) ; 5
(declare-const $deadThen@57 Int)
; [eval] countFalse(a, from + 1, to)
; [eval] from + 1
; [eval] (0 <= from + 1) && ((from + 1 <= to) && (to <= length(a)))
; [eval] 0 <= from + 1
; [eval] from + 1
(push) ; 5
(set-option :timeout 250)
(push) ; 6
(assert (not (not (<= 0 (+ from@29 1)))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= 0 (+ from@29 1))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 36] 0 <= from@29 + 1
(assert (<= 0 (+ from@29 1)))
(push) ; 7
(pop) ; 7
; [eval] (from + 1 <= to) && (to <= length(a))
; [eval] from + 1 <= to
; [eval] from + 1
(push) ; 7
(push) ; 8
(assert (not (not (<= (+ from@29 1) to@30))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
(assert (not (<= (+ from@29 1) to@30)))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 37] from@29 + 1 <= to@30
(assert (<= (+ from@29 1) to@30))
(push) ; 9
(pop) ; 9
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 8
; [dead else-branch 37] !from@29 + 1 <= to@30
(pop) ; 7
(pop) ; 6
; [dead else-branch 36] !0 <= from@29 + 1
(pop) ; 5
(set-option :timeout 0)
(push) ; 5
(assert (not (and
  (<= 0 (+ from@29 1))
  (and (<= (+ from@29 1) to@30) (<= to@30 (length<Array~Int> a@28))))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (and
  (<= 0 (+ from@29 1))
  (and (<= (+ from@29 1) to@30) (<= to@30 (length<Array~Int> a@28)))))
(declare-const z@58 Int)
(push) ; 5
; [eval] (from + 1 <= z) && (z < to)
; [eval] from + 1 <= z
; [eval] from + 1
(push) ; 6
(set-option :timeout 250)
(push) ; 7
(assert (not (not (<= (+ from@29 1) z@58))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= (+ from@29 1) z@58)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 38] from@29 + 1 <= z@58
(assert (<= (+ from@29 1) z@58))
(push) ; 8
(pop) ; 8
; [eval] z < to
(pop) ; 7
(push) ; 7
; [else-branch 38] !from@29 + 1 <= z@58
(assert (not (<= (+ from@29 1) z@58)))
(pop) ; 7
(pop) ; 6
(push) ; 6
(assert (not (not (and (<= (+ from@29 1) z@58) (< z@58 to@30)))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and (<= (+ from@29 1) z@58) (< z@58 to@30)))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= (+ from@29 1) $x) (< $x to@30))
      (and (<= (+ from@29 1) $y) (< $y to@30))
      (= (loc<Array~Int~Ref> a@28 $x) (loc<Array~Int~Ref> a@28 $y)))
    (= $x $y))
  
  :qid |qp.inj11|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(pop) ; 5
(declare-fun inv@59 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= (+ from@29 1) (inv@59 $r)) (< (inv@59 $r) to@30))
    (= (loc<Array~Int~Ref> a@28 (inv@59 $r)) $r))
  :pattern ((inv@59 $r))
  :qid |qp.inv@59-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= (+ from@29 1) $z) (< $z to@30))
    (= (inv@59 (loc<Array~Int~Ref> a@28 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@28 $z))
  :qid |qp.inv@59-exp|)))
(declare-const fvf@60 $FVF<Bool>)
(assert ($FVF.after_val fvf@60 fvf@56))
; Precomputing split data for loc[Array,Int,Ref](a@28, $z).val # W
(define-fun $pTaken7 (($r $Ref)) $Perm
  (ite
    (and (<= (+ from@29 1) (inv@59 $r)) (< (inv@59 $r) to@30))
    ($Perm.min
      (ite
        (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
        $Perm.Write
        $Perm.No)
      ($pTaken7 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= (+ from@29 1) (inv@59 $r)) (< (inv@59 $r) to@30))
    (= (- $Perm.Write ($pTaken7 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@60)))
    (= ($FVF.lookup_val fvf@60 $r) ($FVF.lookup_val $t@32 $r)))
  :pattern (($FVF.lookup_val fvf@60 $r) (inv@33 $r))
  :pattern (($FVF.lookup_val $t@32 $r) (inv@33 $r))
  :qid |qp.fvf@60-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@60))
    (and (<= (+ from@29 1) (inv@59 $r)) (< (inv@59 $r) to@30))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@60)))
  :qid |qp.fvf@60-dom-inv@59|)))
(pop) ; 4
(assert (ite
  (= from@29 to@30)
  true
  (and
    (forall (($r $Ref)) (!
      (not (xor
        ($Set.in_$Ref $r ($FVF.domain_val fvf@60))
        (and (<= (+ from@29 1) (inv@59 $r)) (< (inv@59 $r) to@30))))
      :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@60)))
      :qid |qp.fvf@60-dom-inv@59|))
    (forall (($r $Ref)) (!
      (=>
        (and
          (and (<= from@29 (inv@33 $r)) (< (inv@33 $r) to@30))
          ($Set.in_$Ref $r ($FVF.domain_val fvf@60)))
        (= ($FVF.lookup_val fvf@60 $r) ($FVF.lookup_val $t@32 $r)))
      :pattern (($FVF.lookup_val fvf@60 $r) (inv@33 $r))
      :pattern (($FVF.lookup_val $t@32 $r) (inv@33 $r))
      :qid |qp.fvf@60-lookup-1|))
    ($FVF.after_val fvf@60 fvf@56)
    (forall (($z Int)) (!
      (=>
        (and (<= (+ from@29 1) $z) (< $z to@30))
        (= (inv@59 (loc<Array~Int~Ref> a@28 $z)) $z))
      :pattern ((loc<Array~Int~Ref> a@28 $z))
      :qid |qp.inv@59-exp|))
    (forall (($r $Ref)) (!
      (=>
        (and (<= (+ from@29 1) (inv@59 $r)) (< (inv@59 $r) to@30))
        (= (loc<Array~Int~Ref> a@28 (inv@59 $r)) $r))
      :pattern ((inv@59 $r))
      :qid |qp.inv@59-imp|))
    (and
      (<= 0 (+ from@29 1))
      (and (<= (+ from@29 1) to@30) (<= to@30 (length<Array~Int> a@28))))
    ($FVF.after_val fvf@56 fvf@55)
    (not (= from@29 to@30)))))
(declare-const $deadThen@61 Int)
(set-option :timeout 0)
(push) ; 4
(assert (not (=
  ($countFalse ($Snap.combine
    $Snap.unit
    ($SortWrappers.$FVF<Bool>To$Snap fvf@55)) a@28 from@29 to@30)
  (ite
    (= from@29 to@30)
    $deadThen@61
    (+
      (ite
        ($FVF.lookup_val fvf@34 (loc<Array~Int~Ref> a@28 from@29))
        $deadThen@57
        1)
      ($countFalse ($Snap.combine
        $Snap.unit
        ($SortWrappers.$FVF<Bool>To$Snap fvf@60)) a@28 (+ from@29 1) to@30))))))
(check-sat)
; unknown
(pop) ; 4
; 0.02s
; (get-info :all-statistics)
(pop) ; 3
(pop) ; 2
; ---------- two_way_sort ----------
(declare-const a@62 $Array)
(declare-const i@63 Int)
(declare-const j@64 Int)
(push) ; 2
(declare-const z@65 Int)
(push) ; 3
; [eval] (0 <= z) && (z < length(a))
; [eval] 0 <= z
(push) ; 4
(set-option :timeout 250)
(push) ; 5
(assert (not (not (<= 0 z@65))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (<= 0 z@65)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 39] 0 <= z@65
(assert (<= 0 z@65))
; [eval] z < length(a)
; [eval] length(a)
(pop) ; 5
(push) ; 5
; [else-branch 39] !0 <= z@65
(assert (not (<= 0 z@65)))
(pop) ; 5
(pop) ; 4
(assert (and (<= 0 z@65) (< z@65 (length<Array~Int> a@62))))
; [eval] loc(a, z)
(pop) ; 3
(declare-const $t@66 $FVF<Bool>)
(assert ($FVF.after_val $t@66 fvf@17))
(declare-fun inv@67 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= 0 (inv@67 $r)) (< (inv@67 $r) (length<Array~Int> a@62)))
    (= (loc<Array~Int~Ref> a@62 (inv@67 $r)) $r))
  :pattern ((inv@67 $r))
  :qid |qp.inv@67-imp|)))
(assert (forall ((z@65 Int)) (!
  (=>
    (and (<= 0 z@65) (< z@65 (length<Array~Int> a@62)))
    (= (inv@67 (loc<Array~Int~Ref> a@62 z@65)) z@65))
  :pattern ((loc<Array~Int~Ref> a@62 z@65))
  :qid |qp.inv@67-exp|)))
(assert (forall ((z@65 Int)) (!
  (=>
    (and (<= 0 z@65) (< z@65 (length<Array~Int> a@62)))
    (not (= (loc<Array~Int~Ref> a@62 z@65) $Ref.null)))
  :pattern ((loc<Array~Int~Ref> a@62 z@65))
  :qid |qp.null12|)))
(push) ; 3
(declare-const z@68 Int)
(push) ; 4
; [eval] (0 <= z) && (z < length(a))
; [eval] 0 <= z
(push) ; 5
(push) ; 6
(assert (not (not (<= 0 z@68))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= 0 z@68)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 40] 0 <= z@68
(assert (<= 0 z@68))
; [eval] z < length(a)
; [eval] length(a)
(pop) ; 6
(push) ; 6
; [else-branch 40] !0 <= z@68
(assert (not (<= 0 z@68)))
(pop) ; 6
(pop) ; 5
(assert (and (<= 0 z@68) (< z@68 (length<Array~Int> a@62))))
; [eval] loc(a, z)
(pop) ; 4
(declare-const $t@69 $FVF<Bool>)
(assert ($FVF.after_val $t@69 $t@66))
(declare-fun inv@70 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= 0 (inv@70 $r)) (< (inv@70 $r) (length<Array~Int> a@62)))
    (= (loc<Array~Int~Ref> a@62 (inv@70 $r)) $r))
  :pattern ((inv@70 $r))
  :qid |qp.inv@70-imp|)))
(assert (forall ((z@68 Int)) (!
  (=>
    (and (<= 0 z@68) (< z@68 (length<Array~Int> a@62)))
    (= (inv@70 (loc<Array~Int~Ref> a@62 z@68)) z@68))
  :pattern ((loc<Array~Int~Ref> a@62 z@68))
  :qid |qp.inv@70-exp|)))
(assert (forall ((z@68 Int)) (!
  (=>
    (and (<= 0 z@68) (< z@68 (length<Array~Int> a@62)))
    (not (= (loc<Array~Int~Ref> a@62 z@68) $Ref.null)))
  :pattern ((loc<Array~Int~Ref> a@62 z@68))
  :qid |qp.null13|)))
; [eval] (forall y: Int :: (0 <= y) && (y < length(a)) ==> (forall z: Int :: (y < z) && (z < length(a)) ==> lte(loc(a, y).val, loc(a, z).val)))
(declare-const y@71 Int)
(push) ; 4
; [eval] (0 <= y) && (y < length(a)) ==> (forall z: Int :: (y < z) && (z < length(a)) ==> lte(loc(a, y).val, loc(a, z).val))
; [eval] (0 <= y) && (y < length(a))
; [eval] 0 <= y
(push) ; 5
(push) ; 6
(assert (not (not (<= 0 y@71))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= 0 y@71)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 41] 0 <= y@71
(assert (<= 0 y@71))
; [eval] y < length(a)
; [eval] length(a)
(pop) ; 6
(push) ; 6
; [else-branch 41] !0 <= y@71
(assert (not (<= 0 y@71)))
(pop) ; 6
(pop) ; 5
(push) ; 5
(push) ; 6
(assert (not (not (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62))))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62)))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 42] 0 <= y@71 && y@71 < length[Array,Int](a@62)
(assert (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62))))
; [eval] (forall z: Int :: (y < z) && (z < length(a)) ==> lte(loc(a, y).val, loc(a, z).val))
(declare-const z@72 Int)
(push) ; 7
; [eval] (y < z) && (z < length(a)) ==> lte(loc(a, y).val, loc(a, z).val)
; [eval] (y < z) && (z < length(a))
; [eval] y < z
(push) ; 8
(push) ; 9
(assert (not (not (< y@71 z@72))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (< y@71 z@72)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 43] y@71 < z@72
(assert (< y@71 z@72))
; [eval] z < length(a)
; [eval] length(a)
(pop) ; 9
(push) ; 9
; [else-branch 43] !y@71 < z@72
(assert (not (< y@71 z@72)))
(pop) ; 9
(pop) ; 8
(push) ; 8
(push) ; 9
(assert (not (not (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62))))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 44] y@71 < z@72 && z@72 < length[Array,Int](a@62)
(assert (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62))))
; [eval] lte(loc(a, y).val, loc(a, z).val)
; [eval] loc(a, y)
(set-option :timeout 0)
(push) ; 10
(assert (not (not (= (loc<Array~Int~Ref> a@62 y@71) $Ref.null))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
(assert (not (and
  (<= 0 (inv@70 (loc<Array~Int~Ref> a@62 y@71)))
  (< (inv@70 (loc<Array~Int~Ref> a@62 y@71)) (length<Array~Int> a@62)))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@73 $FVF<Bool>)
(assert ($FVF.after_val fvf@73 $t@69))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@70 $r)) (< (inv@70 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@73)))
    (= ($FVF.lookup_val fvf@73 $r) ($FVF.lookup_val $t@69 $r)))
  :pattern (($FVF.lookup_val fvf@73 $r) (inv@70 $r))
  :pattern (($FVF.lookup_val $t@69 $r) (inv@70 $r))
  :qid |qp.fvf@73-lookup-1|)))
(assert (forall ((y@71 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 y@71) ($FVF.domain_val fvf@73))
    (and
      (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))
      (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62))))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 y@71)
    ($FVF.domain_val fvf@73)))
  :qid |qp.fvf@73-dom|)))
; [eval] loc(a, z)
(push) ; 10
(assert (not (not (= (loc<Array~Int~Ref> a@62 z@72) $Ref.null))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
(assert (not (and
  (<= 0 (inv@70 (loc<Array~Int~Ref> a@62 z@72)))
  (< (inv@70 (loc<Array~Int~Ref> a@62 z@72)) (length<Array~Int> a@62)))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@74 $FVF<Bool>)
(assert ($FVF.after_val fvf@74 fvf@73))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@70 $r)) (< (inv@70 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@74)))
    (= ($FVF.lookup_val fvf@74 $r) ($FVF.lookup_val $t@69 $r)))
  :pattern (($FVF.lookup_val fvf@74 $r) (inv@70 $r))
  :pattern (($FVF.lookup_val $t@69 $r) (inv@70 $r))
  :qid |qp.fvf@74-lookup-1|)))
(assert (forall ((z@72 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@72) ($FVF.domain_val fvf@74))
    (and
      (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))
      (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62))))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@72)
    ($FVF.domain_val fvf@74)))
  :qid |qp.fvf@74-dom|)))
(pop) ; 9
(push) ; 9
; [else-branch 44] !y@71 < z@72 && z@72 < length[Array,Int](a@62)
(assert (not (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))))
(pop) ; 9
(pop) ; 8
(assert (forall ((z@72 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@72) ($FVF.domain_val fvf@74))
    (and
      (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))
      (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62))))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@72)
    ($FVF.domain_val fvf@74)))
  :qid |qp.fvf@74-dom|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@70 $r)) (< (inv@70 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@74)))
    (= ($FVF.lookup_val fvf@74 $r) ($FVF.lookup_val $t@69 $r)))
  :pattern (($FVF.lookup_val fvf@74 $r) (inv@70 $r))
  :pattern (($FVF.lookup_val $t@69 $r) (inv@70 $r))
  :qid |qp.fvf@74-lookup-1|)))
(assert ($FVF.after_val fvf@74 fvf@73))
(assert (forall ((y@71 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 y@71) ($FVF.domain_val fvf@73))
    (and
      (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))
      (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62))))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 y@71)
    ($FVF.domain_val fvf@73)))
  :qid |qp.fvf@73-dom|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@70 $r)) (< (inv@70 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@73)))
    (= ($FVF.lookup_val fvf@73 $r) ($FVF.lookup_val $t@69 $r)))
  :pattern (($FVF.lookup_val fvf@73 $r) (inv@70 $r))
  :pattern (($FVF.lookup_val $t@69 $r) (inv@70 $r))
  :qid |qp.fvf@73-lookup-1|)))
(assert ($FVF.after_val fvf@73 $t@69))
(pop) ; 7
(assert (forall ((z@72 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@72) ($FVF.domain_val fvf@74))
    (and
      (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))
      (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62))))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@72)
    ($FVF.domain_val fvf@74)))
  :qid |qp.fvf@74-dom|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@70 $r)) (< (inv@70 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@74)))
    (= ($FVF.lookup_val fvf@74 $r) ($FVF.lookup_val $t@69 $r)))
  :pattern (($FVF.lookup_val fvf@74 $r) (inv@70 $r))
  :pattern (($FVF.lookup_val $t@69 $r) (inv@70 $r))
  :qid |qp.fvf@74-lookup-1|)))
(assert ($FVF.after_val fvf@74 fvf@73))
(assert (forall ((z@72 Int)) (!
  (forall ((y@71 Int)) (!
    (not (xor
      ($Set.in_$Ref (loc<Array~Int~Ref> a@62 y@71) ($FVF.domain_val fvf@73))
      (and
        (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))
        (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62))))))
    :pattern (($Set.in_$Ref
      (loc<Array~Int~Ref> a@62 y@71)
      ($FVF.domain_val fvf@73)))
    :qid |qp.fvf@73-dom|))
  
  )))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@70 $r)) (< (inv@70 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@73)))
    (= ($FVF.lookup_val fvf@73 $r) ($FVF.lookup_val $t@69 $r)))
  :pattern (($FVF.lookup_val fvf@73 $r) (inv@70 $r))
  :pattern (($FVF.lookup_val $t@69 $r) (inv@70 $r))
  :qid |qp.fvf@73-lookup-1|)))
(assert ($FVF.after_val fvf@73 $t@69))
(pop) ; 6
(push) ; 6
; [else-branch 42] !0 <= y@71 && y@71 < length[Array,Int](a@62)
(assert (not (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62)))))
(pop) ; 6
(pop) ; 5
(assert ($FVF.after_val fvf@73 $t@69))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@70 $r)) (< (inv@70 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@73)))
    (= ($FVF.lookup_val fvf@73 $r) ($FVF.lookup_val $t@69 $r)))
  :pattern (($FVF.lookup_val fvf@73 $r) (inv@70 $r))
  :pattern (($FVF.lookup_val $t@69 $r) (inv@70 $r))
  :qid |qp.fvf@73-lookup-1|)))
(assert (forall ((z@72 Int)) (!
  (forall ((y@71 Int)) (!
    (not (xor
      ($Set.in_$Ref (loc<Array~Int~Ref> a@62 y@71) ($FVF.domain_val fvf@73))
      (and
        (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))
        (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62))))))
    :pattern (($Set.in_$Ref
      (loc<Array~Int~Ref> a@62 y@71)
      ($FVF.domain_val fvf@73)))
    :qid |qp.fvf@73-dom|))
  
  )))
(assert ($FVF.after_val fvf@74 fvf@73))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@70 $r)) (< (inv@70 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@74)))
    (= ($FVF.lookup_val fvf@74 $r) ($FVF.lookup_val $t@69 $r)))
  :pattern (($FVF.lookup_val fvf@74 $r) (inv@70 $r))
  :pattern (($FVF.lookup_val $t@69 $r) (inv@70 $r))
  :qid |qp.fvf@74-lookup-1|)))
(assert (forall ((z@72 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@72) ($FVF.domain_val fvf@74))
    (and
      (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))
      (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62))))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@72)
    ($FVF.domain_val fvf@74)))
  :qid |qp.fvf@74-dom|)))
(pop) ; 4
(assert ($FVF.after_val fvf@73 $t@69))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@70 $r)) (< (inv@70 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@73)))
    (= ($FVF.lookup_val fvf@73 $r) ($FVF.lookup_val $t@69 $r)))
  :pattern (($FVF.lookup_val fvf@73 $r) (inv@70 $r))
  :pattern (($FVF.lookup_val $t@69 $r) (inv@70 $r))
  :qid |qp.fvf@73-lookup-1|)))
(assert (forall ((y@71 Int)) (!
  (forall ((z@72 Int)) (!
    (forall ((y@71 Int)) (!
      (not (xor
        ($Set.in_$Ref (loc<Array~Int~Ref> a@62 y@71) ($FVF.domain_val fvf@73))
        (and
          (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))
          (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62))))))
      :pattern (($Set.in_$Ref
        (loc<Array~Int~Ref> a@62 y@71)
        ($FVF.domain_val fvf@73)))
      :qid |qp.fvf@73-dom|))
    
    ))
  
  )))
(assert ($FVF.after_val fvf@74 fvf@73))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@70 $r)) (< (inv@70 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@74)))
    (= ($FVF.lookup_val fvf@74 $r) ($FVF.lookup_val $t@69 $r)))
  :pattern (($FVF.lookup_val fvf@74 $r) (inv@70 $r))
  :pattern (($FVF.lookup_val $t@69 $r) (inv@70 $r))
  :qid |qp.fvf@74-lookup-1|)))
(assert (forall ((y@71 Int)) (!
  (forall ((z@72 Int)) (!
    (not (xor
      ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@72) ($FVF.domain_val fvf@74))
      (and
        (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))
        (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62))))))
    :pattern (($Set.in_$Ref
      (loc<Array~Int~Ref> a@62 z@72)
      ($FVF.domain_val fvf@74)))
    :qid |qp.fvf@74-dom|))
  
  )))
(assert (forall ((y@71 Int)) (!
  (=>
    (and (<= 0 y@71) (< y@71 (length<Array~Int> a@62)))
    (forall ((z@72 Int)) (!
      (=>
        (and (< y@71 z@72) (< z@72 (length<Array~Int> a@62)))
        ($lte $Snap.unit ($FVF.lookup_val fvf@73 (loc<Array~Int~Ref> a@62 y@71)) ($FVF.lookup_val fvf@74 (loc<Array~Int~Ref> a@62 z@72))))
      :pattern (($lte$ $Snap.unit ($FVF.lookup_val fvf@73 (loc<Array~Int~Ref> a@62 y@71)) ($FVF.lookup_val fvf@74 (loc<Array~Int~Ref> a@62 z@72))))
      :qid |prog.l39|)))
  :pattern ((loc<Array~Int~Ref> a@62 y@71))
  :qid |prog.l38|)))
(pop) ; 3
(push) ; 3
; [exec]
; i := 0
; [exec]
; j := length(a) - 1
; [eval] length(a) - 1
; [eval] length(a)
; loop at Two-Way-Sort-Slow-Inverse.sil,46:3
(declare-const measure@75 Int)
(declare-const i@76 Int)
(declare-const j@77 Int)
(push) ; 4
; Verify loop body
(declare-const $t@78 $Snap)
(declare-const $t@79 $Snap)
(assert (= $t@78 ($Snap.combine $t@79 $Snap.unit)))
(declare-const $t@80 $Snap)
(assert (= $t@79 ($Snap.combine $t@80 $Snap.unit)))
(declare-const $t@81 $Snap)
(assert (= $t@80 ($Snap.combine $t@81 $Snap.unit)))
(declare-const $t@82 $Snap)
(assert (= $t@81 ($Snap.combine $t@82 $Snap.unit)))
(declare-const $t@83 $FVF<Bool>)
(assert ($FVF.after_val $t@83 fvf@74))
(assert (= $t@82 ($Snap.combine $Snap.unit ($SortWrappers.$FVF<Bool>To$Snap $t@83))))
; [eval] (0 <= i) && ((i <= j + 1) && (j < length(a)))
; [eval] 0 <= i
(push) ; 5
(set-option :timeout 250)
(push) ; 6
(assert (not (not (<= 0 i@76))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= 0 i@76)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 45] 0 <= i@76
(assert (<= 0 i@76))
; [eval] (i <= j + 1) && (j < length(a))
; [eval] i <= j + 1
; [eval] j + 1
(push) ; 7
(push) ; 8
(assert (not (not (<= i@76 (+ j@77 1)))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
(assert (not (<= i@76 (+ j@77 1))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 46] i@76 <= j@77 + 1
(assert (<= i@76 (+ j@77 1)))
; [eval] j < length(a)
; [eval] length(a)
(pop) ; 8
(push) ; 8
; [else-branch 46] !i@76 <= j@77 + 1
(assert (not (<= i@76 (+ j@77 1))))
(pop) ; 8
(pop) ; 7
(pop) ; 6
(push) ; 6
; [else-branch 45] !0 <= i@76
(assert (not (<= 0 i@76)))
(pop) ; 6
(pop) ; 5
(assert (and (<= 0 i@76) (and (<= i@76 (+ j@77 1)) (< j@77 (length<Array~Int> a@62)))))
(declare-const z@84 Int)
(push) ; 5
; [eval] (0 <= z) && (z < length(a))
; [eval] 0 <= z
(push) ; 6
(push) ; 7
(assert (not (not (<= 0 z@84))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= 0 z@84)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 47] 0 <= z@84
(assert (<= 0 z@84))
; [eval] z < length(a)
; [eval] length(a)
(pop) ; 7
(push) ; 7
; [else-branch 47] !0 <= z@84
(assert (not (<= 0 z@84)))
(pop) ; 7
(pop) ; 6
(assert (and (<= 0 z@84) (< z@84 (length<Array~Int> a@62))))
; [eval] loc(a, z)
(pop) ; 5
(declare-fun inv@85 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
    (= (loc<Array~Int~Ref> a@62 (inv@85 $r)) $r))
  :pattern ((inv@85 $r))
  :qid |qp.inv@85-imp|)))
(assert (forall ((z@84 Int)) (!
  (=>
    (and (<= 0 z@84) (< z@84 (length<Array~Int> a@62)))
    (= (inv@85 (loc<Array~Int~Ref> a@62 z@84)) z@84))
  :pattern ((loc<Array~Int~Ref> a@62 z@84))
  :qid |qp.inv@85-exp|)))
(assert (forall ((z@84 Int)) (!
  (=>
    (and (<= 0 z@84) (< z@84 (length<Array~Int> a@62)))
    (not (= (loc<Array~Int~Ref> a@62 z@84) $Ref.null)))
  :pattern ((loc<Array~Int~Ref> a@62 z@84))
  :qid |qp.null14|)))
; [eval] (forall z: Int :: (0 <= z) && (z < i) ==> !loc(a, z).val)
(declare-const z@86 Int)
(push) ; 5
; [eval] (0 <= z) && (z < i) ==> !loc(a, z).val
; [eval] (0 <= z) && (z < i)
; [eval] 0 <= z
(push) ; 6
(push) ; 7
(assert (not (not (<= 0 z@86))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= 0 z@86)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 48] 0 <= z@86
(assert (<= 0 z@86))
; [eval] z < i
(pop) ; 7
(push) ; 7
; [else-branch 48] !0 <= z@86
(assert (not (<= 0 z@86)))
(pop) ; 7
(pop) ; 6
(push) ; 6
(push) ; 7
(assert (not (not (and (<= 0 z@86) (< z@86 i@76)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (and (<= 0 z@86) (< z@86 i@76))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 49] 0 <= z@86 && z@86 < i@76
(assert (and (<= 0 z@86) (< z@86 i@76)))
; [eval] !loc(a, z).val
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 8
(assert (not (not (= (loc<Array~Int~Ref> a@62 z@86) $Ref.null))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
(assert (not (and
  (<= 0 (inv@85 (loc<Array~Int~Ref> a@62 z@86)))
  (< (inv@85 (loc<Array~Int~Ref> a@62 z@86)) (length<Array~Int> a@62)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@87 $FVF<Bool>)
(assert ($FVF.after_val fvf@87 $t@83))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@87)))
    (= ($FVF.lookup_val fvf@87 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@87 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@87-lookup-1|)))
(assert (forall ((z@86 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@86) ($FVF.domain_val fvf@87))
    (and (<= 0 z@86) (< z@86 i@76))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@86)
    ($FVF.domain_val fvf@87)))
  :qid |qp.fvf@87-dom|)))
(pop) ; 7
(push) ; 7
; [else-branch 49] !0 <= z@86 && z@86 < i@76
(assert (not (and (<= 0 z@86) (< z@86 i@76))))
(pop) ; 7
(pop) ; 6
(assert (forall ((z@86 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@86) ($FVF.domain_val fvf@87))
    (and (<= 0 z@86) (< z@86 i@76))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@86)
    ($FVF.domain_val fvf@87)))
  :qid |qp.fvf@87-dom|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@87)))
    (= ($FVF.lookup_val fvf@87 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@87 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@87-lookup-1|)))
(assert ($FVF.after_val fvf@87 $t@83))
(pop) ; 5
(assert (forall ((z@86 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@86) ($FVF.domain_val fvf@87))
    (and (<= 0 z@86) (< z@86 i@76))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@86)
    ($FVF.domain_val fvf@87)))
  :qid |qp.fvf@87-dom|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@87)))
    (= ($FVF.lookup_val fvf@87 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@87 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@87-lookup-1|)))
(assert ($FVF.after_val fvf@87 $t@83))
(assert (forall ((z@86 Int)) (!
  (=>
    (and (<= 0 z@86) (< z@86 i@76))
    (not ($FVF.lookup_val fvf@87 (loc<Array~Int~Ref> a@62 z@86))))
  :pattern ((loc<Array~Int~Ref> a@62 z@86))
  :qid |prog.l49|)))
; [eval] (forall z: Int :: (j < z) && (z < length(a)) ==> loc(a, z).val)
(declare-const z@88 Int)
(push) ; 5
; [eval] (j < z) && (z < length(a)) ==> loc(a, z).val
; [eval] (j < z) && (z < length(a))
; [eval] j < z
(push) ; 6
(set-option :timeout 250)
(push) ; 7
(assert (not (not (< j@77 z@88))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (< j@77 z@88)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 50] j@77 < z@88
(assert (< j@77 z@88))
; [eval] z < length(a)
; [eval] length(a)
(pop) ; 7
(push) ; 7
; [else-branch 50] !j@77 < z@88
(assert (not (< j@77 z@88)))
(pop) ; 7
(pop) ; 6
(push) ; 6
(push) ; 7
(assert (not (not (and (< j@77 z@88) (< z@88 (length<Array~Int> a@62))))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (and (< j@77 z@88) (< z@88 (length<Array~Int> a@62)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 51] j@77 < z@88 && z@88 < length[Array,Int](a@62)
(assert (and (< j@77 z@88) (< z@88 (length<Array~Int> a@62))))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 8
(assert (not (not (= (loc<Array~Int~Ref> a@62 z@88) $Ref.null))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
(assert (not (and
  (<= 0 (inv@85 (loc<Array~Int~Ref> a@62 z@88)))
  (< (inv@85 (loc<Array~Int~Ref> a@62 z@88)) (length<Array~Int> a@62)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@89 $FVF<Bool>)
(assert ($FVF.after_val fvf@89 fvf@87))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@89)))
    (= ($FVF.lookup_val fvf@89 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@89 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@89-lookup-1|)))
(assert (forall ((z@88 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@88) ($FVF.domain_val fvf@89))
    (and (< j@77 z@88) (< z@88 (length<Array~Int> a@62)))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@88)
    ($FVF.domain_val fvf@89)))
  :qid |qp.fvf@89-dom|)))
(pop) ; 7
(push) ; 7
; [else-branch 51] !j@77 < z@88 && z@88 < length[Array,Int](a@62)
(assert (not (and (< j@77 z@88) (< z@88 (length<Array~Int> a@62)))))
(pop) ; 7
(pop) ; 6
(assert (forall ((z@88 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@88) ($FVF.domain_val fvf@89))
    (and (< j@77 z@88) (< z@88 (length<Array~Int> a@62)))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@88)
    ($FVF.domain_val fvf@89)))
  :qid |qp.fvf@89-dom|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@89)))
    (= ($FVF.lookup_val fvf@89 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@89 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@89-lookup-1|)))
(assert ($FVF.after_val fvf@89 fvf@87))
(pop) ; 5
(assert (forall ((z@88 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@88) ($FVF.domain_val fvf@89))
    (and (< j@77 z@88) (< z@88 (length<Array~Int> a@62)))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@88)
    ($FVF.domain_val fvf@89)))
  :qid |qp.fvf@89-dom|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@89)))
    (= ($FVF.lookup_val fvf@89 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@89 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@89-lookup-1|)))
(assert ($FVF.after_val fvf@89 fvf@87))
(assert (forall ((z@88 Int)) (!
  (=>
    (and (< j@77 z@88) (< z@88 (length<Array~Int> a@62)))
    ($FVF.lookup_val fvf@89 (loc<Array~Int~Ref> a@62 z@88)))
  :pattern ((loc<Array~Int~Ref> a@62 z@88))
  :qid |prog.l50|)))
; [eval] countFalse(a, 0, length(a)) == i + countFalse(a, i, j + 1)
; [eval] countFalse(a, 0, length(a))
; [eval] length(a)
; [eval] (0 <= 0) && ((0 <= length(a)) && (length(a) <= length(a)))
; [eval] 0 <= 0
(push) ; 5
(set-option :timeout 250)
(push) ; 6
(assert (not false))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 52] True
; [eval] (0 <= length(a)) && (length(a) <= length(a))
; [eval] 0 <= length(a)
; [eval] length(a)
(push) ; 7
(push) ; 8
(assert (not (not (<= 0 (length<Array~Int> a@62)))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
(assert (not (<= 0 (length<Array~Int> a@62))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 53] 0 <= length[Array,Int](a@62)
(assert (<= 0 (length<Array~Int> a@62)))
; [eval] length(a) <= length(a)
; [eval] length(a)
; [eval] length(a)
(pop) ; 8
; [dead else-branch 53] !0 <= length[Array,Int](a@62)
(pop) ; 7
(pop) ; 6
; [dead else-branch 52] False
(pop) ; 5
(set-option :timeout 0)
(push) ; 5
(assert (not (<= 0 (length<Array~Int> a@62))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (<= 0 (length<Array~Int> a@62)))
(declare-const z@90 Int)
(push) ; 5
; [eval] (0 <= z) && (z < length(a))
; [eval] 0 <= z
(push) ; 6
(set-option :timeout 250)
(push) ; 7
(assert (not (not (<= 0 z@90))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= 0 z@90)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 54] 0 <= z@90
(assert (<= 0 z@90))
; [eval] z < length(a)
; [eval] length(a)
(pop) ; 7
(push) ; 7
; [else-branch 54] !0 <= z@90
(assert (not (<= 0 z@90)))
(pop) ; 7
(pop) ; 6
(push) ; 6
(assert (not (not (and (<= 0 z@90) (< z@90 (length<Array~Int> a@62))))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 z@90) (< z@90 (length<Array~Int> a@62))))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= 0 $x) (< $x (length<Array~Int> a@62)))
      (and (<= 0 $y) (< $y (length<Array~Int> a@62)))
      (= (loc<Array~Int~Ref> a@62 $x) (loc<Array~Int~Ref> a@62 $y)))
    (= $x $y))
  
  :qid |qp.inj15|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(pop) ; 5
(declare-fun inv@91 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= 0 (inv@91 $r)) (< (inv@91 $r) (length<Array~Int> a@62)))
    (= (loc<Array~Int~Ref> a@62 (inv@91 $r)) $r))
  :pattern ((inv@91 $r))
  :qid |qp.inv@91-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= 0 $z) (< $z (length<Array~Int> a@62)))
    (= (inv@91 (loc<Array~Int~Ref> a@62 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@62 $z))
  :qid |qp.inv@91-exp|)))
(declare-const fvf@92 $FVF<Bool>)
(assert ($FVF.after_val fvf@92 fvf@89))
; Precomputing split data for loc[Array,Int,Ref](a@62, $z).val # W
(define-fun $pTaken8 (($r $Ref)) $Perm
  (ite
    (and (<= 0 (inv@91 $r)) (< (inv@91 $r) (length<Array~Int> a@62)))
    ($Perm.min
      (ite
        (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
        $Perm.Write
        $Perm.No)
      ($pTaken8 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= 0 (inv@91 $r)) (< (inv@91 $r) (length<Array~Int> a@62)))
    (= (- $Perm.Write ($pTaken8 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@92)))
    (= ($FVF.lookup_val fvf@92 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@92 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@92-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@92))
    (and (<= 0 (inv@91 $r)) (< (inv@91 $r) (length<Array~Int> a@62)))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@92)))
  :qid |qp.fvf@92-dom-inv@91|)))
; [eval] i + countFalse(a, i, j + 1)
; [eval] countFalse(a, i, j + 1)
; [eval] j + 1
; [eval] (0 <= i) && ((i <= j + 1) && (j + 1 <= length(a)))
; [eval] 0 <= i
(push) ; 5
(set-option :timeout 250)
(push) ; 6
(assert (not (not (<= 0 i@76))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (<= 0 i@76)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 55] 0 <= i@76
(assert (<= 0 i@76))
; [eval] (i <= j + 1) && (j + 1 <= length(a))
; [eval] i <= j + 1
; [eval] j + 1
(push) ; 7
(push) ; 8
(assert (not (not (<= i@76 (+ j@77 1)))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
(assert (not (<= i@76 (+ j@77 1))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 56] i@76 <= j@77 + 1
(assert (<= i@76 (+ j@77 1)))
; [eval] j + 1 <= length(a)
; [eval] j + 1
; [eval] length(a)
(pop) ; 8
; [dead else-branch 56] !i@76 <= j@77 + 1
(pop) ; 7
(pop) ; 6
; [dead else-branch 55] !0 <= i@76
(pop) ; 5
(set-option :timeout 0)
(push) ; 5
(assert (not (and
  (<= 0 i@76)
  (and (<= i@76 (+ j@77 1)) (<= (+ j@77 1) (length<Array~Int> a@62))))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (and
  (<= 0 i@76)
  (and (<= i@76 (+ j@77 1)) (<= (+ j@77 1) (length<Array~Int> a@62)))))
(declare-const z@93 Int)
(push) ; 5
; [eval] (i <= z) && (z < j + 1)
; [eval] i <= z
(push) ; 6
(set-option :timeout 250)
(push) ; 7
(assert (not (not (<= i@76 z@93))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= i@76 z@93)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 57] i@76 <= z@93
(assert (<= i@76 z@93))
; [eval] z < j + 1
; [eval] j + 1
(pop) ; 7
(push) ; 7
; [else-branch 57] !i@76 <= z@93
(assert (not (<= i@76 z@93)))
(pop) ; 7
(pop) ; 6
(push) ; 6
(assert (not (not (and (<= i@76 z@93) (< z@93 (+ j@77 1))))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and (<= i@76 z@93) (< z@93 (+ j@77 1))))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= i@76 $x) (< $x (+ j@77 1)))
      (and (<= i@76 $y) (< $y (+ j@77 1)))
      (= (loc<Array~Int~Ref> a@62 $x) (loc<Array~Int~Ref> a@62 $y)))
    (= $x $y))
  
  :qid |qp.inj16|))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(pop) ; 5
(declare-fun inv@94 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= i@76 (inv@94 $r)) (< (inv@94 $r) (+ j@77 1)))
    (= (loc<Array~Int~Ref> a@62 (inv@94 $r)) $r))
  :pattern ((inv@94 $r))
  :qid |qp.inv@94-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= i@76 $z) (< $z (+ j@77 1)))
    (= (inv@94 (loc<Array~Int~Ref> a@62 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@62 $z))
  :qid |qp.inv@94-exp|)))
(declare-const fvf@95 $FVF<Bool>)
(assert ($FVF.after_val fvf@95 fvf@92))
; Precomputing split data for loc[Array,Int,Ref](a@62, $z).val # W
(define-fun $pTaken9 (($r $Ref)) $Perm
  (ite
    (and (<= i@76 (inv@94 $r)) (< (inv@94 $r) (+ j@77 1)))
    ($Perm.min
      (ite
        (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
        $Perm.Write
        $Perm.No)
      ($pTaken9 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= i@76 (inv@94 $r)) (< (inv@94 $r) (+ j@77 1)))
    (= (- $Perm.Write ($pTaken9 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@95)))
    (= ($FVF.lookup_val fvf@95 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@95 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@95-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@95))
    (and (<= i@76 (inv@94 $r)) (< (inv@94 $r) (+ j@77 1)))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@95)))
  :qid |qp.fvf@95-dom-inv@94|)))
(assert (=
  ($countFalse ($Snap.combine
    $Snap.unit
    ($SortWrappers.$FVF<Bool>To$Snap fvf@92)) a@62 0 (length<Array~Int> a@62))
  (+
    i@76
    ($countFalse ($Snap.combine
      $Snap.unit
      ($SortWrappers.$FVF<Bool>To$Snap fvf@95)) a@62 i@76 (+ j@77 1)))))
; [eval] i <= j
(assert (<= i@76 j@77))
(set-option :timeout 250)
(check-sat)
; unknown
; [exec]
; measure := j - i
; [eval] j - i
; [exec]
; assert 0 <= measure
; [eval] 0 <= measure
(set-option :timeout 0)
(push) ; 5
(assert (not (<= 0 (- j@77 i@76))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (<= 0 (- j@77 i@76)))
; [eval] !loc(a, i).val
; [eval] loc(a, i)
(push) ; 5
(assert (not (not (= (loc<Array~Int~Ref> a@62 i@76) $Ref.null))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
(assert (not (and
  (<= 0 (inv@85 (loc<Array~Int~Ref> a@62 i@76)))
  (< (inv@85 (loc<Array~Int~Ref> a@62 i@76)) (length<Array~Int> a@62)))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@96 $FVF<Bool>)
(assert ($FVF.after_val fvf@96 fvf@95))
(assert (=>
  (and
    (<= 0 (inv@85 (loc<Array~Int~Ref> a@62 i@76)))
    (< (inv@85 (loc<Array~Int~Ref> a@62 i@76)) (length<Array~Int> a@62)))
  (=
    ($FVF.lookup_val fvf@96 (loc<Array~Int~Ref> a@62 i@76))
    ($FVF.lookup_val $t@83 (loc<Array~Int~Ref> a@62 i@76)))))
(assert (= ($FVF.domain_val fvf@96) ($Set.singleton_$Ref (loc<Array~Int~Ref> a@62 i@76))))
(set-option :timeout 250)
(push) ; 5
(assert (not ($FVF.lookup_val fvf@96 (loc<Array~Int~Ref> a@62 i@76))))
(check-sat)
; unknown
(pop) ; 5
; 0.02s
; (get-info :all-statistics)
(push) ; 5
(assert (not (not ($FVF.lookup_val fvf@96 (loc<Array~Int~Ref> a@62 i@76)))))
(check-sat)
; unknown
(pop) ; 5
; 0.01s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 58] !Lookup(val,fvf@96,loc[Array,Int,Ref](a@62, i@76))
(assert (not ($FVF.lookup_val fvf@96 (loc<Array~Int~Ref> a@62 i@76))))
; [exec]
; lemmaFront(a, i, j + 1)
; [eval] j + 1
; [eval] (0 <= from) && ((from < to) && (to <= length(a)))
; [eval] 0 <= from
(push) ; 6
(push) ; 7
(assert (not (not (<= 0 i@76))))
(check-sat)
; unknown
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= 0 i@76)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 59] 0 <= i@76
(assert (<= 0 i@76))
; [eval] (from < to) && (to <= length(a))
; [eval] from < to
(push) ; 8
(push) ; 9
(assert (not (not (< i@76 (+ j@77 1)))))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(push) ; 9
(assert (not (< i@76 (+ j@77 1))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 60] i@76 < j@77 + 1
(assert (< i@76 (+ j@77 1)))
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 9
; [dead else-branch 60] !i@76 < j@77 + 1
(pop) ; 8
(pop) ; 7
; [dead else-branch 59] !0 <= i@76
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
(assert (not (and
  (<= 0 i@76)
  (and (< i@76 (+ j@77 1)) (<= (+ j@77 1) (length<Array~Int> a@62))))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and
  (<= 0 i@76)
  (and (< i@76 (+ j@77 1)) (<= (+ j@77 1) (length<Array~Int> a@62)))))
(declare-const z@97 Int)
(push) ; 6
; [eval] (from <= z) && (z < to)
; [eval] from <= z
(push) ; 7
(set-option :timeout 250)
(push) ; 8
(assert (not (not (<= i@76 z@97))))
(check-sat)
; unknown
(pop) ; 8
; 0.01s
; (get-info :all-statistics)
(push) ; 8
(assert (not (<= i@76 z@97)))
(check-sat)
; unknown
(pop) ; 8
; 0.01s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 61] i@76 <= z@97
(assert (<= i@76 z@97))
; [eval] z < to
(pop) ; 8
(push) ; 8
; [else-branch 61] !i@76 <= z@97
(assert (not (<= i@76 z@97)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(assert (not (not (and (<= i@76 z@97) (< z@97 (+ j@77 1))))))
(check-sat)
; unknown
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
(assert (and (<= i@76 z@97) (< z@97 (+ j@77 1))))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 7
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= i@76 $x) (< $x (+ j@77 1)))
      (and (<= i@76 $y) (< $y (+ j@77 1)))
      (= (loc<Array~Int~Ref> a@62 $x) (loc<Array~Int~Ref> a@62 $y)))
    (= $x $y))
  
  :qid |qp.inj17|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(declare-fun inv@98 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= i@76 (inv@98 $r)) (< (inv@98 $r) (+ j@77 1)))
    (= (loc<Array~Int~Ref> a@62 (inv@98 $r)) $r))
  :pattern ((inv@98 $r))
  :qid |qp.inv@98-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= i@76 $z) (< $z (+ j@77 1)))
    (= (inv@98 (loc<Array~Int~Ref> a@62 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@62 $z))
  :qid |qp.inv@98-exp|)))
(declare-const fvf@99 $FVF<Bool>)
(assert ($FVF.after_val fvf@99 fvf@96))
; Precomputing split data for loc[Array,Int,Ref](a@62, $z).val # W
(define-fun $pTaken10 (($r $Ref)) $Perm
  (ite
    (and (<= i@76 (inv@98 $r)) (< (inv@98 $r) (+ j@77 1)))
    ($Perm.min
      (ite
        (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
        $Perm.Write
        $Perm.No)
      ($pTaken10 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= i@76 (inv@98 $r)) (< (inv@98 $r) (+ j@77 1)))
    (= (- $Perm.Write ($pTaken10 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@99)))
    (= ($FVF.lookup_val fvf@99 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@99 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@99-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@99))
    (and (<= i@76 (inv@98 $r)) (< (inv@98 $r) (+ j@77 1)))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@99)))
  :qid |qp.fvf@99-dom-inv@98|)))
; [eval] !loc(a, from).val
; [eval] loc(a, from)
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= (loc<Array~Int~Ref> a@62 i@76) $Ref.null))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
(assert (not (and
  (<= 0 (inv@85 (loc<Array~Int~Ref> a@62 i@76)))
  (< (inv@85 (loc<Array~Int~Ref> a@62 i@76)) (length<Array~Int> a@62)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@100 $FVF<Bool>)
(assert ($FVF.after_val fvf@100 fvf@99))
(declare-const $t@101 $Snap)
(declare-const $t@102 $FVF<Bool>)
(assert ($FVF.after_val $t@102 fvf@100))
(assert (= $t@101 ($Snap.combine ($SortWrappers.$FVF<Bool>To$Snap $t@102) $Snap.unit)))
(declare-const z@103 Int)
(push) ; 6
; [eval] (from <= z) && (z < to)
; [eval] from <= z
(push) ; 7
(set-option :timeout 250)
(push) ; 8
(assert (not (not (<= i@76 z@103))))
(check-sat)
; unknown
(pop) ; 8
; 0.05s
; (get-info :all-statistics)
(push) ; 8
(assert (not (<= i@76 z@103)))
(check-sat)
; unknown
(pop) ; 8
; 0.04s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 62] i@76 <= z@103
(assert (<= i@76 z@103))
; [eval] z < to
(pop) ; 8
(push) ; 8
; [else-branch 62] !i@76 <= z@103
(assert (not (<= i@76 z@103)))
(pop) ; 8
(pop) ; 7
(assert (and (<= i@76 z@103) (< z@103 (+ j@77 1))))
; [eval] loc(a, z)
(pop) ; 6
(declare-fun inv@104 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
    (= (loc<Array~Int~Ref> a@62 (inv@104 $r)) $r))
  :pattern ((inv@104 $r))
  :qid |qp.inv@104-imp|)))
(assert (forall ((z@103 Int)) (!
  (=>
    (and (<= i@76 z@103) (< z@103 (+ j@77 1)))
    (= (inv@104 (loc<Array~Int~Ref> a@62 z@103)) z@103))
  :pattern ((loc<Array~Int~Ref> a@62 z@103))
  :qid |qp.inv@104-exp|)))
(assert (forall ((z@103 Int)) (!
  (=>
    (and (<= i@76 z@103) (< z@103 (+ j@77 1)))
    (not (= (loc<Array~Int~Ref> a@62 z@103) $Ref.null)))
  :pattern ((loc<Array~Int~Ref> a@62 z@103))
  :qid |qp.null18|)))
; [eval] 1 + countFalse(a, from + 1, to) == countFalse(a, from, to)
; [eval] 1 + countFalse(a, from + 1, to)
; [eval] countFalse(a, from + 1, to)
; [eval] from + 1
; [eval] (0 <= from + 1) && ((from + 1 <= to) && (to <= length(a)))
; [eval] 0 <= from + 1
; [eval] from + 1
(push) ; 6
(push) ; 7
(assert (not (not (<= 0 (+ i@76 1)))))
(check-sat)
; unknown
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= 0 (+ i@76 1))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 63] 0 <= i@76 + 1
(assert (<= 0 (+ i@76 1)))
; [eval] (from + 1 <= to) && (to <= length(a))
; [eval] from + 1 <= to
; [eval] from + 1
(push) ; 8
(push) ; 9
(assert (not (not (<= (+ i@76 1) (+ j@77 1)))))
(check-sat)
; unknown
(pop) ; 9
; 0.07s
; (get-info :all-statistics)
(push) ; 9
(assert (not (<= (+ i@76 1) (+ j@77 1))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 64] i@76 + 1 <= j@77 + 1
(assert (<= (+ i@76 1) (+ j@77 1)))
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 9
; [dead else-branch 64] !i@76 + 1 <= j@77 + 1
(pop) ; 8
(pop) ; 7
; [dead else-branch 63] !0 <= i@76 + 1
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
(assert (not (and
  (<= 0 (+ i@76 1))
  (and (<= (+ i@76 1) (+ j@77 1)) (<= (+ j@77 1) (length<Array~Int> a@62))))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and
  (<= 0 (+ i@76 1))
  (and (<= (+ i@76 1) (+ j@77 1)) (<= (+ j@77 1) (length<Array~Int> a@62)))))
(declare-const z@105 Int)
(push) ; 6
; [eval] (from + 1 <= z) && (z < to)
; [eval] from + 1 <= z
; [eval] from + 1
(push) ; 7
(set-option :timeout 250)
(push) ; 8
(assert (not (not (<= (+ i@76 1) z@105))))
(check-sat)
; unknown
(pop) ; 8
; 0.02s
; (get-info :all-statistics)
(push) ; 8
(assert (not (<= (+ i@76 1) z@105)))
(check-sat)
; unknown
(pop) ; 8
; 0.08s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 65] i@76 + 1 <= z@105
(assert (<= (+ i@76 1) z@105))
; [eval] z < to
(pop) ; 8
(push) ; 8
; [else-branch 65] !i@76 + 1 <= z@105
(assert (not (<= (+ i@76 1) z@105)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(assert (not (not (and (<= (+ i@76 1) z@105) (< z@105 (+ j@77 1))))))
(check-sat)
; unknown
(pop) ; 7
; 0.06s
; (get-info :all-statistics)
(assert (and (<= (+ i@76 1) z@105) (< z@105 (+ j@77 1))))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 7
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= (+ i@76 1) $x) (< $x (+ j@77 1)))
      (and (<= (+ i@76 1) $y) (< $y (+ j@77 1)))
      (= (loc<Array~Int~Ref> a@62 $x) (loc<Array~Int~Ref> a@62 $y)))
    (= $x $y))
  
  :qid |qp.inj19|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(declare-fun inv@106 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= (+ i@76 1) (inv@106 $r)) (< (inv@106 $r) (+ j@77 1)))
    (= (loc<Array~Int~Ref> a@62 (inv@106 $r)) $r))
  :pattern ((inv@106 $r))
  :qid |qp.inv@106-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= (+ i@76 1) $z) (< $z (+ j@77 1)))
    (= (inv@106 (loc<Array~Int~Ref> a@62 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@62 $z))
  :qid |qp.inv@106-exp|)))
(declare-const fvf@107 $FVF<Bool>)
(assert ($FVF.after_val fvf@107 $t@102))
; Precomputing split data for loc[Array,Int,Ref](a@62, $z).val # W
(define-fun $pTaken11 (($r $Ref)) $Perm
  (ite
    (and (<= (+ i@76 1) (inv@106 $r)) (< (inv@106 $r) (+ j@77 1)))
    ($Perm.min
      (ite
        (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
(define-fun $pTaken12 (($r $Ref)) $Perm
  (ite
    (and (<= (+ i@76 1) (inv@106 $r)) (< (inv@106 $r) (+ j@77 1)))
    ($Perm.min
      (-
        (ite
          (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
          $Perm.Write
          $Perm.No)
        ($pTaken10 $r))
      (- $Perm.Write ($pTaken11 $r)))
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
        $Perm.Write
        $Perm.No)
      ($pTaken11 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.02s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= (+ i@76 1) (inv@106 $r)) (< (inv@106 $r) (+ j@77 1)))
    (= (- $Perm.Write ($pTaken11 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
            $Perm.Write
            $Perm.No)
          ($pTaken10 $r)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@107)))
    (= ($FVF.lookup_val fvf@107 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@107 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@107-lookup-2|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@107)))
    (= ($FVF.lookup_val fvf@107 $r) ($FVF.lookup_val $t@102 $r)))
  :pattern (($FVF.lookup_val fvf@107 $r) (inv@104 $r))
  :pattern (($FVF.lookup_val $t@102 $r) (inv@104 $r))
  :qid |qp.fvf@107-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@107))
    (and (<= (+ i@76 1) (inv@106 $r)) (< (inv@106 $r) (+ j@77 1)))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@107)))
  :qid |qp.fvf@107-dom-inv@106|)))
; [eval] countFalse(a, from, to)
; [eval] (0 <= from) && ((from <= to) && (to <= length(a)))
; [eval] 0 <= from
(push) ; 6
(set-option :timeout 250)
(push) ; 7
(assert (not (not (<= 0 i@76))))
(check-sat)
; unknown
(pop) ; 7
; 0.13s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= 0 i@76)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 66] 0 <= i@76
(assert (<= 0 i@76))
; [eval] (from <= to) && (to <= length(a))
; [eval] from <= to
(push) ; 8
(push) ; 9
(assert (not (not (<= i@76 (+ j@77 1)))))
(check-sat)
; unknown
(pop) ; 9
; 0.03s
; (get-info :all-statistics)
(push) ; 9
(assert (not (<= i@76 (+ j@77 1))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 67] i@76 <= j@77 + 1
(assert (<= i@76 (+ j@77 1)))
; [eval] to <= length(a)
; [eval] length(a)
(pop) ; 9
; [dead else-branch 67] !i@76 <= j@77 + 1
(pop) ; 8
(pop) ; 7
; [dead else-branch 66] !0 <= i@76
(pop) ; 6
(declare-const z@108 Int)
(push) ; 6
; [eval] (from <= z) && (z < to)
; [eval] from <= z
(push) ; 7
(push) ; 8
(assert (not (not (<= i@76 z@108))))
(check-sat)
; unknown
(pop) ; 8
; 0.09s
; (get-info :all-statistics)
(push) ; 8
(assert (not (<= i@76 z@108)))
(check-sat)
; unknown
(pop) ; 8
; 0.09s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 68] i@76 <= z@108
(assert (<= i@76 z@108))
; [eval] z < to
(pop) ; 8
(push) ; 8
; [else-branch 68] !i@76 <= z@108
(assert (not (<= i@76 z@108)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(assert (not (not (and (<= i@76 z@108) (< z@108 (+ j@77 1))))))
(check-sat)
; unknown
(pop) ; 7
; 0.04s
; (get-info :all-statistics)
(assert (and (<= i@76 z@108) (< z@108 (+ j@77 1))))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 7
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= i@76 $x) (< $x (+ j@77 1)))
      (and (<= i@76 $y) (< $y (+ j@77 1)))
      (= (loc<Array~Int~Ref> a@62 $x) (loc<Array~Int~Ref> a@62 $y)))
    (= $x $y))
  
  :qid |qp.inj20|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(declare-fun inv@109 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= i@76 (inv@109 $r)) (< (inv@109 $r) (+ j@77 1)))
    (= (loc<Array~Int~Ref> a@62 (inv@109 $r)) $r))
  :pattern ((inv@109 $r))
  :qid |qp.inv@109-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= i@76 $z) (< $z (+ j@77 1)))
    (= (inv@109 (loc<Array~Int~Ref> a@62 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@62 $z))
  :qid |qp.inv@109-exp|)))
(declare-const fvf@110 $FVF<Bool>)
(assert ($FVF.after_val fvf@110 fvf@107))
; Precomputing split data for loc[Array,Int,Ref](a@62, $z).val # W
(define-fun $pTaken13 (($r $Ref)) $Perm
  (ite
    (and (<= i@76 (inv@109 $r)) (< (inv@109 $r) (+ j@77 1)))
    ($Perm.min
      (ite
        (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
(define-fun $pTaken14 (($r $Ref)) $Perm
  (ite
    (and (<= i@76 (inv@109 $r)) (< (inv@109 $r) (+ j@77 1)))
    ($Perm.min
      (-
        (ite
          (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
          $Perm.Write
          $Perm.No)
        ($pTaken10 $r))
      (- $Perm.Write ($pTaken13 $r)))
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
        $Perm.Write
        $Perm.No)
      ($pTaken13 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unsat
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= i@76 (inv@109 $r)) (< (inv@109 $r) (+ j@77 1)))
    (= (- $Perm.Write ($pTaken13 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
            $Perm.Write
            $Perm.No)
          ($pTaken10 $r)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@110)))
    (= ($FVF.lookup_val fvf@110 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@110 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@110-lookup-2|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@110)))
    (= ($FVF.lookup_val fvf@110 $r) ($FVF.lookup_val $t@102 $r)))
  :pattern (($FVF.lookup_val fvf@110 $r) (inv@104 $r))
  :pattern (($FVF.lookup_val $t@102 $r) (inv@104 $r))
  :qid |qp.fvf@110-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@110))
    (and (<= i@76 (inv@109 $r)) (< (inv@109 $r) (+ j@77 1)))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@110)))
  :qid |qp.fvf@110-dom-inv@109|)))
(assert (=
  (+
    1
    ($countFalse ($Snap.combine
      $Snap.unit
      ($SortWrappers.$FVF<Bool>To$Snap fvf@107)) a@62 (+ i@76 1) (+ j@77 1)))
  ($countFalse ($Snap.combine
    $Snap.unit
    ($SortWrappers.$FVF<Bool>To$Snap fvf@110)) a@62 i@76 (+ j@77 1))))
; [exec]
; i := i + 1
; [eval] i + 1
; [exec]
; assert j - i < measure
; [eval] j - i < measure
; [eval] j - i
(set-option :timeout 0)
(push) ; 6
(assert (not (< (- j@77 (+ i@76 1)) (- j@77 i@76))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< (- j@77 (+ i@76 1)) (- j@77 i@76)))
; [eval] (0 <= i) && ((i <= j + 1) && (j < length(a)))
; [eval] 0 <= i
(push) ; 6
(set-option :timeout 250)
(push) ; 7
(assert (not (not (<= 0 (+ i@76 1)))))
(check-sat)
; unknown
(pop) ; 7
; 0.25s
; (get-info :all-statistics)
(push) ; 7
(assert (not (<= 0 (+ i@76 1))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 69] 0 <= i@76 + 1
(assert (<= 0 (+ i@76 1)))
; [eval] (i <= j + 1) && (j < length(a))
; [eval] i <= j + 1
; [eval] j + 1
(push) ; 8
(push) ; 9
(assert (not (not (<= (+ i@76 1) (+ j@77 1)))))
(check-sat)
; unknown
(pop) ; 9
; 0.25s
; (get-info :all-statistics)
(push) ; 9
(assert (not (<= (+ i@76 1) (+ j@77 1))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 70] i@76 + 1 <= j@77 + 1
(assert (<= (+ i@76 1) (+ j@77 1)))
; [eval] j < length(a)
; [eval] length(a)
(pop) ; 9
; [dead else-branch 70] !i@76 + 1 <= j@77 + 1
(pop) ; 8
(pop) ; 7
; [dead else-branch 69] !0 <= i@76 + 1
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
(assert (not (and
  (<= 0 (+ i@76 1))
  (and (<= (+ i@76 1) (+ j@77 1)) (< j@77 (length<Array~Int> a@62))))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and
  (<= 0 (+ i@76 1))
  (and (<= (+ i@76 1) (+ j@77 1)) (< j@77 (length<Array~Int> a@62)))))
(declare-const z@111 Int)
(push) ; 6
; [eval] (0 <= z) && (z < length(a))
; [eval] 0 <= z
(push) ; 7
(set-option :timeout 250)
(push) ; 8
(assert (not (not (<= 0 z@111))))
(check-sat)
; unknown
(pop) ; 8
; 0.25s
; (get-info :all-statistics)
(push) ; 8
(assert (not (<= 0 z@111)))
(check-sat)
; unknown
(pop) ; 8
; 0.25s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 71] 0 <= z@111
(assert (<= 0 z@111))
; [eval] z < length(a)
; [eval] length(a)
(pop) ; 8
(push) ; 8
; [else-branch 71] !0 <= z@111
(assert (not (<= 0 z@111)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(assert (not (not (and (<= 0 z@111) (< z@111 (length<Array~Int> a@62))))))
(check-sat)
; unknown
(pop) ; 7
; 0.25s
; (get-info :all-statistics)
(assert (and (<= 0 z@111) (< z@111 (length<Array~Int> a@62))))
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 7
(assert (not (forall (($x Int) ($y Int)) (!
  (=>
    (and
      (and (<= 0 $x) (< $x (length<Array~Int> a@62)))
      (and (<= 0 $y) (< $y (length<Array~Int> a@62)))
      (= (loc<Array~Int~Ref> a@62 $x) (loc<Array~Int~Ref> a@62 $y)))
    (= $x $y))
  
  :qid |qp.inj21|))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(pop) ; 6
(declare-fun inv@112 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (=>
    (and (<= 0 (inv@112 $r)) (< (inv@112 $r) (length<Array~Int> a@62)))
    (= (loc<Array~Int~Ref> a@62 (inv@112 $r)) $r))
  :pattern ((inv@112 $r))
  :qid |qp.inv@112-imp|)))
(assert (forall (($z Int)) (!
  (=>
    (and (<= 0 $z) (< $z (length<Array~Int> a@62)))
    (= (inv@112 (loc<Array~Int~Ref> a@62 $z)) $z))
  :pattern ((loc<Array~Int~Ref> a@62 $z))
  :qid |qp.inv@112-exp|)))
(declare-const fvf@113 $FVF<Bool>)
(assert ($FVF.after_val fvf@113 fvf@110))
; Precomputing split data for loc[Array,Int,Ref](a@62, $z).val # W
(define-fun $pTaken15 (($r $Ref)) $Perm
  (ite
    (and (<= 0 (inv@112 $r)) (< (inv@112 $r) (length<Array~Int> a@62)))
    ($Perm.min
      (ite
        (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
        $Perm.Write
        $Perm.No)
      $Perm.Write)
    $Perm.No))
(define-fun $pTaken16 (($r $Ref)) $Perm
  (ite
    (and (<= 0 (inv@112 $r)) (< (inv@112 $r) (length<Array~Int> a@62)))
    ($Perm.min
      (-
        (ite
          (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
          $Perm.Write
          $Perm.No)
        ($pTaken10 $r))
      (- $Perm.Write ($pTaken15 $r)))
    $Perm.No))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
        $Perm.Write
        $Perm.No)
      ($pTaken15 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unsat
(pop) ; 6
; 0.03s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= 0 (inv@112 $r)) (< (inv@112 $r) (length<Array~Int> a@62)))
    (= (- $Perm.Write ($pTaken15 $r)) $Perm.No))
  
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.50s
; (get-info :all-statistics)
; Chunk depleted?
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (-
        (ite
          (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
          $Perm.Write
          $Perm.No)
        ($pTaken10 $r))
      ($pTaken16 $r))
    $Perm.No)
  
  ))))
(check-sat)
; unsat
(pop) ; 6
; 0.02s
; (get-info :all-statistics)
; Enough permissions taken?
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=>
    (and (<= 0 (inv@112 $r)) (< (inv@112 $r) (length<Array~Int> a@62)))
    (= (- (- $Perm.Write ($pTaken15 $r)) ($pTaken16 $r)) $Perm.No))
  
  ))))
(check-sat)
; unsat
(pop) ; 6
; 0.02s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
            $Perm.Write
            $Perm.No)
          ($pTaken10 $r)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@113)))
    (= ($FVF.lookup_val fvf@113 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@113 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@113-lookup-2|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@113)))
    (= ($FVF.lookup_val fvf@113 $r) ($FVF.lookup_val $t@102 $r)))
  :pattern (($FVF.lookup_val fvf@113 $r) (inv@104 $r))
  :pattern (($FVF.lookup_val $t@102 $r) (inv@104 $r))
  :qid |qp.fvf@113-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (not (xor
    ($Set.in_$Ref $r ($FVF.domain_val fvf@113))
    (and (<= 0 (inv@112 $r)) (< (inv@112 $r) (length<Array~Int> a@62)))))
  :pattern (($Set.in_$Ref $r ($FVF.domain_val fvf@113)))
  :qid |qp.fvf@113-dom-inv@112|)))
; [eval] (forall z: Int :: (0 <= z) && (z < i) ==> !loc(a, z).val)
(declare-const z@114 Int)
(push) ; 6
; [eval] (0 <= z) && (z < i) ==> !loc(a, z).val
; [eval] (0 <= z) && (z < i)
; [eval] 0 <= z
(push) ; 7
(set-option :timeout 250)
(push) ; 8
(assert (not (not (<= 0 z@114))))
(check-sat)
; unknown
(pop) ; 8
; 0.25s
; (get-info :all-statistics)
(push) ; 8
(assert (not (<= 0 z@114)))
(check-sat)
; unknown
(pop) ; 8
; 0.25s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 72] 0 <= z@114
(assert (<= 0 z@114))
; [eval] z < i
(pop) ; 8
(push) ; 8
; [else-branch 72] !0 <= z@114
(assert (not (<= 0 z@114)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(push) ; 8
(assert (not (not (and (<= 0 z@114) (< z@114 (+ i@76 1))))))
(check-sat)
; unknown
(pop) ; 8
; 0.25s
; (get-info :all-statistics)
(push) ; 8
(assert (not (and (<= 0 z@114) (< z@114 (+ i@76 1)))))
(check-sat)
; unknown
(pop) ; 8
; 0.25s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 73] 0 <= z@114 && z@114 < i@76 + 1
(assert (and (<= 0 z@114) (< z@114 (+ i@76 1))))
; [eval] !loc(a, z).val
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= (loc<Array~Int~Ref> a@62 z@114) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (-
      (ite
        (and
          (<= 0 (inv@85 (loc<Array~Int~Ref> a@62 z@114)))
          (< (inv@85 (loc<Array~Int~Ref> a@62 z@114)) (length<Array~Int> a@62)))
        $Perm.Write
        $Perm.No)
      ($pTaken10 (loc<Array~Int~Ref> a@62 z@114)))
    (ite
      (and
        (<= i@76 (inv@104 (loc<Array~Int~Ref> a@62 z@114)))
        (< (inv@104 (loc<Array~Int~Ref> a@62 z@114)) (+ j@77 1)))
      $Perm.Write
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.07s
; (get-info :all-statistics)
(declare-const fvf@115 $FVF<Bool>)
(assert ($FVF.after_val fvf@115 fvf@113))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
            $Perm.Write
            $Perm.No)
          ($pTaken10 $r)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@115)))
    (= ($FVF.lookup_val fvf@115 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@115 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@115-lookup-2|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@115)))
    (= ($FVF.lookup_val fvf@115 $r) ($FVF.lookup_val $t@102 $r)))
  :pattern (($FVF.lookup_val fvf@115 $r) (inv@104 $r))
  :pattern (($FVF.lookup_val $t@102 $r) (inv@104 $r))
  :qid |qp.fvf@115-lookup-1|)))
(assert (forall ((z@114 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@114) ($FVF.domain_val fvf@115))
    (and
      (and (<= 0 z@114) (< z@114 (+ i@76 1)))
      (not ($FVF.lookup_val fvf@96 (loc<Array~Int~Ref> a@62 i@76))))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@114)
    ($FVF.domain_val fvf@115)))
  :qid |qp.fvf@115-dom|)))
(pop) ; 8
(push) ; 8
; [else-branch 73] !0 <= z@114 && z@114 < i@76 + 1
(assert (not (and (<= 0 z@114) (< z@114 (+ i@76 1)))))
(pop) ; 8
(pop) ; 7
(assert (forall ((z@114 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@114) ($FVF.domain_val fvf@115))
    (and
      (and (<= 0 z@114) (< z@114 (+ i@76 1)))
      (not ($FVF.lookup_val fvf@96 (loc<Array~Int~Ref> a@62 i@76))))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@114)
    ($FVF.domain_val fvf@115)))
  :qid |qp.fvf@115-dom|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@115)))
    (= ($FVF.lookup_val fvf@115 $r) ($FVF.lookup_val $t@102 $r)))
  :pattern (($FVF.lookup_val fvf@115 $r) (inv@104 $r))
  :pattern (($FVF.lookup_val $t@102 $r) (inv@104 $r))
  :qid |qp.fvf@115-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
            $Perm.Write
            $Perm.No)
          ($pTaken10 $r)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@115)))
    (= ($FVF.lookup_val fvf@115 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@115 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@115-lookup-2|)))
(assert ($FVF.after_val fvf@115 fvf@113))
(pop) ; 6
(assert (forall ((z@114 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@114) ($FVF.domain_val fvf@115))
    (and
      (and (<= 0 z@114) (< z@114 (+ i@76 1)))
      (not ($FVF.lookup_val fvf@96 (loc<Array~Int~Ref> a@62 i@76))))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@114)
    ($FVF.domain_val fvf@115)))
  :qid |qp.fvf@115-dom|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@115)))
    (= ($FVF.lookup_val fvf@115 $r) ($FVF.lookup_val $t@102 $r)))
  :pattern (($FVF.lookup_val fvf@115 $r) (inv@104 $r))
  :pattern (($FVF.lookup_val $t@102 $r) (inv@104 $r))
  :qid |qp.fvf@115-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
            $Perm.Write
            $Perm.No)
          ($pTaken10 $r)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@115)))
    (= ($FVF.lookup_val fvf@115 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@115 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@115-lookup-2|)))
(assert ($FVF.after_val fvf@115 fvf@113))
(push) ; 6
(assert (not (forall ((z@114 Int)) (!
  (=>
    (and (<= 0 z@114) (< z@114 (+ i@76 1)))
    (not ($FVF.lookup_val fvf@115 (loc<Array~Int~Ref> a@62 z@114))))
  :pattern ((loc<Array~Int~Ref> a@62 z@114))
  :qid |prog.l49|))))
(check-sat)
; unknown
(pop) ; 6
; 0.62s
; (get-info :all-statistics)
(push) ; 6
(pop) ; 6
; [eval] (forall z: Int :: (0 <= z) && (z < i) ==> !loc(a, z).val)
(declare-const z@116 Int)
(push) ; 6
; [eval] (0 <= z) && (z < i) ==> !loc(a, z).val
; [eval] (0 <= z) && (z < i)
; [eval] 0 <= z
(push) ; 7
(set-option :timeout 250)
(push) ; 8
(assert (not (not (<= 0 z@116))))
(check-sat)
; unknown
(pop) ; 8
; 0.25s
; (get-info :all-statistics)
(push) ; 8
(assert (not (<= 0 z@116)))
(check-sat)
; unknown
(pop) ; 8
; 0.25s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 74] 0 <= z@116
(assert (<= 0 z@116))
(push) ; 9
(pop) ; 9
; [eval] z < i
(pop) ; 8
(push) ; 8
; [else-branch 74] !0 <= z@116
(assert (not (<= 0 z@116)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(push) ; 8
(assert (not (not (and (<= 0 z@116) (< z@116 (+ i@76 1))))))
(check-sat)
; unknown
(pop) ; 8
; 0.25s
; (get-info :all-statistics)
(push) ; 8
(assert (not (and (<= 0 z@116) (< z@116 (+ i@76 1)))))
(check-sat)
; unknown
(pop) ; 8
; 0.25s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 75] 0 <= z@116 && z@116 < i@76 + 1
(assert (and (<= 0 z@116) (< z@116 (+ i@76 1))))
(push) ; 9
(pop) ; 9
; [eval] !loc(a, z).val
; [eval] loc(a, z)
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= (loc<Array~Int~Ref> a@62 z@116) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (-
      (ite
        (and
          (<= 0 (inv@85 (loc<Array~Int~Ref> a@62 z@116)))
          (< (inv@85 (loc<Array~Int~Ref> a@62 z@116)) (length<Array~Int> a@62)))
        $Perm.Write
        $Perm.No)
      ($pTaken10 (loc<Array~Int~Ref> a@62 z@116)))
    (ite
      (and
        (<= i@76 (inv@104 (loc<Array~Int~Ref> a@62 z@116)))
        (< (inv@104 (loc<Array~Int~Ref> a@62 z@116)) (+ j@77 1)))
      $Perm.Write
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.06s
; (get-info :all-statistics)
(declare-const fvf@117 $FVF<Bool>)
(assert ($FVF.after_val fvf@117 fvf@115))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
            $Perm.Write
            $Perm.No)
          ($pTaken10 $r)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@117)))
    (= ($FVF.lookup_val fvf@117 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@117 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@117-lookup-2|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@117)))
    (= ($FVF.lookup_val fvf@117 $r) ($FVF.lookup_val $t@102 $r)))
  :pattern (($FVF.lookup_val fvf@117 $r) (inv@104 $r))
  :pattern (($FVF.lookup_val $t@102 $r) (inv@104 $r))
  :qid |qp.fvf@117-lookup-1|)))
(assert (forall ((z@116 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@116) ($FVF.domain_val fvf@117))
    (and
      (and (<= 0 z@116) (< z@116 (+ i@76 1)))
      (not ($FVF.lookup_val fvf@96 (loc<Array~Int~Ref> a@62 i@76))))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@116)
    ($FVF.domain_val fvf@117)))
  :qid |qp.fvf@117-dom|)))
(pop) ; 8
(push) ; 8
; [else-branch 75] !0 <= z@116 && z@116 < i@76 + 1
(assert (not (and (<= 0 z@116) (< z@116 (+ i@76 1)))))
(pop) ; 8
(pop) ; 7
(assert (forall ((z@116 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@116) ($FVF.domain_val fvf@117))
    (and
      (and (<= 0 z@116) (< z@116 (+ i@76 1)))
      (not ($FVF.lookup_val fvf@96 (loc<Array~Int~Ref> a@62 i@76))))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@116)
    ($FVF.domain_val fvf@117)))
  :qid |qp.fvf@117-dom|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@117)))
    (= ($FVF.lookup_val fvf@117 $r) ($FVF.lookup_val $t@102 $r)))
  :pattern (($FVF.lookup_val fvf@117 $r) (inv@104 $r))
  :pattern (($FVF.lookup_val $t@102 $r) (inv@104 $r))
  :qid |qp.fvf@117-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
            $Perm.Write
            $Perm.No)
          ($pTaken10 $r)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@117)))
    (= ($FVF.lookup_val fvf@117 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@117 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@117-lookup-2|)))
(assert ($FVF.after_val fvf@117 fvf@115))
(pop) ; 6
(assert (forall ((z@116 Int)) (!
  (not (xor
    ($Set.in_$Ref (loc<Array~Int~Ref> a@62 z@116) ($FVF.domain_val fvf@117))
    (and
      (and (<= 0 z@116) (< z@116 (+ i@76 1)))
      (not ($FVF.lookup_val fvf@96 (loc<Array~Int~Ref> a@62 i@76))))))
  :pattern (($Set.in_$Ref
    (loc<Array~Int~Ref> a@62 z@116)
    ($FVF.domain_val fvf@117)))
  :qid |qp.fvf@117-dom|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (and (<= i@76 (inv@104 $r)) (< (inv@104 $r) (+ j@77 1)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@117)))
    (= ($FVF.lookup_val fvf@117 $r) ($FVF.lookup_val $t@102 $r)))
  :pattern (($FVF.lookup_val fvf@117 $r) (inv@104 $r))
  :pattern (($FVF.lookup_val $t@102 $r) (inv@104 $r))
  :qid |qp.fvf@117-lookup-1|)))
(assert (forall (($r $Ref)) (!
  (=>
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (inv@85 $r)) (< (inv@85 $r) (length<Array~Int> a@62)))
            $Perm.Write
            $Perm.No)
          ($pTaken10 $r)))
      ($Set.in_$Ref $r ($FVF.domain_val fvf@117)))
    (= ($FVF.lookup_val fvf@117 $r) ($FVF.lookup_val $t@83 $r)))
  :pattern (($FVF.lookup_val fvf@117 $r) (inv@85 $r))
  :pattern (($FVF.lookup_val $t@83 $r) (inv@85 $r))
  :qid |qp.fvf@117-lookup-2|)))
(assert ($FVF.after_val fvf@117 fvf@115))
(push) ; 6
(assert (not (forall ((z@116 Int)) (!
  (=>
    (and (<= 0 z@116) (< z@116 (+ i@76 1)))
    (not ($FVF.lookup_val fvf@117 (loc<Array~Int~Ref> a@62 z@116))))
  :pattern ((loc<Array~Int~Ref> a@62 z@116))
  :qid |prog.l49|))))
(check-sat)
; unknown
(pop) ; 6
; 0.79s
; (get-info :all-statistics)
(pop) ; 5
(pop) ; 4
(pop) ; 3
(pop) ; 2

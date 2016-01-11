(get-info :version)
; (:version "4.4.2")
; Input file is matching_loop_issue_nested.sil
; Started: 2015-11-06 10:22:48
; Silicon.buildVersion: 0.1-SNAPSHOT 5e4128d5fd0a cvc4-func-overloading-easy-fix 2015/11/06 10:12:21
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
(declare-sort $ISeq 0)
(declare-sort $Process 0)
(declare-fun p_put_all<ISeq~Process> ($ISeq) $Process)
(declare-fun p_put<Int~Process> (Int) $Process)
(declare-fun p_seq<Process~Process~Process> ($Process $Process) $Process)
(declare-fun p_empty<Process> () $Process)
(declare-fun append<ISeq~ISeq~ISeq> ($ISeq $ISeq) $ISeq)
(declare-fun drop<ISeq~Int~ISeq> ($ISeq Int) $ISeq)
(declare-fun idx<ISeq~Int~Int> ($ISeq Int) Int)
(declare-fun len<ISeq~Int> ($ISeq) Int)
(declare-fun sgltn<Int~ISeq> (Int) $ISeq)
(assert true)
(assert (forall (($es $ISeq)) (!
  (=
    (ite
      (= (len<ISeq~Int> $es) 0)
      p_empty<Process>
      (p_seq<Process~Process~Process> (p_put<Int~Process> (idx<ISeq~Int~Int> $es 0)) (p_put_all<ISeq~Process> (drop<ISeq~Int~ISeq> $es 1))))
    (p_put_all<ISeq~Process> $es))
  :pattern ((len<ISeq~Int> $es))
  :pattern ((p_seq<Process~Process~Process> (p_put<Int~Process> (idx<ISeq~Int~Int> $es 0)) (p_put_all<ISeq~Process> (drop<ISeq~Int~ISeq> $es 1))))
  :pattern ((p_put_all<ISeq~Process> $es))
  :qid |prog.put_all_def_suspect|)))
(assert (forall (($p1 $Process)) (!
  (forall (($p2 $Process)) (!
    (forall (($p3 $Process)) (!
      (=
        (p_seq<Process~Process~Process> (p_seq<Process~Process~Process> $p1 $p2) $p3)
        (p_seq<Process~Process~Process> $p1 (p_seq<Process~Process~Process> $p2 $p3)))
      :pattern ((p_seq<Process~Process~Process> (p_seq<Process~Process~Process> $p1 $p2) $p3))
      :pattern ((p_seq<Process~Process~Process> $p1 (p_seq<Process~Process~Process> $p2 $p3)))
      ))
    :pattern ((p_seq<Process~Process~Process> $p1 $p2))
    ))
  
  :qid |prog.seq_assoc_nested|)))
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
(declare-fun $SortWrappers.$ISeqTo$Snap ($ISeq) $Snap)
(declare-fun $SortWrappers.$SnapTo$ISeq ($Snap) $ISeq)
(assert (forall ((x $ISeq)) (!
    (= x ($SortWrappers.$SnapTo$ISeq($SortWrappers.$ISeqTo$Snap x)))
    :pattern (($SortWrappers.$ISeqTo$Snap x))
    :qid |$Snap.$ISeq|
    )))
(declare-fun $SortWrappers.$ProcessTo$Snap ($Process) $Snap)
(declare-fun $SortWrappers.$SnapTo$Process ($Snap) $Process)
(assert (forall ((x $Process)) (!
    (= x ($SortWrappers.$SnapTo$Process($SortWrappers.$ProcessTo$Snap x)))
    :pattern (($SortWrappers.$ProcessTo$Snap x))
    :qid |$Snap.$Process|
    )))
; Preamble end
; ------------------------------------------------------------
; ------------------------------------------------------------
; Declaring program functions
(declare-const s@$ $Snap)
; ---------- test ----------
(declare-const es@1 $ISeq)
(declare-const e@2 Int)
(push) ; 2
(push) ; 3
; [eval] p_seq(p_put_all(es), p_put(e)) == p_put_all(append(es, sgltn(e)))
; [eval] p_seq(p_put_all(es), p_put(e))
; [eval] p_put_all(es)
; [eval] p_put(e)
; [eval] p_put_all(append(es, sgltn(e)))
; [eval] append(es, sgltn(e))
; [eval] sgltn(e)
(assert (=
  (p_seq<Process~Process~Process> (p_put_all<ISeq~Process> es@1) (p_put<Int~Process> e@2))
  (p_put_all<ISeq~Process> (append<ISeq~ISeq~ISeq> es@1 (sgltn<Int~ISeq> e@2)))))
(pop) ; 3
(push) ; 3
; [eval] p_seq(p_put_all(es), p_put(e)) == p_put_all(append(es, sgltn(e)))
; [eval] p_seq(p_put_all(es), p_put(e))
; [eval] p_put_all(es)
; [eval] p_put(e)
; [eval] p_put_all(append(es, sgltn(e)))
; [eval] append(es, sgltn(e))
; [eval] sgltn(e)
(push) ; 4
(assert (not (=
  (p_seq<Process~Process~Process> (p_put_all<ISeq~Process> es@1) (p_put<Int~Process> e@2))
  (p_put_all<ISeq~Process> (append<ISeq~ISeq~ISeq> es@1 (sgltn<Int~ISeq> e@2))))))
(check-sat)

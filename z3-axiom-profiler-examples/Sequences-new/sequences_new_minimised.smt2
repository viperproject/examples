(set-option :print-success false)
(set-info :smt-lib-version 2.0)
(set-option :AUTO_CONFIG false)
(set-option :pp.bv_literals false)
(set-option :MODEL.V2 true)
(set-option :smt.PHASE_SELECTION 0)
(set-option :smt.RESTART_STRATEGY 0)
(set-option :smt.RESTART_FACTOR |1.5|)
(set-option :smt.ARITH.RANDOM_INITIAL_VALUE true)
(set-option :smt.CASE_SPLIT 3)
(set-option :smt.DELAY_UNITS true)
(set-option :NNF.SK_HACK true)
(set-option :smt.MBQI false)
(set-option :smt.QI.EAGER_THRESHOLD 100)
(set-option :TYPE_CHECK true)
(set-option :smt.BV.REFLECT true)
(set-option :TIMEOUT 0)
; done setting options


(set-info :category "industrial")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun real_pow (Real Real) Real)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)
(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-fun Ctor (T@T) Int)
(declare-fun intType () T@T)
(declare-fun realType () T@T)
(declare-fun boolType () T@T)
(declare-fun int_2_U (Int) T@U)
(declare-fun U_2_int (T@U) Int)
(declare-fun type (T@U) T@T)
(declare-fun real_2_U (Real) T@U)
(declare-fun U_2_real (T@U) Real)
(declare-fun bool_2_U (Bool) T@U)
(declare-fun U_2_bool (T@U) Bool)
(declare-fun FieldType (T@T T@T) T@T)
(declare-fun FieldTypeInv0 (T@T) T@T)
(declare-fun FieldTypeInv1 (T@T) T@T)
(declare-fun NormalFieldType () T@T)
(declare-fun $allocated () T@U)
(declare-fun RefType () T@T)
(declare-fun special_ref () T@U)
(declare-fun MapType0Type (T@T) T@T)
(declare-fun MapType0TypeInv0 (T@T) T@T)
(declare-fun MapType0Select (T@U T@U T@U) T@U)
(declare-fun MapType0Store (T@U T@U T@U T@U) T@U)
(declare-fun MapType1Type (T@T T@T) T@T)
(declare-fun MapType1TypeInv0 (T@T) T@T)
(declare-fun MapType1TypeInv1 (T@T) T@T)
(declare-fun MapType1Select (T@U T@U T@U) T@U)
(declare-fun MapType1Store (T@U T@U T@U T@U) T@U)
(declare-fun null () T@U)
(declare-fun state (T@U T@U) Bool)
(declare-fun IdenticalOnKnownLocations (T@U T@U T@U) Bool)
(declare-fun HasDirectPerm (T@U T@U T@U) Bool)
(declare-fun PredicateMaskField (T@U) T@U)
(declare-fun IsPredicateField (T@U) Bool)
(declare-fun ZeroMask () T@U)
(declare-fun ZeroPMask () T@U)
(declare-fun NoPerm () Real)
(declare-fun FullPerm () Real)
(declare-fun GoodMask (T@U) Bool)
(declare-fun InsidePredicate (T@U T@U Int T@U T@U Int) Bool)
(declare-fun SeqType (T@T) T@T)
(declare-fun SeqTypeInv0 (T@T) T@T)
(declare-fun |Seq#Length| (T@U) Int)
(declare-fun |Seq#Empty| (T@T) T@U)
(declare-fun |Seq#Singleton| (T@U) T@U)
(declare-fun |Seq#Index| (T@U Int) T@U)
(declare-fun |Seq#Append| (T@U T@U) T@U)
(declare-fun |Seq#Take| (T@U Int) T@U)
(declare-fun |Seq#Drop| (T@U Int) T@U)
(declare-fun |Seq#Contains| (T@U T@U) Bool)
(declare-fun |Seq#Find| (T@U T@U) Int)
(declare-fun |Seq#Equal| (T@U T@U) Bool)
(declare-fun |Seq#Range| (Int Int) T@U)
(declare-fun Heap@@8 () T@U)
(declare-fun Mask@@10 () T@U)
(declare-fun a_2@0 () T@U)
(declare-fun %lbl%+2424 () Bool)
(declare-fun %lbl%@5363 () Bool)
(declare-fun %lbl%@5379 () Bool)
(declare-fun %lbl%@5409 () Bool)
(declare-fun %lbl%@5490 () Bool)
(declare-fun %lbl%+5297 () Bool)
(assert  (and (and (and (and (and (and (and (and (and (and (and (= (Ctor intType) 0) (= (Ctor realType) 1)) (= (Ctor boolType) 2)) (forall ((arg0 Int) ) (! (= (U_2_int (int_2_U arg0)) arg0)
 :qid |typeInv:U_2_int|
 :pattern ( (int_2_U arg0))
))) (forall ((x T@U) ) (!  (=> (= (type x) intType) (= (int_2_U (U_2_int x)) x))
 :qid |cast:U_2_int|
 :pattern ( (U_2_int x))
))) (forall ((arg0@@0 Int) ) (! (= (type (int_2_U arg0@@0)) intType)
 :qid |funType:int_2_U|
 :pattern ( (int_2_U arg0@@0))
))) (forall ((arg0@@1 Real) ) (! (= (U_2_real (real_2_U arg0@@1)) arg0@@1)
 :qid |typeInv:U_2_real|
 :pattern ( (real_2_U arg0@@1))
))) (forall ((x@@0 T@U) ) (!  (=> (= (type x@@0) realType) (= (real_2_U (U_2_real x@@0)) x@@0))
 :qid |cast:U_2_real|
 :pattern ( (U_2_real x@@0))
))) (forall ((arg0@@2 Real) ) (! (= (type (real_2_U arg0@@2)) realType)
 :qid |funType:real_2_U|
 :pattern ( (real_2_U arg0@@2))
))) (forall ((arg0@@3 Bool) ) (! (= (U_2_bool (bool_2_U arg0@@3)) arg0@@3)
 :qid |typeInv:U_2_bool|
 :pattern ( (bool_2_U arg0@@3))
))) (forall ((x@@1 T@U) ) (!  (=> (= (type x@@1) boolType) (= (bool_2_U (U_2_bool x@@1)) x@@1))
 :qid |cast:U_2_bool|
 :pattern ( (U_2_bool x@@1))
))) (forall ((arg0@@4 Bool) ) (! (= (type (bool_2_U arg0@@4)) boolType)
 :qid |funType:bool_2_U|
 :pattern ( (bool_2_U arg0@@4))
))))
(assert (forall ((x@@2 T@U) ) (! (UOrdering2 x@@2 x@@2)
 :qid |bg:subtype-refl|
 :no-pattern (U_2_int x@@2)
 :no-pattern (U_2_bool x@@2)
)))
(assert (forall ((x@@3 T@U) (y T@U) (z T@U) ) (! (let ((alpha (type x@@3)))
 (=> (and (and (= (type y) alpha) (= (type z) alpha)) (and (UOrdering2 x@@3 y) (UOrdering2 y z))) (UOrdering2 x@@3 z)))
 :qid |bg:subtype-trans|
 :pattern ( (UOrdering2 x@@3 y) (UOrdering2 y z))
)))
(assert (forall ((x@@4 T@U) (y@@0 T@U) ) (! (let ((alpha@@0 (type x@@4)))
 (=> (= (type y@@0) alpha@@0) (=> (and (UOrdering2 x@@4 y@@0) (UOrdering2 y@@0 x@@4)) (= x@@4 y@@0))))
 :qid |bg:subtype-antisymm|
 :pattern ( (UOrdering2 x@@4 y@@0) (UOrdering2 y@@0 x@@4))
)))
(assert  (and (and (and (and (and (and (forall ((arg0@@5 T@T) (arg1 T@T) ) (! (= (Ctor (FieldType arg0@@5 arg1)) 3)
 :qid |ctor:FieldType|
)) (forall ((arg0@@6 T@T) (arg1@@0 T@T) ) (! (= (FieldTypeInv0 (FieldType arg0@@6 arg1@@0)) arg0@@6)
 :qid |typeInv:FieldTypeInv0|
 :pattern ( (FieldType arg0@@6 arg1@@0))
))) (forall ((arg0@@7 T@T) (arg1@@1 T@T) ) (! (= (FieldTypeInv1 (FieldType arg0@@7 arg1@@1)) arg1@@1)
 :qid |typeInv:FieldTypeInv1|
 :pattern ( (FieldType arg0@@7 arg1@@1))
))) (= (Ctor NormalFieldType) 4)) (= (type $allocated) (FieldType NormalFieldType boolType))) (= (Ctor RefType) 5)) (= (type special_ref) RefType)))
(assert (distinct $allocated special_ref)
)
(assert  (and (and (and (and (and (and (and (and (and (and (and (and (and (forall ((arg0@@8 T@T) ) (! (= (Ctor (MapType0Type arg0@@8)) 6)
 :qid |ctor:MapType0Type|
)) (forall ((arg0@@9 T@T) ) (! (= (MapType0TypeInv0 (MapType0Type arg0@@9)) arg0@@9)
 :qid |typeInv:MapType0TypeInv0|
 :pattern ( (MapType0Type arg0@@9))
))) (forall ((arg0@@10 T@U) (arg1@@2 T@U) (arg2 T@U) ) (! (let ((B (FieldTypeInv1 (type arg2))))
(= (type (MapType0Select arg0@@10 arg1@@2 arg2)) B))
 :qid |funType:MapType0Select|
 :pattern ( (MapType0Select arg0@@10 arg1@@2 arg2))
))) (forall ((arg0@@11 T@U) (arg1@@3 T@U) (arg2@@0 T@U) (arg3 T@U) ) (! (let ((aVar0 (type arg1@@3)))
(= (type (MapType0Store arg0@@11 arg1@@3 arg2@@0 arg3)) (MapType0Type aVar0)))
 :qid |funType:MapType0Store|
 :pattern ( (MapType0Store arg0@@11 arg1@@3 arg2@@0 arg3))
))) (forall ((m T@U) (x0 T@U) (x1 T@U) (val T@U) ) (! (let ((B@@0 (FieldTypeInv1 (type x1))))
 (=> (= (type val) B@@0) (= (MapType0Select (MapType0Store m x0 x1 val) x0 x1) val)))
 :qid |mapAx0:MapType0Select|
 :weight 0
))) (and (and (forall ((val@@0 T@U) (m@@0 T@U) (x0@@0 T@U) (x1@@0 T@U) (y0 T@U) (y1 T@U) ) (!  (or (= x0@@0 y0) (= (MapType0Select (MapType0Store m@@0 x0@@0 x1@@0 val@@0) y0 y1) (MapType0Select m@@0 y0 y1)))
 :qid |mapAx1:MapType0Select:0|
 :weight 0
)) (forall ((val@@1 T@U) (m@@1 T@U) (x0@@1 T@U) (x1@@1 T@U) (y0@@0 T@U) (y1@@0 T@U) ) (!  (or (= x1@@1 y1@@0) (= (MapType0Select (MapType0Store m@@1 x0@@1 x1@@1 val@@1) y0@@0 y1@@0) (MapType0Select m@@1 y0@@0 y1@@0)))
 :qid |mapAx1:MapType0Select:1|
 :weight 0
))) (forall ((val@@2 T@U) (m@@2 T@U) (x0@@2 T@U) (x1@@2 T@U) (y0@@1 T@U) (y1@@1 T@U) ) (!  (or true (= (MapType0Select (MapType0Store m@@2 x0@@2 x1@@2 val@@2) y0@@1 y1@@1) (MapType0Select m@@2 y0@@1 y1@@1)))
 :qid |mapAx2:MapType0Select|
 :weight 0
)))) (forall ((arg0@@12 T@T) (arg1@@4 T@T) ) (! (= (Ctor (MapType1Type arg0@@12 arg1@@4)) 7)
 :qid |ctor:MapType1Type|
))) (forall ((arg0@@13 T@T) (arg1@@5 T@T) ) (! (= (MapType1TypeInv0 (MapType1Type arg0@@13 arg1@@5)) arg0@@13)
 :qid |typeInv:MapType1TypeInv0|
 :pattern ( (MapType1Type arg0@@13 arg1@@5))
))) (forall ((arg0@@14 T@T) (arg1@@6 T@T) ) (! (= (MapType1TypeInv1 (MapType1Type arg0@@14 arg1@@6)) arg1@@6)
 :qid |typeInv:MapType1TypeInv1|
 :pattern ( (MapType1Type arg0@@14 arg1@@6))
))) (forall ((arg0@@15 T@U) (arg1@@7 T@U) (arg2@@1 T@U) ) (! (let ((aVar1 (MapType1TypeInv1 (type arg0@@15))))
(= (type (MapType1Select arg0@@15 arg1@@7 arg2@@1)) aVar1))
 :qid |funType:MapType1Select|
 :pattern ( (MapType1Select arg0@@15 arg1@@7 arg2@@1))
))) (forall ((arg0@@16 T@U) (arg1@@8 T@U) (arg2@@2 T@U) (arg3@@0 T@U) ) (! (let ((aVar1@@0 (type arg3@@0)))
(let ((aVar0@@0 (type arg1@@8)))
(= (type (MapType1Store arg0@@16 arg1@@8 arg2@@2 arg3@@0)) (MapType1Type aVar0@@0 aVar1@@0))))
 :qid |funType:MapType1Store|
 :pattern ( (MapType1Store arg0@@16 arg1@@8 arg2@@2 arg3@@0))
))) (forall ((m@@3 T@U) (x0@@3 T@U) (x1@@3 T@U) (val@@3 T@U) ) (! (let ((aVar1@@1 (MapType1TypeInv1 (type m@@3))))
 (=> (= (type val@@3) aVar1@@1) (= (MapType1Select (MapType1Store m@@3 x0@@3 x1@@3 val@@3) x0@@3 x1@@3) val@@3)))
 :qid |mapAx0:MapType1Select|
 :weight 0
))) (and (and (forall ((val@@4 T@U) (m@@4 T@U) (x0@@4 T@U) (x1@@4 T@U) (y0@@2 T@U) (y1@@2 T@U) ) (!  (or (= x0@@4 y0@@2) (= (MapType1Select (MapType1Store m@@4 x0@@4 x1@@4 val@@4) y0@@2 y1@@2) (MapType1Select m@@4 y0@@2 y1@@2)))
 :qid |mapAx1:MapType1Select:0|
 :weight 0
)) (forall ((val@@5 T@U) (m@@5 T@U) (x0@@5 T@U) (x1@@5 T@U) (y0@@3 T@U) (y1@@3 T@U) ) (!  (or (= x1@@5 y1@@3) (= (MapType1Select (MapType1Store m@@5 x0@@5 x1@@5 val@@5) y0@@3 y1@@3) (MapType1Select m@@5 y0@@3 y1@@3)))
 :qid |mapAx1:MapType1Select:1|
 :weight 0
))) (forall ((val@@6 T@U) (m@@6 T@U) (x0@@6 T@U) (x1@@6 T@U) (y0@@4 T@U) (y1@@4 T@U) ) (!  (or true (= (MapType1Select (MapType1Store m@@6 x0@@6 x1@@6 val@@6) y0@@4 y1@@4) (MapType1Select m@@6 y0@@4 y1@@4)))
 :qid |mapAx2:MapType1Select|
 :weight 0
)))) (= (type null) RefType)))
(assert (forall ((o T@U) (f T@U) (Heap T@U) (Mask T@U) ) (!  (=> (and (and (and (= (type o) RefType) (= (type f) (FieldType NormalFieldType RefType))) (= (type Heap) (MapType0Type RefType))) (= (type Mask) (MapType1Type RefType realType))) (or (= (MapType0Select Heap o f) null) (U_2_bool (MapType0Select Heap (MapType0Select Heap o f) $allocated))))
 :qid |sequence.29:15|
 :skolemid |0|
 :pattern ( (state Heap Mask) (MapType0Select Heap o f))
)))
(assert (forall ((Heap@@0 T@U) (ExhaleHeap T@U) (Mask@@0 T@U) (o@@0 T@U) (f_2 T@U) ) (! (let ((B@@1 (FieldTypeInv1 (type f_2))))
(let ((A (FieldTypeInv0 (type f_2))))
 (=> (and (and (and (and (and (and (= (type Heap@@0) (MapType0Type RefType)) (= (type ExhaleHeap) (MapType0Type RefType))) (= (type Mask@@0) (MapType1Type RefType realType))) (= (type o@@0) RefType)) (= (type f_2) (FieldType A B@@1))) (IdenticalOnKnownLocations Heap@@0 ExhaleHeap Mask@@0)) (HasDirectPerm Mask@@0 o@@0 f_2)) (= (MapType0Select Heap@@0 o@@0 f_2) (MapType0Select ExhaleHeap o@@0 f_2)))))
 :qid |sequence.36:22|
 :skolemid |1|
 :pattern ( (IdenticalOnKnownLocations Heap@@0 ExhaleHeap Mask@@0) (MapType0Select Heap@@0 o@@0 f_2))
)))
(assert (forall ((Heap@@1 T@U) (ExhaleHeap@@0 T@U) (Mask@@1 T@U) (o@@1 T@U) (f_2@@0 T@U) ) (! (let ((B@@2 (FieldTypeInv1 (type f_2@@0))))
(let ((A@@0 (FieldTypeInv0 (type f_2@@0))))
 (=> (and (and (and (and (and (and (= (type Heap@@1) (MapType0Type RefType)) (= (type ExhaleHeap@@0) (MapType0Type RefType))) (= (type Mask@@1) (MapType1Type RefType realType))) (= (type o@@1) RefType)) (= (type f_2@@0) (FieldType A@@0 B@@2))) (IdenticalOnKnownLocations Heap@@1 ExhaleHeap@@0 Mask@@1)) (HasDirectPerm Mask@@1 o@@1 f_2@@0)) (= (MapType0Select Heap@@1 o@@1 f_2@@0) (MapType0Select ExhaleHeap@@0 o@@1 f_2@@0)))))
 :qid |sequence.39:21|
 :skolemid |2|
 :pattern ( (IdenticalOnKnownLocations Heap@@1 ExhaleHeap@@0 Mask@@1) (MapType0Select ExhaleHeap@@0 o@@1 f_2@@0))
)))
(assert (forall ((arg0@@17 T@U) ) (! (let ((A@@1 (FieldTypeInv0 (type arg0@@17))))
(= (type (PredicateMaskField arg0@@17)) (FieldType A@@1 (MapType1Type RefType boolType))))
 :qid |funType:PredicateMaskField|
 :pattern ( (PredicateMaskField arg0@@17))
)))
(assert (forall ((Heap@@2 T@U) (ExhaleHeap@@1 T@U) (Mask@@2 T@U) (pm_f T@U) ) (! (let ((C (FieldTypeInv0 (type pm_f))))
 (=> (and (and (and (and (and (= (type Heap@@2) (MapType0Type RefType)) (= (type ExhaleHeap@@1) (MapType0Type RefType))) (= (type Mask@@2) (MapType1Type RefType realType))) (= (type pm_f) (FieldType C intType))) (IdenticalOnKnownLocations Heap@@2 ExhaleHeap@@1 Mask@@2)) (and (HasDirectPerm Mask@@2 null pm_f) (IsPredicateField pm_f))) (= (MapType0Select Heap@@2 null (PredicateMaskField pm_f)) (MapType0Select ExhaleHeap@@1 null (PredicateMaskField pm_f)))))
 :qid |sequence.44:19|
 :skolemid |3|
 :pattern ( (IdenticalOnKnownLocations Heap@@2 ExhaleHeap@@1 Mask@@2) (IsPredicateField pm_f) (MapType0Select ExhaleHeap@@1 null (PredicateMaskField pm_f)))
)))
(assert (forall ((Heap@@3 T@U) (ExhaleHeap@@2 T@U) (Mask@@3 T@U) (pm_f@@0 T@U) ) (! (let ((C@@0 (FieldTypeInv0 (type pm_f@@0))))
 (=> (and (and (and (and (and (= (type Heap@@3) (MapType0Type RefType)) (= (type ExhaleHeap@@2) (MapType0Type RefType))) (= (type Mask@@3) (MapType1Type RefType realType))) (= (type pm_f@@0) (FieldType C@@0 intType))) (IdenticalOnKnownLocations Heap@@3 ExhaleHeap@@2 Mask@@3)) (and (HasDirectPerm Mask@@3 null pm_f@@0) (IsPredicateField pm_f@@0))) (and (forall ((o2 T@U) (f_2@@1 T@U) ) (! (let ((B@@3 (FieldTypeInv1 (type f_2@@1))))
(let ((A@@2 (FieldTypeInv0 (type f_2@@1))))
 (=> (and (and (= (type o2) RefType) (= (type f_2@@1) (FieldType A@@2 B@@3))) (U_2_bool (MapType1Select (MapType0Select Heap@@3 null (PredicateMaskField pm_f@@0)) o2 f_2@@1))) (= (MapType0Select Heap@@3 o2 f_2@@1) (MapType0Select ExhaleHeap@@2 o2 f_2@@1)))))
 :qid |sequence.51:134|
 :skolemid |4|
 :pattern ( (MapType0Select Heap@@3 o2 f_2@@1))
)) (forall ((o2@@0 T@U) (f_2@@2 T@U) ) (! (let ((B@@4 (FieldTypeInv1 (type f_2@@2))))
(let ((A@@3 (FieldTypeInv0 (type f_2@@2))))
 (=> (and (and (= (type o2@@0) RefType) (= (type f_2@@2) (FieldType A@@3 B@@4))) (U_2_bool (MapType1Select (MapType0Select Heap@@3 null (PredicateMaskField pm_f@@0)) o2@@0 f_2@@2))) (= (MapType0Select Heap@@3 o2@@0 f_2@@2) (MapType0Select ExhaleHeap@@2 o2@@0 f_2@@2)))))
 :qid |sequence.54:23|
 :skolemid |5|
 :pattern ( (MapType0Select ExhaleHeap@@2 o2@@0 f_2@@2))
)))))
 :qid |sequence.49:19|
 :skolemid |6|
 :pattern ( (IdenticalOnKnownLocations Heap@@3 ExhaleHeap@@2 Mask@@3) (MapType0Select Heap@@3 null (PredicateMaskField pm_f@@0)) (IsPredicateField pm_f@@0))
)))
(assert (forall ((Heap@@4 T@U) (ExhaleHeap@@3 T@U) (Mask@@4 T@U) (pm_f@@1 T@U) ) (! (let ((C@@1 (FieldTypeInv0 (type pm_f@@1))))
 (=> (and (and (and (and (and (= (type Heap@@4) (MapType0Type RefType)) (= (type ExhaleHeap@@3) (MapType0Type RefType))) (= (type Mask@@4) (MapType1Type RefType realType))) (= (type pm_f@@1) (FieldType C@@1 intType))) (IdenticalOnKnownLocations Heap@@4 ExhaleHeap@@3 Mask@@4)) (and (HasDirectPerm Mask@@4 null pm_f@@1) (IsPredicateField pm_f@@1))) (and (forall ((o2@@1 T@U) (f_2@@3 T@U) ) (! (let ((B@@5 (FieldTypeInv1 (type f_2@@3))))
(let ((A@@4 (FieldTypeInv0 (type f_2@@3))))
 (=> (and (and (= (type o2@@1) RefType) (= (type f_2@@3) (FieldType A@@4 B@@5))) (U_2_bool (MapType1Select (MapType0Select Heap@@4 null (PredicateMaskField pm_f@@1)) o2@@1 f_2@@3))) (= (MapType0Select Heap@@4 o2@@1 f_2@@3) (MapType0Select ExhaleHeap@@3 o2@@1 f_2@@3)))))
 :qid |sequence.60:134|
 :skolemid |7|
 :pattern ( (MapType0Select Heap@@4 o2@@1 f_2@@3))
)) (forall ((o2@@2 T@U) (f_2@@4 T@U) ) (! (let ((B@@6 (FieldTypeInv1 (type f_2@@4))))
(let ((A@@5 (FieldTypeInv0 (type f_2@@4))))
 (=> (and (and (= (type o2@@2) RefType) (= (type f_2@@4) (FieldType A@@5 B@@6))) (U_2_bool (MapType1Select (MapType0Select Heap@@4 null (PredicateMaskField pm_f@@1)) o2@@2 f_2@@4))) (= (MapType0Select Heap@@4 o2@@2 f_2@@4) (MapType0Select ExhaleHeap@@3 o2@@2 f_2@@4)))))
 :qid |sequence.63:23|
 :skolemid |8|
 :pattern ( (MapType0Select ExhaleHeap@@3 o2@@2 f_2@@4))
)))))
 :qid |sequence.58:18|
 :skolemid |9|
 :pattern ( (IdenticalOnKnownLocations Heap@@4 ExhaleHeap@@3 Mask@@4) (MapType0Select ExhaleHeap@@3 null (PredicateMaskField pm_f@@1)) (IsPredicateField pm_f@@1))
)))
(assert (forall ((Heap@@5 T@U) (ExhaleHeap@@4 T@U) (Mask@@5 T@U) (o@@2 T@U) ) (!  (=> (and (and (and (and (and (= (type Heap@@5) (MapType0Type RefType)) (= (type ExhaleHeap@@4) (MapType0Type RefType))) (= (type Mask@@5) (MapType1Type RefType realType))) (= (type o@@2) RefType)) (IdenticalOnKnownLocations Heap@@5 ExhaleHeap@@4 Mask@@5)) (U_2_bool (MapType0Select Heap@@5 o@@2 $allocated))) (U_2_bool (MapType0Select ExhaleHeap@@4 o@@2 $allocated)))
 :qid |sequence.69:15|
 :skolemid |10|
 :pattern ( (IdenticalOnKnownLocations Heap@@5 ExhaleHeap@@4 Mask@@5) (MapType0Select Heap@@5 o@@2 $allocated))
)))
(assert (forall ((Heap@@6 T@U) (ExhaleHeap@@5 T@U) (Mask@@6 T@U) (o@@3 T@U) ) (!  (=> (and (and (and (and (and (= (type Heap@@6) (MapType0Type RefType)) (= (type ExhaleHeap@@5) (MapType0Type RefType))) (= (type Mask@@6) (MapType1Type RefType realType))) (= (type o@@3) RefType)) (IdenticalOnKnownLocations Heap@@6 ExhaleHeap@@5 Mask@@6)) (U_2_bool (MapType0Select Heap@@6 o@@3 $allocated))) (U_2_bool (MapType0Select ExhaleHeap@@5 o@@3 $allocated)))
 :qid |sequence.72:14|
 :skolemid |11|
 :pattern ( (IdenticalOnKnownLocations Heap@@6 ExhaleHeap@@5 Mask@@6) (MapType0Select ExhaleHeap@@5 o@@3 $allocated))
)))
(assert (= (type ZeroMask) (MapType1Type RefType realType)))
(assert (forall ((o_1 T@U) (f_3 T@U) ) (! (let ((B@@7 (FieldTypeInv1 (type f_3))))
(let ((A@@6 (FieldTypeInv0 (type f_3))))
 (=> (and (= (type o_1) RefType) (= (type f_3) (FieldType A@@6 B@@7))) (= (U_2_real (MapType1Select ZeroMask o_1 f_3)) 0.0))))
 :qid |sequence.85:22|
 :skolemid |12|
 :pattern ( (MapType1Select ZeroMask o_1 f_3))
)))
(assert (= (type ZeroPMask) (MapType1Type RefType boolType)))
(assert (forall ((o_1@@0 T@U) (f_3@@0 T@U) ) (! (let ((B@@8 (FieldTypeInv1 (type f_3@@0))))
(let ((A@@7 (FieldTypeInv0 (type f_3@@0))))
 (=> (and (= (type o_1@@0) RefType) (= (type f_3@@0) (FieldType A@@7 B@@8))) (not (U_2_bool (MapType1Select ZeroPMask o_1@@0 f_3@@0))))))
 :qid |sequence.91:22|
 :skolemid |13|
 :pattern ( (MapType1Select ZeroPMask o_1@@0 f_3@@0))
)))
(assert (= NoPerm 0.0))
(assert (= FullPerm 1.0))
(assert (forall ((Heap@@7 T@U) (Mask@@7 T@U) ) (!  (=> (and (and (= (type Heap@@7) (MapType0Type RefType)) (= (type Mask@@7) (MapType1Type RefType realType))) (state Heap@@7 Mask@@7)) (GoodMask Mask@@7))
 :qid |sequence.102:15|
 :skolemid |14|
 :pattern ( (state Heap@@7 Mask@@7))
)))
(assert (forall ((Mask@@8 T@U) (o_1@@1 T@U) (f_3@@1 T@U) ) (! (let ((B@@9 (FieldTypeInv1 (type f_3@@1))))
(let ((A@@8 (FieldTypeInv0 (type f_3@@1))))
 (=> (and (and (and (= (type Mask@@8) (MapType1Type RefType realType)) (= (type o_1@@1) RefType)) (= (type f_3@@1) (FieldType A@@8 B@@9))) (GoodMask Mask@@8)) (and (>= (U_2_real (MapType1Select Mask@@8 o_1@@1 f_3@@1)) 0.0) (=> (not (IsPredicateField f_3@@1)) (<= (U_2_real (MapType1Select Mask@@8 o_1@@1 f_3@@1)) 1.0))))))
 :qid |sequence.106:22|
 :skolemid |15|
 :pattern ( (GoodMask Mask@@8) (MapType1Select Mask@@8 o_1@@1 f_3@@1))
)))
(assert (forall ((Mask@@9 T@U) (o_1@@2 T@U) (f_3@@2 T@U) ) (! (let ((B@@10 (FieldTypeInv1 (type f_3@@2))))
(let ((A@@9 (FieldTypeInv0 (type f_3@@2))))
 (=> (and (and (= (type Mask@@9) (MapType1Type RefType realType)) (= (type o_1@@2) RefType)) (= (type f_3@@2) (FieldType A@@9 B@@10))) (and (=> (HasDirectPerm Mask@@9 o_1@@2 f_3@@2) (> (U_2_real (MapType1Select Mask@@9 o_1@@2 f_3@@2)) 0.0)) (=> (> (U_2_real (MapType1Select Mask@@9 o_1@@2 f_3@@2)) 0.0) (HasDirectPerm Mask@@9 o_1@@2 f_3@@2))))))
 :qid |sequence.111:22|
 :skolemid |16|
 :pattern ( (HasDirectPerm Mask@@9 o_1@@2 f_3@@2))
)))
(assert (forall ((x@@5 T@U) (p T@U) (v Int) (y@@1 T@U) (q T@U) (w Int) (z@@0 T@U) (r T@U) (u Int) ) (! (let ((C@@2 (FieldTypeInv0 (type r))))
(let ((B@@11 (FieldTypeInv0 (type q))))
(let ((A@@10 (FieldTypeInv0 (type p))))
 (=> (and (and (and (and (and (and (= (type x@@5) RefType) (= (type p) (FieldType A@@10 intType))) (= (type y@@1) RefType)) (= (type q) (FieldType B@@11 intType))) (= (type z@@0) RefType)) (= (type r) (FieldType C@@2 intType))) (and (InsidePredicate x@@5 p v y@@1 q w) (InsidePredicate y@@1 q w z@@0 r u))) (InsidePredicate x@@5 p v z@@0 r u)))))
 :qid |sequence.129:25|
 :skolemid |17|
 :pattern ( (InsidePredicate x@@5 p v y@@1 q w) (InsidePredicate y@@1 q w z@@0 r u))
)))
(assert (forall ((x@@6 T@U) (p@@0 T@U) (v@@0 Int) (y@@2 T@U) (w@@0 Int) ) (! (let ((A@@11 (FieldTypeInv0 (type p@@0))))
 (=> (and (and (and (= (type x@@6) RefType) (= (type p@@0) (FieldType A@@11 intType))) (= (type y@@2) RefType)) (InsidePredicate x@@6 p@@0 v@@0 y@@2 p@@0 w@@0)) (not (= x@@6 y@@2))))
 :qid |sequence.134:19|
 :skolemid |18|
 :pattern ( (InsidePredicate x@@6 p@@0 v@@0 y@@2 p@@0 w@@0))
)))
(assert  (and (forall ((arg0@@18 T@T) ) (! (= (Ctor (SeqType arg0@@18)) 8)
 :qid |ctor:SeqType|
)) (forall ((arg0@@19 T@T) ) (! (= (SeqTypeInv0 (SeqType arg0@@19)) arg0@@19)
 :qid |typeInv:SeqTypeInv0|
 :pattern ( (SeqType arg0@@19))
))))
(assert (forall ((s T@U) ) (! (let ((T (SeqTypeInv0 (type s))))
 (=> (= (type s) (SeqType T)) (<= 0 (|Seq#Length| s))))
 :qid |sequence.146:18|
 :skolemid |19|
 :pattern ( (|Seq#Length| s))
)))
(assert (forall ((T@@0 T@T) ) (! (= (type (|Seq#Empty| T@@0)) (SeqType T@@0))
 :qid |funType:Seq#Empty|
 :pattern ( (|Seq#Empty| T@@0))
)))
(assert (forall ((T@@1 T@T) ) (! (= (|Seq#Length| (|Seq#Empty| T@@1)) 0)
 :skolemid |20|
)))
(assert (forall ((s@@0 T@U) ) (! (let ((T@@2 (SeqTypeInv0 (type s@@0))))
 (=> (and (= (type s@@0) (SeqType T@@2)) (= (|Seq#Length| s@@0) 0)) (= s@@0 (|Seq#Empty| T@@2))))
 :qid |sequence.152:18|
 :skolemid |21|
 :pattern ( (|Seq#Length| s@@0))
)))
(assert (forall ((arg0@@20 T@U) ) (! (let ((T@@3 (type arg0@@20)))
(= (type (|Seq#Singleton| arg0@@20)) (SeqType T@@3)))
 :qid |funType:Seq#Singleton|
 :pattern ( (|Seq#Singleton| arg0@@20))
)))
(assert (forall ((t T@U) ) (! (= (|Seq#Length| (|Seq#Singleton| t)) 1)
 :qid |sequence.155:18|
 :skolemid |22|
 :pattern ( (|Seq#Length| (|Seq#Singleton| t)))
)))
(assert (forall ((arg0@@21 T@U) (arg1@@9 Int) ) (! (let ((T@@4 (SeqTypeInv0 (type arg0@@21))))
(= (type (|Seq#Index| arg0@@21 arg1@@9)) T@@4))
 :qid |funType:Seq#Index|
 :pattern ( (|Seq#Index| arg0@@21 arg1@@9))
)))
(assert (forall ((t@@0 T@U) ) (! (= (|Seq#Index| (|Seq#Singleton| t@@0) 0) t@@0)
 :qid |sequence.156:18|
 :skolemid |23|
 :pattern ( (|Seq#Singleton| t@@0))
)))
(assert (forall ((arg0@@22 T@U) (arg1@@10 T@U) ) (! (let ((T@@5 (SeqTypeInv0 (type arg0@@22))))
(= (type (|Seq#Append| arg0@@22 arg1@@10)) (SeqType T@@5)))
 :qid |funType:Seq#Append|
 :pattern ( (|Seq#Append| arg0@@22 arg1@@10))
)))
(assert (forall ((s0 T@U) (s1 T@U) ) (! (let ((T@@6 (SeqTypeInv0 (type s0))))
 (=> (and (= (type s0) (SeqType T@@6)) (= (type s1) (SeqType T@@6))) (= (|Seq#Length| (|Seq#Append| s0 s1)) (+ (|Seq#Length| s0) (|Seq#Length| s1)))))
 :qid |sequence.159:18|
 :skolemid |24|
 :pattern ( (|Seq#Length| (|Seq#Append| s0 s1)))
 :pattern ( (|Seq#Length| s0) (|Seq#Append| s0 s1))
 :pattern ( (|Seq#Length| s1) (|Seq#Append| s0 s1))
)))
(assert (forall ((s0@@0 T@U) (s1@@0 T@U) (n Int) ) (! (let ((T@@7 (SeqTypeInv0 (type s0@@0))))
 (=> (and (and (= (type s0@@0) (SeqType T@@7)) (= (type s1@@0) (SeqType T@@7))) (and (<= 0 n) (< n (|Seq#Length| s0@@0)))) (= (|Seq#Index| (|Seq#Append| s0@@0 s1@@0) n) (|Seq#Index| s0@@0 n))))
 :qid |sequence.162:18|
 :skolemid |25|
 :pattern ( (|Seq#Index| (|Seq#Append| s0@@0 s1@@0) n))
 :pattern ( (|Seq#Index| s0@@0 n) (|Seq#Append| s0@@0 s1@@0))
)))
(assert (forall ((s0@@1 T@U) (s1@@1 T@U) (n@@0 Int) ) (! (let ((T@@8 (SeqTypeInv0 (type s0@@1))))
 (=> (and (and (= (type s0@@1) (SeqType T@@8)) (= (type s1@@1) (SeqType T@@8))) (and (<= (|Seq#Length| s0@@1) n@@0) (< n@@0 (|Seq#Length| (|Seq#Append| s0@@1 s1@@1))))) (= (|Seq#Index| (|Seq#Append| s0@@1 s1@@1) n@@0) (|Seq#Index| s1@@1 (- n@@0 (|Seq#Length| s0@@1))))))
 :qid |sequence.165:18|
 :skolemid |26|
 :pattern ( (|Seq#Index| (|Seq#Append| s0@@1 s1@@1) n@@0))
)))
(assert (forall ((s0@@2 T@U) (s1@@2 T@U) (m@@7 Int) ) (! (let ((T@@9 (SeqTypeInv0 (type s0@@2))))
 (=> (and (and (= (type s0@@2) (SeqType T@@9)) (= (type s1@@2) (SeqType T@@9))) (and (<= 0 m@@7) (< m@@7 (|Seq#Length| s1@@2)))) (= (|Seq#Index| (|Seq#Append| s0@@2 s1@@2) (+ m@@7 (|Seq#Length| s0@@2))) (|Seq#Index| s1@@2 m@@7))))
 :qid |sequence.168:18|
 :skolemid |27|
 :pattern ( (|Seq#Index| s1@@2 m@@7) (|Seq#Append| s0@@2 s1@@2))
)))
(assert (forall ((arg0@@23 T@U) (arg1@@11 Int) ) (! (let ((T@@10 (SeqTypeInv0 (type arg0@@23))))
(= (type (|Seq#Take| arg0@@23 arg1@@11)) (SeqType T@@10)))
 :qid |funType:Seq#Take|
 :pattern ( (|Seq#Take| arg0@@23 arg1@@11))
)))
(assert (forall ((s@@1 T@U) (n@@1 Int) ) (! (let ((T@@11 (SeqTypeInv0 (type s@@1))))
 (=> (and (= (type s@@1) (SeqType T@@11)) (<= 0 n@@1)) (and (=> (<= n@@1 (|Seq#Length| s@@1)) (= (|Seq#Length| (|Seq#Take| s@@1 n@@1)) n@@1)) (=> (< (|Seq#Length| s@@1) n@@1) (= (|Seq#Length| (|Seq#Take| s@@1 n@@1)) (|Seq#Length| s@@1))))))
 :qid |sequence.172:18|
 :skolemid |28|
 :pattern ( (|Seq#Length| (|Seq#Take| s@@1 n@@1)))
 :pattern ( (|Seq#Length| s@@1) (|Seq#Take| s@@1 n@@1))
)))
(assert (forall ((s@@2 T@U) (n@@2 Int) (j Int) ) (! (let ((T@@12 (SeqTypeInv0 (type s@@2))))
 (=> (= (type s@@2) (SeqType T@@12)) (=> (and (and (<= 0 j) (< j n@@2)) (< j (|Seq#Length| s@@2))) (= (|Seq#Index| (|Seq#Take| s@@2 n@@2) j) (|Seq#Index| s@@2 j)))))
 :qid |sequence.177:18|
 :skolemid |29|
 :pattern ( (|Seq#Index| (|Seq#Take| s@@2 n@@2) j))
 :pattern ( (|Seq#Index| s@@2 j) (|Seq#Take| s@@2 n@@2))
)))
(assert (forall ((arg0@@24 T@U) (arg1@@12 Int) ) (! (let ((T@@13 (SeqTypeInv0 (type arg0@@24))))
(= (type (|Seq#Drop| arg0@@24 arg1@@12)) (SeqType T@@13)))
 :qid |funType:Seq#Drop|
 :pattern ( (|Seq#Drop| arg0@@24 arg1@@12))
)))
(assert (forall ((s@@3 T@U) (n@@3 Int) ) (! (let ((T@@14 (SeqTypeInv0 (type s@@3))))
 (=> (and (= (type s@@3) (SeqType T@@14)) (<= 0 n@@3)) (and (=> (<= n@@3 (|Seq#Length| s@@3)) (= (|Seq#Length| (|Seq#Drop| s@@3 n@@3)) (- (|Seq#Length| s@@3) n@@3))) (=> (< (|Seq#Length| s@@3) n@@3) (= (|Seq#Length| (|Seq#Drop| s@@3 n@@3)) 0)))))
 :qid |sequence.182:18|
 :skolemid |30|
 :pattern ( (|Seq#Length| (|Seq#Drop| s@@3 n@@3)))
 :pattern ( (|Seq#Length| s@@3) (|Seq#Drop| s@@3 n@@3))
)))
(assert (forall ((s@@4 T@U) (n@@4 Int) (j@@0 Int) ) (! (let ((T@@15 (SeqTypeInv0 (type s@@4))))
 (=> (= (type s@@4) (SeqType T@@15)) (=> (and (and (<= 0 n@@4) (<= 0 j@@0)) (< (+ j@@0 n@@4) (|Seq#Length| s@@4))) (= (|Seq#Index| (|Seq#Drop| s@@4 n@@4) j@@0) (|Seq#Index| s@@4 (+ j@@0 n@@4))))))
 :qid |sequence.187:18|
 :skolemid |31|
 :pattern ( (|Seq#Index| (|Seq#Drop| s@@4 n@@4) j@@0))
)))
(assert (forall ((s@@5 T@U) (n@@5 Int) (k Int) ) (! (let ((T@@16 (SeqTypeInv0 (type s@@5))))
 (=> (= (type s@@5) (SeqType T@@16)) (=> (and (and (<= 0 n@@5) (<= n@@5 k)) (< k (|Seq#Length| s@@5))) (= (|Seq#Index| (|Seq#Drop| s@@5 n@@5) (- k n@@5)) (|Seq#Index| s@@5 k)))))
 :qid |sequence.191:18|
 :skolemid |32|
 :pattern ( (|Seq#Drop| s@@5 n@@5) (|Seq#Index| s@@5 k))
)))
(assert (forall ((s@@6 T@U) (x@@7 T@U) ) (! (let ((T@@17 (type x@@7)))
 (=> (= (type s@@6) (SeqType T@@17)) (and (=> (|Seq#Contains| s@@6 x@@7) (>= (|Seq#Find| s@@6 x@@7) 0)) (=> (>= (|Seq#Find| s@@6 x@@7) 0) (|Seq#Contains| s@@6 x@@7)))))
 :qid |sequence.197:18|
 :skolemid |33|
 :pattern ( (|Seq#Contains| s@@6 x@@7))
 :pattern ( (|Seq#Find| s@@6 x@@7))
)))
(assert (forall ((s@@7 T@U) (x@@8 T@U) ) (! (let ((T@@18 (type x@@8)))
 (=> (= (type s@@7) (SeqType T@@18)) (and (< (|Seq#Find| s@@7 x@@8) (|Seq#Length| s@@7)) (or (= (|Seq#Find| s@@7 x@@8) (- 0 1)) (>= (|Seq#Find| s@@7 x@@8) 0)))))
 :qid |sequence.200:18|
 :skolemid |34|
 :pattern ( (|Seq#Find| s@@7 x@@8))
)))
(assert (forall ((s@@8 T@U) (x@@9 T@U) ) (! (let ((T@@19 (type x@@9)))
 (=> (and (= (type s@@8) (SeqType T@@19)) (>= (|Seq#Find| s@@8 x@@9) 0)) (= (|Seq#Index| s@@8 (|Seq#Find| s@@8 x@@9)) x@@9)))
 :qid |sequence.202:18|
 :skolemid |35|
 :pattern ( (|Seq#Find| s@@8 x@@9))
)))
(assert (forall ((s@@9 T@U) (x@@10 T@U) ) (! (let ((T@@20 (type x@@10)))
 (=> (and (= (type s@@9) (SeqType T@@20)) (= (|Seq#Find| s@@9 x@@10) (- 0 1))) (forall ((i Int) ) (!  (=> (and (<= 0 i) (< i (|Seq#Length| s@@9))) (not (= (|Seq#Index| s@@9 i) x@@10)))
 :qid |sequence.205:35|
 :skolemid |36|
 :pattern ( (|Seq#Index| s@@9 i))
))))
 :qid |sequence.204:18|
 :skolemid |37|
 :pattern ( (|Seq#Find| s@@9 x@@10))
)))
(assert (forall ((s@@10 T@U) (i@@0 Int) ) (! (let ((T@@21 (SeqTypeInv0 (type s@@10))))
 (=> (= (type s@@10) (SeqType T@@21)) (=> (and (<= 0 i@@0) (< i@@0 (|Seq#Length| s@@10))) (>= (|Seq#Find| s@@10 (|Seq#Index| s@@10 i@@0)) 0))))
 :qid |sequence.206:18|
 :skolemid |38|
 :pattern ( (|Seq#Find| s@@10 (|Seq#Index| s@@10 i@@0)))
)))
(assert (forall ((s0@@3 T@U) (s1@@3 T@U) ) (! (let ((T@@22 (SeqTypeInv0 (type s0@@3))))
 (=> (and (= (type s0@@3) (SeqType T@@22)) (= (type s1@@3) (SeqType T@@22))) (and (=> (|Seq#Equal| s0@@3 s1@@3) (and (= (|Seq#Length| s0@@3) (|Seq#Length| s1@@3)) (forall ((j@@1 Int) ) (!  (=> (and (<= 0 j@@1) (< j@@1 (|Seq#Length| s0@@3))) (= (|Seq#Index| s0@@3 j@@1) (|Seq#Index| s1@@3 j@@1)))
 :qid |sequence.232:13|
 :skolemid |39|
 :pattern ( (|Seq#Index| s0@@3 j@@1))
 :pattern ( (|Seq#Index| s1@@3 j@@1))
)))) (=> (and (= (|Seq#Length| s0@@3) (|Seq#Length| s1@@3)) (forall ((j@@2 Int) ) (!  (=> (and (<= 0 j@@2) (< j@@2 (|Seq#Length| s0@@3))) (= (|Seq#Index| s0@@3 j@@2) (|Seq#Index| s1@@3 j@@2)))
 :qid |sequence.232:13|
 :skolemid |39|
 :pattern ( (|Seq#Index| s0@@3 j@@2))
 :pattern ( (|Seq#Index| s1@@3 j@@2))
))) (|Seq#Equal| s0@@3 s1@@3)))))
 :qid |sequence.229:18|
 :skolemid |40|
 :pattern ( (|Seq#Equal| s0@@3 s1@@3))
)))
(assert (forall ((a T@U) (b T@U) ) (! (let ((T@@23 (SeqTypeInv0 (type a))))
 (=> (and (and (= (type a) (SeqType T@@23)) (= (type b) (SeqType T@@23))) (|Seq#Equal| a b)) (= a b)))
 :qid |sequence.234:18|
 :skolemid |41|
 :pattern ( (|Seq#Equal| a b))
)))
(assert (forall ((arg0@@25 Int) (arg1@@13 Int) ) (! (= (type (|Seq#Range| arg0@@25 arg1@@13)) (SeqType intType))
 :qid |funType:Seq#Range|
 :pattern ( (|Seq#Range| arg0@@25 arg1@@13))
)))
(assert (forall ((q@min Int) (q@max Int) ) (!  (and (=> (< q@min q@max) (= (|Seq#Length| (|Seq#Range| q@min q@max)) (- q@max q@min))) (=> (<= q@max q@min) (= (|Seq#Length| (|Seq#Range| q@min q@max)) 0)))
 :qid |sequence.251:15|
 :skolemid |42|
 :pattern ( (|Seq#Length| (|Seq#Range| q@min q@max)))
)))
(assert (forall ((q@min@@0 Int) (q@max@@0 Int) (j@@3 Int) ) (!  (=> (and (<= 0 j@@3) (< j@@3 (- q@max@@0 q@min@@0))) (= (U_2_int (|Seq#Index| (|Seq#Range| q@min@@0 q@max@@0) j@@3)) (+ q@min@@0 j@@3)))
 :qid |sequence.252:15|
 :skolemid |43|
 :pattern ( (|Seq#Index| (|Seq#Range| q@min@@0 q@max@@0) j@@3))
)))
(assert (forall ((q@min@@1 Int) (q@max@@1 Int) (v@@1 T@U) ) (!  (=> (= (type v@@1) intType) (and (=> (|Seq#Contains| (|Seq#Range| q@min@@1 q@max@@1) v@@1) (and (<= q@min@@1 (U_2_int v@@1)) (< (U_2_int v@@1) q@max@@1))) (=> (and (<= q@min@@1 (U_2_int v@@1)) (< (U_2_int v@@1) q@max@@1)) (|Seq#Contains| (|Seq#Range| q@min@@1 q@max@@1) v@@1))))
 :qid |sequence.254:15|
 :skolemid |44|
 :pattern ( (|Seq#Contains| (|Seq#Range| q@min@@1 q@max@@1) v@@1))
)))
(assert  (and (and (= (type Heap@@8) (MapType0Type RefType)) (= (type Mask@@10) (MapType1Type RefType realType))) (= (type a_2@0) (SeqType intType))))
(push 1)
(set-info :boogie-vc-id t2)
(assert (not
(let ((anon0_correct  (=> (! (and %lbl%+2424 true) :lblpos +2424) (=> (state Heap@@8 ZeroMask) (=> (and (and (= Heap@@8 Heap@@8) (= ZeroMask Mask@@10)) (and (= a_2@0 (|Seq#Append| (|Seq#Append| (|Seq#Append| (|Seq#Singleton| (int_2_U 0)) (|Seq#Singleton| (int_2_U 1))) (|Seq#Singleton| (int_2_U (- 0 11)))) (|Seq#Singleton| (int_2_U 22)))) (state Heap@@8 ZeroMask))) (and (! (or %lbl%@5363 (|Seq#Equal| (|Seq#Take| a_2@0 1) (|Seq#Singleton| (int_2_U 0)))) :lblneg @5363) (=> (|Seq#Equal| (|Seq#Take| a_2@0 1) (|Seq#Singleton| (int_2_U 0))) (=> (state Heap@@8 ZeroMask) (and (! (or %lbl%@5379 (|Seq#Equal| (|Seq#Drop| a_2@0 1) (|Seq#Append| (|Seq#Append| (|Seq#Singleton| (int_2_U 1)) (|Seq#Singleton| (int_2_U (- 0 11)))) (|Seq#Singleton| (int_2_U 22))))) :lblneg @5379) (=> (|Seq#Equal| (|Seq#Drop| a_2@0 1) (|Seq#Append| (|Seq#Append| (|Seq#Singleton| (int_2_U 1)) (|Seq#Singleton| (int_2_U (- 0 11)))) (|Seq#Singleton| (int_2_U 22)))) (=> (state Heap@@8 ZeroMask) (and (! (or %lbl%@5409 (|Seq#Equal| (|Seq#Append| (|Seq#Take| a_2@0 1) (|Seq#Append| (|Seq#Singleton| (int_2_U 22)) (|Seq#Drop| a_2@0 2))) (|Seq#Append| (|Seq#Take| (|Seq#Append| (|Seq#Take| a_2@0 1) (|Seq#Append| (|Seq#Singleton| (int_2_U (- 0 1))) (|Seq#Drop| a_2@0 2))) 1) (|Seq#Append| (|Seq#Singleton| (int_2_U 22)) (|Seq#Drop| (|Seq#Append| (|Seq#Take| a_2@0 1) (|Seq#Append| (|Seq#Singleton| (int_2_U (- 0 1))) (|Seq#Drop| a_2@0 2))) 2))))) :lblneg @5409) (=> (|Seq#Equal| (|Seq#Append| (|Seq#Take| a_2@0 1) (|Seq#Append| (|Seq#Singleton| (int_2_U 22)) (|Seq#Drop| a_2@0 2))) (|Seq#Append| (|Seq#Take| (|Seq#Append| (|Seq#Take| a_2@0 1) (|Seq#Append| (|Seq#Singleton| (int_2_U (- 0 1))) (|Seq#Drop| a_2@0 2))) 1) (|Seq#Append| (|Seq#Singleton| (int_2_U 22)) (|Seq#Drop| (|Seq#Append| (|Seq#Take| a_2@0 1) (|Seq#Append| (|Seq#Singleton| (int_2_U (- 0 1))) (|Seq#Drop| a_2@0 2))) 2)))) (=> (state Heap@@8 ZeroMask) (! (or %lbl%@5490 (|Seq#Equal| (|Seq#Append| (|Seq#Take| a_2@0 1) (|Seq#Append| (|Seq#Singleton| (int_2_U 22)) (|Seq#Drop| a_2@0 2))) (|Seq#Append| (|Seq#Append| (|Seq#Append| (|Seq#Singleton| (int_2_U 0)) (|Seq#Singleton| (int_2_U 22))) (|Seq#Singleton| (int_2_U (- 0 11)))) (|Seq#Singleton| (int_2_U 22))))) :lblneg @5490)))))))))))))))
(let ((PreconditionGeneratedEntry_correct  (=> (! (and %lbl%+5297 true) :lblpos +5297) anon0_correct)))
PreconditionGeneratedEntry_correct))
))
(check-sat)
(pop 1)
; Valid

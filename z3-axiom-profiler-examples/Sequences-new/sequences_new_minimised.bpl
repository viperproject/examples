// 
// Translation of SIL program.
// 
// Date:         2015-11-18 12:42:12
// Tool:         carbon 1.0
// Arguments: :  --print sequences_new.bpl ..\silver\src\test\resources\all\sequences\sequences.sil
// Dependencies:
//   Boogie , located at C:\Users\Alex\Documents\viperproject\boogie\binaries\Boogie.exe.
//   Z3 4.4.0, located at C:\Users\Alex\Documents\viperproject\z3\z3.exe.
// 

// ==================================================
// Preamble of State module.
// ==================================================

function state(Heap: HeapType, Mask: MaskType): bool;

// ==================================================
// Preamble of Heap module.
// ==================================================

type Ref;
var Heap: HeapType;
const null: Ref;
type Field A B;
type NormalField;
type HeapType = <A, B> [Ref, Field A B]B;
const unique $allocated: Field NormalField bool;
axiom (forall o: Ref, f: (Field NormalField Ref), Heap: HeapType, Mask: MaskType ::
  { state(Heap, Mask), Heap[o, f] }
  Heap[o, f] == null || Heap[Heap[o, f], $allocated]
);
function IdenticalOnKnownLocations(Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType): bool;
function IsPredicateField<A, B>(f_1: (Field A B)): bool;
// Frame all locations with direct permissions
axiom (forall <A, B> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref, f_2: (Field A B) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), Heap[o, f_2] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, o, f_2) ==> Heap[o, f_2] == ExhaleHeap[o, f_2]
) && (forall <A, B> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref, f_2: (Field A B) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o, f_2] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, o, f_2) ==> Heap[o, f_2] == ExhaleHeap[o, f_2]
);
// Frame all predicate mask locations of predicates with direct permission
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C int) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), IsPredicateField(pm_f), ExhaleHeap[null, PredicateMaskField(pm_f)] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> Heap[null, PredicateMaskField(pm_f)] == ExhaleHeap[null, PredicateMaskField(pm_f)]
);
// Frame all locations with known folded permissions
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C int) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), Heap[null, PredicateMaskField(pm_f)], IsPredicateField(pm_f) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { Heap[o2, f_2] }
    Heap[null, PredicateMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  ) && (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { ExhaleHeap[o2, f_2] }
    Heap[null, PredicateMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  )
) && (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C int) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[null, PredicateMaskField(pm_f)], IsPredicateField(pm_f) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { Heap[o2, f_2] }
    Heap[null, PredicateMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  ) && (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { ExhaleHeap[o2, f_2] }
    Heap[null, PredicateMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  )
);
// All previously-allocated references are still allocated
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), Heap[o, $allocated] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> Heap[o, $allocated] ==> ExhaleHeap[o, $allocated]
) && (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o, $allocated] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> Heap[o, $allocated] ==> ExhaleHeap[o, $allocated]
);

// ==================================================
// Preamble of Permission module.
// ==================================================

type Perm = real;
type MaskType = <A, B> [Ref, Field A B]Perm;
var Mask: MaskType;
const ZeroMask: MaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroMask[o_1, f_3] }
  ZeroMask[o_1, f_3] == 0.000000000
);
type PMaskType = <A, B> [Ref, Field A B]bool;
const ZeroPMask: PMaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroPMask[o_1, f_3] }
  !ZeroPMask[o_1, f_3]
);
function PredicateMaskField<A>(f_4: (Field A int)): Field A PMaskType;
const NoPerm: Perm;
axiom NoPerm == 0.000000000;
const FullPerm: Perm;
axiom FullPerm == 1.000000000;
function Perm(a: real, b: real): Perm;
function GoodMask(Mask: MaskType): bool;
axiom (forall Heap: HeapType, Mask: MaskType ::
  { state(Heap, Mask) }
  state(Heap, Mask) ==> GoodMask(Mask)
);
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { GoodMask(Mask), Mask[o_1, f_3] }
  GoodMask(Mask) ==> Mask[o_1, f_3] >= 0.000000000 && (!IsPredicateField(f_3) ==> Mask[o_1, f_3] <= 1.000000000)
);
function HasDirectPerm<A, B>(Mask: MaskType, o_1: Ref, f_3: (Field A B)): bool;
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { HasDirectPerm(Mask, o_1, f_3) }
  HasDirectPerm(Mask, o_1, f_3) <==> Mask[o_1, f_3] > 0.000000000
);

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

// Declarations for function framing
type FrameType;
const EmptyFrame: FrameType;
function FrameFragment<T>(t: T): FrameType;
function CombineFrames(a_1: FrameType, b_1: FrameType): FrameType;
// Function for recording enclosure of one predicate instance in another
function InsidePredicate<A, B>(x: Ref, p: (Field A int), v: int, y: Ref, q: (Field B int), w: int): bool;
const unique special_ref: Ref;
// Transitivity of InsidePredicate
axiom (forall <A, B, C> x: Ref, p: (Field A int), v: int, y: Ref, q: (Field B int), w: int, z: Ref, r: (Field C int), u: int ::
  { InsidePredicate(x, p, v, y, q, w), InsidePredicate(y, q, w, z, r, u) }
  InsidePredicate(x, p, v, y, q, w) && InsidePredicate(y, q, w, z, r, u) ==> InsidePredicate(x, p, v, z, r, u)
);
// Knowledge that two identical instances of the same predicate cannot be inside each other
axiom (forall <A> x: Ref, p: (Field A int), v: int, y: Ref, w: int ::
  { InsidePredicate(x, p, v, y, p, w) }
  InsidePredicate(x, p, v, y, p, w) ==> x != y
);

// ==================================================
// Preamble of Sequence module.
// ==================================================

type Seq T;

function Seq#Length<T>(Seq T): int;
axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Index<T>(Seq T, int): T;

function Seq#Empty<T>(): Seq T;
axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
axiom (forall<T> s: Seq T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());

function Seq#Singleton<T>(T): Seq T;
axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);
axiom (forall<T> t: T :: { Seq#Singleton(t) } Seq#Index(Seq#Singleton(t), 0) == t); // changed trigger

function Seq#Append<T>(Seq T, Seq T): Seq T;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) } {Seq#Length(s0),Seq#Append(s0,s1)} {Seq#Length(s1),Seq#Append(s0,s1)}
  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } { Seq#Index(s0, n), Seq#Append(s0,s1) }
  (0 <= n && n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)));

axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
  (Seq#Length(s0) <= n && n < Seq#Length(Seq#Append(s0,s1)) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

axiom (forall<T> s0: Seq T, s1: Seq T, m: int :: { Seq#Index(s1, m), Seq#Append(s0,s1) }
  (0 <= m && m < Seq#Length(s1) ==> Seq#Index(Seq#Append(s0,s1), m + Seq#Length(s0)) == Seq#Index(s1, m)));

function Seq#Take<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) } { Seq#Length(s), Seq#Take(s,n) }
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));

axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) }{ Seq#Index(s, j), Seq#Take(s,n) }
  0 <= j && j < n && j < Seq#Length(s) ==>
    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) } { Seq#Length(s), Seq#Drop(s,n) }
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));

axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) }
  0 <= n && 0 <= j && j+n < Seq#Length(s) ==>
    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));

axiom (forall<T> s: Seq T, n: int, k: int :: { Seq#Drop(s,n), Seq#Index(s,k) }
  0 <= n && n <= k && k < Seq#Length(s) ==>
    Seq#Index(Seq#Drop(s,n), k-n) == Seq#Index(s, k));

function Seq#Contains<T>(Seq T, T): bool;
function Seq#Find<T>(Seq T, T): int;
axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) } { Seq#Find(s,x) }
  Seq#Contains(s,x) <==>
    Seq#Find(s,x) >= 0);
axiom (forall<T> s: Seq T, x: T :: { Seq#Find(s,x) }
  Seq#Find(s,x) < Seq#Length(s) && (Seq#Find(s,x) == -1 || Seq#Find(s,x) >= 0));
axiom (forall<T> s: Seq T, x: T :: { Seq#Find(s,x) }
  Seq#Find(s,x) >= 0 ==> Seq#Index(s,Seq#Find(s,x)) == x);
axiom (forall<T> s: Seq T, x: T :: { Seq#Find(s,x) }
  Seq#Find(s,x) == -1 ==> (forall i: int :: { Seq#Index(s, i) } 0 <= i && i < Seq#Length(s) ==> Seq#Index(s, i) != x));
axiom (forall<T> s: Seq T, i: int :: { Seq#Find(s,Seq#Index(s, i)) }
  0 <= i && i < Seq#Length(s) ==> Seq#Find(s,Seq#Index(s, i)) >= 0);
// ** AS: made one change here - changed type of x from ref to T
//axiom (forall<T> x: T ::
//  { Seq#Contains(Seq#Empty(), x) }
//  !Seq#Contains(Seq#Empty(), x));
//axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
//  { Seq#Contains(Seq#Append(s0, s1), x) }
//  Seq#Contains(Seq#Append(s0, s1), x) <==>
//    Seq#Contains(s0, x) || Seq#Contains(s1, x));
//      |
//axiom (forall<T> s: Seq T, n: int, x: T ::
//  { Seq#Contains(Seq#Take(s, n), x) }
//  Seq#Contains(Seq#Take(s, n), x) <==>
//    (exists i: int :: { Seq#Index(s, i) }
//      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));
//axiom (forall<T> s: Seq T, n: int, x: T ::
//  { Seq#Contains(Seq#Drop(s, n), x) }
//  Seq#Contains(Seq#Drop(s, n), x) <==>
//    (exists i: int :: { Seq#Index(s, i) }
//      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

function Seq#Equal<T>(Seq T, Seq T): bool;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) <==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  Seq#Equal(a,b) ==> a == b);


// Additional axioms about common things
//axiom (forall<T> s: Seq T, n: int :: { Seq#Drop(s, n) } // ** NEW
//        n == 0 ==> Seq#Drop(s, n) == s);
//axiom (forall<T> s: Seq T, n: int :: { Seq#Take(s, n) } // ** NEW
//        n == 0 ==> Seq#Take(s, n) == Seq#Empty());
//
//// extra stuff not in current Dafny Prelude -- see also Drop-Index axiom above
//
//axiom (forall<T> x, y: T ::
//  { Seq#Contains(Seq#Singleton(x),y) }
//    Seq#Contains(Seq#Singleton(x),y) <==> x==y);

function Seq#Range(min: int, max: int) returns (Seq int);
axiom (forall min: int, max: int :: { Seq#Length(Seq#Range(min, max)) } (min < max ==> Seq#Length(Seq#Range(min, max)) == max-min) && (max <= min ==> Seq#Length(Seq#Range(min, max)) == 0));
axiom (forall min: int, max: int, j: int :: { Seq#Index(Seq#Range(min, max), j) } 0<=j && j<max-min ==> Seq#Index(Seq#Range(min, max), j) == min + j);

axiom (forall min: int, max: int, v: int :: {Seq#Contains(Seq#Range(min, max),v)}
  (Seq#Contains(Seq#Range(min, max),v) <==> min <= v && v < max));



// ==================================================
// Translation of method t2
// ==================================================

procedure t2() returns ()
  modifies Heap, Mask;
{
  var a_2: (Seq int);
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);


  // -- Translating statement: a := Seq(0, 1, -11, 22) -- sequences.sil,16:5
    a_2 := Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(0), Seq#Singleton(1)), Seq#Singleton(-11)), Seq#Singleton(22));
    assume state(Heap, Mask);

  // -- Translating statement: assert a[..1] == Seq(0) -- sequences.sil,19:5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[..1] == Seq(0) might not hold. (sequences.sil,19:5) [37]"}
      Seq#Equal(Seq#Take(a_2, 1), Seq#Singleton(0));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert a[1..] == Seq(1, -11, 22) -- sequences.sil,20:5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[1..] == Seq(1, -11, 22) might not hold. (sequences.sil,20:5) [38]"}
      Seq#Equal(Seq#Drop(a_2, 1), Seq#Append(Seq#Append(Seq#Singleton(1), Seq#Singleton(-11)), Seq#Singleton(22)));
    assume state(Heap, Mask);
   
  // -- Translating statement: assert a[1 := 22] == a[1 := -1][1 := 22] -- sequences.sil,23:5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[1 := 22] == a[1 := -1][1 := 22] might not hold. (sequences.sil,23:5) [40]"}
      Seq#Equal(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(22), Seq#Drop(a_2, 2))), Seq#Append(Seq#Take(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(-1), Seq#Drop(a_2, 2))), 1), Seq#Append(Seq#Singleton(22), Seq#Drop(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(-1), Seq#Drop(a_2, 2))), 2))));
    assume state(Heap, Mask);


  // -- Translating statement: assert a[1 := 22] == Seq(0, 22, -11, 22) -- sequences.sil,24:5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[1 := 22] == Seq(0, 22, -11, 22) might not hold. (sequences.sil,24:5) [41]"}
      Seq#Equal(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(22), Seq#Drop(a_2, 2))), Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(0), Seq#Singleton(22)), Seq#Singleton(-11)), Seq#Singleton(22)));
    assume state(Heap, Mask);

      
    
assume false;
}

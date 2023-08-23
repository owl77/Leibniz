Definition comp {A B C : Type}(f : A -> B) (g : B -> C) := fun (x :A) => g (f x).

Definition Unique {X : Type} (h: X -> Prop) := forall (x y : X), (h x) /\ (h y) -> x = y.

Definition ExistsUnique { X : Type } (h : X -> Prop) := (exists (u : X), h u) /\ Unique h.

Definition  Pullback {A B C D}(f1: A -> C) (f2 : B -> C)(p1 : D -> A) (p2 : D -> B) :=
(comp p1 f1 = comp p2 f2) /\  forall {E: Type} (q1 : E -> A) (q2 : E -> B),
ExistsUnique ( fun ( h: E -> D) => (comp h p1 = q1) /\ (comp h p2 = q2 )).

Definition to_unit (A : Type) := fun (x : A ) => tt.

Definition topos_true ( u : unit) := True.

Definition mon_obj { A : Type} (f : A -> Prop):= sigT ( fun  (a : A) => (f a = True)).

Definition mon {A : Type} (f : A -> Prop) := fun ( x : mon_obj f) => projT1 x.

Definition Mono (A B: Type):= sigT (fun (f: A -> B) => forall (x y : A), (f x = f y) -> x = y).

Definition Mono_arr {A B : Type} ( m : Mono A B) := projT1 m.

Definition class {X A: Type}( m : Mono X A) := fun ( a : A) => (exists ( x : X), (Mono_arr m) x = a).

(* Lemma class_com : forall {X A: Type}( m : Mono X A), (comp (Mono_arr m) (class m))
= comp (to_unit X) topos_true. 

Proof seems to need extensionality

*)

Definition pullback_obj  {A B C}(f1: A -> C) (f2 : B -> C) := sigT ( fun ( z : A * B) =>
let (a,b) := z in (f1 a = f2 b)).

Definition pullback_arr1 {A B C} (f1: A -> C) (f2 : B -> C) := fun (v : (pullback_obj f1 f2))
=> fst (projT1 v).


Definition pullback_arr2 {A B C} (f1: A -> C) (f2 : B -> C) := fun (v : (pullback_obj f1 f2))
=> snd (projT1 v).

(* Coq needs extensionality in order to have pullbacks *)

(* Conjecture : with extensionality Coq is a topos with subobject classfier Prop *)


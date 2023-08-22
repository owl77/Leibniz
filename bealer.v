
(*       * * * bealer.v  * * *

    Extensionality does not hold in Coq by default.       *)


Axiom F G : forall (A B : Type), A * B -> Prop.

Section A.

Variable X Y Z : Type.

Definition alpha ( y: Y) :=   fun ( z : Z) => (G Y Z) (y,z).

Definition beta := F X (Z -> Prop).

Definition BealerTerm ( w : X * Y ):= beta (fst w, alpha (snd w)).

End A.

Check BealerTerm.

(* BealerTerm
     : forall X Y : Type, Type -> X * Y -> Prop *)


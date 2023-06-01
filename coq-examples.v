Import Coq.Init.Nat.

Section Test.
  Check 0.
  Check nat.
  Check Set.
  Check Type.
  Variable n : nat.
  Check n.
  Check 0 < n.
  Check Prop.
  Check bool.
  Check lt.
  Check lt 0 n.
  Check ltb.
  Check ltb 0 n.
  Check 0 <? n.
  Compute 0 <? 1.
  Compute 0 < 1.
  
  Lemma zero_less_than_one : 0 < 1.
    auto.
  Qed.
  Print zero_less_than_one.
  Print le_n.

  Lemma zero_less_than_two : 0 < 2.
    auto.
  Qed.
  Print zero_less_than_two. 
  Print le_n.
End Test.

Section TestCalc.
  Definition four := S (S (S (S 0))).
  Print four.
  Check four.
  Definition double (n : nat) := plus n n.
  Compute plus four four.
  Check double.
  Print double.
  Check forall m:nat, m >= 0.
  Check exists n:nat, n > 5.
  Compute double four + double 5.
  Fixpoint fact(n:nat) : nat :=
    match n with
      | 0 => 1
      | (S p) => fact p * n
    end.
  Compute fact 5.
  Print nat.
  Print fact.
  (* Fixpoint Y(f:nat->nat):nat := f (Y f). *)
End TestCalc.

Section PropLog.
  Variable A : Prop.
  Goal A -> A.
    intro u.
    apply u.
  Save identity.
  Print identity.
  
  Variable B C : Prop.
  
  Lemma K : A -> B -> A.
    intros u v.
    apply u.
  Qed.
  
  Lemma S : (A -> B -> C) -> (A -> B) -> A -> C.
    intros; apply H; [ assumption | apply H0; assumption ].
  Qed.
  
  Print S.
  
  Lemma conj_disj : A /\ B -> A \/ B.
    intro.
    left.
    apply H.
  (*  elim H; intros.
    left.
    assumption. *)
  Qed.
  
  Hypothesis Stab : forall (A:Prop), ~~A -> A.
  
  Lemma Peirce : ((A -> B) -> A) -> A.
    intro.
    apply Stab.
    intro.
    apply H0.
    apply H.
    intro.
    exfalso.
    apply H0; apply H1.
    (* auto. *)
  Qed.
  Print Peirce.
End PropLog.

Section PredLog.
  Variable alpha : Set.
  Variable x : alpha.
  Variable p : alpha -> Prop.
  
  Lemma all_ex : (forall x, p x) -> exists x, p x.
    intro.
    exists x.
    apply H.
  Qed.
  
  Print all_ex.
  
  Hypothesis Stab : forall (A:Prop), ~~A -> A.
    
  
  Variable person : Set.
  Variable a b c : person.
  Variable drinks : person -> Prop.
  Lemma drinkers : exists a, drinks a -> forall a, drinks a.
    apply Stab; intro; apply H.
    exists b.
    intro drinks_b.
    intro.
    apply Stab; intro; apply H.
    exists a0.
    intro drinks_a.
    exfalso; auto.
  Qed.
  
  Print drinkers.
End PredLog.

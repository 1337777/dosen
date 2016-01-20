(*+    dosenSolution.v    +*)

Set Implicit Arguments.

Module Type Solution.
  
  (** * Shared outer parameter, arrowless graph. *)
  
  Delimit Scope solScope with S. 
  Open Scope solScope. 
  
  Parameter ModObjectsGen : Set.
  Hypothesis ModObjectsGen_eq_dec : forall A1 A2 : ModObjectsGen, {A1 = A2} + {A1 <> A2}.
  Parameter CoModObjectsGen : Set.
  Hypothesis CoModObjectsGen_eq_dec : forall B1 B2 : CoModObjectsGen, {B1 = B2} + {B1 <> B2}.
  
  (** * Sub for Grammatical categories *)
  
  Inductive ModObjects : Set :=
  |  ModGen0 : forall A : ModObjectsGen, ModObjects
  |  Refl0 : forall B : CoModObjects, ModObjects

  with CoModObjects : Set :=
  |  CoModGen0 : forall B : CoModObjectsGen, CoModObjects
  |  CoRefl0 : forall A : ModObjects, CoModObjects.

  Scheme ModObjects_CoModObjects_ind := Induction for ModObjects Sort Prop
                                       with CoModObjects_ModObjects_ind := Induction for CoModObjects Sort Prop.
  Scheme ModObjects_CoModObjects_rec := Induction for ModObjects Sort Set
                                       with CoModObjects_ModObjects_rec := Induction for CoModObjects Sort Set.
  Combined Scheme ModObjects_CoModObjects_mutind from ModObjects_CoModObjects_ind, CoModObjects_ModObjects_ind.
  Definition ModObjects_CoModObjects_mutrec P P0 f f0 f1 f2 := 
    pair (ModObjects_CoModObjects_rec P P0 f f0 f1 f2)
         (CoModObjects_ModObjects_rec P P0 f f0 f1 f2).

  Notation "#0 A" := (ModGen0 A) (at level 4, right associativity) : solScope.
  Notation "'#0 B" := (CoModGen0 B) (at level 4, right associativity) : solScope.
  Notation "F|0 B" := (Refl0 B) (at level 4, right associativity) : solScope.
  Notation "G|0 A" := (CoRefl0 A) (at level 4, right associativity) : solScope.

  Ltac tac_ext_eq_dec base_dec :=
    edestruct (base_dec); [left; f_equal; eassumption | right; injection; eassumption].

  Definition ModObjects_CoModObjects_eq_dec : (forall A1 A2 : ModObjects, {A1 = A2} + {A1 <> A2}) *
                                              (forall B1 B2 : CoModObjects, {B1 = B2} + {B1 <> B2}).
  Proof.
    generalize (ModObjectsGen_eq_dec) (CoModObjectsGen_eq_dec); intros;
    apply ModObjects_CoModObjects_mutrec;
    destruct A2 || destruct B2;
    solve [
        (right;discriminate) |
        match goal with
          |  [H : forall _, forall _, { _ } + { _ } |- _] => tac_ext_eq_dec H
          |  [H : forall _, { _ } + { _ } |- _] => tac_ext_eq_dec H
        end ].
  Defined.

  Reserved Notation "A1 ⊢a A2" (at level 30).
  Reserved Notation "B1 ⊢b B2" (at level 30).

  Inductive ModArrows : ModObjects -> ModObjects -> Set :=
  | ModIden : forall {A}, A ⊢a A
  | Refl1 : forall B1 B2 (g_ : B1 ⊢b B2), F|0 B1 ⊢a F|0 B2
  | CoUnit : forall A1 A2, A1 ⊢a A2 -> F|0 G|0 A1 ⊢a A2
  | ModCom : forall UACom A3, UACom ⊢a A3 -> forall A1, A1 ⊢a UACom -> A1 ⊢a A3

  with CoModArrows : CoModObjects -> CoModObjects -> Set :=
  | CoModIden : forall {B}, B ⊢b B
  | CoRefl1 : forall A1 A2 (f_ : A1 ⊢a A2), G|0 A1 ⊢b G|0 A2
  | Unit : forall B1 B2, B1 ⊢b B2 -> B1 ⊢b G|0 F|0 B2
  | CoModCom : forall UBCom B3, UBCom ⊢b B3 -> forall B1, B1 ⊢b UBCom -> B1 ⊢b B3

  where "A1 ⊢a A2" := (ModArrows A1 A2) : solScope
                                           and "B1 ⊢b B2" := (CoModArrows B1 B2) : solScope.

  Notation "1" := (@ModIden _) (at level 0) : solScope.
  Notation "'1" := (@CoModIden _) (at level 0) : solScope.
  Notation "F| g" := (Refl1 g) (at level 5, right associativity) : solScope.
  Notation "G| f" := (CoRefl1 f) (at level 5, right associativity) : solScope.
  Notation "φ| f" := (CoUnit f) (at level 5, right associativity) : solScope.
  Notation "γ| g" := (Unit g) (at level 5, right associativity) : solScope.
  Notation "f2 <a f1" := (ModCom f2 f1) (at level 24, right associativity) : solScope.
  Notation "g2 <b g1" := (CoModCom g2 g1) (at level 24, right associativity) : solScope.

  Print Grammar pattern.
  Check G| F| '1 <b γ| G| φ| F| G| @ModIden F|0 '#0 _.

  Scheme ModArrows_CoModArrows_ind := Induction for ModArrows Sort Prop
                                     with CoModArrows_ModArrows_ind := Induction for CoModArrows Sort Prop.
  Scheme ModArrows_CoModArrows_rec := Induction for ModArrows Sort Set
                                     with CoModArrows_ModArrows_rec := Induction for CoModArrows Sort Set.
  Combined Scheme ModArrows_CoModArrows_mutind from ModArrows_CoModArrows_ind, CoModArrows_ModArrows_ind.
  Definition ModArrows_CoModArrows_mutrec P P0 f f0 f1 f2 f3 f4 f5 f6 := 
    pair (ModArrows_CoModArrows_rec P P0 f f0 f1 f2 f3 f4 f5 f6)
         (CoModArrows_ModArrows_rec P P0 f f0 f1 f2 f3 f4 f5 f6).

  Reserved Notation "A1 ⊢as A2" (at level 30).
  Reserved Notation "B1 ⊢bs B2" (at level 30).

  Inductive ModArrowsSol : ModObjects -> ModObjects -> Set :=
  | ModIdenSol : forall {A}, A ⊢as A
  | Refl1Sol : forall B1 B2 (g_ : B1 ⊢bs B2), F|0 B1 ⊢as F|0 B2
  | CoUnitSol : forall A1 A2, A1 ⊢as A2 -> F|0 G|0 A1 ⊢as A2

  with CoModArrowsSol : CoModObjects -> CoModObjects -> Set :=
  | CoModIdenSol : forall {B}, B ⊢bs B
  | CoRefl1Sol : forall A1 A2 (f_ : A1 ⊢as A2), G|0 A1 ⊢bs G|0 A2
  | UnitSol : forall B1 B2, B1 ⊢bs B2 -> B1 ⊢bs G|0 F|0 B2

  where "A1 ⊢as A2" := (ModArrowsSol A1 A2) : solScope
                                               and "B1 ⊢bs B2" := (CoModArrowsSol B1 B2) : solScope.

  Notation "$1" := (@ModIdenSol _) (at level 0) : solScope.
  Notation "'$1" := (@CoModIdenSol _) (at level 0) : solScope.
  Notation "Fs| g" := (Refl1Sol g) (at level 5, right associativity) : solScope.
  Notation "Gs| f" := (CoRefl1Sol f) (at level 5, right associativity) : solScope.
  Notation "φs| f" := (CoUnitSol f) (at level 5, right associativity) : solScope.
  Notation "γs| g" := (UnitSol g) (at level 5, right associativity) : solScope.
  
  Check  γs| Gs| φs| Fs| Gs| @ModIdenSol F|0 '#0 _.
  Check Gs| Fs| '$1.
  Check Fs| Gs| $1.
  
  Scheme ModArrowsSol_CoModArrowsSol_ind := Induction for ModArrowsSol Sort Prop
                                           with CoModArrowsSol_ModArrowsSol_ind := Induction for CoModArrowsSol Sort Prop.
  Scheme ModArrowsSol_CoModArrowsSol_rec := Induction for ModArrowsSol Sort Set
                                           with CoModArrowsSol_ModArrowsSol_rec := Induction for CoModArrowsSol Sort Set.
  Combined Scheme ModArrowsSol_CoModArrowsSol_mutind from ModArrowsSol_CoModArrowsSol_ind, CoModArrowsSol_ModArrowsSol_ind.
  Definition ModArrowsSol_CoModArrowsSol_mutrec P P0 f f0 f1 f2 f3 f4 := 
    pair (ModArrowsSol_CoModArrowsSol_rec P P0 f f0 f1 f2 f3 f4)
         (CoModArrowsSol_ModArrowsSol_rec P P0 f f0 f1 f2 f3 f4).

  (** None two conclusions of the first 3 constructors are unifiable, .. except for Com constructor. *)
  
  Definition sol_mut : (forall A1 A2, A1 ⊢as A2 -> A1 ⊢a A2) * (forall B1 B2, B1 ⊢bs B2 -> B1 ⊢b B2).
  Proof.
    apply ModArrowsSol_CoModArrowsSol_mutrec.
    - constructor 1.
    - constructor 2; assumption.
    - constructor 3; assumption.
    - constructor 1.
    - constructor 2; assumption.
    - constructor 3; assumption.
  Defined.

  Definition solMod : (forall A1 A2, A1 ⊢as A2 -> A1 ⊢a A2).
  Proof.
    apply sol_mut.
  Defined.

  Definition solCoMod : (forall B1 B2, B1 ⊢bs B2 -> B1 ⊢b B2).
  Proof.
    apply sol_mut.
  Defined.

  (** These rewrite lemmas solve some (bug) problems of [simpl] or [cbn] not progressing well.
 Are there alternative solutions? *)

  Definition rew_solMod_1 :  forall A, solMod (@ModIdenSol A) = 1.
  Proof.
    reflexivity.
  Qed.

  Definition rew_solMod_F :  forall B1 B2 (g : B1 ⊢bs B2), solMod (Fs| g) = F| (solCoMod g).
  Proof.
    reflexivity.
  Qed.

  Definition rew_solMod_φ :  forall A1 A2 (f : A1 ⊢as A2), solMod (φs| f) = φ| (solMod f).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite rew_solMod_1 rew_solMod_F rew_solMod_φ.

  Definition rew_solCoMod_1 :  forall B, solCoMod (@CoModIdenSol B) = '1.
  Proof.
    reflexivity.
  Qed.

  Definition rew_solCoMod_G :  forall A1 A2 (f : A1 ⊢as A2), solCoMod (Gs| f) = G| (solMod f).
  Proof.
    reflexivity.
  Qed.

  Definition rew_solCoMod_γ :  forall B1 B2 (g : B1 ⊢bs B2), solCoMod (γs| g) = γ| (solCoMod g).
  Proof.
    reflexivity.
  Qed.
  
  Hint Rewrite rew_solCoMod_1 rew_solCoMod_G rew_solCoMod_γ.

  (** ** Dependent destruction on arrows.
   * Copy and change from [Derive Dependent Inversion ModArrowsSol_inv with (forall A1 A2, ModArrowsSol A1 A2) Sort Set.].
   * Keep these transport transparent. **)
  
  Definition transportModSol  : forall A1 A2 A1' (pfA1 : A1' = A1) A2' (pfA2 : A2' = A2), A1 ⊢as A2 -> A1' ⊢as A2'.
  Proof.
    intros * <- * <-.
    exact (fun f => f).
  Defined.

  Eval compute in fun A1 A2 => transportModSol eq_refl eq_refl .

  Definition transportMod  : forall A1 A2 A1' (pfA1 : A1' = A1) A2' (pfA2 : A2' = A2), A1 ⊢a A2 -> A1' ⊢a A2'.
  Proof.
    intros * <- * <-.
    exact (fun f => f).
  Defined.

  Definition transportCoModSol  : forall B1 B2 B1' (pfB1 : B1' = B1) B2' (pfB2 : B2' = B2), B1 ⊢bs B2 -> B1' ⊢bs B2'.
  Proof.
    intros * <- * <-.
    exact (fun g => g).
  Defined.

  Definition transportCoMod  : forall B1 B2 B1' (pfB1 : B1' = B1) B2' (pfB2 : B2' = B2), B1 ⊢b B2 -> B1' ⊢b B2'.
  Proof.
    intros * <- * <-.
    exact (fun g => g).
  Defined.
  
  Definition ModArrowsSol_destruct : forall (A1 A2 : ModObjects)
                                       (P :  A1 ⊢as A2 -> Set),
                                       (forall A'  (pfA1 : A1 = A') (pfA2 : A2 = A'), P  (transportModSol pfA1 pfA2 (@ModIdenSol A'))) ->
                                       (forall B1'  B2' (g : B1' ⊢bs B2') (pfA1 : A1 = F|0 B1') (pfA2 : A2 = F|0 B2'), P  (transportModSol pfA1 pfA2 (Fs| g))) ->
                                       (forall A1'  A2' (f : A1' ⊢as A2') (pfA1 : A1 = F|0 G|0 A1') (pfA2 : A2 = A2'), P  (transportModSol pfA1 pfA2 (φs| f))) ->
                                       forall (f : A1 ⊢as A2), P f.
  Proof.
    destruct f as [A | ? ? g | ? ? f].
    - specialize (H _ eq_refl eq_refl); apply H.
    - specialize (H0 _ _ g eq_refl eq_refl); apply H0.
    - specialize (H1 _ _ f eq_refl eq_refl); apply H1.
  Defined.
  
  Definition ModArrows_destruct : forall (A1 A2 : ModObjects)
                                    (P :  A1 ⊢a A2 -> Set),
                                    (forall A'  (pfA1 : A1 = A') (pfA2 : A2 = A'), P  (transportMod pfA1 pfA2 (@ModIden A'))) ->
                                    (forall B1'  B2' (g : B1' ⊢b B2') (pfA1 : A1 = F|0 B1') (pfA2 : A2 = F|0 B2'), P  (transportMod pfA1 pfA2 (F| g))) ->
                                    (forall A1'  A2' (f : A1' ⊢a A2') (pfA1 : A1 = F|0 G|0 A1') (pfA2 : A2 = A2'), P  (transportMod pfA1 pfA2 (φ| f))) ->
                                    (forall A2'  A3' (f2 : A2' ⊢a A3') A1' (f1 : A1' ⊢a A2') (pfA1 : A1 = A1') (pfA2 : A2 = A3'), P  (transportMod pfA1 pfA2 (f2 <a f1))) ->
                                    forall (f : A1 ⊢a A2), P f.
  Proof.
    destruct f as [A | ? ? g | ? ? f | ? ? f2 ? f1].
    - specialize (H _ eq_refl eq_refl); apply H.
    - specialize (H0 _ _ g eq_refl eq_refl); apply H0.
    - specialize (H1 _ _ f eq_refl eq_refl); apply H1.
    - specialize (H2 _ _ f2 _ f1 eq_refl eq_refl); apply H2.
  Defined.

  Definition CoModArrowsSol_destruct : forall (B1 B2 : CoModObjects)
                                         (P :  B1 ⊢bs B2 -> Set),
                                         (forall B'  (pfB1 : B1 = B') (pfB2 : B2 = B'), P  (transportCoModSol pfB1 pfB2 (@CoModIdenSol B'))) ->
                                         (forall A1'  A2' (f : A1' ⊢as A2') (pfB1 : B1 = G|0 A1') (pfB2 : B2 = G|0 A2'), P  (transportCoModSol pfB1 pfB2 (Gs| f))) ->
                                         (forall B1'  B2' (g : B1' ⊢bs B2') (pfB1 : B1 = B1') (pfB2 : B2 = G|0 F|0 B2'), P  (transportCoModSol pfB1 pfB2 (γs| g))) ->
                                         forall (g : B1 ⊢bs B2), P g.
  Proof.
    destruct g as [B | ? ? f | ? ? g].
    - specialize (H _ eq_refl eq_refl); apply H.
    - specialize (H0 _ _ f eq_refl eq_refl); apply H0.
    - specialize (H1 _ _ g eq_refl eq_refl); apply H1.
  Defined.
  
  Definition CoModArrows_destruct : forall (B1 B2 : CoModObjects)
                                      (P :  B1 ⊢b B2 -> Set),
                                      (forall B'  (pfB1 : B1 = B') (pfB2 : B2 = B'), P  (transportCoMod pfB1 pfB2 (@CoModIden B'))) ->
                                      (forall A1'  A2' (f : A1' ⊢a A2') (pfB1 : B1 = G|0 A1') (pfB2 : B2 = G|0 A2'), P  (transportCoMod pfB1 pfB2 (G| f))) ->
                                      (forall B1'  B2' (g : B1' ⊢b B2') (pfB1 : B1 = B1') (pfB2 : B2 = G|0 F|0 B2'), P  (transportCoMod pfB1 pfB2 (γ| g))) ->
                                      (forall B2'  B3' (g2 : B2' ⊢b B3') B1' (g1 : B1' ⊢b B2') (pfB1 : B1 = B1') (pfB2 : B2 = B3'), P  (transportCoMod pfB1 pfB2 (g2 <b g1))) ->
                                      forall (g : B1 ⊢b B2), P g.
  Proof.
    destruct g as [B | ? ? f | ? ? g | ? ? g2 ? g1].
    - specialize (H _ eq_refl eq_refl); apply H.
    - specialize (H0 _ _ f eq_refl eq_refl); apply H0.
    - specialize (H1 _ _ g eq_refl eq_refl); apply H1.
    - specialize (H2 _ _ g2 _ g1 eq_refl eq_refl); apply H2.
  Defined.

  (** ** Objects have decidable equalities
   * Therefore transport along the same object is identity,
   * and second projection of some dependent pairs sharing the same object index is possible.**)

  Require Import Eqdep_dec.

  Lemma ModObjects_CoModObjects_UIP : (forall (A : ModObjects) (pfA : A = A), pfA = eq_refl) /\ (forall (B : CoModObjects) (pfB : B = B), pfB = eq_refl) .
  Proof.
    apply ModObjects_CoModObjects_mutind;
    intros; apply UIP_dec; apply ModObjects_CoModObjects_eq_dec.
  Qed.

  Lemma ModObjects_UIP : (forall (A : ModObjects) (pfA : A = A), pfA = eq_refl).
  Proof.
    apply ModObjects_CoModObjects_UIP.
  Qed.

  Lemma CoModObjects_UIP : (forall (B : CoModObjects) (pfB : B = B), pfB = eq_refl) .
  Proof.
    apply ModObjects_CoModObjects_UIP.
  Qed.

  Definition ModObjects_eq_dep : forall (P : ModObjects -> Set) (A : ModObjects) (x y : P A), existT P A x = existT P A y -> x = y. 
  Proof.
    intros; apply inj_pair2_eq_dec; [|assumption];
    apply ModObjects_CoModObjects_eq_dec.
  Qed.

  Definition CoModObjects_eq_dep : forall (P : CoModObjects -> Set) (B : CoModObjects) (x y : P B), existT P B x = existT P B y -> x = y.
  Proof.
    intros; apply inj_pair2_eq_dec; [|assumption];
    apply ModObjects_CoModObjects_eq_dec.
  Qed.

  Hint Extern 4 => repeat (match goal with
                            | H : existT _ (_ : ModObjects) _ = existT _ _  _ |- _ => apply ModObjects_eq_dep in H
                            | H : existT _ (_ : CoModObjects) _ = existT _ _  _ |- _ => apply CoModObjects_eq_dep in H
                          end); try subst.

  (** ** Tactics for dependent destruction of arrows. **)
  
  Ltac tac_ModArrowsSol_dep_destruct E :=
    let x := fresh "f_Sol_" in
    let x_eq := fresh "Heq_f_Sol_" in
    remember E as x eqn:x_eq in |- ; simpl in x;
    revert x_eq; pattern x; apply ModArrowsSol_destruct; clear x;
    [ intros A_ |
      intros B1_ B2_ g_ |
      intros A1_ A2_ f_ ];
    intros pfA1 pfA2 x_eq;
    rewrite <- x_eq in *;
    simplify_eq pfA1; intros; try subst;
    try simplify_eq pfA2; intros; try subst;
    try rewrite ?(ModObjects_UIP pfA1) in *; try clear pfA1;
    try rewrite ?(ModObjects_UIP pfA2) in *; try clear pfA2;
    simpl in *.

  Ltac tac_CoModArrowsSol_dep_destruct E :=
    let x := fresh "g_Sol_" in
    let x_eq := fresh "Heq_g_Sol_" in
    remember E as x eqn:x_eq in |- ; simpl in x;
    revert x_eq; pattern x; apply CoModArrowsSol_destruct; clear x;
    [ intros B_ |
      intros A1_ A2_ f_ |
      intros B1_ B2_ g_ ];
    intros pfB1 pfB2 x_eq;
    rewrite <- x_eq in *;
    simplify_eq pfB1; intros; try subst;
    try simplify_eq pfB2; intros; try subst;
    try rewrite ?(CoModObjects_UIP pfB1) in *; try clear pfB1;
    try rewrite ?(CoModObjects_UIP pfB2) in *; try clear pfB2;
    simpl in*.

  Ltac tac_ModArrows_dep_destruct E :=
    let x := fresh "f_Deg_" in
    let x_eq := fresh "Heq_f_Deg_" in
    remember E as x eqn:x_eq in |- ; simpl in x;
    revert x_eq; pattern x; apply ModArrows_destruct; clear x;
    [ intros A_ |
      intros B1_ B2_ g_ |
      intros A1_ A2_ f_ |
      intros A2_ A3_ f2_ A1_ f1_ ];
    intros pfA1 pfA2 x_eq;
    rewrite <- x_eq in *;
    simplify_eq pfA1; intros; try subst;
    try simplify_eq pfA2; intros; try subst;
    try rewrite ?(ModObjects_UIP pfA1) in *; try clear pfA1;
    try rewrite ?(ModObjects_UIP pfA2) in *; try clear pfA2;
    simpl in *.

  Ltac tac_CoModArrows_dep_destruct E :=
    let x := fresh "g_Deg_" in
    let x_eq := fresh "Heq_g_Deg_" in
    remember E as x eqn:x_eq in |- ; simpl in x;
    revert x_eq; pattern x; apply CoModArrows_destruct; clear x;
    [ intros B_ |
      intros A1_ A2_ f_ |
      intros B1_ B2_ g_ |
      intros B2_ B3_ g2_ B1_ g1_ ];
    intros pfB1 pfB2 x_eq;
    rewrite <- x_eq in *;
    simplify_eq pfB1; intros; try subst;
    try simplify_eq pfB2; intros; try subst;
    try rewrite ?(CoModObjects_UIP pfB1) in *; try clear pfB1;
    try rewrite ?(CoModObjects_UIP pfB2) in *; try clear pfB2;
    simpl in*.

  (** * Quotient for Grammatical categories **)
  
  Reserved Notation "f2 ≈a f1" (at level 70).
  Reserved Notation "g2 ≈b g1" (at level 70).

  Inductive convMod : forall A1 A2 : ModObjects, A1 ⊢a A2 -> A1 ⊢a A2 -> Prop := 
  |  ModCongCom : forall A2 A3, forall (f2 f2' : A2 ⊢a A3), f2 ≈a f2' -> forall A1, forall (f1 f1' : A1 ⊢a A2), f1 ≈a f1' -> f2 <a f1 ≈a f2' <a f1'
  |  ModCongRefl1 : forall B1 B2, forall (g g' : B1 ⊢b B2), g ≈b g' -> F| g ≈a F| g'
  |  ModCongCoUnit : forall A1 A2, forall (f f' : A1 ⊢a A2), f ≈a f' -> φ| f ≈a φ| f'
  |  ModRefl : forall A1 A2 (f : A1 ⊢a A2), f ≈a f
  |  ModTrans : forall A1 A2, forall (uModTrans f : A1 ⊢a A2), uModTrans ≈a f -> forall (f' : A1 ⊢a A2), f' ≈a uModTrans -> f' ≈a f
  |  ModSym : forall A1 A2,  forall (f' f : A1 ⊢a A2), f ≈a f' -> f' ≈a f
  |  ModCat1Right : forall A1 A2, forall f : A1 ⊢a A2,  f ≈a f <a 1
  |  ModCat1Left : forall A1 A2, forall f : A1 ⊢a A2,  f ≈a 1 <a f
  |  ModCat2 : forall A3 A4 (f3 : A3 ⊢a A4), forall A2 (f2 : A2 ⊢a A3), forall A1 (f1 : A1 ⊢a A2),
                 (f3 <a f2) <a f1 ≈a f3 <a (f2 <a f1)
  |  ModFun1Refl : forall B, 1 ≈a F| (@CoModIden B)
  |  ModFun2Refl : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                     F| (g2 <b g1) ≈a F| g2 <a F| g1
  | ModNatCoUnit1 : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                      φ| (f2 <a f1) ≈a f2 <a φ| f1
  | ModNatCoUnit2 : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                      φ| (f2 <a f1) ≈a φ| f2 <a F| G| f1
  | ModRectangle : forall  B1 B2 (g : B1 ⊢b B2) A2 (f : F|0 B2 ⊢a A2),
                     f <a F| g ≈a φ| f <a F| γ| g 

  with convCoMod : forall B1 B2 : CoModObjects, B1 ⊢b B2 -> B1 ⊢b B2 -> Prop :=
  |  CoModCongCom : forall B2 B3, forall (g2 g2' : B2 ⊢b B3), g2 ≈b g2' -> forall B1, forall (g1 g1' : B1 ⊢b B2), g1 ≈b g1' -> g2 <b g1 ≈b g2' <b g1'
  |  CoModCongRefl1 : forall A1 A2, forall (f f' : A1 ⊢a A2), f ≈a f' -> G| f ≈b G| f'
  |  CoModCongCoUnit : forall B1 B2, forall (g g' : B1 ⊢b B2), g ≈b g' -> γ| g ≈b γ| g'
  |  CoModRefl : forall B1 B2 (g : B1 ⊢b B2), g ≈b g
  |  CoModTrans : forall B1 B2, forall (uCoModTrans g : B1 ⊢b B2), uCoModTrans ≈b g -> forall (g' : B1 ⊢b B2), g' ≈b uCoModTrans -> g' ≈b g
  |  CoModSym : forall B1 B2,  forall (g' g : B1 ⊢b B2), g ≈b g' -> g' ≈b g
  |  CoModCat1Right : forall B1 B2, forall g : B1 ⊢b B2,  g ≈b g <b '1
  |  CoModCat1Left : forall B1 B2, forall g : B1 ⊢b B2,  g ≈b '1 <b g
  |  CoModCat2 : forall B3 B4 (g3 : B3 ⊢b B4), forall B2 (g2 : B2 ⊢b B3), forall B1 (g1 : B1 ⊢b B2),
                   (g3 <b g2) <b g1 ≈b g3 <b (g2 <b g1)
  |  CoModFun1Refl : forall A, '1 ≈b G| (@ModIden A)
  |  CoModFun2Refl : forall A2 A3 (g2 : A2 ⊢a A3) A1 (g1 : A1 ⊢a A2),
                       G| (g2 <a g1) ≈b G| g2 <b G| g1
  | CoModNatCoUnit1 : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                        γ| (g2 <b g1) ≈b  γ| g2 <b g1
  | CoModNatCoUnit2 : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                        γ| (g2 <b g1) ≈b  G| F| g2 <b γ| g1
  | CoModRectangle : forall  A1 A2 (f : A1 ⊢a A2) B1 (g : B1 ⊢b G|0 A1),
                       G| f <b g ≈b G| φ| f <b γ| g 

  where "f2 ≈a f1" := (convMod f2 f1) : solScope
                                         and "g2 ≈b g1" := (convCoMod g2 g1) : solScope.

  Hint Constructors convMod convCoMod.

  Definition grade : (forall A1 A2 (f : A1 ⊢a A2), nat) * (forall B1 B2 (g : B1 ⊢b B2), nat).
  Proof.
    apply ModArrows_CoModArrows_mutrec.
    - intros; exact (S O).
    - intros; refine (S _); assumption.
    - intros; refine (S _); assumption.
    - intros * ? grade_f2 * ? grade_f1; refine (S (grade_f2 + grade_f1)).
    - intros; exact (S O).
    - intros; refine (S _); assumption.
    - intros; refine (S _); assumption.
    - intros * ? grade_g2 * ? grade_g1; refine (S (grade_g2 + grade_g1)).
  Defined.

  Definition gradeMod : (forall A1 A2 (f : A1 ⊢a A2), nat).
  Proof.
    apply grade.
  Defined.

  Definition gradeCoMod :  (forall B1 B2 (g : B1 ⊢b B2), nat).
  Proof.
    apply grade.
  Defined.

  (** These rewrite lemmas solve some (bug) problems of [simpl] or [cbn] not progressing well.
 Are there alternative solutions? *)
  
  Definition rew_gradeMod_1 :  forall A, gradeMod (@ModIden A) = S O.
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeMod_F :  forall B1 B2 (g : B1 ⊢b B2), gradeMod (F| g) = S(gradeCoMod g).
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeMod_φ :  forall A1 A2 (f : A1 ⊢a A2), gradeMod (φ| f) = S(gradeMod f).
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeMod_Com :  forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2), gradeMod (f2 <a f1) = S(gradeMod f2 + gradeMod f1).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite rew_gradeMod_1 rew_gradeMod_F rew_gradeMod_φ rew_gradeMod_Com.

  Definition rew_gradeCoMod_1 :  forall B, gradeCoMod (@CoModIden B) = S O.
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeCoMod_G :  forall A1 A2 (f : A1 ⊢a A2), gradeCoMod (G| f) = S(gradeMod f).
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeCoMod_φ :  forall B1 B2 (g : B1 ⊢b B2), gradeCoMod (γ| g) = S(gradeCoMod g).
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeCoMod_Com :  forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2), gradeCoMod (g2 <b g1) = S(gradeCoMod g2 + gradeCoMod g1).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite rew_gradeCoMod_1 rew_gradeCoMod_G rew_gradeCoMod_φ rew_gradeCoMod_Com.

  Definition gradeCom : (forall A1 A2 (f : A1 ⊢a A2), nat) * (forall B1 B2 (g : B1 ⊢b B2), nat).
  Proof.
    apply ModArrows_CoModArrows_mutrec.
    - intros; exact (O).
    - intros; refine ( _); assumption.
    - intros; refine ( _); assumption.
    - intros * f2 gradeCom_f2 * f1 gradeCom_f1; refine (gradeCom_f2 + (gradeCom_f1 + gradeMod (f2 <a f1))).
    - intros; exact (O).
    - intros; refine ( _); assumption.
    - intros; refine ( _); assumption.
    - intros * g2 gradeCom_g2 * g1 gradeCom_g1; refine (gradeCom_g2 + (gradeCom_g1 + gradeCoMod (g2 <b g1))).
  Defined.

  Definition gradeComMod : (forall A1 A2 (f : A1 ⊢a A2), nat).
  Proof.
    apply gradeCom.
  Defined.

  Definition gradeComCoMod :  (forall B1 B2 (g : B1 ⊢b B2), nat).
  Proof.
    apply gradeCom.
  Defined.

  Definition rew_gradeComMod_1 :  forall A, gradeComMod (@ModIden A) = O.
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeComMod_F :  forall B1 B2 (g : B1 ⊢b B2), gradeComMod (F| g) = (gradeComCoMod g).
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeComMod_φ :  forall A1 A2 (f : A1 ⊢a A2), gradeComMod (φ| f) = (gradeComMod f).
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeComMod_Com :  forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2), gradeComMod (f2 <a f1) = (gradeComMod f2 + (gradeComMod f1 + gradeMod (f2 <a f1))).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite rew_gradeComMod_1 rew_gradeComMod_F rew_gradeComMod_φ rew_gradeComMod_Com.

  Definition rew_gradeComCoMod_1 :  forall B, gradeComCoMod (@CoModIden B) = O.
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeComCoMod_G :  forall A1 A2 (f : A1 ⊢a A2), gradeComCoMod (G| f) = (gradeComMod f).
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeComCoMod_φ :  forall B1 B2 (g : B1 ⊢b B2), gradeComCoMod (γ| g) = (gradeComCoMod g).
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeComCoMod_Com :  forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2), gradeComCoMod (g2 <b g1) = (gradeComCoMod g2 + (gradeComCoMod g1 + gradeCoMod (g2 <b g1))).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite rew_gradeComCoMod_1 rew_gradeComCoMod_G rew_gradeComCoMod_φ rew_gradeComCoMod_Com.

  Definition gradeTotalMod : (forall A1 A2 (f : A1 ⊢a A2), nat).
  Proof.
    intros; refine (gradeMod f + gradeComMod f).
  Defined.

  Definition gradeTotalCoMod :  (forall B1 B2 (g : B1 ⊢b B2), nat).
  Proof.
    intros; refine (gradeCoMod g + gradeComCoMod g).
  Defined.

  Definition rew_gradeTotalMod :  forall A1 A2 (f : A1 ⊢a A2), gradeTotalMod f = (gradeMod f + gradeComMod f).
  Proof.
    reflexivity.
  Qed.

  Definition rew_gradeTotalCoMod :  forall B1 B2 (g : B1 ⊢b B2), gradeTotalCoMod g = (gradeCoMod g + gradeComCoMod g).
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite rew_gradeTotalMod rew_gradeTotalCoMod.
  Hint Unfold gradeTotalMod gradeTotalCoMod.
  Hint Extern 4 => unfold gradeTotalMod, gradeTotalCoMod in *.

  (** * Reduction relation **)
  
  Reserved Notation "f2 ↜a f1" (at level 70).
  Reserved Notation "g2 ↜b g1" (at level 70).

  Inductive reduceMod : forall A1 A2 : ModObjects, A1 ⊢a A2 -> A1 ⊢a A2 -> Prop := 
  | RedModCongComL : forall A2 A3, forall (f2 f2' : A2 ⊢a A3), f2 ↜a f2' -> forall A1, forall (f1 : A1 ⊢a A2), f2 <a f1 ↜a f2' <a f1
  | RedModCongComR : forall A2 A3, forall (f2 : A2 ⊢a A3), forall A1, forall (f1 f1' : A1 ⊢a A2), f1 ↜a f1' -> f2 <a f1 ↜a f2 <a f1'
  | RedModCongRefl1 : forall B1 B2, forall (g g' : B1 ⊢b B2), g ↜b g' -> F| g ↜a F| g'
  | RedModCongCoUnit : forall A1 A2, forall (f f' : A1 ⊢a A2), f ↜a f' -> φ| f ↜a φ| f'
  | RedModTrans : forall A1 A2, forall (uModTrans f : A1 ⊢a A2), uModTrans ↜a f -> forall (f' : A1 ⊢a A2), f' ↜a uModTrans -> f' ↜a f
  | RedModCat1Right : forall A1 A2, forall f : A1 ⊢a A2,  f ↜a f <a 1
  | RedModCat1Left : forall A1 A2, forall f : A1 ⊢a A2,  f ↜a 1 <a f
  | RedModFun1Refl : forall B, 1 ↜a F| (@CoModIden B)
  | RedModFun2Refl : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                       F| (g2 <b g1) ↜a F| g2 <a F| g1
  | RedModNatCoUnit1 : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                         φ| (f2 <a f1) ↜a f2 <a φ| f1
  | RedModNatCoUnit2 : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                         φ| (f2 <a f1) ↜a φ| f2 <a F| G| f1
  | RedModRectangle : forall  B1 B2 (g : B1 ⊢b B2) A2 (f : F|0 B2 ⊢a A2),
                        f <a F| g ↜a φ| f <a F| γ| g 

  with reduceCoMod : forall B1 B2 : CoModObjects, B1 ⊢b B2 -> B1 ⊢b B2 -> Prop :=
  | RedCoModCongComL : forall B2 B3, forall (g2 g2' : B2 ⊢b B3), g2 ↜b g2' -> forall B1, forall (g1 : B1 ⊢b B2), g2 <b g1 ↜b g2' <b g1
  | RedCoModCongComR : forall B2 B3, forall (g2 : B2 ⊢b B3), forall B1, forall (g1 g1' : B1 ⊢b B2), g1 ↜b g1' -> g2 <b g1 ↜b g2 <b g1'
  | RedCoModCongRefl1 : forall A1 A2, forall (f f' : A1 ⊢a A2), f ↜a f' -> G| f ↜b G| f'
  | RedCoModCongCoUnit : forall B1 B2, forall (g g' : B1 ⊢b B2), g ↜b g' -> γ| g ↜b γ| g'
  | RedCoModTrans : forall B1 B2, forall (uCoModTrans g : B1 ⊢b B2), uCoModTrans ↜b g -> forall (g' : B1 ⊢b B2), g' ↜b uCoModTrans -> g' ↜b g
  | RedCoModCat1Right : forall B1 B2, forall g : B1 ⊢b B2,  g ↜b g <b '1
  | RedCoModCat1Left : forall B1 B2, forall g : B1 ⊢b B2,  g ↜b '1 <b g
  | RedCoModFun1Refl : forall A, '1 ↜b G| (@ModIden A)
  | RedCoModFun2Refl : forall A2 A3 (g2 : A2 ⊢a A3) A1 (g1 : A1 ⊢a A2),
                         G| (g2 <a g1) ↜b G| g2 <b G| g1
  | RedCoModNatCoUnit1 : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                           γ| (g2 <b g1) ↜b  γ| g2 <b g1
  | RedCoModNatCoUnit2 : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                           γ| (g2 <b g1) ↜b  G| F| g2 <b γ| g1
  | RedCoModRectangle : forall  A1 A2 (f : A1 ⊢a A2) B1 (g : B1 ⊢b G|0 A1),
                          G| f <b g ↜b G| φ| f <b γ| g 

  where "f2 ↜a f1" := (reduceMod f2 f1) : solScope
                                           and "g2 ↜b g1" := (reduceCoMod g2 g1) : solScope.

  Hint Constructors reduceMod reduceCoMod.

  Scheme reduceMod_reduceCoMod_ind := Induction for reduceMod Sort Prop
                                     with reduceCoMod_reduceMod_ind := Induction for reduceCoMod Sort Prop .
  Combined Scheme reduceMod_reduceCoMod_mutind from reduceMod_reduceCoMod_ind, reduceCoMod_reduceMod_ind.

  Lemma reduceMod_convMod_reduceCoMod_convCoMod : (forall A1 A2 (fDeg f: A1 ⊢a A2), fDeg ↜a f -> fDeg ≈a f)
                                                  /\ (forall B1 B2 (gDeg g: B1 ⊢b B2), gDeg ↜b g -> gDeg ≈b g).
  Proof.
    apply reduceMod_reduceCoMod_mutind;
    eauto.
  Qed.

  Lemma reduceMod_convMod : (forall A1 A2 (fDeg f: A1 ⊢a A2), fDeg ↜a f -> fDeg ≈a f).
  Proof.
    apply reduceMod_convMod_reduceCoMod_convCoMod.
  Qed.

  Lemma reduceCoMod_convCoMod : (forall B1 B2 (gDeg g: B1 ⊢b B2), gDeg ↜b g -> gDeg ≈b g).
  Proof.
    apply reduceMod_convMod_reduceCoMod_convCoMod.
  Qed.
  
  (** ** Reduction relation is well-founded**)

  (** Seriouz biz start hehe **)
  Require Import CpdtTactics.

  Lemma degrade : (forall A1 A2 (fDeg f: A1 ⊢a A2), fDeg ↜a f -> gradeMod fDeg <= gradeMod f /\ gradeTotalMod fDeg < gradeTotalMod f)
                  /\ (forall B1 B2 (gDeg g: B1 ⊢b B2), gDeg ↜b g -> gradeCoMod gDeg <= gradeCoMod g /\ gradeTotalCoMod gDeg < gradeTotalCoMod g).
  Proof.
    apply reduceMod_reduceCoMod_mutind;
    intros; rewriter; crush.
  Qed.

  Lemma degradeMod : (forall A1 A2 (fDeg f: A1 ⊢a A2), fDeg ↜a f -> gradeMod fDeg <= gradeMod f).
  Proof.
    apply degrade.
  Qed.

  Lemma degradeCoMod : (forall B1 B2 (gDeg g: B1 ⊢b B2), gDeg ↜b g -> gradeCoMod gDeg <= gradeCoMod g).
  Proof.
    apply degrade.
  Qed.

  Hint Resolve degradeMod degradeCoMod.

  Lemma degradeTotalMod : (forall A1 A2 (fDeg f: A1 ⊢a A2), fDeg ↜a f -> gradeTotalMod fDeg < gradeTotalMod f).
  Proof.
    apply degrade.
  Qed.

  Lemma degradeTotalCoMod : (forall B1 B2 (gDeg g: B1 ⊢b B2), gDeg ↜b g -> gradeTotalCoMod gDeg < gradeTotalCoMod g).
  Proof.
    apply degrade.
  Qed.

  Hint Resolve degradeTotalMod degradeTotalCoMod.

  Lemma degradeMod_degradeCoMod_ge_one : (forall A1 A2 (f: A1 ⊢a A2), (S O) <= gradeMod f) /\ (forall B1 B2 (g: B1 ⊢b B2), (S O) <= gradeCoMod g).
  Proof.
    apply ModArrows_CoModArrows_mutind; crush.
  Qed.

  Lemma degradeMod_ge_one : (forall A1 A2 (f: A1 ⊢a A2), (S O) <= gradeMod f).
  Proof.
    apply degradeMod_degradeCoMod_ge_one.
  Qed.

  Lemma degradeCoMod_ge_one : (forall B1 B2 (g: B1 ⊢b B2), (S O) <= gradeCoMod g).
  Proof.
    apply degradeMod_degradeCoMod_ge_one.
  Qed.

  Hint Resolve degradeMod_ge_one degradeCoMod_ge_one.

  (** * Termination *)

  Fixpoint solveMod len {struct len} : forall A1 A2 (f : A1 ⊢a A2) (H_gradeTotalMod : gradeTotalMod f <= len),
                                         { fSol : A1 ⊢as A2 | solMod fSol ↜a f \/ solMod fSol = f }
  with solveCoMod len {struct len} : forall B1 B2 (g : B1 ⊢b B2) (H_gradeTotalCoMod : gradeTotalCoMod g <= len),
                                       { gSol : B1 ⊢bs B2 | solCoMod gSol ↜b g \/ solCoMod gSol = g }.
  Proof.
    (* solveMod *)
    { destruct len.
      (* n is O *)
      - clear; intros until 1; exfalso; generalize (degradeMod_ge_one f); crush.

        (* n is (S n) *)
      - intros; destruct f as [A | B1 B2 g | A1 A2 f | A2 A3 f2 A1 f1].

        (* f is 1 *)
        + exists ($1) .
          right; reflexivity.

        (* f is F| g *)
        + generalize (solveCoMod len _ _ g); intros (gSol, gSol_prop). 
          * clear -H_gradeTotalMod; crush.
          * exists (Fs| gSol) .
            clear -gSol_prop; crush.
            
        (* f is φ| f *)
        + generalize (solveMod len _ _ f); intros (fSol, fSol_prop).
          * clear -H_gradeTotalMod; crush.
          * exists (φs| fSol) .
            clear -fSol_prop; crush.

        (* f is (f2 <a f1) *)
        + generalize (solveMod len _ _ f1); intros (f1Sol, f1Sol_prop);
          [ clear -H_gradeTotalMod; crush | ].
          generalize (solveMod len _ _ f2); intros (f2Sol, f2Sol_prop);
          [ clear -H_gradeTotalMod; crush | ].
          destruct f1Sol as [A1 | B1 B2 g1 | A1_ A2 f1'].

          (*  (f2Sol <a 1) , instance of (f2Sol <a f1Sol) , from (f2 <a f1) , instance of f *)
          * exists (f2Sol) .
            clear -f1Sol_prop f2Sol_prop.
            left; intuition (rewriter; eauto).
            
          (*  (f2Sol <a F| g1) , instance of (f2Sol <a f1Sol) , from (f2 <a f1) , instance of f *)
          * { tac_ModArrowsSol_dep_destruct f2Sol;
              try rename A_ into A3;
              try rename B1_ into B2,  B2_ into B3,  g_ into g2;
              try rename A1_ into A2, A2_ into A3, f_ into f2'.

              (*  (1 <a F| g1) , instance of (f2Sol <a F| g1) , instance of (f2Sol <a f1Sol) , from (f2 <a f1) , instance of f *)
              - exists (Fs| g1) .
                clear -f1Sol_prop f2Sol_prop.
                left; intuition (rewriter; eauto).

              (*  (F| g2 <a F| g1) , instance of (f2Sol <a F| g1) , instance of (f2Sol <a f1Sol) , from (f2 <a f1) , instance of f *)
              - generalize (solveCoMod len _ _ (solCoMod g2 <b solCoMod g1)); intros (g2_o_g1_Sol, g2_o_g1_Sol_prop).
                + destruct f1Sol_prop as [f1Sol_prop|f1Sol_prop], f2Sol_prop as [f2Sol_prop|f2Sol_prop];
                  try subst;
                  try (generalize (degradeMod f1Sol_prop); generalize (degradeTotalMod f1Sol_prop));
                  try (generalize (degradeMod f2Sol_prop); generalize (degradeTotalMod f2Sol_prop));
                  clear -H_gradeTotalMod;
                  rewriter; Omega.omega.
                +exists (Fs| (g2_o_g1_Sol)) .
                 clear - f1Sol_prop f2Sol_prop g2_o_g1_Sol_prop.
                 left; intuition (rewriter; eauto;
                                  eapply RedModTrans with (uModTrans := F| (solCoMod g2 <b solCoMod g1)); eauto).
                 
              (*  (φ| f2' <a F| g1) , instance of (f2Sol <a F| g1) , instance of (f2Sol <a f1Sol) , from (f2 <a f1) , instance of f *)
              - tac_CoModArrowsSol_dep_destruct g1;
                try rename B_ into B1;
                try rename A1_ into A1, A2_ into A2, f_ into f1';
                try rename B1_ into B1, B2_ into B2, g_ into g1'.
                
                (*  (φ| f2' <a F| '1) , instance of (f2Sol <a F| g1) , instance of (f2Sol <a f1Sol) , from (f2 <a f1) , instance of f *)
                + exists (φs| f2') . 
                  clear - f1Sol_prop f2Sol_prop.
                  (* explicit eapply not necessary here *)
                  left; intuition (rewriter; eauto;
                                   eapply RedModTrans with (uModTrans := (φ| (solMod f2') <a 1)); eauto).
                  
                (*  (φ| f2' <a F| G| f1') , instance of (f2Sol <a F| g1) , instance of (f2Sol <a f1Sol) , from (f2 <a f1) , instance of f *)
                + generalize (solveMod len _ _ (solMod f2' <a solMod f1')); intros (f2'_o_f1'_Sol, f2'_o_f1'_Sol_prop).
                  * destruct f1Sol_prop as [f1Sol_prop|f1Sol_prop], f2Sol_prop as [f2Sol_prop|f2Sol_prop];
                    try subst;
                    try (generalize (degradeMod f1Sol_prop); generalize (degradeTotalMod f1Sol_prop));
                    try (generalize (degradeMod f2Sol_prop); generalize (degradeTotalMod f2Sol_prop));
                    clear -H_gradeTotalMod;
                    rewriter; Omega.omega.
                  * exists (φs| (f2'_o_f1'_Sol)) .
                    clear - f1Sol_prop f2Sol_prop f2'_o_f1'_Sol_prop.
                    left; intuition (rewriter; eauto;
                                     eapply RedModTrans with (uModTrans := φ| (solMod f2' <a solMod f1')); eauto). 
                    
                (*  (φ| f2' <a F| γ| g1') , instance of (f2Sol <a F| g1) , instance of (f2Sol <a f1Sol) , from (f2 <a f1) , instance of f *)
                + generalize (solveMod len _ _ (solMod f2' <a F| (solCoMod g1'))); intros (f2'_o_F_g1'_Sol, f2'_o_F_g1'_Sol_prop).
                  * destruct f1Sol_prop as [f1Sol_prop|f1Sol_prop], f2Sol_prop as [f2Sol_prop|f2Sol_prop];
                    try subst;
                    try (generalize (degradeMod f1Sol_prop); generalize (degradeTotalMod f1Sol_prop));
                    try (generalize (degradeMod f2Sol_prop); generalize (degradeTotalMod f2Sol_prop));
                    clear -H_gradeTotalMod;
                    rewriter; Omega.omega.
                  * exists (f2'_o_F_g1'_Sol) .
                    clear - f1Sol_prop f2Sol_prop f2'_o_F_g1'_Sol_prop.
                    left; intuition (rewriter; eauto;
                                     eapply RedModTrans with (uModTrans := (solMod f2' <a F| (solCoMod g1'))); eauto). 
            }
            
          (*  (f2Sol <a φ| f1') , instance of (f2Sol <a f1Sol) , from (f2 <a f1) , instance of f *)
          * { generalize (solveMod len _ _ (solMod f2Sol <a solMod f1')); intros (f2_o_f1'_Sol, f2_o_f1'_Sol_prop).
              - destruct f1Sol_prop as [f1Sol_prop|f1Sol_prop], f2Sol_prop as [f2Sol_prop|f2Sol_prop];
                try subst;
                try (generalize (degradeMod f1Sol_prop); generalize (degradeTotalMod f1Sol_prop));
                try (generalize (degradeMod f2Sol_prop); generalize (degradeTotalMod f2Sol_prop));
                clear -H_gradeTotalMod;
                rewriter; Omega.omega.
              - exists (φs| (f2_o_f1'_Sol)) .
                clear - f1Sol_prop f2Sol_prop f2_o_f1'_Sol_prop.
                left; intuition (rewriter; eauto;
                                 eapply RedModTrans with (uModTrans := (φ| (solMod f2Sol <a solMod f1'))); eauto). 
            }
    }
    
    (* solveCoMod *)
    { destruct len.
      (* n is O *)
      - clear; intros until 1; exfalso; generalize (degradeCoMod_ge_one g); crush.

        (* n is (S n) *)
      - intros; destruct g as [B | A1 A2 f | B1 B2 g | B2 B3 g2 B1 g1].

        (* g is '1 *)
        + exists ('$1) .
          right; reflexivity.

        (* g is G| f *)
        + generalize (solveMod len _ _ f); intros (fSol, fSol_prop). 
          * clear -H_gradeTotalCoMod; crush.
          * exists (Gs| fSol) .
            clear -fSol_prop; crush.
            
        (* g is γ| g *)
        + generalize (solveCoMod len _ _ g); intros (gSol, gSol_prop).
          * clear -H_gradeTotalCoMod; crush.
          * exists (γs| gSol) .
            clear -gSol_prop; crush.

        (* g is (g2 <b g1) *)
        + generalize (solveCoMod len _ _ g1); intros (g1Sol, g1Sol_prop);
          [ clear -H_gradeTotalCoMod; crush | ].
          generalize (solveCoMod len _ _ g2); intros (g2Sol, g2Sol_prop);
          [ clear -H_gradeTotalCoMod; crush | ].
          destruct g2Sol as [B3 | A2 A3 f2 | B2_ B3 g2'].

          (*  ('1 <b g1Sol) , instance of (g2Sol <b g1Sol) , from (g2 <b g1) , instance of g *)
          * exists (g1Sol) .
            clear -g2Sol_prop g1Sol_prop.
            left; intuition (rewriter; eauto).
            
          (*  (G| f2 <b g1Sol) , instance of (g2Sol <b g1Sol) , from (g2 <b g1) , instance of g *)
          * { tac_CoModArrowsSol_dep_destruct g1Sol;
              try rename B_ into B1;
              try rename A1_ into A1,  A2_ into A2,  f_ into f1;
              try rename B1_ into B1, B2_ into B2, g_ into g1'.

              (*  (G| f2 <b '1) , instance of (g2Sol <b G| f1) , instance of (g2Sol <b g1Sol) , from (g2 <b g1) , instance of g *)
              - exists (Gs| f2) .
                clear -g2Sol_prop g1Sol_prop.
                left; intuition (rewriter; eauto).

              (*  (G| f2 <b G| f1) , instance of (g2Sol <b G| f1) , instance of (g2Sol <b g1Sol) , from (g2 <b g1) , instance of g *)
              - generalize (solveMod len _ _ (solMod f2 <a solMod f1)); intros (f2_o_f1_Sol, f2_o_f1_Sol_prop).
                + destruct g2Sol_prop as [g2Sol_prop|g2Sol_prop], g1Sol_prop as [g1Sol_prop|g1Sol_prop];
                  try subst;
                  try (generalize (degradeCoMod g2Sol_prop); generalize (degradeTotalCoMod g2Sol_prop));
                  try (generalize (degradeCoMod g1Sol_prop); generalize (degradeTotalCoMod g1Sol_prop));
                  clear -H_gradeTotalCoMod;
                  rewriter; Omega.omega.
                +exists (Gs| (f2_o_f1_Sol)) .
                 clear - g2Sol_prop g1Sol_prop f2_o_f1_Sol_prop.
                 left; intuition (rewriter; eauto;
                                  eapply RedCoModTrans with (uCoModTrans := G| (solMod f2 <a solMod f1)); eauto).
                 
              (*  (G| f2 <b γ| g1') , instance of (g2Sol <b G| f1) , instance of (g2Sol <b g1Sol) , from (g2 <b g1) , instance of g *)
              - tac_ModArrowsSol_dep_destruct f2;
                try rename A_ into A2;
                try rename B1_ into B2, B2_ into B3, g_ into g2';
                try rename A1_ into A2, A2_ into A3, f_ into f2'.
                
                (*  (G| 1 <b γ| g1') , instance of (g2Sol <b G| f1) , instance of (g2Sol <b g1Sol) , from (g2 <b g1) , instance of g *)
                + exists (γs| g1') . 
                  clear - g2Sol_prop g1Sol_prop.
                  (* explicit eapply not necessary here *)
                  left; intuition (rewriter; eauto;
                                   eapply RedCoModTrans with (uCoModTrans := (γ| '1 <b (solCoMod g1'))); eauto).
                  
                (*  (G| F| g2' <b γ| g1') , instance of (g2Sol <b G| f1) , instance of (g2Sol <b g1Sol) , from (g2 <b g1) , instance of g *)
                + generalize (solveCoMod len _ _ (solCoMod g2' <b solCoMod g1')); intros (g2'_o_g1'_Sol, g2'_o_g1'_Sol_prop).
                  * destruct g2Sol_prop as [g2Sol_prop|g2Sol_prop], g1Sol_prop as [g1Sol_prop|g1Sol_prop];
                    try subst;
                    try (generalize (degradeCoMod g2Sol_prop); generalize (degradeTotalCoMod g2Sol_prop));
                    try (generalize (degradeCoMod g1Sol_prop); generalize (degradeTotalCoMod g1Sol_prop));
                    clear -H_gradeTotalCoMod;
                    rewriter; Omega.omega.
                  * exists (γs| (g2'_o_g1'_Sol)) .
                    clear - g2Sol_prop g1Sol_prop g2'_o_g1'_Sol_prop.
                    left; intuition (rewriter; eauto;
                                     eapply RedCoModTrans with (uCoModTrans := γ| (solCoMod g2' <b solCoMod g1')); eauto). 
                    
                (*  (G| φ| f2' <b γ| g1') , instance of (g2Sol <b G| f1) , instance of (g2Sol <b g1Sol) , from (g2 <b g1) , instance of g *)
                + generalize (solveCoMod len _ _ (G| (solMod f2') <b solCoMod g1')); intros (G_f2'_o_g1'_Sol, G_f2'_o_g1'_Sol_prop).
                  * destruct g2Sol_prop as [g2Sol_prop|g2Sol_prop], g1Sol_prop as [g1Sol_prop|g1Sol_prop];
                    try subst;
                    try (generalize (degradeCoMod g2Sol_prop); generalize (degradeTotalCoMod g2Sol_prop));
                    try (generalize (degradeCoMod g1Sol_prop); generalize (degradeTotalCoMod g1Sol_prop));
                    clear -H_gradeTotalCoMod;
                    rewriter; Omega.omega.
                  * exists (G_f2'_o_g1'_Sol) .
                    clear - g2Sol_prop g1Sol_prop G_f2'_o_g1'_Sol_prop.
                    left; intuition (rewriter; eauto;
                                     eapply RedCoModTrans with (uCoModTrans := (G| (solMod f2') <b solCoMod g1')); eauto). 
            }
            
          (*  (γ| g2' <b g1Sol) , instance of (g2Sol <b g1Sol) , from (g2 <b g1) , instance of g *)
          * { generalize (solveCoMod len _ _ (solCoMod g2' <b solCoMod g1Sol)); intros (g2_o_g1'_Sol, g2_o_g1'_Sol_prop).
              - destruct g2Sol_prop as [g2Sol_prop|g2Sol_prop], g1Sol_prop as [g1Sol_prop|g1Sol_prop];
                try subst;
                try (generalize (degradeCoMod g2Sol_prop); generalize (degradeTotalCoMod g2Sol_prop));
                try (generalize (degradeCoMod g1Sol_prop); generalize (degradeTotalCoMod g1Sol_prop));
                clear -H_gradeTotalCoMod;
                rewriter; Omega.omega.
              - exists (γs| (g2_o_g1'_Sol)) .
                clear - g2Sol_prop g1Sol_prop g2_o_g1'_Sol_prop.
                left; intuition (rewriter; eauto;
                                 eapply RedCoModTrans with (uCoModTrans := (γ| (solCoMod g2' <b solCoMod g1Sol))); eauto). 
            }
    }
  Defined.

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

  Inductive ModArrows : ModObjects -> ModObjects -> Type :=
  | ModIden : forall {A}, A ⊢a A
  | Refl1 : forall B1 B2 (g_ : B1 ⊢b B2), F|0 B1 ⊢a F|0 B2
  | CoUnit : forall A1 A2, A1 ⊢a A2 -> F|0 G|0 A1 ⊢a A2
  | ModCom : forall UACom A3, UACom ⊢a A3 -> forall A1, A1 ⊢a UACom -> A1 ⊢a A3

  with CoModArrows : CoModObjects -> CoModObjects -> Type :=
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
  Scheme ModArrows_CoModArrows_rec := Induction for ModArrows Sort Type
                                     with CoModArrows_ModArrows_rec := Induction for CoModArrows Sort Type.
  Combined Scheme ModArrows_CoModArrows_mutind from ModArrows_CoModArrows_ind, CoModArrows_ModArrows_ind.
  Definition ModArrows_CoModArrows_mutrec P P0 f f0 f1 f2 f3 f4 f5 f6 := 
    pair (ModArrows_CoModArrows_rec P P0 f f0 f1 f2 f3 f4 f5 f6)
         (CoModArrows_ModArrows_rec P P0 f f0 f1 f2 f3 f4 f5 f6).

  Reserved Notation "A1 ⊢as A2" (at level 30).
  Reserved Notation "B1 ⊢bs B2" (at level 30).

  Inductive ModArrowsSol : ModObjects -> ModObjects -> Type :=
  | ModIdenSol : forall {A}, A ⊢as A
  | Refl1Sol : forall B1 B2 (g_ : B1 ⊢bs B2), F|0 B1 ⊢as F|0 B2
  | CoUnitSol : forall A1 A2, A1 ⊢as A2 -> F|0 G|0 A1 ⊢as A2

  with CoModArrowsSol : CoModObjects -> CoModObjects -> Type :=
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
  Scheme ModArrowsSol_CoModArrowsSol_rec := Induction for ModArrowsSol Sort Type
                                           with CoModArrowsSol_ModArrowsSol_rec := Induction for CoModArrowsSol Sort Type.
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
   * Copy and change from [Derive Dependent Inversion ModArrowsSol_inv with (forall A1 A2, ModArrowsSol A1 A2) Sort Type.].
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
                                       (P :  A1 ⊢as A2 -> Type),
                                       (forall A'  (pfA1 : A1 = A') (pfA2 : A2 = A'), P  (transportModSol pfA1 pfA2 (@ModIdenSol A'))) ->
                                       (forall B1'  B2' (g : B1' ⊢bs B2') (pfA1 : A1 = F|0 B1') (pfA2 : A2 = F|0 B2'), P  (transportModSol pfA1 pfA2 (Fs| g))) ->
                                       (forall A1'  A2' (f : A1' ⊢as A2') (pfA1 : A1 = F|0 G|0 A1') (pfA2 : A2 = A2'), P  (transportModSol pfA1 pfA2 (φs| f))) ->
                                       forall (f : A1 ⊢as A2), P f.
  Proof.
    destruct f as [A | ? ? g | ? ? f].
    - specialize (X _ eq_refl eq_refl); apply X.
    - specialize (X0 _ _ g eq_refl eq_refl); apply X0.
    - specialize (X1 _ _ f eq_refl eq_refl); apply X1.
  Defined.
  
  Definition ModArrows_destruct : forall (A1 A2 : ModObjects)
                                    (P :  A1 ⊢a A2 -> Type),
                                    (forall A'  (pfA1 : A1 = A') (pfA2 : A2 = A'), P  (transportMod pfA1 pfA2 (@ModIden A'))) ->
                                    (forall B1'  B2' (g : B1' ⊢b B2') (pfA1 : A1 = F|0 B1') (pfA2 : A2 = F|0 B2'), P  (transportMod pfA1 pfA2 (F| g))) ->
                                    (forall A1'  A2' (f : A1' ⊢a A2') (pfA1 : A1 = F|0 G|0 A1') (pfA2 : A2 = A2'), P  (transportMod pfA1 pfA2 (φ| f))) ->
                                    (forall A2'  A3' (f2 : A2' ⊢a A3') A1' (f1 : A1' ⊢a A2') (pfA1 : A1 = A1') (pfA2 : A2 = A3'), P  (transportMod pfA1 pfA2 (f2 <a f1))) ->
                                    forall (f : A1 ⊢a A2), P f.
  Proof.
    destruct f as [A | ? ? g | ? ? f | ? ? f2 ? f1].
    - specialize (X _ eq_refl eq_refl); apply X.
    - specialize (X0 _ _ g eq_refl eq_refl); apply X0.
    - specialize (X1 _ _ f eq_refl eq_refl); apply X1.
    - specialize (X2 _ _ f2 _ f1 eq_refl eq_refl); apply X2.
  Defined.

  Definition CoModArrowsSol_destruct : forall (B1 B2 : CoModObjects)
                                         (P :  B1 ⊢bs B2 -> Type),
                                         (forall B'  (pfB1 : B1 = B') (pfB2 : B2 = B'), P  (transportCoModSol pfB1 pfB2 (@CoModIdenSol B'))) ->
                                         (forall A1'  A2' (f : A1' ⊢as A2') (pfB1 : B1 = G|0 A1') (pfB2 : B2 = G|0 A2'), P  (transportCoModSol pfB1 pfB2 (Gs| f))) ->
                                         (forall B1'  B2' (g : B1' ⊢bs B2') (pfB1 : B1 = B1') (pfB2 : B2 = G|0 F|0 B2'), P  (transportCoModSol pfB1 pfB2 (γs| g))) ->
                                         forall (g : B1 ⊢bs B2), P g.
  Proof.
    destruct g as [B | ? ? f | ? ? g].
    - specialize (X _ eq_refl eq_refl); apply X.
    - specialize (X0 _ _ f eq_refl eq_refl); apply X0.
    - specialize (X1 _ _ g eq_refl eq_refl); apply X1.
  Defined.
  
  Definition CoModArrows_destruct : forall (B1 B2 : CoModObjects)
                                      (P :  B1 ⊢b B2 -> Type),
                                      (forall B'  (pfB1 : B1 = B') (pfB2 : B2 = B'), P  (transportCoMod pfB1 pfB2 (@CoModIden B'))) ->
                                      (forall A1'  A2' (f : A1' ⊢a A2') (pfB1 : B1 = G|0 A1') (pfB2 : B2 = G|0 A2'), P  (transportCoMod pfB1 pfB2 (G| f))) ->
                                      (forall B1'  B2' (g : B1' ⊢b B2') (pfB1 : B1 = B1') (pfB2 : B2 = G|0 F|0 B2'), P  (transportCoMod pfB1 pfB2 (γ| g))) ->
                                      (forall B2'  B3' (g2 : B2' ⊢b B3') B1' (g1 : B1' ⊢b B2') (pfB1 : B1 = B1') (pfB2 : B2 = B3'), P  (transportCoMod pfB1 pfB2 (g2 <b g1))) ->
                                      forall (g : B1 ⊢b B2), P g.
  Proof.
    destruct g as [B | ? ? f | ? ? g | ? ? g2 ? g1].
    - specialize (X _ eq_refl eq_refl); apply X.
    - specialize (X0 _ _ f eq_refl eq_refl); apply X0.
    - specialize (X1 _ _ g eq_refl eq_refl); apply X1.
    - specialize (X2 _ _ g2 _ g1 eq_refl eq_refl); apply X2.
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
    simpl transportModSol in * .

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
    simpl transportCoModSol in * .

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
    simpl transportMod in * .

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
    simpl transportCoMod in * .

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

  (** * Congruent Resolution **)
  
  Module Type CongruentResolution.
    
    (** ** Nodes where self is some Com **)
    
    Inductive nodesMod : forall A1 A2, A1 ⊢a A2 -> Type :=
  | selfMod : forall {A2 A3} {f2 : A2 ⊢a A3} {A1} {f1 : A1 ⊢a A2}, nodesMod (f2 <a f1)
  | bottomF : forall B1 B2 (g : B1 ⊢b B2), nodesCoMod g -> nodesMod (F| g)
  | bottomφ : forall A1 A2 (f : A1 ⊢a A2), nodesMod f -> nodesMod (φ| f)
  | leftComMod : forall {A1 A2} {f1 : A1 ⊢a A2},  forall A3 (f2 : A2 ⊢a A3), nodesMod f2 -> nodesMod (f2 <a f1)
  | rightComMod : forall A1 A2 (f1 : A1 ⊢a A2), nodesMod f1 -> forall {A3} {f2 : A2 ⊢a A3}, nodesMod (f2 <a f1)

    with nodesCoMod : forall B1 B2, B1 ⊢b B2 -> Type :=
    | selfCoMod : forall {B2 B3} {g2 : B2 ⊢b B3} {B1} {g1 : B1 ⊢b B2}, nodesCoMod (g2 <b g1)
    | bottomG : forall A1 A2 (f : A1 ⊢a A2), nodesMod f -> nodesCoMod (G| f)
    | bottomγ : forall B1 B2 (g : B1 ⊢b B2), nodesCoMod g -> nodesCoMod (γ| g)
    | leftComCoMod : forall {B1 B2} {g1 : B1 ⊢b B2},  forall B3 (g2 : B2 ⊢b B3), nodesCoMod g2 -> nodesCoMod (g2 <b g1)
    | rightComCoMod : forall B1 B2 (g1 : B1 ⊢b B2), nodesCoMod g1 -> forall {B3} {g2 : B2 ⊢b B3}, nodesCoMod (g2 <b g1).

    Hint Constructors nodesMod nodesCoMod.

    Scheme nodesMod_nodesCoMod_ind := Induction for nodesMod Sort Prop
                                      with nodesCoMod_nodesMod_ind := Induction for nodesCoMod Sort Prop .
    Scheme nodesMod_nodesCoMod_rec := Induction for nodesMod Sort Type
                                      with nodesCoMod_nodesMod_rec := Induction for nodesCoMod Sort Type.
    Combined Scheme nodesMod_nodesCoMod_mutind from nodesMod_nodesCoMod_ind, nodesCoMod_nodesMod_ind.
    Definition nodesMod_nodesCoMod_mutrec P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8 := 
      pair (nodesMod_nodesCoMod_rec P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8)
           (nodesCoMod_nodesMod_rec P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8).

    (** ** Nodes where self is some Refl or CoRefl **)
    
    Inductive nodesReflMod : forall A1 A2, A1 ⊢a A2 -> Type :=
    | selfMod_Refl : forall {B1 B2} {g : B1 ⊢b B2}, nodesReflMod (F| g)
    | bottomF_Refl : forall B1 B2 (g : B1 ⊢b B2), nodesReflCoMod g -> nodesReflMod (F| g)
    | bottomφ_Refl : forall A1 A2 (f : A1 ⊢a A2), nodesReflMod f -> nodesReflMod (φ| f)
    | leftComMod_Refl : forall {A1 A2} {f1 : A1 ⊢a A2},  forall A3 (f2 : A2 ⊢a A3), nodesReflMod f2 -> nodesReflMod (f2 <a f1)
    | rightComMod_Refl : forall A1 A2 (f1 : A1 ⊢a A2), nodesReflMod f1 -> forall {A3} {f2 : A2 ⊢a A3}, nodesReflMod (f2 <a f1)

    with nodesReflCoMod : forall B1 B2, B1 ⊢b B2 -> Type :=
    | selfCoMod_Refl : forall {A1 A2} {f : A1 ⊢a A2}, nodesReflCoMod (G| f)
    | bottomG_Refl : forall A1 A2 (f : A1 ⊢a A2), nodesReflMod f -> nodesReflCoMod (G| f)
    | bottomγ_Refl : forall B1 B2 (g : B1 ⊢b B2), nodesReflCoMod g -> nodesReflCoMod (γ| g)
    | leftComCoMod_Refl : forall {B1 B2} {g1 : B1 ⊢b B2},  forall B3 (g2 : B2 ⊢b B3), nodesReflCoMod g2 -> nodesReflCoMod (g2 <b g1)
    | rightComCoMod_Refl : forall B1 B2 (g1 : B1 ⊢b B2), nodesReflCoMod g1 -> forall {B3} {g2 : B2 ⊢b B3}, nodesReflCoMod (g2 <b g1).

    Hint Constructors nodesReflMod nodesReflCoMod.

    Scheme nodesReflMod_nodesReflCoMod_ind := Induction for nodesReflMod Sort Prop
                                              with nodesReflCoMod_nodesReflMod_ind := Induction for nodesReflCoMod Sort Prop .
    Scheme nodesReflMod_nodesReflCoMod_rec := Induction for nodesReflMod Sort Type
                                              with nodesReflCoMod_nodesReflMod_rec := Induction for nodesReflCoMod Sort Type.
    Combined Scheme nodesReflMod_nodesReflCoMod_mutind from nodesReflMod_nodesReflCoMod_ind, nodesReflCoMod_nodesReflMod_ind.
    Definition nodesReflMod_nodesReflCoMod_mutrec P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8 := 
      pair (nodesReflMod_nodesReflCoMod_rec P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8)
           (nodesReflCoMod_nodesReflMod_rec P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8).

    (** ** Linking primitives for Mod  **)
    
    Inductive linksRedModCat1Right {A1 A2} {f : A1 ⊢a A2} : nodesMod (f <a 1) -> nodesMod (f) -> Prop :=
    | linksRedModCat1Right_intro1 : forall n, linksRedModCat1Right (leftComMod n) (n).

    Inductive linksRedModCat1Left {A1 A2} {f : A1 ⊢a A2} : nodesMod (1 <a f) -> nodesMod (f) -> Prop :=
    | linksRedModCat1Left_intro1 : forall n, linksRedModCat1Left (rightComMod n) (n).

    Inductive linksRedModCat2Right {A3 A4} {f3 : A3 ⊢a A4} {A2} {f2 : A2 ⊢a A3} {A1} {f1 : A1 ⊢a A2} : nodesMod (f3 <a (f2 <a f1)) -> nodesMod ((f3 <a f2) <a f1) -> Prop :=
    | linksRedModCat2Right_intro1 : linksRedModCat2Right (selfMod) (leftComMod selfMod)
    | linksRedModCat2Right_intro2 : linksRedModCat2Right (rightComMod selfMod) (selfMod)
    | linksRedModCat2Right_intro3 : forall n3, linksRedModCat2Right (leftComMod n3) (leftComMod (leftComMod n3))
    | linksRedModCat2Right_intro4 : forall n2, linksRedModCat2Right (rightComMod (leftComMod n2)) (leftComMod (rightComMod n2))
    | linksRedModCat2Right_intro5 : forall n1, linksRedModCat2Right (rightComMod (rightComMod n1)) (rightComMod n1).

    Inductive linksRedModCat2Left {A3 A4} {f3 : A3 ⊢a A4} {A2} {f2 : A2 ⊢a A3} {A1} {f1 : A1 ⊢a A2} : nodesMod ((f3 <a f2) <a f1) -> nodesMod (f3 <a (f2 <a f1)) -> Prop :=
    | linksRedModCat2Left_intro1 : linksRedModCat2Left (selfMod) (rightComMod selfMod)
    | linksRedModCat2Left_intro2 : linksRedModCat2Left (leftComMod selfMod) (selfMod)
    | linksRedModCat2Left_intro3 : forall n1, linksRedModCat2Left (rightComMod n1) (rightComMod (rightComMod n1))
    | linksRedModCat2Left_intro4 : forall n2, linksRedModCat2Left (leftComMod (rightComMod n2)) (rightComMod (leftComMod n2))
    | linksRedModCat2Left_intro5 : forall n3, linksRedModCat2Left (leftComMod (leftComMod n3)) (leftComMod n3).

    Definition linksRedModFun1Refl {B} : nodesMod (F| (@CoModIden B)) ->  nodesMod (@ModIden (F|0 B)) -> Prop :=
      (fun n n' => False).

    Inductive linksRedModFun2Refl {B2 B3} {g2 : B2 ⊢b B3} {B1} {g1 : B1 ⊢b B2} : nodesMod (F| g2 <a F| g1) ->  nodesMod (F| (g2 <b g1)) -> Prop :=
    | linksRedModFun2Refl_intro1 : linksRedModFun2Refl (selfMod) (bottomF (selfCoMod))
    | linksRedModFun2Refl_intro2 : forall m2, linksRedModFun2Refl (leftComMod (bottomF m2)) (bottomF (leftComCoMod m2))
    | linksRedModFun2Refl_intro3 : forall m1, linksRedModFun2Refl (rightComMod (bottomF m1)) (bottomF (rightComCoMod m1)).

    Definition linksRedModFun2Refl_Rev {B2 B3} {g2 : B2 ⊢b B3} {B1} {g1 : B1 ⊢b B2} : nodesMod (F| (g2 <b g1)) ->  nodesMod (F| g2 <a F| g1) -> Prop :=
      (fun n n' => linksRedModFun2Refl n' n).

    Inductive linksRedModNatCoUnit1{A2 A3} {f2 : A2 ⊢a A3} {A1} {f1 : A1 ⊢a A2} : nodesMod (f2 <a φ| f1) -> nodesMod (φ| (f2 <a f1)) -> Prop := 
    | linksRedModNatCoUnit1_intro1 : linksRedModNatCoUnit1 (selfMod) (bottomφ selfMod)
    | linksRedModNatCoUnit1_intro2 : forall n, linksRedModNatCoUnit1 (leftComMod n) (bottomφ (leftComMod n))
    | linksRedModNatCoUnit1_intro3 : forall n, linksRedModNatCoUnit1 (rightComMod (bottomφ n)) (bottomφ (rightComMod n)).

    Inductive linksRedModNatCoUnit2 {A2 A3} {f2 : A2 ⊢a A3} {A1} {f1 : A1 ⊢a A2} : nodesMod (φ| f2 <a F| G| f1) -> nodesMod (φ| (f2 <a f1)) -> Prop :=
    | linksRedModNatCoUnit2_intro1 : linksRedModNatCoUnit2 (selfMod) (bottomφ selfMod)
    | linksRedModNatCoUnit2_intro2 : forall n, linksRedModNatCoUnit2 (leftComMod (bottomφ n)) (bottomφ (leftComMod n))
    | linksRedModNatCoUnit2_intro3 : forall n, linksRedModNatCoUnit2 (rightComMod (bottomF (bottomG n))) (bottomφ (rightComMod n)).

    Inductive linksRedModRectangle {B1 B2} {g : B1 ⊢b B2} {A2} {f : F|0 B2 ⊢a A2} : nodesMod (φ| f <a F| γ| g) -> nodesMod (f <a F| g) -> Prop :=
    | linksRedModRectangle_intro1 : linksRedModRectangle (selfMod) (selfMod)
    | linksRedModRectangle_intro2 : forall n, linksRedModRectangle (leftComMod (bottomφ n)) (leftComMod n)
    | linksRedModRectangle_intro3 : forall m, linksRedModRectangle (rightComMod (bottomF (bottomγ m))) (rightComMod (bottomF m)).

    Hint Constructors linksRedModFun2Refl linksRedModCat1Right linksRedModCat1Left linksRedModCat2Right linksRedModCat2Left linksRedModNatCoUnit1 linksRedModNatCoUnit2 linksRedModRectangle.
    
    (** ** Congruent linking for Mod **)
    
    Inductive linksRedModCongRefl B1 B2 (g g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop) : nodesMod (F| g) -> nodesMod (F| g') -> Prop :=
    | linksRedModCongRefl1_intro : forall m m', Λ m m' -> linksRedModCongRefl Λ (bottomF m) (bottomF m').

    Inductive linksRedModCongCoUnit A1 A2 (f f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop) : nodesMod (φ| f) -> nodesMod (φ| f') -> Prop :=
    | linksRedModCongCoUnit_intro : forall n n', Δ n n' -> linksRedModCongCoUnit Δ (bottomφ n) (bottomφ n').

    Inductive linksRedModCongComL A2 A3 (f2 f2' : A2 ⊢a A3) (Δ : nodesMod f2 -> nodesMod f2' -> Prop) {A1} {f1 : A1 ⊢a A2} : nodesMod (f2 <a f1) -> nodesMod (f2' <a f1) -> Prop :=
    | linksRedModCongComL_intro1 : linksRedModCongComL Δ (selfMod) (selfMod)
    | linksRedModCongComL_intro2 : forall n n', Δ n n' -> linksRedModCongComL Δ (leftComMod n) (leftComMod n')
    | linksRedModCongComL_intro3 : forall n1, linksRedModCongComL Δ (rightComMod n1) (rightComMod n1).

    Inductive linksRedModCongComR {A2} {A3} {f2 : A2 ⊢a A3} A1 (f1 f1' : A1 ⊢a A2) (Δ : nodesMod f1 -> nodesMod f1' -> Prop) : nodesMod (f2 <a f1) -> nodesMod (f2 <a f1') -> Prop :=
    | linksRedModCongComR_intro1 : linksRedModCongComR Δ (selfMod) (selfMod)
    | linksRedModCongComR_intro2 : forall n2, linksRedModCongComR Δ (leftComMod n2) (leftComMod n2)
    | linksRedModCongComR_intro3 : forall n n', Δ n n' -> linksRedModCongComR Δ (rightComMod n) (rightComMod n').

    Hint Constructors linksRedModCongRefl linksRedModCongCoUnit linksRedModCongComL linksRedModCongComR.
    
    (** ** Transitive linking for Mod **)
    
    Inductive linksRedModTrans A1 A2 (uModTrans f : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod uModTrans -> Prop) (f'' : A1 ⊢a A2) (Δ' : nodesMod uModTrans -> nodesMod f'' -> Prop) : nodesMod f -> nodesMod f'' -> Prop :=
    | linksRedModTrans_intro : forall n n', Δ n n' -> forall n'', Δ' n' n'' -> linksRedModTrans Δ Δ' n n''. 
    
    Hint Constructors linksRedModTrans.

    (** ** Linking primitives for CoMod  **)
    
    Inductive linksRedCoModCat1Right {B1 B2} {g : B1 ⊢b B2} : nodesCoMod (g <b '1) -> nodesCoMod (g) -> Prop :=
    | linksRedCoModCat1Right_intro2 : forall m, linksRedCoModCat1Right (leftComCoMod m) (m).

    Inductive linksRedCoModCat1Left {B1 B2} {g : B1 ⊢b B2} : nodesCoMod ('1 <b g) -> nodesCoMod (g) -> Prop :=
    | linksRedCoModCat1Left_intro2 : forall m, linksRedCoModCat1Left (rightComCoMod m) (m).

    Inductive linksRedCoModCat2Right {B3 B4} {g3 : B3 ⊢b B4} {B2} {g2 : B2 ⊢b B3} {B1} {g1 : B1 ⊢b B2} : nodesCoMod (g3 <b (g2 <b g1)) -> nodesCoMod ((g3 <b g2) <b g1) -> Prop :=
    | linksRedCoModCat2Right_intro1 : linksRedCoModCat2Right (selfCoMod) (leftComCoMod selfCoMod)
    | linksRedCoModCat2Right_intro2 : linksRedCoModCat2Right (rightComCoMod selfCoMod) (selfCoMod)
    | linksRedCoModCat2Right_intro3 : forall m3, linksRedCoModCat2Right (leftComCoMod m3) (leftComCoMod (leftComCoMod m3))
    | linksRedCoModCat2Right_intro4 : forall m2, linksRedCoModCat2Right (rightComCoMod (leftComCoMod m2)) (leftComCoMod (rightComCoMod m2))
    | linksRedCoModCat2Right_intro5 : forall m1, linksRedCoModCat2Right (rightComCoMod (rightComCoMod m1)) (rightComCoMod m1).

    Inductive linksRedCoModCat2Left {B3 B4} {g3 : B3 ⊢b B4} {B2} {g2 : B2 ⊢b B3} {B1} {g1 : B1 ⊢b B2} : nodesCoMod ((g3 <b g2) <b g1) -> nodesCoMod (g3 <b (g2 <b g1)) -> Prop :=
    | linksRedCoModCat2Left_intro1 : linksRedCoModCat2Left (selfCoMod) (rightComCoMod selfCoMod)
    | linksRedCoModCat2Left_intro2 : linksRedCoModCat2Left (leftComCoMod selfCoMod) (selfCoMod)
    | linksRedCoModCat2Left_intro3 : forall m1, linksRedCoModCat2Left (rightComCoMod m1) (rightComCoMod (rightComCoMod m1))
    | linksRedCoModCat2Left_intro4 : forall m2, linksRedCoModCat2Left (leftComCoMod (rightComCoMod m2)) (rightComCoMod (leftComCoMod m2))
    | linksRedCoModCat2Left_intro5 : forall m3, linksRedCoModCat2Left (leftComCoMod (leftComCoMod m3)) (leftComCoMod m3).

    Definition linksRedCoModFun1Refl {A} : nodesCoMod (G| (@ModIden A)) ->  nodesCoMod (@CoModIden (G|0 A)) -> Prop :=
      (fun m m' => False).

    Inductive linksRedCoModFun2Refl {A2 A3} {f2 : A2 ⊢a A3} {A1} {f1 : A1 ⊢a A2} : nodesCoMod (G| f2 <b G| f1) ->  nodesCoMod (G| (f2 <a f1)) -> Prop :=
    | linksRedCoModFun2Refl_intro1 : linksRedCoModFun2Refl (selfCoMod) (bottomG (selfMod))
    | linksRedCoModFun2Refl_intro2 : forall n2, linksRedCoModFun2Refl (leftComCoMod (bottomG n2)) (bottomG (leftComMod n2))
    | linksRedCoModFun2Refl_intro3 : forall n1, linksRedCoModFun2Refl (rightComCoMod (bottomG n1)) (bottomG (rightComMod n1)).

    Definition linksRedCoModFun2Refl_Rev {A2 A3} {f2 : A2 ⊢a A3} {A1} {f1 : A1 ⊢a A2} : nodesCoMod (G| (f2 <a f1)) ->  nodesCoMod (G| f2 <b G| f1) -> Prop :=
      (fun m m' => linksRedCoModFun2Refl m' m).
    
    Inductive linksRedCoModNatUnit1{B2 B3} {g2 : B2 ⊢b B3} {B1} {g1 : B1 ⊢b B2} : nodesCoMod (γ| g2 <b g1) -> nodesCoMod (γ| (g2 <b g1)) -> Prop := 
    | linksRedCoModNatUnit1_intro1 : linksRedCoModNatUnit1 (selfCoMod) (bottomγ selfCoMod)
    | linksRedCoModNatUnit1_intro2 : forall m, linksRedCoModNatUnit1 (leftComCoMod (bottomγ m)) (bottomγ (leftComCoMod m))
    | linksRedCoModNatUnit1_intro3 : forall m, linksRedCoModNatUnit1 (rightComCoMod m) (bottomγ (rightComCoMod m)).

    Inductive linksRedCoModNatUnit2 {B2 B3} {g2 : B2 ⊢b B3} {B1} {g1 : B1 ⊢b B2} : nodesCoMod ( G| F| g2 <b γ| g1) -> nodesCoMod (γ| (g2 <b g1)) -> Prop :=
    | linksRedCoModNatUnit2_intro1 : linksRedCoModNatUnit2 (selfCoMod) (bottomγ selfCoMod)
    | linksRedCoModNatUnit2_intro2 : forall m, linksRedCoModNatUnit2 (leftComCoMod (bottomG (bottomF m))) (bottomγ (leftComCoMod m))
    | linksRedCoModNatUnit2_intro3 : forall m, linksRedCoModNatUnit2 (rightComCoMod (bottomγ m)) (bottomγ (rightComCoMod m)).

    Inductive linksRedCoModRectangle {A1 A2} {f : A1 ⊢a A2} {B1} {g : B1 ⊢b G|0 A1} : nodesCoMod (G| φ| f <b γ| g) -> nodesCoMod ( G| f <b g) -> Prop :=
    | linksRedCoModRectangle_intro1 : linksRedCoModRectangle (selfCoMod) (selfCoMod)
    | linksRedCoModRectangle_intro2 : forall n, linksRedCoModRectangle (leftComCoMod (bottomG (bottomφ n))) (leftComCoMod (bottomG n))
    | linksRedCoModRectangle_intro3 : forall m, linksRedCoModRectangle (rightComCoMod (bottomγ m)) (rightComCoMod m).

    Hint Constructors linksRedCoModFun2Refl linksRedCoModCat1Right linksRedCoModCat1Left linksRedCoModCat2Right linksRedCoModCat2Left linksRedCoModNatUnit1 linksRedCoModNatUnit2 linksRedCoModRectangle.
    
    (** ** Congruent linking for CoMod **)
    
    Inductive linksRedCoModCongRefl A1 A2 (f f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop) : nodesCoMod (G| f) -> nodesCoMod (G| f') -> Prop :=
    | linksRedCoModCongRefl1_intro : forall n n', Δ n n' -> linksRedCoModCongRefl Δ (bottomG n) (bottomG n').

    Inductive linksRedCoModCongUnit B1 B2 (g g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop) : nodesCoMod (γ| g) -> nodesCoMod (γ| g') -> Prop :=
    | linksRedCoModCongUnit_intro : forall m m', Λ m m' -> linksRedCoModCongUnit Λ (bottomγ m) (bottomγ m').

    Inductive linksRedCoModCongComL B2 B3 (g2 g2' : B2 ⊢b B3) (Λ : nodesCoMod g2 -> nodesCoMod g2' -> Prop) {B1} {g1 : B1 ⊢b B2} : nodesCoMod (g2 <b g1) -> nodesCoMod (g2' <b g1) -> Prop :=
    | linksRedCoModCongComL_intro1 : linksRedCoModCongComL Λ (selfCoMod) (selfCoMod)
    | linksRedCoModCongComL_intro2 : forall m m', Λ m m' -> linksRedCoModCongComL Λ (leftComCoMod m) (leftComCoMod m')
    | linksRedCoModCongComL_intro3 : forall m1, linksRedCoModCongComL Λ (rightComCoMod m1) (rightComCoMod m1).

    Inductive linksRedCoModCongComR {B2} {B3} {g2 : B2 ⊢b B3} B1 (g1 g1' : B1 ⊢b B2) (Λ : nodesCoMod g1 -> nodesCoMod g1' -> Prop) : nodesCoMod (g2 <b g1) -> nodesCoMod (g2 <b g1') -> Prop :=
    | linksRedCoModCongComR_intro1 : linksRedCoModCongComR Λ (selfCoMod) (selfCoMod)
    | linksRedCoModCongComR_intro2 : forall m2, linksRedCoModCongComR Λ (leftComCoMod m2) (leftComCoMod m2)
    | linksRedCoModCongComR_intro3 : forall m m', Λ m m' -> linksRedCoModCongComR Λ (rightComCoMod m) (rightComCoMod m').

    Hint Constructors linksRedCoModCongRefl linksRedCoModCongUnit linksRedCoModCongComL linksRedCoModCongComR.
    
    (** ** Transitive linking for CoMod **)
    
    Inductive linksRedCoModTrans B1 B2 (uCoModTrans g : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod uCoModTrans -> Prop) (g'' : B1 ⊢b B2) (Λ' : nodesCoMod uCoModTrans -> nodesCoMod g'' -> Prop) : nodesCoMod g -> nodesCoMod g'' -> Prop :=
    | linksRedCoModTrans_intro : forall m m', Λ m m' -> forall m'', Λ' m' m'' -> linksRedCoModTrans Λ Λ' m m''. 
    
    Hint Constructors linksRedCoModTrans.

    (** ** redCongMod congruent reduction, parametrized by particular reductions **)

    (** /!\ MAYBE USE PARAMETRIC MODULE FUNCTORS HERE /!\ **)

    Reserved Notation "Δ ⊧ f' ↜a f \at n" (at level 70, f' at next level).
    Reserved Notation "Λ ⊧ g' ↜b g \at m" (at level 70, g' at next level).

    Section redCongMod.

      (** *** redCongMod for Com nodes **)
      
      Variable (redOnceMod : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop).
      
      Inductive redCongMod_Mod : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
      | redCongMod_RedModCongRefl : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                      Λ ⊧ g' ↜b g \at m ->
                                      linksRedModCongRefl Λ ⊧ F| g' ↜a F| g \at (bottomF m)
      | redCongMod_RedModCongCoUnit : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                        Δ ⊧ f' ↜a f \at n ->
                                        linksRedModCongCoUnit Δ ⊧ φ| f' ↜a φ| f \at (bottomφ n)
      | redCongMod_RedModCongComL : forall A2 A3 (f2 : A2 ⊢a A3) n2 (f2' : A2 ⊢a A3) Δ {A1} {f1 : A1 ⊢a A2},
                                      Δ ⊧ f2' ↜a f2 \at n2 ->
                                      linksRedModCongComL Δ ⊧ (f2' <a f1) ↜a (f2 <a f1) \at (leftComMod n2)
      | redCongMod_RedModCongComR : forall {A2} {A3} {f2 : A2 ⊢a A3} A1 (f1 : A1 ⊢a A2) n1 (f1' : A1 ⊢a A2) Δ,
                                      Δ ⊧ f1' ↜a f1 \at n1 ->
                                      linksRedModCongComR Δ ⊧ (f2 <a f1') ↜a (f2 <a f1) \at (rightComMod n1)

      | redCongMod_redOnceMod : forall A1 A2 (f : A1 ⊢a A2) (n : nodesMod f) (f' : A1 ⊢a A2) (Δ : (nodesMod f -> nodesMod f' -> Prop)),
                                  @redOnceMod A1 A2 f  n f' Δ ->
                                  Δ ⊧ f' ↜a f \at n

      with redCongMod_CoMod : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) -> Prop :=
      | redCongMod_RedCoModCongRefl : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                        Δ ⊧ f' ↜a f \at n ->
                                        linksRedCoModCongRefl Δ ⊧ G| f' ↜b G| f \at (bottomG n)
      | redCongMod_RedCoModCongUnit : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                        Λ ⊧ g' ↜b g \at m ->
                                        linksRedCoModCongUnit Λ ⊧ γ| g' ↜b γ| g \at (bottomγ m)
      | redCongMod_RedCoModCongComL : forall B2 B3 (g2 : B2 ⊢b B3) m2 (g2' : B2 ⊢b B3) Λ {B1} {g1 : B1 ⊢b B2},
                                        Λ ⊧ g2' ↜b g2 \at m2 ->
                                        linksRedCoModCongComL Λ ⊧ (g2' <b g1) ↜b (g2 <b g1) \at (leftComCoMod m2)
      | redCongMod_RedCoModCongComR : forall {B2} {B3} {g2 : B2 ⊢b B3} B1 (g1 : B1 ⊢b B2) m1 (g1' : B1 ⊢b B2) Λ,
                                        Λ ⊧ g1' ↜b g1 \at m1 ->
                                        linksRedCoModCongComR Λ ⊧ (g2 <b g1') ↜b (g2 <b g1) \at (rightComCoMod m1)

      where "Δ ⊧ f' ↜a f \at n" := (@redCongMod_Mod _ _ f n f' Δ) : solScope
                                                                      and "Λ ⊧ g' ↜b g \at m" := (@redCongMod_CoMod _ _ g m g' Λ) : solScope.

      Hint Constructors redCongMod_Mod redCongMod_CoMod.

      Scheme redCongMod_Mod_redCongMod_CoMod_ind := Induction for redCongMod_Mod Sort Prop
                                                    with redCongMod_CoMod_redCongMod_Mod_ind := Induction for redCongMod_CoMod Sort Prop .
      Combined Scheme redCongMod_Mod_redCongMod_CoMod_mutind from redCongMod_Mod_redCongMod_CoMod_ind, redCongMod_CoMod_redCongMod_Mod_ind.

      (** *** redCongMod for Refl nodes **)
      
      Variable (redOnceMod_r : forall A1 A2 (f : A1 ⊢a A2), (nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop).
      
      Inductive redCongMod_Mod_r : forall A1 A2 (f : A1 ⊢a A2), (nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
      | redCongMod_RedModCongRefl_r : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                        Λ ⊧ g' ↜b g \at m ->
                                        linksRedModCongRefl Λ ⊧ F| g' ↜a F| g \at (bottomF_Refl m)
      | redCongMod_RedModCongCoUnit_r : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                          Δ ⊧ f' ↜a f \at n ->
                                          linksRedModCongCoUnit Δ ⊧ φ| f' ↜a φ| f \at (bottomφ_Refl n)
      | redCongMod_RedModCongComL_r : forall A2 A3 (f2 : A2 ⊢a A3) n2 (f2' : A2 ⊢a A3) Δ {A1} {f1 : A1 ⊢a A2},
                                        Δ ⊧ f2' ↜a f2 \at n2 ->
                                        linksRedModCongComL Δ ⊧ (f2' <a f1) ↜a (f2 <a f1) \at (leftComMod_Refl n2)
      | redCongMod_RedModCongComR_r : forall {A2} {A3} {f2 : A2 ⊢a A3} A1 (f1 : A1 ⊢a A2) n1 (f1' : A1 ⊢a A2) Δ,
                                        Δ ⊧ f1' ↜a f1 \at n1 ->
                                        linksRedModCongComR Δ ⊧ (f2 <a f1') ↜a (f2 <a f1) \at (rightComMod_Refl n1)

      | redCongMod_redOnceMod_r : forall A1 A2 (f : A1 ⊢a A2) (n : nodesReflMod f) (f' : A1 ⊢a A2) (Δ : (nodesMod f -> nodesMod f' -> Prop)),
                                    @redOnceMod_r A1 A2 f  n f' Δ ->
                                    Δ ⊧ f' ↜a f \at n

      with redCongMod_CoMod_r : forall B1 B2 (g : B1 ⊢b B2), (nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) -> Prop :=
      | redCongMod_RedCoModCongRefl_r : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                          Δ ⊧ f' ↜a f \at n ->
                                          linksRedCoModCongRefl Δ ⊧ G| f' ↜b G| f \at (bottomG_Refl n)
      | redCongMod_RedCoModCongUnit_r : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                          Λ ⊧ g' ↜b g \at m ->
                                          linksRedCoModCongUnit Λ ⊧ γ| g' ↜b γ| g \at (bottomγ_Refl m)
      | redCongMod_RedCoModCongComL_r : forall B2 B3 (g2 : B2 ⊢b B3) m2 (g2' : B2 ⊢b B3) Λ {B1} {g1 : B1 ⊢b B2},
                                          Λ ⊧ g2' ↜b g2 \at m2 ->
                                          linksRedCoModCongComL Λ ⊧ (g2' <b g1) ↜b (g2 <b g1) \at (leftComCoMod_Refl m2)
      | redCongMod_RedCoModCongComR_r : forall {B2} {B3} {g2 : B2 ⊢b B3} B1 (g1 : B1 ⊢b B2) m1 (g1' : B1 ⊢b B2) Λ,
                                          Λ ⊧ g1' ↜b g1 \at m1 ->
                                          linksRedCoModCongComR Λ ⊧ (g2 <b g1') ↜b (g2 <b g1) \at (rightComCoMod_Refl m1)

      where "Δ ⊧ f' ↜a f \at n" := (@redCongMod_Mod_r _ _ f n f' Δ) : solScope
                                                                        and "Λ ⊧ g' ↜b g \at m" := (@redCongMod_CoMod_r _ _ g m g' Λ) : solScope.

      Hint Constructors redCongMod_Mod_r redCongMod_CoMod_r.

      Scheme redCongMod_Mod_redCongMod_CoMod_ind_r := Induction for redCongMod_Mod_r Sort Prop
                                                      with redCongMod_CoMod_redCongMod_Mod_ind_r := Induction for redCongMod_CoMod_r Sort Prop .
      Combined Scheme redCongMod_Mod_redCongMod_CoMod_mutind_r from redCongMod_Mod_redCongMod_CoMod_ind_r, redCongMod_CoMod_redCongMod_Mod_ind_r.
      
    End redCongMod.

    (** *** Instantiations of redCongMod **)

    Inductive redOnce_RedModCat1Right : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | RedModCat1Right : forall A1 A2 (f : A1 ⊢a A2),
                          @redOnce_RedModCat1Right _ _ (f <a 1) (selfMod) (f) linksRedModCat1Right .

    Definition redCong_RedModCat1Right_Mod  := redCongMod_Mod redOnce_RedModCat1Right.
    Definition redCong_RedModCat1Right_CoMod  := redCongMod_CoMod redOnce_RedModCat1Right.

    Inductive redOnce_RedModCat1Left : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | RedModCat1Left : forall A1 A2 (f : A1 ⊢a A2),
                         @redOnce_RedModCat1Left _ _ (1 <a f) (selfMod) (f) linksRedModCat1Left .

    Definition redCong_RedModCat1Left_Mod  := redCongMod_Mod redOnce_RedModCat1Left.
    Definition redCong_RedModCat1Left_CoMod  := redCongMod_CoMod redOnce_RedModCat1Left.
    
    Inductive redOnce_RedModCat2Right : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | RedModCat2Right : forall A3 A4 (f3 : A3 ⊢a A4) A2 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                          @redOnce_RedModCat2Right _ _ (f3 <a (f2 <a f1)) (selfMod) ((f3 <a f2) <a f1) linksRedModCat2Right .

    Definition redCong_RedModCat2Right_Mod  := redCongMod_Mod redOnce_RedModCat2Right.
    Definition redCong_RedModCat2Right_CoMod  := redCongMod_CoMod redOnce_RedModCat2Right.

    Inductive redOnce_RedModCat2Left : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | RedModCat2Left : forall A3 A4 (f3 : A3 ⊢a A4) A2 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                         @redOnce_RedModCat2Left _ _ ((f3 <a f2) <a f1) (selfMod) (f3 <a (f2 <a f1)) linksRedModCat2Left .

    Definition redCong_RedModCat2Left_Mod  := redCongMod_Mod redOnce_RedModCat2Left.
    Definition redCong_RedModCat2Left_CoMod  := redCongMod_CoMod redOnce_RedModCat2Left.

    Inductive redOnce_RedModFun1Refl : forall A1 A2 (f : A1 ⊢a A2), (nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | RedModFun1Refl : forall B,
                         @redOnce_RedModFun1Refl _ _ (F| (@CoModIden B)) (selfMod_Refl) (1) linksRedModFun1Refl .

    Definition redCong_RedModFun1Refl_Mod  := redCongMod_Mod_r redOnce_RedModFun1Refl.
    Definition redCong_RedModFun1Refl_CoMod  := redCongMod_CoMod_r redOnce_RedModFun1Refl.
    
    Inductive redOnce_RedModFun2Refl : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | RedModFun2Refl : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                         @redOnce_RedModFun2Refl _ _ (F| g2 <a F| g1) (selfMod) (F| (g2 <b g1)) linksRedModFun2Refl .

    Definition redCong_RedModFun2Refl_Mod  := redCongMod_Mod redOnce_RedModFun2Refl.
    Definition redCong_RedModFun2Refl_CoMod  := redCongMod_CoMod redOnce_RedModFun2Refl.

    Inductive redOnce_RedModFun2Refl_Rev : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | RedModFun2Refl_Rev : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                             @redOnce_RedModFun2Refl_Rev _ _ (F| (g2 <b g1)) (bottomF selfCoMod) (F| g2 <a F| g1) linksRedModFun2Refl_Rev .

    Definition redCong_RedModFun2Refl_Rev_Mod  := redCongMod_Mod redOnce_RedModFun2Refl_Rev.
    Definition redCong_RedModFun2Refl_Rev_CoMod  := redCongMod_CoMod redOnce_RedModFun2Refl_Rev.

    Inductive redOnce_RedModNatCoUnit1 : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | RedModNatCoUnit1 : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                           @redOnce_RedModNatCoUnit1 _ _ (f2 <a φ| f1) (selfMod) (φ| (f2 <a f1)) linksRedModNatCoUnit1 .

    Definition redCong_RedModNatCoUnit1_Mod  := redCongMod_Mod redOnce_RedModNatCoUnit1.
    Definition redCong_RedModNatCoUnit1_CoMod  := redCongMod_CoMod redOnce_RedModNatCoUnit1.
    
    Inductive redOnce_RedModNatCoUnit2 : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | RedModNatCoUnit2 : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                           @redOnce_RedModNatCoUnit2 _ _ (φ| f2 <a F| G| f1) (selfMod) (φ| (f2 <a f1)) linksRedModNatCoUnit2 .

    Definition redCong_RedModNatCoUnit2_Mod  := redCongMod_Mod redOnce_RedModNatCoUnit2.
    Definition redCong_RedModNatCoUnit2_CoMod  := redCongMod_CoMod redOnce_RedModNatCoUnit2.
    
    Inductive redOnce_RedModRectangle : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | RedModRectangle : forall B1 B2 (g : B1 ⊢b B2) A2 (f : F|0 B2 ⊢a A2),
                          @redOnce_RedModRectangle _ _ (φ| f <a F| γ| g) (selfMod) (f <a F| g) linksRedModRectangle .

    Definition redCong_RedModRectangle_Mod  := redCongMod_Mod redOnce_RedModRectangle.
    Definition redCong_RedModRectangle_CoMod  := redCongMod_CoMod redOnce_RedModRectangle.
    
    Hint Constructors redOnce_RedModCat1Right redOnce_RedModCat1Left redOnce_RedModCat2Right redOnce_RedModCat2Left redOnce_RedModFun1Refl redOnce_RedModFun2Refl redOnce_RedModFun2Refl_Rev redOnce_RedModNatCoUnit1 redOnce_RedModNatCoUnit2 redOnce_RedModRectangle.
    
    (** ** redCongCoMod congruent reduction, parametrized by particular reductions *)
    
    (** /!\ MAYBE USE PARAMETRIC MODULE FUNCTORS HERE /!\ **)
    
    Reserved Notation "Δ ⊧ f' ↜a f \at' n" (at level 70, f' at next level).
    Reserved Notation "Λ ⊧ g' ↜b g \at' m" (at level 70, g' at next level).
    
    Section redCongCoMod.

      (** *** redCongCoMod for CoCom nodes **)

      Variable (redOnceCoMod : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop).
      
      Inductive redCongCoMod_Mod : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
      | redCongCoMod_RedModCongRefl : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                        Λ ⊧ g' ↜b g \at' m ->
                                        linksRedModCongRefl Λ ⊧ F| g' ↜a F| g \at' (bottomF m)
      | redCongCoMod_RedModCongCoUnit : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                          Δ ⊧ f' ↜a f \at' n ->
                                          linksRedModCongCoUnit Δ ⊧ φ| f' ↜a φ| f \at' (bottomφ n)
      | redCongCoMod_RedModCongComL : forall A2 A3 (f2 : A2 ⊢a A3) n2 (f2' : A2 ⊢a A3) Δ {A1} {f1 : A1 ⊢a A2},
                                        Δ ⊧ f2' ↜a f2 \at' n2 ->
                                        linksRedModCongComL Δ ⊧ (f2' <a f1) ↜a (f2 <a f1) \at' (leftComMod n2)
      | redCongCoMod_RedModCongComR : forall {A2} {A3} {f2 : A2 ⊢a A3} A1 (f1 : A1 ⊢a A2) n1 (f1' : A1 ⊢a A2) Δ,
                                        Δ ⊧ f1' ↜a f1 \at' n1 ->
                                        linksRedModCongComR Δ ⊧ (f2 <a f1') ↜a (f2 <a f1) \at' (rightComMod n1)

      with redCongCoMod_CoMod : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) -> Prop :=
      | redCongCoMod_RedCoModCongRefl : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                          Δ ⊧ f' ↜a f \at' n ->
                                          linksRedCoModCongRefl Δ ⊧ G| f' ↜b G| f \at' (bottomG n)
      | redCongCoMod_RedCoModCongUnit : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                          Λ ⊧ g' ↜b g \at' m ->
                                          linksRedCoModCongUnit Λ ⊧ γ| g' ↜b γ| g \at' (bottomγ m)
      | redCongCoMod_RedCoModCongComL : forall B2 B3 (g2 : B2 ⊢b B3) m2 (g2' : B2 ⊢b B3) Λ {B1} {g1 : B1 ⊢b B2},
                                          Λ ⊧ g2' ↜b g2 \at' m2 ->
                                          linksRedCoModCongComL Λ ⊧ (g2' <b g1) ↜b (g2 <b g1) \at' (leftComCoMod m2)
      | redCongCoMod_RedCoModCongComR : forall {B2} {B3} {g2 : B2 ⊢b B3} B1 (g1 : B1 ⊢b B2) m1 (g1' : B1 ⊢b B2) Λ,
                                          Λ ⊧ g1' ↜b g1 \at' m1 ->
                                          linksRedCoModCongComR Λ ⊧ (g2 <b g1') ↜b (g2 <b g1) \at' (rightComCoMod m1)

      | redCongCoMod_redOnceCoMod : forall B1 B2 (g : B1 ⊢b B2) (m : (nodesCoMod g)) (g' : B1 ⊢b B2) (Λ : (nodesCoMod g -> nodesCoMod g' -> Prop)),
                                      @redOnceCoMod B1 B2 g  m g' Λ ->
                                      Λ ⊧ g' ↜b g \at' m
                                        
      where "Δ ⊧ f' ↜a f \at' n" := (@redCongCoMod_Mod _ _ f n f' Δ) : solScope
                                                                         and "Λ ⊧ g' ↜b g \at' m" := (@redCongCoMod_CoMod _ _ g m g' Λ) : solScope.

      Hint Constructors redCongCoMod_Mod redCongCoMod_CoMod.

      Scheme redCongCoMod_Mod_redCongCoMod_CoMod_ind := Induction for redCongCoMod_Mod Sort Prop
                                                        with redCongCoMod_CoMod_redCongCoMod_Mod_ind := Induction for redCongCoMod_CoMod Sort Prop .
      Combined Scheme redCongCoMod_Mod_redCongCoMod_CoMod_mutind from redCongCoMod_Mod_redCongCoMod_CoMod_ind, redCongCoMod_CoMod_redCongCoMod_Mod_ind.

      (** *** redCongCoMod for CoRefl nodes **)

      Variable (redOnceCoMod_r : forall B1 B2 (g : B1 ⊢b B2), (nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop).
      
      Inductive redCongCoMod_Mod_r : forall A1 A2 (f : A1 ⊢a A2), (nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
      | redCongCoMod_RedModCongRefl_r : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                          Λ ⊧ g' ↜b g \at' m ->
                                          linksRedModCongRefl Λ ⊧ F| g' ↜a F| g \at' (bottomF_Refl m)
      | redCongCoMod_RedModCongCoUnit_r : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                            Δ ⊧ f' ↜a f \at' n ->
                                            linksRedModCongCoUnit Δ ⊧ φ| f' ↜a φ| f \at' (bottomφ_Refl n)
      | redCongCoMod_RedModCongComL_r : forall A2 A3 (f2 : A2 ⊢a A3) n2 (f2' : A2 ⊢a A3) Δ {A1} {f1 : A1 ⊢a A2},
                                          Δ ⊧ f2' ↜a f2 \at' n2 ->
                                          linksRedModCongComL Δ ⊧ (f2' <a f1) ↜a (f2 <a f1) \at' (leftComMod_Refl n2)
      | redCongCoMod_RedModCongComR_r : forall {A2} {A3} {f2 : A2 ⊢a A3} A1 (f1 : A1 ⊢a A2) n1 (f1' : A1 ⊢a A2) Δ,
                                          Δ ⊧ f1' ↜a f1 \at' n1 ->
                                          linksRedModCongComR Δ ⊧ (f2 <a f1') ↜a (f2 <a f1) \at' (rightComMod_Refl n1)

      with redCongCoMod_CoMod_r : forall B1 B2 (g : B1 ⊢b B2), (nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) -> Prop :=
      | redCongCoMod_RedCoModCongRefl_r : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                            Δ ⊧ f' ↜a f \at' n ->
                                            linksRedCoModCongRefl Δ ⊧ G| f' ↜b G| f \at' (bottomG_Refl n)
      | redCongCoMod_RedCoModCongUnit_r : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                            Λ ⊧ g' ↜b g \at' m ->
                                            linksRedCoModCongUnit Λ ⊧ γ| g' ↜b γ| g \at' (bottomγ_Refl m)
      | redCongCoMod_RedCoModCongComL_r : forall B2 B3 (g2 : B2 ⊢b B3) m2 (g2' : B2 ⊢b B3) Λ {B1} {g1 : B1 ⊢b B2},
                                            Λ ⊧ g2' ↜b g2 \at' m2 ->
                                            linksRedCoModCongComL Λ ⊧ (g2' <b g1) ↜b (g2 <b g1) \at' (leftComCoMod_Refl m2)
      | redCongCoMod_RedCoModCongComR_r : forall {B2} {B3} {g2 : B2 ⊢b B3} B1 (g1 : B1 ⊢b B2) m1 (g1' : B1 ⊢b B2) Λ,
                                            Λ ⊧ g1' ↜b g1 \at' m1 ->
                                            linksRedCoModCongComR Λ ⊧ (g2 <b g1') ↜b (g2 <b g1) \at' (rightComCoMod_Refl m1)

      | redCongCoMod_redOnceCoMod_r : forall B1 B2 (g : B1 ⊢b B2) (m : (nodesReflCoMod g)) (g' : B1 ⊢b B2) (Λ : (nodesCoMod g -> nodesCoMod g' -> Prop)),
                                        @redOnceCoMod_r B1 B2 g  m g' Λ ->
                                        Λ ⊧ g' ↜b g \at' m
                                          
      where "Δ ⊧ f' ↜a f \at' n" := (@redCongCoMod_Mod_r _ _ f n f' Δ) : solScope
                                                                           and "Λ ⊧ g' ↜b g \at' m" := (@redCongCoMod_CoMod_r _ _ g m g' Λ) : solScope.

      Hint Constructors redCongCoMod_Mod_r redCongCoMod_CoMod_r.

      Scheme redCongCoMod_Mod_redCongCoMod_CoMod_ind_r := Induction for redCongCoMod_Mod_r Sort Prop
                                                          with redCongCoMod_CoMod_redCongCoMod_Mod_ind_r := Induction for redCongCoMod_CoMod_r Sort Prop .
      Combined Scheme redCongCoMod_Mod_redCongCoMod_CoMod_mutind_r from redCongCoMod_Mod_redCongCoMod_CoMod_ind_r, redCongCoMod_CoMod_redCongCoMod_Mod_ind_r.
      
    End redCongCoMod.

    (** *** Instantiations of redCongCoMod **)

    Inductive redOnce_RedCoModCat1Right : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
    | RedCoModCat1Right : forall B1 B2 (g : B1 ⊢b B2),
                            @redOnce_RedCoModCat1Right _ _ (g <b '1) (selfCoMod) (g) linksRedCoModCat1Right .

    Definition redCong_RedCoModCat1Right_CoMod := redCongCoMod_CoMod redOnce_RedCoModCat1Right.
    Definition redCong_RedCoModCat1Right_Mod := redCongCoMod_Mod redOnce_RedCoModCat1Right.
    
    Inductive redOnce_RedCoModCat1Left : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
    | RedCoModCat1Left : forall B1 B2 (g : B1 ⊢b B2),
                           @redOnce_RedCoModCat1Left _ _ ('1 <b g) (selfCoMod) (g) linksRedCoModCat1Left .

    Definition redCong_RedCoModCat1Left_CoMod := redCongCoMod_CoMod redOnce_RedCoModCat1Left.
    Definition redCong_RedCoModCat1Left_Mod := redCongCoMod_Mod redOnce_RedCoModCat1Left.

    Inductive redOnce_RedCoModCat2Right : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
    | RedCoModCat2Right : forall B3 B4 (g3 : B3 ⊢b B4) B2 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                            @redOnce_RedCoModCat2Right _ _ (g3 <b (g2 <b g1)) (selfCoMod) ((g3 <b g2) <b g1) linksRedCoModCat2Right .

    Definition redCong_RedCoModCat2Right_CoMod := redCongCoMod_CoMod redOnce_RedCoModCat2Right.
    Definition redCong_RedCoModCat2Right_Mod := redCongCoMod_Mod redOnce_RedCoModCat2Right.
    
    Inductive redOnce_RedCoModCat2Left : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
    | RedCoModCat2Left : forall B3 B4 (g3 : B3 ⊢b B4) B2 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                           @redOnce_RedCoModCat2Left _ _ ((g3 <b g2) <b g1) (selfCoMod) (g3 <b (g2 <b g1)) linksRedCoModCat2Left .

    Definition redCong_RedCoModCat2Left_CoMod := redCongCoMod_CoMod redOnce_RedCoModCat2Left.
    Definition redCong_RedCoModCat2Left_Mod := redCongCoMod_Mod redOnce_RedCoModCat2Left.
    
    Inductive redOnce_RedCoModFun1Refl : forall B1 B2 (g : B1 ⊢b B2), (nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
    | RedCoModFun1Refl : forall A,
                           @redOnce_RedCoModFun1Refl _ _ (G| (@ModIden A)) (selfCoMod_Refl) ('1) linksRedCoModFun1Refl .

    Definition redCong_RedCoModFun1Refl_CoMod := redCongCoMod_CoMod_r redOnce_RedCoModFun1Refl.
    Definition redCong_RedCoModFun1Refl_Mod := redCongCoMod_Mod_r redOnce_RedCoModFun1Refl.
    
    Inductive redOnce_RedCoModFun2Refl : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
    | RedCoModFun2Refl : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                           @redOnce_RedCoModFun2Refl _ _ (G| f2 <b G| f1) (selfCoMod) (G| (f2 <a f1)) linksRedCoModFun2Refl .

    Definition redCong_RedCoModFun2Refl_CoMod := redCongCoMod_CoMod redOnce_RedCoModFun2Refl.
    Definition redCong_RedCoModFun2Refl_Mod := redCongCoMod_Mod redOnce_RedCoModFun2Refl.
    
    Inductive redOnce_RedCoModFun2Refl_Rev : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
    | RedCoModFun2Refl_Rev : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                               @redOnce_RedCoModFun2Refl_Rev _ _ (G| (f2 <a f1)) (bottomG selfMod) (G| f2 <b G| f1) linksRedCoModFun2Refl_Rev .

    Definition redCong_RedCoModFun2Refl_Rev_CoMod := redCongCoMod_CoMod redOnce_RedCoModFun2Refl_Rev.
    Definition redCong_RedCoModFun2Refl_Rev_Mod := redCongCoMod_Mod redOnce_RedCoModFun2Refl_Rev.
    
    Inductive redOnce_RedCoModNatUnit1 : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
    | RedCoModNatUnit1 : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                           @redOnce_RedCoModNatUnit1 _ _ (γ| g2 <b g1) (selfCoMod) (γ| (g2 <b g1)) linksRedCoModNatUnit1 .

    Definition redCong_RedCoModNatUnit1_CoMod := redCongCoMod_CoMod redOnce_RedCoModNatUnit1.
    Definition redCong_RedCoModNatUnit1_Mod := redCongCoMod_Mod redOnce_RedCoModNatUnit1.
    
    Inductive redOnce_RedCoModNatUnit2 : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
    | RedCoModNatUnit2 : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                           @redOnce_RedCoModNatUnit2 _ _ (G| F| g2 <b γ| g1) (selfCoMod) (γ| (g2 <b g1)) linksRedCoModNatUnit2 .

    Definition redCong_RedCoModNatUnit2_CoMod := redCongCoMod_CoMod redOnce_RedCoModNatUnit2.
    Definition redCong_RedCoModNatUnit2_Mod := redCongCoMod_Mod redOnce_RedCoModNatUnit2.
    
    Inductive redOnce_RedCoModRectangle : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
    | RedCoModRectangle : forall A1 A2 (f : A1 ⊢a A2) B1 (g : B1 ⊢b G|0 A1),
                            @redOnce_RedCoModRectangle _ _ (G| φ| f <b γ| g) (selfCoMod) (G| f <b g) linksRedCoModRectangle .

    Definition redCong_RedCoModRectangle_CoMod := redCongCoMod_CoMod redOnce_RedCoModRectangle.
    Definition redCong_RedCoModRectangle_Mod := redCongCoMod_Mod redOnce_RedCoModRectangle.
    
    Hint Constructors redOnce_RedCoModCat1Right redOnce_RedCoModCat1Left redOnce_RedCoModCat2Right redOnce_RedCoModCat2Left redOnce_RedCoModFun1Refl redOnce_RedCoModFun2Refl redOnce_RedCoModFun2Refl_Rev redOnce_RedCoModNatUnit1 redOnce_RedCoModNatUnit2 redOnce_RedCoModRectangle.

    
    (** ** reduceCongMod collects all the redCong_ instances of redCongMod  **)
    
    Reserved Notation "Δ ⊧ f' ↜a f" (at level 70, f' at next level). 
    Reserved Notation "Λ ⊧ g' ↜b g" (at level 70, g' at next level).

    Inductive reduceCongMod : forall A1 A2 (f f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | RedModCat1Right_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n
                                   (* implicit [f] from earlier derivation helps easier ([selfMod _]) description of this input [n] *)
                                   {f' : A1 ⊢a A2} {Δ},
                                   (* output [f'] and [Δ] computed by eauto, always at most one-deterministically, and when node [n] is ok well-formed-for-this-reduction then at least one *)
                                   redCong_RedModCat1Right_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedModCat1Left_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                  redCong_RedModCat1Left_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedModCat2Right_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                   redCong_RedModCat2Right_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedModCat2Left_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                  redCong_RedModCat2Left_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedModFun1Refl_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                  redCong_RedModFun1Refl_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedModFun2Refl_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                  redCong_RedModFun2Refl_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedModFun2Refl_Rev_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                      redCong_RedModFun2Refl_Rev_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedModNatCoUnit1_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                    redCong_RedModNatCoUnit1_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedModNatCoUnit2_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                    redCong_RedModNatCoUnit2_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedModRectangle_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                   redCong_RedModRectangle_Mod n Δ -> Δ ⊧ f' ↜a f

    | RedCoModCat1Right_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                     redCong_RedCoModCat1Right_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedCoModCat1Left_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                    redCong_RedCoModCat1Left_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedCoModCat2Right_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                     redCong_RedCoModCat2Right_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedCoModCat2Left_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                    redCong_RedCoModCat2Left_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedCoModFun1Refl_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                    redCong_RedCoModFun1Refl_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedCoModFun2Refl_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                    redCong_RedCoModFun2Refl_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedCoModFun2Refl_Rev_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                        redCong_RedCoModFun2Refl_Rev_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedCoModNatUnit1_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                    redCong_RedCoModNatUnit1_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedCoModNatUnit2_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                    redCong_RedCoModNatUnit2_Mod n Δ -> Δ ⊧ f' ↜a f
    | RedCoModRectangle_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                                     redCong_RedCoModRectangle_Mod n Δ -> Δ ⊧ f' ↜a f

    where "Δ ⊧ f' ↜a f" := (@reduceCongMod _ _ f f' Δ) : solScope.

    Inductive reduceCongCoMod : forall B1 B2 (g g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop := 
    | RedModCat1Right_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                     redCong_RedModCat1Right_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedModCat1Left_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                    redCong_RedModCat1Left_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedModCat2Right_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                     redCong_RedModCat2Right_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedModCat2Left_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                    redCong_RedModCat2Left_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedModFun1Refl_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                    redCong_RedModFun1Refl_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedModFun2Refl_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                    redCong_RedModFun2Refl_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedModFun2Refl_Rev_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                        redCong_RedModFun2Refl_Rev_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedModNatCoUnit1_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                      redCong_RedModNatCoUnit1_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedModNatCoUnit2_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                      redCong_RedModNatCoUnit2_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedModRectangle_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                     redCong_RedModRectangle_CoMod m Λ -> Λ ⊧ g' ↜b g

    | RedCoModCat1Right_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                       redCong_RedCoModCat1Right_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedCoModCat1Left_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                      redCong_RedCoModCat1Left_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedCoModCat2Right_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                       redCong_RedCoModCat2Right_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedCoModCat2Left_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                      redCong_RedCoModCat2Left_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedCoModFun1Refl_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                      redCong_RedCoModFun1Refl_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedCoModFun2Refl_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                      redCong_RedCoModFun2Refl_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedCoModFun2Refl_Rev_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                          redCong_RedCoModFun2Refl_Rev_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedCoModNatUnit1_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                      redCong_RedCoModNatUnit1_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedCoModNatUnit2_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                      redCong_RedCoModNatUnit2_CoMod m Λ -> Λ ⊧ g' ↜b g
    | RedCoModRectangle_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                                       redCong_RedCoModRectangle_CoMod m Λ -> Λ ⊧ g' ↜b g
    where "Λ ⊧ g' ↜b g" := (@reduceCongCoMod _ _ g g' Λ) : solScope.

    Hint Constructors reduceCongMod reduceCongCoMod.

    (** ** reduceCongMultiMod do multi of reduceCongMod together with extensionality  **)
    
    Reserved Notation "Δ ⊧ f' *↜a f" (at level 70, f' at next level). 
    Reserved Notation "Λ ⊧ g' *↜b g" (at level 70, g' at next level).
    Notation "Δ <<->> Δ0" := (forall nm nm', Δ nm nm' <-> Δ0 nm nm') (at level 95).

    Inductive reduceCongMultiMod : forall A1 A2 (f f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | reduceCongMultiMod_refl : forall {A1 A2} {f : A1 ⊢a A2},
                                  eq ⊧ f *↜a f
    | reduceCongMultiMod_list : forall A1 A2 (f uModTrans : A1 ⊢a A2) Δ,
                                  Δ ⊧ uModTrans ↜a f ->
                                  forall (f'' : A1 ⊢a A2) Δ',
                                    Δ' ⊧ f'' *↜a uModTrans ->
                                    linksRedModTrans Δ Δ' ⊧ f'' *↜a f
    | reduceCongMultiMod_ext : forall A1 A2 (f f' : A1 ⊢a A2) ΔU,
                                 ΔU ⊧ f' *↜a f ->
                                 forall {Δ} {pfExtΔ : Δ <<->> ΔU}, 
                                   Δ ⊧ f' *↜a f
    where "Δ ⊧ f' *↜a f" := (@reduceCongMultiMod _ _ f f' Δ) : solScope.

    Hint Constructors reduceCongMultiMod.
    
    Inductive reduceCongMultiCoMod : forall B1 B2 (g g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop := 
    | reduceCongMultiCoMod_refl : forall {B1 B2} {g : B1 ⊢b B2},
                                    eq ⊧ g *↜b g
    | reduceCongMultiCoMod_list : forall B1 B2 (g uCoModTrans : B1 ⊢b B2) Λ,
                                    Λ ⊧ uCoModTrans ↜b g ->
                                    forall (g'' : B1 ⊢b B2) Λ', Λ' ⊧ g'' *↜b uCoModTrans ->
                                                           linksRedCoModTrans Λ Λ' ⊧ g'' *↜b g
    | reduceCongMultiCoMod_ext : forall B1 B2 (g g' : B1 ⊢b B2) ΛU,
                                   ΛU ⊧ g' *↜b g ->
                                   forall {Λ} {pfΛ : Λ <<->> ΛU}, 
                                     Λ ⊧ g' *↜b g
    where "Λ ⊧ g' *↜b g" := (@reduceCongMultiCoMod _ _ g g' Λ) : solScope.

    Hint Constructors reduceCongMultiCoMod.
    
    (** ** Some lemmas : extensionality of links transformations, for Mod **)

    Local Hint Extern 4 => match goal with
                            | [J : _ <<->> _ |- ((_ : nodesMod _ -> nodesMod _ -> Prop) _ _) ] => eapply J
                            | [J : _ <<->> _ |- ((_ : nodesCoMod _ -> nodesCoMod _ -> Prop) _ _) ] => eapply J
                          end : tacs_ext_links.

    Ltac tac_ext_links :=
      match goal with [ |- _ <<->> _ ] => split; induction 1; firstorder eauto with tacs_ext_links end.
    
    Lemma ext_linksRedModCongRefl : forall B1 B2 (g g' : B1 ⊢b B2) (Λ Λ0: nodesCoMod g -> nodesCoMod g' -> Prop),
                                      Λ <<->> Λ0 -> linksRedModCongRefl Λ <<->> linksRedModCongRefl Λ0.
    Proof.
      intros until 1; tac_ext_links.
    Qed.
    
    Lemma ext_linksRedModCongCoUnit : forall A1 A2 (f f' : A1 ⊢a A2) (Δ Δ' : nodesMod f -> nodesMod f' -> Prop),
                                        Δ <<->> Δ' -> linksRedModCongCoUnit Δ <<->> linksRedModCongCoUnit Δ'.
    Proof.
      intros until 1; tac_ext_links.
    Qed.

    Lemma ext_linksRedModCongComL : forall A2 A3 (f2 f2' : A2 ⊢a A3) (Δ Δ' : nodesMod f2 -> nodesMod f2' -> Prop) {A1} {f1 : A1 ⊢a A2},
                                      Δ <<->> Δ' -> @linksRedModCongComL _ _ _ _ Δ _ f1 <<->> @linksRedModCongComL _ _ _ _ Δ' _ f1.
    Proof.
      intros until 1; tac_ext_links.
    Qed.
    
    Lemma ext_linksRedModCongComR : forall {A2} {A3} {f2 : A2 ⊢a A3} A1 (f1 f1' : A1 ⊢a A2) (Δ Δ' : nodesMod f1 -> nodesMod f1' -> Prop),
                                      Δ <<->> Δ' -> @linksRedModCongComR _ _ f2 _ _ _ Δ <<->> @linksRedModCongComR _ _ f2 _ _ _ Δ'.
    Proof.
      intros until 1; tac_ext_links.
    Qed.

    Lemma ext_linksRedModTrans : forall A1 A2 (uModTrans f : A1 ⊢a A2) (Δ Δ0 : nodesMod f -> nodesMod uModTrans -> Prop) (f'' : A1 ⊢a A2) (Δ' Δ'0 : nodesMod uModTrans -> nodesMod f'' -> Prop),
                                   Δ <<->> Δ0 -> Δ' <<->> Δ'0 -> linksRedModTrans Δ Δ' <<->> linksRedModTrans Δ0 Δ'0 .
    Proof.
      intros until 2; tac_ext_links.
    Qed.

    (** ** Some lemmas : extensionality of links transformations, for CoMod **)
    
    Lemma ext_linksRedCoModCongRefl : forall A1 A2 (f f' : A1 ⊢a A2) (Δ Δ0 : nodesMod f -> nodesMod f' -> Prop),
                                        Δ <<->> Δ0 -> linksRedCoModCongRefl Δ <<->> linksRedCoModCongRefl Δ0.
    Proof.
      intros until 1; tac_ext_links.
    Qed.

    Lemma ext_linksRedCoModCongUnit : forall B1 B2 (g g' : B1 ⊢b B2) (Λ Λ0 : nodesCoMod g -> nodesCoMod g' -> Prop),
                                        Λ <<->> Λ0 -> linksRedCoModCongUnit Λ <<->> linksRedCoModCongUnit Λ0.
    Proof.
      intros until 1; tac_ext_links.
    Qed.

    Lemma ext_linksRedCoModCongComL : forall B2 B3 (g2 g2' : B2 ⊢b B3) (Λ Λ0 : nodesCoMod g2 -> nodesCoMod g2' -> Prop) {B1} {g1 : B1 ⊢b B2},
                                        Λ <<->> Λ0 -> @linksRedCoModCongComL _ _ _ _ Λ B1 g1 <<->> @linksRedCoModCongComL _ _ _ _ Λ0  B1 g1.
    Proof.
      intros until 1; tac_ext_links.
    Qed.
    
    Lemma ext_linksRedCoModCongComR : forall {B2} {B3} {g2 : B2 ⊢b B3} B1 (g1 g1' : B1 ⊢b B2) (Λ Λ0 : nodesCoMod g1 -> nodesCoMod g1' -> Prop),
                                        Λ <<->> Λ0 -> @linksRedCoModCongComR _ B3 g2 _ _ _ Λ <<->> @linksRedCoModCongComR _ B3 g2 _ _ _ Λ0.
    Proof.
      intros until 1; tac_ext_links.
    Qed.

    Lemma ext_linksRedCoModTrans : forall B1 B2 (uCoModTrans g : B1 ⊢b B2) (Λ Λ0 : nodesCoMod g -> nodesCoMod uCoModTrans -> Prop) (g'' : B1 ⊢b B2) (Λ' Λ'0: nodesCoMod uCoModTrans -> nodesCoMod g'' -> Prop),
                                     Λ <<->> Λ0 -> Λ' <<->> Λ'0 -> linksRedCoModTrans Λ Λ' <<->> linksRedCoModTrans Λ0 Λ'0 .
    Proof.
      intros until 2; tac_ext_links.
    Qed.

    (** ** Some lemmas : Derived congruence, for Mod **)

    (**  /!\  THIS DERIVED CONGRUENCE OF MULTI (REFL AND LIST) NATURALLY-REALLY DO HOLD 
              AXIOMATIC (EQ_DEP, UIP) DEPENDENT DESTRUCTION OF THE NODES INDEXEDBY ARROWS (WHICH ARE INDEXED BY OBJECTS)  /!\ **)

    Lemma reduceCongMultiMod_refl_ext : forall {A1 A2} {f : A1 ⊢a A2},
                                        forall {Δ} {pfExtEq : (Δ <<->> eq)},
                                          Δ ⊧ f *↜a f.
    Proof.
      econstructor 3; [econstructor 1 | eassumption].
    Qed.

    Lemma reduceCongMultiMod_list_ext : forall A1 A2 (f uModTrans : A1 ⊢a A2) Δ,
                                          Δ ⊧ uModTrans ↜a f ->
                                          forall (f'' : A1 ⊢a A2) Δ', Δ' ⊧ f'' *↜a uModTrans ->
                                                                 forall {ΔΔ'} {pfExtΔΔ' : ΔΔ' <<->> linksRedModTrans Δ Δ'}, 
                                                                   ΔΔ' ⊧ f'' *↜a f.
    Proof.
      econstructor 3; [econstructor 2 |  ]; eassumption.
    Qed.
    
    Lemma trans_eq_L:
      forall (A1 A2 : ModObjects) (f f'' : A1 ⊢a A2)
        (Δ' : nodesMod f -> nodesMod f'' -> Prop),
        linksRedModTrans eq Δ' <<->> Δ'.
    Proof.
      split.
      - destruct 1; congruence.
      - econstructor;[|eassumption]; reflexivity.
    Qed.

    Lemma trans_list:
      forall (A1 A2 : ModObjects) (f uModTrans : A1 ⊢a A2)
        (Δ : nodesMod f -> nodesMod uModTrans -> Prop) 
        (f'' : A1 ⊢a A2) (Δ' : nodesMod uModTrans -> nodesMod f'' -> Prop)
        (f''0 : A1 ⊢a A2) (Δ'0 : nodesMod f'' -> nodesMod f''0 -> Prop),
        linksRedModTrans (linksRedModTrans Δ Δ') Δ'0 <<->>
                         linksRedModTrans Δ (linksRedModTrans Δ' Δ'0).
    Proof.
      split; intros;
      repeat match goal with [J : linksRedModTrans _ _ _ _ |- _] => destruct J end;
      repeat (eassumption || econstructor).
    Qed.

    Lemma reduceCongMultiMod_trans : forall A1 A2 (f uModTrans : A1 ⊢a A2) Δ,
                                       Δ ⊧ uModTrans *↜a f ->
                                       forall (f'' : A1 ⊢a A2) Δ',
                                         Δ' ⊧ f'' *↜a uModTrans ->
                                         linksRedModTrans Δ Δ' ⊧ f'' *↜a f.
    Proof.
      induction 1.
      - intros; eapply reduceCongMultiMod_ext.
        + eassumption.
        + apply trans_eq_L.
      - intros; eapply reduceCongMultiMod_ext.
        + eapply reduceCongMultiMod_list; [eassumption | ].
          eapply IHreduceCongMultiMod; eassumption.
        + apply trans_list.
      - intros; eapply reduceCongMultiMod_ext.
        + eapply IHreduceCongMultiMod; eassumption.
        + apply ext_linksRedModTrans; [assumption | clear; tauto].
    Qed.

    Lemma reduceCongMultiMod_trans_ext : forall A1 A2 (f uModTrans : A1 ⊢a A2) Δ,
                                           Δ ⊧ uModTrans *↜a f ->
                                           forall (f'' : A1 ⊢a A2) Δ',
                                             Δ' ⊧ f'' *↜a uModTrans ->
                                             forall {ΔΔ'} {pfExtΔΔ' : ΔΔ' <<->> linksRedModTrans Δ Δ'},
                                               ΔΔ' ⊧ f'' *↜a f.
    Proof.
      intros; eapply reduceCongMultiMod_ext.
      - eapply reduceCongMultiMod_trans; eassumption.
      - eassumption.
    Qed.
    
    Lemma trans_eq_R:
      forall (A1 A2 : ModObjects) (f f' : A1 ⊢a A2)
        (Δ : nodesMod f -> nodesMod f' -> Prop),
        Δ <<->> linksRedModTrans Δ eq.
    Proof.
      split.
      - econstructor;[eassumption|]; reflexivity.
      - destruct 1; congruence.
    Qed.

    Lemma reduceCongMultiMod_single :
      forall A1 A2 (f f' : A1 ⊢a A2) Δ,
        Δ ⊧ f' ↜a f -> Δ ⊧ f' *↜a f.
    Proof.
      intros; eapply reduceCongMultiMod_ext. 
      - eapply reduceCongMultiMod_list;
        [eassumption | eapply reduceCongMultiMod_refl].
      - eapply trans_eq_R.
    Qed.
    
    (** ** Some lemmas : Derived congruence, for CoMod **)

    Lemma reduceCongMultiCoMod_refl_ext : forall {B1 B2} {g : B1 ⊢b B2},
                                          forall {Λ} {pfExtEq : (Λ <<->> eq)},
                                            Λ ⊧ g *↜b g.
    Proof.
      econstructor 3; [econstructor 1 | eassumption].
    Qed.

    Lemma reduceCongMultiCoMod_list_ext : forall B1 B2 (g uCoModTrans : B1 ⊢b B2) Λ,
                                            Λ ⊧ uCoModTrans ↜b g ->
                                            forall (g'' : B1 ⊢b B2) Λ', Λ' ⊧ g'' *↜b uCoModTrans ->
                                                                   forall {ΛΛ'} {pfExtΛΛ' : ΛΛ' <<->> linksRedCoModTrans Λ Λ'},
                                                                     ΛΛ' ⊧ g'' *↜b g.
    Proof.
      econstructor 3; [econstructor 2 |  ]; eassumption.
    Qed.

    Lemma transCo_eq_L:
      forall (B1 B2 : CoModObjects) (g g'' : B1 ⊢b B2)
        (Λ' : nodesCoMod g -> nodesCoMod g'' -> Prop),
        linksRedCoModTrans eq Λ' <<->> Λ'.
    Proof.
      split.
      - destruct 1; congruence.
      - econstructor;[|eassumption]; reflexivity.
    Qed.

    Lemma transCo_list:
      forall (B1 B2 : CoModObjects) (g uCoModTrans : B1 ⊢b B2)
        (Λ : nodesCoMod g -> nodesCoMod uCoModTrans -> Prop) 
        (g'' : B1 ⊢b B2) (Λ' : nodesCoMod uCoModTrans -> nodesCoMod g'' -> Prop)
        (g''0 : B1 ⊢b B2) (Λ'0 : nodesCoMod g'' -> nodesCoMod g''0 -> Prop),
        linksRedCoModTrans (linksRedCoModTrans Λ Λ') Λ'0 <<->>
                           linksRedCoModTrans Λ (linksRedCoModTrans Λ' Λ'0).
    Proof.
      split; intros;
      repeat match goal with [J : linksRedCoModTrans _ _ _ _ |- _] => destruct J end;
      repeat (eassumption || econstructor).
    Qed.

    Lemma reduceCongMultiCoMod_trans : forall B1 B2 (g uCoModTrans : B1 ⊢b B2) Λ,
                                         Λ ⊧ uCoModTrans *↜b g ->
                                         forall (g'' : B1 ⊢b B2) Λ', Λ' ⊧ g'' *↜b uCoModTrans ->
                                                                linksRedCoModTrans Λ Λ' ⊧ g'' *↜b g.
    Proof.
      induction 1.
      - intros; eapply reduceCongMultiCoMod_ext.
        + eassumption.
        + apply transCo_eq_L.
      - intros; eapply reduceCongMultiCoMod_ext.
        + eapply reduceCongMultiCoMod_list; [eassumption | ].
          eapply IHreduceCongMultiCoMod; eassumption.
        + apply transCo_list.
      - intros; eapply reduceCongMultiCoMod_ext.
        + eapply IHreduceCongMultiCoMod; eassumption.
        + apply ext_linksRedCoModTrans; [assumption | clear; tauto].
    Qed.

    Lemma reduceCongMultiCoMod_trans_ext : forall B1 B2 (g uCoModTrans : B1 ⊢b B2) Λ,
                                             Λ ⊧ uCoModTrans *↜b g ->
                                             forall (g'' : B1 ⊢b B2) Λ', Λ' ⊧ g'' *↜b uCoModTrans ->
                                                                    forall {ΛΛ'} {pfExtΛΛ' : ΛΛ' <<->> linksRedCoModTrans Λ Λ'},
                                                                      ΛΛ' ⊧ g'' *↜b g.
    Proof.
      intros; eapply reduceCongMultiCoMod_ext.
      - eapply reduceCongMultiCoMod_trans; eassumption.
      - eassumption.
    Qed.

    Lemma transCo_eq_R:
      forall (B1 B2 : CoModObjects) (g g' : B1 ⊢b B2)
        (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
        Λ <<->> linksRedCoModTrans Λ eq.
    Proof.
      split.
      - econstructor;[eassumption|]; reflexivity.
      - destruct 1; congruence.
    Qed.

    Lemma reduceCongMultiCoMod_single : forall B1 B2 (g g' : B1 ⊢b B2) Λ,
                                          Λ ⊧ g' ↜b g -> Λ ⊧ g' *↜b g.
    Proof.
      intros; eapply reduceCongMultiCoMod_ext. 
      - eapply reduceCongMultiCoMod_list;
        [eassumption | eapply reduceCongMultiCoMod_refl].
      - eapply transCo_eq_R.
    Qed.

    (** ** Notations for categorial adjunctions programming **)
    
    (** Unification and type inference  give special notations for programming in categories, special sequencing notation for transitivity,
        /!\ Next: is it possible to internalize into the categorial programming the external [match] and [fix] contained in the cut elimination lemma ? ... /!\ **)

    (** INIT may appear also in the middle of the sequence, such to confirm/check the current arrow **)

    Notation "'INIT' f" := (@reduceCongMultiMod_refl_ext _ _ f eq _) (at level 58).
    Notation "'NOOP'" := (reduceCongMultiMod_refl_ext).
    Notation "r1 ;; r2" := (reduceCongMultiMod_trans_ext r1 r2) (at level 60, right associativity).

    Notation "'cat1r' 'at' n" := (reduceCongMultiMod_single (@RedModCat1Right_Cong_Mod _ _ _ n _ _ _)) (at level 58).
    Notation "'cat1l' 'at' n" := (reduceCongMultiMod_single (@RedModCat1Left_Cong_Mod _ _ _ n _ _ _)) (at level 58).
    Notation "'cat2r' 'at' n" := (reduceCongMultiMod_single (@RedModCat2Right_Cong_Mod _ _ _ n _ _ _)) (at level 58).
    Notation "'cat2l' 'at' n" := (reduceCongMultiMod_single (@RedModCat2Left_Cong_Mod _ _ _ n _ _ _)) (at level 58).
    Notation "'fun1' 'at' n" := (reduceCongMultiMod_single (@RedModFun1Refl_Cong_Mod _ _ _ n _ _ _)) (at level 58).
    Notation "'fun2' 'at' n" := (reduceCongMultiMod_single (@RedModFun2Refl_Cong_Mod _ _ _ n _ _ _)) (at level 58).
    Notation "'fun2rev' 'at' n" := (reduceCongMultiMod_single (@RedModFun2Refl_Rev_Cong_Mod _ _ _ n _ _ _)) (at level 58).
    Notation "'counit1' 'at' n" := (reduceCongMultiMod_single (@RedModNatCoUnit1_Cong_Mod _ _ _ n _ _ _)) (at level 58).
    Notation "'counit2' 'at' n" := (reduceCongMultiMod_single (@RedModNatCoUnit2_Cong_Mod _ _ _ n _ _ _)) (at level 58).
    Notation "'rect' 'at' n" := (reduceCongMultiMod_single (@RedModRectangle_Cong_Mod _ _ _ n _ _ _)) (at level 58).

    Notation "'cat1r' 'at'' n" := (reduceCongMultiCoMod_single (@RedModCat1Right_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
    Notation "'cat1l' 'at'' n" := (reduceCongMultiCoMod_single (@RedModCat1Left_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
    Notation "'cat2r' 'at'' n" := (reduceCongMultiCoMod_single (@RedModCat2Right_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
    Notation "'cat2l' 'at'' n" := (reduceCongMultiCoMod_single (@RedModCat2Left_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
    Notation "'fun1' 'at'' n" := (reduceCongMultiCoMod_single (@RedModFun1Refl_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
    Notation "'fun2' 'at'' n" := (reduceCongMultiCoMod_single (@RedModFun2Refl_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
    Notation "'fun2rev' 'at'' n" := (reduceCongMultiCoMod_single (@RedModFun2Refl_Rev_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
    Notation "'counit1' 'at'' n" := (reduceCongMultiCoMod_single (@RedModNatCoUnit1_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
    Notation "'counit2' 'at'' n" := (reduceCongMultiCoMod_single (@RedModNatCoUnit2_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
    Notation "'rect' 'at'' n" := (reduceCongMultiCoMod_single (@RedModRectangle_Cong_CoMod _ _ _ n _ _ _)) (at level 58).

    Notation "'INIT'' g" := (@reduceCongMultiCoMod_refl_ext _ _ g eq _) (at level 58).
    Notation "'NOOP''" := (reduceCongMultiCoMod_refl_ext).
    Notation "r1 ;;' r2" := (reduceCongMultiCoMod_trans_ext r1 r2) (at level 60, right associativity).

    Notation "'cat1r'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModCat1Right_Cong_CoMod  _ _ _ m _ _ _)) (at level 58).
    Notation "'cat1l'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModCat1Left_Cong_CoMod  _ _ _ m _ _ _)) (at level 58).
    Notation "'cat2r'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModCat2Right_Cong_CoMod  _ _ _ m _ _ _)) (at level 58).
    Notation "'cat2l'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModCat2Left_Cong_CoMod  _ _ _ m _ _ _)) (at level 58).
    Notation "'fun1'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModFun1Refl_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
    Notation "'fun2'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModFun2Refl_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
    Notation "'fun2rev'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModFun2Refl_Rev_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
    Notation "'unit1'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModNatUnit1_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
    Notation "'unit2'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModNatUnit2_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
    Notation "'rect'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModRectangle_Cong_CoMod _ _ _ m _ _ _)) (at level 58).

    Notation "'cat1r'' 'at' m" := (reduceCongMultiMod_single (@RedCoModCat1Right_Cong_Mod  _ _ _ m _ _ _)) (at level 58).
    Notation "'cat1l'' 'at' m" := (reduceCongMultiMod_single (@RedCoModCat1Left_Cong_Mod  _ _ _ m _ _ _)) (at level 58).
    Notation "'cat2r'' 'at' m" := (reduceCongMultiMod_single (@RedCoModCat2Right_Cong_Mod  _ _ _ m _ _ _)) (at level 58).
    Notation "'cat2l'' 'at' m" := (reduceCongMultiMod_single (@RedCoModCat2Left_Cong_Mod  _ _ _ m _ _ _)) (at level 58).
    Notation "'fun1'' 'at' m" := (reduceCongMultiMod_single (@RedCoModFun1Refl_Cong_Mod _ _ _ m _ _ _)) (at level 58).
    Notation "'fun2'' 'at' m" := (reduceCongMultiMod_single (@RedCoModFun2Refl_Cong_Mod _ _ _ m _ _ _)) (at level 58).
    Notation "'fun2rev'' 'at' m" := (reduceCongMultiMod_single (@RedCoModFun2Refl_Rev_Cong_Mod _ _ _ m _ _ _)) (at level 58).
    Notation "'unit1'' 'at' m" := (reduceCongMultiMod_single (@RedCoModNatUnit1_Cong_Mod _ _ _ m _ _ _)) (at level 58).
    Notation "'unit2'' 'at' m" := (reduceCongMultiMod_single (@RedCoModNatUnit2_Cong_Mod _ _ _ m _ _ _)) (at level 58).
    Notation "'rect'' 'at' m" := (reduceCongMultiMod_single (@RedCoModRectangle_Cong_Mod _ _ _ m _ _ _)) (at level 58).

    Check fun m => INIT' G| (φ| (F| _) <a _) ;;' (fun2' at' ( (bottomG (leftComMod (bottomφ (bottomF m))))) ;;' (NOOP' ;;' unit2' at'  ( (bottomγ (bottomG ( _ )))))) .
    Fail Check fun m => INIT' G| (φ| (F| _) <a _) ;;' (fun2' at' ( (bottomG (leftComMod (bottomF m)))) ;;' (NOOP' ;;' unit2' at'  ( (bottomγ (bottomG ( _ )))))) . 
    Check fun m => INIT' G| (φ| (F| _) <a _) ;;' (fun2' at' ( (bottomG (leftComMod (bottomφ (bottomF m))))) ;;' (NOOP' ;;' unit2' at'  ( (bottomγ (bottomG ( _ )))))) ;;' fun1' at' ( (leftComCoMod_Refl _)).
    Check fun n => INIT F| (γ| (G| _) <b _) ;; (fun2 at ( (bottomF (leftComCoMod (bottomγ (bottomG n))))) ;; (NOOP ;; counit2 at ( (bottomφ (bottomF ( _ )))))) .

    Ltac shelveLinks :=
      try match goal with
            | [ |- nodesMod _ -> nodesMod _ -> Prop ] => shelve
            | [ |- nodesCoMod _ -> nodesCoMod _ -> Prop ] => shelve
          end.

    (** *** Example of using automation after notations for categorial adjunctions programming **)

    Lemma example1 : forall A, { f'' : _ & { ΔΔ' : _ | ΔΔ' ⊧ f'' *↜a F| (γ| (G| (@ModIden A) <b G| 1) <b G| 1) }} .
    Proof.
      intros. eexists. eexists.
      refine (fun2' at  ( (bottomF (leftComCoMod (bottomγ  (selfCoMod))))) ;; _).

      Restart. intros. eexists. eexists.
      refine (fun2' at  ( (bottomF (leftComCoMod (bottomγ  (selfCoMod))))) ;; NOOP); shelveLinks;
      repeat (intuition eauto; econstructor).
      Show Proof.
      
      Restart. intros. eexists. eexists.
      refine (fun2' at  ( (bottomF (leftComCoMod (bottomγ  (selfCoMod))))) ;; fun1' at ( (bottomF_Refl (rightComCoMod_Refl selfCoMod_Refl))) ;; NOOP); shelveLinks;
      repeat (intuition eauto; econstructor).
      Show Proof.

      Restart. intros. eexists. eexists.
      refine (INIT F| (γ| (G| (@ModIden A) <b G| 1) <b G| 1) ;; fun2' at  ( (bottomF (leftComCoMod (bottomγ  (selfCoMod))))) ;; NOOP); shelveLinks;
      repeat (intuition eauto; econstructor).
      Show Proof.

      Restart. intros. eexists. eexists.
      refine (INIT F| (γ| (G| (@ModIden A) <b G| 1) <b G| 1) ;; fun2' at  ( (bottomF (leftComCoMod (bottomγ  (selfCoMod))))) ;; fun1' at ( (bottomF_Refl (rightComCoMod_Refl selfCoMod_Refl))) ;; NOOP); shelveLinks;
      repeat (intuition eauto; econstructor).
      Show Proof.

      Restart. intros. eexists. eexists.
      refine (INIT F| (γ| (G| (@ModIden A) <b G| 1) <b G| 1) ;;
                                                             fun2' at  ( (bottomF (leftComCoMod (bottomγ  (selfCoMod))))) ;;
                                                             fun1' at ( (bottomF_Refl (rightComCoMod_Refl selfCoMod_Refl))) ;;
                                                             cat1r at  ( (bottomF (leftComCoMod (bottomγ  (bottomG (selfMod)))))) ;;
                                                             INIT F| (γ| (G| 1) <b '1) ;;
                                                                                       fun1' at ( (bottomF_Refl (leftComCoMod_Refl (bottomγ_Refl  (selfCoMod_Refl))))) ;;
                                                                                       NOOP); shelveLinks;
      repeat (intuition eauto; econstructor).
      Show Proof.
    Qed.

    Print example1.
    
    (** ** Derived congruences on the multi,  for Mod **)

    Lemma cong_F : forall B1 B2 (g' g : B1 ⊢b B2) Λ,  Λ ⊧ g' ↜b g ->
                                                 linksRedModCongRefl Λ ⊧ F| g' ↜a F| g .
    Proof.
      destruct 1;
      [econstructor 1 | econstructor 2 | econstructor 3 | econstructor 4
       | econstructor 5 | econstructor 6 | econstructor 7 | econstructor 8
       | econstructor 9 | econstructor 10 | econstructor 11 | econstructor 12
       | econstructor 13 | econstructor 14 | econstructor 15 | econstructor 16
       | econstructor 17 | econstructor 18 | econstructor 19 | econstructor 20 ];
      ((apply redCongMod_RedModCongRefl ||  apply redCongMod_RedModCongRefl_r ) ||
                                                                                (apply redCongCoMod_RedModCongRefl || apply redCongCoMod_RedModCongRefl_r)) (* alt: constructor 1 *);
      eassumption.
    Qed.

    Lemma cong_eq_linksRedModCongRefl:
      forall B1 B2 (g : B1 ⊢b B2),
        linksRedModCongRefl (eq : (nodesCoMod g -> nodesCoMod g -> Prop)) <<->> eq.
    Proof.
      split.
      - destruct 1; subst; reflexivity.
      - intros <- .
        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
        dep_destruct nm.
        constructor; reflexivity.
    Qed.

    Lemma cong_trans_linksRedModCongRefl:
      forall B1 B2 (g uCoModTrans : B1 ⊢b B2)
        (Λ : nodesCoMod g -> nodesCoMod uCoModTrans -> Prop) 
        (g'' : B1 ⊢b B2) (Λ' : nodesCoMod uCoModTrans -> nodesCoMod g'' -> Prop),
        linksRedModCongRefl (linksRedCoModTrans Λ Λ') <<->>
                            linksRedModTrans (linksRedModCongRefl Λ) (linksRedModCongRefl Λ').
    Proof.
      split.
      - destruct 1 as [? ? H].
        destruct H.
        repeat (eassumption || econstructor).
      - destruct 1 as [? ? H ? H0]. 
        destruct H.
        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
        dep_destruct H0.
        repeat (eassumption || econstructor).
    Qed.

    Lemma cong_F_multi : forall B1 B2 (g' g : B1 ⊢b B2) Λ,  Λ ⊧ g' *↜b g ->
                                                       linksRedModCongRefl Λ ⊧ F| g' *↜a F| g.
    Proof.
      induction 1.
      - eapply reduceCongMultiMod_ext.
        + eapply reduceCongMultiMod_refl.
        + eapply cong_eq_linksRedModCongRefl.
      - eapply reduceCongMultiMod_ext.
        + eapply reduceCongMultiMod_list.
          * eapply cong_F. eassumption.
          * eassumption.
        + apply cong_trans_linksRedModCongRefl .
      - eapply reduceCongMultiMod_ext.
        + eassumption.
        + apply ext_linksRedModCongRefl. assumption.
    Qed.

    Lemma cong_φ : forall A1 A2 (f' f : A1 ⊢a A2) Δ,  Δ ⊧ f' ↜a f ->
                                                 linksRedModCongCoUnit Δ ⊧ φ| f' ↜a φ| f .
    Proof.
      destruct 1;
      [ econstructor 1 | econstructor 2 | econstructor 3 | econstructor 4
        | econstructor 5 | econstructor 6 | econstructor 7 | econstructor 8
        | econstructor 9 | econstructor 10 | econstructor 11 | econstructor 12
        | econstructor 13 | econstructor 14 | econstructor 15 | econstructor 16
        | econstructor 17 | econstructor 18 | econstructor 19 | econstructor 20 ];
      ((apply redCongMod_RedModCongCoUnit ||  apply redCongMod_RedModCongCoUnit_r ) ||
                                                                                    (apply redCongCoMod_RedModCongCoUnit || apply redCongCoMod_RedModCongCoUnit_r)) (* alt: constructor 2 *);
      eassumption.
    Qed.

    Lemma cong_eq_linksRedModCongCoUnit :
      forall A1 A2 (f : A1 ⊢a A2),
        linksRedModCongCoUnit (eq : (nodesMod f -> nodesMod f -> Prop)) <<->> eq.
    Proof.
      split.
      - destruct 1; subst; reflexivity.
      - intros <- .
        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
        dep_destruct nm.
        constructor; reflexivity.
    Qed.

    Lemma cong_trans_linksRedModCongCoUnit :
      forall A1 A2 (f uModTrans : A1 ⊢a A2)
        (Δ : nodesMod f -> nodesMod uModTrans -> Prop) 
        (f'' : A1 ⊢a A2) (Δ' : nodesMod uModTrans -> nodesMod f'' -> Prop),
        linksRedModCongCoUnit (linksRedModTrans Δ Δ') <<->>
                              linksRedModTrans (linksRedModCongCoUnit Δ) (linksRedModCongCoUnit Δ').
    Proof.
      split.
      - destruct 1 as [? ? H].
        destruct H.
        repeat (eassumption || econstructor).
      - destruct 1 as [? ? H ? H0]. 
        destruct H.
        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
        dep_destruct H0.
        repeat (eassumption || econstructor).
    Qed.

    Lemma cong_φ_multi : forall A1 A2 (f' f : A1 ⊢a A2) Δ,  Δ ⊧ f' *↜a f ->
                                                       linksRedModCongCoUnit Δ ⊧ φ| f' *↜a φ| f.
    Proof.
      induction 1.
      - eapply reduceCongMultiMod_ext.
        + eapply reduceCongMultiMod_refl.
        + eapply cong_eq_linksRedModCongCoUnit.
      - eapply reduceCongMultiMod_ext.
        + eapply reduceCongMultiMod_list.
          * eapply cong_φ. eassumption.
          * eassumption.
        + apply cong_trans_linksRedModCongCoUnit .
      - eapply reduceCongMultiMod_ext.
        + eassumption.
        + apply ext_linksRedModCongCoUnit. assumption.
    Qed.

    Lemma cong_ComL : forall A2 A3 (f2 f2' : A2 ⊢a A3) Δ A1 (f1 : A1 ⊢a A2),
                        Δ ⊧ f2' ↜a f2 ->
                        linksRedModCongComL Δ ⊧ (f2' <a f1) ↜a (f2 <a f1) .
    Proof.
      destruct 1;
      [ econstructor 1 | econstructor 2 | econstructor 3 | econstructor 4
        | econstructor 5 | econstructor 6 | econstructor 7 | econstructor 8
        | econstructor 9 | econstructor 10 | econstructor 11 | econstructor 12
        | econstructor 13 | econstructor 14 | econstructor 15 | econstructor 16
        | econstructor 17 | econstructor 18 | econstructor 19 | econstructor 20 ];
      ((apply redCongMod_RedModCongComL ||  apply redCongMod_RedModCongComL_r ) ||
                                                                                (apply redCongCoMod_RedModCongComL || apply redCongCoMod_RedModCongComL_r)) (* alt: constructor 3 *);
      eassumption.
    Qed.

    Lemma cong_eq_linksRedModCongComL :
      forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
        linksRedModCongComL (eq : (nodesMod f2 -> nodesMod f2 -> Prop)) <<->> (eq  : nodesMod (f2 <a f1) -> nodesMod (f2 <a f1) -> Prop).
    Proof.
      split.
      - destruct 1; subst; reflexivity.
      - intros <- .
        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
        dep_destruct nm;
          constructor; reflexivity.
    Qed.

    Lemma cong_trans_linksRedModCongComL :
      forall A2 A3 (f2 f2' : A2 ⊢a A3) Δ (f2'' : A2 ⊢a A3) Δ' A1 (f1 : A1 ⊢a A2),
        linksRedModCongComL (linksRedModTrans Δ Δ') <<->>
                            linksRedModTrans ((linksRedModCongComL Δ) : nodesMod (f2 <a f1) -> nodesMod  (f2' <a f1) -> Prop)
                            ((linksRedModCongComL Δ') : nodesMod (f2' <a f1) -> nodesMod  (f2'' <a f1) -> Prop).
    Proof.
      split.
      - destruct 1 as [ | ? ? H |  ].
        + repeat (eassumption || econstructor).
        + destruct H. repeat (eassumption || econstructor).
        + repeat (eassumption || econstructor).
      - destruct 1 as [? ? H ? H0]. 
        destruct H;
          (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
          dep_destruct H0;
          repeat (eassumption || econstructor).
    Qed.

    Lemma cong_ComL_multi : forall A2 A3 (f2 f2' : A2 ⊢a A3) Δ,
                              Δ ⊧ f2' *↜a f2 ->
                              forall A1 (f1 : A1 ⊢a A2),
                                linksRedModCongComL Δ ⊧ (f2' <a f1) *↜a (f2 <a f1) .
    Proof.
      induction 1; intros.
      - eapply reduceCongMultiMod_ext.
        + eapply reduceCongMultiMod_refl.
        + eapply cong_eq_linksRedModCongComL.
      - eapply reduceCongMultiMod_ext.
        + eapply reduceCongMultiMod_list.
          * eapply cong_ComL. eassumption.
          * apply IHreduceCongMultiMod.
        + apply cong_trans_linksRedModCongComL .
      - eapply reduceCongMultiMod_ext.
        + apply IHreduceCongMultiMod.
        + apply ext_linksRedModCongComL. assumption.
    Qed.
    
    Lemma cong_ComR : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 f1' : A1 ⊢a A2) Δ,
                        Δ ⊧ f1' ↜a f1 ->
                        linksRedModCongComR Δ ⊧ (f2 <a f1') ↜a (f2 <a f1) .
    Proof.
      destruct 1;
      [ econstructor 1 | econstructor 2 | econstructor 3 | econstructor 4
        | econstructor 5 | econstructor 6 | econstructor 7 | econstructor 8
        | econstructor 9 | econstructor 10 | econstructor 11 | econstructor 12
        | econstructor 13 | econstructor 14 | econstructor 15 | econstructor 16
        | econstructor 17 | econstructor 18 | econstructor 19 | econstructor 20 ];
      ((apply redCongMod_RedModCongComR ||  apply redCongMod_RedModCongComR_r ) ||
                                                                                (apply redCongCoMod_RedModCongComR || apply redCongCoMod_RedModCongComR_r)) (* alt: constructor 4 *);
      eassumption.
    Qed.

    Lemma cong_eq_linksRedModCongComR :
      forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
        linksRedModCongComR (eq : (nodesMod f1 -> nodesMod f1 -> Prop)) <<->> (eq  : nodesMod (f2 <a f1) -> nodesMod (f2 <a f1) -> Prop).
    Proof.
      split.
      - destruct 1; subst; reflexivity.
      - intros <- .
        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
        dep_destruct nm;
          constructor; reflexivity.
    Qed.

    Lemma cong_trans_linksRedModCongComR :
      forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 f1' : A1 ⊢a A2) Δ (f1'' : A1 ⊢a A2) Δ',
        linksRedModCongComR (linksRedModTrans Δ Δ') <<->>
                            linksRedModTrans ((linksRedModCongComR Δ) : nodesMod (f2 <a f1) -> nodesMod  (f2 <a f1') -> Prop)
                            ((linksRedModCongComR Δ') : nodesMod (f2 <a f1') -> nodesMod  (f2 <a f1'') -> Prop).
    Proof.
      split.
      - destruct 1 as [ | ? ? H |  ].
        + repeat (eassumption || econstructor).
        + repeat (eassumption || econstructor).
        + destruct H. repeat (eassumption || econstructor).
      - destruct 1 as [? ? H ? H0]. 
        destruct H;
          (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
          dep_destruct H0;
          repeat (eassumption || econstructor).
    Qed.

    Lemma cong_ComR_multi : forall A1 A2 (f1' f1 : A1 ⊢a A2) Δ,
                              Δ ⊧ f1' *↜a f1 ->
                              forall A3 (f2 : A2 ⊢a A3),
                                linksRedModCongComR Δ ⊧ (f2 <a f1') *↜a (f2 <a f1) .
    Proof.
      induction 1; intros.
      - eapply reduceCongMultiMod_ext.
        + eapply reduceCongMultiMod_refl.
        + eapply cong_eq_linksRedModCongComR.
      - eapply reduceCongMultiMod_ext.
        + eapply reduceCongMultiMod_list.
          * eapply cong_ComR. eassumption.
          * apply IHreduceCongMultiMod.
        + apply cong_trans_linksRedModCongComR .
      - eapply reduceCongMultiMod_ext.
        + apply IHreduceCongMultiMod.
        + apply ext_linksRedModCongComR. assumption.
    Qed.

    (** ** Derived congruences on the multi,  for CoMod **)

    Lemma cong_G : forall A1 A2 (f' f : A1 ⊢a A2) Δ,  Δ ⊧ f' ↜a f ->
                                                 linksRedCoModCongRefl Δ ⊧ G| f' ↜b G| f .
    Proof.
      destruct 1;
      [econstructor 1 | econstructor 2 | econstructor 3 | econstructor 4
       | econstructor 5 | econstructor 6 | econstructor 7 | econstructor 8
       | econstructor 9 | econstructor 10 | econstructor 11 | econstructor 12
       | econstructor 13 | econstructor 14 | econstructor 15 | econstructor 16
       | econstructor 17 | econstructor 18 | econstructor 19 | econstructor 20 ];
      ((apply redCongMod_RedCoModCongRefl ||  apply redCongMod_RedCoModCongRefl_r ) ||
                                                                                    (apply redCongCoMod_RedCoModCongRefl || apply redCongCoMod_RedCoModCongRefl_r)) (* alt: constructor 1 *);
      eassumption.
    Qed.

    Lemma cong_eq_linksRedCoModCongRefl:
      forall A1 A2 (f : A1 ⊢a A2),
        linksRedCoModCongRefl (eq : (nodesMod f -> nodesMod f -> Prop)) <<->> eq.
    Proof.
      split.
      - destruct 1; subst; reflexivity.
      - intros <- .
        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
        dep_destruct nm.
        constructor; reflexivity.
    Qed.

    Lemma cong_trans_linksRedCoModCongRefl:
      forall A1 A2 (f uModTrans : A1 ⊢a A2)
        (Δ : nodesMod f -> nodesMod uModTrans -> Prop) 
        (f'' : A1 ⊢a A2) (Δ' : nodesMod uModTrans -> nodesMod f'' -> Prop),
        linksRedCoModCongRefl (linksRedModTrans Δ Δ') <<->>
                              linksRedCoModTrans (linksRedCoModCongRefl Δ) (linksRedCoModCongRefl Δ').
    Proof.
      split.
      - destruct 1 as [? ? H].
        destruct H.
        repeat (eassumption || econstructor).
      - destruct 1 as [? ? H ? H0]. 
        destruct H.
        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
        dep_destruct H0.
        repeat (eassumption || econstructor).
    Qed.

    Lemma cong_G_multi : forall A1 A2 (f' f : A1 ⊢a A2) Λ,  Λ ⊧ f' *↜a f ->
                                                       linksRedCoModCongRefl Λ ⊧ G| f' *↜b G| f.
    Proof.
      induction 1.
      - eapply reduceCongMultiCoMod_ext.
        + eapply reduceCongMultiCoMod_refl.
        + eapply cong_eq_linksRedCoModCongRefl.
      - eapply reduceCongMultiCoMod_ext.
        + eapply reduceCongMultiCoMod_list.
          * eapply cong_G. eassumption.
          * eassumption.
        + apply cong_trans_linksRedCoModCongRefl .
      - eapply reduceCongMultiCoMod_ext.
        + eassumption.
        + apply ext_linksRedCoModCongRefl. assumption.
    Qed.

    Lemma cong_γ : forall B1 B2 (g' g : B1 ⊢b B2) Λ,  Λ ⊧ g' ↜b g ->
                                                 linksRedCoModCongUnit Λ ⊧ γ| g' ↜b γ| g .
    Proof.
      destruct 1;
      [ econstructor 1 | econstructor 2 | econstructor 3 | econstructor 4
        | econstructor 5 | econstructor 6 | econstructor 7 | econstructor 8
        | econstructor 9 | econstructor 10 | econstructor 11 | econstructor 12
        | econstructor 13 | econstructor 14 | econstructor 15 | econstructor 16
        | econstructor 17 | econstructor 18 | econstructor 19 | econstructor 20 ];
      ((apply redCongMod_RedCoModCongUnit ||  apply redCongMod_RedCoModCongUnit_r ) ||
                                                                                    (apply redCongCoMod_RedCoModCongUnit || apply redCongCoMod_RedCoModCongUnit_r)) (* alt: constructor 2 *);
      eassumption.
    Qed.

    Lemma cong_eq_linksRedCoModCongUnit :
      forall B1 B2 (g : B1 ⊢b B2),
        linksRedCoModCongUnit (eq : (nodesCoMod g -> nodesCoMod g -> Prop)) <<->> eq.
    Proof.
      split.
      - destruct 1; subst; reflexivity.
      - intros <- .
        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
        dep_destruct nm.
        constructor; reflexivity.
    Qed.

    Lemma cong_trans_linksRedCoModCongUnit :
      forall B1 B2 (g uCoModTrans : B1 ⊢b B2)
        (Λ : nodesCoMod g -> nodesCoMod uCoModTrans -> Prop) 
        (g'' : B1 ⊢b B2) (Λ' : nodesCoMod uCoModTrans -> nodesCoMod g'' -> Prop),
        linksRedCoModCongUnit (linksRedCoModTrans Λ Λ') <<->>
                              linksRedCoModTrans (linksRedCoModCongUnit Λ) (linksRedCoModCongUnit Λ').
    Proof.
      split.
      - destruct 1 as [? ? H].
        destruct H.
        repeat (eassumption || econstructor).
      - destruct 1 as [? ? H ? H0]. 
        destruct H.
        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
        dep_destruct H0.
        repeat (eassumption || econstructor).
    Qed.

    Lemma cong_γ_multi : forall A1 A2 (g' g : A1 ⊢b A2) Λ,  Λ ⊧ g' *↜b g ->
                                                       linksRedCoModCongUnit Λ ⊧ γ| g' *↜b γ| g.
    Proof.
      induction 1.
      - eapply reduceCongMultiCoMod_ext.
        + eapply reduceCongMultiCoMod_refl.
        + eapply cong_eq_linksRedCoModCongUnit.
      - eapply reduceCongMultiCoMod_ext.
        + eapply reduceCongMultiCoMod_list.
          * eapply cong_γ. eassumption.
          * eassumption.
        + apply cong_trans_linksRedCoModCongUnit .
      - eapply reduceCongMultiCoMod_ext.
        + eassumption.
        + apply ext_linksRedCoModCongUnit. assumption.
    Qed.

    Lemma cong_ComL_CoMod : forall B2 B3 (g2 g2' : B2 ⊢b B3) Λ B1 (g1 : B1 ⊢b B2),
                              Λ ⊧ g2' ↜b g2 ->
                              linksRedCoModCongComL Λ ⊧ (g2' <b g1) ↜b (g2 <b g1) .
    Proof.
      destruct 1;
      [ econstructor 1 | econstructor 2 | econstructor 3 | econstructor 4
        | econstructor 5 | econstructor 6 | econstructor 7 | econstructor 8
        | econstructor 9 | econstructor 10 | econstructor 11 | econstructor 12
        | econstructor 13 | econstructor 14 | econstructor 15 | econstructor 16
        | econstructor 17 | econstructor 18 | econstructor 19 | econstructor 20 ];
      ((apply redCongMod_RedCoModCongComL ||  apply redCongMod_RedCoModCongComL_r ) ||
                                                                                    (apply redCongCoMod_RedCoModCongComL || apply redCongCoMod_RedCoModCongComL_r)) (* alt: constructor 3 *);
      eassumption.
    Qed.

    Lemma cong_eq_linksRedCoModCongComL :
      forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
        linksRedCoModCongComL (eq : (nodesCoMod g2 -> nodesCoMod g2 -> Prop)) <<->> (eq  : nodesCoMod (g2 <b g1) -> nodesCoMod (g2 <b g1) -> Prop).
    Proof.
      split.
      - destruct 1; subst; reflexivity.
      - intros <- .
        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
        dep_destruct nm;
          constructor; reflexivity.
    Qed.

    Lemma cong_trans_linksRedCoModCongComL :
      forall B2 B3 (g2 g2' : B2 ⊢b B3) Λ (g2'' : B2 ⊢b B3) Λ' B1 (g1 : B1 ⊢b B2),
        linksRedCoModCongComL (linksRedCoModTrans Λ Λ') <<->>
                              linksRedCoModTrans ((linksRedCoModCongComL Λ) : nodesCoMod (g2 <b g1) -> nodesCoMod  (g2' <b g1) -> Prop)
                              ((linksRedCoModCongComL Λ') : nodesCoMod (g2' <b g1) -> nodesCoMod  (g2'' <b g1) -> Prop).
    Proof.
      split.
      - destruct 1 as [ | ? ? H |  ].
        + repeat (eassumption || econstructor).
        + destruct H. repeat (eassumption || econstructor).
        + repeat (eassumption || econstructor).
      - destruct 1 as [? ? H ? H0]. 
        destruct H;
          (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
          dep_destruct H0;
          repeat (eassumption || econstructor).
    Qed.

    Lemma cong_ComL_CoMod_multi : forall B2 B3 (g2 g2' : B2 ⊢b B3) Δ,
                                    Δ ⊧ g2' *↜b g2 ->
                                    forall B1 (g1 : B1 ⊢b B2),
                                      linksRedCoModCongComL Δ ⊧ (g2' <b g1) *↜b (g2 <b g1) .
    Proof.
      induction 1; intros.
      - eapply reduceCongMultiCoMod_ext.
        + eapply reduceCongMultiCoMod_refl.
        + eapply cong_eq_linksRedCoModCongComL.
      - eapply reduceCongMultiCoMod_ext.
        + eapply reduceCongMultiCoMod_list.
          * eapply cong_ComL_CoMod. eassumption.
          * apply IHreduceCongMultiCoMod.
        + apply cong_trans_linksRedCoModCongComL .
      - eapply reduceCongMultiCoMod_ext.
        + apply IHreduceCongMultiCoMod.
        + apply ext_linksRedCoModCongComL. assumption.
    Qed.
    
    Lemma cong_ComR_CoMod : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 g1' : B1 ⊢b B2) Λ,
                              Λ ⊧ g1' ↜b g1 ->
                              linksRedCoModCongComR Λ ⊧ (g2 <b g1') ↜b (g2 <b g1) .
    Proof.
      destruct 1;
      [ econstructor 1 | econstructor 2 | econstructor 3 | econstructor 4
        | econstructor 5 | econstructor 6 | econstructor 7 | econstructor 8
        | econstructor 9 | econstructor 10 | econstructor 11 | econstructor 12
        | econstructor 13 | econstructor 14 | econstructor 15 | econstructor 16
        | econstructor 17 | econstructor 18 | econstructor 19 | econstructor 20 ];
      ((apply redCongMod_RedCoModCongComR ||  apply redCongMod_RedCoModCongComR_r ) ||
                                                                                    (apply redCongCoMod_RedCoModCongComR || apply redCongCoMod_RedCoModCongComR_r)) (* alt: constructor 4 *);
      eassumption.
    Qed.

    Lemma cong_eq_linksRedCoModCongComR :
      forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
        linksRedCoModCongComR (eq : (nodesCoMod g1 -> nodesCoMod g1 -> Prop)) <<->> (eq  : nodesCoMod (g2 <b g1) -> nodesCoMod (g2 <b g1) -> Prop).
    Proof.
      split.
      - destruct 1; subst; reflexivity.
      - intros <- .
        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
        dep_destruct nm;
          constructor; reflexivity.
    Qed.

    Lemma cong_trans_linksRedCoModCongComR :
      forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 g1' : B1 ⊢b B2) Λ (g1'' : B1 ⊢b B2) Λ',
        linksRedCoModCongComR (linksRedCoModTrans Λ Λ') <<->>
                              linksRedCoModTrans ((linksRedCoModCongComR Λ) : nodesCoMod (g2 <b g1) -> nodesCoMod  (g2 <b g1') -> Prop)
                              ((linksRedCoModCongComR Λ') : nodesCoMod (g2 <b g1') -> nodesCoMod  (g2 <b g1'') -> Prop).
    Proof.
      split.
      - destruct 1 as [ | ? ? H |  ].
        + repeat (eassumption || econstructor).
        + repeat (eassumption || econstructor).
        + destruct H. repeat (eassumption || econstructor).
      - destruct 1 as [? ? H ? H0]. 
        destruct H;
          (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
          dep_destruct H0;
          repeat (eassumption || econstructor).
    Qed.

    Lemma cong_ComR_CoMod_multi : forall B1 B2 (g1' g1 : B1 ⊢b B2) Λ,
                                    Λ ⊧ g1' *↜b g1 ->
                                    forall B3 (g2 : B2 ⊢b B3),
                                      linksRedCoModCongComR Λ ⊧ (g2 <b g1') *↜b (g2 <b g1) .
    Proof.
      induction 1; intros.
      - eapply reduceCongMultiCoMod_ext.
        + eapply reduceCongMultiCoMod_refl.
        + eapply cong_eq_linksRedCoModCongComR.
      - eapply reduceCongMultiCoMod_ext.
        + eapply reduceCongMultiCoMod_list.
          * eapply cong_ComR_CoMod. eassumption.
          * apply IHreduceCongMultiCoMod.
        + apply cong_trans_linksRedCoModCongComR .
      - eapply reduceCongMultiCoMod_ext.
        + apply IHreduceCongMultiCoMod.
        + apply ext_linksRedCoModCongComR. assumption.
    Qed.
    
    (** ** Completeness lemma of new saturated-congruent reduce relation under the precedent reduce relation,
   is comparable to the development lemma for semiassociativity,
   also is comparable to the filtered/directed colimit technique for presentable objects in categories, which are reflections of free colimits in the polymorphic (Yoneda) representation
   ... memo that another name for filtered colimit is inductive colimit !  **) 

    Lemma terminology_completeness_lemma : (forall A1 A2 (f' f : A1 ⊢a A2),  f' ↜a f -> exists Δ,  Δ ⊧ f' *↜a f) /\ (forall B1 B2 (g' g : B1 ⊢b B2),  g' ↜b g -> exists Λ,  Λ ⊧ g' *↜b g).
    Proof.
      apply reduceMod_reduceCoMod_mutind.
      -  intros * ? [Δ IH]; eexists. apply cong_ComL_multi. eassumption.
      -  intros * ? [Δ IH]; eexists. apply cong_ComR_multi. eassumption.
      -  intros * ? [Δ IH]; eexists. apply cong_F_multi. eassumption.
      -  intros * ? [Δ IH]; eexists. apply cong_φ_multi. eassumption.
      -  intros * ? [Δ IH] * ? [Δ' IH']; eexists. eapply reduceCongMultiMod_trans. eassumption. eassumption.
      -  eexists. eapply reduceCongMultiMod_single;
           (eapply RedModCat1Right_Cong_Mod;
            eapply redCongMod_redOnceMod;
            eapply RedModCat1Right).
      -  eexists. eapply reduceCongMultiMod_single;
           (eapply RedModCat1Left_Cong_Mod;
            eapply redCongMod_redOnceMod;
            eapply RedModCat1Left).
      -  eexists. eapply reduceCongMultiMod_single;
           (eapply RedModFun1Refl_Cong_Mod;
            eapply redCongMod_redOnceMod_r;
            eapply RedModFun1Refl).
      -  eexists. eapply reduceCongMultiMod_single;
           (eapply RedModFun2Refl_Cong_Mod;
            eapply redCongMod_redOnceMod;
            eapply RedModFun2Refl).
      -  eexists. eapply reduceCongMultiMod_single;
           (eapply RedModNatCoUnit1_Cong_Mod;
            eapply redCongMod_redOnceMod;
            eapply RedModNatCoUnit1).
      -  eexists. eapply reduceCongMultiMod_single;
           (eapply RedModNatCoUnit2_Cong_Mod;
            eapply redCongMod_redOnceMod;
            eapply RedModNatCoUnit2).
      -  eexists. eapply reduceCongMultiMod_single;
           (eapply RedModRectangle_Cong_Mod;
            eapply redCongMod_redOnceMod;
            eapply RedModRectangle).

      -  intros * ? [Λ IH]; eexists. apply cong_ComL_CoMod_multi. eassumption.
      -  intros * ? [Λ IH]; eexists. apply cong_ComR_CoMod_multi. eassumption.
      -  intros * ? [Λ IH]; eexists. apply cong_G_multi. eassumption.
      -  intros * ? [Λ IH]; eexists. apply cong_γ_multi. eassumption.
      -  intros * ? [Λ IH] * ? [Λ' IH']; eexists. eapply reduceCongMultiCoMod_trans. eassumption. eassumption.
      -  eexists. eapply reduceCongMultiCoMod_single;
           (eapply RedCoModCat1Right_Cong_CoMod;
            eapply redCongCoMod_redOnceCoMod;
            eapply RedCoModCat1Right).
      -  eexists. eapply reduceCongMultiCoMod_single;
           (eapply RedCoModCat1Left_Cong_CoMod;
            eapply redCongCoMod_redOnceCoMod;
            eapply RedCoModCat1Left).
      -  eexists. eapply reduceCongMultiCoMod_single;
           (eapply RedCoModFun1Refl_Cong_CoMod;
            eapply redCongCoMod_redOnceCoMod_r;
            eapply RedCoModFun1Refl).
      -  eexists. eapply reduceCongMultiCoMod_single;
           (eapply RedCoModFun2Refl_Cong_CoMod;
            eapply redCongCoMod_redOnceCoMod;
            eapply RedCoModFun2Refl).
      -  eexists. eapply reduceCongMultiCoMod_single;
           (eapply RedCoModNatUnit1_Cong_CoMod;
            eapply redCongCoMod_redOnceCoMod;
            eapply RedCoModNatUnit1).
      -  eexists. eapply reduceCongMultiCoMod_single;
           (eapply RedCoModNatUnit2_Cong_CoMod;
            eapply redCongCoMod_redOnceCoMod;
            eapply RedCoModNatUnit2).
      -  eexists. eapply reduceCongMultiCoMod_single;
           (eapply RedCoModRectangle_Cong_CoMod;
            eapply redCongCoMod_redOnceCoMod;
            eapply RedCoModRectangle).
    Qed.
    
    (** ** Soundness lemma of new saturated-congruent reduce relation for the original conversion relation,
        lengthy because the final relations [reduceCongMultiMod] and  [reduceCongMultiCoMod] are not defined mutually **) 

    Lemma terminology_soundness_RedModCat1Right:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedModCat1Right_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedModCat1Right_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongMod_Mod_redCongMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedModCat1Left:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedModCat1Left_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedModCat1Left_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongMod_Mod_redCongMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedModCat2Right:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedModCat2Right_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedModCat2Right_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongMod_Mod_redCongMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedModCat2Left:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedModCat2Left_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedModCat2Left_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongMod_Mod_redCongMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedModFun1Refl:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesReflMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedModFun1Refl_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesReflCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedModFun1Refl_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongMod_Mod_redCongMod_CoMod_mutind_r;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedModFun2Refl:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedModFun2Refl_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedModFun2Refl_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongMod_Mod_redCongMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedModFun2Refl_Rev:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedModFun2Refl_Rev_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedModFun2Refl_Rev_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongMod_Mod_redCongMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedModNatCoUnit1:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedModNatCoUnit1_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedModNatCoUnit1_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongMod_Mod_redCongMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedModNatCoUnit2:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedModNatCoUnit2_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedModNatCoUnit2_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongMod_Mod_redCongMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedModRectangle:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedModRectangle_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedModRectangle_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongMod_Mod_redCongMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedCoModCat1Right:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedCoModCat1Right_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedCoModCat1Right_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongCoMod_Mod_redCongCoMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedCoModCat1Left:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedCoModCat1Left_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedCoModCat1Left_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongCoMod_Mod_redCongCoMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedCoModCat2Right:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedCoModCat2Right_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedCoModCat2Right_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongCoMod_Mod_redCongCoMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedCoModCat2Left:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedCoModCat2Left_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedCoModCat2Left_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongCoMod_Mod_redCongCoMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedCoModFun1Refl:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesReflMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedCoModFun1Refl_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesReflCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedCoModFun1Refl_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongCoMod_Mod_redCongCoMod_CoMod_mutind_r;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedCoModFun2Refl:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedCoModFun2Refl_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedCoModFun2Refl_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongCoMod_Mod_redCongCoMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedCoModFun2Refl_Rev:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedCoModFun2Refl_Rev_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedCoModFun2Refl_Rev_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongCoMod_Mod_redCongCoMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedCoModNatUnit1:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedCoModNatUnit1_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedCoModNatUnit1_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongCoMod_Mod_redCongCoMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedCoModNatUnit2:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedCoModNatUnit2_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedCoModNatUnit2_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongCoMod_Mod_redCongCoMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_RedCoModRectangle:
      (forall (A1 A2 : ModObjects) (f : A1 ⊢a A2) (n : nodesMod f)
         (f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop),
         redCong_RedCoModRectangle_Mod n Δ -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g : B1 ⊢b B2) (m : nodesCoMod g)
         (g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop),
         redCong_RedCoModRectangle_CoMod m Λ -> g' ≈b g).
    Proof.
      apply redCongCoMod_Mod_redCongCoMod_CoMod_mutind;
      eauto.
      destruct 1; eauto.
    Qed.

    Lemma terminology_soundness_lemma_single:
      (forall (A1 A2 : ModObjects) (f f' : A1 ⊢a A2)
         (Δ : nodesMod f -> nodesMod f' -> Prop), Δ ⊧ f' ↜a f -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g g' : B1 ⊢b B2)
         (Λ : nodesCoMod g -> nodesCoMod g' -> Prop), Λ ⊧ g' ↜b g -> g' ≈b g).
    Proof.
      split; [
        destruct 1; [
          eapply terminology_soundness_RedModCat1Right; eassumption |
          eapply terminology_soundness_RedModCat1Left; eassumption |
          eapply terminology_soundness_RedModCat2Right; eassumption |
          eapply terminology_soundness_RedModCat2Left; eassumption |
          eapply terminology_soundness_RedModFun1Refl; eassumption |
          eapply terminology_soundness_RedModFun2Refl; eassumption |
          eapply terminology_soundness_RedModFun2Refl_Rev; eassumption |
          eapply terminology_soundness_RedModNatCoUnit1; eassumption |
          eapply terminology_soundness_RedModNatCoUnit2; eassumption |
          eapply terminology_soundness_RedModRectangle; eassumption |
          eapply terminology_soundness_RedCoModCat1Right; eassumption |
          eapply terminology_soundness_RedCoModCat1Left; eassumption |
          eapply terminology_soundness_RedCoModCat2Right; eassumption |
          eapply terminology_soundness_RedCoModCat2Left; eassumption |
          eapply terminology_soundness_RedCoModFun1Refl; eassumption |
          eapply terminology_soundness_RedCoModFun2Refl; eassumption |
          eapply terminology_soundness_RedCoModFun2Refl_Rev; eassumption |
          eapply terminology_soundness_RedCoModNatUnit1; eassumption |
          eapply terminology_soundness_RedCoModNatUnit2; eassumption |
          eapply terminology_soundness_RedCoModRectangle; eassumption ]
                      .. ].
    Qed.
    
    Lemma terminology_soundness_lemma:
      (forall (A1 A2 : ModObjects) (f f' : A1 ⊢a A2)
         (Δ : nodesMod f -> nodesMod f' -> Prop), Δ ⊧ f' *↜a f -> f' ≈a f) /\
      (forall (B1 B2 : CoModObjects) (g g' : B1 ⊢b B2)
         (Λ : nodesCoMod g -> nodesCoMod g' -> Prop), Λ ⊧ g' *↜b g -> g' ≈b g).
    Proof.
      split.
      - induction 1.
        + apply ModRefl.
        + eapply ModTrans; [ | eassumption].
          eapply terminology_soundness_lemma_single. eassumption.
        + assumption.
      - induction 1.
        + apply CoModRefl.
        + eapply CoModTrans; [ | eassumption].
          eapply terminology_soundness_lemma_single. eassumption.
        + assumption.
    Qed.

    (** ** Degradation lemmas for nodes **) 
    
    Definition gradeNode : (forall A1 A2 (f : A1 ⊢a A2) (n : nodesMod f), nat) * (forall B1 B2 (g : B1 ⊢b B2) (m : nodesCoMod g), nat).
    Proof.
      apply nodesMod_nodesCoMod_mutrec.
      - intros * f2 * f1. refine (gradeMod (f2 <a f1)).
      - intros; assumption.
      - intros; assumption.
      - intros; assumption.
      - intros; assumption.
      - intros * g2 * g1. refine (gradeCoMod (g2 <b g1)).
      - intros; assumption.
      - intros; assumption.
      - intros; assumption.
      - intros; assumption.
    Defined.
    
    Definition gradeNodeMod : (forall A1 A2 (f : A1 ⊢a A2) (n : nodesMod f), nat).
    Proof.
      apply gradeNode.
    Defined.
    
    Definition gradeNodeCoMod :  (forall B1 B2 (g : B1 ⊢b B2) (m : nodesCoMod g), nat).
    Proof.
      apply gradeNode.
    Defined.

    (** These rewrite lemmas to avoid COQ bug where [simpl] or [cbn] do not progress well **)
    
    Definition rew_gradeNodeMod_selfMod : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2), gradeNodeMod (selfMod : nodesMod (f2 <a f1)) = gradeMod (f2 <a f1).
    Proof.
      reflexivity.
    Defined.

    Definition rew_gradeNodeMod_bottomF : forall B1 B2 (g : B1 ⊢b B2) (m : nodesCoMod g), gradeNodeMod (bottomF m) = gradeNodeCoMod m.
    Proof.
      reflexivity.
    Defined.

    Definition rew_gradeNodeMod_bottomφ : forall A1 A2 (f : A1 ⊢a A2) (n : nodesMod f), gradeNodeMod (bottomφ n) = gradeNodeMod n.
    Proof.
      reflexivity.
    Defined.

    Definition rew_gradeNodeMod_leftComMod : forall A1 A2 (f1 : A1 ⊢a A2) A3 (f2 : A2 ⊢a A3) (n2 : nodesMod f2), gradeNodeMod (leftComMod n2 : nodesMod (f2 <a f1)) = gradeNodeMod n2.
    Proof.
      reflexivity.
    Defined.
    
    Definition rew_gradeNodeMod_rightComMod : forall A1 A2 (f1 : A1 ⊢a A2) (n1 : nodesMod f1) A3 (f2 : A2 ⊢a A3), gradeNodeMod(rightComMod n1 : nodesMod (f2 <a f1)) = gradeNodeMod n1.
    Proof.
      reflexivity.
    Defined.

    Definition rew_gradeNodeCoMod_selfCoMod : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2), gradeNodeCoMod (selfCoMod :  nodesCoMod (g2 <b g1)) = gradeCoMod (g2 <b g1).
    Proof.
      reflexivity.
    Defined.

    Definition rew_gradeNodeCoMod_bottomG : forall A1 A2 (f : A1 ⊢a A2) (n : nodesMod f), gradeNodeCoMod (bottomG n) = gradeNodeMod n.
    Proof.
      reflexivity.
    Defined.

    Definition rew_gradeNodeCoMod_bottomγ : forall B1 B2 (g : B1 ⊢b B2) (m : nodesCoMod g), gradeNodeCoMod (bottomγ m) = gradeNodeCoMod m.
    Proof.
      reflexivity.
    Defined.

    Definition rew_gradeNodeCoMod_leftComCoMod : forall B1 B2 (g1 : B1 ⊢b B2) B3 (g2 : B2 ⊢b B3) (m2 : nodesCoMod g2), gradeNodeCoMod (leftComCoMod m2 : nodesCoMod (g2 <b g1)) = gradeNodeCoMod m2.
    Proof.
      reflexivity.
    Defined.

    Definition rew_gradeNodeCoMod_rightComCoMod : forall B1 B2 (g1 : B1 ⊢b B2) (m1 : nodesCoMod g1) B3 (g2 : B2 ⊢b B3), gradeNodeCoMod (rightComCoMod m1 : nodesCoMod (g2 <b g1)) = gradeNodeCoMod m1.
    Proof.
      reflexivity.
    Defined.
    
    Hint Rewrite rew_gradeNodeMod_selfMod rew_gradeNodeMod_bottomF rew_gradeNodeMod_bottomφ rew_gradeNodeMod_leftComMod rew_gradeNodeMod_rightComMod
         rew_gradeNodeCoMod_selfCoMod rew_gradeNodeCoMod_bottomG rew_gradeNodeCoMod_bottomγ rew_gradeNodeCoMod_leftComCoMod rew_gradeNodeCoMod_rightComCoMod .

    (* TODO: change NatCoUnit2 to Nat2CoUnit and NatCoUnit1 to Nat1CoUnit and NatUnit2 to Nat2Unit and NatUnit1 to Nat1Unit ... 
   make [UACom] maximal implicit in [ModCom] ? *)

    (** Memo that [solveCongMod] do elim to [Type] not [Set], therefore [ModArrows] and [nodesMod] are in [Type] contrasted to [ModObjects] in [Set] **)

    Fixpoint solveCongMod len {struct len} : forall A1 A2 (f : A1 ⊢a A2) (n : nodesMod f) (H_gradeNodeTotalMod : gradeMod f + gradeNodeMod n <= len),
                                               { fSol : A1 ⊢a A2 & { Δ : nodesMod f ->  nodesMod fSol -> Prop |
                                                                     Δ ⊧ fSol *↜a f /\ forall n', ~ Δ n n' }}
    with solveCongCoMod len {struct len} : forall B1 B2 (g : B1 ⊢b B2) (m : nodesCoMod g) (H_gradeNodeTotalCoMod : gradeCoMod g + gradeNodeCoMod m <= len),
                                             { gSol : B1 ⊢b B2 & { Λ : nodesCoMod g ->  nodesCoMod gSol -> Prop |
                                                                   Λ ⊧ gSol *↜b g /\ forall m', ~ Λ m m' }}.
    Proof.
      (* solveCongMod *)
      { destruct len.
        
        (* len is O *)
        - clear; intros until 1; exfalso; generalize (degradeMod_ge_one f); Omega.omega.

        (* len is (S len) *)
        - intros; destruct n as  [A2 A3 f2 A1 f1 | B1 B2 g m | A1 A2 f n | A1 A2 f1 A3 f2 n | A1 A2 f1 n A3 f2 ].

          (* n is selfMod (f2 <a f1) *)
          + destruct f1 as [A1 | B1 B2 g1 | A1' A2 f1' | A12 A2 f1'2 A1 f1'1].

            (*  (f2 <a 1) , instance of (f2 <a f1), instance of f *)
            * exists (f2) , (linksRedModCat1Right) .
              { split.
                - apply reduceCongMultiMod_single.
                  eapply RedModCat1Right_Cong_Mod.
                  apply redCongMod_redOnceMod.
                  apply RedModCat1Right. 
                - intros * Hlink.
                  inversion Hlink.
              }
              
            (*  (f2 <a F| g1) , instance of (f2 <a f1) , instance of f *)
            * { tac_ModArrows_dep_destruct f2;
                try rename A_ into A3;
                try rename B1_ into B2,  B2_ into B3,  g_ into g2;
                try rename A1_ into A2', A2_ into A3', f_ into f2';
                try rename A2_ into A23', A3_ into A3', f2_ into f2'2, f1_ into f2'1; try rename A1_ into A2'.
                
                (*  (1 <a F| g1) , instance of (f2 <a F| g1) , instance of (f2 <a f1) , instance of f *)
                - exists (F| g1) , (linksRedModCat1Left) .
                  { split.
                    - apply reduceCongMultiMod_single.
                      eapply RedModCat1Left_Cong_Mod.
                      apply redCongMod_redOnceMod.
                      apply RedModCat1Left. 
                    - intros * Hlink.
                      inversion Hlink.
                  }

                (*  (F| g2 <a F| g1) , instance of (f2 <a F| g1) , instance of (f2 <a f1) , instance of f *)
                - generalize (solveCongCoMod len _ _ _ (selfCoMod : nodesCoMod (g2 <b g1))); intros (g2_o_g1_Sol, (Λ, (g2_o_g1_Sol_prop_reduce, g2_o_g1_Sol_prop_desintegration))).  
                  + clear -H_gradeNodeTotalMod. rewriter. Omega.omega.
                  + exists (F| g2_o_g1_Sol), (linksRedModTrans (linksRedModFun2Refl) (linksRedModCongRefl Λ)) .
                    { split.
                      - eapply reduceCongMultiMod_list.
                        + (eapply RedModFun2Refl_Cong_Mod;
                           apply redCongMod_redOnceMod;
                           apply RedModFun2Refl).
                        + apply cong_F_multi. eassumption.
                      - intros * Hlink.
                        inversion Hlink as [ ? n1 Hlink0 ? Hlink1]; clear Hlink; subst.
                        destruct Hlink1 as [ ? ? Hlink1' ].
                        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                        dep_destruct Hlink0.
                        eapply g2_o_g1_Sol_prop_desintegration. eassumption.
                    }

                (*  (φ| f2' <a F| g1) , instance of (f2 <a F| g1) , instance of (f2 <a f1) , instance of f *)
                -  tac_CoModArrows_dep_destruct g1;
                  try rename B_ into B1;
                  try rename A1_ into A1, A2_ into A2, f_ into f1';
                  try rename B1_ into B1, B2_ into B2, g_ into g1';
                  try rename B2_ into B12', g2_ into g1'2, B1_ into B1, g1_ into g1'1; try rename B3_ into B2'.
                   
                   (*  (φ| f2' <a F| '1) , instance of (f2 <a F| g1) , instance of (f2 <a f1) , instance of f *)
                   + (* choice here is by single step only ... note that for total solveMod double step was held *)
                     generalize (solveCongMod len _ _ _ (selfMod : nodesMod (φ| f2' <a 1))); intros (φ_f2'_o_1_Sol, (Δ, (φ_f2'_o_1_Sol_prop_reduce, φ_f2'_o_1_Sol_prop_desintegration))).  
                     * clear -H_gradeNodeTotalMod. rewriter. Omega.omega.
                     * exists (φ_f2'_o_1_Sol), (linksRedModTrans (linksRedModCongComR linksRedModFun1Refl) (Δ)) .
                       { split.
                         - eapply reduceCongMultiMod_list.
                           + (eapply RedModFun1Refl_Cong_Mod;
                              apply redCongMod_RedModCongComR_r;
                              apply redCongMod_redOnceMod_r;
                              apply RedModFun1Refl).
                           + assumption.
                         - intros * Hlink.
                           inversion Hlink as [ ? n1 Hlink0 ? Hlink1]; clear Hlink; subst.
                           inversion Hlink0; clear Hlink0; subst.
                           eapply φ_f2'_o_1_Sol_prop_desintegration. eassumption.
                       }
                       
                   (*  (φ| f2' <a F| G| f1') , instance of (f2 <a F| g1) , instance of (f2 <a f1) , instance of f *)
                   + generalize (solveCongMod len _ _ _ (selfMod : nodesMod (f2' <a f1'))); intros (f2'_o_f1'_Sol, (Δ, (f2'_o_f1'_Sol_prop_reduce, f2'_o_f1_Sol_prop_desintegration))).  
                     * clear -H_gradeNodeTotalMod. rewriter. Omega.omega.
                     * exists (φ| f2'_o_f1'_Sol), (linksRedModTrans (linksRedModNatCoUnit2) (linksRedModCongCoUnit Δ)) .
                       { split.
                         - eapply reduceCongMultiMod_list.
                           + (eapply RedModNatCoUnit2_Cong_Mod;
                              apply redCongMod_redOnceMod;
                              apply RedModNatCoUnit2).
                           + apply cong_φ_multi. assumption.
                         - intros * Hlink.
                           inversion Hlink as [ ? n1 Hlink0 ? Hlink1]; clear Hlink; subst.
                           destruct Hlink1 as [ ? ? Hlink1' ].
                           (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                           dep_destruct Hlink0.
                           eapply f2'_o_f1_Sol_prop_desintegration. eassumption.
                       }
                       
                   (*  (φ| f2' <a F| γ| g1') , instance of (f2 <a F| g1) , instance of (f2 <a f1) , instance of f *)
                   + generalize (solveCongMod len _ _ _ (selfMod : nodesMod (f2' <a F| g1'))); intros (f2'_o_F_g1'_Sol, (Δ, (f2'_o_F_g1'_Sol_prop_reduce, f2'_o_F_g1'_Sol_prop_desintegration))).  
                     * clear -H_gradeNodeTotalMod. rewriter. Omega.omega.
                     * exists (f2'_o_F_g1'_Sol), (linksRedModTrans (linksRedModRectangle) (Δ)) .
                       { split.
                         - eapply reduceCongMultiMod_list.
                           + (eapply RedModRectangle_Cong_Mod;
                              apply redCongMod_redOnceMod;
                              apply RedModRectangle).
                           + assumption.
                         - intros * Hlink.
                           inversion Hlink as [ ? n1 Hlink0 ? Hlink1]; clear Hlink; subst.
                           inversion Hlink0; subst; clear Hlink0.
                           eapply f2'_o_F_g1'_Sol_prop_desintegration. eassumption.
                       }

                   (*  (φ| f2' <a F| (g1'2 <b g1'1)) , instance of (f2 <a F| g1) , instance of (f2 <a f1) , instance of f *)
                   + generalize (solveCongMod len _ _ _ (selfMod : nodesMod (φ| f2' <a F| g1'2))); intros (φ_f2'_o_F_g1'2_Sol, (Δ, (φ_f2'_o_F_g1'2_Sol_prop_reduce, φ_f2'_o_F_g1'2_Sol_prop_desintegration))).
                     * clear -H_gradeNodeTotalMod. rewriter. Omega.omega.
                     * exists (φ_f2'_o_F_g1'2_Sol <a F| g1'1) , (linksRedModTrans (linksRedModCongComR linksRedModFun2Refl_Rev) (linksRedModTrans linksRedModCat2Right (linksRedModCongComL Δ))) . 
                       { split.
                         - eapply reduceCongMultiMod_list.
                           + (eapply RedModFun2Refl_Rev_Cong_Mod;
                              apply redCongMod_RedModCongComR;
                              apply redCongMod_redOnceMod;
                              apply RedModFun2Refl_Rev).
                           + eapply reduceCongMultiMod_list.
                             * (eapply RedModCat2Right_Cong_Mod;
                                apply redCongMod_redOnceMod;
                                apply RedModCat2Right).
                             * apply cong_ComL_multi. assumption.
                         - intros * Hlink.
                           inversion Hlink as [ ? ? Hlink0 ? Hlink1 ]; clear Hlink; subst.
                           inversion Hlink1 as [ ? ? Hlink10 ? Hlink11 ]; clear Hlink1; subst.
                           
                           inversion Hlink0; subst.
                           inversion Hlink10; subst.
                           dep_destruct Hlink11.
                           eapply φ_f2'_o_F_g1'2_Sol_prop_desintegration. eassumption.                            
                       }

                (*  ((f2'2 <a f2'1) <a F| g1) , instance of (f2 <a F| g1) , instance of (f2 <a f1) , instance of f )*)
                - generalize (solveCongMod len _ _ _ (selfMod : nodesMod (f2'1 <a F| g1))); intros (f2'1_o_F_g1_Sol, (Δ, (f2'1_o_F_g1_Sol_prop_reduce, f2'1_o_F_g1_Sol_prop_desintegration))).
                  + clear -H_gradeNodeTotalMod. rewriter. Omega.omega.
                  + exists (f2'2 <a f2'1_o_F_g1_Sol), (linksRedModTrans (linksRedModCat2Left) (linksRedModCongComR Δ)) .
                    { split.
                      - eapply reduceCongMultiMod_list.
                        + (eapply RedModCat2Left_Cong_Mod;
                           apply redCongMod_redOnceMod;
                           apply RedModCat2Left).
                        + apply cong_ComR_multi. assumption.
                      - intros * Hlink.
                        inversion Hlink as [ ? n1 Hlink0 ? Hlink1]; clear Hlink; subst.
                        inversion Hlink0; subst.  dep_destruct Hlink1.
                        eapply f2'1_o_F_g1_Sol_prop_desintegration. eassumption.
                    }
              }

            (*  (f2 <a φ| f1') , instance of (f2 <a f1) , instance of f *)
            * { generalize (solveCongMod len _ _ _ (selfMod : nodesMod (f2 <a f1'))); intros (f2_o_f1'_Sol, (Δ, (f2_o_f1'_Sol_prop_reduce, f2_o_f1_Sol_prop_desintegration))).  
                * clear -H_gradeNodeTotalMod. rewriter. Omega.omega.
                * exists (φ| f2_o_f1'_Sol), (linksRedModTrans (linksRedModNatCoUnit1) (linksRedModCongCoUnit Δ)) .
                  { split.
                    - eapply reduceCongMultiMod_list.
                      + (eapply RedModNatCoUnit1_Cong_Mod;
                         apply redCongMod_redOnceMod;
                         apply RedModNatCoUnit1).
                      + apply cong_φ_multi. assumption.
                    - intros * Hlink.
                      inversion Hlink as [ ? n1 Hlink0 ? Hlink1]; clear Hlink; subst.
                      destruct Hlink1 as [ ? ? Hlink1' ].
                      (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                      dep_destruct Hlink0.
                      eapply f2_o_f1_Sol_prop_desintegration. eassumption.
                  }
              }

            (*  (f2 <a (f1'2 <a f1'1)) ,  instance of (f2 <a f1) ,  instance of f )*)
            * { generalize (solveCongMod len _ _ _ (selfMod : nodesMod (f2 <a f1'2))); intros (f2_o_f1'2_Sol, (Δ, (f2_o_f1'2_Sol_prop_reduce, f2_o_f1'2_Sol_prop_desintegration))).
                * clear -H_gradeNodeTotalMod. rewriter. Omega.omega.
                * exists (f2_o_f1'2_Sol <a f1'1), (linksRedModTrans (linksRedModCat2Right) (linksRedModCongComL Δ)) .
                  { split.
                    - eapply reduceCongMultiMod_list.
                      + (eapply RedModCat2Right_Cong_Mod;
                         apply redCongMod_redOnceMod;
                         apply RedModCat2Right).
                      + apply cong_ComL_multi. assumption.
                    - intros * Hlink.
                      inversion Hlink as [ ? n1 Hlink0 ? Hlink1]; clear Hlink; subst.
                      inversion Hlink0; subst.
                      dep_destruct Hlink1.
                      eapply f2_o_f1'2_Sol_prop_desintegration. eassumption.
                  }
              }
              
          (* n is (bottomF m) *)
          + generalize (solveCongCoMod len _ _ _ m); intros (g_Sol, (Λ, (g_Sol_prop_reduce, g_Sol_prop_desintegration))).  
            * clear -H_gradeNodeTotalMod. autorewrite with core  in H_gradeNodeTotalMod. Omega.omega. 
            * exists (F| g_Sol), (linksRedModCongRefl Λ) .
              { split.
                - apply cong_F_multi. assumption.
                - intros * Hlink.
                  (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                  dep_destruct Hlink.
                  eapply g_Sol_prop_desintegration. eassumption.
              }

          (* n is (bottomφ n) *)
          + generalize (solveCongMod len _ _ _ n); intros (f_Sol, (Δ, (f_Sol_prop_reduce, f_Sol_prop_desintegration))).  
            * clear -H_gradeNodeTotalMod. autorewrite with core  in H_gradeNodeTotalMod. Omega.omega. 
            * exists (φ| f_Sol), (linksRedModCongCoUnit Δ) .
              { split.
                - apply cong_φ_multi. assumption.
                - intros * Hlink.
                  (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                  dep_destruct Hlink.
                  eapply f_Sol_prop_desintegration. eassumption.
              }
              
          (* n is (leftComMod n) *)
          + generalize (solveCongMod len _ _ _ n); intros (f2_Sol, (Δ, (f2_Sol_prop_reduce, f2_Sol_prop_desintegration))).  
            * clear -H_gradeNodeTotalMod. autorewrite with core  in H_gradeNodeTotalMod. Omega.omega. 
            * exists (f2_Sol <a f1), (linksRedModCongComL Δ) .
              { split.
                - apply cong_ComL_multi. assumption.
                - intros * Hlink.
                  (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                  dep_destruct Hlink.
                  eapply f2_Sol_prop_desintegration. eassumption.
              }

          (* n is (rightComMod n) *)
          + generalize (solveCongMod len _ _ _ n); intros (f1_Sol, (Δ, (f1_Sol_prop_reduce, f1_Sol_prop_desintegration))).  
            * clear -H_gradeNodeTotalMod. autorewrite with core  in H_gradeNodeTotalMod. Omega.omega. 
            * exists (f2 <a f1_Sol), (linksRedModCongComR Δ) .
              { split.
                - apply cong_ComR_multi. assumption.
                - intros * Hlink.
                  (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                  dep_destruct Hlink.
                  eapply f1_Sol_prop_desintegration. eassumption.
              }
      }

      (* solveCongCoMod *)
      { destruct len.

        (* len is O *)
        - clear; intros until 1; exfalso; generalize (degradeCoMod_ge_one g); Omega.omega.

        (* len is (S len) *)
        - intros; destruct m as  [B2 B3 g2 B1 g1 | A1 A2 f n | B1 B2 g m | B1 B2 g1 B3 g2 m | B1 B2 g1 m B3 g2 ].

          (* m is selfCoMod (g2 <a g1) *)
          + destruct g2 as [B2 | A2 A3 f2 | B2 B3' g2' | B23 B3 g2'2 B2 g2'1].

            (*  (1 <b g1) , instance of (g2 <b g1), instance of g *)
            * exists (g1) , (linksRedCoModCat1Left) .
              { split.
                - apply reduceCongMultiCoMod_single.
                  eapply RedCoModCat1Left_Cong_CoMod.
                  apply redCongCoMod_redOnceCoMod.
                  apply RedCoModCat1Left. 
                - intros * Hlink.
                  inversion Hlink.
              }
              
            (*  (G| f2 <b g1) , instance of (g2 <b g1) , instance of g *)
            * { tac_CoModArrows_dep_destruct g1;
                try rename B_ into B1;
                try rename A1_ into A1', A2_ into A2', f_ into f1;
                try rename B1_ into B1, B2_ into B2', g_ into g1';
                try rename B2_ into B12, g2_ into g1'2, B1_ into B1, g1_ into g1'1; try rename B3_ into B2.

                (*  (G| f2 <b 1) , instance of (g2 <b g1) , instance of g *)
                - exists (G| f2) , (linksRedCoModCat1Right) .
                  { split.
                    - apply reduceCongMultiCoMod_single.
                      eapply RedCoModCat1Right_Cong_CoMod.
                      apply redCongCoMod_redOnceCoMod.
                      apply RedCoModCat1Right. 
                    - intros * Hlink.
                      inversion Hlink.
                  }

                (*  (G| f2 <b G| f1) , instance of (g2 <b g1)  , instance of g *)
                - generalize (solveCongMod len _ _ _ (selfMod : nodesMod (f2 <a f1))); intros (f2_o_f1_Sol, (Δ, (f2_o_f1_Sol_prop_reduce, f2_o_f1_Sol_prop_desintegration))).  
                  + clear -H_gradeNodeTotalCoMod. rewriter. Omega.omega.
                  + exists (G| f2_o_f1_Sol), (linksRedCoModTrans (linksRedCoModFun2Refl) (linksRedCoModCongRefl Δ)) .
                    { split.
                      - eapply reduceCongMultiCoMod_list.
                        + (eapply RedCoModFun2Refl_Cong_CoMod;
                           apply redCongCoMod_redOnceCoMod;
                           apply RedCoModFun2Refl).
                        + apply cong_G_multi. eassumption.
                      - intros * Hlink.
                        inversion Hlink as [ ? m1 Hlink0 ? Hlink1]; clear Hlink; subst.
                        destruct Hlink1 as [ ? ? Hlink1' ].
                        (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                        dep_destruct Hlink0.
                        eapply f2_o_f1_Sol_prop_desintegration. eassumption.
                    }

                (*  (G| f2 <b γ| g1') , instance of (g2 <b g1)  , instance of g *)
                - tac_ModArrows_dep_destruct f2;
                  try rename A_ into A3;
                  try rename B1_ into B2',  B2_ into B3',  g_ into g2';
                  try rename A1_ into A2', A2_ into A3', f_ into f2';
                  try rename A2_ into A23, A3_ into A3, f2_ into f2'2, f1_ into f2'1; try rename A1_ into A2.
                  
                  (*  (G| 1 <b γ| g1') , instance of (g2 <b g1)  , instance of g *)
                  + (* choice here is by single step only ... note that for total solveMod double step was held *)
                    generalize (solveCongCoMod len _ _ _ (selfCoMod : nodesCoMod ('1 <b γ| g1'))); intros (_1_o_γ_g1'_Sol, (Λ, (_1_o_γ_g1'_Sol_prop_reduce, _1_o_γ_g1'_Sol_prop_desintegration))).  
                    * clear -H_gradeNodeTotalCoMod. rewriter. Omega.omega.
                    * exists (_1_o_γ_g1'_Sol), (linksRedCoModTrans (linksRedCoModCongComL linksRedCoModFun1Refl) (Λ)) .
                      { split.
                        - eapply reduceCongMultiCoMod_list.
                          + (eapply RedCoModFun1Refl_Cong_CoMod;
                             apply redCongCoMod_RedCoModCongComL_r;
                             apply redCongCoMod_redOnceCoMod_r;
                             apply RedCoModFun1Refl).
                          + assumption.
                        - intros * Hlink.
                          inversion Hlink as [ ? m1 Hlink0 ? Hlink1]; clear Hlink; subst.
                          inversion Hlink0; clear Hlink0; subst.
                          eapply _1_o_γ_g1'_Sol_prop_desintegration. eassumption.
                      }
                      
                  (*  (G| F| g2' <b γ| g1') , instance of (g2 <b g1) , instance of g *)
                  + generalize (solveCongCoMod len _ _ _ (selfCoMod : nodesCoMod (g2' <b g1'))); intros (g2'_o_g1'_Sol, (Λ, (g2'_o_g1'_Sol_prop_reduce, g2'_o_g1'_Sol_prop_desintegration))).  
                    * clear -H_gradeNodeTotalCoMod. rewriter. Omega.omega.
                    * exists (γ| g2'_o_g1'_Sol), (linksRedCoModTrans (linksRedCoModNatUnit2) (linksRedCoModCongUnit Λ)) .
                      { split.
                        - eapply reduceCongMultiCoMod_list.
                          + (eapply RedCoModNatUnit2_Cong_CoMod;
                             apply redCongCoMod_redOnceCoMod;
                             apply RedCoModNatUnit2).
                          + apply cong_γ_multi. assumption.
                        - intros * Hlink.
                          inversion Hlink as [ ? m1 Hlink0 ? Hlink1]; clear Hlink; subst.
                          destruct Hlink1 as [ ? ? Hlink1' ].
                          (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                          dep_destruct Hlink0.
                          eapply g2'_o_g1'_Sol_prop_desintegration. eassumption.
                      }
                      
                  (*  (G| φ| f2' <b γ| g1') , instance of (g2 <b g1)  , instance of g *)
                  + generalize (solveCongCoMod len _ _ _ (selfCoMod : nodesCoMod (G| f2' <b g1'))); intros (G_f2'_o_g1'_Sol, (Λ, (G_f2'_o_g1'_Sol_prop_reduce, G_f2'_o_g1'_Sol_prop_desintegration))).  
                    * clear -H_gradeNodeTotalCoMod. rewriter. Omega.omega.
                    * exists (G_f2'_o_g1'_Sol), (linksRedCoModTrans (linksRedCoModRectangle) (Λ)) .
                      { split.
                        - eapply reduceCongMultiCoMod_list.
                          + (eapply RedCoModRectangle_Cong_CoMod;
                             apply redCongCoMod_redOnceCoMod;
                             apply RedCoModRectangle).
                          + assumption.
                        - intros * Hlink.
                          inversion Hlink as [ ? m1 Hlink0 ? Hlink1]; clear Hlink; subst.
                          inversion Hlink0; subst; clear Hlink0.
                          eapply G_f2'_o_g1'_Sol_prop_desintegration. eassumption.
                      }

                  (*  (G| (f2'2 <a f2'1) <b γ| g1') , instance of (g2 <b g1) , instance of g *)
                  + generalize (solveCongCoMod len _ _ _ (selfCoMod : nodesCoMod (G| f2'1 <b γ| g1'))); intros (G_f2'1_o_γ_g1'_Sol, (Λ, (G_f2'1_o_γ_g1'_Sol_prop_reduce, G_f2'1_o_γ_g1'_Sol_prop_desintegration))).
                    * clear -H_gradeNodeTotalCoMod. rewriter. Omega.omega.
                    * exists (G| f2'2 <b G_f2'1_o_γ_g1'_Sol) , (linksRedCoModTrans (linksRedCoModCongComL linksRedCoModFun2Refl_Rev) (linksRedCoModTrans linksRedCoModCat2Left (linksRedCoModCongComR Λ))) . 
                      { split.
                        - eapply reduceCongMultiCoMod_list.
                          + (eapply RedCoModFun2Refl_Rev_Cong_CoMod;
                             apply redCongCoMod_RedCoModCongComL;
                             apply redCongCoMod_redOnceCoMod;
                             apply RedCoModFun2Refl_Rev).
                          + eapply reduceCongMultiCoMod_list.
                            * (eapply RedCoModCat2Left_Cong_CoMod;
                               apply redCongCoMod_redOnceCoMod;
                               apply RedCoModCat2Left).
                            * apply cong_ComR_CoMod_multi. assumption.
                        - intros * Hlink.
                          inversion Hlink as [ ? ? Hlink0 ? Hlink1 ]; clear Hlink; subst.
                          inversion Hlink1 as [ ? ? Hlink10 ? Hlink11 ]; clear Hlink1; subst.
                          
                          inversion Hlink0; subst.
                          inversion Hlink10; subst.
                          dep_destruct Hlink11.
                          eapply G_f2'1_o_γ_g1'_Sol_prop_desintegration. eassumption.                            
                      }

                (*  (G| f2 <b (g1'2 <b g1'1)) , instance of (g2 <b g1)  , instance of g )*)
                - generalize (solveCongCoMod len _ _ _ (selfCoMod : nodesCoMod (G| f2 <b g1'2))); intros (G_f2_o_g1'2_Sol, (Λ, (G_f2_o_g1'2_Sol_prop_reduce, G_f2_o_g1'2_Sol_prop_desintegration))).
                  + clear -H_gradeNodeTotalCoMod. rewriter. Omega.omega.
                  + exists (G_f2_o_g1'2_Sol <b g1'1), (linksRedCoModTrans (linksRedCoModCat2Right) (linksRedCoModCongComL Λ)) .
                    { split.
                      - eapply reduceCongMultiCoMod_list.
                        + (eapply RedCoModCat2Right_Cong_CoMod;
                           apply redCongCoMod_redOnceCoMod;
                           apply RedCoModCat2Right).
                        + apply cong_ComL_CoMod_multi. assumption.
                      - intros * Hlink.
                        inversion Hlink as [ ? m1 Hlink0 ? Hlink1]; clear Hlink; subst.
                        inversion Hlink0; subst.  dep_destruct Hlink1.
                        eapply G_f2_o_g1'2_Sol_prop_desintegration. eassumption.
                    }
              }

            (*  (γ| g2' <b g1) , instance of (g2 <b g1) , instance of g *)
            * { generalize (solveCongCoMod len _ _ _ (selfCoMod : nodesCoMod (g2' <b g1))); intros (g2'_o_g1_Sol, (Λ, (g2'_o_g1_Sol_prop_reduce, g2'_o_g1_Sol_prop_desintegration))).  
                * clear -H_gradeNodeTotalCoMod. rewriter. Omega.omega.
                * exists (γ| g2'_o_g1_Sol), (linksRedCoModTrans (linksRedCoModNatUnit1) (linksRedCoModCongUnit Λ)) .
                  { split.
                    - eapply reduceCongMultiCoMod_list.
                      + (eapply RedCoModNatUnit1_Cong_CoMod;
                         apply redCongCoMod_redOnceCoMod;
                         apply RedCoModNatUnit1).
                      + apply cong_γ_multi. assumption.
                    - intros * Hlink.
                      inversion Hlink as [ ? m1 Hlink0 ? Hlink1]; clear Hlink; subst.
                      destruct Hlink1 as [ ? ? Hlink1' ].
                      (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                      dep_destruct Hlink0.
                      eapply g2'_o_g1_Sol_prop_desintegration. eassumption.
                  }
              }

            (*  ((g2'2 <b g2'1) <b g1) ,  instance of (g2 <a g1) ,  instance of g )*)
            * { generalize (solveCongCoMod len _ _ _ (selfCoMod : nodesCoMod (g2'1 <b g1))); intros (g2'1_o_g1_Sol, (Λ, (g2'1_o_g1_Sol_prop_reduce, g2'1_o_g1_Sol_prop_desintegration))).
                * clear -H_gradeNodeTotalCoMod. rewriter. Omega.omega.
                * exists (g2'2 <b g2'1_o_g1_Sol), (linksRedCoModTrans (linksRedCoModCat2Left) (linksRedCoModCongComR Λ)) .
                  { split.
                    - eapply reduceCongMultiCoMod_list.
                      + (eapply RedCoModCat2Left_Cong_CoMod;
                         apply redCongCoMod_redOnceCoMod;
                         apply RedCoModCat2Left).
                      + apply cong_ComR_CoMod_multi. assumption.
                    - intros * Hlink.
                      inversion Hlink as [ ? m1 Hlink0 ? Hlink1]; clear Hlink; subst.
                      inversion Hlink0; subst.
                      dep_destruct Hlink1.
                      eapply g2'1_o_g1_Sol_prop_desintegration. eassumption.
                  }
              }
              
          (* m is (bottomG n) *)
          + generalize (solveCongMod len _ _ _ n); intros (f_Sol, (Δ, (f_Sol_prop_reduce, f_Sol_prop_desintegration))).  
            * clear -H_gradeNodeTotalCoMod. autorewrite with core  in H_gradeNodeTotalCoMod. Omega.omega. 
            * exists (G| f_Sol), (linksRedCoModCongRefl Δ) .
              { split.
                - apply cong_G_multi. assumption.
                - intros * Hlink.
                  (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                  dep_destruct Hlink.
                  eapply f_Sol_prop_desintegration. eassumption.
              }

          (* m is (bottomφ m) *)
          + generalize (solveCongCoMod len _ _ _ m); intros (g_Sol, (Λ, (g_Sol_prop_reduce, g_Sol_prop_desintegration))).  
            * clear -H_gradeNodeTotalCoMod. autorewrite with core  in H_gradeNodeTotalCoMod. Omega.omega. 
            * exists (γ| g_Sol), (linksRedCoModCongUnit Λ) .
              { split.
                - apply cong_γ_multi. assumption.
                - intros * Hlink.
                  (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                  dep_destruct Hlink.
                  eapply g_Sol_prop_desintegration. eassumption.
              }
              
          (* m is (leftComMod m) *)
          + generalize (solveCongCoMod len _ _ _ m); intros (g2_Sol, (Λ, (g2_Sol_prop_reduce, g2_Sol_prop_desintegration))).  
            * clear -H_gradeNodeTotalCoMod. autorewrite with core  in H_gradeNodeTotalCoMod. Omega.omega. 
            * exists (g2_Sol <b g1), (linksRedCoModCongComL Λ) .
              { split.
                - apply cong_ComL_CoMod_multi. assumption.
                - intros * Hlink.
                  (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                  dep_destruct Hlink.
                  eapply g2_Sol_prop_desintegration. eassumption.
              }

          (* m is (rightComMod m) *)
          + generalize (solveCongCoMod len _ _ _ m); intros (g1_Sol, (Λ, (g1_Sol_prop_reduce, g1_Sol_prop_desintegration))).  
            * clear -H_gradeNodeTotalCoMod. autorewrite with core  in H_gradeNodeTotalCoMod. Omega.omega. 
            * exists (g2 <b g1_Sol), (linksRedCoModCongComR Λ) .
              { split.
                - apply cong_ComR_CoMod_multi. assumption.
                - intros * Hlink.
                  (** /!\ AXIOMATIC DEPENDENT DESTRUCTION /!\ **)
                  dep_destruct Hlink.
                  eapply g1_Sol_prop_desintegration. eassumption.
              }
      }
    Defined.

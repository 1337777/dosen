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

  Module Type CongruentResolution.
    
    (* nodes where self is some Com *)
    
    Inductive nodesMod : forall A1 A2, A1 ⊢a A2 -> Set :=
  | selfMod : forall {A2 A3} {f2 : A2 ⊢a A3} {A1} {f1 : A1 ⊢a A2}, nodesMod (f2 <a f1)
  | bottomF : forall B1 B2 (g : B1 ⊢b B2), nodesCoMod g -> nodesMod (F| g)
  | bottomφ : forall A1 A2 (f : A1 ⊢a A2), nodesMod f -> nodesMod (φ| f)
  | leftComMod : forall {A1 A2} {f1 : A1 ⊢a A2},  forall A3 (f2 : A2 ⊢a A3), nodesMod f2 -> nodesMod (f2 <a f1)
  | rightComMod : forall A1 A2 (f1 : A1 ⊢a A2), nodesMod f1 -> forall {A3} {f2 : A2 ⊢a A3}, nodesMod (f2 <a f1)

  with nodesCoMod : forall B1 B2, B1 ⊢b B2 -> Set :=
  | selfCoMod : forall {B2 B3} {g2 : B2 ⊢b B3} {B1} {g1 : B1 ⊢b B2}, nodesCoMod (g2 <b g1)
  | bottomG : forall A1 A2 (f : A1 ⊢a A2), nodesMod f -> nodesCoMod (G| f)
  | bottomγ : forall B1 B2 (g : B1 ⊢b B2), nodesCoMod g -> nodesCoMod (γ| g)
  | leftComCoMod : forall {B1 B2} {g1 : B1 ⊢b B2},  forall B3 (g2 : B2 ⊢b B3), nodesCoMod g2 -> nodesCoMod (g2 <b g1)
  | rightComCoMod : forall B1 B2 (g1 : B1 ⊢b B2), nodesCoMod g1 -> forall {B3} {g2 : B2 ⊢b B3}, nodesCoMod (g2 <b g1).

  Hint Constructors nodesMod nodesCoMod.

  Scheme nodesMod_nodesCoMod_ind := Induction for nodesMod Sort Prop
                                    with nodesCoMod_nodesMod_ind := Induction for nodesCoMod Sort Prop .
  Scheme nodesMod_nodesCoMod_rec := Induction for nodesMod Sort Set
                                    with nodesCoMod_nodesMod_rec := Induction for nodesCoMod Sort Set.
  Combined Scheme nodesMod_nodesCoMod_mutind from nodesMod_nodesCoMod_ind, nodesCoMod_nodesMod_ind.
  Definition nodesMod_nodesCoMod_mutrec P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8 := 
    pair (nodesMod_nodesCoMod_rec P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8)
         (nodesCoMod_nodesMod_rec P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8).

  (* nodes where self is some Refl or CoRefl *)
  
  Inductive nodesReflMod : forall A1 A2, A1 ⊢a A2 -> Set :=
  | selfMod_Refl : forall {B1 B2} {g : B1 ⊢b B2}, nodesReflMod (F| g)
  | bottomF_Refl : forall B1 B2 (g : B1 ⊢b B2), nodesReflCoMod g -> nodesReflMod (F| g)
  | bottomφ_Refl : forall A1 A2 (f : A1 ⊢a A2), nodesReflMod f -> nodesReflMod (φ| f)
  | leftComMod_Refl : forall {A1 A2} {f1 : A1 ⊢a A2},  forall A3 (f2 : A2 ⊢a A3), nodesReflMod f2 -> nodesReflMod (f2 <a f1)
  | rightComMod_Refl : forall A1 A2 (f1 : A1 ⊢a A2), nodesReflMod f1 -> forall {A3} {f2 : A2 ⊢a A3}, nodesReflMod (f2 <a f1)

  with nodesReflCoMod : forall B1 B2, B1 ⊢b B2 -> Set :=
  | selfCoMod_Refl : forall {A1 A2} {f : A1 ⊢a A2}, nodesReflCoMod (G| f)
  | bottomG_Refl : forall A1 A2 (f : A1 ⊢a A2), nodesReflMod f -> nodesReflCoMod (G| f)
  | bottomγ_Refl : forall B1 B2 (g : B1 ⊢b B2), nodesReflCoMod g -> nodesReflCoMod (γ| g)
  | leftComCoMod_Refl : forall {B1 B2} {g1 : B1 ⊢b B2},  forall B3 (g2 : B2 ⊢b B3), nodesReflCoMod g2 -> nodesReflCoMod (g2 <b g1)
  | rightComCoMod_Refl : forall B1 B2 (g1 : B1 ⊢b B2), nodesReflCoMod g1 -> forall {B3} {g2 : B2 ⊢b B3}, nodesReflCoMod (g2 <b g1).

  Hint Constructors nodesReflMod nodesReflCoMod.

  Scheme nodesReflMod_nodesReflCoMod_ind := Induction for nodesReflMod Sort Prop
                                    with nodesReflCoMod_nodesReflMod_ind := Induction for nodesReflCoMod Sort Prop .
  Scheme nodesReflMod_nodesReflCoMod_rec := Induction for nodesReflMod Sort Set
                                    with nodesReflCoMod_nodesReflMod_rec := Induction for nodesReflCoMod Sort Set.
  Combined Scheme nodesReflMod_nodesReflCoMod_mutind from nodesReflMod_nodesReflCoMod_ind, nodesReflCoMod_nodesReflMod_ind.
  Definition nodesReflMod_nodesReflCoMod_mutrec P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8 := 
    pair (nodesReflMod_nodesReflCoMod_rec P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8)
         (nodesReflCoMod_nodesReflMod_rec P P0 f f0 f1 f2 f3 f4 f5 f6 f7 f8).

  (* reduceMod linking  *)
  
  Inductive linksRedModCat1Right {A1 A2} {f : A1 ⊢a A2} : nodesMod (f <a 1) -> nodesMod (f) -> Prop :=
  | linksRedModCat1Right_intro1 : forall n, linksRedModCat1Right (leftComMod n) (n).

  Inductive linksRedModCat1Left {A1 A2} {f : A1 ⊢a A2} : nodesMod (1 <a f) -> nodesMod (f) -> Prop :=
  | linksRedModCat1Left_intro1 : forall n, linksRedModCat1Left (rightComMod n) (n).

  Inductive linksRedModCat2 {A3 A4} {f3 : A3 ⊢a A4} {A2} {f2 : A2 ⊢a A3} {A1} {f1 : A1 ⊢a A2} : nodesMod (f3 <a (f2 <a f1)) -> nodesMod ((f3 <a f2) <a f1) -> Prop :=
  | linksRedModCat2_intro1 : linksRedModCat2 (selfMod) (leftComMod selfMod)
  | linksRedModCat2_intro2 : linksRedModCat2 (rightComMod selfMod) (selfMod)
  | linksRedModCat2_intro3 : forall n3, linksRedModCat2 (leftComMod n3) (leftComMod (leftComMod n3))
  | linksRedModCat2_intro4 : forall n2, linksRedModCat2 (rightComMod (leftComMod n2)) (leftComMod (rightComMod n2))
  | linksRedModCat2_intro5 : forall n1, linksRedModCat2 (rightComMod (rightComMod n1)) (rightComMod n1).
  
  Inductive linksRedModFun2Refl {B2 B3} {g2 : B2 ⊢b B3} {B1} {g1 : B1 ⊢b B2} : nodesMod (F| g2 <a F| g1) ->  nodesMod (F| (g2 <b g1)) -> Prop :=
  | linksRedModFun2Refl_intro1 : linksRedModFun2Refl (selfMod) (bottomF (selfCoMod))
  | linksRedModFun2Refl_intro2 : forall m2, linksRedModFun2Refl (leftComMod (bottomF m2)) (bottomF (leftComCoMod m2))
  | linksRedModFun2Refl_intro3 : forall m1, linksRedModFun2Refl (rightComMod (bottomF m1)) (bottomF (rightComCoMod m1)).

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

  Hint Constructors linksRedModFun2Refl linksRedModCat1Left linksRedModCat1Right linksRedModCat2 linksRedModNatCoUnit1 linksRedModNatCoUnit2 linksRedModRectangle.
  
  (* reduceMod congruent linking *)
  
  Inductive linksRedModCongRefl B1 B2 (g g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop) : nodesMod (F| g) -> nodesMod (F| g') -> Prop :=
  | linksRedModCongRefl1_intro : forall m m', Λ m m' -> linksRedModCongRefl Λ (bottomF m) (bottomF m').

  Inductive linksRedModCongCoUnit A1 A2 (f f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop) : nodesMod (φ| f) -> nodesMod (φ| f') -> Prop :=
  | linksRedModCongCoUnit_intro : forall n n', Δ n n' -> linksRedModCongCoUnit Δ (bottomφ n) (bottomφ n').

  Inductive linksRedModCongComL A2 A3 (f2 f2' : A2 ⊢a A3) (Δ : nodesMod f2 -> nodesMod f2' -> Prop) {A1} {f1 : A1 ⊢a A2} : nodesMod (f2 <a f1) -> nodesMod (f2' <a f1) -> Prop :=
  | linksRedModCongComL_intro1 : linksRedModCongComL Δ (selfMod) (selfMod)
  | linksRedModCongComL_intro3 : forall n n', Δ n n' -> linksRedModCongComL Δ (leftComMod n) (leftComMod n')
  | linksRedModCongComL_intro2 : forall n1, linksRedModCongComL Δ (rightComMod n1) (rightComMod n1).

  Inductive linksRedModCongComR {A2} {A3} {f2 : A2 ⊢a A3} A1 (f1 f1' : A1 ⊢a A2) (Δ : nodesMod f1 -> nodesMod f1' -> Prop) : nodesMod (f2 <a f1) -> nodesMod (f2 <a f1') -> Prop :=
  | linksRedModCongComR_intro1 : linksRedModCongComR Δ (selfMod) (selfMod)
  | linksRedModCongComR_intro2 : forall n2, linksRedModCongComR Δ (leftComMod n2) (leftComMod n2)
  | linksRedModCongComR_intro3 : forall n n', Δ n n' -> linksRedModCongComR Δ (rightComMod n) (rightComMod n').

  Hint Constructors linksRedModCongRefl linksRedModCongCoUnit linksRedModCongComL linksRedModCongComR.
  
  (* reduceMod transitive linking *)
  
  Inductive linksRedModTrans A1 A2 (uModTrans f : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod uModTrans -> Prop) (f'' : A1 ⊢a A2) (Δ' : nodesMod uModTrans -> nodesMod f'' -> Prop) : nodesMod f -> nodesMod f'' -> Prop :=
  | linksRedModTrans_intro : forall n n', Δ n n' -> forall n'', Δ' n' n'' -> linksRedModTrans Δ Δ' n n''. 
  
  Hint Constructors linksRedModTrans.

  (* reduceCoMod linking  *)
 
  Inductive linksRedCoModCat1Right {B1 B2} {g : B1 ⊢b B2} : nodesCoMod (g <b '1) -> nodesCoMod (g) -> Prop :=
  | linksRedCoModCat1Right_intro2 : forall m, linksRedCoModCat1Right (leftComCoMod m) (m).

  Inductive linksRedCoModCat1Left {B1 B2} {g : B1 ⊢b B2} : nodesCoMod ('1 <b g) -> nodesCoMod (g) -> Prop :=
  | linksRedCoModCat1Left_intro2 : forall m, linksRedCoModCat1Left (rightComCoMod m) (m).

  Inductive linksRedCoModCat2 {B3 B4} {g3 : B3 ⊢b B4} {B2} {g2 : B2 ⊢b B3} {B1} {g1 : B1 ⊢b B2} : nodesCoMod (g3 <b (g2 <b g1)) -> nodesCoMod ((g3 <b g2) <b g1) -> Prop :=
  | linksRedCoModCat2_intro1 : linksRedCoModCat2 (selfCoMod) (leftComCoMod selfCoMod)
  | linksRedCoModCat2_intro2 : linksRedCoModCat2 (rightComCoMod selfCoMod) (selfCoMod)
  | linksRedCoModCat2_intro3 : forall m3, linksRedCoModCat2 (leftComCoMod m3) (leftComCoMod (leftComCoMod m3))
  | linksRedCoModCat2_intro4 : forall m2, linksRedCoModCat2 (rightComCoMod (leftComCoMod m2)) (leftComCoMod (rightComCoMod m2))
  | linksRedCoModCat2_intro5 : forall m1, linksRedCoModCat2 (rightComCoMod (rightComCoMod m1)) (rightComCoMod m1).

  Inductive linksRedCoModFun2Refl {A2 A3} {f2 : A2 ⊢a A3} {A1} {f1 : A1 ⊢a A2} : nodesCoMod (G| f2 <b G| f1) ->  nodesCoMod (G| (f2 <a f1)) -> Prop :=
  | linksRedCoModFun2Refl_intro1 : linksRedCoModFun2Refl (selfCoMod) (bottomG (selfMod))
  | linksRedCoModFun2Refl_intro2 : forall n2, linksRedCoModFun2Refl (leftComCoMod (bottomG n2)) (bottomG (leftComMod n2))
  | linksRedCoModFun2Refl_intro3 : forall n1, linksRedCoModFun2Refl (rightComCoMod (bottomG n1)) (bottomG (rightComMod n1)).

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

  Hint Constructors linksRedCoModFun2Refl linksRedCoModCat1Left linksRedCoModCat1Right linksRedCoModCat2 linksRedCoModNatUnit1 linksRedCoModNatUnit2 linksRedCoModRectangle.
  
  (* reduceCoMod congruent linking *)
  
  Inductive linksRedCoModCongRefl A1 A2 (f f' : A1 ⊢a A2) (Δ : nodesMod f -> nodesMod f' -> Prop) : nodesCoMod (G| f) -> nodesCoMod (G| f') -> Prop :=
  | linksRedCoModCongRefl1_intro : forall n n', Δ n n' -> linksRedCoModCongRefl Δ (bottomG n) (bottomG n').

  Inductive linksRedCoModCongUnit B1 B2 (g g' : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod g' -> Prop) : nodesCoMod (γ| g) -> nodesCoMod (γ| g') -> Prop :=
  | linksRedCoModCongUnit_intro : forall m m', Λ m m' -> linksRedCoModCongUnit Λ (bottomγ m) (bottomγ m').

  Inductive linksRedCoModCongComL B2 B3 (g2 g2' : B2 ⊢b B3) (Λ : nodesCoMod g2 -> nodesCoMod g2' -> Prop) {B1} {g1 : B1 ⊢b B2} : nodesCoMod (g2 <b g1) -> nodesCoMod (g2' <b g1) -> Prop :=
  | linksRedCoModCongComL_intro1 : linksRedCoModCongComL Λ (selfCoMod) (selfCoMod)
  | linksRedCoModCongComL_intro3 : forall m m', Λ m m' -> linksRedCoModCongComL Λ (leftComCoMod m) (leftComCoMod m')
  | linksRedCoModCongComL_intro2 : forall m1, linksRedCoModCongComL Λ (rightComCoMod m1) (rightComCoMod m1).

  Inductive linksRedCoModCongComR {B2} {B3} {g2 : B2 ⊢b B3} B1 (g1 g1' : B1 ⊢b B2) (Λ : nodesCoMod g1 -> nodesCoMod g1' -> Prop) : nodesCoMod (g2 <b g1) -> nodesCoMod (g2 <b g1') -> Prop :=
  | linksRedCoModCongComR_intro1 : linksRedCoModCongComR Λ (selfCoMod) (selfCoMod)
  | linksRedCoModCongComR_intro2 : forall m2, linksRedCoModCongComR Λ (leftComCoMod m2) (leftComCoMod m2)
  | linksRedCoModCongComR_intro3 : forall m m', Λ m m' -> linksRedCoModCongComR Λ (rightComCoMod m) (rightComCoMod m').

  Hint Constructors linksRedCoModCongRefl linksRedCoModCongUnit linksRedCoModCongComL linksRedCoModCongComR.
  
  (* reduceCoMod transitive linking *)
  
  Inductive linksRedCoModTrans B1 B2 (uCoModTrans g : B1 ⊢b B2) (Λ : nodesCoMod g -> nodesCoMod uCoModTrans -> Prop) (g'' : B1 ⊢b B2) (Λ' : nodesCoMod uCoModTrans -> nodesCoMod g'' -> Prop) : nodesCoMod g -> nodesCoMod g'' -> Prop :=
  | linksRedCoModTrans_intro : forall m m', Λ m m' -> forall m'', Λ' m' m'' -> linksRedCoModTrans Λ Λ' m m''. 
  
  Hint Constructors linksRedCoModTrans.

  (** redCongMod congruent reduction, parametrized by particular reductions, 
        the sum is for inputing [nodesReflMod] nodes, actually only for redOnce_RedModFun1Refl *)

  Reserved Notation "Δ ⊧ f' ↜a f \at n" (at level 70, f' at next level).
  Reserved Notation "Λ ⊧ g' ↜b g \at m" (at level 70, g' at next level).
  Print Module Datatypes.
  Definition sum1 A A' B B' (a : A -> A') (b : B -> B') : A + B -> A' + B' :=
    fun x => (match x with inl x => inl (a x) | inr x => inr (b x) end).

  Section redCongMod.

    Variable (redOnceMod : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f + nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop).
    
    Inductive redCongMod_Mod : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f + nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | redCongMod_RedModCongRefl : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                    Λ ⊧ g' ↜b g \at inl m ->
                                 linksRedModCongRefl Λ ⊧ F| g' ↜a F| g \at inl (bottomF m)
    | redCongMod_RedModCongRefl_r : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                    Λ ⊧ g' ↜b g \at inr m ->
                                 linksRedModCongRefl Λ ⊧ F| g' ↜a F| g \at inr (bottomF_Refl m)
    | redCongMod_RedModCongCoUnit : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                      Δ ⊧ f' ↜a f \at inl n ->
                                   linksRedModCongCoUnit Δ ⊧ φ| f' ↜a φ| f \at inl (bottomφ n)
    | redCongMod_RedModCongCoUnit_r : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                      Δ ⊧ f' ↜a f \at inr n ->
                                   linksRedModCongCoUnit Δ ⊧ φ| f' ↜a φ| f \at inr (bottomφ_Refl n)
    | redCongMod_linksRedModCongComL : forall A2 A3 (f2 : A2 ⊢a A3) n2 (f2' : A2 ⊢a A3) Δ {A1} {f1 : A1 ⊢a A2},
                                         Δ ⊧ f2' ↜a f2 \at inl n2 ->
                                      linksRedModCongComL Δ ⊧ (f2' <a f1) ↜a (f2 <a f1) \at inl (leftComMod n2)
    | redCongMod_linksRedModCongComL_r : forall A2 A3 (f2 : A2 ⊢a A3) n2 (f2' : A2 ⊢a A3) Δ {A1} {f1 : A1 ⊢a A2},
                                         Δ ⊧ f2' ↜a f2 \at inr n2 ->
                                      linksRedModCongComL Δ ⊧ (f2' <a f1) ↜a (f2 <a f1) \at inr (leftComMod_Refl n2)
    | redCongMod_linksRedModCongComR : forall {A2} {A3} {f2 : A2 ⊢a A3} A1 (f1 : A1 ⊢a A2) n1 (f1' : A1 ⊢a A2) Δ,
                                         Δ ⊧ f1' ↜a f1 \at inl n1 ->
                                      linksRedModCongComR Δ ⊧ (f2 <a f1') ↜a (f2 <a f1) \at inl (rightComMod n1)
    | redCongMod_linksRedModCongComR_r : forall {A2} {A3} {f2 : A2 ⊢a A3} A1 (f1 : A1 ⊢a A2) n1 (f1' : A1 ⊢a A2) Δ,
                                         Δ ⊧ f1' ↜a f1 \at inr n1 ->
                                      linksRedModCongComR Δ ⊧ (f2 <a f1') ↜a (f2 <a f1) \at inr (rightComMod_Refl n1)

    | redCongMod_redOnceMod : forall A1 A2 (f : A1 ⊢a A2) (n : nodesMod f + nodesReflMod f) (f' : A1 ⊢a A2) (Δ : (nodesMod f -> nodesMod f' -> Prop)),
                             @redOnceMod A1 A2 f  n f' Δ ->
                             Δ ⊧ f' ↜a f \at n

    with redCongMod_CoMod : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g + nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) -> Prop :=
    | redCongMod_RedCoModCongRefl : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                      Δ ⊧ f' ↜a f \at inl n ->
                                   linksRedCoModCongRefl Δ ⊧ G| f' ↜b G| f \at inl (bottomG n)
    | redCongMod_RedCoModCongRefl_r : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                      Δ ⊧ f' ↜a f \at inr n ->
                                   linksRedCoModCongRefl Δ ⊧ G| f' ↜b G| f \at inr (bottomG_Refl n)
    | redCongMod_linksRedCoModCongUnit : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                           Λ ⊧ g' ↜b g \at inl m ->
                                        linksRedCoModCongUnit Λ ⊧ γ| g' ↜b γ| g \at inl (bottomγ m)
    | redCongMod_linksRedCoModCongUnit_r : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                           Λ ⊧ g' ↜b g \at inr m ->
                                           linksRedCoModCongUnit Λ ⊧ γ| g' ↜b γ| g \at inr (bottomγ_Refl m)
    | redCongMod_linksRedCoModCongComL : forall B2 B3 (g2 : B2 ⊢b B3) m2 (g2' : B2 ⊢b B3) Λ {B1} {g1 : B1 ⊢b B2},
                                           Λ ⊧ g2' ↜b g2 \at inl m2 ->
                                        linksRedCoModCongComL Λ ⊧ (g2' <b g1) ↜b (g2 <b g1) \at inl (leftComCoMod m2)
    | redCongMod_linksRedCoModCongComL_r : forall B2 B3 (g2 : B2 ⊢b B3) m2 (g2' : B2 ⊢b B3) Λ {B1} {g1 : B1 ⊢b B2},
                                           Λ ⊧ g2' ↜b g2 \at inr m2 ->
                                        linksRedCoModCongComL Λ ⊧ (g2' <b g1) ↜b (g2 <b g1) \at inr (leftComCoMod_Refl m2)
    | redCongMod_linksRedCoModCongComR : forall {B2} {B3} {g2 : B2 ⊢b B3} B1 (g1 : B1 ⊢b B2) m1 (g1' : B1 ⊢b B2) Λ,
                                           Λ ⊧ g1' ↜b g1 \at inl m1 ->
                                        linksRedCoModCongComR Λ ⊧ (g2 <b g1') ↜b (g2 <b g1) \at inl (rightComCoMod m1)
    | redCongMod_linksRedCoModCongComR_r : forall {B2} {B3} {g2 : B2 ⊢b B3} B1 (g1 : B1 ⊢b B2) m1 (g1' : B1 ⊢b B2) Λ,
                                           Λ ⊧ g1' ↜b g1 \at inr m1 ->
                                        linksRedCoModCongComR Λ ⊧ (g2 <b g1') ↜b (g2 <b g1) \at inr (rightComCoMod_Refl m1)

    where "Δ ⊧ f' ↜a f \at n" := (@redCongMod_Mod _ _ f n f' Δ) : solScope
                                                                 and "Λ ⊧ g' ↜b g \at m" := (@redCongMod_CoMod _ _ g m g' Λ) : solScope.

    Hint Constructors redCongMod_Mod redCongMod_CoMod.

    Scheme redCongMod_Mod_redCongMod_CoMod_ind := Induction for redCongMod_Mod Sort Prop
                                      with redCongMod_CoMod_redCongMod_Mod_ind := Induction for redCongMod_CoMod Sort Prop .
    Combined Scheme redCongMod_Mod_redCongMod_CoMod_mutind from redCongMod_Mod_redCongMod_CoMod_ind, redCongMod_CoMod_redCongMod_Mod_ind.

  End redCongMod.

  Inductive redOnce_RedModCat1Right : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f + nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
  | RedModCat1Right : forall A1 A2 (f : A1 ⊢a A2),
                       @redOnce_RedModCat1Right _ _ (f <a 1) (inl selfMod) (f) linksRedModCat1Right .

  Definition redCong_RedModCat1Right_Mod  := redCongMod_Mod redOnce_RedModCat1Right.
  Definition redCong_RedModCat1Right_CoMod  := redCongMod_CoMod redOnce_RedModCat1Right.

  Inductive redOnce_RedModCat1Left : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f + nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
  | RedModCat1Left : forall A1 A2 (f : A1 ⊢a A2),
                       @redOnce_RedModCat1Left _ _ (1 <a f) (inl selfMod) (f) linksRedModCat1Left .

  Definition redCong_RedModCat1Left_Mod  := redCongMod_Mod redOnce_RedModCat1Left.
  Definition redCong_RedModCat1Left_CoMod  := redCongMod_CoMod redOnce_RedModCat1Left.
  
  Inductive redOnce_RedModCat2 : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f + nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
  | RedModCat2 : forall A3 A4 (f3 : A3 ⊢a A4) A2 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                       @redOnce_RedModCat2 _ _ (f3 <a (f2 <a f1)) (inl selfMod) ((f3 <a f2) <a f1) linksRedModCat2 .

  Definition redCong_RedModCat2_Mod  := redCongMod_Mod redOnce_RedModCat2.
  Definition redCong_RedModCat2_CoMod  := redCongMod_CoMod redOnce_RedModCat2.
  
  Inductive redOnce_RedModFun1Refl : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f + nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
  | RedModFun1Refl : forall B,
                       @redOnce_RedModFun1Refl _ _ (F| (@CoModIden B)) (inr selfMod_Refl) (1) (fun n n' => False) .

  Definition redCong_RedModFun1Refl_Mod  := redCongMod_Mod redOnce_RedModFun1Refl.
  Definition redCong_RedModFun1Refl_CoMod  := redCongMod_CoMod redOnce_RedModFun1Refl.
  
  Inductive redOnce_RedModFun2Refl : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f + nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
  | RedModFun2Refl : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                       @redOnce_RedModFun2Refl _ _ (F| g2 <a F| g1) (inl selfMod) (F| (g2 <b g1)) linksRedModFun2Refl .

  Definition redCong_RedModFun2Refl_Mod  := redCongMod_Mod redOnce_RedModFun2Refl.
  Definition redCong_RedModFun2Refl_CoMod  := redCongMod_CoMod redOnce_RedModFun2Refl.

  Inductive redOnce_RedModNatCoUnit1 : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f + nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
  | RedModNatCoUnit1 : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                       @redOnce_RedModNatCoUnit1 _ _ (f2 <a φ| f1) (inl selfMod) (φ| (f2 <a f1)) linksRedModNatCoUnit1 .

  Definition redCong_RedModNatCoUnit1_Mod  := redCongMod_Mod redOnce_RedModNatCoUnit1.
  Definition redCong_RedModNatCoUnit1_CoMod  := redCongMod_CoMod redOnce_RedModNatCoUnit1.
  
  Inductive redOnce_RedModNatCoUnit2 : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f + nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
  | RedModNatCoUnit2 : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                       @redOnce_RedModNatCoUnit2 _ _ (φ| f2 <a F| G| f1) (inl selfMod) (φ| (f2 <a f1)) linksRedModNatCoUnit2 .

  Definition redCong_RedModNatCoUnit2_Mod  := redCongMod_Mod redOnce_RedModNatCoUnit2.
  Definition redCong_RedModNatCoUnit2_CoMod  := redCongMod_CoMod redOnce_RedModNatCoUnit2.
  
  Inductive redOnce_RedModRectangle : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f + nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
  | RedModRectangle : forall B1 B2 (g : B1 ⊢b B2) A2 (f : F|0 B2 ⊢a A2),
                       @redOnce_RedModRectangle _ _ (φ| f <a F| γ| g) (inl selfMod) (f <a F| g) linksRedModRectangle .

  Definition redCong_RedModRectangle_Mod  := redCongMod_Mod redOnce_RedModRectangle.
  Definition redCong_RedModRectangle_CoMod  := redCongMod_CoMod redOnce_RedModRectangle.
  
  Hint Constructors redOnce_RedModCat1Left redOnce_RedModCat1Right redOnce_RedModCat2 redOnce_RedModFun1Refl redOnce_RedModFun2Refl redOnce_RedModNatCoUnit1 redOnce_RedModNatCoUnit2 redOnce_RedModRectangle.
  
  (** redCongCoMod congruent reduction, parametrized by particular reductions,
        the sum is for inputing [nodesReflMod] nodes, actually only for redOnce_RedModFun1Refl *)
  
  Reserved Notation "Δ ⊧' f' ↜a f \at n" (at level 70, f' at next level).
  Reserved Notation "Λ ⊧' g' ↜b g \at m" (at level 70, g' at next level).
  
  Section redCongCoMod.

    Variable (redOnceCoMod : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g + nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop).
    
    Inductive redCongCoMod_Mod : forall A1 A2 (f : A1 ⊢a A2), (nodesMod f + nodesReflMod f) -> forall (f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
    | redCongCoMod_RedModCongRefl : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                      Λ ⊧' g' ↜b g \at inl m ->
                                 linksRedModCongRefl Λ ⊧' F| g' ↜a F| g \at inl (bottomF m)
     | redCongCoMod_RedModCongRefl_r : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                      Λ ⊧' g' ↜b g \at inr m ->
                                      linksRedModCongRefl Λ ⊧' F| g' ↜a F| g \at inr (bottomF_Refl m)
     | redCongCoMod_RedModCongCoUnit : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                        Δ ⊧' f' ↜a f \at inl n ->
                                   linksRedModCongCoUnit Δ ⊧' φ| f' ↜a φ| f \at inl (bottomφ n)
     | redCongCoMod_RedModCongCoUnit_r : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                        Δ ⊧' f' ↜a f \at inr n ->
                                   linksRedModCongCoUnit Δ ⊧' φ| f' ↜a φ| f \at inr (bottomφ_Refl n)
    | redCongCoMod_linksRedModCongComL : forall A2 A3 (f2 : A2 ⊢a A3) n2 (f2' : A2 ⊢a A3) Δ {A1} {f1 : A1 ⊢a A2},
                                           Δ ⊧' f2' ↜a f2 \at inl n2 ->
                                      linksRedModCongComL Δ ⊧' (f2' <a f1) ↜a (f2 <a f1) \at inl (leftComMod n2)
    | redCongCoMod_linksRedModCongComL_r : forall A2 A3 (f2 : A2 ⊢a A3) n2 (f2' : A2 ⊢a A3) Δ {A1} {f1 : A1 ⊢a A2},
                                           Δ ⊧' f2' ↜a f2 \at inr n2 ->
                                      linksRedModCongComL Δ ⊧' (f2' <a f1) ↜a (f2 <a f1) \at inr (leftComMod_Refl n2)
    | redCongCoMod_linksRedModCongComR : forall {A2} {A3} {f2 : A2 ⊢a A3} A1 (f1 : A1 ⊢a A2) n1 (f1' : A1 ⊢a A2) Δ,
                                           Δ ⊧' f1' ↜a f1 \at inl n1 ->
                                      linksRedModCongComR Δ ⊧' (f2 <a f1') ↜a (f2 <a f1) \at inl (rightComMod n1)
    | redCongCoMod_linksRedModCongComR_r : forall {A2} {A3} {f2 : A2 ⊢a A3} A1 (f1 : A1 ⊢a A2) n1 (f1' : A1 ⊢a A2) Δ,
                                           Δ ⊧' f1' ↜a f1 \at inr n1 ->
                                      linksRedModCongComR Δ ⊧' (f2 <a f1') ↜a (f2 <a f1) \at inr (rightComMod_Refl n1)

    with redCongCoMod_CoMod : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g + nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) -> Prop :=
    | redCongCoMod_RedCoModCongRefl : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                        Δ ⊧' f' ↜a f \at inl n ->
                                   linksRedCoModCongRefl Δ ⊧' G| f' ↜b G| f \at inl (bottomG n)
    | redCongCoMod_RedCoModCongRefl_r : forall A1 A2 (f : A1 ⊢a A2) n (f' : A1 ⊢a A2) Δ,
                                        Δ ⊧' f' ↜a f \at inr n ->
                                   linksRedCoModCongRefl Δ ⊧' G| f' ↜b G| f \at inr (bottomG_Refl n)
    | redCongCoMod_linksRedCoModCongUnit : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                             Λ ⊧' g' ↜b g \at inl m ->
                                                   linksRedCoModCongUnit Λ ⊧' γ| g' ↜b γ| g \at inl (bottomγ m)
    | redCongCoMod_linksRedCoModCongUnit_r : forall B1 B2 (g : B1 ⊢b B2) m (g' : B1 ⊢b B2) Λ,
                                             Λ ⊧' g' ↜b g \at inr m ->
                                                   linksRedCoModCongUnit Λ ⊧' γ| g' ↜b γ| g \at inr (bottomγ_Refl m)
    | redCongCoMod_linksRedCoModCongComL : forall B2 B3 (g2 : B2 ⊢b B3) m2 (g2' : B2 ⊢b B3) Λ {B1} {g1 : B1 ⊢b B2},
                                             Λ ⊧' g2' ↜b g2 \at inl m2 ->
                                        linksRedCoModCongComL Λ ⊧' (g2' <b g1) ↜b (g2 <b g1) \at inl (leftComCoMod m2)
    | redCongCoMod_linksRedCoModCongComL_r : forall B2 B3 (g2 : B2 ⊢b B3) m2 (g2' : B2 ⊢b B3) Λ {B1} {g1 : B1 ⊢b B2},
                                             Λ ⊧' g2' ↜b g2 \at inr m2 ->
                                        linksRedCoModCongComL Λ ⊧' (g2' <b g1) ↜b (g2 <b g1) \at inr (leftComCoMod_Refl m2)
    | redCongCoMod_linksRedCoModCongComR : forall {B2} {B3} {g2 : B2 ⊢b B3} B1 (g1 : B1 ⊢b B2) m1 (g1' : B1 ⊢b B2) Λ,
                                             Λ ⊧' g1' ↜b g1 \at inl m1 ->
                                        linksRedCoModCongComR Λ ⊧' (g2 <b g1') ↜b (g2 <b g1) \at inl (rightComCoMod m1)
    | redCongCoMod_linksRedCoModCongComR_r : forall {B2} {B3} {g2 : B2 ⊢b B3} B1 (g1 : B1 ⊢b B2) m1 (g1' : B1 ⊢b B2) Λ,
                                             Λ ⊧' g1' ↜b g1 \at inr m1 ->
                                        linksRedCoModCongComR Λ ⊧' (g2 <b g1') ↜b (g2 <b g1) \at inr (rightComCoMod_Refl m1)

    | redCongCoMod_redOnceCoMod : forall B1 B2 (g : B1 ⊢b B2) (m : (nodesCoMod g + nodesReflCoMod g)) (g' : B1 ⊢b B2) (Λ : (nodesCoMod g -> nodesCoMod g' -> Prop)),
                             @redOnceCoMod B1 B2 g  m g' Λ ->
                             Λ ⊧' g' ↜b g \at m
                                                              
    where "Δ ⊧' f' ↜a f \at n" := (@redCongCoMod_Mod _ _ f n f' Δ) : solScope
                                                                 and "Λ ⊧' g' ↜b g \at m" := (@redCongCoMod_CoMod _ _ g m g' Λ) : solScope.

    Hint Constructors redCongCoMod_Mod redCongCoMod_CoMod.

    Scheme redCongCoMod_Mod_redCongCoMod_CoMod_ind := Induction for redCongCoMod_Mod Sort Prop
                                      with redCongCoMod_CoMod_redCongCoMod_Mod_ind := Induction for redCongCoMod_CoMod Sort Prop .
    Combined Scheme redCongCoMod_Mod_redCongCoMod_CoMod_mutind from redCongCoMod_Mod_redCongCoMod_CoMod_ind, redCongCoMod_CoMod_redCongCoMod_Mod_ind.

  End redCongCoMod.

  Inductive redOnce_RedCoModCat1Right : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g + nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
  | RedCoModCat1Right : forall B1 B2 (g : B1 ⊢b B2),
                       @redOnce_RedCoModCat1Right _ _ (g <b '1) (inl selfCoMod) (g) linksRedCoModCat1Right .

  Definition redCong_RedCoModCat1Right_CoMod := redCongCoMod_CoMod redOnce_RedCoModCat1Right.
  Definition redCong_RedCoModCat1Right_Mod := redCongCoMod_Mod redOnce_RedCoModCat1Right.
  
  Inductive redOnce_RedCoModCat1Left : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g + nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
  | RedCoModCat1Left : forall B1 B2 (g : B1 ⊢b B2),
                       @redOnce_RedCoModCat1Left _ _ ('1 <b g) (inl selfCoMod) (g) linksRedCoModCat1Left .

  Definition redCong_RedCoModCat1Left_CoMod := redCongCoMod_CoMod redOnce_RedCoModCat1Left.
  Definition redCong_RedCoModCat1Left_Mod := redCongCoMod_Mod redOnce_RedCoModCat1Left.

  Inductive redOnce_RedCoModCat2 : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g + nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
  | RedCoModCat2 : forall B3 B4 (g3 : B3 ⊢b B4) B2 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                       @redOnce_RedCoModCat2 _ _ (g3 <b (g2 <b g1)) (inl selfCoMod) ((g3 <b g2) <b g1) linksRedCoModCat2 .

  Definition redCong_RedCoModCat2_CoMod := redCongCoMod_CoMod redOnce_RedCoModCat2.
  Definition redCong_RedCoModCat2_Mod := redCongCoMod_Mod redOnce_RedCoModCat2.
  
  Inductive redOnce_RedCoModFun1Refl : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g + nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
  | RedCoModFun1Refl : forall A,
                       @redOnce_RedCoModFun1Refl _ _ (G| (@ModIden A)) (inr selfCoMod_Refl) ('1) (fun m m' => False) .

  Definition redCong_RedCoModFun1Refl_CoMod := redCongCoMod_CoMod redOnce_RedCoModFun1Refl.
  Definition redCong_RedCoModFun1Refl_Mod := redCongCoMod_Mod redOnce_RedCoModFun1Refl.
  
  Inductive redOnce_RedCoModFun2Refl : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g + nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
  | RedCoModFun2Refl : forall A2 A3 (f2 : A2 ⊢a A3) A1 (f1 : A1 ⊢a A2),
                       @redOnce_RedCoModFun2Refl _ _ (G| f2 <b G| f1) (inl selfCoMod) (G| (f2 <a f1)) linksRedCoModFun2Refl .

  Definition redCong_RedCoModFun2Refl_CoMod := redCongCoMod_CoMod redOnce_RedCoModFun2Refl.
  Definition redCong_RedCoModFun2Refl_Mod := redCongCoMod_Mod redOnce_RedCoModFun2Refl.
  
  Inductive redOnce_RedCoModNatUnit1 : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g + nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
  | RedCoModNatUnit1 : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                       @redOnce_RedCoModNatUnit1 _ _ (γ| g2 <b g1) (inl selfCoMod) (γ| (g2 <b g1)) linksRedCoModNatUnit1 .

  Definition redCong_RedCoModNatUnit1_CoMod := redCongCoMod_CoMod redOnce_RedCoModNatUnit1.
  Definition redCong_RedCoModNatUnit1_Mod := redCongCoMod_Mod redOnce_RedCoModNatUnit1.
  
  Inductive redOnce_RedCoModNatUnit2 : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g + nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
  | RedCoModNatUnit2 : forall B2 B3 (g2 : B2 ⊢b B3) B1 (g1 : B1 ⊢b B2),
                       @redOnce_RedCoModNatUnit2 _ _ (G| F| g2 <b γ| g1) (inl selfCoMod) (γ| (g2 <b g1)) linksRedCoModNatUnit2 .

  Definition redCong_RedCoModNatUnit2_CoMod := redCongCoMod_CoMod redOnce_RedCoModNatUnit2.
  Definition redCong_RedCoModNatUnit2_Mod := redCongCoMod_Mod redOnce_RedCoModNatUnit2.
  
  Inductive redOnce_RedCoModRectangle : forall B1 B2 (g : B1 ⊢b B2), (nodesCoMod g + nodesReflCoMod g) -> forall (g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop :=
  | RedCoModRectangle : forall A1 A2 (f : A1 ⊢a A2) B1 (g : B1 ⊢b G|0 A1),
                       @redOnce_RedCoModRectangle _ _ (G| φ| f <b γ| g) (inl selfCoMod) (G| f <b g) linksRedCoModRectangle .

  Definition redCong_RedCoModRectangle_CoMod := redCongCoMod_CoMod redOnce_RedCoModRectangle.
  Definition redCong_RedCoModRectangle_Mod := redCongCoMod_Mod redOnce_RedCoModRectangle.
  
  Hint Constructors redOnce_RedCoModCat1Left redOnce_RedCoModCat1Right redOnce_RedCoModCat2 redOnce_RedCoModFun1Refl redOnce_RedCoModFun2Refl redOnce_RedCoModNatUnit1 redOnce_RedCoModNatUnit2 redOnce_RedCoModRectangle.
  
  (** reduceCongMod collects all the redCong_ instances of redCongMod,   NEXT: reduceCongMultiMod *)
  
  Reserved Notation "Δ ⊧ f' ↜a f" (at level 70, f' at next level). 
  Reserved Notation "Λ ⊧ g' ↜b g" (at level 70, g' at next level).

  Inductive reduceCongMod : forall A1 A2 (f f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
  | RedModCat1Right_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n
                            (* implicit [f] from earlier derivation helps easier ([selfMod _]) description of this input [n] *)
                            {f' : A1 ⊢a A2} {Δ},
                            (* output [f'] and [Δ] computed by eauto, always at most one-deterministically, and when node [n] is ok well-formed-for-this-reduction then at least one *)
                            redCong_RedModCat1Right_Mod (inl n) Δ -> Δ ⊧ f' ↜a f
  | RedModCat1Left_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedModCat1Left_Mod (inl n) Δ -> Δ ⊧ f' ↜a f
  | RedModCat2_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedModCat2_Mod (inl n) Δ -> Δ ⊧ f' ↜a f
  | RedModFun1Refl_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedModFun1Refl_Mod (inr n) Δ -> Δ ⊧ f' ↜a f
  | RedModFun2Refl_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedModFun2Refl_Mod (inl n) Δ -> Δ ⊧ f' ↜a f
  | RedModNatCoUnit1_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedModNatCoUnit1_Mod (inl n) Δ -> Δ ⊧ f' ↜a f
  | RedModNatCoUnit2_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedModNatCoUnit2_Mod (inl n) Δ -> Δ ⊧ f' ↜a f
  | RedModRectangle_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedModRectangle_Mod (inl n) Δ -> Δ ⊧ f' ↜a f

  | RedCoModCat1Right_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedCoModCat1Right_Mod (inl n) Δ -> Δ ⊧ f' ↜a f
  | RedCoModCat1Left_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedCoModCat1Left_Mod (inl n) Δ -> Δ ⊧ f' ↜a f
  | RedCoModCat2_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedCoModCat2_Mod (inl n) Δ -> Δ ⊧ f' ↜a f
  | RedCoModFun1Refl_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedCoModFun1Refl_Mod (inr n) Δ -> Δ ⊧ f' ↜a f
  | RedCoModFun2Refl_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedCoModFun2Refl_Mod (inl n) Δ -> Δ ⊧ f' ↜a f
  | RedCoModNatUnit1_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedCoModNatUnit1_Mod (inl n) Δ -> Δ ⊧ f' ↜a f
  | RedCoModNatUnit2_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedCoModNatUnit2_Mod (inl n) Δ -> Δ ⊧ f' ↜a f
  | RedCoModRectangle_Cong_Mod : forall A1 A2 (f : A1 ⊢a A2) n {f' : A1 ⊢a A2} {Δ},
                            redCong_RedCoModRectangle_Mod (inl n) Δ -> Δ ⊧ f' ↜a f

  where "Δ ⊧ f' ↜a f" := (@reduceCongMod _ _ f f' Δ) : solScope.

  Inductive reduceCongCoMod : forall B1 B2 (g g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop := 
  | RedModCat1Right_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedModCat1Right_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  | RedModCat1Left_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedModCat1Left_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  | RedModCat2_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedModCat2_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  | RedModFun1Refl_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedModFun1Refl_CoMod (inr m) Λ -> Λ ⊧ g' ↜b g
  | RedModFun2Refl_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedModFun2Refl_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  | RedModNatCoUnit1_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedModNatCoUnit1_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  | RedModNatCoUnit2_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedModNatCoUnit2_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  | RedModRectangle_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedModRectangle_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g

  | RedCoModCat1Right_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedCoModCat1Right_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  | RedCoModCat1Left_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedCoModCat1Left_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  | RedCoModCat2_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedCoModCat2_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  | RedCoModFun1Refl_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedCoModFun1Refl_CoMod (inr m) Λ -> Λ ⊧ g' ↜b g
  | RedCoModFun2Refl_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedCoModFun2Refl_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  | RedCoModNatUnit1_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedCoModNatUnit1_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  | RedCoModNatUnit2_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedCoModNatUnit2_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  | RedCoModRectangle_Cong_CoMod : forall B1 B2 (g : B1 ⊢b B2) m {g' : B1 ⊢b B2} {Λ},
                            redCong_RedCoModRectangle_CoMod (inl m) Λ -> Λ ⊧ g' ↜b g
  where "Λ ⊧ g' ↜b g" := (@reduceCongCoMod _ _ g g' Λ) : solScope.

  Hint Constructors reduceCongMod reduceCongCoMod.

  Reserved Notation "Δ ⊧ f' *↜a f" (at level 70, f' at next level). 
  Reserved Notation "Λ ⊧ g' *↜b g" (at level 70, g' at next level).

  Inductive reduceCongMultiMod : forall A1 A2 (f f' : A1 ⊢a A2), (nodesMod f -> nodesMod f' -> Prop) ->  Prop := 
  | reduceCongMultiMod_refl : forall {A1 A2} {f : A1 ⊢a A2},
                              forall {Δ} {pf : (forall n n', n = n' <-> Δ n n' : Prop)},
                                Δ ⊧ f *↜a f
  | reduceCongMultiMod_list : forall A1 A2 (f uModTrans : A1 ⊢a A2) Δ,
                                 Δ ⊧ uModTrans ↜a f ->
                                 forall (f'' : A1 ⊢a A2) Δ', Δ' ⊧ f'' *↜a uModTrans ->
                                                        forall {ΔΔ'} {pf : forall n n', linksRedModTrans Δ Δ' n n' <-> ΔΔ' n n'}, 
                                                          ΔΔ' ⊧ f'' *↜a f
  | reduceCongMultiMod_ext : forall A1 A2 (f f' : A1 ⊢a A2) Δ,
                             forall {ΔU} {pf : forall n n', ΔU n n' <-> Δ n n'}, 
                               ΔU ⊧ f' *↜a f ->
                               Δ ⊧ f' *↜a f
  where "Δ ⊧ f' *↜a f" := (@reduceCongMultiMod _ _ f f' Δ) : solScope.

  Hint Constructors reduceCongMultiMod.

  Inductive reduceCongMultiCoMod : forall B1 B2 (g g' : B1 ⊢b B2), (nodesCoMod g -> nodesCoMod g' -> Prop) ->  Prop := 
  | reduceCongMultiCoMod_refl : forall {B1 B2} {g : B1 ⊢b B2},
                                forall {Λ} {pf : (forall n n', n = n' <-> Λ n n' : Prop)},
                                  Λ ⊧ g *↜b g
  | reduceCongMultiCoMod_list : forall B1 B2 (g uCoModTrans : B1 ⊢b B2) Λ,
                                 Λ ⊧ uCoModTrans ↜b g ->
                                 forall (g'' : B1 ⊢b B2) Λ', Λ' ⊧ g'' *↜b uCoModTrans ->
                                                        forall {ΛΛ'} {pf : forall m m', linksRedCoModTrans Λ Λ' m m' <-> ΛΛ' m m'},
                                                          ΛΛ' ⊧ g'' *↜b g
  | reduceCongMultiCoMod_ext : forall B1 B2 (g g' : B1 ⊢b B2) Λ,
                             forall {ΛU} {pf : forall n n', ΛU n n' <-> Λ n n'}, 
                               ΛU ⊧ g' *↜b g ->
                               Λ ⊧ g' *↜b g
  where "Λ ⊧ g' *↜b g" := (@reduceCongMultiCoMod _ _ g g' Λ) : solScope.

  Hint Constructors reduceCongMultiCoMod.

  Lemma reduceCongMultiMod_trans : forall A1 A2 (f uModTrans : A1 ⊢a A2) Δ,
                                     Δ ⊧ uModTrans *↜a f ->
                                     forall (f'' : A1 ⊢a A2) Δ', Δ' ⊧ f'' *↜a uModTrans ->
                                                            forall {ΔΔ'} {pf : forall n n', linksRedModTrans Δ Δ' n n' <-> ΔΔ' n n'}, 
                                                              ΔΔ' ⊧ f'' *↜a f.
  Proof.
    Fail timeout 5 (induction 1; eauto).
    Restart.
    induction 1. Focus 3. intros. econstructor 3. eassumption. eapply IHreduceCongMultiMod. eassumption.  clear -pf.
    split.
    induction 1. econstructor. apply pf. eassumption. eassumption.
    induction 1. econstructor. apply pf. eassumption. eassumption.

    Focus 1. intros. econstructor 3. 2: eassumption. clear -pf pf0.
    intros. enough (Δ' n n' <-> linksRedModTrans Δ Δ' n n' ) by firstorder.
    clear -pf.
    split.
    intros. econstructor. 2: eassumption. apply pf. reflexivity.
    induction 1. apply pf in H. subst. assumption.

    Focus 1.
    intros. econstructor 2. eassumption. eapply IHreduceCongMultiMod. eassumption.
    clear. intuition eauto.
    intros. enough (linksRedModTrans Δ (linksRedModTrans Δ' Δ'0) n n' <-> linksRedModTrans ΔΔ' Δ'0 n n') by firstorder.
    clear -pf.
    intros. 
    assert (linksRedModTrans ΔΔ' Δ'0 n n' <-> linksRedModTrans (linksRedModTrans Δ Δ') Δ'0 n n').
    { clear -pf.
      split.
      induction 1. econstructor. apply pf. eassumption. eassumption.
      induction 1. econstructor. apply pf. eassumption. eassumption.
    }
    enough ( linksRedModTrans Δ (linksRedModTrans Δ' Δ'0) n n' <-> linksRedModTrans (linksRedModTrans Δ Δ') Δ'0 n n') by firstorder.
    clear.
    split.
    induction 1. induction H0. econstructor. 2: eassumption. econstructor. eassumption. eassumption.
    induction 1. induction H. econstructor. 1: eassumption. econstructor. eassumption. eassumption.
  Qed.

  Print Assumptions reduceCongMultiMod_trans.
  Hint Resolve reduceCongMultiMod_trans.
  
  Lemma reduceCongMultiMod_single : forall A1 A2 (f f' : A1 ⊢a A2) Δ,
                                     Δ ⊧ f' ↜a f -> Δ ⊧ f' *↜a f.
    econstructor 2.
    eassumption.
    econstructor 1. intuition eauto.
    split. induction 1. subst; assumption.
    econstructor. eassumption. reflexivity.
  Qed.

  Print Assumptions reduceCongMultiMod_single.
  Hint Resolve reduceCongMultiMod_single.
  
  Lemma reduceCongMultiCoMod_trans : forall B1 B2 (g uCoModTrans : B1 ⊢b B2) Λ,
                                      Λ ⊧ uCoModTrans *↜b g ->
                                      forall (g'' : B1 ⊢b B2) Λ', Λ' ⊧ g'' *↜b uCoModTrans ->
                                                             forall {ΛΛ'} {pf : forall m m', linksRedCoModTrans Λ Λ' m m' <-> ΛΛ' m m'},
                                                               ΛΛ' ⊧ g'' *↜b g.
  Admitted.

  Hint Resolve reduceCongMultiCoMod_trans.
  Lemma reduceCongMultiCoMod_single : forall B1 B2 (g g' : B1 ⊢b B2) Λ,
                                        Λ ⊧ g' ↜b g -> Λ ⊧ g' *↜b g.
    econstructor 2.
    eassumption.
    econstructor 1. intuition eauto.
    split. induction 1. subst; assumption.
    econstructor. eassumption. reflexivity.
  Qed.
  Hint Resolve reduceCongMultiCoMod_single.

  (** unification and type inference  give special notations for programming in categories, special sequencing notation for transitivity *)
  
  Notation "'INIT' f" := (@reduceCongMultiMod_refl _ _ f eq _) (at level 58).
  Notation "'NOOP'" := (reduceCongMultiMod_refl).
  Notation "r1 ;; r2" := (reduceCongMultiMod_trans r1 r2) (at level 60, right associativity).

  Notation "'cat1r' 'at' n" := (reduceCongMultiMod_single (@RedModCat1Right_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'cat1l' 'at' n" := (reduceCongMultiMod_single (@RedModCat1Left_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'cat2' 'at' n" := (reduceCongMultiMod_single (@RedModCat2_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'fun1' 'at' n" := (reduceCongMultiMod_single (@RedModFun1Refl_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'fun2' 'at' n" := (reduceCongMultiMod_single (@RedModFun2Refl_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'counit1' 'at' n" := (reduceCongMultiMod_single (@RedModNatCoUnit1_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'counit2' 'at' n" := (reduceCongMultiMod_single (@RedModNatCoUnit2_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'rect' 'at' n" := (reduceCongMultiMod_single (@RedModRectangle_Cong_Mod _ _ _ n _ _ _)) (at level 58).

  Notation "'cat1r' 'at'' n" := (reduceCongMultiCoMod_single (@RedModCat1Right_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'cat1l' 'at'' n" := (reduceCongMultiCoMod_single (@RedModCat1Left_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'cat2' 'at'' n" := (reduceCongMultiCoMod_single (@RedModCat2_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'fun1' 'at'' n" := (reduceCongMultiCoMod_single (@RedModFun1Refl_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'fun2' 'at'' n" := (reduceCongMultiCoMod_single (@RedModFun2Refl_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'counit1' 'at'' n" := (reduceCongMultiCoMod_single (@RedModNatCoUnit1_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'counit2' 'at'' n" := (reduceCongMultiCoMod_single (@RedModNatCoUnit2_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'rect' 'at'' n" := (reduceCongMultiCoMod_single (@RedModRectangle_Cong_CoMod _ _ _ n _ _ _)) (at level 58).

  Notation "'INIT'' g" := (@reduceCongMultiCoMod_refl _ _ g eq _) (at level 58).
  Notation "'NOOP''" := (reduceCongMultiCoMod_refl).
  Notation "r1 ;;' r2" := (reduceCongMultiCoMod_trans r1 r2) (at level 60, right associativity).

  Notation "'cat1r'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModCat1Right_Cong_CoMod  _ _ _ m _ _ _)) (at level 58).
  Notation "'cat1l'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModCat1Left_Cong_CoMod  _ _ _ m _ _ _)) (at level 58).
  Notation "'cat2'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModCat2_Cong_CoMod  _ _ _ m _ _ _)) (at level 58).
  Notation "'fun1'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModFun1Refl_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
  Notation "'fun2'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModFun2Refl_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
  Notation "'unit1'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModNatUnit1_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
  Notation "'unit2'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModNatUnit2_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
  Notation "'rect'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModRectangle_Cong_CoMod _ _ _ m _ _ _)) (at level 58).

  Notation "'cat1r'' 'at' m" := (reduceCongMultiMod_single (@RedCoModCat1Right_Cong_Mod  _ _ _ m _ _ _)) (at level 58).
  Notation "'cat1l'' 'at' m" := (reduceCongMultiMod_single (@RedCoModCat1Left_Cong_Mod  _ _ _ m _ _ _)) (at level 58).
  Notation "'cat2'' 'at' m" := (reduceCongMultiMod_single (@RedCoModCat2_Cong_Mod  _ _ _ m _ _ _)) (at level 58).
  Notation "'fun1'' 'at' m" := (reduceCongMultiMod_single (@RedCoModFun1Refl_Cong_Mod _ _ _ m _ _ _)) (at level 58).
  Notation "'fun2'' 'at' m" := (reduceCongMultiMod_single (@RedCoModFun2Refl_Cong_Mod _ _ _ m _ _ _)) (at level 58).
  Notation "'unit1'' 'at' m" := (reduceCongMultiMod_single (@RedCoModNatUnit1_Cong_Mod _ _ _ m _ _ _)) (at level 58).
  Notation "'unit2'' 'at' m" := (reduceCongMultiMod_single (@RedCoModNatUnit2_Cong_Mod _ _ _ m _ _ _)) (at level 58).
  Notation "'rect'' 'at' m" := (reduceCongMultiMod_single (@RedCoModRectangle_Cong_Mod _ _ _ m _ _ _)) (at level 58).

  (*
  Notation "'INIT' f" := (@reduceCongMultiMod_refl _ _ f eq _) (at level 58).
  Notation "'NOOP'" := (reduceCongMultiMod_refl).
  Notation "r1 ;; r2" := (reduceCongMultiMod_list r1 r2) (at level 60, right associativity).

  Notation "'cat1r' 'at' n" := (reduceCongMultiMod_single (@RedModCat1Right_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'cat1l' 'at' n" := (reduceCongMultiMod_single (@RedModCat1Left_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'cat2' 'at' n" := (reduceCongMultiMod_single (@RedModCat2_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'fun1' 'at' n" := (reduceCongMultiMod_single (@RedModFun1Refl_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'fun2' 'at' n" := (reduceCongMultiMod_single (@RedModFun2Refl_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'counit1' 'at' n" := (reduceCongMultiMod_single (@RedModNatCoUnit1_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'counit2' 'at' n" := (reduceCongMultiMod_single (@RedModNatCoUnit2_Cong_Mod _ _ _ n _ _ _)) (at level 58).
  Notation "'rect' 'at' n" := (reduceCongMultiMod_single (@RedModRectangle_Cong_Mod _ _ _ n _ _ _)) (at level 58).

  Notation "'cat1r' 'at'' n" := (reduceCongMultiCoMod_single (@RedModCat1Right_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'cat1l' 'at'' n" := (reduceCongMultiCoMod_single (@RedModCat1Left_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'cat2' 'at'' n" := (reduceCongMultiCoMod_single (@RedModCat2_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'fun1' 'at'' n" := (reduceCongMultiCoMod_single (@RedModFun1Refl_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'fun2' 'at'' n" := (reduceCongMultiCoMod_single (@RedModFun2Refl_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'counit1' 'at'' n" := (reduceCongMultiCoMod_single (@RedModNatCoUnit1_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'counit2' 'at'' n" := (reduceCongMultiCoMod_single (@RedModNatCoUnit2_Cong_CoMod _ _ _ n _ _ _)) (at level 58).
  Notation "'rect' 'at'' n" := (reduceCongMultiCoMod_single (@RedModRectangle_Cong_CoMod _ _ _ n _ _ _)) (at level 58).

  Notation "'INIT'' g" := (@reduceCongMultiCoMod_refl _ _ g eq _) (at level 58).
  Notation "'NOOP''" := (reduceCongMultiCoMod_refl).
  Notation "r1 ;;' r2" := (reduceCongMultiCoMod_list r1 r2) (at level 60, right associativity).

  Notation "'cat1r'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModCat1Right_Cong_CoMod  _ _ _ m _ _ _)) (at level 58).
  Notation "'cat1l'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModCat1Left_Cong_CoMod  _ _ _ m _ _ _)) (at level 58).
  Notation "'cat2'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModCat2_Cong_CoMod  _ _ _ m _ _ _)) (at level 58).
  Notation "'fun1'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModFun1Refl_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
  Notation "'fun2'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModFun2Refl_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
  Notation "'unit1'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModNatUnit1_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
  Notation "'unit2'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModNatUnit2_Cong_CoMod _ _ _ m _ _ _)) (at level 58).
  Notation "'rect'' 'at'' m" := (reduceCongMultiCoMod_single (@RedCoModRectangle_Cong_CoMod _ _ _ m _ _ _)) (at level 58).

  Notation "'cat1r'' 'at' m" := (reduceCongMultiMod_single (@RedCoModCat1Right_Cong_Mod  _ _ _ m _ _ _)) (at level 58).
  Notation "'cat1l'' 'at' m" := (reduceCongMultiMod_single (@RedCoModCat1Left_Cong_Mod  _ _ _ m _ _ _)) (at level 58).
  Notation "'cat2'' 'at' m" := (reduceCongMultiMod_single (@RedCoModCat2_Cong_Mod  _ _ _ m _ _ _)) (at level 58).
  Notation "'fun1'' 'at' m" := (reduceCongMultiMod_single (@RedCoModFun1Refl_Cong_Mod _ _ _ m _ _ _)) (at level 58).
  Notation "'fun2'' 'at' m" := (reduceCongMultiMod_single (@RedCoModFun2Refl_Cong_Mod _ _ _ m _ _ _)) (at level 58).
  Notation "'unit1'' 'at' m" := (reduceCongMultiMod_single (@RedCoModNatUnit1_Cong_Mod _ _ _ m _ _ _)) (at level 58).
  Notation "'unit2'' 'at' m" := (reduceCongMultiMod_single (@RedCoModNatUnit2_Cong_Mod _ _ _ m _ _ _)) (at level 58).
  Notation "'rect'' 'at' m" := (reduceCongMultiMod_single (@RedCoModRectangle_Cong_Mod _ _ _ m _ _ _)) (at level 58).
*)
  Check fun m => INIT' G| (φ| (F| _) <a _) ;;' (fun2' at' ( (bottomG (leftComMod (bottomφ (bottomF m))))) ;;' (NOOP' ;;' unit2' at'  ( (bottomγ (bottomG ( _ )))))) .
  Fail Check fun m => INIT' G| (φ| (F| _) <a _) ;;' (fun2' at' ( (bottomG (leftComMod (bottomF m)))) ;;' (NOOP' ;;' unit2' at'  ( (bottomγ (bottomG ( _ )))))) . 
  Check fun m => INIT' G| (φ| (F| _) <a _) ;;' (fun2' at' ( (bottomG (leftComMod (bottomφ (bottomF m))))) ;;' (NOOP' ;;' unit2' at'  ( (bottomγ (bottomG ( _ )))))) ;;' fun1' at' ( (leftComCoMod_Refl _)).

  Check fun n => INIT F| (γ| (G| _) <b _) ;; (fun2 at ( (bottomF (leftComCoMod (bottomγ (bottomG n))))) ;; (NOOP ;; counit2 at ( (bottomφ (bottomF ( _ )))))) .

(*
  Arguments sum1 / _ _ _ _ _ _ _. (* /! not really helping [simpl] or [cbn] *)
  (*  Hint Extern 4 => match goal with [ |- sum1 _ _ ?EV = _ ] => is_evar EV; instantiate (1:= inl _); reflexivity end.*)
  Ltac tac_sumBAD := idtac.
(*    (tryif match goal with [ |- context[sum1 _ _ ?EV] ] => is_evar EV; instantiate (1:= inl _); simpl end then (repeat match goal with [ |- context[sum1 _ _ ?EV] ] => is_evar EV; instantiate (1:= inl _); simpl end; reflexivity) else idtac).*)
  Hint Extern 4 => tac_sumBAD.
  Ltac tac_sumBAD2 := idtac .
(*    (tryif match goal with [ |- context[sum1 _ _ ?EV] ] => is_evar EV; instantiate (1:= inr _); simpl end then (repeat match goal with [ |- context[sum1 _ _ ?EV] ] => is_evar EV; instantiate (1:= inr _); simpl end; reflexivity) else idtac).*)
  Hint Extern 4 => tac_sumBAD2.
 *)
  
  Lemma lll : forall A, exists  f'', exists ΔΔ',  ΔΔ' ⊧ f'' *↜a F| (γ| (G| (@ModIden A) <b G| 1) <b G| 1) .
    intros. eexists. eexists.
    refine (fun2' at  ( (bottomF (leftComCoMod (bottomγ  (selfCoMod))))) ;; _).

    Undo.
    refine (fun2' at  ( (bottomF (leftComCoMod (bottomγ  (selfCoMod))))) ;; NOOP);
      try match goal with [ |- nodesMod _ -> nodesMod _ -> Prop ] => shelve end;
      repeat (intuition eauto; econstructor).
    Show Proof.
    
    Undo.
    refine (fun2' at  ( (bottomF (leftComCoMod (bottomγ  (selfCoMod))))) ;; fun1' at ( (bottomF_Refl (rightComCoMod_Refl selfCoMod_Refl))) ;; NOOP);
      try match goal with [ |- nodesMod _ -> nodesMod _ -> Prop ] => shelve end;
      repeat (intuition eauto; econstructor).
    Show Proof.

    Undo.
    refine (INIT F| (γ| (G| (@ModIden A) <b G| 1) <b G| 1) ;; fun2' at  ( (bottomF (leftComCoMod (bottomγ  (selfCoMod))))) ;; NOOP);
      try match goal with [ |- nodesMod _ -> nodesMod _ -> Prop ] => shelve end;
      repeat (intuition eauto; econstructor).
    Show Proof.

    Undo.
    refine (INIT F| (γ| (G| (@ModIden A) <b G| 1) <b G| 1) ;; fun2' at  ( (bottomF (leftComCoMod (bottomγ  (selfCoMod))))) ;; fun1' at ( (bottomF_Refl (rightComCoMod_Refl selfCoMod_Refl))) ;; NOOP);
      try match goal with [ |- nodesMod _ -> nodesMod _ -> Prop ] => shelve end;
      repeat (intuition eauto; econstructor).
    Show Proof.
    
  (*
    Focus 2.    econstructor 1. 2: eauto.
    econstructor .  
    2: eauto.
  
    econstructor .  2: eauto.
    econstructor 5.  constructor .
    
     2 : intuition eauto.

     intros.
     econstructor. 
     intros. eassumption.
     intros. assumption. *)
(*
    Undo 1.
    refine (fun2' at  (inl (bottomF (leftComCoMod (bottomγ  (selfCoMod))))) ;; fun1' at (inl (bottomF (rightComCoMod selfCoMod))) ;; NOOP);
      repeat ((econstructor 1 + econstructor 2 + econstructor 3 + econstructor 4 + econstructor 5 + econstructor 6 + econstructor 7 + econstructor 8 + econstructor 9 + econstructor 10 + econstructor 11 + econstructor); intuition eauto 12;
              (tac_sumBAD || tac_sumBAD2)).
*)
  Qed.


  Lemma terminology_completeness_lemma_aux1 : forall A1 A2 (f' f : A1 ⊢a A2) Δ,  Δ ⊧ f' ↜a f -> exists Δcong,  Δcong ⊧ G| f' ↜b G| f /\ (forall n n',  linksRedCoModCongRefl Δ n n' <-> Δcong n n').
  Proof.
    intros.
    induction H; red in H.
    - (* which operation, Cat1Right *)
      remember (inl n)  eqn:Heq_n_. revert Heq_n_.
      revert n. pattern A1, A2, f, s, f', Δ, H. About redCongMod_Mod_redCongMod_CoMod_ind.
      eapply (redCongMod_Mod_redCongMod_CoMod_ind) with (redOnceMod := redOnce_RedModCat1Right) (* must write co-proposition, so abort for now *).

      Focus 9. (* which congruence, here non inductive case (direct self _ case),  for easy *)
      {
      intros. subst.
      eexists. split. repeat (eassumption || econstructor). Undo.
      eapply RedModCat1Right_Cong_CoMod.
      eapply redCongMod_RedCoModCongRefl.
      eapply redCongMod_redOnceMod. eassumption.
      tauto. }

      Unfocus.
  Admitted.
  
      Lemma terminology_completeness_lemma : (forall A1 A2 (f' f : A1 ⊢a A2),  f' ↜a f -> exists Δ,  Δ ⊧ f' *↜a f) /\ (forall B1 B2 (g' g : B1 ⊢b B2),  g' ↜b g -> exists Λ,  Λ ⊧ g' *↜b g).
    apply reduceMod_reduceCoMod_mutind.
    Admitted.

    
  (** NEXT DELETE USERLESS ' FROM ⊧' AND REUSE SAME ⊧ **)
  

  Definition gradeNodeMod : (forall A1 A2 (f : A1 ⊢a A2) (x : nodesMod f), nat).
    (* traverse bottomF bottomφ .. until selfMod f_ then get gradeMod f_ *)
  Admitted.
  
  Definition gradeNodeCoMod :  (forall B1 B2 (g : B1 ⊢b B2) (y : nodesCoMod g), nat).
  Admitted.

  Fixpoint solveCongMod len {struct len} : forall A1 A2 (f : A1 ⊢a A2) (x : nodesMod f)
                                         (H_grade : gradeNodeMod ((Datatypes.id) x) <= len),
                                         { fo : A1 ⊢a A2 &
                                                { Δ : nodesMod f ->  nodesMod fo -> Prop |
                                                  Δ ⊧ fo ↜a f /\
                                                  ~ exists y, Δ x y }}. 

  Admitted.
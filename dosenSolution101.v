(**#+TITLE: dosenSolution101.v

Proph

https://gitlab.com/1337777/dosen/blob/master/dosenSolution101.v

solves some question of Dosen which is how to program the logical/particular/rewriting/(one-step) polymorphism/cut-elimination and the confluence/commutation of this rewriting for the grammatical polymorph pairing-projections ( "product" ) ...

The computational/total/asymptotic/reduction/(multi-step) polymorphism/cut-elimination of many polymorph mathematics were already programmed in the earlier COQ texts : polymorph reflections/adjunctions , polymorph comonad , polymorph grammatical-metafunctors , polymorph localizations ... The form of these programs was the same : primo to define grammatical (multi-step) reduction relation , then secondo to define some non-structural recursive grade function from the morphisms to the integers , and finally tertio to define some non-structural recursive cut-elimination function from any two-morphisms input ( "topmost cut" ) by choosing some syntactic-match cases precedence when there are ambiguities ref which reduction shall apply . Memo that the grade function was linear arithmetic ( addition , maximum , less than ) over the integers .

Now to proceed to the logical consequences of such things shall require some alternative logical description : some logical/particular/rewriting/(one-step) polymorphism/cut-elimination resolution and the confluence/commutation lemma of this rewriting which shows that this logical resolution is indeed some alternative description of the computational function . Memo that the grade function here will ( necessarily ? ) be non-linear arithmetic ( addition , multiplication , distributivity , less than ) over the integers which mimic/simulate the constructors of the morphisms , in particular : the polymorphism ( "distributivity" ) of the composition/cut constructor over the pairing constructor . More precisely : grade ( f o> g ) = 3 * grade f * grade g  ;  grade ( 1 ) = 1  ;  grade ( ~_1 o> f ) = 1 + grade f  ;  grade ( ~_2 o> f ) = 1 + grade f  ;  grade ( << f , g >> ) = 1 + grade f + grade g .

This COQ program and deduction is mostly-automated , and the COQ [nia] automation-tactic is sufficient for this non-linear arithmetic . The confluence lemma produce some total of ( ( 7 * 8 ) * ( 7 * 8 ) = 3136 goals ) , but only ( 37 classes of goals) are critical via the automation-tactics ; moreover the COQ computer ( parallel dual core , 4 gigabytes memory ) motion-time for ( 93 + 27 = 120 minutes ) .

For instant first impression , the lemma that the « resolved-cut » is congruent modulo solution-conversion is written as :

#+BEGIN_EXAMPLE
Fixpoint solveCoMod_PolyCoMod_cong_Post_ len {struct len}  :
  forall (B1 : obCoMod) (B1' : obCoMod) (g'Sol g'Sol0 : 'CoMod(0 B1 ~> B1' )0 %sol)
    ( Hconv : ( g'Sol0 ~~~ g'Sol )%sol_once ), 
        forall  B2 (g_Sol : 'CoMod(0 B2 ~> B1 )0 %sol),
        forall (H_gradeParticular : ( (Sol.gradeConv Hconv + Rewrite.gradeParticular ((Sol.toCoMod g_Sol) o>CoMod (Sol.toCoMod g'Sol))%poly)%Z <= Z.of_nat len)%Z ),
          ( ( ( g_Sol o>CoMod g'Sol0 ) ~~~ ( g_Sol o>CoMod g'Sol ) )) %sol %sol_conv . 
#+END_EXAMPLE

This file [[1337777.OOO//dosenSolution101.v]] is the epilogue of Dosen book « Cut-Elimination in Categories » .

Keywords : 1337777.OOO//dosenSolution101.v ; pairing-projections grammar ; logical cut-elimination ; confluence ; non-linear arithmetic

Outline :

  * Grammatical description of polymorph pairing-projections 
  ** Importing the non-linear arithmetic COQ automation-tactics
  ** Common-inductive polymorph morphisms, with overloaded notations for the composition/cut constructor

  * Solution
  ** Grade of solution-conversion for combined non-structural induction  
  ** Destruction of solution-morphisms with inner-instantiation of object-indexes

  * Congruent-Rewriting relation
  ** Non-linear mimicking grade function
  ** Degradation lemma and the non-linear arithmetic COQ automation-tactic [nia]

  * Polymorphism/cut-elimination by congruent-rewriting

  * Confluence
  ** Goals accounting
  ** Unique solution for the logical-rewriting relation

  * Polymorphism conversion
  ** Cut-elimination resolution is congruent from the polymorphism-terminology to the solution-terminology

-----

PS : Oktoberfest 2017 continues as NovemberSchätz 2017 at the CMU Schätz weekends 11:37-14:00 until november ...

-----

memory amazon.com/hz/wishlist/ls/28SN02HR4EB8W , eth 0x54810dcb93b37DBE874694407f78959Fa222D920 , paypal 1337777.OOO@gmail.com , wechatpay 2796386464@qq.com , irc #OOO1337777

**)

(**

* Grammatical description of polymorph pairing-projections 

** Importing the non-linear arithmetic COQ automation-tactics

This new deduction of the logical confluence lemma necessarily uses some finer/step/particular polymorphism/cut-elimination ( "rewriting" ) which shall ( necessarily ? ) proceed by some non-linear mimicking-grade ( [gradeParticular] ) .,

This contrasts from the earlier computations of the asymptotic/total polymorphism/cut-elimination ( "reduction" ) which may proceed by some linear asymptotical-grade ( [gradeTotal] ) ., 

Therefore instead of importing the [Omega.omega] automation-tactic , oneself shall import the [nia] automation-tactic of the [Psatz] module ., 

#+BEGIN_SRC coq :exports both :results silent **)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun eqtype ssrnat seq fintype.
Require Import ZArith.
Require Import Psatz.
Require Import Setoid.
(* [Equality] module is non-necessary , here only for easier for draft, 
    alt: Destruct_domLimit -style *)
Require Import Equality.

Module CONFLUENCE.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments Z.add : simpl nomatch.
Arguments Z.mul : simpl nomatch.

(**#+END_SRC

** Common-inductive polymorph morphisms, with overloaded notations for the composition/cut constructor

For now the base generating graph is empty and without generating objects and without generating morphisms ., The grammatical description of polymorph pairing-projections is done using some common-inductive presentation with common-inductive elimination-scheme ,. Memo the overloaded notations for the composition/cut constructor [ ( _ o>CoMod _ ) ] which is reused fot the projections-constructors .

The end/goal is to eliminate the polymorphism/cut/algebraic [PolyCoMod] terminology into some solution/combinatorial terminology without such cuts;  and then to show that whatever-wanted conversion property involving polymorphism/cuts which held in the old terminology is still-derivable from the new terminology .,

Indeed, the unknown intermediate/transitive object/index which is present in some cut causes that, sometimes during some deduction by induction, oneself is required to show some side-conclusion ( side-goal (arithmetical) assumption of the induction hypothesis implication ) where this intermediate object/index appears, but the introduced (arithmetical) assumption of the main-conclusion cannot mention this intermediate object/index .,

#+BEGIN_SRC coq :exports both :results silent **)

Inductive obCoMod : Type :=
  Limit : forall B1 B2 : obCoMod, obCoMod.

Delimit Scope poly_scope with poly.
Open Scope poly.

Reserved Notation "''CoMod' (0 B1 ~> B2 )0"
         (at level 25, format "''CoMod' (0  B1  ~>  B2  )0").

Inductive CoMod00 : obCoMod -> obCoMod -> Type :=

| PolyCoMod : forall (B2 : obCoMod) (B1 : obCoMod)
  , 'CoMod(0 B2 ~> B1 )0 -> forall B1' : obCoMod,
      'CoMod(0 B1 ~> B1' )0 -> 'CoMod(0 B2 ~> B1' )0


| UnitCoMod : forall {B : obCoMod}, 'CoMod(0 B ~> B )0

| Project_1 : forall B1 B2,
      forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0), 'CoMod(0 (Limit B1 B2) ~> B1' )0

| Project_2 : forall B1 B2,
      forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0), 'CoMod(0 (Limit B1 B2) ~> B2' )0

| Limitator : forall B1 B2 M,
    forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
      'CoMod(0 M ~> (Limit B1 B2) )0

where "''CoMod' (0 B1 ~> B2 )0" := (@CoMod00 B1 B2) : poly_scope.

Notation "g_ o>CoMod g'" :=
  (@PolyCoMod _ _ g_ _ g') (at level 25, right associativity) : poly_scope.

Definition PolyCoMod_rewrite B2 B1 B1' g_ g' :=
  (@PolyCoMod B2 B1 g_ B1' g').

Notation "g_ o>CoMod g'" :=
  (@PolyCoMod_rewrite _ _ _ g_ g') (at level 25, right associativity) : poly_scope.

Notation "'uCoMod'" := (@UnitCoMod _) (at level 0) : poly_scope.

Notation "@ 'uCoMod' B" :=
  (@UnitCoMod B) (at level 11, only parsing) : poly_scope.

Notation "~_1 @ B2 o>CoMod b1" :=
  (@Project_1 _ B2 _ b1) (at level 25, B2 at next level) : poly_scope.

Notation "~_1 o>CoMod b1" :=
  (@Project_1 _ _ _ b1) (at level 25) : poly_scope.

Notation "~_2 @ B1 o>CoMod b2" :=
  (@Project_2 B1 _ _ b2) (at level 25, B1 at next level) : poly_scope.

Notation "~_2 o>CoMod b2" :=
  (@Project_2 _ _ _ b2) (at level 25) : poly_scope.

Notation "<< g_1 ,CoMod g_2 >>" :=
  (@Limitator _ _ _ g_1 g_2) (at level 0 , format "<<  g_1  ,CoMod  g_2  >>") : poly_scope.

(**#+END_SRC

* Solution

The solution-conversion relation gives the sense in the solution-terminology : the relation contains the sense of the << eta-conversion >> [Limitator_Project_1_Project_2] that the pairing of the two projections is the identity , also oneself shall show later that the sense of << unresolved-cut polymorphism >> conversion ( "associativity" ) in the solution-terminology is already-derivable by induction . 

But moreover , the solution-conversion relation contains two logical solution-conversions [Project_1_Limitator Project_2_Limitator], which will be required by the confluence lemma later to dispose of the ambiguities in the choice of the logical cut-elimination rewriting-step ; while those ambiguities are already-disposed by the computational syntactic-case-matching in the computational cut-elimination chosen function

Memo that the description of the solution-conversion in this congruent-rewriting-style instead of the reduction-style is really necessary for later in [solveCoMod_PolyCoMod_cong_Pre_] [solveCoMod_PolyCoMod_cong_Post_] which show that the « resolved-cut » is congruent modulo solution-conversion .,

#+BEGIN_SRC coq :exports both :results silent **)

Module Sol.

  Section Section1.

    Inductive CoMod00 : obCoMod -> obCoMod -> Type :=

    | UnitCoMod : forall {B : obCoMod}, 'CoMod(0 B ~> B )0

    | Project_1 : forall B1 B2,
        forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0), 'CoMod(0 (Limit B1 B2) ~> B1' )0

    | Project_2 : forall B1 B2,
        forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0), 'CoMod(0 (Limit B1 B2) ~> B2' )0

    | Limitator : forall B1 B2 M,
        forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
          'CoMod(0 M ~> (Limit B1 B2) )0

  where "''CoMod' (0 B1 ~> B2 )0" := (@CoMod00 B1 B2).

  End Section1.

  Module Export Ex_Notations0.
    Delimit Scope sol_scope with sol.
    
    Notation "''CoMod' (0 B1 ~> B2 )0" := (@CoMod00 B1 B2) : sol_scope.

    Notation "'uCoMod'" := (@UnitCoMod _) (at level 0) : sol_scope.

    Notation "@ 'uCoMod' B" :=
      (@UnitCoMod B) (at level 11, only parsing) : sol_scope.

    Notation "~_1 @ B2 o>CoMod b1" :=
      (@Project_1 _ B2 _ b1) (at level 25, B2 at next level) : sol_scope.

    Notation "~_1 o>CoMod b1" :=
      (@Project_1 _ _ _ b1) (at level 25) : sol_scope.

    Notation "~_2 @ B1 o>CoMod b2" :=
      (@Project_2 B1 _ _ b2) (at level 25, B1 at next level) : sol_scope.

    Notation "~_2 o>CoMod b2" :=
      (@Project_2 _ _ _ b2) (at level 25) : sol_scope.

    Notation "<< g_1 ,CoMod g_2 >>" :=
      (@Limitator _ _ _ g_1 g_2) (at level 0, format "<<  g_1  ,CoMod  g_2  >>") : sol_scope.

  End Ex_Notations0.

  Definition toCoMod :
    forall (B1 B2 : obCoMod), 'CoMod(0 B1 ~> B2 )0 %sol -> 'CoMod(0 B1 ~> B2 )0.
  Proof.
    (move => B1 B2 g); elim : B1 B2 / g =>
    [ B
    | B1 B2 B1' b1 b1Sol
    | B1 B2 B2' b2 b2Sol
    | B1 B2 M g_1 g_1Sol g_2 g_2Sol ];
      [ apply: (@uCoMod B)
      | apply: (~_1 @ B2 o>CoMod b1Sol)
      | apply: (~_2 @ B1 o>CoMod b2Sol)
      | apply: (<< g_1Sol ,CoMod g_2Sol >>)].
  Defined.

  Definition toCoMod_injective :
    forall (B1 B2 : obCoMod) (g g' : 'CoMod(0 B1 ~> B2 )0 %sol),
      toCoMod g = toCoMod g' -> g = g' .
  Proof.
    intros B1 B2 g; induction g; dependent destruction g'; simpl in * ; try by [];
      ( move => HH ) ; dependent destruction HH;
        ( congr Project_1 || congr Project_2 || congr Limitator ); auto.
  Qed.

  Definition isSolb : forall (B1 B2 : obCoMod), forall (g : 'CoMod(0 B1 ~> B2 )0), bool.
  Proof.
    move => B1 B2 g. elim: B1 B2 / g.
    - intros; exact: false.

    - intros; exact: true.
    - intros; assumption.
    - intros; assumption.
    - move => B1 B2 M g_1 IH_g_1 g_2 IH_g_2; refine (IH_g_1 && IH_g_2).
  Defined.

  Lemma isSolb_isSol : forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0),
      isSolb g -> ({ gSol : 'CoMod(0 B1 ~> B2 )0 %sol | Sol.toCoMod gSol = g}).
  Proof.
    induction g; simpl in * ; intros Hsol;  try by [].
    exists (uCoMod)%sol. reflexivity.
    destruct IHg as [gSol Heq] => //. exists (~_1 o>CoMod gSol)%sol. simpl in *; rewrite Heq; reflexivity.
    destruct IHg as [gSol Heq] => //. exists (~_2 o>CoMod gSol)%sol. simpl in *; rewrite Heq; reflexivity.
    move : Hsol => /andP [] => * . destruct IHg1 as [gSol1 Heq1] => //. destruct IHg2 as [gSol2 Heq2] => //.  exists (<< gSol1 ,CoMod gSol2 >>)%sol. simpl in *; rewrite Heq1 Heq2; reflexivity. 
  Qed.
  
  Lemma isSolbN_isSolN : forall (B1 B2 : obCoMod),
      forall fSol : 'CoMod(0 B1 ~> B2 )0 %sol, forall (f : 'CoMod(0 B1 ~> B2 )0), (Sol.toCoMod fSol) = f -> Sol.isSolb f.
  Proof.
    move => B1 B2 fSol ; elim : B1 B2 / fSol ;
             intros; subst; try apply/andP; simpl; auto.
  Qed.

  Lemma isSolbN_isSolN_alt : forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0),
      ~~ isSolb g ->  ~ ( exists gSol : 'CoMod(0 B1 ~> B2 )0 %sol , (Sol.toCoMod gSol) = g ).
  Proof.
    intros F1 F2 f f_isSolbN []. move: f_isSolbN. apply/negP/negPn. apply: isSolbN_isSolN.
    eauto.
  Qed.


  Module Cong.

  Reserved Notation "g2 ~~~ g1" (at level 70).

  Module Project_1_Limitator.

    (* this conversion is for confluence only *)

    Variant convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 %sol -> 'CoMod(0 B1 ~> B2 )0 %sol -> Type :=
      
    | Project_1_Limitator : 
        forall B1 B2,
        forall B1'_1 (b1_1 : 'CoMod(0 B1 ~> B1'_1 )0 %sol),
        forall B1'_2 (b1_2 : 'CoMod(0 B1 ~> B1'_2 )0 %sol),
          ( ~_1 o>CoMod << b1_1 ,CoMod b1_2 >>)%sol
           ~~~ ( << ~_1 @ B2 o>CoMod b1_1 ,CoMod ~_1 @ B2 o>CoMod b1_2 >>
                 : 'CoMod(0 Limit B1 B2 ~> Limit B1'_1 B1'_2 )0 )%sol

    where "g2 ~~~ g1" := (@convCoMod _ _ g1 g2).
    
  End Project_1_Limitator.

  Module Project_2_Limitator.

    (* this conversion is for confluence only *)

    Variant convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 %sol -> 'CoMod(0 B1 ~> B2 )0 %sol -> Type :=
      
    | Project_2_Limitator : 
        forall B1 B2,
        forall B2'_1 (b2_1 : 'CoMod(0 B2 ~> B2'_1 )0 %sol),
        forall B2'_2 (b2_2 : 'CoMod(0 B2 ~> B2'_2 )0 %sol),
          ( ~_2 o>CoMod << b2_1 ,CoMod b2_2 >> )%sol
          ~~~ ( << ~_2 @ B1 o>CoMod b2_1 ,CoMod ~_2 @ B1 o>CoMod b2_2 >>
                : 'CoMod(0 Limit B1 B2 ~> Limit B2'_1 B2'_2 )0 )%sol

    where "g2 ~~~ g1" := (@convCoMod _ _ g1 g2).

  End Project_2_Limitator.

  Module Limitator_Project_1_Project_2.

    (* this conversion is for sense only *)

    Variant convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 %sol -> 'CoMod(0 B1 ~> B2 )0 %sol -> Type :=
      
    | Limitator_Project_1_Project_2 : forall B1 B2,
        ( uCoMod )%sol
        ~~~ ( << ~_1 @ B2 o>CoMod uCoMod ,CoMod ~_2 @ B1 o>CoMod uCoMod >>
              : 'CoMod(0 Limit B1 B2 ~> Limit B1 B2 )0 )%sol

    where "g2 ~~~ g1" := (@convCoMod _ _ g1 g2).
  
  End Limitator_Project_1_Project_2.

  Section Section1.
    
    Variable convCoMod_Atom : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 %sol -> 'CoMod(0 B1 ~> B2 )0 %sol -> Type .

    Inductive convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 %sol -> 'CoMod(0 B1 ~> B2 )0 %sol -> Type :=

    | ConvCoMod_Atom :
        ( forall (B1 B2 : obCoMod) (g2 : 'CoMod(0 B1 ~> B2 )0)
            (g1 : 'CoMod(0 B1 ~> B2 )0 %sol),
            @convCoMod_Atom _ _ g1 g2 -> g2 ~~~ g1 )%sol

    | Project_1_cong : ( forall B1 B2,
        forall B1' (b1 b1' : 'CoMod(0 B1 ~> B1' )0),
          b1' ~~~ b1 -> ( ~_1 @ B2 o>CoMod b1' ) ~~~ ( ~_1 @ B2 o>CoMod b1 ) )%sol

    | Project_2_cong : ( forall B1 B2,
        forall B2' (b2 b2' : 'CoMod(0 B2 ~> B2' )0),
          b2' ~~~ b2 -> ( ~_2 @ B1 o>CoMod b2' ) ~~~ ( ~_2 @ B1 o>CoMod b2 ) )%sol

    | Limitator_cong_1 : ( forall B1 B2 L,
        forall (g_1 g'_1 : 'CoMod(0 L ~> B1 )0) (g_2 : 'CoMod(0 L ~> B2 )0),
          g'_1 ~~~ g_1 ->
          ( << g'_1 ,CoMod g_2 >> ) ~~~ ( << g_1 ,CoMod g_2 >> ) )%sol
                                    
    | Limitator_cong_2 : ( forall B1 B2 L,
        forall (g_1 : 'CoMod(0 L ~> B1 )0) (g_2 g'_2: 'CoMod(0 L ~> B2 )0),
          g'_2 ~~~ g_2 ->
          ( << g_1 ,CoMod g'_2 >> ) ~~~ ( << g_1 ,CoMod g_2 >> ) )%sol
                                                                       
    where "g2 ~~~ g1" := (@convCoMod _ _ g1 g2).

    End Section1.

    Module Export Ex_Notations.
      Delimit Scope sol_cong_scope with sol_cong.
      Hint Constructors Project_1_Limitator.convCoMod.
      Hint Constructors Project_2_Limitator.convCoMod.
      Hint Constructors Limitator_Project_1_Project_2.convCoMod.
      Hint Constructors convCoMod.

      Notation "g2 ~~~ g1" := (@convCoMod _ _ _ g1 g2) (at level 70) : sol_cong_scope.
      Notation "g2 ~~~ g1 @ R" := (@convCoMod R _ _ g1 g2) (g1 at next level, at level 70) : sol_cong_scope.
    End Ex_Notations.

  End Cong.

  Module Once.
    
    Section Section1.
    Import Cong.Ex_Notations.
  
    Variant convCoMod : forall (B1 B2 : obCoMod),
        'CoMod(0 B1 ~> B2 )0 %sol -> 'CoMod(0 B1 ~> B2 )0 %sol -> Type :=

    | Project_1_Limitator : forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0 %sol),
        ( g2 ~~~ g1 @ Cong.Project_1_Limitator.convCoMod )%sol_cong -> g2 ~~~ g1

    | Project_2_Limitator : forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0 %sol),
        ( g2 ~~~ g1 @ Cong.Project_2_Limitator.convCoMod )%sol_cong -> g2 ~~~ g1

    | Limitator_Project_1_Project_2 : forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0 %sol),
        ( g2 ~~~ g1 @ Cong.Limitator_Project_1_Project_2.convCoMod )%sol_cong -> g2 ~~~ g1

    where "g2 ~~~ g1" := (@convCoMod _ _ g1 g2).

    End Section1.

    Module Export Ex_Notations.
      Export Cong.Ex_Notations.
      Delimit Scope sol_once_scope with sol_once.
      Hint Constructors convCoMod.
      
      Notation "g2 ~~~ g1" := (@convCoMod _ _ g1 g2) : sol_once_scope.
    End Ex_Notations.

  End Once.

  Section Section2.
  Import Once.Ex_Notations.

  Inductive convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 %sol -> 'CoMod(0 B1 ~> B2 )0 %sol -> Prop :=

  | convCoMod_Refl : forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0 %sol),
      g ~~~ g

  | convCoMod_List : forall (B1 B2 : obCoMod) (uTrans g : 'CoMod(0 B1 ~> B2 )0 %sol),
      ( uTrans ~~~ g )%sol_once -> forall (g0 : 'CoMod(0 B1 ~> B2 )0 %sol),
        ( g0 ~~~ uTrans ) -> g0 ~~~ g

  | convCoMod_List_Sym : forall (B1 B2 : obCoMod) (uTrans g : 'CoMod(0 B1 ~> B2 )0 %sol),
      ( g ~~~ uTrans )%sol_once -> forall (g0 : 'CoMod(0 B1 ~> B2 )0 %sol),
        ( g0 ~~~ uTrans ) -> g0 ~~~ g

  where "g2 ~~~ g1" := (@convCoMod _ _ g1 g2).

  End Section2.
  
  Module Export Ex_Notations1.
    Export Ex_Notations0.
    Export Once.Ex_Notations.
    Delimit Scope sol_conv_scope with sol_conv.
    Hint Constructors convCoMod.

    Notation "g2 ~~~ g1" := (@convCoMod _ _ g1 g2) : sol_conv_scope.
  End Ex_Notations1.

  Module _Atom_Cong.

    Lemma Project_1_Limitator : 
      forall B1 B2,
      forall B1'_1 (b1_1 : 'CoMod(0 B1 ~> B1'_1 )0 %sol),
      forall B1'_2 (b1_2 : 'CoMod(0 B1 ~> B1'_2 )0 %sol),
        ( ( ~_1 o>CoMod << b1_1 ,CoMod b1_2 >> )%sol
          ~~~ ( << ~_1 @ B2 o>CoMod b1_1 ,CoMod ~_1 @ B2 o>CoMod b1_2 >>
                : 'CoMod(0 Limit B1 B2 ~> Limit B1'_1 B1'_2 )0 )%sol )%sol_conv .
    Proof. eauto. Qed.

    Lemma Project_2_Limitator : 
      forall B1 B2,
      forall B2'_1 (b2_1 : 'CoMod(0 B2 ~> B2'_1 )0 %sol),
      forall B2'_2 (b2_2 : 'CoMod(0 B2 ~> B2'_2 )0 %sol),
        ( ( ~_2 o>CoMod << b2_1 ,CoMod b2_2 >> )%sol
          ~~~ ( << ~_2 @ B1 o>CoMod b2_1 ,CoMod ~_2 @ B1 o>CoMod b2_2 >>
                : 'CoMod(0 Limit B1 B2 ~> Limit B2'_1 B2'_2 )0 )%sol )%sol_conv .
    Proof. eauto. Qed.

    Lemma Limitator_Project_1_Project_2 : forall B1 B2,
        ( ( uCoMod )%sol
        ~~~ ( << ~_1 @ B2 o>CoMod uCoMod ,CoMod ~_2 @ B1 o>CoMod uCoMod >>
              : 'CoMod(0 Limit B1 B2 ~> Limit B1 B2 )0 )%sol )%sol_conv.
    Proof. eauto. Qed.

    Lemma Project_1_cong :
      ( forall B1 B2, forall B1' (b1 b1' : 'CoMod(0 B1 ~> B1' )0),
            ( b1' ~~~ b1 ) -> ( ( ~_1 @ B2 o>CoMod b1' ) ~~~ ( ~_1 @ B2 o>CoMod b1 ) ) ) %sol %sol_conv .
    Proof.
      induction 1; [ | destruct X; [ destruct c | destruct c | idtac ] .. ]; eauto .
    Defined.

    Lemma Project_2_cong :
      ( forall B1 B2, forall B2' (b2 b2' : 'CoMod(0 B2 ~> B2' )0),
          ( b2' ~~~ b2 ) -> ( ( ~_2 @ B1 o>CoMod b2' ) ~~~ ( ~_2 @ B1 o>CoMod b2 ) ) )%sol %sol_conv .
    Proof.
      induction 1; [ | destruct X; [ destruct c | destruct c | idtac ] .. ]; eauto .
    Defined.

    Lemma Limitator_cong_1 :
      ( forall B1 B2 L, forall (g_1 g'_1 : 'CoMod(0 L ~> B1 )0) (g_2 : 'CoMod(0 L ~> B2 )0),
          (g'_1 ~~~ g_1) ->
          ( ( << g'_1 ,CoMod g_2 >> ) ~~~ ( << g_1 ,CoMod g_2 >> ) ) )%sol %sol_conv .
    Proof.
      induction 1; [ | destruct X; [ destruct c | destruct c | idtac ] .. ]; eauto .
    Defined.

    Lemma Limitator_cong_2 :
      ( forall B1 B2 L, forall (g_1 : 'CoMod(0 L ~> B1 )0) (g_2 g'_2: 'CoMod(0 L ~> B2 )0),
            (g'_2 ~~~ g_2) ->
            ( ( << g_1 ,CoMod g'_2 >> ) ~~~ ( << g_1 ,CoMod g_2 >> ) ) )%sol %sol_conv .
    Proof.
      induction 1; [ | destruct X; [ destruct c | destruct c | idtac ] .. ]; eauto .
    Defined.

    Module Export Ex_Notations0.

      Hint Resolve Project_1_Limitator Project_2_Limitator Limitator_Project_1_Project_2.
      Hint Resolve Project_1_cong Project_2_cong Limitator_cong_1 Limitator_cong_2 .

      Definition tac_Sol := ( Project_1_Limitator , Project_2_Limitator , Limitator_Project_1_Project_2 ) .

    End Ex_Notations0.

    Lemma convCoMod_Trans :
      ( forall (B1 B2 : obCoMod) (uTrans g1 : 'CoMod(0 B1 ~> B2 )0) (Hrew1 : (uTrans ~~~ g1) ),
          forall g3 (Hrew2 : (g3 ~~~ uTrans) ), (g3 ~~~ g1) )%sol %sol_conv.
    Proof.
      induction 1; eauto.
    Defined.

    Section Section1.

      Hint Resolve convCoMod_Trans .

      Lemma Limitator_cong_12 :
        ( forall B1 B2 L, forall (g_1 g'_1 : 'CoMod(0 L ~> B1 )0) (g_2 g'_2 : 'CoMod(0 L ~> B2 )0),
              (g'_1 ~~~ g_1) -> (g'_2 ~~~ g_2) ->
              ( ( << g'_1 ,CoMod g'_2 >> ) ~~~ ( << g_1 ,CoMod g_2 >> ) ) )%sol %sol_conv .
      Proof.
        eauto.
      Defined.

      Lemma convCoMod_Sym :
        ( forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0) (Hsol_conv : (g2 ~~~ g1)),
          (g1 ~~~ g2) ) %sol %sol_conv.
      Proof.
        induction 1; eauto. 
      Defined.

    End Section1.
    
    Module Export Ex_Notations.
      Export Ex_Notations0.
      Hint Resolve convCoMod_Trans convCoMod_Sym Limitator_cong_12.

      Hint Rewrite Project_1_Limitator Project_2_Limitator Limitator_Project_1_Project_2. 

      Add Parametric Relation (B1 B2 : obCoMod) : ('CoMod(0 B1 ~> B2 )0 %sol) (@convCoMod B1 B2)
          reflexivity proved by
          (@convCoMod_Refl B1 B2)
          symmetry proved by
          (fun x y => @convCoMod_Sym B1 B2 y x)
          transitivity proved by
          (fun x y z r1 r2 => (@convCoMod_Trans B1 B2 y x r1 z r2))
            as convCoMod_rewrite.

      Add Parametric Morphism B1 B2 B1' :
        (@Project_1 B1 B2 B1') with
          signature ((@convCoMod B1 B1')
                       ==> (@convCoMod (Limit B1 B2) B1'))
            as Project_1_cong_rewrite.
          by move => *; apply: Project_1_cong. Qed.

      Add Parametric Morphism B1 B2 B2' :
        (@Project_2 B1 B2 B2') with
          signature ((@convCoMod B2 B2')
                       ==> (@convCoMod (Limit B1 B2) B2'))
            as Project_2_cong_rewrite.
          by move => *; apply: Project_2_cong. Qed.

      Add Parametric Morphism B1 B2 M :
        (@Limitator B1 B2 M) with
          signature ((@convCoMod M B1)
                       ==> (@convCoMod M B2)
                       ==> (@convCoMod M (Limit B1 B2)))
            as Limitator_cong_rewrite.
          by eauto. Qed.

    End Ex_Notations.

  End _Atom_Cong.

(**#+END_SRC

** Grade of solution-conversion for combined non-structural induction

Later oneself shall do some non-structural induction which combine (sum) the structural induction over this solution-conversion together with some non-structural induction over the morphisms ., Therefore oneself may translate this structural induction instead over the integers , such that to be able to sum all the involved integers

#+BEGIN_SRC coq :exports both :results silent **)

  Definition gradeConv : forall (B1 B2 : obCoMod)
                           (g g0 : 'CoMod(0 B1 ~> B2 )0 %sol),   ( g0 ~~~ g )%sol_once ->  Z.
  Proof.
    destruct 1; [ ( induction c;
                    [ refine (1)%Z
                    | refine (1 + IHc)%Z
                    | refine (1 + IHc)%Z
                     | refine (1 + IHc)%Z
                     | refine (1 + IHc)%Z ] ) .. ].
  Defined.

  Lemma gradeConv_gt0 :
    forall (B1 B2 : obCoMod)
      (g g0 : 'CoMod(0 B1 ~> B2 )0 %sol) (Hconv : ( g0 ~~~ g )%sol_once),
      (1 <= (gradeConv Hconv))%Z.
  Proof.
    destruct Hconv; [ ( induction c; simpl in *; intros; abstract nia ) ..] .
  Qed.

  Module Export Ex_Notations.
    Export Ex_Notations1.
    Export _Atom_Cong.Ex_Notations.

    Ltac tac_gradeConv_gt0_sol :=
      match goal with
      | [ Hconv1 : ( _ ~~~ _ )%sol_once ,
                   Hconv2 : ( _ ~~~ _ )%sol_once |- _ ] =>
        move : (@Sol.gradeConv_gt0 _ _ _ _ Hconv1)
                 (@Sol.gradeConv_gt0 _ _ _ _ Hconv2)
      | [ Hconv1 : ( _ ~~~ _ )%sol_once |- _ ] =>
        move : (@Sol.gradeConv_gt0 _ _ _ _ Hconv1)
      end .

  End Ex_Notations.
  
(**#+END_SRC

** Destruction of solution-morphisms with inner-instantiation of object-indexes

Instead of the general [dependent destruction] tactic which may add logical axiom, 
oneself may program particular lemmas for (dependent-)destruction with inner instantiations of indexes :

#+BEGIN_SRC coq :exports both :results silent **)

  Module Destruct_domLimit.

    Inductive CoMod00_domLimit : forall (B1 B1' B2 : obCoMod),
      ( 'CoMod(0 Limit B1 B1' ~> B2 )0 %sol ) -> Type :=

    | UnitCoMod : forall {B B' : obCoMod}, CoMod00_domLimit (@uCoMod (Limit B B'))%sol

    | Project_1 : forall B1 B2,
        forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0),
          CoMod00_domLimit (~_1 @ B2 o>CoMod b1)%sol 

    | Project_2 : forall B1 B2,
        forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0),
          CoMod00_domLimit (~_2 @ B1 o>CoMod b2)%sol 

    | Limitator : forall B1 B2 M M',
        forall (g_1 : 'CoMod(0 Limit M M' ~> B1 )0 %sol) (g_2 : 'CoMod(0 Limit M M' ~> B2 )0 %sol),
          CoMod00_domLimit (<< g_1 ,CoMod g_2 >>)%sol

    where "''CoMod' (0 B1 ~> B2 )0" := (@CoMod00 B1 B2).

    Lemma CoMod00_domLimitP : forall B1 B2 ( g : 'CoMod(0 B1 ~> B2 )0 %sol ),
        ltac:( destruct B1; intros; [ refine (CoMod00_domLimit g) ] ).
    Proof.
      move => B1 B2 g. case : B1 B2 / g.
      - destruct B.
        constructor 1.
      - destruct B1.
        constructor 2.
      - constructor 3.
      - destruct M.
        constructor 4.
    Defined.

  End Destruct_domLimit.

End Sol.

(**#+END_SRC

* Congruent-Rewriting relation

For the logical confluence lemma, oneself shall proceed with congruent (inner) step rewriting-style cut-elimination resolution instead of the total asymptotic reduction-style cut-elimination resolution which is sufficient for the computational polymorphism/cut-elimination but not sufficient for the logical confluence lemma  .,

#+BEGIN_SRC coq :exports both :results silent **)

Module Cong.

  Reserved Notation "g2 <~~ g1" (at level 70).

  Module CoMod_unit.

    Variant convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type :=
      
    | CoMod_unit :
        forall (B B' : obCoMod) (f : 'CoMod(0 B ~> B' )0),
          ( f )
            <~~ ( ( uCoMod ) o>CoMod f
                : 'CoMod(0 B ~> B' )0 )

    where "g2 <~~ g1" := (@convCoMod _ _ g1 g2).
    
  End CoMod_unit.

  Module CoMod_inputUnitCoMod.

    Variant convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type :=
      
    | CoMod_inputUnitCoMod :
        forall (B' B : obCoMod) (g : 'CoMod(0 B' ~> B )0),
          ( g )
            <~~  ( g o>CoMod ( uCoMod )
                 : 'CoMod(0 B' ~> B )0 )

    where "g2 <~~ g1" := (@convCoMod _ _ g1 g2).

  End CoMod_inputUnitCoMod.

  Module Project_1_morphism.

    Variant convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type :=
      
    | Project_1_morphism : forall B1 B2,
        forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0)
          B1'' (b1' : 'CoMod(0 B1' ~> B1'' )0),
          ( ~_1 @ B2 o>CoMod (b1 o>CoMod b1') )
            <~~ ( ( ~_1 @ B2 o>CoMod b1 ) o>CoMod b1'
                : 'CoMod(0 Limit B1 B2 ~> B1'' )0 )

    where "g2 <~~ g1" := (@convCoMod _ _ g1 g2).
  
  End Project_1_morphism.

  Module Project_2_morphism.

    Variant convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type :=
      
    | Project_2_morphism : forall B1 B2,
        forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0)
          B2'' (b2' : 'CoMod(0 B2' ~> B2'' )0),
          ( ~_2 @ B1 o>CoMod (b2 o>CoMod b2') )
            <~~ ( ( ~_2 @ B1 o>CoMod b2 ) o>CoMod b2'
                : 'CoMod(0 Limit B1 B2 ~> B2'' )0 )

    where "g2 <~~ g1" := (@convCoMod _ _ g1 g2).
    
  End Project_2_morphism.

  Module Limitator_morphism.

    Variant convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type :=
      
    | Limitator_morphism : forall B1 B2 M,
        forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0)
          M' (m : 'CoMod(0 M' ~> M )0),
          ( << m o>CoMod g_1 ,CoMod m o>CoMod g_2 >> )
            <~~ ( m o>CoMod << g_1 ,CoMod g_2 >>
                : 'CoMod(0 M' ~> Limit B1 B2 )0 )

    where "g2 <~~ g1" := (@convCoMod _ _ g1 g2).
    
  End Limitator_morphism.

  Module Limitator_Project_1.

    Variant convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type :=
      
    | Limitator_Project_1 : forall B1 B2 M,
        forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
        forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0),
          ( g_1 o>CoMod b1 )
            <~~ ( << g_1 ,CoMod g_2 >> o>CoMod ( ~_1 @ B2 o>CoMod b1)
                : 'CoMod(0 M ~> B1' )0 )

    where "g2 <~~ g1" := (@convCoMod _ _ g1 g2).
    
  End Limitator_Project_1.

  Module Limitator_Project_2.

    Variant convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type :=
      
    | Limitator_Project_2 : forall B1 B2 M,
        forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
        forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0),
          ( g_2 o>CoMod b2 )
            <~~ ( << g_1 ,CoMod g_2 >> o>CoMod ( ~_2 @ B1 o>CoMod b2)
                : 'CoMod(0 M ~> B2' )0 )

    where "g2 <~~ g1" := (@convCoMod _ _ g1 g2).
    
  End Limitator_Project_2.

  
  (* Limitator_Project_1_Project_2 Project_1_Limitator Project_2_Limitator are OK for 
     the degradation lemma , but things are smoother when 
     the irreductibility coincides with solution , ref lemma isSolb_isRed_False_alt 
     and lemma uniquesolution *)
  Section Section1.
    
    Variable convCoMod_Atom : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type .

    Inductive convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type :=

    | ConvCoMod_Atom :
        forall (B1 B2 : obCoMod) (g2 : 'CoMod(0 B1 ~> B2 )0)
          (g1 : 'CoMod(0 B1 ~> B2 )0),
          @convCoMod_Atom _ _ g1 g2 -> g2 <~~ g1

    | PolyCoMod_cong_Pre :
        forall (B B' : obCoMod) (g_ g_0 : 'CoMod(0 B ~> B' )0),
        forall (B'' : obCoMod) (g' : 'CoMod(0 B' ~> B'' )0),
          g_0 <~~ g_ -> ( g_0 o>CoMod g' ) <~~ ( g_ o>CoMod g' )

    | PolyCoMod_cong_Post :
        forall (B B' : obCoMod) (g_ : 'CoMod(0 B ~> B' )0),
        forall (B'' : obCoMod) (g' g'0 : 'CoMod(0 B' ~> B'' )0),
          g'0 <~~ g' -> ( g_ o>CoMod g'0 ) <~~ ( g_ o>CoMod g' )

    | Project_1_cong : forall B1 B2,
        forall B1' (b1 b1' : 'CoMod(0 B1 ~> B1' )0),
          b1' <~~ b1 -> ( ~_1 @ B2 o>CoMod b1' ) <~~ ( ~_1 @ B2 o>CoMod b1 )

    | Project_2_cong : forall B1 B2,
        forall B2' (b2 b2' : 'CoMod(0 B2 ~> B2' )0),
          b2' <~~ b2 -> ( ~_2 @ B1 o>CoMod b2' ) <~~ ( ~_2 @ B1 o>CoMod b2 )

    | Limitator_cong_1 : forall B1 B2 L,
        forall (g_1 g'_1 : 'CoMod(0 L ~> B1 )0) (g_2 : 'CoMod(0 L ~> B2 )0),
          g'_1 <~~ g_1 ->
          ( << g'_1 ,CoMod g_2 >> ) <~~ ( << g_1 ,CoMod g_2 >> )
                                    
    | Limitator_cong_2 : forall B1 B2 L,
        forall (g_1 : 'CoMod(0 L ~> B1 )0) (g_2 g'_2: 'CoMod(0 L ~> B2 )0),
          g'_2 <~~ g_2 ->
          ( << g_1 ,CoMod g'_2 >> ) <~~ ( << g_1 ,CoMod g_2 >> )
                                                                       
    where "g2 <~~ g1" := (@convCoMod _ _ g1 g2).

    End Section1.

    Module Export Ex_Notations.
      Delimit Scope cong_scope with cong.
      Hint Constructors CoMod_unit.convCoMod.
      Hint Constructors CoMod_inputUnitCoMod.convCoMod.
      Hint Constructors Project_1_morphism.convCoMod.
      Hint Constructors Project_2_morphism.convCoMod.
      Hint Constructors Limitator_morphism.convCoMod.
      Hint Constructors Limitator_Project_1.convCoMod.
      Hint Constructors Limitator_Project_2.convCoMod.
      Hint Constructors convCoMod.

      Notation "g2 <~~ g1" := (@convCoMod _ _ _ g1 g2) (at level 70) : cong_scope.
      Notation "g2 <~~ g1 @ R" := (@convCoMod R _ _ g1 g2) (g1 at next level, at level 70) : cong_scope.
    End Ex_Notations.

End Cong.

Module Once.
    
  Section Section1.
  Import Cong.Ex_Notations.
  
  Variant convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type :=

  (* 3 -- units *)

  | CoMod_unit : forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0),
      ( g2 <~~ g1 @ Cong.CoMod_unit.convCoMod )%cong -> g2 <~~ g1

  | CoMod_inputUnitCoMod : forall (B1 B2 : obCoMod) (g2 g1: 'CoMod(0 B1 ~> B2 )0),
      ( g2 <~~ g1 @ Cong.CoMod_inputUnitCoMod.convCoMod )%cong -> g2 <~~ g1

  (* 4 -- polymorphisms *)

  | Project_1_morphism : forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0),
      ( g2 <~~ g1 @ Cong.Project_1_morphism.convCoMod )%cong -> g2 <~~ g1

  | Project_2_morphism : forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0),
      ( g2 <~~ g1 @ Cong.Project_2_morphism.convCoMod )%cong -> g2 <~~ g1

  | Limitator_morphism : forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0),
      ( g2 <~~ g1 @ Cong.Limitator_morphism.convCoMod )%cong -> g2 <~~ g1

  (* 7 -- projection cancel particular-pairing *)

  | Limitator_Project_1 : forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0),
      ( g2 <~~ g1 @ Cong.Limitator_Project_1.convCoMod )%cong -> g2 <~~ g1

  | Limitator_Project_2 : forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0),
      ( g2 <~~ g1 @ Cong.Limitator_Project_2.convCoMod )%cong -> g2 <~~ g1

  where "g2 <~~ g1" := (@convCoMod _ _ g1 g2).

  End Section1.

  Module Export Ex_Notations.
    Export Cong.Ex_Notations.
    Delimit Scope once_scope with once.
    Hint Constructors convCoMod.

    Notation "g2 <~~ g1" := (@convCoMod _ _ g1 g2) : once_scope.
  End Ex_Notations.

End Once.

Module Rewrite.

  Section Section1.
  Import Once.Ex_Notations.
  
  Inductive convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Prop :=

  | convCoMod_Refl : forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0),
      g <~~ g

  | convCoMod_List : forall (B1 B2 : obCoMod) (uTrans g : 'CoMod(0 B1 ~> B2 )0),
      ( uTrans <~~ g )%once -> forall (g0 : 'CoMod(0 B1 ~> B2 )0),
        ( g0 <~~ uTrans ) -> g0 <~~ g

  where "g2 <~~ g1" := (@convCoMod _ _ g1 g2).

  End Section1.
  
  Module Export Ex_Notations0.
    Export Once.Ex_Notations.
    Delimit Scope rew_scope with rew.
    Hint Constructors convCoMod.

    Notation "g2 <~~ g1" := (@convCoMod _ _ g1 g2) : rew_scope.
  End Ex_Notations0.
  
  Module _Atom_Cong.

    Lemma CoMod_unit :
        forall (B B' : obCoMod) (f : 'CoMod(0 B ~> B' )0),
          ( ( f )
            <~~ ( ( uCoMod ) o>CoMod f
                : 'CoMod(0 B ~> B' )0 ) ) %rew .
    Proof. eauto. Qed.

    Lemma CoMod_inputUnitCoMod :
        forall (B' B : obCoMod) (g : 'CoMod(0 B' ~> B )0),
          ( ( g )
              <~~  ( g o>CoMod ( uCoMod )
                   : 'CoMod(0 B' ~> B )0 ) )%rew .
    Proof. eauto. Qed.

    Lemma Project_1_morphism : forall B1 B2,
        forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0)
          B1'' (b1' : 'CoMod(0 B1' ~> B1'' )0),
          ( ( ~_1 @ B2 o>CoMod (b1 o>CoMod b1') )
              <~~ ( ( ~_1 @ B2 o>CoMod b1 ) o>CoMod b1'
                  : 'CoMod(0 Limit B1 B2 ~> B1'' )0 ) )%rew .
    Proof. eauto. Qed.

    Lemma Project_2_morphism : forall B1 B2,
        forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0)
          B2'' (b2' : 'CoMod(0 B2' ~> B2'' )0),
          ( ( ~_2 @ B1 o>CoMod (b2 o>CoMod b2') )
              <~~ ( ( ~_2 @ B1 o>CoMod b2 ) o>CoMod b2'
                  : 'CoMod(0 Limit B1 B2 ~> B2'' )0 ) )%rew .
    Proof. eauto. Qed.
      
    Lemma Limitator_morphism : forall B1 B2 M,
        forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0)
          M' (m : 'CoMod(0 M' ~> M )0),
          ( ( << m o>CoMod g_1 ,CoMod m o>CoMod g_2 >> )
              <~~ ( m o>CoMod << g_1 ,CoMod g_2 >>
                  : 'CoMod(0 M' ~> Limit B1 B2 )0 ) )%rew .
    Proof. eauto. Qed.

    Lemma Limitator_Project_1 : forall B1 B2 M,
        forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
        forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0),
          ( ( g_1 o>CoMod b1 )
              <~~ ( << g_1 ,CoMod g_2 >> o>CoMod ( ~_1 @ B2 o>CoMod b1)
                  : 'CoMod(0 M ~> B1' )0 ) )%rew .
    Proof. eauto. Qed.

    Lemma Limitator_Project_2 : forall B1 B2 M,
        forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
        forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0),
          ( ( g_2 o>CoMod b2 )
              <~~ ( << g_1 ,CoMod g_2 >> o>CoMod ( ~_2 @ B1 o>CoMod b2)
                  : 'CoMod(0 M ~> B2' )0 ) )%rew .
    Proof. eauto. Qed.
    
    Lemma convCoMod_Trans :
      forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0) (Hrew1 : (g2 <~~ g1)%rew),
      forall g3 (Hrew2 : (g3 <~~ g2)%rew), (g3 <~~ g1) %rew .
    Proof.
      induction 1; eauto.
    Defined.

    Lemma PolyCoMod_cong_Pre :
        forall (B B' : obCoMod) (g_ g_0 : 'CoMod(0 B ~> B' )0),
        forall (B'' : obCoMod) (g' : 'CoMod(0 B' ~> B'' )0),
          ( g_0 <~~ g_ )%rew  -> ( ( g_0 o>CoMod g' ) <~~ ( g_ o>CoMod g' ) )%rew .
    Proof.
      induction 1; [ | destruct X ]; eauto .
    Defined.

    Lemma PolyCoMod_cong_Post :
        forall (B B' : obCoMod) (g_ : 'CoMod(0 B ~> B' )0),
        forall (B'' : obCoMod) (g' g'0 : 'CoMod(0 B' ~> B'' )0),
          ( g'0 <~~ g' )%rew -> ( ( g_ o>CoMod g'0 ) <~~ ( g_ o>CoMod g' ) )%rew .
    Proof.
      induction 1; [ | destruct X ]; eauto .
    Defined.

    Lemma Project_1_cong : forall B1 B2,
        forall B1' (b1 b1' : 'CoMod(0 B1 ~> B1' )0),
          ( b1' <~~ b1 )%rew -> ( ( ~_1 @ B2 o>CoMod b1' ) <~~ ( ~_1 @ B2 o>CoMod b1 ) )%rew .
    Proof.
      induction 1; [ | destruct X ]; eauto .
    Defined.

    Lemma Project_2_cong : forall B1 B2,
        forall B2' (b2 b2' : 'CoMod(0 B2 ~> B2' )0),
          ( b2' <~~ b2 )%rew -> ( ( ~_2 @ B1 o>CoMod b2' ) <~~ ( ~_2 @ B1 o>CoMod b2 ) )%rew .
    Proof.
      induction 1; [ | destruct X ]; eauto .
    Defined.

    Lemma Limitator_cong_1 :  forall B1 B2 L,
        forall (g_1 g'_1 : 'CoMod(0 L ~> B1 )0) (g_2 : 'CoMod(0 L ~> B2 )0),
          (g'_1 <~~ g_1)%rew ->
          ( ( << g'_1 ,CoMod g_2 >> ) <~~ ( << g_1 ,CoMod g_2 >> ) )%rew .
    Proof.
      induction 1; [ | destruct X ]; eauto .
    Defined.

    Lemma Limitator_cong_2 : forall B1 B2 L,
        forall (g_1 : 'CoMod(0 L ~> B1 )0) (g_2 g'_2: 'CoMod(0 L ~> B2 )0),
          (g'_2 <~~ g_2)%rew ->
          ( ( << g_1 ,CoMod g'_2 >> ) <~~ ( << g_1 ,CoMod g_2 >> ) )%rew .
    Proof.
      induction 1; [ | destruct X ]; eauto .
    Defined.

    Module Export Ex_Notations.

      Hint Resolve CoMod_unit  CoMod_inputUnitCoMod  Project_1_morphism  Project_2_morphism Limitator_morphism Limitator_Project_1 Limitator_Project_2.
      Hint Resolve convCoMod_Trans (*TODO: Trans? *) PolyCoMod_cong_Pre PolyCoMod_cong_Post Project_1_cong Project_2_cong Limitator_cong_1 Limitator_cong_2 .
      Hint Rewrite CoMod_unit  CoMod_inputUnitCoMod  Project_1_morphism  Project_2_morphism Limitator_morphism Limitator_Project_1 Limitator_Project_2.
      Hint Rewrite PolyCoMod_cong_Pre PolyCoMod_cong_Post Project_1_cong Project_2_cong Limitator_cong_1 Limitator_cong_2 .

      Definition tac_Rewrite := (CoMod_unit, CoMod_inputUnitCoMod, Project_1_morphism, Project_2_morphism, Limitator_morphism, Limitator_Project_1, Limitator_Project_2).
      
      Ltac tac_assumption_rewrite_ :=
        match goal with
        | [ HH1 : ( _ <~~ _ )%rew , HH2 : ( _ <~~ _ )%rew ,
                                        HH3 : ( _ <~~ _ )%rew , HH4 : ( _ <~~ _ )%rew |- _ ] =>
          rewrite !(HH1 , HH2 , HH3 , HH4 , tac_Rewrite)
        | [ HH1 : ( _ <~~ _ )%rew , HH2 : ( _ <~~ _ )%rew ,
                                        HH3 : ( _ <~~ _ )%rew , HH4 : ( _ <~~ _ )%rew |- _ ] =>
          rewrite !(HH1 , HH2 , HH3 , HH4 , tac_Rewrite)
        | [ HH1 : ( _ <~~ _ )%rew , HH2 : ( _ <~~ _ )%rew ,
                                        HH3 : ( _ <~~ _ )%rew |- _ ] =>
          rewrite !(HH1 , HH2 , HH3 , tac_Rewrite)
        | [ HH1 : ( _ <~~ _ )%rew , HH2 : ( _ <~~ _ )%rew |- _ ] =>
          rewrite !(HH1 , HH2 , tac_Rewrite)
        | [ HH1 : ( _ <~~ _ )%rew |- _ ] =>
          rewrite !(HH1 , tac_Rewrite)
        end.

      Ltac tac_assumption_rewrite :=
        simpl in *; intros; (abstract
                               intuition (eauto; tac_assumption_rewrite_; eauto)).

      Add Parametric Relation (B1 B2 : obCoMod) : ('CoMod(0 B1 ~> B2 )0) (@convCoMod B1 B2)
          reflexivity proved by
          (@convCoMod_Refl B1 B2)
          transitivity proved by
          (fun x y z r1 r2 => (@convCoMod_Trans B1 B2 y x r1 z r2))
            as convCoMod_rewrite.

      Add Parametric Morphism B2 B1 B1' :
        (@PolyCoMod_rewrite B2 B1 B1' ) with
          signature ((@convCoMod B2 B1)
                       ==> (@convCoMod B1 B1')
                       ==> (@convCoMod B2 B1'))
            as PolyCoMod_cong_rewrite.
          by eauto. Qed.

      Add Parametric Morphism B1 B2 B1' :
        (@Project_1 B1 B2 B1') with
          signature ((@convCoMod B1 B1')
                       ==> (@convCoMod (Limit B1 B2) B1'))
            as Project_1_cong_rewrite.
          by move => *; apply: Project_1_cong. Qed.

      Add Parametric Morphism B1 B2 B2' :
        (@Project_2 B1 B2 B2') with
          signature ((@convCoMod B2 B2')
                       ==> (@convCoMod (Limit B1 B2) B2'))
            as Project_2_cong_rewrite.
          by move => *; apply: Project_2_cong. Qed.

      Add Parametric Morphism B1 B2 M :
        (@Limitator B1 B2 M) with
          signature ((@convCoMod M B1)
                       ==> (@convCoMod M B2)
                       ==> (@convCoMod M (Limit B1 B2)))
            as Limitator_cong_rewrite.
          by eauto. Qed.

    End Ex_Notations.

  End _Atom_Cong.

(**#+END_SRC

** Non-linear mimicking grade function

This grade [gradeParticular] is some non-linear function from the morphisms to the integers which mimicks the structure of the morphisms, such that the multiplication-function mimicks the cut constructor and the addition-function mimicks the pairing constructor and other constructors, and such that the distributivity of the cut operation over the pairing operation becomes some degradation via the distributivity of multiplication over the addition .,

In the earlier texts for the reduction-style cut-elimination for the localizations (which includes the pairing-projections) , the grade function [gradeTotal] was some linear function where the max function asymtotically corresponds to the pairing constructor

#+BEGIN_SRC coq :exports both :results silent **)

  Definition gradeParticular :
    forall (B1 B2 : obCoMod), 'CoMod(0 B1 ~> B2 )0 -> Z.
  Proof.
    move => B1 B2 g; elim : B1 B2 / g.
    - (* PolyCoMod *)
      move => B2 B1 g_ gradeParticular_g_ B1' g' gradeParticular_g' ;
               exact (3 * (gradeParticular_g_ * gradeParticular_g'))%Z .
    - (* UnitCoMod *)
      intros; exact (1)%Z.
    - (* Project_1  *)
      move => B1 B2 B1' b1 gradeParticular_b1.
      exact (1 + (gradeParticular_b1))%Z.
    - (* Project_2  *)
      move => B1 B2 B2' b2 gradeParticular_b2.
      exact (1 + (gradeParticular_b2))%Z.
    - (* Limitator *)
      move => B1 B2 M g_1 gradeParticular_g_1 g_2 gradeParticular_g_2.
      exact (1 + (gradeParticular_g_1 + gradeParticular_g_2))%Z .
  Defined.

  Lemma gradeParticular_gt0 :
    forall (B1 B2 : obCoMod) ( g : 'CoMod(0 B1 ~> B2 )0),
      (1 <= (gradeParticular g))%Z.
  Proof.
    induction g; simpl in *; intros; abstract nia.
  Qed.

  Lemma isSolb_isRed_False_alt : forall (B1 B2 : obCoMod) (f : 'CoMod(0 B1 ~> B2 )0),
      forall fRed, (fRed <~~ f)%once -> ~~ Sol.isSolb f .
  Proof.
    destruct 1; [
      ( induction c; [ destruct c | idtac .. ];
        move => //= ; repeat match goal with
                            | [ HH : is_true (Sol.isSolb _)  |- _ ] =>
                              try rewrite -> HH in *; clear HH
                            | [   |- context [Sol.isSolb ?ggg]  ] => destruct (Sol.isSolb ggg)
                            end;
               simpl; move => //= ) .. ] .
  Qed.

  Module Export Ex_Notations1.
    Export Ex_Notations0.
    Export _Atom_Cong.Ex_Notations.
    Import Sol.Ex_Notations.
    
    Ltac tac_isSolb :=
      repeat match goal with
             | [ HH : ( _ <~~ _ )%once  |- _ ] =>
               move : (Rewrite.isSolb_isRed_False_alt HH) ; clear HH
             | [ HH : is_true (Sol.isSolb _)  |- _ ] =>
               try rewrite -> HH in *; clear HH
             | [ HH : is_true (~~ Sol.isSolb _)  |- _ ] =>
               try rewrite -> (negbTE HH) in *; clear HH
             | [   |- context [Sol.isSolb ?ggg]  ] => destruct (Sol.isSolb ggg)
             end.
    
    Ltac tac_gradeParticular_gt0 :=
      match goal with
      | [ gg1 : 'CoMod(0 _ ~> _ )0 ,
                gg2 : 'CoMod(0 _ ~> _ )0 ,
                      gg3 : 'CoMod(0 _ ~> _ )0 ,
                            gg4 : 'CoMod(0 _ ~> _ )0 |- _ ] =>
        move : (@Rewrite.gradeParticular_gt0 _ _ gg1) (@Rewrite.gradeParticular_gt0 _ _ gg2)
                                                 (@Rewrite.gradeParticular_gt0 _ _ gg3)
                                                 (@Rewrite.gradeParticular_gt0 _ _ gg4)
      | [ gg1 : 'CoMod(0 _ ~> _ )0 ,
                gg2 : 'CoMod(0 _ ~> _ )0 ,
                      gg3 : 'CoMod(0 _ ~> _ )0 |- _ ] =>
        move : (@Rewrite.gradeParticular_gt0 _ _ gg1) (@Rewrite.gradeParticular_gt0 _ _ gg2)
                                                 (@Rewrite.gradeParticular_gt0 _ _ gg3)
      | [ gg1 : 'CoMod(0 _ ~> _ )0 ,
                gg2 : 'CoMod(0 _ ~> _ )0 |- _ ] =>
        move : (@Rewrite.gradeParticular_gt0 _ _ gg1) (@Rewrite.gradeParticular_gt0 _ _ gg2) 
      | [ gg1 : 'CoMod(0 _ ~> _ )0 |- _ ] =>
        move : (@Rewrite.gradeParticular_gt0 _ _ gg1)
      end.

    Ltac tac_gradeParticular_gt0_sol :=
      match goal with
      | [ gg1 : 'CoMod(0 _ ~> _ )0 %sol ,
                gg2 : 'CoMod(0 _ ~> _ )0 %sol ,
                      gg3 : 'CoMod(0 _ ~> _ )0 %sol ,
                            gg4 : 'CoMod(0 _ ~> _ )0 %sol ,
                                  gg5 : 'CoMod(0 _ ~> _ )0 %sol ,
                                        gg6 : 'CoMod(0 _ ~> _ )0 %sol |- _ ] =>
        move : (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg1))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg2))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg3))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg4))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg5))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg6))
      | [ gg1 : 'CoMod(0 _ ~> _ )0 %sol ,
                gg2 : 'CoMod(0 _ ~> _ )0 %sol ,
                      gg3 : 'CoMod(0 _ ~> _ )0 %sol ,
                            gg4 : 'CoMod(0 _ ~> _ )0 %sol ,
                                  gg5 : 'CoMod(0 _ ~> _ )0 %sol |- _ ] =>
        move : (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg1))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg2))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg3))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg4))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg5))
      | [ gg1 : 'CoMod(0 _ ~> _ )0 %sol ,
                gg2 : 'CoMod(0 _ ~> _ )0 %sol ,
                      gg3 : 'CoMod(0 _ ~> _ )0 %sol ,
                            gg4 : 'CoMod(0 _ ~> _ )0 %sol |- _ ] =>
        move : (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg1))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg2))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg3))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg4))
      | [ gg1 : 'CoMod(0 _ ~> _ )0 %sol ,
                gg2 : 'CoMod(0 _ ~> _ )0 %sol ,
                      gg3 : 'CoMod(0 _ ~> _ )0 %sol  |- _ ] =>
        move : (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg1))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg2))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg3))
      | [ gg1 : 'CoMod(0 _ ~> _ )0 %sol ,
                gg2 : 'CoMod(0 _ ~> _ )0 %sol |- _ ] =>
        move : (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg1))
                 (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg2)) 
      | [ gg1 : 'CoMod(0 _ ~> _ )0 %sol |- _ ] =>
        move : (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod gg1))
      end .

  End Ex_Notations1.

(**#+END_SRC

** Degradation lemma and the non-linear arithmetic COQ automation-tactic [nia]

This degradation lemma and the non-linear arithmetic side-goals are solved 
mostly-automatically. One interesting question is that, for larger and more complex 
polymorph mathematics such as , whether this deduction is again mostly-automated and whether
external specialized "satisfiability modulo theory" would be lacked and whether the scale 
of the human-resources is linearly-proportional to the scale of the input ., 

#+BEGIN_SRC coq :exports both :results silent **)

  Lemma degrade :
    forall (B1 B2 : obCoMod) (gDeg g : 'CoMod(0 B1 ~> B2 )0),
      (gDeg <~~ g)%once ->
      ((gradeParticular gDeg) < (gradeParticular g))%Z . 
  Proof.
    move => B1 B2 gDeg g Honce.
    destruct Honce; 
      [ ( match goal with
          | [Hcong : ( _ <~~ _ )%cong |- _ ] =>
            induction Hcong;
            [ match goal with
              | [Hatom : _ ?g1 ?g2
                 |- ( gradeParticular ?g2 < gradeParticular ?g1 )%Z ] => destruct Hatom
              end
            | idtac .. ]
          end;
          intros; tac_gradeParticular_gt0; simpl in *; intros; abstract intuition nia )
          .. ].
  Qed.

  Lemma degrade_rew :
    forall (B1 B2 : obCoMod) (gDeg g : 'CoMod(0 B1 ~> B2 )0),
      (gDeg <~~ g)%rew ->
      ((gradeParticular gDeg) <= (gradeParticular g))%Z . 
  Proof.
    move => B1 B2 gDeg g Hrew.
    induction Hrew;
      first by reflexivity.
    match goal with
      [ Honce : ( _ <~~ _ )%once |- _ ] =>
      move: (degrade Honce); abstract nia
    end.
  Qed.

  Module Export Ex_Notations.
    Export Ex_Notations1.

    Ltac tac_degrade H_gradeParticular :=
      repeat match goal with
             | [ Hrew : ( _ <~~ _ )%rew |- _ ] =>
               move : (Rewrite.degrade_rew Hrew) ; clear Hrew
             | [ Honce : ( _ <~~ _ )%once |- _ ] =>
               move : (Rewrite.degrade Honce) ; clear Honce
             end;
      move: H_gradeParticular; clear; simpl in *; intros;
      try tac_gradeParticular_gt0; try tac_gradeParticular_gt0_sol;
      intros; abstract nia.

  End Ex_Notations.
  
End Rewrite.

(**#+END_SRC

* Polymorphism/cut-elimination by congruent-rewriting

The confluence lemma [confluence] is parametrized by some interface (module type) of the cut-elimination which in fact uniquely-determine this cut-elimination resolution function [solveCoMod] (modulo solution-conversion) .,

Commonly, oneself would define some non-structurally recursive function via some [Fixpoint] combinator and then derive the corresponding rewriting equations ., But when the domain of the function is some dependent/indexed type, this could become very complex ., Surprisingly, the confluence lemma is able to proceed with only the rewriting equations and do not necessitate (internal) knowledge that these rewriting do terminate ., But for sure , oneself does (externally) know that the (external) repeated-rewriting automation-tactic will always terminate .,

Memo that the cut-elimination function [solveCoMod] becomes some (auxilliary) cut-elimination intermediate-function [solveCoMod_PolyCoMod] when the input ( "topmost cut" ) is some composition/cut of two solution-morphisms  .., This cut-elimination intermediate-function could be given the name << resolved-cut >> in contrast to << grammatical-cut >> , and any solution which contains such resolved-cuts could be given th name << unresolved-solution >> in contrast to << grammatical-solution >> ,. Indeed, this resolved-cut [solveCoMod_PolyCoMod] satisfies defining-equations which are all similar as the defining-rewriting-equations of the grammatical-cut , moreover this resolved-cut satisfies one derived-equation [Limitator_morphism] and one derived-congruence-equation [solveCoMod_PolyCoMod_cong] which are similar as some, in fact defining- , rewriting-equation of the grammatical-cut .

Memo that the non-structural induction in the derived congruences [solveCoMod_PolyCoMod_cong_Pre_] [solveCoMod_PolyCoMod_cong_Post_] for the resolved-cut [solveCoMod_PolyCoMod] is more technical because the measure is the sum of the grade [gradeConv] of the solution-conversion input plus the grade [gradeParticular] of one of the resolved-cut output . 

#+BEGIN_SRC coq :exports both :results silent **)

Module Type Resolve.

  Import Sol.Ex_Notations.
  Import Rewrite.Ex_Notations.

  Parameter solveCoMod_PolyCoMod :
    forall (B2 : obCoMod) (B1 : obCoMod) (g_Sol : 'CoMod(0 B2 ~> B1 )0 %sol)
      (B1' : obCoMod) (g'Sol : 'CoMod(0 B1 ~> B1' )0 %sol),
      'CoMod(0 B2 ~> B1' )0 %sol .

  Notation "g_ o>CoMod g'" :=
    (@solveCoMod_PolyCoMod _ _ g_ _ g') (at level 25, right associativity) : sol_scope.
      
  Definition solveCoMod_PolyCoMod_rewrite B2 B1 B1' g_ g' :=
    (@solveCoMod_PolyCoMod B2 B1 g_ B1' g').

  Notation "g_ o>CoMod g'" :=
    (@solveCoMod_PolyCoMod_rewrite _ _ _ g_ g') (at level 25, right associativity) : sol_scope.

  Axiom CoMod_unit :
    ( forall (B B' : obCoMod) (f : 'CoMod(0 B ~> B' )0),
        ( f )
          = ( ( uCoMod ) o>CoMod f
                : 'CoMod(0 B ~> B' )0 ) )%sol.

  Axiom CoMod_inputUnitCoMod :
    ( forall (B' B : obCoMod) (g : 'CoMod(0 B' ~> B )0),
        ( g )
          =  ( g o>CoMod ( uCoMod )
                 : 'CoMod(0 B' ~> B )0 ) )%sol.

  Axiom Project_1_morphism : forall B1 B2,
      ( forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0)
          B1'' (b1' : 'CoMod(0 B1' ~> B1'' )0),
          ( ~_1 @ B2 o>CoMod (b1 o>CoMod b1') )
          = ( ( ~_1 @ B2 o>CoMod b1 ) o>CoMod b1'
              : 'CoMod(0 Limit B1 B2 ~> B1'' )0 ) )%sol.

  Axiom Project_2_morphism : forall B1 B2,
      ( forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0)
          B2'' (b2' : 'CoMod(0 B2' ~> B2'' )0),
          ( ~_2 @ B1 o>CoMod (b2 o>CoMod b2') )
            = ( ( ~_2 @ B1 o>CoMod b2 ) o>CoMod b2'
                  : 'CoMod(0 Limit B1 B2 ~> B2'' )0 ) )%sol.
     
  Axiom Limitator_morphism_Limitator :
    forall (B1 B2 B0 B3 : obCoMod)
      (g_1 : ('CoMod(0 Limit B0 B3 ~> B1 )0)%sol) (g_2 : ('CoMod(0 Limit B0 B3 ~> B2 )0)%sol)
      (M : obCoMod) (m1 : ('CoMod(0 M ~> B0 )0)%sol)(m2 : ('CoMod(0 M ~> B3 )0)%sol),
      ( << << m1 ,CoMod m2 >> o>CoMod g_1 ,CoMod << m1 ,CoMod m2 >> o>CoMod g_2 >>%sol )
      = (<< m1 ,CoMod m2 >> o>CoMod << g_1 ,CoMod g_2 >>)%sol.

  Axiom Limitator_Project_1 : forall B1 B2 M,
      ( forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
          forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0),
            ( g_1 o>CoMod b1 )
              = ( << g_1 ,CoMod g_2 >> o>CoMod ( ~_1 @ B2 o>CoMod b1)
                    : 'CoMod(0 M ~> B1' )0 ) )%sol .

  Axiom Limitator_Project_2 : forall B1 B2 M,
      ( forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
          forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0),
            ( g_2 o>CoMod b2 )
              = ( << g_1 ,CoMod g_2 >> o>CoMod ( ~_2 @ B1 o>CoMod b2)
                    : 'CoMod(0 M ~> B2' )0 ) )%sol .
  
  Parameter solveCoMod :
    forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0), 'CoMod(0 B1 ~> B2 )0 %sol.
  
  Axiom solveCoMod_PolyCoModP :
    forall (B2 : obCoMod) (B1 : obCoMod) (g_ : 'CoMod(0 B2 ~> B1 )0)
      (B1' : obCoMod) (g' : 'CoMod(0 B1 ~> B1' )0),
      ( ( (solveCoMod g_) o>CoMod (solveCoMod g') )
          = solveCoMod (g_ o>CoMod g')%poly )%sol .

  Axiom solveCoMod_UnitCoModP :
     forall {B : obCoMod},
       ( uCoMod
           = solveCoMod ( @uCoMod B )%poly )%sol .

  Axiom solveCoMod_Project_1P :
    forall B1 B2, forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0),
        ( ~_1 @ B2 o>CoMod (solveCoMod b1)
                           = solveCoMod ( ~_1 @ B2 o>CoMod b1 )%poly )%sol .

  Axiom solveCoMod_Project_2P :
    forall B1 B2, forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0),
        ( ~_2 @ B1 o>CoMod (solveCoMod b2)
                           = solveCoMod ( ~_2 @ B1 o>CoMod b2 )%poly )%sol.

  Axiom solveCoMod_LimitatorP :
    forall B1 B2 L, forall (g_1 : 'CoMod(0 L ~> B1 )0) (g_2 : 'CoMod(0 L ~> B2 )0),
        ( << (solveCoMod g_1) ,CoMod (solveCoMod g_2) >>
                               = solveCoMod ( << g_1 ,CoMod g_2 >> )%poly )%sol .

  Module Export Ex_Notations0.
    
    Export Sol.Ex_Notations.
    Export Rewrite.Ex_Notations.

    Notation "g_ o>CoMod g'" :=
      (@solveCoMod_PolyCoMod _ _ g_ _ g') (at level 25, right associativity) : sol_scope.
    
    Notation "g_ o>CoMod g'" :=
      (@solveCoMod_PolyCoMod_rewrite _ _ _ g_ g') (at level 25, right associativity) : sol_scope.

    Hint Resolve solveCoMod_PolyCoModP solveCoMod_UnitCoModP
         solveCoMod_Project_1P solveCoMod_Project_2P
         solveCoMod_LimitatorP .

    Definition tac_solveCoMod := ( solveCoMod_PolyCoModP , @solveCoMod_UnitCoModP ,
                                     solveCoMod_Project_1P , solveCoMod_Project_2P ,
                                     solveCoMod_LimitatorP ) .
    
    Hint Resolve Project_1_morphism Project_2_morphism Limitator_morphism_Limitator
         CoMod_unit CoMod_inputUnitCoMod
         Limitator_Project_1 Limitator_Project_2 .

    Definition tac_solveCoMod_PolyCoMod := ( Limitator_morphism_Limitator , Project_1_morphism , Project_2_morphism, 
                                         Limitator_Project_1 , Limitator_Project_2 ,
                                         CoMod_unit , CoMod_inputUnitCoMod ).

  End Ex_Notations0.

  Lemma Limitator_morphism : forall B1 B2 M,
      ( forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0)
          M' (m : 'CoMod(0 M' ~> M )0),
          ( m o>CoMod << g_1 ,CoMod g_2 >> )
            ~~~ ( << m o>CoMod g_1 ,CoMod m o>CoMod g_2 >>
                  : 'CoMod(0 M' ~> Limit B1 B2 )0 ) )%sol %sol_conv. 
  Proof.
    induction m.
    rewrite -?tac_solveCoMod_PolyCoMod; reflexivity. 
    rewrite -?tac_solveCoMod_PolyCoMod. rewrite -IHm. eapply Sol._Atom_Cong.Project_1_Limitator.
    rewrite -?tac_solveCoMod_PolyCoMod. rewrite -IHm. eapply Sol._Atom_Cong.Project_2_Limitator.
    rewrite -?tac_solveCoMod_PolyCoMod. reflexivity.
  Qed.

  Fixpoint solveCoMod_PolyCoMod_cong_Pre_ len {struct len}  :
    forall (B2 : obCoMod) (B1 : obCoMod) (g_Sol g_Sol0 : 'CoMod(0 B2 ~> B1 )0 %sol)
      ( Hconv : ( g_Sol0 ~~~ g_Sol )%sol_once ), 
          forall  B1' (g'Sol : 'CoMod(0 B1 ~> B1' )0 %sol),
          forall (H_gradeParticular : ( (Sol.gradeConv Hconv + Rewrite.gradeParticular ((Sol.toCoMod g_Sol) o>CoMod (Sol.toCoMod g'Sol))%poly)%Z <= Z.of_nat len)%Z ),
            ( ( ( g_Sol0 o>CoMod g'Sol ) ~~~ ( g_Sol o>CoMod g'Sol ) )) %sol %sol_conv . 
  Proof.
    case : len => [ | len ].
    (* len is O *)
    - clear; ( move => B1 B2 g_Sol g_Sol0 Hconv B1' g'Sol H_gradeParticular ); exfalso.
      tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular.
    - destruct Hconv; rename c into Hconv. 
      (* Sol.Once.Project_1_Limitator *)
      { destruct Hconv; [dependent destruction c | .. ]; intros .
        (* ConvCoMod_Atom *)
        + { dependent destruction g'Sol.  
            * { rewrite -?tac_solveCoMod_PolyCoMod.  eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod .  reflexivity. }
            * { rewrite -?tac_solveCoMod_PolyCoMod .  reflexivity. } 
            * { rewrite -?Limitator_morphism.
                eapply Sol._Atom_Cong.Limitator_cong_12.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  apply: Sol.Once.Project_1_Limitator. apply: Sol.Cong.ConvCoMod_Atom. constructor.
                  (*ALT: constructor 1 (* Project_1_Limitator *). constructor 1 (* ConvCoMod_Atom *). constructor. *)
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  constructor 1  (* Project_1_Limitator *). constructor 1 (* ConvCoMod_Atom *). constructor.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
          }
        (* Project_1_cong *)
        + { rewrite -?tac_solveCoMod_PolyCoMod . apply: Sol._Atom_Cong.Project_1_cong.
            unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
            constructor 1 (* Project_1_Limitator *) . exact: Hconv.
            simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. } 
        (* Project_2_cong *)
        + { rewrite -?tac_solveCoMod_PolyCoMod . apply: Sol._Atom_Cong.Project_2_cong.
            unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
            constructor 1 (* Project_1_Limitator *) . exact: Hconv.
            simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. } 
        (* Limitator_cong_1 *)
        + { dependent destruction g'Sol.  
            * { rewrite -?tac_solveCoMod_PolyCoMod.  eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod .
                unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                constructor 1 (* Project_1_Limitator *). apply: Hconv.
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod . reflexivity. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                eapply Sol._Atom_Cong.Limitator_cong_12.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  constructor 1 (* Project_1_Limitator *). constructor 4 (* Limitator_cong_1 *).  exact: Hconv.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  constructor 1 (* Project_1_Limitator *). constructor 4 (* Limitator_cong_1 *).  exact: Hconv.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
          }
        (* Limitator_cong_2 *)
        + { dependent destruction g'Sol.  
            * { rewrite -?tac_solveCoMod_PolyCoMod.  eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod . reflexivity. }
            * { rewrite -?tac_solveCoMod_PolyCoMod .
                unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                constructor 1 (* Project_1_Limitator *). apply: Hconv.
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                eapply Sol._Atom_Cong.Limitator_cong_12.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  constructor 1 (* Project_1_Limitator *). constructor 5 (* Limitator_cong_2 *).  exact: Hconv.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  constructor 1 (* Project_1_Limitator *). constructor 5 (* Limitator_cong_2 *).  exact: Hconv.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
          }
      }

      (* Sol.Once.Project_2_Limitator *)
      { destruct Hconv; [dependent destruction c | .. ]; intros .
        (* ConvCoMod_Atom *)
        + { dependent destruction g'Sol.  
            * { rewrite -?tac_solveCoMod_PolyCoMod.  eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod .  reflexivity. }
            * { rewrite -?tac_solveCoMod_PolyCoMod .  reflexivity. } 
            * { (*MEMO: oneself cannot alter the precedence of rewritings,
                but onselft may do one single step of rewriting
                OLD: rewrite -?tac_solveCoMod_PolyCoMod.1.1.2 .*)
                rewrite -?Limitator_morphism.
                eapply Sol._Atom_Cong.Limitator_cong_12.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  constructor 2 (* Project_2_Limitator *). constructor 1 (* ConvCoMod_Atom *). constructor.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  constructor 2 (* Project_2_Limitator *) . constructor 1 (* ConvCoMod_Atom *). constructor.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
          }
        (* Project_1_cong *)
        + { rewrite -?tac_solveCoMod_PolyCoMod . apply: Sol._Atom_Cong.Project_1_cong.
            unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
            constructor 2 (* Project_2_Limitator *) . exact: Hconv.
            simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. } 
        (* Project_2_cong *)
        + { rewrite -?tac_solveCoMod_PolyCoMod . apply: Sol._Atom_Cong.Project_2_cong.
            unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
            constructor 2 (* Project_2_Limitator *) . exact: Hconv.
            simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. } 
        (* Limitator_cong_1 *)
        + { dependent destruction g'Sol.  
            * { rewrite -?tac_solveCoMod_PolyCoMod.  eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod .
                unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                constructor 2 (* Project_2_Limitator *). apply: Hconv.
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod . reflexivity. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                eapply Sol._Atom_Cong.Limitator_cong_12.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  constructor 2 (* Project_2_Limitator *). constructor 4 (* Limitator_cong_1 *).  exact: Hconv.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  constructor 2 (* Project_2_Limitator *). constructor 4 (* Limitator_cong_1 *).  exact: Hconv.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
          }
        (* Limitator_cong_2 *)
        + { dependent destruction g'Sol.  
            * { rewrite -?tac_solveCoMod_PolyCoMod.  eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod . reflexivity. }
            * { rewrite -?tac_solveCoMod_PolyCoMod .
                unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                constructor 2 (* Project_2_Limitator *). apply: Hconv.
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                eapply Sol._Atom_Cong.Limitator_cong_12.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  constructor 2 (* Project_2_Limitator *). constructor 5 (* Limitator_cong_2 *).  exact: Hconv.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  constructor 2 (* Project_2_Limitator *). constructor 5 (* Limitator_cong_2 *).  exact: Hconv.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
          }
      }

      (* Sol.Once.Limitator_Project_1_Project_2 *)
      { destruct Hconv; [dependent destruction c | .. ]; intros .
        (* ConvCoMod_Atom *)
        + { dependent destruction g'Sol.  
            * { rewrite -?tac_solveCoMod_PolyCoMod.  eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod .  reflexivity. }
            * { rewrite -?tac_solveCoMod_PolyCoMod .  reflexivity. } 
            * { (*MEMO: oneself cannot alter the precedence of rewritings,
                but onselft may do one single step of rewriting
                OLD: rewrite -?tac_solveCoMod_PolyCoMod.1.1.2 .*)
                rewrite -?Limitator_morphism.
                eapply Sol._Atom_Cong.Limitator_cong_12.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  apply: Sol.Once.Limitator_Project_1_Project_2 (* constructor 3 *). apply: Sol.Cong.ConvCoMod_Atom. constructor.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  apply: Sol.Once.Limitator_Project_1_Project_2 (* constructor 3 *). apply: Sol.Cong.ConvCoMod_Atom. constructor.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
          }
        (* Project_1_cong *)
        + { rewrite -?tac_solveCoMod_PolyCoMod . apply: Sol._Atom_Cong.Project_1_cong.
            unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
             apply: Sol.Once.Limitator_Project_1_Project_2 (* constructor 3 *) . exact: Hconv.
            simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. } 
        (* Project_2_cong *)
        + { rewrite -?tac_solveCoMod_PolyCoMod . apply: Sol._Atom_Cong.Project_2_cong.
            unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
             apply: Sol.Once.Limitator_Project_1_Project_2 (* constructor 3 *) . exact: Hconv.
            simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. } 
        (* Limitator_cong_1 *)
        + { dependent destruction g'Sol.  
            * { rewrite -?tac_solveCoMod_PolyCoMod.  eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod .
                unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                apply: Sol.Once.Limitator_Project_1_Project_2 (* constructor 3 *). apply: Hconv.
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod . reflexivity. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                eapply Sol._Atom_Cong.Limitator_cong_12.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  apply: Sol.Once.Limitator_Project_1_Project_2 (* constructor 3 *).
                  apply: Sol.Cong.Limitator_cong_1 (* constructor 4 *).  exact: Hconv.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  apply: Sol.Once.Limitator_Project_1_Project_2 (* constructor 3 *).
                  apply: Sol.Cong.Limitator_cong_1 (* constructor 4 *).  exact: Hconv.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
          }
        (* Limitator_cong_2 *)
        + { dependent destruction g'Sol.  
            * { rewrite -?tac_solveCoMod_PolyCoMod.  eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod . reflexivity. }
            * { rewrite -?tac_solveCoMod_PolyCoMod .
                unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                apply: Sol.Once.Limitator_Project_1_Project_2 (* constructor 3 *). apply: Hconv.
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                eapply Sol._Atom_Cong.Limitator_cong_12.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                  apply: Sol.Once.Limitator_Project_1_Project_2 (* constructor 3 *).
                  apply: Sol.Cong.Limitator_cong_2 (* constructor 5 *).  exact: Hconv.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular.
                - unshelve eapply (solveCoMod_PolyCoMod_cong_Pre_ len).
                   apply: Sol.Once.Limitator_Project_1_Project_2 (* constructor 3 *).
                  apply: Sol.Cong.Limitator_cong_2 (* constructor 5 *).  exact: Hconv.
                  simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
          }
      }
  Qed. 

  Definition solveCoMod_PolyCoMod_cong_Pre_sol_once :
    forall (B2 : obCoMod) (B1 : obCoMod) (g_Sol g_Sol0 : 'CoMod(0 B2 ~> B1 )0 %sol)
      ( Hconv : ( g_Sol0 ~~~ g_Sol )%sol_once ), 
          forall  B1' (g'Sol : 'CoMod(0 B1 ~> B1' )0 %sol),
            ( ( ( g_Sol0 o>CoMod g'Sol ) ~~~ ( g_Sol o>CoMod g'Sol ) )) %sol %sol_conv . 
  Proof.
    intros.  apply: (@solveCoMod_PolyCoMod_cong_Pre_ (Z.to_nat((Sol.gradeConv Hconv + Rewrite.gradeParticular ((Sol.toCoMod g_Sol) o>CoMod (Sol.toCoMod g'Sol))%poly)%Z )) _ _ _ _ Hconv);
               intros; rewrite Z2Nat.id; simpl in *; try tac_gradeConv_gt0_sol; try tac_gradeParticular_gt0; try tac_gradeParticular_gt0_sol; abstract nia.
  Qed.

  Definition solveCoMod_PolyCoMod_cong_Pre_sol_conv :
    forall (B2 : obCoMod) (B1 : obCoMod) (g_Sol g_Sol0 : 'CoMod(0 B2 ~> B1 )0 %sol)
      ( Hconv : ( g_Sol0 ~~~ g_Sol )%sol_conv ), 
          forall  B1' (g'Sol : 'CoMod(0 B1 ~> B1' )0 %sol),
            ( ( ( g_Sol0 o>CoMod g'Sol ) ~~~ ( g_Sol o>CoMod g'Sol ) )) %sol %sol_conv . 
  Proof.
    induction 1 as [ | | ]; [reflexivity | ..];
      match goal with
        [ Hsol_once : ( _ ~~~ _ )%sol_once |- _ ] =>
        move: (solveCoMod_PolyCoMod_cong_Pre_sol_once Hsol_once)
      end; eauto.
  Qed.

  Fixpoint solveCoMod_PolyCoMod_cong_Post_ len {struct len}  :
    forall (B1 : obCoMod) (B1' : obCoMod) (g'Sol g'Sol0 : 'CoMod(0 B1 ~> B1' )0 %sol)
      ( Hconv : ( g'Sol0 ~~~ g'Sol )%sol_once ), 
          forall  B2 (g_Sol : 'CoMod(0 B2 ~> B1 )0 %sol),
          forall (H_gradeParticular : ( (Sol.gradeConv Hconv + Rewrite.gradeParticular ((Sol.toCoMod g_Sol) o>CoMod (Sol.toCoMod g'Sol))%poly)%Z <= Z.of_nat len)%Z ),
            ( ( ( g_Sol o>CoMod g'Sol0 ) ~~~ ( g_Sol o>CoMod g'Sol ) )) %sol %sol_conv . 
  Proof.
    case : len => [ | len ].
    (* len is O *)
    - clear; ( move => B1 B2 g_Sol g_Sol0 Hconv B1' g'Sol H_gradeParticular ); exfalso.
      tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular.

    (* len is S len *)
    - destruct Hconv; rename c into Hconv. 
      (* Sol.Once.Project_1_Limitator *)
      { destruct Hconv; [dependent destruction c | .. ]; intros .
        (* ConvCoMod_Atom *)
        + { dependent destruction g_Sol.  
            * { rewrite -?tac_solveCoMod_PolyCoMod.  eauto. }
            * { (*  *)
                rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_1_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear. eauto.
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_2_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear. eauto.
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?(tac_solveCoMod_PolyCoMod, Limitator_morphism). reflexivity. }
          }
        (* Project_1_cong *)
        + { dependent destruction g_Sol.
            * { rewrite -?tac_solveCoMod_PolyCoMod. apply: Sol._Atom_Cong.Project_1_cong. clear -Hconv; eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_1_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_2_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. } } 
        (* Project_2_cong *)
        + { dependent destruction g_Sol.
            * { rewrite -?tac_solveCoMod_PolyCoMod. apply: Sol._Atom_Cong.Project_2_cong. clear -Hconv; eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_1_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_2_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. } } 
        (* Limitator_cong_1 *)
        + { rewrite -?Limitator_morphism.
            apply: Sol._Atom_Cong.Limitator_cong_1.
            unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
            clear -Hconv; eauto. 
            simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
        (* Limitator_cong_2 *)
        + { rewrite -?Limitator_morphism.
            apply: Sol._Atom_Cong.Limitator_cong_2.
            unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
            clear -Hconv; eauto. 
            simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
      }
      (* Sol.Once.Project_2_Limitator *)
      { destruct Hconv; [dependent destruction c | .. ]; intros .
        (* ConvCoMod_Atom *)
        + { dependent destruction g_Sol.  
            * { rewrite -?tac_solveCoMod_PolyCoMod.  eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_1_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear. eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_2_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear. eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?(tac_solveCoMod_PolyCoMod, Limitator_morphism). reflexivity. }
          }
        (* Project_1_cong *)
        + { dependent destruction g_Sol.
            * { rewrite -?tac_solveCoMod_PolyCoMod. apply: Sol._Atom_Cong.Project_1_cong. clear -Hconv; eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_1_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_2_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. } } 
        (* Project_2_cong *)
        + { dependent destruction g_Sol.
            * { rewrite -?tac_solveCoMod_PolyCoMod. apply: Sol._Atom_Cong.Project_2_cong. clear -Hconv; eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_1_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_2_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. } } 
        (* Limitator_cong_1 *)
        + { rewrite -?Limitator_morphism.
            apply: Sol._Atom_Cong.Limitator_cong_1.
            unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
            clear -Hconv; eauto. 
            simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
        (* Limitator_cong_2 *)
        + { rewrite -?Limitator_morphism.
            apply: Sol._Atom_Cong.Limitator_cong_2.
            unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
            clear -Hconv; eauto. 
            simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
      }
      (* Sol.Once.Limitator_Project_1_Project_2 *)
      { destruct Hconv; [dependent destruction c | .. ]; intros .
        (* ConvCoMod_Atom *)
        + { dependent destruction g_Sol.  
            * { rewrite -?tac_solveCoMod_PolyCoMod. clear. eauto. }
            * { (*MEMO: single step rewrite *)
                rewrite -[X in ( X ~~~ _ )%sol_conv]tac_solveCoMod_PolyCoMod
                -[Y in ( _ ~~~ Y )%sol_conv]tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_1_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear. eauto.
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { (*MEMO: single step rewrite *)
                rewrite -[X in ( X ~~~ _ )%sol_conv]tac_solveCoMod_PolyCoMod
                -[Y in ( _ ~~~ Y )%sol_conv]tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_2_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear. eauto.
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod. reflexivity. }
          }
        (* Project_1_cong *)
        + { dependent destruction g_Sol.
            * { rewrite -?tac_solveCoMod_PolyCoMod. apply: Sol._Atom_Cong.Project_1_cong. clear -Hconv; eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_1_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_2_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. } } 
        (* Project_2_cong *)
        + { dependent destruction g_Sol.
            * { rewrite -?tac_solveCoMod_PolyCoMod. apply: Sol._Atom_Cong.Project_2_cong. clear -Hconv; eauto. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_1_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                apply: Sol._Atom_Cong.Project_2_cong.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
            * { rewrite -?tac_solveCoMod_PolyCoMod.
                unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
                clear -Hconv; eauto. 
                simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. } } 
        (* Limitator_cong_1 *)
        + { rewrite -?Limitator_morphism.
            apply: Sol._Atom_Cong.Limitator_cong_1.
            unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
            clear -Hconv; eauto. 
            simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
        (* Limitator_cong_2 *)
        + { rewrite -?Limitator_morphism.
            apply: Sol._Atom_Cong.Limitator_cong_2.
            unshelve eapply (solveCoMod_PolyCoMod_cong_Post_ len).
            clear -Hconv; eauto. 
            simpl in *. try tac_gradeConv_gt0_sol ; tac_degrade H_gradeParticular. }
      }
  Qed.

  Definition solveCoMod_PolyCoMod_cong_Post_sol_once :
    forall (B1 : obCoMod) (B1' : obCoMod) (g'Sol g'Sol0 : 'CoMod(0 B1 ~> B1' )0 %sol)
      ( Hconv : ( g'Sol0 ~~~ g'Sol )%sol_once ), 
          forall  B2 (g_Sol : 'CoMod(0 B2 ~> B1 )0 %sol),
            ( ( ( g_Sol o>CoMod g'Sol0 ) ~~~ ( g_Sol o>CoMod g'Sol ) )) %sol %sol_conv . 
  Proof.
    intros.  apply: (@solveCoMod_PolyCoMod_cong_Post_ (Z.to_nat((Sol.gradeConv Hconv + Rewrite.gradeParticular ((Sol.toCoMod g_Sol) o>CoMod (Sol.toCoMod g'Sol))%poly)%Z )) _ _ _ _ Hconv);
               intros; rewrite Z2Nat.id; simpl in *; try tac_gradeConv_gt0_sol; try tac_gradeParticular_gt0; try tac_gradeParticular_gt0_sol; abstract nia.
  Qed.

  Definition solveCoMod_PolyCoMod_cong_Post_sol_conv :
    forall (B1 : obCoMod) (B1' : obCoMod) (g'Sol g'Sol0 : 'CoMod(0 B1 ~> B1' )0 %sol)
      ( Hconv : ( g'Sol0 ~~~ g'Sol )%sol_conv ), 
          forall  B2 (g_Sol : 'CoMod(0 B2 ~> B1 )0 %sol),
            ( ( ( g_Sol o>CoMod g'Sol0 ) ~~~ ( g_Sol o>CoMod g'Sol ) )) %sol %sol_conv . 
  Proof.
    induction 1; [reflexivity | ..];
    match goal with
      [ Hsol_once : ( _ ~~~ _ )%sol_once |- _ ] =>
      move: (solveCoMod_PolyCoMod_cong_Post_sol_once Hsol_once)
    end; eauto.
  Qed.

  Definition solveCoMod_PolyCoMod_cong :
    forall (B1 : obCoMod) (B1' : obCoMod) (g'Sol g'Sol0 : 'CoMod(0 B1 ~> B1' )0 %sol)
      ( Hconv' : ( g'Sol0 ~~~ g'Sol )%sol_conv ), 
    forall  B2 (g_Sol g_Sol0 : 'CoMod(0 B2 ~> B1 )0 %sol)
      ( Hconv_ : ( g_Sol0 ~~~ g_Sol )%sol_conv ), 
    ( ( ( g_Sol0 o>CoMod g'Sol0 ) ~~~ ( g_Sol o>CoMod g'Sol ) )) %sol %sol_conv . 
  Proof.
    intros. rewrite solveCoMod_PolyCoMod_cong_Post_sol_conv; last eassumption;
              rewrite solveCoMod_PolyCoMod_cong_Pre_sol_conv; last eassumption;
                reflexivity.
  Qed.

  Definition solveCoMod_toCoMod_cong_sol_once :
    forall (B1 B2 : obCoMod) (gSol gSol0 : 'CoMod(0 B1 ~> B2 )0 %sol),
      ( gSol0 ~~~ gSol )%sol_once ->
      ( solveCoMod (Sol.toCoMod gSol0) ~~~ solveCoMod (Sol.toCoMod gSol) )%sol_conv.
  Proof.
    destruct 1;
      ( induction c; [dependent destruction c | ..] ;
        simpl in * ; rewrite -?tac_solveCoMod ; eauto ) .
  Qed.
    
  Definition solveCoMod_toCoMod_cong :
    forall (B1 B2 : obCoMod) (gSol gSol0 : 'CoMod(0 B1 ~> B2 )0 %sol),
      ( gSol0 ~~~ gSol )%sol_conv ->
      ( solveCoMod (Sol.toCoMod gSol0) ~~~ solveCoMod (Sol.toCoMod gSol) )%sol_conv.
  Proof.
    induction 1; [reflexivity | ..];
    match goal with
      [ Hsol_once : ( _ ~~~ _ )%sol_once |- _ ] =>
      move: (solveCoMod_toCoMod_cong_sol_once Hsol_once)
    end; eauto.
  Qed.

  Definition solveCoMod_toCoMod (B1 B2 : obCoMod) (gSol : 'CoMod(0 B1 ~> B2 )0 %sol)
    := solveCoMod (Sol.toCoMod gSol) .
  
  Fixpoint solveCoMod_PolyCoModP1_ len {struct len} :
    forall (B2 : obCoMod) (B1 : obCoMod) (g_Sol : 'CoMod(0 B2 ~> B1 )0 %sol)
      (B1' : obCoMod) (g'Sol : 'CoMod(0 B1 ~> B1' )0 %sol),
    forall (H_gradeParticular : ( (Rewrite.gradeParticular ((Sol.toCoMod g_Sol) o>CoMod (Sol.toCoMod g'Sol)))%Z <= Z.of_nat len)%Z ),
      ( (Sol.toCoMod (g_Sol o>CoMod g'Sol)%sol) <~~ ((Sol.toCoMod g_Sol) o>CoMod (Sol.toCoMod g'Sol))%poly )%rew.
  Proof.
    case : len => [ | len ].
 
    (* len is O *)
    - clear; ( move => B1 B2 g_Sol B1' g'Sol H_gradeParticular ); exfalso;
        tac_degrade H_gradeParticular.

    (* len is (S len) *)
    - intros B1 B2 g_Sol B1' g'Sol H_gradeParticular.
      (* g is (g_ o>Mod g') , to (g_Sol o>Mod g'Sol) *)
      destruct g_Sol as
          [ B  (* @uCoMod B %sol *)
          | B1 B2 _B1' b1_Sol (* ~_1 @ B2 o>CoMod b1_Sol *)
          | B1 B2 B2' b2_Sol (* ~_2 @ B1 o>CoMod b2_Sol *)
          | B1 B2 M g__1Sol g__2Sol (* << g__1Sol ,CoMod g__2Sol >> %sol *) ].

      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((@uCoMod B) o>CoMod g'Sol) *)
      + rewrite -?tac_solveCoMod_PolyCoMod; tac_assumption_rewrite.

      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((~_1 o>CoMod b1_Sol) o>CoMod g'Sol) *)
      + move: (solveCoMod_PolyCoModP1_ len _ _ b1_Sol _ g'Sol ltac:(abstract tac_degrade H_gradeParticular)).
        { destruct g'Sol.
        rewrite -?tac_solveCoMod_PolyCoMod.  tac_assumption_rewrite.
        rewrite -?tac_solveCoMod_PolyCoMod.  tac_assumption_rewrite.
        rewrite -?tac_solveCoMod_PolyCoMod.  tac_assumption_rewrite.
        rewrite -?tac_solveCoMod_PolyCoMod.  tac_assumption_rewrite. }

      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((~_2 o>CoMod b2_Sol) o>CoMod g'Sol) *)
      + move: (solveCoMod_PolyCoModP1_ len _ _ b2_Sol _ g'Sol ltac:(abstract tac_degrade H_gradeParticular)).
        rewrite -?tac_solveCoMod_PolyCoMod; tac_assumption_rewrite.

      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod g'Sol) *)
      + (* clear - solveCoMod__ H_gradeParticular g_Sol_prop g'Sol_prop. *)
        move: (Sol.Destruct_domLimit.CoMod00_domLimitP g'Sol) => g'Sol_domLimitP.
        destruct g'Sol_domLimitP as
            [ B B' (* @uCoMod (Limit B B') %sol *)
            | B1 B2 B1' b1'Sol (* ~_1 @ B2 o>CoMod b1'Sol *)
            | B1 B2 B2' b2'Sol (* ~_2 @ B1 o>CoMod b2'Sol *)
            | B1 B2 _M M' g'_1Sol g'_2Sol (* << g'_1Sol ,CoMod g'_2Sol >> %sol *) ].

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod g'Sol) , is  ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod (@uCoMod B)) *)
        *  rewrite -?tac_solveCoMod_PolyCoMod; tac_assumption_rewrite.  

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< g__1Sol ,CoMOd g__2Sol >>) o>CoMod g'Sol) , is  ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod  (~_1 o>CoMod b1'Sol) ) *)
        * move: (solveCoMod_PolyCoModP1_ len _ _ g__1Sol _ b1'Sol ltac:(abstract tac_degrade H_gradeParticular)).
          rewrite -?tac_solveCoMod_PolyCoMod; tac_assumption_rewrite.

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< g__1Sol,CoMod g__2Sol >>) o>CoMod g'Sol) , is  ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod  (~_2 o>CoMod b2'Sol) ) *)
        * move: (solveCoMod_PolyCoModP1_ len _ _ g__2Sol _ b2'Sol ltac:(abstract tac_degrade H_gradeParticular)).
          rewrite -?tac_solveCoMod_PolyCoMod; tac_assumption_rewrite.

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod g'Sol) , is  ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod  (<< g'_1Sol ,CoMod g'_2Sol >>) ) *)
        * move: (solveCoMod_PolyCoModP1_ len _ _ (<< g__1Sol ,CoMod g__2Sol >> %sol) _ g'_1Sol ltac:(abstract tac_degrade H_gradeParticular))
                  (solveCoMod_PolyCoModP1_ len _ _ (<< g__1Sol ,CoMod g__2Sol >> %sol) _ g'_2Sol ltac:(abstract tac_degrade H_gradeParticular)) . 
          rewrite -?tac_solveCoMod_PolyCoMod; tac_assumption_rewrite.
  Defined.

  Definition solveCoMod_PolyCoModP1 :
    forall (B2 : obCoMod) (B1 : obCoMod) (g_Sol : 'CoMod(0 B2 ~> B1 )0 %sol)
      (B1' : obCoMod) (g'Sol : 'CoMod(0 B1 ~> B1' )0 %sol),   
      ( (Sol.toCoMod (g_Sol o>CoMod g'Sol)%sol) <~~ ((Sol.toCoMod g_Sol) o>CoMod (Sol.toCoMod g'Sol))%poly )%rew.
  Proof.
    intros ? ? g_Sol ? g'Sol; apply: (@solveCoMod_PolyCoModP1_ (Z.to_nat (Rewrite.gradeParticular ((Sol.toCoMod g_Sol) o>CoMod (Sol.toCoMod g'Sol)))%Z)).
      try tac_gradeParticular_gt0; try tac_gradeParticular_gt0_sol;
      intros; rewrite Z2Nat.id; simpl; abstract nia.
  Qed.
    
  Fixpoint solveCoModP1_ len {struct len} :
    forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0),
    forall (H_gradeParticular : ( (Rewrite.gradeParticular g) <= Z.of_nat len)%Z ),
      ( (Sol.toCoMod (solveCoMod g)) <~~ g )%rew .
  Proof.
    case : len => [ | len ].
 
    (* len is O *)
    - clear; ( move => B1 B2 g H_gradeParticular ); exfalso;
        tac_degrade H_gradeParticular.

    (* len is (S len) *)
    - move => B1 B2 g; case : B1 B2 / g =>
      [ B2 B1 g_ B1' g'  (* g_ o>CoMod g' *)
      | B  (* @uCoMod B*)
      | B1 B2 B1' b1 (* ~_1 @ B2 o>CoMod b1 *)
      | B1 B2 B2' b2 (* ~_2 @ B1 o>CoMod b2 *)
      | B1 B2 M g_1 g_2 (* << g_1 ,CoMod g_2 >> *) ].

      (* g is g_ o>CoMod g' *)
      + all: cycle 1. 
        
      (* g is @uCoMod B *)
      + move => H_gradeParticular. rewrite -?tac_solveCoMod. left. 

      (* g is ~_1 @ B2 o>CoMod b1 *)
      + move => H_gradeParticular.
        move: (solveCoModP1_ len _ _ b1 ltac:(tac_degrade H_gradeParticular)).
        clear. rewrite -?tac_solveCoMod; tac_assumption_rewrite. 

      (* g is ~_2 @ B1 o>CoMod b2 *)
      + move => H_gradeParticular.
        move: (solveCoModP1_ len _ _ b2 ltac:(tac_degrade H_gradeParticular)).
        clear. rewrite -?tac_solveCoMod; tac_assumption_rewrite. 

      (* g is << g_1 ,CoMod g_2 >> *)
      + move => H_gradeParticular.
        move: (solveCoModP1_ len _ _ g_1 ltac:(tac_degrade H_gradeParticular)).
        move: (solveCoModP1_ len _ _ g_2 ltac:(tac_degrade H_gradeParticular)).
        clear. rewrite -?tac_solveCoMod; tac_assumption_rewrite. 

      (* g is g_ o>CoMod g' *)
      + rewrite -!/(g_ o>CoMod g'). move => H_gradeParticular.
        move: (solveCoModP1_ len _ _ g_ ltac:(tac_degrade H_gradeParticular)).
        move: (solveCoModP1_ len _ _ g' ltac:(tac_degrade H_gradeParticular)).
        clear. rewrite -?tac_solveCoMod. 
        rewrite -solveCoMod_PolyCoModP1 (*ALT: do rewrite {1}HH se select correct g_ and g'*).
        tac_assumption_rewrite.
  Defined.
        
  Lemma solveCoModP1 :
    forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0), 
               ( (Sol.toCoMod (solveCoMod g)) <~~ g )%rew .
  Proof.
    intros ? ? g; apply: (@solveCoModP1_ (Z.to_nat (Rewrite.gradeParticular g)%Z)).
      try tac_gradeParticular_gt0; try tac_gradeParticular_gt0_sol;
      intros; rewrite Z2Nat.id; simpl; abstract nia.
  Qed.

  Lemma solveCoModP2 :
    ( forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0), 
               ( g = (solveCoMod (Sol.toCoMod g)) ) )%sol .
  Proof.
    intros. symmetry. move: (solveCoModP1 (Sol.toCoMod g)) => Hrew.
    dependent destruction Hrew;
    match goal with
    | [ Heq : Sol.toCoMod _ = Sol.toCoMod _  |- _ ] =>
      move : (Sol.toCoMod_injective Heq) => <- ; reflexivity 
    | [ HH : ( _ <~~ _ )%once  |- _ ] =>
      exfalso; move : (Rewrite.isSolb_isRed_False_alt HH) =>
      /Sol.isSolbN_isSolN_alt ; clear; eauto   
    end.
  Qed.
  
  Module Export Ex_Notations1.
    Export Ex_Notations0.

    Hint Resolve solveCoMod_toCoMod_cong solveCoMod_PolyCoMod_cong Limitator_morphism solveCoMod_PolyCoModP solveCoMod_PolyCoModP1 solveCoModP1 solveCoModP2 .

    (*TODO: really add this Limitator_morphism ? *)
    Definition tac_solveCoMod_PolyCoMod := ( solveCoMod_PolyCoModP1 , Ex_Notations0.tac_solveCoMod_PolyCoMod , Limitator_morphism ).

    Add Parametric Morphism B2 B1 B1' :
      (@solveCoMod_PolyCoMod_rewrite B2 B1 B1' ) with
        signature ((@Sol.convCoMod B2 B1)
                     ==> (@Sol.convCoMod B1 B1')
                     ==> (@Sol.convCoMod B2 B1'))
          as PolyCoMod_cong_rewrite.
        by intros; apply: solveCoMod_PolyCoMod_cong . Qed.

    Add Parametric Morphism B1 B2 :
      (@solveCoMod_toCoMod B1 B2 ) with
        signature ((@Sol.convCoMod B1 B2)
                     ==> (@Sol.convCoMod B1 B2))
          as solveCoMod_toCoMod_cong_rewrite.
        by intros; apply: solveCoMod_toCoMod_cong . Qed.

  End Ex_Notations1.

  Fixpoint solveCoMod_PolyCoMod_CoMod_morphism_ len {struct len} :
    ( forall (B0 B : obCoMod) (g : 'CoMod(0 B0 ~> B )0)
        (B' : obCoMod) (g_ : 'CoMod(0 B ~> B' )0)
        (B'' : obCoMod) (g' : 'CoMod(0 B' ~> B'' )0),
        forall (H_gradeParticular : ((Rewrite.gradeParticular (Sol.toCoMod g) + (Rewrite.gradeParticular (Sol.toCoMod g_) + Rewrite.gradeParticular (Sol.toCoMod g'))) <= Z.of_nat len)%Z ),
          ( g o>CoMod ( g_ o>CoMod g' ) )
            ~~~ ( ( g o>CoMod g_ ) o>CoMod g' ) )%sol %sol_conv .
  Proof.
    case : len => [ | len ].

    (* n is O *)
    - clear; ( move => B0 B g B' g_ B'' g' H_gradeParticular ); exfalso;
        move : (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod g)) (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod g_)) (@Rewrite.gradeParticular_gt0 _ _ (Sol.toCoMod g'))
      => H_gradeParticular_gt0; abstract nia.

    (* n is (S n) *)
    - move => B0 B g B' g_ B'' g'.
      destruct g; intros H_gradeParticular;
        [ rewrite -!tac_solveCoMod_PolyCoMod; reflexivity
        | rewrite -!tac_solveCoMod_PolyCoMod;
          eapply Sol._Atom_Cong.Project_1_cong;
          eapply (solveCoMod_PolyCoMod_CoMod_morphism_ len);
          clear -H_gradeParticular; move: H_gradeParticular;
          simpl in *; intros; tac_isSolb;
          simpl in *; intros; tac_gradeParticular_gt0_sol; intros; abstract intuition nia
        | rewrite -!tac_solveCoMod_PolyCoMod;
          eapply Sol._Atom_Cong.Project_2_cong;
          eapply (solveCoMod_PolyCoMod_CoMod_morphism_ len);
          clear -H_gradeParticular; move: H_gradeParticular;
          simpl in *; intros; tac_isSolb;
          simpl in *; intros; tac_gradeParticular_gt0_sol; intros; abstract intuition nia
        | dependent destruction g_;
          [ rewrite -!tac_solveCoMod_PolyCoMod; reflexivity
          | rewrite -!tac_solveCoMod_PolyCoMod;
            eapply (solveCoMod_PolyCoMod_CoMod_morphism_ len);
            clear -H_gradeParticular; move: H_gradeParticular;
            simpl in *; intros; tac_isSolb;
            simpl in *; intros; tac_gradeParticular_gt0_sol; intros; abstract intuition nia
          | rewrite -!tac_solveCoMod_PolyCoMod;
            eapply (solveCoMod_PolyCoMod_CoMod_morphism_ len);
            clear -H_gradeParticular; move: H_gradeParticular;
            simpl in *; intros; tac_isSolb;
            simpl in *; intros; tac_gradeParticular_gt0_sol; intros; abstract intuition nia
          | dependent destruction g';
            [ rewrite -!tac_solveCoMod_PolyCoMod; reflexivity
            | rewrite -!tac_solveCoMod_PolyCoMod;
              eapply (solveCoMod_PolyCoMod_CoMod_morphism_ len);
              clear -H_gradeParticular; move: H_gradeParticular;
              simpl in *; intros; tac_isSolb;
              simpl in *; intros; tac_gradeParticular_gt0_sol; intros; abstract intuition nia
            | rewrite -!tac_solveCoMod_PolyCoMod;
              eapply (solveCoMod_PolyCoMod_CoMod_morphism_ len);
              clear -H_gradeParticular; move: H_gradeParticular;
              simpl in *; intros; tac_isSolb;
              simpl in *; intros; tac_gradeParticular_gt0_sol; intros; abstract intuition nia
            | rewrite -!tac_solveCoMod_PolyCoMod;
              eapply Sol._Atom_Cong.Limitator_cong_12;
              [ ( rewrite -!(solveCoMod_PolyCoMod_CoMod_morphism_ len);
                  first (by rewrite -!tac_solveCoMod_PolyCoMod; reflexivity);
                  clear -H_gradeParticular; move: H_gradeParticular;
                  simpl in *; intros; tac_isSolb;
                  simpl in *; intros; tac_gradeParticular_gt0_sol; intros; abstract intuition nia ) .. ]
            ]
          ]
        ].
  Qed. 

  Lemma solveCoMod_PolyCoMod_CoMod_morphism :
    ( forall (B0 B : obCoMod) (g : 'CoMod(0 B0 ~> B )0)
        (B' : obCoMod) (g_ : 'CoMod(0 B ~> B' )0)
        (B'' : obCoMod) (g' : 'CoMod(0 B' ~> B'' )0),
        ( g o>CoMod ( g_ o>CoMod g' ) )
          ~~~ ( ( g o>CoMod g_ ) o>CoMod g' ) )%sol %sol_conv .
  Proof.
    intros; apply: (@solveCoMod_PolyCoMod_CoMod_morphism_ ( Z.to_nat ((Rewrite.gradeParticular (Sol.toCoMod g) + (Rewrite.gradeParticular (Sol.toCoMod g_) + Rewrite.gradeParticular (Sol.toCoMod g')))) ));
      intros; tac_gradeParticular_gt0_sol; intros; rewrite Z2Nat.id; abstract nia.
  Qed.

  Module Export Ex_Notations.
    Export Ex_Notations1.

    Hint Resolve solveCoMod_PolyCoMod_CoMod_morphism .

  End Ex_Notations.

End Resolve.

(**#+END_SRC

* Confluence

Confluence is ultimately to show that cut-elimination logical-rewriting is alternative description of cut-elimination computational-function ,.

Sometimes during the definition of some cut-elimination computationally-chosen function, then at every syntactic-match case, where there was some actual choice in the ambiguity of two basic-reductions on the input, this will require to append some corresponding solution-conversion on the two outputs, such that the alternative description of this cut-elimination via logical congruent-rewriting is valid ., 

Now these critical ambiguities produce the absent only solution-conversions which could prevent the deduction of what is named the confluence lemma : that for any two divergent basic-reduction, oneself can further-reduce to some same (solution-)morphism by commuting the effect of these two basic-reductions .,

+BEGIN_SRC coq :exports both :results silent **)

Module Confluence.

  (* Memo that the confluence lemma does not require some interface of the cut-elimination resolution where the rewriting-relation is the actual internal-equality, but it is sufficient that the rewriting-relation be the solution-conversion relation *)
  Declare Module Resolve : Resolve.
  Import Resolve.Ex_Notations.

(**#+END_SRC

** Goals accounting

The nested destructions of the two basic-reductions during the confluence lemma produce some total of
( ( 7 * 8 ) * ( 7 * 8 ) =  3136 goals ) ., After some initial automatic filtering-out ( exfalso ) of some impossible cases , there rest 705 goals ., Next some sequential manual solving until all the interesting cases are exhausted requires manually-inspecting approximataly 120 goals ,. Finally after cleaning the deduction and refactoring it into subdeductions ,. the COQ computer runs for 93 minutes plus some additional 27 minutes for the [Qed] check command ( dual core , 4 gigabytes memory ) ., The only painful part is doing interactive lemma deduction of such many goals without enough computer memory ,.

+BEGIN_SRC coq :exports both :results silent **)
  
      (* + h cong x k cong  = 7 x 7  == 8 match  ( possibly x 7 x 7 inner = 2401 )
         -  polyPre x polyPre , similar intermediate red via one IH
         -  polyPre x polyPost , same intermediate red
         -  polyPost x polyPost , similar intermediate red via one IH
         --  projX   x projX , similar intermediate red via one IH
         --  pairingX x pairingX , similar intermediate red via one IH on one component
         --  pairingX x pairingY , same intermediate red
         
         + h atom x k atom  = 7 x 7  == 5 match
         -  unitl x unitl  ,  no divergence     |- (_ <~ ?hk) (_ <~ ?hk)
         -  unitl x unitr  ,   no divergence     |- (_ <~ ?hk) (_ <~ ?hk)
         -  unitl x pairingmor , same intermediate red
         --  unitr x projXmor  , same intermediate red
         -  unitr x unitr  ,  no divergence
         -- projXmor x projXmor   , no divergence
         --  projXmor x pairingmor , derivable-simiar intermediate red ,
         - pairingmor x pairingmor , no divergence
         ---  pairingmor x projXmor , derivable-simiar intermediate red ,
         -- pairingprojX x pairingprojX , nodivergence 
         + h atom x k cong  = 7 x 7  == 10 match  ( possibly x 7 inner = 343 )
         -  unitl x polyPre ,  exfalso  (_ <~ uCoMod)%cong |-
         -  unitl x polyPost , same intermediate red
         -  unitr x polyPre , same intermediate red
         -  unitr x polyPost , exfalso  (_ <~ uCoMod)%cong |-
         --  projXmor x polyPre , unwrap-refine k cong (?gg <~ ~_X o> _)%cong |- , same intermediate red 
         --  projXmor x polyPost , same intermediate red 
         -  pairingmor x polyPre , same intermediate red 
         -  pairingmor x polyPost , unwrap-refine k cong (?gg <~ << _ , _>>)%cong |- , same intermediate red 
         -  pairingprojX x polyPre , unwrap-refine k cong (?gg <~ << _ , _>>)%cong |- , same intermediate red 
         --  pairingprojX x polyPost , unwrap-refine k cong (?gg <~ ~_Xo> _)%cong |- , same intermediate red 
         + h cong x k atom  = 7 x 7  == 0 match  ( possibly x 7 inner = 343 )
         - same as h atom x k cong = - 7 x 7
                          = 196 classes == 8 + 5 + 10 == 23 match  ( possibly = 3136 )
       
       after initial filtering : 705 goals out of 7 * 8 * 7 * 8 = 56 * 56 = 3136 goals ,
       after sequential manual solving except projXmor x pairingmor : 586 goals resting
             where projXmor x pairingmor is at 492 goals resting
       
       short : some total of ( ( 7 * 8 ) * ( 7 * 8 ) = 3136 goals ) , 
       but only ( 15 + 14 + 8 = 37 classes of goals) are critical via the automation-tactics 
       total timing (version by dependent destruction tactics) : start 19h01 - end 20h13 = 92.96m , qed start 20h15 - end ?h? = 27.81m 
       *)

  Ltac tac_atom_atom :=
    match goal with
    (* atom x atom *)
    (* unitl x unitl  ,  no divergence *)
    | [ Hcong_h : Cong.CoMod_unit.convCoMod _ ?gg ,
        Hcong_k : Cong.CoMod_unit.convCoMod _ ?gg |- _ ] =>
      do 2 ( exists (Resolve.solveCoMod gg) );
        intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* unitl x unitr  ,   no divergence *)
    | [ Hcong_h : Cong.CoMod_unit.convCoMod _ uCoMod ,
        Hcong_k : Cong.CoMod_inputUnitCoMod.convCoMod _ uCoMod |- _ ] =>
      do 2 ( exists (Resolve.solveCoMod uCoMod) );
        intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* unitl x pairingmor , same intermediate red *)
    | [ Hcong_h : Cong.CoMod_unit.convCoMod _ << ?g_1 ,CoMod ?g_2 >> ,
        Hcong_k : Cong.Limitator_morphism.convCoMod _ _ |- _ ] =>
      do 2 ( exists (Resolve.solveCoMod << g_1,CoMod g_2 >>) );
        intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* unitr x unitr  ,  no divergence *)
    | [ Hcong_h : Cong.CoMod_inputUnitCoMod.convCoMod (?gg o>CoMod _) ?gg,
        Hcong_k : Cong.CoMod_inputUnitCoMod.convCoMod (?gg o>CoMod _) ?gg |- _ ] =>
      do 2 ( exists (Resolve.solveCoMod gg) );
        intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* unitr x proj1mor  , same intermediate red *)
    | [ Hcong_h : Cong.CoMod_inputUnitCoMod.convCoMod _ ( ~_1 o>CoMod ?sub_gg ) ,
        Hcong_k : Cong.Project_1_morphism.convCoMod _ ( ~_1 o>CoMod (?sub_gg o>CoMod uCoMod) ) |- _ ] =>
      do 2 ( exists (Resolve.solveCoMod (  ~_1 o>CoMod sub_gg )) );
        intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* unitr x proj2mor  , same intermediate red *)
    | [ Hcong_h : Cong.CoMod_inputUnitCoMod.convCoMod _ ( ~_2 o>CoMod ?sub_gg ) ,
        Hcong_k : Cong.Project_2_morphism.convCoMod _ ( ~_2 o>CoMod (?sub_gg o>CoMod uCoMod) ) |- _ ] =>
      do 2 ( exists (Resolve.solveCoMod (  ~_2 o>CoMod sub_gg )) );
        intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* proj1mor x proj1mor ,  no divergence  *)
    | [ Hcong_h : Cong.Project_1_morphism.convCoMod _ (~_1 o>CoMod (?b1 o>CoMod ?b1')) ,
        Hcong_k : Cong.Project_1_morphism.convCoMod _ (~_1 o>CoMod (?b1 o>CoMod ?b1'))
        |- context[ ( _ <~~ ~_1 o>CoMod (?b1 o>CoMod ?b1') )%rew ] ] =>
      do 2 ( exists (Resolve.solveCoMod ( ~_1 o>CoMod (b1 o>CoMod b1') )) );
        intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* proj1mor x pairingmor , derivable-simiar intermediate red *)
    | [ Hcong_h : Cong.Project_1_morphism.convCoMod _ (~_1 o>CoMod (?sub_gg_ o>CoMod << ?subX_gg' ,CoMod ?subY_gg' >>)) ,
        Hcong_k : Cong.Limitator_morphism.convCoMod _
                    << (~_1 o>CoMod ?sub_gg_) o>CoMod ?subX_gg' ,CoMod (~_1 o>CoMod ?sub_gg_) o>CoMod ?subY_gg' >>
        |- context[ {h' : _ & {k' : _ & ( ( _ <~~ ~_1 o>CoMod (?sub_gg_ o>CoMod << ?subX_gg' ,CoMod ?subY_gg' >>) )%rew * _ )%type }} ] ] =>
      exists (Resolve.solveCoMod ( ~_1 o>CoMod ( << sub_gg_ o>CoMod subX_gg' ,CoMod sub_gg_ o>CoMod subY_gg' >> ) ));
        exists (Resolve.solveCoMod (  << ( ~_1 o>CoMod sub_gg_ ) o>CoMod subX_gg' ,CoMod ( ~_1 o>CoMod sub_gg_ ) o>CoMod subY_gg' >> ));
        repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
          intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* proj2mor x pairingmor , derivable-simiar intermediate red *)
    | [ Hcong_h : Cong.Project_2_morphism.convCoMod _ (~_2 o>CoMod (?sub_gg_ o>CoMod << ?subX_gg' ,CoMod ?subY_gg' >>)) ,
        Hcong_k : Cong.Limitator_morphism.convCoMod _
                    << (~_2 o>CoMod ?sub_gg_) o>CoMod ?subX_gg' ,CoMod (~_2 o>CoMod ?sub_gg_) o>CoMod ?subY_gg' >>
        |- context[ {h' : _ & {k' : _ & ( ( _ <~~ ~_2 o>CoMod (?sub_gg_ o>CoMod << ?subX_gg' ,CoMod ?subY_gg' >>) )%rew * _ )%type }} ] ] =>
      exists (Resolve.solveCoMod ( ~_2 o>CoMod ( << sub_gg_ o>CoMod subX_gg' ,CoMod sub_gg_ o>CoMod subY_gg' >> ) ));
        exists (Resolve.solveCoMod (  << ( ~_2 o>CoMod sub_gg_ ) o>CoMod subX_gg' ,CoMod ( ~_2 o>CoMod sub_gg_ ) o>CoMod subY_gg' >> ));
        repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
          intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* proj2mor x proj2mor ,  no divergence   *)
    | [ Hcong_h : Cong.Project_2_morphism.convCoMod _ (~_2 o>CoMod (?b2 o>CoMod ?b2')) ,
        Hcong_k : Cong.Project_2_morphism.convCoMod _ (~_2 o>CoMod (?b2 o>CoMod ?b2'))
        |- context[ ( _ <~~ ~_2 o>CoMod (?b2 o>CoMod ?b2') )%rew ] ] =>
      do 2 ( exists (Resolve.solveCoMod ( ~_2 o>CoMod (b2 o>CoMod b2') )) );
        intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* pairingmor x proj1mor (permute) , derivable-simiar intermediate red *)
    | [ Hcong_h : Cong.Limitator_morphism.convCoMod _
                    << (~_1 o>CoMod ?sub_gg_) o>CoMod ?subX_gg' ,CoMod (~_1 o>CoMod ?sub_gg_) o>CoMod ?subY_gg' >> ,
        Hcong_k : Cong.Project_1_morphism.convCoMod _ (~_1 o>CoMod (?sub_gg_ o>CoMod << ?subX_gg' ,CoMod ?subY_gg' >>)) 
        |- context[ {h' : _ & {k' : _ & ( ( _ <~~ << (~_1 o>CoMod ?sub_gg_) o>CoMod ?subX_gg' ,CoMod (~_1 o>CoMod ?sub_gg_) o>CoMod ?subY_gg' >> )%rew * _ )%type }} ] ] =>
      exists (Resolve.solveCoMod (  << ( ~_1 o>CoMod sub_gg_ ) o>CoMod subX_gg' ,CoMod ( ~_1 o>CoMod sub_gg_ ) o>CoMod subY_gg' >> ));
      exists (Resolve.solveCoMod ( ~_1 o>CoMod ( << sub_gg_ o>CoMod subX_gg' ,CoMod sub_gg_ o>CoMod subY_gg' >> ) ));
      repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
      intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* pairingmor x proj2mor (permute) , derivable-simiar intermediate red *)
    | [ Hcong_h : Cong.Limitator_morphism.convCoMod _
                    << (~_2 o>CoMod ?sub_gg_) o>CoMod ?subX_gg' ,CoMod (~_2 o>CoMod ?sub_gg_) o>CoMod ?subY_gg' >> ,
        Hcong_k : Cong.Project_2_morphism.convCoMod _ (~_2 o>CoMod (?sub_gg_ o>CoMod << ?subX_gg' ,CoMod ?subY_gg' >>)) 
        |- context[ {h' : _ & {k' : _ & ( ( _ <~~ << (~_2 o>CoMod ?sub_gg_) o>CoMod ?subX_gg' ,CoMod (~_2 o>CoMod ?sub_gg_) o>CoMod ?subY_gg' >> )%rew * _ )%type }} ] ] =>
      exists (Resolve.solveCoMod (  << ( ~_2 o>CoMod sub_gg_ ) o>CoMod subX_gg' ,CoMod ( ~_2 o>CoMod sub_gg_ ) o>CoMod subY_gg' >> ));
      exists (Resolve.solveCoMod ( ~_2 o>CoMod ( << sub_gg_ o>CoMod subX_gg' ,CoMod sub_gg_ o>CoMod subY_gg' >> ) ));
      repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
      intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* pairingmor x pairingmor ,  no divergence   *)
    | [ Hcong_h : Cong.Limitator_morphism.convCoMod _ << ?m o>CoMod ?g_1 ,CoMod ?m o>CoMod ?g_2 >> ,
                  Hcong_k : Cong.Limitator_morphism.convCoMod _ << ?m o>CoMod ?g_1 ,CoMod ?m o>CoMod ?g_2 >>
        |- context[ ( _ <~~  << ?m o>CoMod ?g_1 ,CoMod ?m o>CoMod ?g_2 >> )%rew ] ] =>
      do 2 ( exists (Resolve.solveCoMod ( << m o>CoMod g_1 ,CoMod m o>CoMod g_2 >> )) );
      intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* pairingproj1 x pairingproj1 ,  no divergence   *)
    | [ Hcong_h : Cong.Limitator_Project_1.convCoMod _ (?g_1 o>CoMod ?b1) ,
                  Hcong_k : Cong.Limitator_Project_1.convCoMod _ (?g_1 o>CoMod ?b1)
        |- context[ ( _ <~~   ?g_1 o>CoMod ?b1 )%rew ] ] =>
      do 2 ( exists (Resolve.solveCoMod (  g_1 o>CoMod b1 )) );
      intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* pairingproj2 x pairingproj2 ,  no divergence   *)
    | [ Hcong_h : Cong.Limitator_Project_2.convCoMod _ (?g_2 o>CoMod ?b2) ,
                  Hcong_k : Cong.Limitator_Project_2.convCoMod _ (?g_2 o>CoMod ?b2)
        |- context[ ( _ <~~   ?g_2 o>CoMod ?b2 )%rew ] ] =>
      do 2 ( exists (Resolve.solveCoMod (  g_2 o>CoMod b2 )) );
      intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    end.
  
  Ltac tac_atom_cong :=
    match goal with
    (* atom x cong  *)
    (* unitl x polyPre ,  exfalso *)
    | [ Hcong_h : Cong.CoMod_unit.convCoMod (uCoMod o>CoMod ?gg') ?gg' ,
        Hcong_k : (?gg_cong_k <~~ uCoMod)%cong |- _ ] =>
      exfalso; clear -Hcong_k;
        dependent destruction Hcong_k;
        match goal with
        | [ Hcong_k : _  uCoMod gg_cong_k |- _ ] =>
          dependent destruction Hcong_k
        end 
    (* unitl x polyPost , same intermediate red *)
    | [ Hcong_h : Cong.CoMod_unit.convCoMod (uCoMod o>CoMod ?gg') ?gg' ,
        Hcong_k : (?gg'cong_h <~~ ?gg')%cong
        |- context[ (_ <~~ uCoMod o>CoMod ?gg'cong_h)%rew ] ] =>
      do 2 ( exists (Resolve.solveCoMod gg'cong_h) );
        intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* unitr x polyPre , same intermediate red *)
    | [ Hcong_h : Cong.CoMod_inputUnitCoMod.convCoMod (?gg_ o>CoMod ?gg') _ ,
        Hcong_k : (?gg_cong_k <~~ ?gg_)%cong
        |- context[ ( _ <~~ ?gg_cong_k o>CoMod ?gg' )%rew ] ] =>
      dependent destruction Hcong_h;
        do 2 ( exists (Resolve.solveCoMod gg_cong_k) );
        intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* unitr x polyPost , exfalso  (_ <~ uCoMod)%cong |- *)
    | [ Hcong_h : Cong.CoMod_inputUnitCoMod.convCoMod (?gg_ o>CoMod ?gg') _ ,
        Hcong_k : (?gg'cong_k <~~ ?gg')%cong |- _ ] =>
      exfalso; dependent destruction Hcong_h; dependent destruction Hcong_k;
        match goal with
        | [ Hcong_k : _  uCoMod gg'cong_k |- _ ] =>
          dependent destruction Hcong_k
        end
    (* polyPre x proj1mor , unwrap-refine h cong (?gg <~ ~_X o> _)%cong |- , same intermediate red *)
    | [ Hcong_h : (?gg_cong_h <~~ ?gg_)%cong,
        Hcong_k : Cong.Project_1_morphism.convCoMod (?gg_ o>CoMod ?gg') _
        |- context[ ( _ <~~ ?gg_cong_h o>CoMod ?gg' )%rew ] ] =>
      dependent destruction Hcong_k; dependent destruction Hcong_h;
        [ solve [ match goal with
                  | [ Hcong_h : _ (~_1 o>CoMod _) gg_cong_h |- _ ] => dependent destruction Hcong_h
                  end ] | ];
        match goal with
        | [ Hcong_h : (?sub_gg_cong_h <~~ ?sub_gg_)%cong |- _ ] =>
          do 2 ( exists (Resolve.solveCoMod (~_1 o>CoMod (sub_gg_cong_h o>CoMod gg'))) );
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
        end
    (* polyPre x proj2mor , unwrap-refine h cong (?gg <~ ~_X o> _)%cong |- , same intermediate red *)
    | [ Hcong_h : (?gg_cong_h <~~ ?gg_)%cong,
        Hcong_k : Cong.Project_2_morphism.convCoMod (?gg_ o>CoMod ?gg') _
        |- context[ ( _ <~~ ?gg_cong_h o>CoMod ?gg' )%rew ] ] =>
      dependent destruction Hcong_k; dependent destruction Hcong_h;
        [ solve [ match goal with
                  | [ Hcong_h : _ (~_2 o>CoMod _) gg_cong_h |- _ ] => dependent destruction Hcong_h
                  end ] | ];
        match goal with
        | [ Hcong_h : (?sub_gg_cong_h <~~ ?sub_gg_)%cong |- _ ] =>
          do 2 ( exists (Resolve.solveCoMod (~_2 o>CoMod (sub_gg_cong_h o>CoMod gg'))) );
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
        end
    (* polyPost x proj1mor ,  same intermediate red  *)
    | [ Hcong_h : (?gg'cong_h <~~ ?gg')%cong,
        Hcong_k : Cong.Project_1_morphism.convCoMod (?gg_ o>CoMod ?gg') _
        |- context[ ( _ <~~ ?gg_ o>CoMod ?gg'cong_h )%rew ] ] =>
      dependent destruction Hcong_k;
        match goal with
        | [ |- context[ ( ~_1 o>CoMod ?sub_gg_ ) o>CoMod gg'cong_h ] ] =>
          do 2 ( exists (Resolve.solveCoMod (~_1 o>CoMod (sub_gg_ o>CoMod gg'cong_h))) );
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
        end
    (* polyPost x proj2mor ,  same intermediate red  *)
    | [ Hcong_h : (?gg'cong_h <~~ ?gg')%cong,
        Hcong_k : Cong.Project_2_morphism.convCoMod (?gg_ o>CoMod ?gg') _
        |- context[ ( _ <~~ ?gg_ o>CoMod ?gg'cong_h )%rew ] ] =>
      dependent destruction Hcong_k;
        match goal with
        | [ |- context[ ( ~_2 o>CoMod ?sub_gg_ ) o>CoMod gg'cong_h ] ] =>
          do 2 ( exists (Resolve.solveCoMod (~_2 o>CoMod (sub_gg_ o>CoMod gg'cong_h))) );
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
        end
    (* pairingmor x polyPre , same intermediate red  *)
    | [ Hcong_h : (?gg_cong_h <~~ ?gg_)%cong,
        Hcong_k : Cong.Limitator_morphism.convCoMod (?gg_ o>CoMod ?gg') _
        |- context[ ( _ <~~ ?gg_cong_h o>CoMod ?gg' )%rew ] ] =>
      dependent destruction Hcong_k;
        match goal with
        | [ |- context[ ( gg_cong_h o>CoMod << ?gg_1 ,CoMod ?gg_2 >> ) ] ] => 
          do 2 ( exists (Resolve.solveCoMod ( << gg_cong_h o>CoMod gg_1 ,CoMod gg_cong_h o>CoMod gg_2 >> )) );
            assert (Hcong_h_rew : (gg_cong_h <~~ gg_)%rew) by eauto;
            intuition (eauto; rewrite -?tac_Rewrite ?Hcong_h_rew /= ; eauto)
        end
    (* pairingmor x polyPost , unwrap-refine k cong (?gg <~ << _ , _>>)%cong |- , same intermediate red *)
    | [ Hcong_h : (?gg'cong_h <~~ ?gg')%cong,
        Hcong_k : Cong.Limitator_morphism.convCoMod (?gg_ o>CoMod ?gg') _
        |- context[ ( _ <~~ ?gg_ o>CoMod ?gg'cong_h )%rew ] ] =>
      dependent destruction Hcong_k; dependent destruction Hcong_h;
        [ solve [ match goal with
                  | [ Hcong_h : _ (<< ?gg'1 ,CoMod ?gg'2 >>) gg'cong_h |- _ ] =>
                    dependent destruction Hcong_h
                  end ]
        | match goal with
          | [ Hcong_h : (?subX_gg'cong_h <~~ ?subX_gg')%cong
              |- context[ gg_ o>CoMod << ?subX_gg'cong_h ,CoMod ?subY_gg' >> ] ] =>
            do 2 ( exists (Resolve.solveCoMod ( << gg_ o>CoMod subX_gg'cong_h ,CoMod gg_ o>CoMod subY_gg' >>)) );
            assert (Hcong_h_rew : (subX_gg'cong_h <~~ subX_gg')%rew) by eauto;
            repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite ?Hcong_h_rew /= ; eauto)
          end
        | match goal with
          | [ Hcong_h : (?subY_gg'cong_h <~~ ?subY_gg')%cong
              |- context[ gg_ o>CoMod << ?subX_gg' ,CoMod ?subY_gg'cong_h >> ] ] =>
            do 2 ( exists (Resolve.solveCoMod ( << gg_ o>CoMod subX_gg' ,CoMod gg_ o>CoMod subY_gg'cong_h >>)) );
            assert (Hcong_h_rew : (subY_gg'cong_h <~~ subY_gg')%rew) by eauto;
            repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite ?Hcong_h_rew /= ; eauto)
          end ]
    (* pairingproj1 x polyPre , unwrap-refine k cong (?gg <~ << _ , _>>)%cong |- , same intermediate red  *)
    | [ Hcong_h : (?gg_cong_h <~~ ?gg_)%cong,
        Hcong_k : Cong.Limitator_Project_1.convCoMod (?gg_ o>CoMod ?gg') _
        |- context[ ( _ <~~ ?gg_cong_h o>CoMod ?gg' )%rew ] ] =>
      dependent destruction Hcong_k; dependent destruction Hcong_h;
        [ solve [ match goal with
                  | [ Hcong_h : _ (<< ?gg_1 ,CoMod ?gg_2 >>) gg_cong_h |- _ ] =>
                    dependent destruction Hcong_h
                  end ]
        | match goal with
          | [ Hcong_h : (?subX_gg_cong_h <~~ ?subX_gg_)%cong
              |- context[ << ?subX_gg_cong_h ,CoMod _ >> o>CoMod (~_1 o>CoMod ?sub_gg') ] ] =>
            do 2 ( exists (Resolve.solveCoMod (subX_gg_cong_h o>CoMod sub_gg')) );
            assert (Hcong_h_rew : (subX_gg_cong_h <~~ subX_gg_)%rew) by eauto;
            repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite ?Hcong_h_rew /= ; eauto)
          end
        | match goal with
          | [ Hcong_h : (?subY_gg_cong_h <~~ ?subY_gg_)%cong
              |- context[ << ?subX_gg_ ,CoMod ?subY_gg_cong_h >> o>CoMod (~_1 o>CoMod ?sub_gg') ] ] =>
            do 2 ( exists (Resolve.solveCoMod (subX_gg_ o>CoMod sub_gg')) );
            repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
          end ]
    (* pairingproj2 x polyPre , unwrap-refine k cong (?gg <~ << _ , _>>)%cong |- , same intermediate red  *)
    | [ Hcong_h : (?gg_cong_h <~~ ?gg_)%cong,
        Hcong_k : Cong.Limitator_Project_2.convCoMod (?gg_ o>CoMod ?gg') _
        |- context[ ( _ <~~ ?gg_cong_h o>CoMod ?gg' )%rew ] ] =>
      dependent destruction Hcong_k; dependent destruction Hcong_h;
        [ solve [ match goal with
                  | [ Hcong_h : _ (<< ?gg_1 ,CoMod ?gg_2 >>) gg_cong_h |- _ ] =>
                    dependent destruction Hcong_h
                  end ]
        | match goal with
          | [ Hcong_h : (?subX_gg_cong_h <~~ ?subX_gg_)%cong
              |- context[ << ?subX_gg_cong_h ,CoMod ?subY_gg_ >> o>CoMod (~_2 o>CoMod ?sub_gg') ] ] =>
            do 2 ( exists (Resolve.solveCoMod (subY_gg_ o>CoMod sub_gg')) );
            repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
          end
        | match goal with
          | [ Hcong_h : (?subY_gg_cong_h <~~ ?subY_gg_)%cong
              |- context[ << ?subX_gg_ ,CoMod ?subY_gg_cong_h >> o>CoMod (~_2 o>CoMod ?sub_gg') ] ] =>
            do 2 ( exists (Resolve.solveCoMod (subY_gg_cong_h o>CoMod sub_gg')) );
            assert (Hcong_h_rew : (subY_gg_cong_h <~~ subY_gg_)%rew) by eauto;
            repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite ?Hcong_h_rew /= ; eauto)
          end ]
    (* pairingproj1 x polyPost , unwrap-refine k cong (?gg <~ ~_Xo> _)%cong |- , same intermediate red *)
    | [ Hcong_h : (?gg'cong_h <~~ ?gg')%cong,
        Hcong_k : Cong.Limitator_Project_1.convCoMod (?gg_ o>CoMod ?gg') _
        |- context[ ( _ <~~ ?gg_ o>CoMod ?gg'cong_h )%rew ] ] =>
      dependent destruction Hcong_k; dependent destruction Hcong_h;
        [ solve [ match goal with
                  | [ Hcong_h : _ ( ~_1 o>CoMod _ ) gg'cong_h |- _ ] =>
                    dependent destruction Hcong_h
                  end ] | ];
        match goal with
        | [ Hcong_h : (?sub_gg'cong_h <~~ ?sub_gg')%cong
            |- context[ << ?subX_gg_ ,CoMod ?subY_gg_ >> o>CoMod (~_1 o>CoMod ?sub_gg'cong_h) ] ] =>
          do 2 ( exists (Resolve.solveCoMod (subX_gg_ o>CoMod sub_gg'cong_h)) );
            assert (Hcong_h_rew : (sub_gg'cong_h <~~ sub_gg')%rew) by eauto;
            repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
              intuition (eauto; rewrite -?tac_Rewrite ?Hcong_h_rew /= ; eauto)
        end
    (* pairingproj2 x polyPost , unwrap-refine k cong (?gg <~ ~_Xo> _)%cong |- , same intermediate red *)
    | [ Hcong_h : (?gg'cong_h <~~ ?gg')%cong,
        Hcong_k : Cong.Limitator_Project_2.convCoMod (?gg_ o>CoMod ?gg') _
        |- context[ ( _ <~~ ?gg_ o>CoMod ?gg'cong_h )%rew ] ] =>
      dependent destruction Hcong_k; dependent destruction Hcong_h;
        [ solve [ match goal with
                  | [ Hcong_h : _ ( ~_2 o>CoMod _ ) gg'cong_h |- _ ] =>
                    dependent destruction Hcong_h
                  end ] | ];
        match goal with
        | [ Hcong_h : (?sub_gg'cong_h <~~ ?sub_gg')%cong
            |- context[ << ?subX_gg_ ,CoMod ?subY_gg_ >> o>CoMod (~_2 o>CoMod ?sub_gg'cong_h) ] ] =>
          do 2 ( exists (Resolve.solveCoMod (subY_gg_ o>CoMod sub_gg'cong_h)) );
            assert (Hcong_h_rew : (sub_gg'cong_h <~~ sub_gg')%rew) by eauto;
            repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
              intuition (eauto; rewrite -?tac_Rewrite ?Hcong_h_rew /= ; eauto)
        end
    end.                  

  Ltac tac_cong_cong :=
    match goal with
    (* cong x cong *)
    (* polyPre x polyPre , similar intermediate red via one IH *)
    | [ Hcong_h : (?gg_cong_h <~~ ?gg_)%cong,
        Hcong_k : (?gg_cong_k <~~ ?gg_)%cong,
        IHcong_h : forall kk, (kk <~~ ?gg_)%once -> _
        |- context[ ( _ <~~ ?gg_cong_h o>CoMod ?gg' )%rew ] ] =>
      destruct (@IHcong_h gg_cong_k) as (h' , (k' , h'k'P)); [ eauto |  ];
        exists (Resolve.solveCoMod ((Sol.toCoMod h') o>CoMod gg'));
        exists (Resolve.solveCoMod ((Sol.toCoMod k') o>CoMod gg'));
          repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* polyPre x polyPost , same intermediate red *)
    | [ Hcong_h : (?gg_cong_h <~~ ?gg_)%cong , Hcong_k : (?gg'cong_k <~~ ?gg')%cong
        |- context[ ( _ <~~ ?gg_cong_h o>CoMod ?gg' )%rew ] ] =>
      match goal with
      | [  |- context[ ( _ <~~ gg_ o>CoMod gg'cong_k )%rew ] ] =>
        do 2 ( exists (Resolve.solveCoMod (gg_cong_h o>CoMod gg'cong_k)) );
          repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
      end
    (* polyPost x polyPost , similar intermediate red via one IH *)
    | [ Hcong_h : (?gg'cong_h <~~ ?gg')%cong,
        Hcong_k : (?gg'cong_k <~~ ?gg')%cong,
        IHcong_h : forall kk, (kk <~~ ?gg')%once -> _
       |- context[ ( _ <~~ ?gg_ o>CoMod ?gg'cong_h )%rew ] ] =>
      destruct (@IHcong_h gg'cong_k) as (h' , (k' , h'k'P)); [ eauto |  ];
        exists (Resolve.solveCoMod (gg_ o>CoMod (Sol.toCoMod h')));
        exists (Resolve.solveCoMod (gg_ o>CoMod (Sol.toCoMod k')));
          repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* proj1   x proj1 , similar intermediate red via one IH *)
    | [ Hcong_h : (?gg'_cong_h <~~ ?gg)%cong,
        Hcong_k : (?gg'_cong_k <~~ ?gg)%cong,
        IHcong_h : forall k, (k <~~ ?gg)%once -> _
        |- context[ ( _ <~~ ~_1 o>CoMod ?gg'_cong_h )%rew ] ] =>
      destruct (@IHcong_h gg'_cong_k) as (h' , (k' , h'k'P)); [ eauto |  ];
        exists (Resolve.solveCoMod ( ~_1 o>CoMod (Sol.toCoMod h') ));
        exists (Resolve.solveCoMod ( ~_1 o>CoMod (Sol.toCoMod k') ));
          repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* proj2   x proj2 , similar intermediate red via one IH *)
    | [ Hcong_h : (?gg'_cong_h <~~ ?gg)%cong,
        Hcong_k : (?gg'_cong_k <~~ ?gg)%cong,
        IHcong_h : forall k, (k <~~ ?gg)%once -> _
        |- context[ ( _ <~~ ~_2 o>CoMod ?gg'_cong_h )%rew ] ] =>
      destruct (@IHcong_h gg'_cong_k) as (h' , (k' , h'k'P)); [ eauto |  ];
        exists (Resolve.solveCoMod ( ~_2 o>CoMod (Sol.toCoMod h') ));
        exists (Resolve.solveCoMod ( ~_2 o>CoMod (Sol.toCoMod k') ));
          repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* pairing1 x pairing1 , similar intermediate red via one IH on one component *)
    | [ Hcong_h : (?subX_gg'_cong_h <~~ ?subX_gg)%cong,
        Hcong_k : (?subX_gg'_cong_k <~~ ?subX_gg)%cong,
        IHcong_h : forall k, (k <~~ ?subX_gg)%once -> _
        |- context[ ( _ <~~ << ?subX_gg'_cong_h ,CoMod ?subY_gg >> )%rew ] ] =>
      destruct (@IHcong_h subX_gg'_cong_k) as (h' , (k' , h'k'P)); [ eauto |  ];
        exists (Resolve.solveCoMod ( << (Sol.toCoMod h') ,CoMod subY_gg >> ));
        exists (Resolve.solveCoMod ( << (Sol.toCoMod k') ,CoMod subY_gg >> ));
          repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* pairing2 x pairing2 , similar intermediate red via one IH on one component *)
    | [ Hcong_h : (?subY_gg'_cong_h <~~ ?subY_gg)%cong,
        Hcong_k : (?subY_gg'_cong_k <~~ ?subY_gg)%cong,
        IHcong_h : forall k, (k <~~ ?subY_gg)%once -> _
        |- context[ ( _ <~~ << ?subX_gg ,CoMod ?subY_gg'_cong_h >> )%rew ] ] =>
      destruct (@IHcong_h subY_gg'_cong_k) as (h' , (k' , h'k'P)); [ eauto |  ];
        exists (Resolve.solveCoMod ( << subX_gg ,CoMod (Sol.toCoMod h') >> ));
        exists (Resolve.solveCoMod ( << subX_gg ,CoMod (Sol.toCoMod k') >> ));
          repeat split; [ | | rewrite -!(tac_solveCoMod, tac_solveCoMod_PolyCoMod) /=  ];
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    (* pairingX x pairingY , same intermediate red *)
    | [ Hcong_h : (?subX_gg'_cong_h <~~ ?subX_gg)%cong,
        Hcong_k : (?subY_gg'_cong_k <~~ ?subY_gg)%cong
        |- context[ ( _ <~~ << ?subX_gg'_cong_h ,CoMod ?subY_gg >> )%rew ] ] =>
        do 2 ( exists (Resolve.solveCoMod ( << subX_gg'_cong_h ,CoMod subY_gg'_cong_k >> )) );
            intuition (eauto; rewrite -?tac_Rewrite /= ; eauto)
    end.

  Lemma confluence : forall (B1 B2 : obCoMod) (g h : 'CoMod(0 B1 ~> B2 )0),
      ( h <~~ g )%once -> forall k, ( k <~~ g )%once ->
      { h' : 'CoMod(0 B1 ~> B2 )0 %sol
             & { k' : 'CoMod(0 B1 ~> B2 )0 %sol
                      & ( ( Sol.toCoMod h' <~~ h )%rew * ( ( Sol.toCoMod k' <~~ k )%rew *
                          ( ( h' ~~~ k' )%sol_conv ) ) )%type } }.
  Proof.
    intros B1 B2 g h Honce_h k Honce_k.
    destruct Honce_h;
      [ ( induction c; try rename c into Hcong_h;
          try rename IHc into IHcong_h; try rename IHc1 into IHcong1_h;
          try rename IHc2 into IHcong2_h;
          [ (move : (Hcong_h) => Hcong_h_copy); dependent destruction Hcong_h_copy;
            dependent destruction Honce_k;
            [ ( dependent destruction c; try rename c into Hcong_k;
                [ (* h atom x k atom *)
                  (move : (Hcong_k) => Hcong_k_copy); dependent destruction Hcong_k_copy;
                   abstract tac_atom_atom
                | ( (* h atom x k cong *)
                  try solve [(move : (Hcong_k) => Hcong_k_copy); dependent destruction Hcong_k_copy];
                   abstract tac_atom_cong
                ) .. ]
              ) .. ]
          | ( dependent destruction Honce_k;
              [ ( dependent destruction c; try rename c into Hcong_k;
                  [ (* h cong x k atom *)
                    (move : (Hcong_k) => Hcong_k_copy); dependent destruction Hcong_k_copy;
                     abstract tac_atom_cong
                  | ( (* h cong x k cong *)
                    try solve [(move : (Hcong_k) => Hcong_k_copy); dependent destruction Hcong_k_copy];
                    abstract tac_cong_cong
                  ) .. ]
                ) .. ]
            ) .. ]
        ) .. ] .  
  Qed.
  (* Admitted. *) (* skip during testing *)
    
(**#+END_SRC

** Unique solution for the logical-rewriting relation

Confluence is ultimately to show that cut-elimination logical-rewriting is alternative description of cut-elimination computational-function , in other words : the graph of the logical-rewriting relation into solutions is some function ( .., with at most one output ( .., modulo solution-conversion ) ). 

+BEGIN_SRC coq :exports both :results silent **)

  Fixpoint uniqueSolution_ len {struct len} :
    forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0),
    forall (H_gradeParticular : ( (Rewrite.gradeParticular g) <= Z.of_nat len)%Z ),
      forall h : 'CoMod(0 B1 ~> B2 )0 %sol,
        ( Sol.toCoMod h <~~ g )%rew ->
        forall k : 'CoMod(0 B1 ~> B2 )0 %sol,
          ( Sol.toCoMod k <~~ g )%rew -> ( h ~~~ k )%sol_conv.
  Proof.
    case : len => [ | len ].
 
    (* n is O *)
    - clear; ( move => B1 B2 g H_gradeParticular h Hrew_h k Hrew_k ); exfalso;
        tac_gradeParticular_gt0; intros; abstract nia.

    (* n is (S n) *)
    - move =>  B1 B2 g H_gradeParticular h Hrew_h k Hrew_k .
      dependent destruction Hrew_h;
        dependent destruction Hrew_k;
        [ match goal with
            [ Heq : Sol.toCoMod _ = Sol.toCoMod _ |- _ ] =>
            rewrite (Sol.toCoMod_injective x) {uniqueSolution_} //
          end
        | match goal with
            [ Honce :  ( _ <~~ _ )%once |- _ ] =>
            ( move : Honce => /Rewrite.isSolb_isRed_False_alt /Sol.isSolbN_isSolN_alt => * );
            clear uniqueSolution_ ; exfalso; eauto
          end
            ..
        | match goal with
            [ Honce_h :  ( ?uTrans_h <~~ ?gg )%once ,
                         Honce_k :  ( ?uTrans_k <~~ ?gg )%once |- _ ] =>
            (move: (confluence Honce_h Honce_k) => [h' [ k' h'k'P]]);
            ( move : (Rewrite.degrade Honce_h) (Rewrite.degrade Honce_k) => H_degrade_Honce_h H_degrade_Honce_k );
            transitivity h';
            [ transitivity k';
               [ apply: (uniqueSolution_ len _ _ uTrans_k)
               | clear -h'k'P; by intuition ]
             | apply: (uniqueSolution_ len _ _ uTrans_h) ];
            clear uniqueSolution_ ; abstract intuition (eauto; nia)
          end ] .
  Defined.

  Lemma uniqueSolution : forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0),
      forall h : 'CoMod(0 B1 ~> B2 )0 %sol,
        ( Sol.toCoMod h <~~ g )%rew ->
        forall k : 'CoMod(0 B1 ~> B2 )0 %sol,
          ( Sol.toCoMod k <~~ g )%rew -> ( h ~~~ k )%sol_conv.
  Proof.
    intros ? ? g; apply: (@uniqueSolution_ (Z.to_nat(Rewrite.gradeParticular g)));
        tac_gradeParticular_gt0; intros; rewrite Z2Nat.id; abstract nia.
  Qed.

  Lemma uniqueSolution_solveCoMod :
    forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0),
    forall (k : 'CoMod(0 B1 ~> B2 )0 %sol), ( Sol.toCoMod k <~~ g )%rew ->
       ( (Resolve.solveCoMod g) ~~~ k )%sol_conv .
  Proof.
    intros B1 B2 g k Hrew. move: (Resolve.solveCoModP1 g) => Hrew_solveCoModP1_g.
    eapply uniqueSolution with (g := g); eassumption.
  Qed.

  Lemma confluence_multi : forall (B1 B2 : obCoMod) (g h : 'CoMod(0 B1 ~> B2 )0),
      ( h <~~ g )%rew -> forall k, ( k <~~ g )%rew ->
      { h' : 'CoMod(0 B1 ~> B2 )0 %sol
             & { k' : 'CoMod(0 B1 ~> B2 )0 %sol
                      & ( ( Sol.toCoMod h' <~~ h )%rew * ( ( Sol.toCoMod k' <~~ k )%rew *
                          ( ( h' ~~~ k' )%sol_conv ) ) )%type } }.
  Proof.
    intros B1 B2 g h Hrew_h k Hrew_k.
    exists (Resolve.solveCoMod h). exists (Resolve.solveCoMod k).
    move: (Resolve.solveCoModP1 h) (Resolve.solveCoModP1 k) (@uniqueSolution _ _ g). intuition eauto.
  Qed.

End Confluence.

(**#+END_SRC

* Polymorphism conversion

This symmetrized rewrite relation [Polymorphism] gives the sense in the polymorphism-terminology ,. In
addition to the earlier rewrite relation [Rewrite] conversions, oneself appends the << eta-conversion >> [imitator_Project_1_Project_2] that the pairing of the two projections is the identity , also oneself appends the << cut-polymorphism >> conversion ( "associativity" ) [CoMod_morphism] , also oneself appends the symmetrized form of every conversion [convCoMod_List_Sym] ,.

+BEGIN_SRC coq :exports both :results silent **)

Module Polymorphism.

  Import Rewrite.Ex_Notations.
  Import Sol.Ex_Notations.

  Reserved Notation "g2 <~> g1" (at level 70). (*TODO: change to <~> *)

  Module Cong.

    Module Limitator_Project_1_Project_2.

      Variant convCoMod : forall (B1 B2 : obCoMod),
        'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type :=

      | Limitator_Project_1_Project_2 : forall B1 B2,
          ( uCoMod )
            <~> ( << ~_1 @ B2 o>CoMod uCoMod ,CoMod ~_2 @ B1 o>CoMod uCoMod >>
                : 'CoMod(0 Limit B1 B2 ~> Limit B1 B2 )0 )

      where "g2 <~> g1" := (@convCoMod _ _ g1 g2).
      
    End Limitator_Project_1_Project_2.

    Module CoMod_morphism.

      Variant convCoMod : forall (B1 B2 : obCoMod),
        'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type :=

      | CoMod_morphism :
          forall (B0 B : obCoMod) (g : 'CoMod(0 B0 ~> B )0)
            (B' : obCoMod) (g_ : 'CoMod(0 B ~> B' )0)
            (B'' : obCoMod) (g' : 'CoMod(0 B' ~> B'' )0),
            ( ( g o>CoMod ( g_ o>CoMod g' ) )
                <~> ( ( g o>CoMod g_ ) o>CoMod g' 
                    : 'CoMod(0 B0 ~> B'' )0 ) )

      where "g2 <~> g1" := (@convCoMod _ _ g1 g2).
      
    End CoMod_morphism.

    Module Export Ex_Notations.
      Hint Constructors Limitator_Project_1_Project_2.convCoMod CoMod_morphism.convCoMod.
    End Ex_Notations.

  End Cong.

  Module Once.
    
    Section Section1.
      Import Cong.Ex_Notations.
      
      Variant convCoMod : forall (B1 B2 : obCoMod),
          'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Type :=

      | Rewrite_Once : forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0),
          ( g2 <~~ g1 )%once -> g2 <~> g1

      | Limitator_Project_1_Project_2 : forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0),
          ( g2 <~~ g1 @ Cong.Limitator_Project_1_Project_2.convCoMod )%cong -> g2 <~> g1

      | CoMod_morphism : forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0),
          ( g2 <~~ g1 @ Cong.CoMod_morphism.convCoMod )%cong -> g2 <~> g1

      where "g2 <~> g1" := (@convCoMod _ _ g1 g2).

    End Section1.

    Module Export Ex_Notations.
      Export Cong.Ex_Notations.
      Delimit Scope polym_once_scope with polym_once.
      Hint Constructors convCoMod.

      Notation "g2 <~> g1" := (@convCoMod _ _ g1 g2) : polym_once_scope.
    End Ex_Notations.

  End Once.

  Section Section1.
  Import Once.Ex_Notations.

  Inductive convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Prop :=

  | convCoMod_Refl : forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0),
      g <~> g

  | convCoMod_List : forall (B1 B2 : obCoMod) (uTrans g : 'CoMod(0 B1 ~> B2 )0),
      ( uTrans <~> g )%polym_once -> forall (g0 : 'CoMod(0 B1 ~> B2 )0),
        ( g0 <~> uTrans ) -> g0 <~> g

  | convCoMod_List_Sym : forall (B1 B2 : obCoMod) (uTrans g : 'CoMod(0 B1 ~> B2 )0),
      ( g <~> uTrans )%polym_once -> forall (g0 : 'CoMod(0 B1 ~> B2 )0),
        ( g0 <~> uTrans ) -> g0 <~> g

  where "g2 <~> g1" := (@convCoMod _ _ g1 g2).

  End Section1.
  
  Module Export Ex_Notations0.
    Export Once.Ex_Notations.
    Delimit Scope polym_scope with polym.
    Hint Constructors convCoMod.

    Notation "g2 <~> g1" := (@convCoMod _ _ g1 g2) : polym_scope.
  End Ex_Notations0.

  Module _Atom_Cong.

    Lemma CoMod_unit :
        forall (B B' : obCoMod) (f : 'CoMod(0 B ~> B' )0),
          ( ( f )
            <~> ( ( uCoMod ) o>CoMod f
                : 'CoMod(0 B ~> B' )0 ) ) %polym .
    Proof. eauto. Qed.

    Lemma CoMod_inputUnitCoMod :
        forall (B' B : obCoMod) (g : 'CoMod(0 B' ~> B )0),
          ( ( g )
              <~>  ( g o>CoMod ( uCoMod )
                   : 'CoMod(0 B' ~> B )0 ) )%polym .
    Proof. eauto. Qed.

    Lemma Project_1_morphism : forall B1 B2,
        forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0)
          B1'' (b1' : 'CoMod(0 B1' ~> B1'' )0),
          ( ( ~_1 @ B2 o>CoMod (b1 o>CoMod b1') )
              <~> ( ( ~_1 @ B2 o>CoMod b1 ) o>CoMod b1'
                  : 'CoMod(0 Limit B1 B2 ~> B1'' )0 ) )%polym .
    Proof. eauto. Qed.

    Lemma Project_2_morphism : forall B1 B2,
        forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0)
          B2'' (b2' : 'CoMod(0 B2' ~> B2'' )0),
          ( ( ~_2 @ B1 o>CoMod (b2 o>CoMod b2') )
              <~> ( ( ~_2 @ B1 o>CoMod b2 ) o>CoMod b2'
                  : 'CoMod(0 Limit B1 B2 ~> B2'' )0 ) )%polym .
    Proof. eauto. Qed.
      
    Lemma Limitator_morphism : forall B1 B2 M,
        forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0)
          M' (m : 'CoMod(0 M' ~> M )0),
          ( ( << m o>CoMod g_1 ,CoMod m o>CoMod g_2 >> )
              <~> ( m o>CoMod << g_1 ,CoMod g_2 >>
                  : 'CoMod(0 M' ~> Limit B1 B2 )0 ) )%polym .
    Proof. eauto. Qed.

    Lemma Limitator_Project_1 : forall B1 B2 M,
        forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
        forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0),
          ( ( g_1 o>CoMod b1 )
              <~> ( << g_1 ,CoMod g_2 >> o>CoMod ( ~_1 @ B2 o>CoMod b1)
                  : 'CoMod(0 M ~> B1' )0 ) )%polym .
    Proof. eauto. Qed.

    Lemma Limitator_Project_2 : forall B1 B2 M,
        forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
        forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0),
          ( ( g_2 o>CoMod b2 )
              <~> ( << g_1 ,CoMod g_2 >> o>CoMod ( ~_2 @ B1 o>CoMod b2)
                  : 'CoMod(0 M ~> B2' )0 ) )%polym .
    Proof. eauto. Qed.

    Lemma Limitator_Project_1_Project_2 : forall B1 B2,
          ( ( uCoMod )
              <~> ( << ~_1 @ B2 o>CoMod uCoMod ,CoMod ~_2 @ B1 o>CoMod uCoMod >>
                  : 'CoMod(0 Limit B1 B2 ~> Limit B1 B2 )0 ) )%polym .
    Proof. eauto. Qed.

    Lemma PolyCoMod_cong_Pre :
        forall (B B' : obCoMod) (g_ g_0 : 'CoMod(0 B ~> B' )0),
        forall (B'' : obCoMod) (g' : 'CoMod(0 B' ~> B'' )0),
          ( g_0 <~> g_ )%polym  -> ( ( g_0 o>CoMod g' ) <~> ( g_ o>CoMod g' ) )%polym .
    Proof.
      induction 1; [ | destruct X; [ destruct c | destruct c | idtac ] .. ]; eauto .
    Defined.

    Lemma PolyCoMod_cong_Post :
        forall (B B' : obCoMod) (g_ : 'CoMod(0 B ~> B' )0),
        forall (B'' : obCoMod) (g' g'0 : 'CoMod(0 B' ~> B'' )0),
          ( g'0 <~> g' )%polym -> ( ( g_ o>CoMod g'0 ) <~> ( g_ o>CoMod g' ) )%polym .
    Proof.
      induction 1; [ | destruct X; [ destruct c | destruct c | idtac ] .. ]; eauto .
    Defined.

    Lemma Project_1_cong : forall B1 B2,
        forall B1' (b1 b1' : 'CoMod(0 B1 ~> B1' )0),
          ( b1' <~> b1 )%polym -> ( ( ~_1 @ B2 o>CoMod b1' ) <~> ( ~_1 @ B2 o>CoMod b1 ) )%polym .
    Proof.
      induction 1; [ | destruct X; [ destruct c | destruct c | idtac ] .. ]; eauto .
    Defined.

    Lemma Project_2_cong : forall B1 B2,
        forall B2' (b2 b2' : 'CoMod(0 B2 ~> B2' )0),
          ( b2' <~> b2 )%polym -> ( ( ~_2 @ B1 o>CoMod b2' ) <~> ( ~_2 @ B1 o>CoMod b2 ) )%polym .
    Proof.
      induction 1; [ | destruct X; [ destruct c | destruct c | idtac ] .. ]; eauto .
    Defined.

    Lemma Limitator_cong_1 :  forall B1 B2 L,
        forall (g_1 g'_1 : 'CoMod(0 L ~> B1 )0) (g_2 : 'CoMod(0 L ~> B2 )0),
          (g'_1 <~> g_1)%polym ->
          ( ( << g'_1 ,CoMod g_2 >> ) <~> ( << g_1 ,CoMod g_2 >> ) )%polym .
    Proof.
      induction 1; [ | destruct X; [ destruct c | destruct c | idtac ] .. ]; eauto .
    Defined.

    Lemma Limitator_cong_2 : forall B1 B2 L,
        forall (g_1 : 'CoMod(0 L ~> B1 )0) (g_2 g'_2: 'CoMod(0 L ~> B2 )0),
          (g'_2 <~> g_2)%polym ->
          ( ( << g_1 ,CoMod g'_2 >> ) <~> ( << g_1 ,CoMod g_2 >> ) )%polym .
    Proof.
      induction 1; [ | destruct X; [ destruct c | destruct c | idtac ] .. ]; eauto .
    Defined.

    Module Export Ex_Notations0.

      Hint Resolve CoMod_unit CoMod_inputUnitCoMod
           Project_1_morphism Project_2_morphism Limitator_morphism
           Limitator_Project_1 Limitator_Project_2 Limitator_Project_1_Project_2.
      Hint Resolve PolyCoMod_cong_Pre PolyCoMod_cong_Post
           Project_1_cong Project_2_cong
           Limitator_cong_1 Limitator_cong_2 .

      Definition tac_Polymorphism := ( CoMod_unit , CoMod_inputUnitCoMod ,
                                     Project_1_morphism , Project_2_morphism , Limitator_morphism ,
                                     Limitator_Project_1 , Limitator_Project_2 , Limitator_Project_1_Project_2 ) .

    End Ex_Notations0.

    Lemma convCoMod_Trans :
      forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0) (Hrew1 : (g2 <~> g1)%polym ),
      forall g3 (Hrew2 : (g3 <~> g2)%polym ), (g3 <~> g1)%polym.
    Proof.
      induction 1; eauto.
    Defined.

    Section Section1.

      Hint Resolve convCoMod_Trans .

      Lemma convCoMod_Sym :
        forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0) (Hrew : (g2 <~> g1)%polym),
          (g1 <~> g2)%polym.
      Proof.
        induction 1; eauto. 
      Defined.

    End Section1.
    
    Module Export Ex_Notations.
      Export Ex_Notations0.
      Hint Resolve convCoMod_Sym convCoMod_Trans.

      Hint Rewrite CoMod_unit CoMod_inputUnitCoMod
           Project_1_morphism Project_2_morphism Limitator_morphism
           Limitator_Project_1 Limitator_Project_2 Limitator_Project_1_Project_2 .

      Add Parametric Relation (B1 B2 : obCoMod) : ('CoMod(0 B1 ~> B2 )0) (@convCoMod B1 B2)
          reflexivity proved by
          (@convCoMod_Refl B1 B2)
          symmetry proved by
          (fun x y => @convCoMod_Sym B1 B2 y x)
          transitivity proved by
          (fun x y z r1 r2 => (@convCoMod_Trans B1 B2 y x r1 z r2))
            as convCoMod_rewrite.

      Add Parametric Morphism B2 B1 B1' :
        (@PolyCoMod_rewrite B2 B1 B1' ) with
          signature ((@convCoMod B2 B1)
                       ==> (@convCoMod B1 B1')
                       ==> (@convCoMod B2 B1'))
            as PolyCoMod_cong_rewrite.
          by eauto. Qed.

      Add Parametric Morphism B1 B2 B1' :
        (@Project_1 B1 B2 B1') with
          signature ((@convCoMod B1 B1')
                       ==> (@convCoMod (Limit B1 B2) B1'))
            as Project_1_cong_rewrite.
          by move => *; apply: Project_1_cong. Qed.

      Add Parametric Morphism B1 B2 B2' :
        (@Project_2 B1 B2 B2') with
          signature ((@convCoMod B2 B2')
                       ==> (@convCoMod (Limit B1 B2) B2'))
            as Project_2_cong_rewrite.
          by move => *; apply: Project_2_cong. Qed.

      Add Parametric Morphism B1 B2 M :
        (@Limitator B1 B2 M) with
          signature ((@convCoMod M B1)
                       ==> (@convCoMod M B2)
                       ==> (@convCoMod M (Limit B1 B2)))
            as Limitator_cong_rewrite.
          by eauto. Qed.

    End Ex_Notations.

  End _Atom_Cong.

  Module Export Ex_Notations.
    Export Ex_Notations0.
    Export _Atom_Cong.Ex_Notations.
  End Ex_Notations.

  Lemma convCoMod_Rew_convCoMod_Polym :
    forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0),
      (g2 <~~ g1)%rew -> (g2 <~> g1)%polym.
  Proof.
    induction 1; eauto.
  Defined.

  Lemma Sol_convCoMod_Polymorphism_convCoMod_sol_once :
    forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0 %sol),
      ( g2 ~~~ g1 )%sol_once -> ( Sol.toCoMod g2 <~> Sol.toCoMod g1 )%polym.
  Proof.
    destruct 1;
      [ ( induction c; [destruct c | ..]; simpl in *; eauto;
          match goal with
          | [ IHconvCoMod1 : ( _ <~> _ )%polym |- _ ] =>
            rewrite IHconvCoMod1; clear IHconvCoMod1; try reflexivity
          | [ |- context[ ~_1 @ ?C o>CoMod << Sol.toCoMod ?b1_1 ,CoMod Sol.toCoMod ?b1_2 >> ] ] =>
            transitivity
              ( ( ~_1 @ C o>CoMod uCoMod )
                  o>CoMod << Sol.toCoMod b1_1 ,CoMod Sol.toCoMod b1_2 >> );
            [ rewrite !_Atom_Cong.Limitator_morphism | rewrite !_Atom_Cong.Project_1_morphism ];
            rewrite !tac_Polymorphism; reflexivity
          | [ |- context[ ~_2 @ ?C o>CoMod << Sol.toCoMod ?b2_1 ,CoMod Sol.toCoMod ?b2_2 >> ] ] =>
            transitivity
              ( ( ~_2 @ C o>CoMod uCoMod )
                  o>CoMod << Sol.toCoMod b2_1 ,CoMod Sol.toCoMod b2_2 >> );
            [ rewrite !_Atom_Cong.Limitator_morphism | rewrite !_Atom_Cong.Project_2_morphism ];
            rewrite !tac_Polymorphism; reflexivity
          end ) .. ].
  Qed.

  Lemma Sol_convCoMod_Polymorphism_convCoMod :
    forall (B1 B2 : obCoMod) (g2 g1 : 'CoMod(0 B1 ~> B2 )0 %sol),
      ( g2 ~~~ g1 )%sol_conv -> ( Sol.toCoMod g2 <~> Sol.toCoMod g1 )%polym.
  Proof.
    induction 1; first (by eauto);
      match goal with
      | [ Honce : ( _ ~~~ _ )%sol_once |- _ ] =>
        move: (Sol_convCoMod_Polymorphism_convCoMod_sol_once Honce)
      end; eauto.
  Qed. 
  
  Lemma Sol_convCoMod_Polymorphism_convCoMod' : forall (B1 B2 : obCoMod) (g _g : 'CoMod(0 B1 ~> B2 )0),
      ( Confluence.Resolve.solveCoMod g ~~~ Confluence.Resolve.solveCoMod _g )%sol_conv
      -> (g <~> _g)%polym .
  Proof.
    move => B1 B2 g _g /Sol_convCoMod_Polymorphism_convCoMod ;
             move : (Confluence.Resolve.solveCoModP1 g) => /convCoMod_Rew_convCoMod_Polym.
    move: (Confluence.Resolve.solveCoModP1 _g) => /convCoMod_Rew_convCoMod_Polym.
    intros; etransitivity; [ try eassumption .. ];
      etransitivity; [ try eassumption .. ];
        by symmetry; eassumption .
  Qed.

(**#+END_SRC

** Cut-elimination resolution is congruent from the polymorphism-terminology to the solution-terminology

Lemma [congruentSolution] shows that cut-elimination resolution is congruent from polymorphism-terminology to the solution-terminology ., The question of whether two morphisms are convertible in the polymorphism-terminology is equivalent/transferable as the question of whether their two polymorphism/cut-eliminated solution-morphisms are convertible in the solution-terminology .,

The polymorphism-terminology is more algebraic, while the solution-terminology is more combinatorial and therefore the solution-terminology is , in this case and most cases , (recursively-)decidable . 

+BEGIN_SRC coq :exports both :results silent **)

  Module _Confluence.

    Import Confluence.Resolve.Ex_Notations.

    Lemma congruentSolution_once_ : forall (B1 B2 : obCoMod) (g _g : 'CoMod(0 B1 ~> B2 )0),
      (g <~~ _g)%once ->
      forall g_rew : 'CoMod(0 B1 ~> B2 )0 %sol,
        ( Sol.toCoMod g_rew <~~ g )%rew ->
        forall _g_rew : 'CoMod(0 B1 ~> B2 )0 %sol,
          ( Sol.toCoMod _g_rew <~~ _g )%rew -> ( g_rew ~~~ _g_rew )%sol_conv.
    Proof.
      intros; eapply Confluence.uniqueSolution with (g := _g); eauto.
    Qed.

    Lemma congruentSolution_rew_ : forall (B1 B2 : obCoMod) (g _g : 'CoMod(0 B1 ~> B2 )0),
        (g <~~ _g)%rew ->
        forall g_rew : 'CoMod(0 B1 ~> B2 )0 %sol,
          ( Sol.toCoMod g_rew <~~ g )%rew ->
          forall _g_rew : 'CoMod(0 B1 ~> B2 )0 %sol,
            ( Sol.toCoMod _g_rew <~~ _g )%rew -> ( g_rew ~~~ _g_rew )%sol_conv.
    Proof.
      intros B1 B2 g _g Hrew g_rew Hrew'g _g_rew Hrew'_g.
      induction Hrew.
      - { eapply Confluence.uniqueSolution; eassumption. }
      - { move: (Confluence.Resolve.solveCoModP1 uTrans) => Hrew'uTrans .
          transitivity (Confluence.Resolve.solveCoMod uTrans).
          + eapply congruentSolution_once_ (*with (_g := g) (g := uTrans)*); eassumption.
          + eapply IHHrew; eassumption. }
    Qed.

    Lemma congruentSolution_once : forall (B1 B2 : obCoMod) (g _g : 'CoMod(0 B1 ~> B2 )0),
        (g <~~ _g)%once -> ( Confluence.Resolve.solveCoMod g ~~~ Confluence.Resolve.solveCoMod _g )%sol_conv.
    Proof.
      intros; apply: congruentSolution_once_;
        ( eassumption || apply: Confluence.Resolve.solveCoModP1 ).
    Qed.

    Lemma congruentSolution_rew : forall (B1 B2 : obCoMod) (g _g : 'CoMod(0 B1 ~> B2 )0),
        (g <~~ _g)%rew -> ( Confluence.Resolve.solveCoMod g ~~~ Confluence.Resolve.solveCoMod _g )%sol_conv.
    Proof.
      intros; apply: congruentSolution_rew_;
        ( eassumption || apply: Confluence.Resolve.solveCoModP1 ).
    Qed.

    Lemma congruentSolution : forall (B1 B2 : obCoMod) (g _g : 'CoMod(0 B1 ~> B2 )0),
        (g <~> _g)%polym -> ( Confluence.Resolve.solveCoMod g ~~~ Confluence.Resolve.solveCoMod _g )%sol_conv.
    Proof.
      induction 1; first (by eauto);
        [ ( match goal with
            | [ Hpolym_once : ( _ <~> _ )%polym_once |- _ ] => 
              etransitivity;
              [ (eassumption || clear -Hpolym_once) .. ];
              destruct Hpolym_once;
              first by (apply: congruentSolution_once; assumption)
                       || (symmetry; apply: congruentSolution_once; assumption)
            end;
            match goal with
            | [ Hcong : ( _ <~~ _ @ Cong.Limitator_Project_1_Project_2.convCoMod)%cong |- _ ] => 
              induction Hcong;
              first (by destruct c; rewrite -!tac_solveCoMod ;
                     ( apply: Sol._Atom_Cong.Limitator_Project_1_Project_2 )
                     || ( symmetry; apply: Sol._Atom_Cong.Limitator_Project_1_Project_2) );
              rewrite -!tac_solveCoMod ; eauto
            | [ Hcong : ( _ <~~ _ @ Cong.CoMod_morphism.convCoMod)%cong |- _ ] => 
              induction Hcong;
              first (by destruct c; rewrite -!tac_solveCoMod ;
                     (apply: Confluence.Resolve.solveCoMod_PolyCoMod_CoMod_morphism)
                     || (symmetry; apply: Confluence.Resolve.solveCoMod_PolyCoMod_CoMod_morphism) );
              rewrite -!tac_solveCoMod; eauto
            end ) .. ] .
    Qed.

    Lemma congruentSolution' : forall (B1 B2 : obCoMod) (g _g : 'CoMod(0 B1 ~> B2 )0),
        (g <~> _g)%polym <->
        ( Confluence.Resolve.solveCoMod g ~~~ Confluence.Resolve.solveCoMod _g )%sol_conv.
    Proof.
      split; first by apply: congruentSolution.
      apply: Sol_convCoMod_Polymorphism_convCoMod'.
    Qed.

  End _Confluence.
  
End Polymorphism.

End CONFLUENCE.

(**#+END_SRC

Voila. **)

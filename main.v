Set Warnings "-notation-overridden,-parsing".
Add LoadPath "~/Desktop/coq_imp/".
Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import List.
Import ListNotations.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Lemma XnotY : X <> Y.
Proof.
  apply eqb_string_false_iff. unfold eqb_string. reflexivity.
Qed.

Lemma YnotX : Y <> X.
Proof.
  apply eqb_string_false_iff. unfold eqb_string. reflexivity.
Qed.

Lemma ZnotY : Z <> Y.
Proof.
  apply eqb_string_false_iff. unfold eqb_string. reflexivity.
Qed.

Lemma ZnotX : Z <> X.
Proof.
  apply eqb_string_false_iff. unfold eqb_string. reflexivity.
Qed.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

Definition store := total_map nat. (**map from str to nat**)
Definition heap := partial_map_nat nat.  (**nat from str to nat**)
 

Fixpoint aeval (st : store) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : store) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).
Definition empty_h : heap := empty.

Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CFetch (x : string) (e : aexp)
  | CHeap (e : aexp) (x : aexp)
  | CAlloc (e : string) (l: list aexp)
  | CDisposal (e : aexp).

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.
Notation "x ':=' '*' e" :=
  (CFetch x e) (at level 60, right associativity) : imp_scope.
Notation "'*' e ':=' x" :=
  (CHeap e x) (at level 60, right associativity) : imp_scope.
Notation "e ':=CONS(' l ')' " :=
  (CAlloc e l) (at level 80, right associativity) : imp_scope.
Notation "'DISPOSE(' e ')'" :=
  (CDisposal e) (at level 60, right associativity) : imp_scope.

Reserved Notation "'[' st ',' h ',' res ']' '=[' c ']=>' '[' st' ',' h' ',' res' ']'"
(at level 61, c at level 60).

Inductive ceval : com -> store -> heap -> bool -> store -> heap -> bool -> Prop :=
  | E_Skip : forall st h res,
      [st, h, res] =[ SKIP ]=> [st, h, res]
  | E_Ass  : forall st a1 n x h res,
      aeval st a1 = n ->
      [st, h, res] =[ x ::= a1 ]=> [(x !-> n ; st), h, res]
  | E_Seq : forall c1 c2 st1 st2 st3 h1 h2 h3 res1 res2 res3,
      [st1, h1, res1] =[ c1 ]=> [st2, h2, res2] ->
      [st2, h2, res2] =[ c2 ]=> [st3, h3, res3] ->
      [st1, h1, res1] =[ c1 ;; c2 ]=> [st3, h3, res2 && res3]
  | E_IfTrue : forall st1 st2 b c1 c2 h1 h2 res1 res2,
      beval st1 b = true ->
      [st1, h1, res1] =[ c1 ]=> [st2, h2, res2] ->
      [st1, h1, res1] =[ TEST b THEN c1 ELSE c2 FI ]=> [st2, h2, res2]
  | E_IfFalse : forall st1 st2 b c1 c2 h1 h2 res1 res2,
      beval st1 b = false ->
      [st1, h1, res1] =[ c2 ]=> [st2, h2, res2] ->
      [st1, h1, res1] =[ TEST b THEN c1 ELSE c2 FI ]=> [st2, h2, res2]
  | E_WhileFalse : forall b st c h res,
      beval st b = false ->
      [st, h, res] =[ WHILE b DO c END ]=> [st, h, res]
  | E_WhileTrue : forall st1 st2 st3 h1 h2 h3 res1 res2 res3 b c,
      beval st1 b = true ->
      [st1, h1, res1] =[ c ]=> [st2, h2, res2] ->
      [st2, h2, res2] =[ WHILE b DO c END ]=> [st3, h3, res3] ->
      [st1, h1, res1] =[ WHILE b DO c END ]=> [st3, h3, res2 && res3]
  | E_Fetch : forall st h res x e n,
      (h (aeval st e) = Some n) ->
      [st, h, res] =[ x := *e ]=> [(x !-> n ; st), h, res]
  | E_FetchFail : forall st h res st1 h1 x e,
      (h (aeval st e) = None) ->
      [st, h, res] =[ x := *e ]=> [st1, h1, false]
  | E_Heap : forall st h res x e,
      ~(h (aeval st e) = None) ->
      [st, h, res] =[ *e := x ]=> [st, (aeval st e |-> aeval st x; h), res]
  | E_HeapFail : forall st h res st1 h1 x e,
      (h (aeval st e) = None) ->
      [st, h, res] =[ *e := x ]=> [st1, h1, false]
  | E_Disposal : forall st h res e n,
      ~(h (aeval st e) = None) ->
      (aeval st e = n) ->
      [st, h, res] =[ DISPOSE( e ) ]=> [st, (n !!-> None ; h), res]
  | E_DisposalFail : forall st h st1 h1 res e,
      (h (aeval st e) = None) ->
      [st, h, res] =[ DISPOSE( e ) ]=> [st1, h1, false]
  | E_AllocSingle : forall st h res e n pointer,
      (h pointer = None) ->
      [st, h, res] =[ e :=CONS(cons n nil) ]=> [(e !-> pointer ; st), (pointer |-> (aeval st n) ; h), res]
  | E_AllocFew : forall st1 h1 res st2 h2 e n l,
      [st1, h1, res] =[ e :=CONS(l) ]=> [st2, h2, res] ->
      (h2 ((st2 e) - 1) = None) ->
      [st1, h1, res] =[ e :=CONS(n :: l) ]=> [(e !-> (st2 e - 1); st2), ((st2 e - 1) |-> (aeval st2 n) ; h2), res]

where "'[' st ',' h ',' res ']' '=[' c ']=>' '[' st' ',' h' ',' res' ']'" := (ceval c st h res st' h' res').

Tactic Notation "T_Seq" := eapply E_Seq with (res2:=true) (res3:=true).

Example stack_easy_example:
  [empty_st, empty_h, true] =[
    X ::= 0;; Y ::= 1
  ]=> [(Y !-> 1 ; X !-> 0), empty_h, true].
Proof.
  T_Seq.
  apply E_Ass. simpl. exists. apply E_Ass. reflexivity.
Qed.

Definition lnum (n : nat) : list aexp := cons (ANum n) nil.

Example heap_easy_example:
  [empty_st, (0 |-> 179 ; 1 |-> 0), true] =[
    X :=CONS( (lnum 5) ++ (lnum 6) ) ;; 
    DISPOSE(X + 1)
  ]=> [(X !-> 42), (42 |-> 5; 0 |-> 179; 1 |-> 0 ), true].
Proof. 
  T_Seq.
  eapply E_AllocFew. eapply E_AllocSingle with (pointer:=43). 
  apply update_neq. omega.
  simpl. apply update_neq. omega.
  simpl. 
  rewrite add_none with (n:=43) (m:= 6) (h:=(42 |-> 5; 0 |-> 179; 1 |-> 0)).
  rewrite add_swap with (n:=42) (m:=43).
  assert(H: (X !-> 42; X !-> 43) = (X !-> 42) ).
  { apply t_update_shadow. }
  rewrite H.
  apply E_Disposal. simpl. rewrite t_update_eq_nat. intros contra. inversion contra.
  reflexivity. omega. apply update_neq. omega.
Qed.
  
Theorem IsCrashFromCrash: forall c st1 h1 st2 h2 res2,
  [st1, h1, false] =[ c ]=> [st2, h2, res2] -> res2 = false.
Proof.
  intros c.
  induction c; intros st1 h1 st2 h2 res2 H; inversion H; subst; repeat(reflexivity).
  - apply IHc1 in H2. rewrite H2. reflexivity.
  - apply IHc1 in H10. rewrite H10. reflexivity.
  - apply IHc2 in H10. rewrite H10. reflexivity.
  - apply IHc in H3. rewrite H3. reflexivity.
Qed.

Definition Assertion := store -> heap -> bool -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st h res, P st h res -> Q st h res.

Notation "P ->> Q" := (assert_implies P Q) (at level 80).
Notation "P <<->> Q" := (P ->> Q /\ Q ->> P) (at level 80).

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st h res st' h' res',
     [st, h, res] =[ c ]=> [st', h', res'] ->
     P st h res ->
     Q st' h' res'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level).

Theorem SwapCorrect:
  forall x y m n,
  {{(fun st h res => h x = Some n /\ h y = Some m /\ res = true)}}
  (X := *x ;; Y := *y ;; *x := Y ;; *y := X)
  {{(fun st h res => h x = Some m /\ h y = Some n /\ res = true)}}.
Proof.
  unfold hoare_triple. intros *. intros H [G1 [G2 G3]].
  inversion H; subst. clear H. 
  inversion H2; subst. clear H2.
  inversion H9; subst. clear H9.
  inversion H1; subst. clear H1.
  inversion H10; subst. clear H10.
  inversion H1; subst. clear H1.
  inversion H11; subst. clear H11.
  simpl. repeat(rewrite t_update_eq).
  assert (L: (Y !-> n1; X !-> n0; st) X = n0).
  { rewrite t_update_neq. apply t_update_eq. apply YnotX. }
  repeat(rewrite L). rewrite update_eq. simpl in H8. simpl in H9.
  destruct (y =? x) eqn:E. 
  - apply beq_nat_true in E. rewrite E in *. rewrite update_eq. 
    rewrite<-G1. rewrite<-G2. rewrite H8. 
    split; try(split); reflexivity.
  - apply beq_nat_false in E. rewrite update_neq. rewrite update_eq.
    rewrite<-G1. rewrite<-G2. rewrite H8. rewrite H9.
    split; try(split); reflexivity. assumption.
  - simpl in H7. simpl in H9. destruct (x =? y) eqn:E.
    + apply beq_nat_true in E. rewrite E in *. 
      rewrite update_eq in H7. inversion H7.
    + apply beq_nat_false in E. eapply update_neq in E. 
      rewrite E in H7. rewrite H9 in H7. inversion H7.
  - simpl in H8. simpl in H10. rewrite H8 in H10. inversion H10.
  - simpl in H9. rewrite G2 in H9. inversion H9.
  - simpl in H8. rewrite G1 in H8. inversion H8.
Qed.

(**stack hoare rules**)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st h res, Q st h res) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st h res st' h' re' Heval HP.
  apply (H st' h' re').  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st h res, ~ (P st h res)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st h res st' h' res' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : store) (h : heap) (res : bool) =>
    P (X !-> aeval st a ; st) h res.

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X ::= a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st h res st' h' res' HE HQ.
  inversion HE; subst;
  unfold assn_sub in HQ. apply HQ. Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st h res st' h' res' Hc HP. apply (Hhoare st h res st' h' res').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st h res st' h' res' Hc HP.
  apply Himp.
  apply (Hhoare st h res st' h' res').
  assumption. assumption. Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st h res st' h' res' H HP. inversion H. subst.
  assumption.  Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st h res st' h' res' H12 Pre.
  inversion H12; subst.
  destruct (res2) eqn:E.
  - simpl. apply (H1 st2 h2 true st' h' res3); try assumption.
    apply (H2 st h res st2 h2 true); assumption.
  - assert (H : res3 = false).
    { apply IsCrashFromCrash in H10. assumption. } 
    simpl. rewrite H in H10.
    apply (H1 st2 h2 false st' h' false); try assumption.
    apply (H2 st h res st2 h2 false); try assumption.
Qed.

Definition bassn b : Assertion :=
  fun st h res => (beval st b = true).

Lemma bexp_eval_true : forall b st h res,
  beval st b = true -> (bassn b) st h res.
Proof.
  intros b st h res Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st h res,
  beval st b = false -> ~ ((bassn b) st h res).
Proof.
  intros b st h res Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st h res => P st h res /\ bassn b st h res}} c1 {{Q}} ->
  {{fun st h res => P st h res /\ ~ (bassn b st h res)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st h res st' h' res' HE HP.
  inversion HE; subst.
  - apply (HTrue st h res st' h' res').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - apply (HFalse st h res st' h' res').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. 
Qed.

Theorem hoare_while : forall P b c,
  {{fun st h res => P st h res /\ bassn b st h res}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st h res => P st h res /\ ~ (bassn b st h res)}}.
Proof.
  intros P b c Hhoare st h res st' h' res' He HP.
  remember (WHILE b DO c END)%imp as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - split. assumption. apply bexp_eval_false. assumption.
  - destruct (res2) eqn:E.
    + simpl. apply IHHe2. reflexivity.
      apply (Hhoare st1 h1 res1 st2 h2 true). assumption.
      split. assumption. apply bexp_eval_true. assumption.
    + assert (T: res3 = false).
      { apply IsCrashFromCrash in He2. assumption. } 
      simpl. rewrite T in IHHe2. apply IHHe2. reflexivity.
      apply (Hhoare st1 h1 res1 st2 h2 false). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(**end stack hoare rules**)

Inductive max_list : nat -> nat -> list nat -> Prop :=
| empty_pref (l : list nat) : max_list 0 0 l
| empty_list (i : nat) : max_list 0 i [ ]
| head_max_list (n i: nat) (l : list nat)
                (H1 : max_list n i l) (H2 : n < (nth i l 0)) : max_list (nth i l 0) (S i) l  
| head_min_list (n i: nat) (l : list nat)
                (H1 : max_list n i l) (H2 : (nth i l 0) <= n) : max_list n (S i) l.

Theorem max_list_ex : max_list 5 6 [1;3;2;5;4;4].
Proof.
  apply head_min_list; try apply head_min_list;
  try apply (head_max_list 3 3 [1; 3; 2; 5; 4; 4]);
  try apply head_min_list; try apply (head_max_list 1 1 [1; 3; 2; 5; 4; 4]);
  try apply (head_max_list 0 0 [1; 3; 2; 5; 4; 4]);
  try apply empty_pref; simpl; omega.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ~P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Fixpoint len (l : list nat) : nat :=
  match l with
  | nil => O
  | h :: t => S(len t)
  end.

Theorem GetMaxCorrect:
  forall l,
  {{(fun st h res => (forall (i: nat), i < len l -> (h i = Some (nth i l 0)) ) /\ res = true)}}
  ( X ::= 0;; 
    Y ::= 0;;
    WHILE ~(Y = len l) DO 
      Z := *Y;;
      TEST Z <= X 
        THEN SKIP
        ELSE X ::= Z
      FI;;
      Y ::= Y + 1
    END)
  {{(fun st h res => max_list (st X) (len l) l /\ res = true)}}.
Proof.
  intros l.
  eapply hoare_seq. Focus 2.
  apply hoare_consequence_pre with ((fun (st : store) (h : heap) (res : bool) =>
                               (forall (i: nat), i < len l -> (h i = Some (nth i l 0)) ) /\
                                res = true /\ st X = 0)[X |-> 0]). 
  apply hoare_asgn.
  intros st h res [H1 H2]. 
  unfold assn_sub, t_update. split; try split; try assumption; try reflexivity.

  eapply hoare_seq. Focus 2.
  apply hoare_consequence_pre with ((fun (st : store) (h : heap) (res : bool) =>
                               (forall (i: nat), i < len l -> (h i = Some (nth i l 0)) ) /\
                                res = true /\ st X = 0 /\ st Y = 0)[Y |-> 0]). 
  apply hoare_asgn.
  intros st h res [H1 [H2 H3]]. 
  unfold assn_sub, t_update, eqb_string. simpl. split; try split; try split; 
                                            try assumption; try reflexivity.
  
  apply hoare_consequence_pre with ((fun (st : store) (h : heap) (res : bool) =>
                              (forall (i: nat), i < len l -> (h i = Some (nth i l 0)) ) /\
                                 res = true /\ max_list (st X) (st Y) l /\ (st Y <= len l))).
  eapply hoare_consequence_post.
  apply hoare_while.
  apply hoare_consequence_pre with ((fun (st : store) (h : heap) (res : bool) =>
                               (forall (i: nat), i < len l -> (h i = Some (nth i l 0)) ) /\
                                 res = true /\ max_list (st X) (st Y) l /\ 
                               (st Y) <= len l /\ bassn (~ Y = len l) st h res)).
  apply hoare_seq with (fun (st : store) (h : heap) (res : bool) =>
                              (forall (i: nat), i < len l -> (h i = Some (nth i l 0)) ) /\
                               res = true /\ max_list (st X) (st Y) l /\ (st Y <= len l) /\ 
                               bassn (~ Y = len l) st h res /\ st Z = (nth (st Y) l 0)).
  eapply hoare_seq.
  apply hoare_asgn.
  apply hoare_if.
  eapply hoare_consequence_post.
  apply hoare_skip.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
  intros *. intros [[H1 [H2 [H3 [H4 [H5 H6]]]]] H7]. repeat(split).
  apply H1.
  apply H2.
     rewrite add_1_r. apply head_min_list. apply H3. rewrite H6 in H7. 
     apply leb_le in H7. apply H7.
     apply negb_true_iff in H5. apply eqb_neq in H5. rewrite add_1_r. 
     apply lt_le_S. apply le_neq. split; assumption.

  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
  intros *. intros [[H1 [H2 [H3 [H4 [H7 H5]]]]] H6]. repeat(split).
  apply H1.
  apply H2.
    rewrite add_1_r. rewrite H5. apply head_max_list with (n:=(st X)). apply H3.
    rewrite H5 in H6. apply not_true_is_false in H6. apply leb_iff_conv in H6.
    apply H6.
    apply negb_true_iff in H7. apply eqb_neq in H7. rewrite add_1_r. 
    apply lt_le_S. apply le_neq. split; assumption.
  
  Focus 3.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
  intros *. intros [[H1 [H2 [H3 H4]]] H6]; repeat(split); try assumption.
  apply eq_true_negb_classical in H6. apply eqb_eq in H6.
  rewrite H6 in H3. assumption.

  Focus 2.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
  intros *. intros [[H1 [H2 [H3 H4]]] H5]. repeat split; try assumption.
  
  Focus 2.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
  intros *. intros [H1 [H2 [H3 H4]]].
  rewrite H3. rewrite H4. repeat split; try assumption.
  apply empty_pref. omega.

  unfold hoare_triple.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
  intros *. intros H [H1 [H2 [H3 [H4 H5]]]]. repeat(split); inversion H; subst;
    try(apply negb_true_iff in H5; apply eqb_neq in H5;
        assert(G : st Y <= len l /\ st Y <> len l) );
    try(split; assumption);
    try(apply le_neq in G; apply H1 in G; simpl in H13; 
        rewrite H13 in G; inversion G).
  - apply H1.
  - rewrite t_update_neq. rewrite t_update_neq. assumption. 
    apply ZnotY. apply ZnotX.
  - rewrite t_update_neq. apply H4. apply ZnotY.
  - rewrite t_update_neq. apply negb_true_iff. apply eqb_neq. apply H5. apply ZnotY.
  - rewrite t_update_eq. rewrite t_update_neq. simpl in H13.
    inversion G. reflexivity. apply ZnotY.
Qed.

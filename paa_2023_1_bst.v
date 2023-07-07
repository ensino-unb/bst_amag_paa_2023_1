(** Projeto e Análise de Algoritmos - 2023-1 *)

(** * Árvores binárias de busca - material adaptado de https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html *)

(**

 - Leitura recomendada: capítulo 12 _Introduction to Algorithms, 3rd Edition_, Cormen, Leiserson, and Rivest, MIT Press 2009.

 *)

From Coq Require Import String.
From Coq Require Export Arith.
From Coq Require Export Lia.

Notation  "a >=? b" := (Nat.leb b a) (at level 70) : nat_scope.
Notation  "a >? b"  := (Nat.ltb b a) (at level 70) : nat_scope.

Ltac inv H := inversion H; clear H; subst.

Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT :   P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H; split.
  - intro H'.
    inv H.
    + reflexivity.
    + contradiction.
  - intro H'; subst.
    inv H; assumption.
Qed.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

(** Utilizaremos números naturais para representar as chaves em cada nó de nossas árvores binárias de busca porque os naturais possuem uma ordem total [<=?] com diversos teoremas já provados. *)

Definition key := nat.

(** Adicionalmente, os nós armazenarão pares chave/valor, onde o valor associado a uma chave terá um tipo [V] qualquer. Definiremos indutivamente a estrutura [tree] para representar árvores binárias cujos nós contêm uma chave [k] e um valor [v]. As árvores possuem dois construtores, [E] que representa a árvore vazia, e [T] que recebe os seguintes argumentos: 

- [l]: a subárvore à esquerda do nó atual;
- [k]: a chave ligada ao nó atual;
- [v]: o valor associado à chave [k], e;
- [r]: a subárvore à direita do nó atual.

Nesta construção, cada chave se liga a apenas um valor. *)

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).

Arguments E {V}.
Arguments T {V}.

(** Exemplo: A árvore binária abaixo contém valores do tipo [string]
<<
      4 -> "four"
      /        \
     /          \
  2 -> "two"   5 -> "five"
>>

e é representada da seguinte forma: *)

Definition ex_tree : tree string :=
  (T (T E 2 "two" E) 4 "four" (T E 5 "five" E))%string.

(** A árvore vazia [empty_tree] não contém chaves: *)

Definition empty_tree {V : Type} : tree V := E. 

(** Uma árvore binária de busca é caracterizada pela seguinte invariante: dado qualquer nó não-vazio com chave [k], todas as chaves da subárvore à esquerda são menores do que [k], e todas as chaves da subárvore à direita são maiores do que [k]. Formalizaremos esta invariante com a ajuda da função [ForallT]: *)

Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V) : Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

(** Esta função expressa as condições para que uma árvore satisfaça uma dada propriedade [P]: Se a árvore for vazia então a propriedade é satisfeita por vacuidade, e portanto retorna [True]. Quando a árvore não é vazia, e portanto tem a forma [T l k v r], então precisamos que o nó que tem chave [k] e valor [v] satisfaça a propriedade [P], assim como as subárvores à esquerda e à direita. A invariante citada acima é formalizada por meio da propriedade [BST]: *)

Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => y > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).

(** Esta propriedade é composta de dois construtores:

    - O primeiro construtor, denotado por [BST_E], consiste em um axioma que estabelece que uma árvore vazia é uma árvore binária de busca.

    - O segundo construtor, denotado por [BST_T], consiste na regra que diz que para que uma árvore não vazia [T l x v r] seja uma árvore binária de busca é necessário que todas as chaves da subárvore à esquerda sejam menores do que [x], todas a chaves da subárvore à direita sejam maiores do que [x], e que as subárvores à esquerda e à direita sejam também árvores binárias de busca. *)

Hint Constructors BST.

(** A primeira operação importante relacionada às árvores binárias de busca é certamente a busca que pode ser implementada de forma muito eficiente. Por exemplo, a função [bound k t] retorna [true] quando [k] é uma chave de [t], e [false] caso contrário. *)

Fixpoint bound {V : Type} (x : key) (t : tree V) :=
  match t with
  | E => false
  | T l y v r => if x <? y then bound x l
                else if x >? y then bound x r
                     else true
  end.

(** Analogamente, a função [lookup d k t] retorna o valor ligado à chave [k] em [t], ou retorna o valor _default_ [d] quando [k] não é uma chave de [t]. *)

Fixpoint lookup {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | E => d
  | T l y v r => if x <? y then lookup d x l
                else if x >? y then lookup d x r
                     else v
  end.

(** Observe que se [t] não é uma árvore binária de busca então as funções [bound] e [lookup] podem retornar respostas erradas: *)

Module NotBst.
  Open Scope string_scope.

  (** De fato, considere a seguinte árvore que não é uma árvore binária de busca: *)
  
  Definition t : tree string :=
    T (T E 5 "five" E) 4 "four" (T E 2 "two" E).

  (** Ela possui uma ocorrência da chave 2, mas em uma posição não esperada pelas funções [bound] e [lookup]: *)
  
  Example not_bst_bound_wrong :
    bound 2 t = false.
  Proof.
    reflexivity.
  Qed.

  Example not_bst_lookup_wrong :
    lookup "" 2 t <> "two".
  Proof.
    simpl. unfold not. intros contra. discriminate.
  Qed.
End NotBst.

(** A segunda operação fundamental de árvores binárias de busca que estudaremos neste trabalho é a inserção. A função [insert k v t] insere a chave [k] com o valor [v] na árvore binária de busca [t], de forma a preservar a invariante de uma árvore binária de busca. *)

Fixpoint insert {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if x <? y then T (insert x v l) y v' r
                 else if x >? y then T l y v' (insert x v r)
                      else T l x v r
  end.

(** Nossa primeira tarefa será mostrar que a função [insert] de fato preserva a invariante citada acima. Inicialmente, observe que o predicado [BST] classifica corretamente alguns exemplos: *)

Example is_BST_ex :
  BST ex_tree.
Proof.
  unfold ex_tree.
  repeat (constructor; try lia).
Qed.

Example not_BST_ex :
  ~ BST NotBst.t.
Proof.
  unfold NotBst.t. intros contra.
  inv contra. inv H3. lia.
Qed.


(** A seguir, prove que a função [insert] produz uma árvore binária de busca, mas antes prove que a função [insert] preserva qualquer propriedade dos nós: *)

Lemma ForallT_insert : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t -> forall (k : key) (v : V),
      P k v -> ForallT P (insert k v t).
Proof.
  induction t.
  - intros H k v HP. simpl. auto.
  - intros H k' v' HP. simpl. bdestruct (k >? k').
    + simpl. split.
      * inv H. assumption.
      * split.
        ** apply IHt1.
           *** inv H. apply H2.
           *** assumption.
        ** inv H. apply H2.
    + bdestruct (k' >? k).
      * simpl. split.
        ** inv H. assumption.
        ** split.
           *** inv H. apply H3.
           *** apply IHt2.
               **** inv H. apply H3.
               **** assumption.
      * simpl. split.
        ** assumption.
        ** split; inv H; apply H3.
Qed.

(*André*) Lemma total_bst_sub_bst : forall (V : Type) (k : key) (v : V) (l r : tree V), BST (T l k v r) -> BST l /\ BST r.
(*André*) Proof.
(*André*)   intros. inversion H. split. assumption. assumption.
(*André*) Admitted.

(** Prove que ao receber uma árvore binária de busca como argumento, a função [insert] gera outra árvore binária de busca. *)

Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> BST (insert k v t).
Proof.
(*André*)  intros. induction t.
(*André*)   - simpl. apply BST_T.
(*André*)     * simpl. lia.
(*André*)     * simpl. lia.
(*André*)     * assumption.
(*André*)     * assumption.
(*André*)   - apply total_bst_sub_bst in H. destruct H as (H1, H2).
              simpl. destruct (k0 >? k) eqn:H'.
              * apply BST_T.
                 ** induction t1.
                  *** simpl. split. apply Nat.ltb_lt in H'. apply H'. lia.
                  *** simpl. destruct (k1 >? k) eqn:H''.
                      apply IHt1 in H1. replace (T (insert k v t1_1) k1 v1 t1_2) with (insert k v (T t1_1 k1 v1 t1_2)).
                      **** admit.
                      **** simpl. destruct (k1 >? k) eqn:H'''.
                          ***** reflexivity.
                          ***** discriminate.
                      **** destruct (k >? k1) eqn:H''''.
                          ***** simpl. apply Nat.ltb_ge in H''. apply Nat.ltb_lt in H'''', H'. split. 
                                ****** lia. 
                                ****** split.
                                       ******* inversion H1. rewrite H' in H''''. Preciso juntar H5 com H''''.
                              replace (y < k0) with (y < k1).


                              apply total_bst_sub_bst in H1. destruct H1 as (H3, H4). split.
                                      ******* 
  Search " >? ".

Nat.ltb_ge: forall x y : nat, (y >? x) = false <-> y <= x
Nat.ltb_lt:
                 ** admit.
                 ** apply IHt1. apply H1.
                 ** apply H2.
              * destruct (k >? k0) eqn:H''.
                 ** apply BST_T.
                    *** admit.
                    *** admit.
                    *** apply H1.
                    *** apply IHt2. apply H2.
                 ** apply BST_T.
                    *** admit.
                    *** admit.
                    *** apply H1.
                    *** apply H2.
(*André all of the above*)


Admitted.

(** * A correção das funções de busca [lookup] e [bound] *)

(** Qual o comportamento esperado para as funções [lookup] e [bound]? Ao procurarmos uma chave na árvore binária de busca vazia com a função [lookup], devemos obter o valor default [d]: *)

Theorem lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k empty_tree = d.
Proof.
  auto.
Qed.

(** Se inserirmos a chave [k] e valor [v] na árvore binária de busca [t], então a busca em [insert k v t] com a função [lookup] retorna [v]: *)

Theorem lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V), lookup d k (insert k v t) = v.
Proof.
  induction t; intros; simpl.
  - bdestruct (k <? k); try lia;auto.
  - bdestruct (k <? k0); bdestruct (k0 <? k); simpl; try lia; auto.
    + bdestruct (k <? k0); bdestruct (k0 <? k); try lia; auto.
    + bdestruct (k <? k0); bdestruct (k0 <? k); try lia; auto.
    + bdestruct (k0 <? k0); try lia; auto.
Qed.

(** A tática [bdall] a seguir, simplifica esta prova evitando os passos repetitivos *)
Ltac bdestruct_guard :=
  match goal with
  | |- context [ if ?X =? ?Y then _ else _ ] => bdestruct (X =? Y)
  | |- context [ if ?X <=? ?Y then _ else _ ] => bdestruct (X <=? Y)
  | |- context [ if ?X <? ?Y then _ else _ ] => bdestruct (X <? Y)
  end.

Ltac bdall :=
  repeat (simpl; bdestruct_guard; try lia; auto).

Theorem lookup_insert_eq' :
  forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v.
Proof.
  induction t; intros; bdall.
Qed.

(** Prove que a busca de uma chave [k'], via a função [lookup], na árvore binária de busca [insert k v t], com [k] e [k'] distintos, retorna o resultado de buscar [k'] em [t]:  *)

Theorem lookup_insert_neq :
  forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
   k <> k' -> lookup d k' (insert k v t) = lookup d k' t.
Proof.
Admitted.
  
(** Enuncie e prove os três teoremas análogos para a função [bound]. *)

(** A relação esperada entre as funções [bound] e [lookup] é que, se [bound k t] retorna [false] então [lookup d k t] retorna o valor default [d]. Prove este fato dado pelo seguinte teorema: *)

Theorem bound_default :
  forall (V : Type) (k : key) (d : V) (t : tree V),
    bound k t = false ->
    lookup d k t = d.
Proof.
  Admitted.    


(** Função de remoção de um elemento. *)

Fixpoint find_max {V:Type} (t : tree V) :=
  match t with
  | E => 0
  | T l x v r => match r with
                 | E => x
                 | T r1 x' v' r2 => find_max r
                 end
  end.

Eval compute in (find_max ex_tree).

Definition ex_tree2 : tree string :=
  (T (T (T E 1 "two" E) 2 "two" (T E 3 "two" E)) 4 "four" (T E 5 "five" E))%string.

Eval compute in (find_max ex_tree2).



Fixpoint remove {V: Type} x (t: tree V) :=
  match t with
  | E => E
  | T l y v r => if (x <? y) then T (remove x l) y v r
                 else if (x >? y) then T l y v (remove x r)
                      else match l with
    | E => r
    | T l1 xl vl l2 => match r with
                     | E => l
                       | T r1 xr vr r2 => let max := find_max l in
                                          T (remove max l) max vl r
                       end
                           end
  end.

Eval compute in (remove 4 ex_tree).
Eval compute in (remove 2 ex_tree).
Eval compute in (remove 5 ex_tree).
Eval compute in (remove 7 ex_tree).

Lemma ForallT_remove : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t -> forall (k : key) (v : V),
      P k v -> ForallT P (remove k t).
Proof.
Admitted.
  
Theorem remove_bst: forall {V: Type} (t: tree V) x, BST t -> BST (remove x t).
Proof.
  induction t.
  - intros x H. simpl. assumption.    
  - intros x H. simpl. inv H.
    destruct (k >? x) eqn:H'.
    + constructor.
      * apply ForallT_remove.
        ** assumption.
        ** auto.
        ** apply Nat.ltb_lt. assumption.
      * assumption.
      * apply IHt1. assumption.
      * apply H7.
    + destruct (x >? k) eqn:H''.
      * constructor.
        ** assumption.
        ** apply ForallT_remove.
           *** assumption.
           *** auto.
           *** apply Nat.ltb_lt. assumption.
        ** assumption.
        ** apply IHt2. assumption.
      * destruct t1.
        ** assumption.
        ** destruct t2.
           *** assumption.
           *** Admitted.
  
Fixpoint remove_folha {V: Type} x (t : tree V) := match t with
                             | E => t
                             | T E k v' E => if (k =? x) then E else t
                             | T l k v' r => if x <? k then T (remove_folha x l) k v' r
                                            else if x >? k then T l k v' (remove_folha x r)
                                                 else t
                             end.

Lemma ForallT_remove_folha : forall (V : Type) (P : key -> V -> Prop) (t : tree V) x,
    ForallT P t -> ForallT P (remove_folha x t).
Proof.
Admitted.
  
Theorem remove_folha_bst: forall {V: Type} (t: tree V) x, BST t -> BST (remove_folha x t).
Proof.
  induction t.
  - intros x H. simpl. auto.
  - intros x H. simpl. destruct t1.
    + destruct t2.
      * destruct (k =? x).
        ** constructor.
        ** assumption.
      * destruct (k >? x).
        ** simpl. assumption.
        ** destruct (x >? k).
           *** apply BST_T.
               **** simpl. auto.
               **** inv H. apply ForallT_remove_folha. assumption.
               **** auto.
               **** Admitted.


  
remove x t := match t with
              | E => E
              | T l k v r => if x <? k then T (remove x l) k v r
                 else if x >? k then T l k v (remove x r)
                      else ?? T l x v r
                              
Theorem remove_bst: forall t x, BST t -> BST (remove x t)

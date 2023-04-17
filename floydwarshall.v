
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
Require Export Coq.Vectors.Fin.
Require Export Coq.ZArith.ZArith.
From Coq Require Import Lia.




Notation "'node'" := (t).
Check node 3.
Check @F1 2. (*  0 in t 3  *)
Check FS (@F1 1). (* 1 in t 3  *)
Check FS( FS (@F1 0)). (* 2 in t 3  *)


(*

We can use type forall n : nat,node n to repersent a n-vertix set.

node 3 denote a set which contains 3 element {1,2,3}

1 -- @F1 2,  2 -- FS (@F1 1), 3 -- FS( FS (@F1 0))

*)

Fixpoint NodeLst (n:nat):list (node n):=
(* 
 NodeLst n can return a list which contains all 
 element in node n.  
*)
match n with
| O => nil
| S O =>  [@F1 0]
| S (S n') => @F1 (S n')
      :: map FS ((@F1  n') ::(map FS (NodeLst  n')))
end.


Compute NodeLst O.
Compute NodeLst 1.
Compute NodeLst 2.
Compute NodeLst 3.




Open Scope Z_scope.

Inductive optionZ := inf | Some (z :Z).
Check Some 5.
Check inf.
Definition oZadd (n m:optionZ) : optionZ :=
  match n,m with
  | inf,_ => inf
  | _,inf => inf
  | Some n',Some m' => Some (n'+m')
end.
Notation "x + y" := (oZadd x y) : optionZ_scope.
Open Scope optionZ_scope.

Compute  inf + (Some (-100000000000)).
Compute  inf + (Some 100000000000).
Compute  (Some 10) + (Some 10).


Definition oZleb (n m:optionZ) : bool :=
  match n,m with
  | _,inf => true
  | inf,_ => false
  | Some n',Some m' => n' <=? m'
end.
Notation "x <=? y" := (oZleb x y) (at level 70) : optionZ_scope.

Compute inf <=? inf.
Compute  Some 0  <=?  Some 0 .
Compute Some (-1) <=? Some 1.
Compute Some 1 <=? Some (-1).


Inductive oZle : optionZ -> optionZ -> Prop :=
  | oZle_1inf (n:optionZ) : oZle n inf
  | oZle_nm (n m:Z): n <= m -> oZle (Some n) (Some m).
Notation "n <= m" := (oZle n m).

Example oZle1: Some 5 <= inf.
Proof. apply oZle_1inf. Qed.


Definition oZmin (x y : optionZ) : optionZ:=
  if x <=? y then x else y.
  
Compute oZmin (Some (-1))(Some (-2)).




Open Scope optionZ_scope.
Theorem oZleb_reflect : forall (x y:optionZ), reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. 
  split. 
  +  intro E. destruct E.
    - destruct n.
      * reflexivity .
      * reflexivity .
    - simpl. apply Z.leb_le. assumption.
  + 
    - intro E.  destruct x.
      Focus 2.  destruct y.
      *  apply oZle_1inf.
      Focus 2. apply oZle_nm. simpl in E. apply Z.leb_le. assumption.
      * destruct y. apply oZle_1inf. simpl in E. congruence.
Qed.


Theorem oZmin_Correctness: forall (x y : optionZ),oZmin x y <= x /\ oZmin x y <= y.
Proof.
  intros. split.
  + unfold oZmin. assert (R: reflect (x <= y) (x <=? y)).
    apply oZleb_reflect. destruct R.
    - destruct x. apply  oZle_1inf. apply oZle_nm. lia.
    -  destruct x.
      *  destruct y. apply oZle_1inf. apply oZle_1inf.
      * destruct y.  
          **assert (R: Some z <= inf). apply  oZle_1inf. congruence.
          **  apply oZle_nm. unfold not in n. 
              assert (H1: not(z <= z0)%Z ). unfold not. intros. 
              assert (H2:  Some z <= Some z0 ). apply oZle_nm. assumption.
              apply n. assumption. lia.
  + unfold oZmin. assert (R: reflect (x <= y) (x <=? y)).
  apply oZleb_reflect. destruct R.
  - destruct y. apply  oZle_1inf.  assumption.
  - destruct y. apply oZle_1inf. apply oZle_nm. lia.
  Qed.


Axiom oZleb_Add_zero: forall (x:optionZ) ,x =  x + Some 0.


Axiom ozle_a1: forall (a b c : optionZ),
not (b <= a) -> (b <= c) -> (a <= c).


Axiom ozle_a2: forall (a b c d e: optionZ),
(a <= b) -> (c <= d)-> (e <= a + c) -> (e <= b + d).


Axiom ozle_a3: forall (a b c d : optionZ),
(a <= b) -> (c <= d)-> (a + c <= b + d).





Inductive edge (n:nat) : Type :=
  Edge (x:node n)(y :node n) (z:optionZ).
(*
  Edge is a dependent type,it assign a nat value for two term
  which belone to the same type.
  Edge x y z repersent a edge connecting x and y has weight z.
*)
Arguments Edge {n}.

Check Edge  (@F1 2) (FS (@F1 1)) (Some(-1)).
(*
 The term has type edge (t 3) and denotes a edge connecting
 1,2 in vertix set {1,2,3}
*)
Check Edge  (@F1 2) (FS (@F1 1)) inf.
(*Failed Check Edge  (@F1 1) (FS (@F1 1)) 3.
*)
Fail Compute Edge (@F1 1)(@F1 2) (Some 3).


Definition fst {n:nat} (e:@edge n):=
  match e with
  | Edge x _ _  => x
  end.


Definition snd {n:nat} (e:edge n):=
  match e with
  | Edge _ y _  => y
  end.


Definition trd {n:nat} (e:edge n):=
  match e with
  | Edge _ _ z  => z
  end.


Compute fst (Edge  (@F1 2) (FS (@F1 1)) (Some 3)).
Compute snd (Edge  (@F1 2) (FS (@F1 1)) (Some 3)).
Compute trd (Edge  (@F1 2) (FS (@F1 1)) (Some (-100))).




(*Definition Graph n :=  (list (edge n)).

*)
Notation "'Graph' n" := (list (edge n))(at level 100).

(*
graph is defined as a list of edge and Graph n means a graph
make from n vertices.
*)

Check Graph 1.
Check @nil (edge 3).
Check [Edge  (@F1 2) (FS (@F1 1)) (Some 3);
        Edge   (FS (@F1 1)) (FS(FS (@F1 0))) (Some(-5));
         Edge   (FS(FS (@F1 0))) (@F1 2) (Some 4)].
Fail Check [Edge  (@F1 2) (FS (@F1 1)) (Some 3);
        Edge  (@F1 2) (FS(FS (@F1 0))) (Some 4);
        Edge  (@F1 1) (FS (@F1 0))  (Some(-5))].
(*
  Using a list of Edge to represent a graph
  For example,[( (node 1:Node 3) (node 2:Node 3) 5)] is a graph has 5 nodes
  with the a weight 5 edge pointing from node 1 to node 2.
  nil ( Node 3) is a graph only has 3 node without any edges.
*)
Definition mygraph := 
[Edge  (@F1 2) (FS (@F1 1)) (Some 1);
        Edge  (@F1 2) (FS(FS (@F1 0))) (Some 4);
        Edge   (FS (@F1 1)) (FS(FS (@F1 0))) (Some 2);
       Edge   (FS(FS (@F1 0))) (FS (@F1 1)) (Some 1);
        Edge   (FS(FS (@F1 0))) (FS (@F1 1)) (Some(-1))].
Check mygraph.


Fixpoint Find_weight {n:nat} (i j : node n) (g : Graph n) (current:optionZ) : optionZ :=
(*
 finding the minimum edge length from i to j in order to build the adjacency matrix
*)
if eqb i j then Some 0 
else
match g with
| nil => current
| h :: t => if eqb (fst h) i && eqb (snd h) j && (trd h <=? current)
            then Find_weight i j t (trd h)
            else Find_weight i j t current
end.
           
Compute Find_weight (FS(FS (@F1 0))) (FS (@F1 1))  mygraph inf.


Axiom Find_weight_a1: forall (n:nat) (i :node n)(g : Graph n),  Find_weight i i g inf = Some 0.


Axiom Find_weight_a2: forall (n:nat) (i j:node n)(g : Graph n)(e:edge n),  
In e g -> fst e = i -> snd e = j -> Find_weight i j g inf <= trd e.




Definition Matrix n := (node n) -> (node n) -> optionZ.

Definition adj_Matrix {n:nat} (g : Graph n) : Matrix n := 
(*
    Building the adjacency matrix
*)
   fun i j =>  Find_weight i j g inf.

Example adj_findw:
forall (n:nat) (i j :node n)(g:Graph n),
adj_Matrix g i j = Find_weight i j g inf.
Proof.
intros.
unfold adj_Matrix.
reflexivity.

Compute (adj_Matrix mygraph) F1 F1.
Compute (adj_Matrix mygraph) F1 (FS F1).
Compute (adj_Matrix mygraph) F1 (FS(FS F1)).

Compute (adj_Matrix mygraph) (FS F1) F1.
Compute (adj_Matrix mygraph) (FS F1) (FS F1).
Compute (adj_Matrix mygraph) (FS F1) (FS(FS F1)).

Compute (adj_Matrix mygraph) (FS(FS F1)) F1.
Compute (adj_Matrix mygraph) (FS(FS F1)) (FS F1).
Compute (adj_Matrix mygraph) (FS(FS F1)) (FS(FS F1)).
(*
[[0 1 4]
 [inf 0 2]
 [inf -1 0]

*)


Definition Update {n:nat}(m:Matrix n)(v:node n):(Matrix n):=

(*
The function update the distance matrix m by consider adding a new node v
as intermediate vertix
*)
fun i j => if m i j <=?  (m i v) + (m v j) then  m i j else  (m i v) + (m v j).


Compute (Update (adj_Matrix mygraph) (FS F1)) F1 (FS(FS F1)).


Fixpoint Floyd_warshall {n:nat}(m:Matrix n)(vlist:list (node n)) : (Matrix n):=
(*
The function adding intermediate vertices and update the distance matrix recursively.
v is the number of intermediate vertices we did not consider.
When there is only one intermediate vertice we don't considered we can update the distance
matrix by the final vertix.
*)
  match vlist with
|  nil => m
|  h::t =>  Floyd_warshall (Update m  h) t
end.

Compute (Floyd_warshall (adj_Matrix mygraph) (NodeLst 3)) F1 F1.
Compute (Floyd_warshall (adj_Matrix mygraph) (NodeLst 3)) F1 (FS F1).
Compute (Floyd_warshall (adj_Matrix mygraph) (NodeLst 3)) F1 (FS(FS F1)).

Compute (Floyd_warshall (adj_Matrix mygraph) (NodeLst 3)) (FS F1) F1.
Compute (Floyd_warshall (adj_Matrix mygraph) (NodeLst 3)) (FS F1) (FS F1).
Compute (Floyd_warshall (adj_Matrix mygraph) (NodeLst 3)) (FS F1) (FS(FS F1)).

Compute (Floyd_warshall (adj_Matrix mygraph) (NodeLst 3)) (FS(FS F1)) F1.
Compute (Floyd_warshall (adj_Matrix mygraph) (NodeLst 3)) (FS(FS F1)) (FS F1).
Compute (Floyd_warshall (adj_Matrix mygraph) (NodeLst 3)) (FS(FS F1)) (FS(FS F1)).

(*
[[0 1 3]
 [inf 0 2]
 [inf -1 0]

*)









Inductive IsPath (n:nat): (Graph n) -> Prop := 

(*
 The edge list is considered to be a path if it has only one edge or 
 the edge can be connected for example [(1 2 3)(2 6 5) (6 3 4)] is a path 1-2-6
 the reason why need to maintain the 3rd element is the list is that the graph might 
 be a multigraph.
 
*)
  | IsPath0:forall (e:edge n), IsPath n [e]
  | IsPath1:forall (h m:edge n) (t:Graph n) , IsPath n (m::t) -> snd h = fst m -> IsPath n (h::m::t).
Implicit Arguments IsPath [n]. 

Example IsPathE1: IsPath [Edge  (@F1 2) (FS (@F1 1)) (Some 1)].
(*
  proof the edge 0-1 is  a path.
*)
Proof.
apply IsPath0.
Qed.

Example IsPathE2: IsPath [Edge  (@F1 2) (FS (@F1 1)) (Some 1);
                          Edge  (FS (@F1 1)) (FS(FS (@F1 0))) (Some 5);
                          Edge  (FS(FS (@F1 0))) (@F1 2) (Some 3)].
(*
  proof the edge 0-1-2-0 is  a path.
*)
Proof.
apply IsPath1.
+ apply IsPath1.
  - apply IsPath0.
  - simpl. reflexivity .
+ simpl. reflexivity .
Qed.


Fixpoint PathLength{n:nat} (p:Graph n): optionZ:=
(*
 PathLength return the length of a path
*)
match p with
| nil => Some 0
| h::t =>  oZadd (trd h)  (PathLength t)
end.

Compute PathLength [Edge  (@F1 2) (FS (@F1 1)) (Some 1);
                          Edge  (FS (@F1 1)) (FS(FS (@F1 0))) (Some 5);
                          Edge  (FS(FS (@F1 0))) (@F1 2) (Some (-10))].


Axiom PathLength_a1:forall (n:nat)(p p': Graph n),
PathLength p + PathLength p' = PathLength ( p ++ p').



Fixpoint InGraph {n:nat} (p:Graph n) (g:Graph n): Prop :=
match p with
| nil => True
| h :: t => (In h g \/ trd h = inf \/ (trd h = Some 0 /\ fst h = snd h))  /\ InGraph t g 
end.

Example InGraphE0: InGraph [Edge  (@F1 2) (FS (@F1 1)) inf] mygraph.
Proof.
simpl. split. right. left. reflexivity . reflexivity . Qed.

Example InGraphE1: InGraph nil mygraph.
Proof.
simpl. reflexivity . Qed.

Example InGraphE2: InGraph [Edge  (@F1 2) (FS (@F1 1)) (Some 1)] mygraph.
Proof.
simpl. split.
+ left. left. reflexivity .
+ reflexivity .
Qed.

Example InGraphE3: InGraph [Edge  (@F1 2) (FS (@F1 1)) (Some 1);
                            Edge  (@F1 2) (FS (FS (@F1 0))) (Some 4)] mygraph.
Proof.
simpl. split.
Focus 2.
split. Focus 2. reflexivity . left. right. 
left. reflexivity .
+ left. left. reflexivity .
Qed.

Example InGraphE4: InGraph [Edge  (@F1 2) (@F1 2) (Some 0)] mygraph.
Proof.
simpl. split.
Focus 2.
split. right. right. auto.
Qed.


Fixpoint FromI2J {n:nat} (i j: node n) (p:Graph n): Prop :=
match p with
| nil => False
| e :: nil => (fst e = i)  /\ (snd e = j)
| e :: l => (fst e = i) /\  snd( last l (Edge  i j (Some 0)) ) = j
end.

Example FromI2JE0: 
forall (n:nat) (i:node n), FromI2J i i ((Edge i i (Some 0))::nil).
intros. destruct i. simpl. auto. simpl. auto.
Qed.

Example FromI2JE1: not (FromI2J (@F1 2)(FS (@F1 1)) nil) .
simpl.  unfold not. intros h. apply h. Qed.

Example FromI2JE2:  (FromI2J (@F1 2)(FS (@F1 1)) [Edge  (@F1 2) (FS (@F1 1)) (Some 1)]) .
simpl.  split. 
+ reflexivity .
+ reflexivity . 
Qed.

Example FromI2JE3:  FromI2J (@F1 2)(FS (@F1 1)) 
[Edge  (@F1 2) (FS(FS (@F1 0))) (Some 2);
 Edge  (FS(FS (@F1 0))) (FS (@F1 1)) (Some 1)] .
simpl.  split. 
+ reflexivity .
+ reflexivity . 
Qed.

Example FromI2JE4:  not (FromI2J (@F1 2)(FS (@F1 1)) 
[Edge  (@F1 2) (FS(FS (@F1 0))) (Some 2);
 Edge  (FS(FS (@F1 0))) (@F1 2) (Some 1)]) .
simpl.  unfold not. intros.
destruct H. discriminate.
Qed.

Example FromI2JE5:  FromI2J (@F1 2)(FS (@F1 1)) [Edge (@F1 2) (FS (@F1 1)) (Some 1)].

simpl. split. reflexivity. reflexivity.
Qed.


Fixpoint UseIntermediate {n:nat} (p:Graph n) (l: list (node n)) : Prop :=
match p with
| nil => True
| e::nil => True
| h :: t => In (snd h) l  /\  UseIntermediate  t l
end.

Example UseInterE1: UseIntermediate nil [(@F1 2)].
simpl. reflexivity . Qed.

Example UseInterE2: UseIntermediate [Edge  (FS(FS (@F1 0))) (FS (@F1 1)) (Some 1)] [(@F1 2)].
simpl. reflexivity . Qed.

Example UseInterE3: UseIntermediate [Edge  (FS(FS (@F1 0))) (FS (@F1 1)) (Some 1);Edge  (FS (@F1 1)) (FS (@F1 1)) (Some 5)] 
                                    [@F1 2;(FS (@F1 1))].
simpl. split.
+ right. left. reflexivity .
+ reflexivity .
Qed.

Example UseInterE4: not(UseIntermediate [Edge  (FS(FS (@F1 0))) (FS (@F1 1)) (Some 1);Edge  (FS (@F1 1)) (FS (@F1 1)) (Some 5)] 
                                    [@F1 2]).
simpl. unfold not. intros.
destruct H.
destruct H.
+ discriminate.
+ assumption .
Qed.


Definition ValidPath {n:nat} 
(* 
 ValidPath p g i j l means
 p is a path from i to j in graph g and only use intermediate vertices in
 vertix list l 
 *)
(p: Graph n) (g:Graph n) (i j: node n) (l:list (node n)): Prop :=

  (IsPath p ) /\ (InGraph p g) /\ (FromI2J i j p) /\ (UseIntermediate p l).

Example ValidPathE1:
ValidPath [Edge (@F1 2)  (FS(@F1 1)) (Some 1);
           Edge (FS(@F1 1)) (FS (FS (@F1 0))) (Some 2)] 
           mygraph (@F1 2) (FS (FS (@F1 0))) [(FS(@F1 1))]. 

Proof.
unfold ValidPath.
split.
+ apply IsPath1. 
  - apply IsPath0.
  - simpl. reflexivity.
+ split.
  - simpl. split. left. left. reflexivity.
    split. left. right. right. left. reflexivity.
    reflexivity.
  - split.
    * simpl. split. reflexivity. reflexivity.
  * simpl. split. left. reflexivity.
reflexivity.
Qed.


Definition NoNegCyc {n:nat} (g:Graph n) : Prop :=
(* 
 NoNegCyc g is a proposition which means a graph g has no negative cycle
 *)
forall (p:Graph n)(i:node n)(l :list (node n)), 
ValidPath p g i i l -> Some 0 <= PathLength p. 


Definition MinDistance {n:nat} 
(* 
  d is the minimum distance from i to j in graph g  by using
 the intermediate vertices in l 
 *)

(d:optionZ ) (i j: node n)(g: Graph n)(l : list (node n))
 : Prop :=
 (exists (p: Graph n), (ValidPath p g i j l) /\ (d = PathLength p)  /\
 (forall (p': Graph n), (ValidPath p' g i j l) -> d <= PathLength p'))
.


Definition SelectSP {n:nat} (p p':Graph n) : Graph n:= 
  if PathLength p <=? PathLength p' then  p  else p'.


Axiom SelectSP_a1: forall (n:nat)(i j a :node n)(g x x0 x1 :Graph n) (l: list (node n)),
ValidPath x g i j l -> 
ValidPath x0 g i a l -> 
ValidPath x1 g a j l ->
ValidPath (SelectSP x (x0 ++ x1)) g i j (a :: l). 

(********************************************************************************)
Lemma Cyc_is_zero: 
forall (n:nat) (g p:Graph n) (i:node n), 
NoNegCyc g -> 
MinDistance (Some 0) i i g [].
Proof.
intros.
exists [Edge i i (Some 0)].
split.
{
  split.
  {
    apply IsPath0.
  }
  split.
  {
    simpl. split. right. right. auto. auto.
  }
  {
    simpl. split. apply FromI2JE0. reflexivity. 
  } 
  
}
split.
{
  simpl. reflexivity.
}

intros. apply H in H0. assumption.
Qed.




Axiom Base_Case_Correctness_l1:
forall (n:nat) (g :Graph n) (i j : node n),
InGraph [Edge i j (adj_Matrix g i j)] g.

Axiom in_a1: forall (n: nat)(i j :node n)(g p: Graph n),
i <> j -> ValidPath p g i j  [] -> (In (Edge i j (PathLength p)) g) \/(PathLength p = inf) .


Axiom Three_case_a1: forall (n:nat)(i j a:node n)(g p':Graph n)(l:list(node n)),
ValidPath p' g i j (a :: l) -> 
ValidPath p' g i j l \/ 
(exists (p1' p2' : Graph n), ValidPath p1' g i a l /\ ValidPath p2' g a j l
/\ p' = p1' ++ p2')
\/ 
(exists (p1' p2' p3' : Graph n), (ValidPath p1' g i a l) /\  (ValidPath p2' g a a l) /\
(ValidPath p3' g a j l) /\ (p' = p1' ++ p2' ++ p3')).



Theorem Base_Case_Correctness:
forall (n:nat)(i j: node n)(g: Graph n), 
NoNegCyc g->
MinDistance ((adj_Matrix g) i j) i j g nil.

Proof.
intros. unfold adj_Matrix. fold (if eqb i j
then Some 0
else Find_weight i j g inf).
assert (R: reflect (i = j) (eqb i j) ).
apply  iff_reflect. symmetry. apply eqb_eq. destruct R.
{
  
rewrite e. rewrite Find_weight_a1.  apply Cyc_is_zero. assumption. assumption.
}

  unfold MinDistance. exists [Edge i j ((adj_Matrix g) i j)]. split.
  {
    split. apply IsPath0.
    split.
    apply Base_Case_Correctness_l1.
    
    split.
    destruct i. simpl. auto. simpl. auto. simpl. auto. 

  }
  split.
  {
    simpl. 
    assert (R: reflect (i = j) (eqb i j) ).
    apply  iff_reflect. symmetry. apply eqb_eq. destruct R.
    unfold adj_Matrix.  apply oZleb_Add_zero.
    unfold adj_Matrix. apply oZleb_Add_zero.
  }
  {
    intros.
    assert ((In (Edge  i j (PathLength p')) g ) \/ (PathLength p' = inf)) .
    apply in_a1. assumption. assumption.
    assert ( PathLength p' = trd (Edge i j (PathLength p'))). simpl. reflexivity.
    destruct H1.
    {
      rewrite H2.
      apply Find_weight_a2. assumption. reflexivity.  reflexivity.

    }
    {
      rewrite H1.
      destruct (Find_weight i j g inf).
      assert (R: reflect (inf <= inf) (inf <=? inf) ).
      apply oZleb_reflect.  apply reflect_iff in R. apply R.
      auto. 
      assert (R: reflect (Some z <= inf) (Some z <=? inf) ).
      apply oZleb_reflect.  apply reflect_iff in R. apply R. auto.

    }
  }
  Qed.





Axiom Floyd_Warshal_a1:forall (n:nat)(i j a: node n)(g: Graph n)(l : list (node n)),
Floyd_warshall (adj_Matrix g) (a :: l) i j =  
 oZmin (Floyd_warshall (adj_Matrix g) l i j) 
  ((Floyd_warshall (adj_Matrix g) l i a) + 
  (Floyd_warshall (adj_Matrix g) l a j)).



Axiom Repeat_node_not_shortest: forall (n:nat)(i j a: node n)(g x2 x3 x4: Graph n)(l : list (node n)),
NoNegCyc g ->
ValidPath x2 g i a l ->  ValidPath x3 g a a l -> ValidPath x4 g a j l ->
oZmin (Floyd_warshall (adj_Matrix g) l i j)
  (Floyd_warshall (adj_Matrix g) l i a +
   Floyd_warshall (adj_Matrix g) l a j) <= 
PathLength (x2 ++ x3 ++ x4).


Theorem Inductive_Case_Correctness:
forall (n:nat)(i j a: node n)(g: Graph n)(l : list (node n)),
 NoNegCyc g 
 -> (MinDistance (Floyd_warshall (adj_Matrix g) l i j) i j g l)
 -> (MinDistance (Floyd_warshall (adj_Matrix g) l i a) i a g l) 
 -> (MinDistance (Floyd_warshall (adj_Matrix g) l a j) a j g l)
 -> MinDistance (Floyd_warshall (adj_Matrix g) (a::l) i j) i j g (a::l).
 Proof.
  intros.
  destruct H0. destruct H1. destruct H2.
  unfold MinDistance.
  exists (SelectSP x (x0 ++ x1)).
  split.
  {
    apply SelectSP_a1.
    destruct H0. 
    assumption. destruct H1.  assumption. destruct H2. assumption.
  }
  split.
  {    rewrite Floyd_Warshal_a1.
  unfold SelectSP.
  destruct H0. destruct H3.
  rewrite H3.
  destruct H1. destruct H5.
  rewrite H5.
  destruct H2. destruct H7.
  rewrite  H7.
  assert (R: reflect (PathLength x <= PathLength (x0 ++ x1))
  (PathLength x <=? PathLength (x0 ++ x1))).
   apply oZleb_reflect. destruct R.
   + unfold oZmin.
   assert (R: reflect (PathLength x <= PathLength (x0 ++ x1))
   (PathLength x <=? PathLength (x0 ++ x1))). apply oZleb_reflect.
   rewrite PathLength_a1.  destruct R.
   - 
    reflexivity.
   - congruence.
   + unfold oZmin.
   rewrite PathLength_a1.
   assert (R: reflect (PathLength x <= PathLength (x0 ++ x1))
   (PathLength x <=? PathLength (x0 ++ x1))). apply oZleb_reflect. destruct R.
   - congruence.
   - reflexivity.
  
}
  {
  intros. rewrite Floyd_Warshal_a1.
  apply Three_case_a1 in H3. destruct H3. 
  {
    unfold oZmin.
    assert (R: reflect (Floyd_warshall (adj_Matrix g) l i j <=
    Floyd_warshall (adj_Matrix g) l i a +
    Floyd_warshall (adj_Matrix g) l a j)
    (Floyd_warshall (adj_Matrix g) l i j <=?
    Floyd_warshall (adj_Matrix g) l i a +
    Floyd_warshall (adj_Matrix g) l a j)). apply oZleb_reflect. destruct R.
    destruct H0. destruct H4.
    {
      apply H5. apply H3.
    }
    {
      destruct H0. destruct H4.
      apply H5 in H3.
      apply (ozle_a1 (Floyd_warshall (adj_Matrix g) l i a +
      Floyd_warshall (adj_Matrix g) l a j)(Floyd_warshall (adj_Matrix g) l i j) (PathLength p')).
      assumption. assumption.
    }
    }
    destruct H3.
    {
      destruct H3. destruct H3. destruct H3. destruct H4.
      rewrite H5. Print PathLength_a1.
      rewrite <- PathLength_a1. unfold oZmin.
      assert (R: reflect ( Floyd_warshall (adj_Matrix g) l i j <=
      Floyd_warshall (adj_Matrix g) l i a +
      Floyd_warshall (adj_Matrix g) l a j)
     ( Floyd_warshall (adj_Matrix g) l i j <=?
     Floyd_warshall (adj_Matrix g) l i a +
     Floyd_warshall (adj_Matrix g) l a j)). apply oZleb_reflect. destruct R.
     + destruct H1. destruct H6. apply H7 in H3.
      destruct H2. destruct H8. apply H9 in H4.
      apply (ozle_a2 (Floyd_warshall (adj_Matrix g) l i a) (PathLength x2)
      (Floyd_warshall (adj_Matrix g) l a j)(PathLength x3)(Floyd_warshall (adj_Matrix g) l i j)).
      assumption. assumption.  assumption.
      + destruct H1. destruct H6. apply H7 in H3.
      destruct H2. destruct H8. apply H9 in H4.
      apply (ozle_a3 (Floyd_warshall (adj_Matrix g) l i a)(PathLength x2)
      (Floyd_warshall (adj_Matrix g) l a j)(PathLength x3)).
      assumption. assumption. 
    }
    {


      destruct H3. destruct H3. destruct H3.
      destruct H3. destruct H4. destruct H5. rewrite H6.
      apply (Repeat_node_not_shortest n i j a g x2 x3 x4 l).
      assumption.  assumption. assumption. assumption.


    }

  }

Qed.
  



Fixpoint Floyd_warshall_lemma (n:nat)(i j: node n)(g: Graph n)(l : list (node n)) : 
  NoNegCyc g -> MinDistance ((Floyd_warshall (adj_Matrix g) l) i j) i j g l.
Proof.
  intros.
  induction l.
  + simpl. apply Base_Case_Correctness. assumption.
  + apply Inductive_Case_Correctness. assumption. assumption.
  apply Floyd_warshall_lemma . assumption.
  apply Floyd_warshall_lemma. assumption.
Qed.


Theorem Floyd_warshall_Correctness:
forall (n:nat)(i j: node n)(g: Graph n), NoNegCyc g ->
MinDistance ((Floyd_warshall (adj_Matrix g) (NodeLst n)) i j) i j g (NodeLst n).
Proof. intros. apply  Floyd_warshall_lemma. assumption.
Qed.
(********************************************************************************)



Fixpoint sublist {n :nat} (l:list (node n))(v:list (node n)) : Prop := 

(*
 l is the sublist of v
*)
match l with
| nil => True
| h :: t => (In h v) /\ (sublist t v)
end.

Example sublistE1: sublist [] [@F1 2].
simpl. reflexivity . Qed.

Example sublistE2: sublist [@F1 2] (NodeLst 3).
simpl. split. left.   reflexivity . reflexivity . Qed.


Axiom  NodeLst_Correctness:
forall (n:nat)(x:node n),(1 <= n)%nat -> In x (NodeLst n).

Theorem NodeLst_include_All_list:

(*
Use:
NodeLst_Correctness
*)
forall (n:nat)(l :list (node n)),
(1 <= n)%nat  -> sublist l (NodeLst n).
Proof.
intros. induction l.
+ destruct n.
  - simpl.  reflexivity .
  - simpl.  reflexivity .
+ simpl. split.
 Focus 2. assumption.
apply  NodeLst_Correctness. assumption.
Qed.


Axiom path_still_valid:
forall (n:nat)(i j :node n)(l v :list (node n))(g p:Graph n),
 (1 <= n)%nat
 -> sublist l v
 -> ValidPath p g i j l
 -> ValidPath p g i j v.
 



Theorem  Floyd_warshall_Solved_APSP:

(*
Use:
Floyd_warshall_Correctness. 
NodeLst_include_All_list.
path_still_valid  
*)
forall (n:nat)(i j: node n)(g p: Graph n)(l:list (node n)), 
(1 <= n)%nat -> NoNegCyc g
-> (ValidPath p g i j l) 
-> ((Floyd_warshall (adj_Matrix g) (NodeLst n)) i j) <= PathLength p.

Proof. 
intros. 
assert 
(R1: MinDistance ((Floyd_warshall (adj_Matrix g) (NodeLst n)) i j) i j g (NodeLst n)).
apply Floyd_warshall_Correctness.
assert
(R2: sublist l (NodeLst n)). apply  NodeLst_include_All_list. assumption.
assert 
(R3:ValidPath p g i j  (NodeLst n)).
apply ( path_still_valid n i j l (NodeLst n) g p).
assumption. assumption. assumption.
assert 
(R4:MinDistance(Floyd_warshall(adj_Matrix g)
   (NodeLst n) i j) i j g
(NodeLst n)).
apply Floyd_warshall_Correctness. assumption. assumption.
destruct R1. destruct H2. destruct H3. apply H4.
apply (path_still_valid n i j l (NodeLst n) g p).
assumption. apply (NodeLst_include_All_list n l).
assumption. assumption. Qed.

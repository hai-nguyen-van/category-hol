theory Adjunctions

imports
  Main
  "Category2/Category"
  "Category2/Functors"
  "Category2/NatTrans"
  "ProductCategory"
  "Homset"
  "FunctorComposition"

begin

record ('o1, 'o2, 'm1, 'm2, 'a, 'b, 'c, 'd) Adjunction = 
  CatDom :: "('o1, 'm1, 'a) Category_scheme"
  CatCod :: "('o2, 'm2, 'b) Category_scheme"
  LeftFtor :: "('o1, 'o2, 'm1, 'm2, 'a, 'b, 'c) Functor_scheme"
  RightFtor :: "('o2, 'o1, 'm2, 'm1, 'b, 'a, 'd) Functor_scheme"
  Unit :: "'o1 \<Rightarrow> 'o2 \<Rightarrow> ('m2 \<Rightarrow> 'm1)"
  (* A \<in> CDom, B \<in> CCod,
     Hom_CCod (LeftFtor ## A, B) \<cong> Hom_CDom (A, RightFtor ## B)*)

(*
locale PreFunctor = 
  fixes F :: "('o1, 'o2, 'm1, 'm2, 'a1, 'a2, 'a) Functor_scheme"  (structure) 
  assumes FunctorComp: "f \<approx>>\<^bsub>CatDom F\<^esub> g \<Longrightarrow> F ## (f ;;\<^bsub>CatDom F\<^esub> g) = (F ## f) ;;\<^bsub>CatCod F\<^esub> (F ## g)"
  and     FunctorId:   "X \<in> obj\<^bsub>CatDom F\<^esub> \<Longrightarrow> \<exists> Y \<in> obj\<^bsub>CatCod F\<^esub> . F ## (id\<^bsub>CatDom F\<^esub> X) = id\<^bsub>CatCod F\<^esub> Y"
  and     CatDom[simp]:      "Category(CatDom F)"
  and     CatCod[simp]:      "Category(CatCod F)"

locale FunctorM = PreFunctor +
  assumes     FunctorCompM: "f maps\<^bsub>CatDom F\<^esub> X to Y \<Longrightarrow> (F ## f) maps\<^bsub>CatCod F\<^esub> (F @@ X) to (F @@ Y)"

locale FunctorExt = 
  fixes F :: "('o1, 'o2, 'm1, 'm2, 'a1, 'a2, 'a) Functor_scheme"  (structure) 
  assumes FunctorMapExt: "(MapM F) \<in> extensional (Mor (CatDom F))"

locale Functor = FunctorM + FunctorExt
*)

definition coextensional :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "coextensional A B = {f. \<forall>x. if x \<notin> A then f x = undefined else f x \<in> B}"

(*
definition extensional :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "extensional A = {f. \<forall>x. x \<notin> A \<longrightarrow> f x = undefined}"

definition "restrict" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b"
  where "restrict f A = (\<lambda>x. if x \<in> A then f x else undefined)"
*)
(* l'ensemble des flèches tq tout elt n'étant pas du domaine entraine que f n'y soit pas définie*)

locale Adjunction =
  fixes Adj :: "('o1, 'o2, 'm1, 'm2, 'a, 'b, 'c, 'd) Adjunction" (structure)
  assumes CatDom[simp]:  "Category (CatDom Adj)"
  and     CatCod[simp]:   "Category (CatCod Adj)"
  and     FtorLeftFtor:   "Functor (LeftFtor Adj)"
  and     FtorRightFtor:  "Functor (RightFtor Adj)"
  and     UnitOneToOne:   "A \<in> Obj (CatDom Adj) \<Longrightarrow> B \<in> Obj (CatCod Adj) \<Longrightarrow>
                            bij (Unit Adj A B)"
  and     UnitHomsetDoms: "A \<in> Obj (CatDom Adj) \<Longrightarrow> B \<in> Obj (CatCod Adj) \<Longrightarrow>
                            (Unit Adj A B) \<in> extensional (Hom (CatCod Adj) ((LeftFtor Adj) @@ A) B)"
  and     UnitHomsetCods: "A \<in> Obj (CatDom Adj) \<Longrightarrow> B \<in> Obj (CatCod Adj) \<Longrightarrow>
                            (Unit Adj A B) \<in> coextensional (Hom (CatCod Adj) ((LeftFtor Adj) @@ A) B) (Hom (CatDom Adj) A ((RightFtor Adj) @@ B))"
  and     UnitNatural:    "False"
(*
record ('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans = 
  NTDom :: "('o1, 'o2, 'm1, 'm2, 'a, 'b) Functor" 
  NTCod :: "('o1, 'o2, 'm1, 'm2, 'a, 'b) Functor" 
  NatTransMap :: "'o1 \<Rightarrow> 'm2"
*)

  (* A \<in> CDom, B \<in> CCod,
     Hom_CCod (LeftFtor ## A, B) \<cong> Hom_CDom (A, RightFtor ## B)*)

(*
record ('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans = 
  NTDom :: "('o1, 'o2, 'm1, 'm2, 'a, 'b) Functor" 
  NTCod :: "('o1, 'o2, 'm1, 'm2, 'a, 'b) Functor" 
  NatTransMap :: "'o1 \<Rightarrow> 'm2"
*)

record ('o1, 'o2, 'm1, 'm2, 'a, 'b, 'c, 'd, 'e) Adjunction' = 
  CatDom :: "('o1, 'm1, 'a) Category_scheme"
  CatCod :: "('o2, 'm2, 'b) Category_scheme"
  LeftFtor :: "('o1, 'o2, 'm1, 'm2, 'a, 'b, 'c) Functor_scheme"
  RightFtor :: "('o2, 'o1, 'm2, 'm1, 'b, 'a, 'd) Functor_scheme"
  NTUnit :: "('o1, 'o1, 'm1, 'm1, 'a, 'a, 'e) NatTrans_scheme"

locale Adjunction' =
  fixes Adj :: "('o1, 'o2, 'm1, 'm2, 'a, 'b, 'c, 'd, 'e) Adjunction'" (structure)
  assumes CatDom[simp]:  "Category (CatDom Adj)"
  and     CatCod[simp]:   "Category (CatCod Adj)"
  and     FtorLeftFtor:   "Functor (LeftFtor Adj)"
  and     FtorRightFtor:  "Functor (RightFtor Adj)"
  and     UnitNaturalFtorDom: "NTDom (NTUnit Adj) = IdentityFunctor (CatDom Adj)"
  and     UnitNaturalFtorCod: "False"
  and     UnitNatural:    "False"

value "(suc ` {1, 2})"

definition HasFiniteProducts =

end
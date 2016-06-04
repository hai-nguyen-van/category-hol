theory Concrete

imports
  Main
  "Category2/Category"
  "Category2/Functors"
  "Category2/SetCat"
  "ProductCategory"

begin

locale FaithfulFunctor = Functor +
  fixes C :: "('o, 'm, 'a) Category_scheme"
  assumes "CatDom F = C"
  and inj: "\<And>c c' f1 f2.
            \<lbrakk> c \<in> Obj C ; c' \<in> Obj C ;
              f1 \<in> Mor C ; f2 \<in> Mor C ;
              Dom C f1 = c ; Dom C f2 = c ;
              Cod C f1 = c' ; Cod C f2 = c' ;
              F ## f1 = F ## f2
            \<rbrakk> \<Longrightarrow>
            f1 = f2"

record ('o, 'm, 'a, 'b) ConcreteCategory =
  Cat :: "('o, 'm, 'a) Category_scheme"
  FF :: "('o, ZF, 'm, ZF, 'a, ZF, 'b) Functor_scheme"
  (* Embeds category into Set: not sure for the 3rd ZF type instance *)

definition DiagonalFunctor'' where
  "DiagonalFunctor'' C \<equiv> \<lparr>
      CatDom = C,
      CatCod = C,
      MapM = \<lambda>m. m
  \<rparr>"



lemma IdentityFunctorFaithful:
  fixes C
  assumes "Category C"
  shows "FaithfulFunctor (FId C) C"
proof -
  fix f1 f2 c c'
  have dom: "CatDom (FId' C) = C"
    by (simp add: IdentityFunctor'_def)
  have ftor: "Functor (FId C)" using assms by (rule Functors.IdFtorFtor)
  have inj: "\<lbrakk> c \<in> Obj C ; c' \<in> Obj C ;
            f1 \<in> Mor C ; f2 \<in> Mor C ;
            Dom C f1 = c ; Dom C f2 = c ;
            Cod C f1 = c' ; Cod C f2 = c' ;
            (FId C) ## f1 = (FId C) ## f2
         \<rbrakk> \<Longrightarrow>
         f1 = f2"
    proof -

    have left: "f1 \<in> Mor C \<Longrightarrow> (FId C) ## f1 = f1" using assms
      apply (simp add: IdentityFunctor_def MakeFtor_def, auto)
      apply (simp add: IdentityFunctor'_def)
      by (rule ccontr, insert assms(1), simp add: IdentityFunctor'_def)

    have right: "f2 \<in> Mor C \<Longrightarrow> (FId C) ## f2 = f2" using assms
      apply (simp add: IdentityFunctor_def MakeFtor_def, auto)
      apply (simp add: IdentityFunctor'_def)
      by (rule ccontr, insert assms(1), simp add: IdentityFunctor'_def)

    assume "(FId C) ## f1 = (FId C) ## f2" and "f1 \<in> Mor C" and "f2 \<in> Mor C"
    then show ?thesis using left right
    by auto
    qed
  
  show ?thesis using local.ftor local.dom local.inj 
oops

(* Comment reconstruire la preuve après l'avoir découpée ? *)
(*
lemma IdentityFunctorFaithful:
  fixes C
  assumes "Category C"
  shows "FaithfulFunctor (FId C) C"
proof -
  fix f1 f2 c c'
  have "Functor (FId C)" using assms by (rule Functors.IdFtorFtor)
  have "\<lbrakk> c \<in> Obj C ; c' \<in> Obj C ;
            f1 \<in> Mor C ; f2 \<in> Mor C ;
            Dom C f1 = c ; Dom C f2 = c ;
            Cod C f1 = c' ; Cod C f2 = c' ;
            (FId C) ## f1 = (FId C) ## f2
         \<rbrakk> \<Longrightarrow>
         f1 = f2" 

  proof -

    have left: "f1 \<in> Mor C \<Longrightarrow> (FId C) ## f1 = f1" using assms
        proof (simp add: IdentityFunctor_def MakeFtor_def, auto)
        
          have *: "f1 \<in> mor\<^bsub>C\<^esub> \<Longrightarrow> Category C \<Longrightarrow> f1 \<in> mor\<^bsub>CatDom FId' C\<^esub> \<Longrightarrow> FId' C ## f1 = f1"
            by (simp add: IdentityFunctor'_def)

        moreover (* next ? *)

          have **: "f1 \<in> mor\<^bsub>C\<^esub> \<Longrightarrow> Category C \<Longrightarrow> f1 \<notin> mor\<^bsub>CatDom FId' C\<^esub> \<Longrightarrow> undefined = f1"
            by (rule ccontr, insert assms(1), simp add: IdentityFunctor'_def)
        
        ultimately have ?thesis
oops
*)

end
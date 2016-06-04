theory SmallExamples

imports
  Main
  "Category2/Category"

begin

section "Small concrete examples"

(* Category [one_cat] with exactly one object *)
datatype one_cat_obj =
  Obj1
datatype one_cat_morph =
  Id1  (* the unique morphism is the identity by identity law *)

definition one_cat :: "(one_cat_obj, one_cat_morph) Category" where 
  "one_cat = MakeCat \<lparr>
    Obj = { Obj1 },
    Mor = { Id1 },
    Dom = \<lambda>f. case f of
              Id1 \<Rightarrow> Obj1,
    Cod = \<lambda>f. case f of
              Id1 \<Rightarrow> Obj1,
    Id = \<lambda>x. case x of
              Obj1 \<Rightarrow> Id1,
    Comp = \<lambda>f1 f2. case (f1, f2) of
                (Id1, Id1) \<Rightarrow> Id1
  \<rparr>"

(* Proving the above scheme satisfies category axioms *)
lemma "Category (one_cat)"
apply (simp add: one_cat_def)
apply (rule MakeCat)
apply (unfold_locales)
apply (auto)
apply (case_tac h, auto)
apply (case_tac g, auto)
done

(* Category [two_cat] with exactly two objects *)
datatype two_cat_obj =
    ObjA
  | ObjB
datatype two_cat_morph =
    MorphF
  | IdA
  | IdB

definition two_cat :: "(two_cat_obj, two_cat_morph) Category" where 
  "two_cat = MakeCat \<lparr>
    Obj = { ObjA, ObjB },
    Mor = { MorphF, IdA, IdB },
    Dom = \<lambda>f. case f of
              MorphF \<Rightarrow> ObjA
            | IdA \<Rightarrow> ObjA
            | IdB \<Rightarrow> ObjB,
    Cod = \<lambda>f. case f of
              MorphF \<Rightarrow> ObjB
            | IdA \<Rightarrow> ObjA
            | IdB \<Rightarrow> ObjB,
    Id = \<lambda>x. case x of
              ObjA \<Rightarrow> IdA
            | ObjB \<Rightarrow> IdB,
    Comp = \<lambda>f1 f2. case (f1, f2) of
                (IdA, IdA) \<Rightarrow> IdA
              | (IdB, IdB) \<Rightarrow> IdB
              | (IdA, MorphF) \<Rightarrow> MorphF
              | (MorphF, IdB) \<Rightarrow> MorphF
  \<rparr>"

(* Proving the above scheme satisfies category axioms *)
lemma "Category (two_cat)"
apply (simp add: two_cat_def)
apply (rule MakeCat)
apply (unfold_locales)
apply (auto)
apply (fastforce+)
done

(* Category [three_cat] with exactly three objects *)
datatype three_cat_obj =
    ObjA3
  | ObjB3
  | ObjC3
datatype three_cat_morph =
    MorphF3
  | MorphG3
  | MorphH3
  | IdA3
  | IdB3
  | IdC3

definition three_cat :: "(three_cat_obj, three_cat_morph) Category" where
  "three_cat = MakeCat \<lparr>
    Obj = { ObjA3, ObjB3, ObjC3 },
    Mor = { MorphF3, MorphG3, MorphH3, IdA3, IdB3, IdC3 },
    Dom = \<lambda>f. case f of
              MorphF3 \<Rightarrow> ObjA3
            | MorphG3 \<Rightarrow> ObjB3
            | MorphH3 \<Rightarrow> ObjA3
            | IdA3 \<Rightarrow> ObjA3
            | IdB3 \<Rightarrow> ObjB3
            | IdC3 \<Rightarrow> ObjC3,
    Cod = \<lambda>f. case f of
              MorphF3 \<Rightarrow> ObjB3
            | MorphG3 \<Rightarrow> ObjC3
            | MorphH3 \<Rightarrow> ObjC3
            | IdA3 \<Rightarrow> ObjA3
            | IdB3 \<Rightarrow> ObjB3
            | IdC3 \<Rightarrow> ObjC3,
    Id = \<lambda>x. case x of
              ObjA3 \<Rightarrow> IdA3
            | ObjB3 \<Rightarrow> IdB3
            | ObjC3 \<Rightarrow> IdC3,
    Comp = \<lambda>f1 f2. case (f1, f2) of
              (MorphF3, MorphG3) \<Rightarrow> MorphH3
            | (IdA3, MorphF3) \<Rightarrow> MorphF3
            | (IdA3, MorphH3) \<Rightarrow> MorphH3
            | (IdA3, IdA3) \<Rightarrow> IdA3
            | (MorphF3, IdB3) \<Rightarrow> MorphF3
            | (IdB3, MorphG3) \<Rightarrow> MorphG3
            | (IdB3, IdB3) \<Rightarrow> IdB3
            | (IdC3, IdC3) \<Rightarrow> IdC3
            | (MorphH3, IdC3) \<Rightarrow> MorphH3
            | (MorphG3, IdC3) \<Rightarrow> MorphG3
  \<rparr>"

lemma "Category (three_cat)"
apply (simp add: three_cat_def)
apply (rule MakeCat)
apply (unfold_locales)
apply (fastforce+)
done

definition undefined_cat :: "('o, 'm) Category" where 
  "undefined_cat = MakeCat \<lparr>
    Obj = { undefined },
    Mor = { undefined },
    Dom = \<lambda>f. undefined,
    Cod = \<lambda>f. undefined,
    Id = \<lambda>x. undefined,
    Comp = \<lambda>f1 f2. undefined
  \<rparr>"

value "undefined = undefined"

end

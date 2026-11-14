module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.RepresentableEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.CoconeConeInclusion

/-! native Hom の円錐と Yoneda 加群円錐の評価を、右包含ごと比較する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded

/-- 射の等式による cone の移送は、同じ次数 −1 の左包含も保つ。 -/
lemma dgGluingConeInl_eqToIso {R : Type u} [CommRing R] {P Q : Complex R}
    (f g : P ⟶ Q) (h : f = g) :
    (mappingCone.inl f).comp
      (Cochain.ofHom (eqToIso (congrArg (fun a : P ⟶ Q => mappingCone a) h)).hom)
      (add_zero (-1)) = mappingCone.inl g := by
  subst g
  simp

variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (x y z : E)
  (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z)

/-- Hom 後合成の円錐と Yoneda 加群円錐の同じ対象での評価との実同型。 -/
def dgGluingYonedaConeEvaluationIso :
    mappingCone (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) f) ≅
      (moduleEvaluation R E x).obj (moduleCone R E ((dgYoneda R E).onClosed.map f)) :=
  eqToIso (congrArg (fun a : homObject R E x y ⟶ homObject R E x z => mappingCone a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_evaluate R E x y z f).symm)

/-- 評価との比較は、指定した同じ右包含を厳密に保つ。 -/
lemma dgGluingYonedaConeEvaluationIso_inr :
    mappingCone.inr (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) f) ≫
      (dgGluingYonedaConeEvaluationIso R E x y z f).hom =
    mappingCone.inr ((moduleEvaluation R E x).map ((dgYoneda R E).onClosed.map f)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInr_eqToIso _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_evaluate R E x y z f).symm

/-- Yoneda 加群円錐の評価との比較は、指定した同じ次数 −1 の左包含も保つ。 -/
lemma dgGluingYonedaConeEvaluationIso_inl :
    (mappingCone.inl
      (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) f)).comp
      (Cochain.ofHom (dgGluingYonedaConeEvaluationIso R E x y z f).hom) (add_zero (-1)) =
    mappingCone.inl ((moduleEvaluation R E x).map ((dgYoneda R E).onClosed.map f)) :=
  dgGluingConeInl_eqToIso _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_evaluate R E x y z f).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

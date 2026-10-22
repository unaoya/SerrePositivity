module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeModuleMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.GradedPostcomposition

/-! 加群円錐射の左包含での評価は、元の指定零ホモトピーによる全次数の後合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "G" => DGGluingObject R C D M
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "yf" => CategoryTheory.Functor.map (DGFunctor.onClosed (dgYoneda R G)) f
local notation "b" => dgGluingConeInrModuleMap R C D M Y Z f p q

/-- 左包含での評価は、構成に使った同じ全加群 Hom の境界元の評価。 -/
lemma dgGluingConeModuleMapEvaluation_inl_element (X : G) :
    (mappingCone.inl (dgGluingPostcomposition R C D M X Y Z f)).comp
      (Cochain.ofHom (dgGluingConeModuleMapEvaluation R C D M Y Z f p q X))
      (add_zero (-1)) =
    (moduleHomπ R G (representable R Y) (representable R W) X).f (-1)
      (dgGluingConeModuleNullElement R C D M Y Z f p q) := by
  rw [dgGluingConeModuleMapEvaluation, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain]
  rw [dgGluingConeModuleEvaluationIso_inl]
  rw [dgGluingConeModuleMap]
  erw [moduleConeDescOfBoundary_eval R G yf
    (dgGluingConeModuleNullElement R C D M Y Z f p q) b
    (dgGluingConeModuleNullElement_boundary R C D M Y Z f p q) X,
    mappingCone.inl_desc]
  rfl

/-- 左成分は、元の指定 native 境界元による全次数の後合成そのもの。 -/
lemma dgGluingConeModuleMapEvaluation_inl (X : G) :
    (mappingCone.inl (dgGluingPostcomposition R C D M X Y Z f)).comp
      (Cochain.ofHom (dgGluingConeModuleMapEvaluation R C D M Y Z f p q X))
      (add_zero (-1)) =
    (dgGluingGradedPostcomposition R G X Y W).f (-1)
      (dgGluingConeNullElement R C D M Y Z f p q) := by
  rw [dgGluingConeModuleMapEvaluation_inl_element, dgGluingConeModuleNullElement]
  exact dgGluingYonedaHom_postcomposition R G X Y W
    (dgGluingConeNullElement R C D M Y Z f p q)

end SerrePositivity.InfinityCategories

module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeDerivedInverse
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeSliceTriangle
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeMappedFamily
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：元の全 cone 族の同じ既存 D(R) 像を、元の augmentation 同型の逆へ厳密に同定する。
方針：同じ全合成三角形を後合成で送り、全 Arrow 比較と逆の一意性を使う。
規約：元の全族と同じ分解を保持する。使われ方：元の実屋根との大域比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeDerivedFamilyHom_heq_mapped :
    HEq (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeDerivedFamilyHom A X Y)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeMappedFamilyHom A X Y (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A)) := by
  unfold _root_.SerrePositivity.ComplexLimits.normalizedTensorConeDerivedFamilyHom
  have ht : ∀ {α β : Sort _} (h : α = β) (v : β), HEq (h.mpr v) v := by
    intro α β h v
    cases h
    rfl
  exact ht _ _
private lemma arrow_mk_of_heq {C : Type*} [Category* C] {x y x' y' : C}
    (hx : x = x') (hy : y = y') (f : x ⟶ y) (g : x' ⟶ y') (h : HEq f g) :
    Arrow.mk f = Arrow.mk g := by
  cases hx
  cases hy
  cases eq_of_heq h
  rfl

lemma normalizedTensorConeDerivedFamilyHom_inverse_arrow :
    Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeDerivedFamilyHom A X Y) =
    Arrow.mk (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedAugmentationIso A X Y).inv := by
  let F := _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A
  have hy := congrArg (fun f => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram_derived A X Y).symm
  have h₁ := _root_.SerrePositivity.ComplexLimits.arrow_mk_of_heq rfl hy (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeDerivedFamilyHom A X Y)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeMappedFamilyHom A X Y F)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeDerivedFamilyHom_heq_mapped A X Y)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeMappedHomotopy A X Y F)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeHomotopy A X Y) F) rfl
  exact h₁.trans (h₂.trans (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePostDerived_inverse_arrow A X Y))

lemma normalizedTensorConeDerivedFamilyHom_isIso :
    IsIso (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeDerivedFamilyHom A X Y) := by
  let K := nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)
  have ht : ∀ (a b : Arrow (hoFunctor.obj ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)))),
      a = b → IsIso b.hom → IsIso a.hom := by
    intro a b h hb
    subst b
    exact hb
  apply ht _ _ (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeDerivedFamilyHom_inverse_arrow A X Y)
  change IsIso (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedAugmentationIso A X Y).inv
  exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedAugmentationIso A X Y).isIso_inv

end SerrePositivity.ComplexLimits

module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeAugmentationDerived
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeSliceTriangle
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeMappedFamily
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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

private lemma inv_arrow {C : Type*} [Category* C] {x y x' y' : C}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] (h : Arrow.mk f = Arrow.mk g) :
    Arrow.mk (inv f) = Arrow.mk (inv g) := by
  obtain ⟨hx, hy, hh⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  cases hx
  cases hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hh
  cases hh
  rfl

lemma normalizedTensorConePostDerived_inverse_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
      (normalizedTensorConeHomotopy A X Y) (complexSemifreeResolutionInfinity A)))) =
    Arrow.mk (normalizedTensorElementDerivedAugmentationIso A X Y).inv := by
  let K := nerve (normalizedTensorElementIndex A X Y)
  let F := complexSemifreeResolutionInfinity A
  let T := (hoFunctor.map ((ihom K).map F)).toFunctor
  let c := SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (normalizedTensorConeHomotopy A X Y) F))
  let e := SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y) F))
  have he : Arrow.mk e = Arrow.mk (normalizedTensorElementDerivedAugmentationIso A X Y).hom :=
    normalizedTensorDoubleConeSliceEvaluation_derived_arrow A X Y
  have hi : ∀ (a b : Arrow (SSet.HomotopyCategory ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)))),
      a = b → IsIso b.hom → IsIso a.hom := by
    intro a b h hb
    subst b
    exact hb
  have : IsIso (normalizedTensorElementDerivedAugmentationIso A X Y).hom :=
    (normalizedTensorElementDerivedAugmentationIso A X Y).isIso_hom
  have : IsIso e := hi _ _ he (by
    change IsIso (normalizedTensorElementDerivedAugmentationIso A X Y).hom
    exact (normalizedTensorElementDerivedAugmentationIso A X Y).isIso_hom)
  have htri : c ≫ e = 𝟙 _ := by
    have h := congrArg T.map (normalizedTensorDoubleConeSliceEvaluation_triangle A X Y)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    change T.map (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (normalizedTensorConeHomotopy A X Y))) ≫
      T.map (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
          (normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y))) = _ at h
    rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom] at h
    exact h
  have hc : c = inv e := by
    calc
      c = c ≫ (e ≫ inv e) := by rw [IsIso.hom_inv_id, Category.comp_id]
      _ = (c ≫ e) ≫ inv e := (Category.assoc _ _ _).symm
      _ = inv e := by rw [htri, Category.id_comp]
  exact (congrArg Arrow.mk hc).trans
    (inv_arrow e (normalizedTensorElementDerivedAugmentationIso A X Y).hom he)

end SerrePositivity.EInfinity.ComplexLimits

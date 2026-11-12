module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FunctorComponentComparison

/-!
概要：両端の指定した値同値と全自然比較に沿い、成分回収を元の fiber 写像へ反映する。
方針：始点で同じ逆射を使用し、終点の成分への単射性で元の一致を回収する。
規約：元の両写像と指定点を保持。使われ方：元の coslice 輸送による恒等点の因子化。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 各値と頂点での同じ同値と全自然比較は、元の写像による全成分回収を反映する。 -/
lemma componentRepresentative_reflect {J : Type u} {T Y : SSet.{u}}
    [Quasicategory T] [Quasicategory Y] (q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence T Y)
    (W X : J → SSet.{u}) [∀ j, Quasicategory (W j)] [∀ j, Quasicategory (X j)]
    (r : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (W j) (X j))
    (f : ∀ j, W j ⟶ T) (g : ∀ j, X j ⟶ Y)
    (h : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f j ≫ q.hom) ((r j).hom ≫ g j))
    (hs : ∀ y : Y _⦋0⦌, ∃ j, ∃ v : X j _⦋0⦌,
      SSet.π₀.mk ((g j).app (Opposite.op ⦋0⦌) v) = SSet.π₀.mk y)
    (t : T _⦋0⦌) :
    ∃ j, ∃ w : W j _⦋0⦌,
      SSet.π₀.mk ((f j).app (Opposite.op ⦋0⦌) w) = SSet.π₀.mk t := by
  obtain ⟨j, v, hv⟩ := hs (q.hom.app (Opposite.op ⦋0⦌) t)
  let w := (r j).inv.app (Opposite.op ⦋0⦌) v
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.functorIso_point_component (h j) w
  change SSet.π₀.mk (q.hom.app (Opposite.op ⦋0⦌)
      ((f j).app (Opposite.op ⦋0⦌) w)) =
    SSet.π₀.mk ((g j).app (Opposite.op ⦋0⦌) ((r j).hom.app (Opposite.op ⦋0⦌) w)) at hh
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.qCatEquivalence_inv_hom_component (r j) v
  have hg := congrArg (SSet.mapπ₀ (g j)) hr
  simp only [SSet.mapπ₀_mk] at hg
  refine ⟨j, w, ?_⟩
  apply q.isQCatEquivalence.isSimplicialHomotopyEquivalence.mapPiZero_bijective.injective
  simp only [SSet.mapπ₀_mk]
  exact hh.trans (hg.trans hv)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

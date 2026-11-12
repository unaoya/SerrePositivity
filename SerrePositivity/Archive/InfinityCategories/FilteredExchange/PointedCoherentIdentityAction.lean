module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedCoherentCosliceFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceSourceIdentity

/-!
概要：恒等 coslice 点での全係数前合成は元の標準 pointed fiber 比較。
方針：零単体からの射の定値表示と既存の恒等前合成の式を正規化する。
規約：全反転 Hom をそのまま保持する。
使われ方：零面の全係数円柱の始点固定条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 一点からの射に係数を加えると、同じ定値頂点の全係数族を回収する。 -/
lemma pointMap_whiskerRight_lift {Z : SSet.{u}} (w : (Δ[0] : SSet.{u}) ⟶ Z)
    (A : SSet.{u}) :
    w ▷ A = snd Δ[0] A ≫ lift (SSet.const (SSet.yonedaEquiv w)) (𝟙 A) := by
  have hw := SSet.yonedaEquiv_symm_zero (SSet.yonedaEquiv w)
  rw [Equiv.symm_apply_apply] at hw
  conv_lhs => rw [hw]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨a, x⟩
  rfl

/-- 元の恒等 coslice 点の全係数作用は同じ元の標準 fiber 比較。 -/
lemma pointedCoherentSourcePrecomposition_identity_action (K : KanObject.{u}) :
    (cosliceIdentityPoint (coherentNerveVertex K) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject K).op) ≫
      (coherentCosliceSourcePrecomposition pointKanObject K ≫ pointedCoherentCosliceIso.hom) =
    snd Δ[0] _ ≫ pointedCoherentFiberComparison K ≫
      vertexFiberι pointedSpaceProjection (coherentNerveVertex K) := by
  rw [pointMap_whiskerRight_lift]
  simp only [Category.assoc]
  rw [← Category.assoc _ (coherentCosliceSourcePrecomposition pointKanObject K),
    coherentCosliceSourcePrecomposition_identity]
  simp only [Category.assoc]
  rw [← pointedCoherentCosliceIso_comparison]

end SerrePositivity.InfinityCategories.F2

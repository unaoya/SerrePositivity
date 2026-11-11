module
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct

/-! # 同じ始端を持つ二つの prism の外ホーンへの貼り合わせ

概要：全パラメーターで始端が一致する二つの辺族を零番外ホーン上へ貼る。
方針：二次外ホーンの押し出しをパラメーターとの積で保存する。
規約：両辺を厳密に保持。使われ方：実屋根の比較と指定目標の輸送の同時延長。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 零番外ホーンの二辺表示は任意のパラメーターとの積でも押し出し。 -/
lemma roofFirstHornPrism_isPushout (L : SSet.{u}) :
    IsPushout (L ◁ (SSet.stdSimplex.δ (1 : Fin 2)))
      (L ◁ (SSet.stdSimplex.δ (1 : Fin 2)))
      (L ◁ horn₂₀.ι₀₁) (L ◁ horn₂₀.ι₀₂) :=
  IsPushout.map (tensorLeft L) horn₂₀.isPushout

variable {L E : SSet.{u}} (f g : L ⊗ Δ[1] ⟶ E)
variable (h : (L ◁ (SSet.stdSimplex.δ (1 : Fin 2))) ≫ f =
  (L ◁ (SSet.stdSimplex.δ (1 : Fin 2))) ≫ g)

/-- 始端が一致する二つの辺族を、全係数を保って外ホーンへ貼る。 -/
def roofFirstHornPrism : L ⊗ (Λ[2, 0] : SSet.{u}) ⟶ E :=
  (roofFirstHornPrism_isPushout L).desc f g h

/-- 貼った外ホーンの最初の辺は指定された比較。 -/
lemma roofFirstHornPrism_edge01 :
    (L ◁ horn₂₀.ι₀₁) ≫ roofFirstHornPrism f g h = f :=
  (roofFirstHornPrism_isPushout L).inl_desc _ _ _

/-- 貼った外ホーンの対角は指定された輸送。 -/
lemma roofFirstHornPrism_edge02 :
    (L ◁ horn₂₀.ι₀₂) ≫ roofFirstHornPrism f g h = g :=
  (roofFirstHornPrism_isPushout L).inr_desc _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories

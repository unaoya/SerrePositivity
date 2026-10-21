module

public import SerrePositivity.InfinityCategories.F2.CoconeHomotopyUnitCylinder
public import SerrePositivity.InfinityCategories.F2.CoherentColimitCoconeHomotopy

/-!
概要：元の coherent 変換に沿う、元の native 全空間余錐の単位の自然性円柱。
方針：全余錐円柱の二時間の制限を読み、底と余極限の指定辺を回収する。
規約：元の変換・両単位・頂点の辺を保持。使われ方：a6 の native 二脚との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の native 全空間余錐の単位を結ぶ、元の変換に沿った二時間の円柱。 -/
def coherentColimitUnitCylinder :=
  coconeHomotopyUnitCylinder (coherentDiagramTotalCocone F) (coherentDiagramTotalCocone G)
    (coherentColimitCoconeHomotopy B H)

/-- 図式側では元の指定変換の全円柱を厳密に回収する。 -/
lemma coherentColimitUnitCylinder_source :
    (SSet.ι₀ (X := (SSet.uliftFunctor.{u + 1, u}).obj B) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (coherentColimitUnitCylinder B H).h = H.h := by
  rw [coherentColimitUnitCylinder, coconeHomotopyUnitCylinder_source,
    coherentColimitCoconeHomotopy_restrict]

/-- 頂点側では元の余極限関手が送る指定辺を、底に関して定値な全円柱として回収する。 -/
lemma coherentColimitUnitCylinder_target :
    (SSet.ι₁ (X := (SSet.uliftFunctor.{u + 1, u}).obj B) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (coherentColimitUnitCylinder B H).h =
        snd ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[1] ≫
          SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B H).edge := by
  rw [coherentColimitUnitCylinder, coconeHomotopyUnitCylinder_target,
    coherentColimitCoconeHomotopy_h]
  change _ = _ ≫ SSet.yonedaEquiv.symm ((coherentColimitFunctor B).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (curry H.h)))
  rw [← SSet.yonedaEquiv_comp, Equiv.symm_apply_apply]
  change _ = _ ≫ (curry H.h ≫ coherentColimitCoconeFunctor B) ≫ evaluateFunctorAt _
  rfl

end SerrePositivity.InfinityCategories.F2

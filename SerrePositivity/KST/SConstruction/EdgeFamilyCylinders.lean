module
public import SerrePositivity.KST.SConstruction.PointFamilyHomotopyEdge

/-! # 元の実辺を任意の共通パラメータ上の同じ円柱にする
概要：元の全辺を第二射影で引き戻し、元の同じ両端頂点を全パラメータで回収する。
方針：区間の端点を零単体の面として評価し、元の辺の始終点の式を使う。
規約：辺・円柱を選び直さず、元の全一単体を保持する。
使われ方：元の BF 二入力比較辺の段評価を、最終射の補正と二時刻で合成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 元の全辺を、共通パラメータによらない同じ全円柱へ写す。 -/
def edgeFamilyCylinder {U E : SSet.{u}} {x y : E _⦋0⦌} (a : E.Edge x y) :
    U ⊗ (Δ[1] : SSet.{u}) ⟶ E := snd U Δ[1] ≫ SSet.yonedaEquiv.symm a.edge

/-- 元の円柱の始端は、元の同じ始点で全パラメータにわたり定数。 -/
lemma edgeFamilyCylinder_zero {U E : SSet.{u}} {x y : E _⦋0⦌} (a : E.Edge x y) :
    SSet.ι₀ ≫ edgeFamilyCylinder (U := U) a = SSet.const x := by
  rw [edgeFamilyCylinder, SSet.ι₀_snd_assoc]
  calc
    _ = SSet.const (X := U) (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) ≫
      stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm a.edge := by
      simp only [stdSimplex.δ_one_eq_const, ← Category.assoc, SSet.comp_const]
    _ = _ := by
      rw [SSet.Edge.δ_one_yonedaEquiv_symm, SSet.yonedaEquiv_symm_zero, SSet.comp_const]

/-- 元の円柱の終端も、元の同じ終点で全パラメータにわたり定数。 -/
lemma edgeFamilyCylinder_one {U E : SSet.{u}} {x y : E _⦋0⦌} (a : E.Edge x y) :
    SSet.ι₁ ≫ edgeFamilyCylinder (U := U) a = SSet.const y := by
  rw [edgeFamilyCylinder, SSet.ι₁_snd_assoc]
  calc
    _ = SSet.const (X := U) (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) ≫
      stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm a.edge := by
      simp only [stdSimplex.δ_zero_eq_const, ← Category.assoc, SSet.comp_const]
    _ = _ := by
      rw [SSet.Edge.δ_zero_yonedaEquiv_symm, SSet.yonedaEquiv_symm_zero, SSet.comp_const]

end SerrePositivity.KST.SConstruction

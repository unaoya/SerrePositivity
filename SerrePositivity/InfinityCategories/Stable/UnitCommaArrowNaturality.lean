module
public import SerrePositivity.InfinityCategories.Stable.LoopSourceUniversalUnit
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaUnitComponent
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaFiberLeftFibration
public import SerrePositivity.InfinityCategories.Core.HomotopyNatTrans

/-!
概要：固定始域 comma の実矢印と始対象性、指定 loop 単位の可逆性。
方針：実ホモトピーの Ho 自然性と left fibration の可逆性反映を使う。
規約：生の関手値の端点を保つ。使われ方：元の loop 四角形の押し出し性の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ comma の実矢印と始対象性の比較。 -/
def unitCommaFiberArrowTransformation {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌) :
    (hoFunctor.map (SSet.const x : unitCommaFiber G x ⟶ X)).toFunctor ⟶
      (hoFunctor.map (unitCommaFiberTarget (𝟙 (unitCommaFiber G x)) ≫ G)).toFunctor :=
  let H := unitCommaFiberHomotopy (𝟙 (unitCommaFiber G x))
  homotopyNatTransOfEndpoints H.h H.h₀ H.h₁

/-- 同じ comma の実矢印と始対象性の比較。 -/
def unitCommaFiberArrowHom {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    (v : (unitCommaFiber G x) _⦋0⦌) :
    (hoFunctor.map (SSet.const x : unitCommaFiber G x ⟶ X)).toFunctor.obj
      (HomotopyCategory.mk v) ⟶
    (hoFunctor.map (unitCommaFiberTarget (𝟙 (unitCommaFiber G x)) ≫ G)).toFunctor.obj
      (HomotopyCategory.mk v) :=
  (unitCommaFiberArrowTransformation G x).app (HomotopyCategory.mk v)

/-- 同じ comma の実矢印と始対象性の比較。 -/
lemma hoConstMap_edge {E X : SSet.{u}} (x : X _⦋0⦌) {a b : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) a b) :
    (hoFunctor.map (SSet.const x : E ⟶ X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk e) =
      𝟙 ((hoFunctor.map (SSet.const x : E ⟶ X)).toFunctor.obj
        (HomotopyCategory.mk a)) := by
  change SSet.Truncated.HomotopyCategory.homMk
    (e.map ((truncation 2).map (SSet.const x : E ⟶ X))) = _
  have he : e.map ((truncation 2).map (SSet.const x : E ⟶ X)) =
      SSet.Truncated.Edge.id (X := (truncation 2).obj X) (PinchedHom.constant x 0) := by
    apply SSet.Truncated.Edge.ext
    change PinchedHom.constant x 1 = X.σ 0 (PinchedHom.constant x 0)
    rw [pinchedConstant_zero]
    exact pinchedConstant_one x
  rw [he]
  exact SSet.Truncated.HomotopyCategory.homMk_id
    (V := (truncation 2).obj X) (PinchedHom.constant x 0)

/-- 同じ comma の実矢印と始対象性の比較。 -/
lemma unitCommaFiberArrowHom_naturality_edge {X Y : SSet.{u}}
    (G : Y ⟶ X) (x : X _⦋0⦌) {a b : (unitCommaFiber G x) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (unitCommaFiber G x)) a b) :
    unitCommaFiberArrowHom G x b = unitCommaFiberArrowHom G x a ≫
      (hoFunctor.map (unitCommaFiberTarget (𝟙 (unitCommaFiber G x)) ≫ G)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk e) := by
  have h := (unitCommaFiberArrowTransformation G x).naturality
    (SSet.Truncated.HomotopyCategory.homMk e)
  rw [hoConstMap_edge] at h
  exact (Category.id_comp _).symm.trans h
end SerrePositivity.InfinityCategories

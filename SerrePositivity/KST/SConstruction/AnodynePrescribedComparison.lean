module
public import SerrePositivity.KST.SConstruction.AnodyneRelativeFibrationFamily
public import SerrePositivity.KST.SConstruction.PrescribedRawHomotopyLift

/-! # 全指定面と元の全基底比較を保つ高次比較の持ち上げ
概要：fibration に沿い、両端と anodyne な指定面の全比較、基底の全円柱を同時に保つ。
方針：境界との pushout-product に沿う全パラメータ持ち上げを実円柱へ戻す。
規約：基底比較を定数と仮定せず、指定面の全時刻の像を厳密に回収する。
使われ方：三面を保持する始辺消去四面体を元の高次 prism に沿って相対的に比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open scoped Simplicial

/-- 両端・全指定面・元の全基底比較を厳密に保持する実比較円柱。 -/
def anodynePrescribedComparisonData {A D E B : SSet.{u}}
    (i : A ⟶ D) (hi : anodyneExtensions i) (p : E ⟶ B) [Fibration p]
    (f g : D ⟶ E) (H : SSet.Homotopy (f ≫ p) (g ≫ p))
    (C : SSet.Homotopy (i ≫ f) (i ≫ g))
    (hc : C.h ≫ p = (i ▷ (Δ[1] : SSet.{u})) ≫ H.h) :
    {K : SSet.Homotopy f g // K.h ≫ p = H.h ∧
      (i ▷ (Δ[1] : SSet.{u})) ≫ K.h = C.h} := by
  let ex := exists_anodyneRelativeFibrationFamily i hi (SSet.boundary 1).ι p
    C.h (boundaryMap f g) H.h (KanHomotopyExtension.boundary_compatibility i f g C)
    hc ((familyBoundaryMap_post p f g).trans
      (HomotopyEndpointComparison.boundary_eq H).symm)
  let K := familyHomotopyOfBoundary f g ex.choose ex.choose_spec.1
  exact ⟨K, ex.choose_spec.2.2, ex.choose_spec.2.1⟩

end SerrePositivity.KST.SConstruction

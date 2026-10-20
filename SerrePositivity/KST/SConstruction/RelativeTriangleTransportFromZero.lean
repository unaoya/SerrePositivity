module
public import SerrePositivity.KST.SConstruction.RelativeFaceTransportFromZero

/-! # 元の全三角形を始端に保つ相対境界移送
概要：元の全三角形を時刻零に保持し、指定した境界円柱を全側面として回収する。
方針：全三角形境界の包含に沿う始端固定移送から、元の各辺と固定対角面を回収する。
規約：元の二単体を選び直さず全像を保持する。境界円柱は入力したものそのもの。
使われ方：BF 三入力の辺を元の比較辺へ移し、元の全三角形と共通対角辺を保つ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {E : SSet.{u}} [KanComplex E] (s : E _⦋2⦌)
  (a : (∂Δ[2] : SSet.{u}) ⟶ E)
  (H : SSet.Homotopy ((SSet.boundary 2).ι ≫ SSet.yonedaEquiv.symm s) a)

/-- 元の全三角形を始端に固定した、同じ全境界円柱の相対移送データ。 -/
def triangleTransportFromZeroData :=
  faceTransportFromZeroData (SSet.boundary 2).ι (SSet.yonedaEquiv.symm s) a H

/-- 元の指定境界を持つ実二単体。 -/
def triangleTransportFromZero := SSet.yonedaEquiv (triangleTransportFromZeroData s a H).val

/-- 元の各指定辺を、新しい全二単体の対応する面として厳密に回収する。 -/
lemma triangleTransportFromZero_face (i : Fin 3) :
    E.δ i (triangleTransportFromZero s a H) = SSet.yonedaEquiv (SSet.boundary.ι i ≫ a) := by
  change E.δ i (SSet.yonedaEquiv (triangleTransportFromZeroData s a H).val) = _
  rw [← stdSimplex.yonedaEquiv_δ_comp]
  apply congrArg SSet.yonedaEquiv
  rw [← SSet.boundary.ι_ι_assoc, (triangleTransportFromZeroData s a H).restriction]

/-- 元の同じ全三角形から新しい全二単体への実比較円柱。 -/
def triangleTransportFromZeroComparison : SSet.Homotopy
    (SSet.yonedaEquiv.symm s) (SSet.yonedaEquiv.symm (triangleTransportFromZero s a H)) :=
  familyHomotopyEndpointTransport (triangleTransportFromZeroData s a H).comparison
    rfl (Equiv.symm_apply_apply _ _).symm

/-- 全比較円柱も、元の相対移送の同じ全写像そのもの。 -/
lemma triangleTransportFromZeroComparison_h :
    (triangleTransportFromZeroComparison s a H).h =
      (triangleTransportFromZeroData s a H).comparison.h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 全比較の側面は、元の指定した同じ全境界円柱そのもの。 -/
lemma triangleTransportFromZeroComparison_boundary :
    ((SSet.boundary 2).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleTransportFromZeroComparison s a H).h = H.h := by
  rw [triangleTransportFromZeroComparison_h]
  exact (triangleTransportFromZeroData s a H).comparison_boundary

/-- 指定境界円柱の一辺が固定されれば、全三角形の比較でも同じ辺全体を固定する。 -/
lemma triangleTransportFromZeroComparison_fixed_face (i : Fin 3) (q : (Δ[1] : SSet.{u}) ⟶ E)
    (hq : (SSet.boundary.ι i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst Δ[1] Δ[1] ≫ q) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ (triangleTransportFromZeroComparison s a H).h =
      fst Δ[1] Δ[1] ≫ q := by
  rw [← SSet.boundary.ι_ι i, comp_whiskerRight, Category.assoc,
    triangleTransportFromZeroComparison_boundary, hq]

end SerrePositivity.KST.SConstruction

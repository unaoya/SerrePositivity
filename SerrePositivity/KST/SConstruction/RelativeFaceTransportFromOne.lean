module
public import SerrePositivity.KST.SConstruction.RelativeFamilyRectification
public import SerrePositivity.KST.SConstruction.FamilyCompositeImageClasses

/-! # 元の終端面と全境界円柱を保つ相対面移送
概要：元の全終端面を固定し、指定した全境界円柱をそのまま持つ全比較を構成する。
方針：終端一頂点と全側面の包含の anodyne 性に沿い、Kan 標的へ相対的に持ち上げる。
規約：元の終端面・全境界円柱を厳密に回収する。区間の順序反転を使わない。
使われ方：元の BF 三角形を時刻一に保ち、時刻零の辺を元の BF 比較辺へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet HomotopicalAlgebra
open SerrePositivity.SimplicialModel.KanFibrationEndpointExtension
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 元の終端面と指定全境界円柱をそのまま保持する、新しい面と実比較のデータ。 -/
structure FaceTransportFromOneData {A T E : SSet.{u}} (j : A ⟶ T)
    (b : T ⟶ E) (a : A ⟶ E) (H : SSet.Homotopy a (j ≫ b)) where
  /-- 指定した元の始点境界を持つ新しい面。 -/
  val : T ⟶ E
  /-- 新しい面の境界は元の指定境界そのもの。 -/
  restriction : j ≫ val = a
  /-- 元の同じ全終端面へ至る実比較円柱。 -/
  comparison : SSet.Homotopy val b
  /-- 比較の全側面は、元の同じ全境界円柱。 -/
  comparison_boundary : (j ▷ (Δ[1] : SSet.{u})) ≫ comparison.h = H.h

/-- 元の全終端面を変更せず、同じ全境界円柱を側面とする相対面移送を構成する。 -/
def faceTransportFromOneData {A T E : SSet.{u}} [KanComplex E]
    (j : A ⟶ T) [Mono j] (b : T ⟶ E) (a : A ⟶ E)
    (H : SSet.Homotopy a (j ≫ b)) : FaceTransportFromOneData j b a H := by
  let p := terminal.from E
  have hp : SSet.modelCategoryQuillen.J.rlp p :=
    (SSet.modelCategoryQuillen.fibration_iff p).mp inferInstance
  let ex := exists_from_one p hp j b a H (terminal.from _)
    (by apply terminal.hom_ext) (by apply terminal.hom_ext)
  exact ⟨ex.choose, ex.choose_spec.1, ex.choose_spec.2.choose,
    ex.choose_spec.2.choose_spec.1⟩

end SerrePositivity.KST.SConstruction

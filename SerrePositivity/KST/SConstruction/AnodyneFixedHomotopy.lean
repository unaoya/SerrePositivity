module
public import SerrePositivity.KST.SConstruction.FamilyCompositeImageClasses
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRelativeLifting
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-! # anodyne 部分を全時刻固定する実比較
概要：同じ anodyne 制限を持つ二写像の間に、その全制限を固定する実円柱を構成する。
方針：境界との pushout-product の anodyne 性から相対ホモトピー延長を適用する。
規約：元の全指定部分を全比較時刻で厳密に保持する。標的全体の可縮性は要求しない。
使われ方：元の三面を保つ始辺消去四面体の二選択を高次比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.InfinityCategories
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 同じ anodyne 制限を持つ元の二写像を、その全制限を固定して比較する。 -/
def anodyneFixedHomotopyData {A B E : SSet.{u}} [KanComplex E]
    (i : A ⟶ B) (hi : anodyneExtensions i) (f g : B ⟶ E) (he : i ≫ f = i ≫ g) :
    {H : SSet.Homotopy f g // (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst A Δ[1] ≫ i ≫ f} := by
  let pp := KanRelativeLifting.boundaryProduct i
  have hp : HasLiftingProperty pp.ι (CategoryTheory.Limits.terminal.from E) :=
    (anodyneExtensions_pushoutObjObjι' pp hi) _
      ((HomotopicalAlgebra.fibration_iff _).mp inferInstance)
  let H := familyHomotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (i ≫ f)) rfl he
  have hH : H.h = fst A (Δ[1] : SSet.{u}) ≫ i ≫ f :=
    familyHomotopyEndpointTransport_h _ _ _
  let ex := KanRelativeLifting.exists_extension i hp f g H
  exact ⟨ex.choose, ex.choose_spec.trans hH⟩

end SerrePositivity.KST.SConstruction

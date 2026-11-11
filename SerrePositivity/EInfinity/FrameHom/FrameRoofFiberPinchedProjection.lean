module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofFiberPinched
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.PinchedFamilyComposition

/-!
# 元の屋根 fiber と pinched Hom の同型は全 slice 包含を保つ

概要：元の fiber 同型を同じ qY の全 slice に含めると元の屋根の錐を回収する。
方針：元の始点・点図式の等式輸送を全包含に移し、引き戻しの第一射影を計算する。
規約：全単体・元の点図式・元の q を保つ。
使われ方：実 corner 評価の prism の終端と元の pinched 族の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SSet SerrePositivity.InfinityCategories
open scoped Simplicial

lemma roofSliceFiberPointTransport_ι {E : SSet.{u}} {p p' : (Δ[0] : SSet.{u}) ⟶ E}
    (h : p = p') (x : E _⦋0⦌) :
    (eqToIso (congrArg (fun a => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection a) x) h)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p') x =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) x ≫ (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver h)).hom := by
  subst p'
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]

variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E)

def roofTargetSlicePointIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y) ≫ q) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))) :=
  eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetPoint q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)))

lemma roofTargetFiberPinchedIso_slice (n : I) :
    (roofTargetFiberPinchedIso A Y q n).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice E (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (A.obj n)))
        (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (roofTargetProjection A Y q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n) ≫
        pullback.fst _ _ ≫ (roofTargetSlicePointIso Y q).hom := by
  dsimp only [roofTargetFiberPinchedIso, Iso.trans_hom, Iso.symm_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [roofSliceFiberPointTransport_ι (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetPoint q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))]
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberTransport_ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y) ≫ q))
    (roofTargetFrameVertex A q n)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y) ≫ q))
    (nerveMap A ≫ q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)
  simp only [eqToIso.hom]
  rw [reassoc_of% h₂, reassoc_of% h₁]
  rfl

end SerrePositivity.EInfinity.FrameHom.FrameArrows

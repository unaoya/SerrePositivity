module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：定値写像による引き戻しを、元の底と指定 fiber の直積へ厳密に分解する。
方針：引き戻しの両射影と fiber の持ち上げを使って両逆射を作る。
規約：充填性・極限性の仮定は不要。
使われ方：定値図式の unstraightening を始域とする相対関手の指数則。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks

/-- 定値写像への引き戻しから元の底と指定 fiber の積へ写す。 -/
def pullbackConstantToTensor {E B : SSet.{u}} (p : E ⟶ B) (b : B.obj (Opposite.op ⦋0⦌))
    (A : SSet.{u}) : pullback p (SSet.const b : A ⟶ B) ⟶ A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b :=
  lift (pullback.snd _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b (pullback.fst _ _) (by
    rw [pullback.condition, SSet.comp_const]))

/-- 指定 fiber の積から定値写像への引き戻しへ写す。 -/
def tensorToPullbackConstant {E B : SSet.{u}} (p : E ⟶ B) (b : B.obj (Opposite.op ⦋0⦌))
    (A : SSet.{u}) : A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ pullback p (SSet.const b : A ⟶ B) :=
  pullback.lift (snd A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (fst A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)) (by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const])

/-- 定値写像への引き戻しは、同じ底と指定 fiber の積に厳密に同型。 -/
def pullbackConstantTensorIso {E B : SSet.{u}} (p : E ⟶ B)
    (b : B.obj (Opposite.op ⦋0⦌)) (A : SSet.{u}) :
    pullback p (SSet.const b : A ⟶ B) ≅ A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b where
  hom := pullbackConstantToTensor p b A
  inv := tensorToPullbackConstant p b A
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [pullbackConstantToTensor, tensorToPullbackConstant, Category.assoc,
        pullback.lift_fst, lift_snd_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]
    · simp only [pullbackConstantToTensor, tensorToPullbackConstant, Category.assoc,
        pullback.lift_snd, lift_fst, Category.id_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [pullbackConstantToTensor, tensorToPullbackConstant, Category.assoc,
        lift_fst, pullback.lift_snd, Category.id_comp]
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
      simp only [pullbackConstantToTensor, tensorToPullbackConstant, Category.assoc,
        lift_snd_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, pullback.lift_fst, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks

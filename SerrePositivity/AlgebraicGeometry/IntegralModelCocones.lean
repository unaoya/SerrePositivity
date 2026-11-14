module

public import SerrePositivity.AlgebraicGeometry.IntegralModelCategory
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
概要：有限・有限表示の代数の模型二つを同じ模型へ送る。
方針：テンソル積を取り、元の環への二つの射を積により合成する。
規約：有限表示性は既存の baseChange と trans を使い、係数環の Noether 性は要求しない。
使われ方：整拡大の近似の添字圏の filtered 性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped TensorProduct
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- 有限表示代数のテンソル積の有限表示性を、既存の有限表示の底変換から得る。 -/
private theorem finitePresentation_tensor_integralModel
    (C D : Type u) [CommRing C] [CommRing D] [Algebra R C] [Algebra R D]
    [Algebra.FinitePresentation R C] [Algebra.FinitePresentation R D] :
    Algebra.FinitePresentation R (C ⊗[R] D) := by
  have : Algebra.FinitePresentation C (C ⊗[R] D) :=
    ((Algebra.Presentation.ofFinitePresentation R D).baseChange C).finitePresentation_of_isFinite
  exact Algebra.FinitePresentation.trans R C _

set_option backward.isDefEq.respectTransparency false in
/-- 任意の二つの有限・有限表示模型は、共通の有限・有限表示模型への射を持つ。 -/
theorem integralModelCategory_cocone_objs (X Y : IntegralModelCategory R B) :
    ∃ (Z : IntegralModelCategory R B) (_ : X ⟶ Z) (_ : Y ⟶ Z), True := by
  let C := X.obj.left.obj
  let D := Y.obj.left.obj
  let E := C ⊗[R] D
  have : Algebra.FinitePresentation R E := finitePresentation_tensor_integralModel C D
  have : Module.Finite R E := inferInstance
  let g : E →ₐ[R] B := Algebra.TensorProduct.lift X.obj.hom.hom Y.obj.hom.hom
    (fun _ _ ↦ Commute.all _ _)
  let Z := integralModelObj g
  have hX : Z.obj.hom.hom.comp Algebra.TensorProduct.includeLeft = X.obj.hom.hom :=
    Algebra.TensorProduct.lift_comp_includeLeft X.obj.hom.hom Y.obj.hom.hom
      (fun _ _ ↦ Commute.all _ _)
  have hY : Z.obj.hom.hom.comp Algebra.TensorProduct.includeRight = Y.obj.hom.hom :=
    Algebra.TensorProduct.lift_comp_includeRight' X.obj.hom.hom Y.obj.hom.hom
      (fun _ _ ↦ Commute.all _ _)
  exact ⟨Z, integralModelHomMk Algebra.TensorProduct.includeLeft hX,
    integralModelHomMk Algebra.TensorProduct.includeRight hY, trivial⟩

end SerrePositivity.AlgebraicGeometry

module

public import SerrePositivity.AlgebraicGeometry.AffineVCover
public import SerrePositivity.AlgebraicGeometry.FaithfullyFlatValuationLift
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
概要：忠実平坦な環準同型は affine v 被覆。
方針：試験付値環でテンソル積に底変換し、その閉点・一般点からの付値持ち上げを使う。
規約：有限表示を要求せず、零環も同じ付値判定で扱う。
使われ方：Rydh 3.10 の fppf 因子の v 被覆性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- 忠実平坦射は、任意の階数の付値環に関する affine v 判定を満たす。 -/
theorem isAffineVCover_of_faithfullyFlat (f : A →+* B) (hf : f.FaithfullyFlat) :
    IsAffineVCover f := by
  intro V _ _ k
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A V := k.toAlgebra
  letI : Module.FaithfullyFlat A B := hf
  let T := V ⊗[A] B
  have hT : (algebraMap V T).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  obtain ⟨W, hW, hval, e, l, he, hl⟩ :=
    exists_valuation_lift_of_faithfullyFlat (algebraMap V T) hT
  refine ⟨W, hW, hval, e, l.comp Algebra.TensorProduct.includeRight.toRingHom, he, ?_⟩
  have hsq : Algebra.TensorProduct.includeRight.toRingHom.comp f = (algebraMap V T).comp k :=
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := A) (A := V) (B := B)).symm
  rw [RingHom.comp_assoc, hsq, ← RingHom.comp_assoc, hl]

end SerrePositivity.AlgebraicGeometry

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGAlgebraExtensionInfinity
public import SerrePositivity.KST.LocalizingInvariants.DGEndAlgebra
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic

/-! # 右加群用一対象圏の End の代数方向
概要：右加群用の一対象圏の End を反転してから代数化すると、元の代数を回収する。
方針：Sp の dgEndAlgebra を使い、二つの Koszul 交換を対称性で消す。
規約：元の積・単位を保持。使われ方：元の右代数から具体的 ⊙ への代数射。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
open scoped MonObj
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) (x : _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)

/-- 元の代数は、右加群用一対象圏の反転した全 End の代数と同じ単位・積で同型。 -/
def dgAlgebraRightEndIso :
    B ≅ LocalizingInvariants.dgEndAlgebra R (EndomorphismObject x)ᵒᵖ
      (Opposite.op EndomorphismObject.point) := by
  refine Mon.mkIso (M := B)
    (N := LocalizingInvariants.dgEndAlgebra R (EndomorphismObject x)ᵒᵖ
      (Opposite.op EndomorphismObject.point)) (Iso.refl B.X) ?_ ?_
  · change η[B.X] ≫ 𝟙 _ = η[B.X]
    exact Category.comp_id _
  · change μ[B.X] ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫
      (β_ B.X B.X).hom ≫ (β_ B.X B.X).hom ≫ μ[B.X]
    rw [id_tensorHom_id, Category.comp_id, Category.id_comp, SymmetricCategory.symmetry_assoc]

end SerrePositivity.KST.SConstruction

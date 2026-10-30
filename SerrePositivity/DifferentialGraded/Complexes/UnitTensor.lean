module
public import SerrePositivity.DifferentialGraded.Complexes.Unit
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensorLinear

/-! # 単位からの射の tensor と次数零評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- 単位からの射 f,g の tensor を、単位の対角と合成して 1 で評価する。
閉次数零射の合成と元の合成を比較する入口。 -/
lemma unit_tensor_apply {P Q : Complex A} (f : 𝟙_ (Complex A) ⟶ P)
    (g : 𝟙_ (Complex A) ⟶ Q) :
    (((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g)).f 0) (1 : A) =
      ιTensorObj P Q 0 0 0 rfl ((cycleFromUnit P f).val ⊗ₜ[A] (cycleFromUnit Q g).val) := by
  change ((leftUnitor' (𝟙_ (Complex A))).inv 0 ≫ (f ⊗ₘ g).f 0) (1 : A) = _
  rw [leftUnitor'_inv, Category.assoc, Category.assoc, ι_tensorHom]
  rfl

/-- 任意の chain map は単位からの射の評価と可換。 -/
lemma cycleFromUnit_postcomp {P Q : Complex A} (f : 𝟙_ (Complex A) ⟶ P) (g : P ⟶ Q) :
    (cycleFromUnit Q (f ≫ g)).val = g.f 0 (cycleFromUnit P f).val := rfl
end SerrePositivity.DifferentialGraded

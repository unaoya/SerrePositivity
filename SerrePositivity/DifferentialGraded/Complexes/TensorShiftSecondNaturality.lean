module
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
/-!
概要：左 tensor shift 比較の、シフトしない第二複体に関する自然性を公開する。
方針：各次数の同じ tensor 生成元で左 shift の符号なし公式を照合する。
規約：全整数 shift と非有界複体を扱う。
使われ方：c′ の sphere 係数抽出と元の Hom 鎖写像の可換性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (R : Type u) [CommRing R]

lemma tensorShiftLeft_second_naturality (P : Complex R) {K L : Complex R}
    (g : K ⟶ L) (s : ℤ) :
    (𝟙 (P⟦s⟧) ⊗ₘ g) ≫ (SerrePositivity.cochainTensorShiftLeft P L s).hom =
      (SerrePositivity.cochainTensorShiftLeft P K s).hom ≫ (𝟙 P ⊗ₘ g)⟦s⟧' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro b c hbc
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (SerrePositivity.cochainTensorShiftLeft P L s).hom.f n
    ((𝟙 (P⟦s⟧) ⊗ₘ g).f n
      (ιTensorObj (P⟦s⟧) K b c n hbc (x ⊗ₜ[R] y))) =
    ((𝟙 P ⊗ₘ g)⟦s⟧').f n
      ((SerrePositivity.cochainTensorShiftLeft P K s).hom.f n
        (ιTensorObj (P⟦s⟧) K b c n hbc (x ⊗ₜ[R] y)))
  rw [tensorMap_apply, tensorShiftLeft_apply, tensorShiftLeft_apply]
  change _ = (𝟙 P ⊗ₘ g).f (n + s) _
  rw [tensorMap_apply]
  rfl

end SerrePositivity.DifferentialGraded

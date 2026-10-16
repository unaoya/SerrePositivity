module
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality

/-! # 左の閉零写像を後で作用させる次数0 tensor表示 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorZeroCochain_ofHom_left {P P' Q Q' : Complex A}
    (F : P ⟶ P') (g : Cochain Q Q' 0) :
    tensorZeroCochain (Cochain.ofHom F) g =
      ((tensorLeftHom P Q Q').f 0 g).comp (Cochain.ofHom (F ▷ Q')) (zero_add 0) := by
  rw [tensorZeroCochain, tensorRightHom_ofHom]
  exact (tensorLeftHom_cochain_naturality F Q Q' 0 g).symm

end SerrePositivity.DifferentialGraded

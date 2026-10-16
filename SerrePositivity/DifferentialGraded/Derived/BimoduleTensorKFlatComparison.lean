module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorMaps
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleKFlatQuasiIso

/-! # 右相対K-flat因子間の準同型による導来合成の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {Q Q' : BimoduleCategory A C E}

def composeWithKFlatIso
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    composeWith A B C E Q ⋙ bimoduleToDerived A B E ≅
      composeWith A B C E Q' ⋙ bimoduleToDerived A B E := by
  let a := whiskerRight (composeWithMap A B C E g) (bimoduleToDerived A B E)
  haveI : ∀ P, IsIso (a.app P) := fun P => bimoduleToDerived_inverts A B E _
    (composeMap_second_kFlat_quasiIso A B C E P hQ hQ' g hg)
  haveI : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

@[simp]
lemma composeWithKFlatIso_hom (hQ hQ' g hg) :
    (composeWithKFlatIso A B C E (Q := Q) (Q' := Q') hQ hQ' g hg).hom =
      whiskerRight (composeWithMap A B C E g) (bimoduleToDerived A B E) := rfl

def derivedComposeWithKFlatIso
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    derivedComposeWith A B C E Q hQ ≅ derivedComposeWith A B C E Q' hQ' :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (composeWith A B C E Q ⋙ bimoduleToDerived A B E)
    (composeWith A B C E Q' ⋙ bimoduleToDerived A B E)
    (derivedComposeWith A B C E Q hQ) (derivedComposeWith A B C E Q' hQ')
    (composeWithKFlatIso A B C E hQ hQ' g hg)

@[simp]
lemma derivedComposeWithKFlatIso_hom (hQ hQ' g hg) :
    (derivedComposeWithKFlatIso A B C E (Q := Q) (Q' := Q') hQ hQ' g hg).hom =
      derivedComposeWithMap A B C E hQ hQ' g := rfl

lemma derivedComposeWithKFlatIso_id
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    derivedComposeWithKFlatIso A B C E hQ hQ (𝟙 Q)
      ((BimoduleCategory.quasiIso A C E).id_mem Q) = Iso.refl _ := by
  apply Iso.ext
  rw [derivedComposeWithKFlatIso_hom, derivedComposeWithMap_id]
  rfl

lemma derivedComposeWithKFlatIso_trans {Q'' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hQ'' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q''))
    (g : Q ⟶ Q') (h : Q' ⟶ Q'')
    (hg : BimoduleCategory.quasiIso A C E g) (hh : BimoduleCategory.quasiIso A C E h) :
    derivedComposeWithKFlatIso A B C E hQ hQ' g hg ≪≫
      derivedComposeWithKFlatIso A B C E hQ' hQ'' h hh =
    derivedComposeWithKFlatIso A B C E hQ hQ'' (g ≫ h)
      ((BimoduleCategory.quasiIso A C E).comp_mem g h hg hh) := by
  apply Iso.ext
  simp only [Iso.trans_hom, derivedComposeWithKFlatIso_hom]
  exact (derivedComposeWithMap_comp A B C E hQ hQ' hQ'' g h).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor

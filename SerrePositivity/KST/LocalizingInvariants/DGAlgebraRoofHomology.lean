module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveRoofValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoofNaturality

/-!
概要：実代数 roof のホモロジー作用を、その実分母の逆を使って定義する。
方針：忘却・ホモロジーの合成関手が全準同型を反転することを既存の roof 評価に渡す。
規約：任意の整数次数。使われ方：候補 roof の元の π₂ 作用の検証。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

def algebraHomologyFunctor (z : ℤ) : Mon (Complex R) ⥤ ModuleCat R :=
  Mon.forget (Complex R) ⋙ homologyFunctor (ModuleCat R) (.up ℤ) z

lemma algebraHomologyFunctor_invertsQuasiIsos (z : ℤ) :
    InvertsQuasiIsos R (algebraHomologyFunctor R z) := by
  intro A B f hf
  have := hf
  change IsIso (homologyMap f.hom z)
  infer_instance

namespace SurjectiveRoof
variable {A B C : Mon (Complex R)} (r : SurjectiveRoof R A B) (s : SurjectiveRoof R B C) (z : ℤ)

def homologyValue : A.X.homology z ⟶ B.X.homology z :=
  value R (algebraHomologyFunctor R z) (algebraHomologyFunctor_invertsQuasiIsos R z) r

lemma ofHom_homologyValue (f : A ⟶ B) :
    (ofHom R f).homologyValue R z = homologyMap f.hom z := ofHom_value R _ _ f

lemma comp_homologyValue : (r.comp R s).homologyValue R z =
    r.homologyValue R z ≫ s.homologyValue R z := comp_value R _ _ r s

lemma postcompose_homologyValue (f : B ⟶ C) :
    (r.postcompose R f).homologyValue R z = r.homologyValue R z ≫ homologyMap f.hom z :=
  postcompose_value R _ _ r f

lemma nonpositiveNormalization_homologyValue [A.X.IsStrictlyLE 0] :
    (r.nonpositiveNormalization R).homologyValue R z = r.homologyValue R z :=
  nonpositiveNormalization_value R r _ _

lemma inverse_homologyValue_comp (f : A ⟶ B) (hf : QuasiIso f.hom) :
    (ofQuasiIsoInverse R f hf).homologyValue R z ≫ homologyMap f.hom z = 𝟙 _ :=
  inverse_value_comp R f (algebraHomologyFunctor R z)
    (algebraHomologyFunctor_invertsQuasiIsos R z) hf

lemma comp_inverse_homologyValue (f : A ⟶ B) (hf : QuasiIso f.hom) :
    homologyMap f.hom z ≫ (ofQuasiIsoInverse R f hf).homologyValue R z = 𝟙 _ :=
  comp_inverse_value R f (algebraHomologyFunctor R z)
    (algebraHomologyFunctor_invertsQuasiIsos R z) hf

end SurjectiveRoof
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

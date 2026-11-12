module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseConnectiveRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantQuasiIso

/-!
概要：元の実 roof と準同型の実逆 span を、元の IsKConnective 不変量値の射へ送る。
方針：元の invariantFunctor の connective 準同型反転へ、実 roof の合成と三角形を渡す。
規約：元の BF 値と元の射の類を使う。使われ方：実一切断の逆と値の塔の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1})
  {k : ℤ} (h : IsKConnective R Φ k) {A B C : Mon (Complex R)}

def IsKConnective.roofValue (hA : IsConnective R A) (r : SurjectiveRoof R A B) :
    SpectrumHo.obj (invariantValue R Φ A) ⟶ SpectrumHo.obj (invariantValue R Φ B) :=
  SurjectiveRoof.connectiveValue R (invariantFunctor R Φ)
    (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ) hA r

lemma IsKConnective.roofValue_comp (hA : IsConnective R A) (hB : IsConnective R B)
    (r : SurjectiveRoof R A B) (s : SurjectiveRoof R B C) :
    h.roofValue R Φ hA (r.comp R s) = h.roofValue R Φ hA r ≫ h.roofValue R Φ hB s :=
  SurjectiveRoof.comp_connectiveValue R (invariantFunctor R Φ)
    (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ) hA hB r s

lemma IsKConnective.inverseRoofValue_comp (f : A ⟶ B) (hf : QuasiIso f.hom)
    (hB : IsConnective R B) :
    h.roofValue R Φ hB (SurjectiveRoof.ofQuasiIsoInverse R f hf) ≫
      SpectrumHo.hom (invariantMap R Φ f) = 𝟙 _ :=
  SurjectiveRoof.inverse_connectiveValue_comp R f (invariantFunctor R Φ)
    (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ) hB hf

lemma IsKConnective.comp_inverseRoofValue (f : A ⟶ B) (hf : QuasiIso f.hom)
    (hB : IsConnective R B) :
    SpectrumHo.hom (invariantMap R Φ f) ≫
      h.roofValue R Φ hB (SurjectiveRoof.ofQuasiIsoInverse R f hf) = 𝟙 _ :=
  SurjectiveRoof.comp_inverse_connectiveValue R f (invariantFunctor R Φ)
    (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ) hB hf

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

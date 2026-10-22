module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseConnectiveRoof

/-!
概要：実準同型逆 roof の評価は、元の可換な脚を保つ。
方針：既存の逆三角形に元の脚を後合成する。
規約：一般分数表示を使わない。connective 準同型反転版も保持。使われ方：実候補の底の計算。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (f : A ⟶ B)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)
  (hf : QuasiIso f.hom) (a : A ⟶ C) (b : B ⟶ C) (h : f ≫ b = a)

include h in
lemma inverse_value_naturality (hL : InvertsQuasiIsos R L) :
    value R L hL (ofQuasiIsoInverse R f hf) ≫ L.map a = L.map b := by
  rw [← h, L.map_comp, ← Category.assoc, inverse_value_comp, Category.id_comp]

include h in
lemma inverse_connectiveValue_naturality (hL : InvertsConnectiveQuasiIsos R L)
    (hB : IsConnective R B) :
    connectiveValue R L hL hB (ofQuasiIsoInverse R f hf) ≫ L.map a = L.map b := by
  rw [← h, L.map_comp, ← Category.assoc, inverse_connectiveValue_comp, Category.id_comp]

lemma value_eq_inverse_denominator (hL : InvertsQuasiIsos R L) (r : SurjectiveRoof R A B) :
    value R L hL (ofQuasiIsoInverse R r.denominator r.denominator_quasiIso) ≫ L.map r.numerator =
      value R L hL r := by
  have := hL r.denominator r.denominator_quasiIso
  apply (cancel_epi (L.map r.denominator)).1
  rw [← Category.assoc, comp_inverse_value, Category.id_comp, denominator_value]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof

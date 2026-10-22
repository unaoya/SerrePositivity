module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSurjectiveRoof

/-!
概要：構成した元の実 roof を、準同型を反転する関手の元の射として評価する。
方針：分母の逆と分子の像を合成し、元の pullback 条件から合成の評価を証明する。
規約：roof の存在と局所化の射を同一視しない。使われ方：構成済みの逆の抽出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
variable (R : Type u) [CommRing R] {D : Type v} [Category.{w} D]
  (L : Mon (Complex R) ⥤ D) (hL : InvertsQuasiIsos R L)
  {A B C : Mon (Complex R)}

def value (r : SurjectiveRoof R A B) : L.obj A ⟶ L.obj B := by
  have := hL r.denominator r.denominator_quasiIso
  exact inv (L.map r.denominator) ≫ L.map r.numerator

lemma denominator_value (r : SurjectiveRoof R A B) :
    L.map r.denominator ≫ value R L hL r = L.map r.numerator := by
  have := hL r.denominator r.denominator_quasiIso
  change L.map r.denominator ≫ (inv (L.map r.denominator) ≫ L.map r.numerator) = _
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

lemma ofHom_value (f : A ⟶ B) : value R L hL (ofHom R f) = L.map f := by
  have := hL (𝟙 A) (by change QuasiIso (𝟙 A.X); infer_instance)
  change inv (L.map (𝟙 A)) ≫ L.map f = L.map f
  simp only [L.map_id, IsIso.inv_id, Category.id_comp]

lemma postcompose_value (r : SurjectiveRoof R A B) (b : B ⟶ C) :
    value R L hL (postcompose R r b) = value R L hL r ≫ L.map b := by
  have := hL r.denominator r.denominator_quasiIso
  change inv (L.map r.denominator) ≫ L.map (r.numerator ≫ b) =
    (inv (L.map r.denominator) ≫ L.map r.numerator) ≫ L.map b
  rw [L.map_comp, Category.assoc]

lemma comp_value (r : SurjectiveRoof R A B) (s : SurjectiveRoof R B C) :
    value R L hL (comp R r s) = value R L hL r ≫ value R L hL s := by
  have := hL (comp R r s).denominator (comp R r s).denominator_quasiIso
  let p := MonoidPullback.fst r.numerator s.denominator
  let q := MonoidPullback.snd r.numerator s.denominator
  have he : L.map p ≫ L.map r.numerator = L.map q ≫ L.map s.denominator := by
    rw [← L.map_comp, ← L.map_comp]
    exact congrArg L.map (MonoidPullback.condition r.numerator s.denominator)
  have hc : L.map (comp R r s).denominator ≫ (value R L hL r ≫ value R L hL s) =
      L.map (comp R r s).numerator := by
    calc
      _ = L.map p ≫ (L.map r.denominator ≫ value R L hL r) ≫ value R L hL s := by
        change L.map (p ≫ r.denominator) ≫ _ = _
        simp only [L.map_comp, Category.assoc]
      _ = L.map p ≫ L.map r.numerator ≫ value R L hL s := by rw [denominator_value]
      _ = L.map q ≫ (L.map s.denominator ≫ value R L hL s) := by
        rw [← Category.assoc, he, Category.assoc]
      _ = L.map q ≫ L.map s.numerator := by rw [denominator_value]
      _ = _ := (L.map_comp _ _).symm
  apply (cancel_epi (L.map (comp R r s).denominator)).1
  exact (denominator_value R L hL (comp R r s)).trans hc.symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof

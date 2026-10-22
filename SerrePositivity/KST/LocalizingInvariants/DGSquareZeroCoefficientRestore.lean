module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessCoefficient

/-!
概要：共通底の係数表示を、指定した元の底上の平方零標的へ戻す。
方針：実係数同型の逆と元の底変更射を合成し、係数射の三角形を保持する。
規約：任意の係数射の可逆性は要求しない。使われ方：fixed 模型の元の標的比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)} (q : A ⟶ B)
  (N : Bimod B B) {M L : Bimod A A} (e : bimoduleRestrict q N ≅ M)

def coefficientRestore : algebra A M ⟶ algebra B N :=
  (coefficientIso A e).inv ≫ baseChangeMap q N

lemma coefficientRestore_triangle : (coefficientIso A e).hom ≫
    coefficientRestore q N e = baseChangeMap q N := by
  rw [coefficientRestore, Iso.hom_inv_id_assoc]

lemma coefficientRestore_projection : coefficientRestore q N e ≫ projection B N =
    projection A M ≫ q := by
  change ((coefficientIso A e).inv ≫ baseChangeMap q N) ≫ _ = _
  rw [Category.assoc, baseChangeMap_projection, ← Category.assoc]
  change (coefficientMap A e.inv ≫ projection A (bimoduleRestrict q N)) ≫ q = _
  rw [coefficientMap_projection]

lemma coefficientRestore_zeroSection : zeroSection A M ≫ coefficientRestore q N e =
    q ≫ zeroSection B N := by
  rw [coefficientRestore, ← Category.assoc]
  change (zeroSection A M ≫ coefficientMap A e.inv) ≫ baseChangeMap q N = _
  rw [zeroSection_coefficientMap]
  exact zeroSection_mapOver q (bimoduleRestrict q N) N (𝟙 _)

lemma coefficientRestore_coefficient (m : L ⟶ bimoduleRestrict q N) :
    coefficientMap A (m ≫ e.hom) ≫ coefficientRestore q N e =
      coefficientMap A m ≫ baseChangeMap q N := by
  rw [← coefficientMap_comp, Category.assoc]
  change coefficientMap A m ≫ (coefficientIso A e).hom ≫ coefficientRestore q N e = _
  rw [coefficientRestore_triangle]

end SerrePositivity.KST.LocalizingInvariants.SquareZero

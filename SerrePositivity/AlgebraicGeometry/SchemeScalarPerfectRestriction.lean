module

public import SerrePositivity.AlgebraicGeometry.SchemeScalarMorphism
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitMap

/-!
概要：Γ–Specの同じ標準同型による基底の係数移送を実際の制限と照合する。
方針：元の単位・余単位の恒等式とFrobenius順極限の合成則を使う。
規約：元の構造射のappLEと同じ基底環・切断環を保持する。
使われ方：矩形の増大行と幾何的nerveのΓの同じ基底の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
variable {R : Type u} [CommRing R] {N : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- 元のスカラーの制限は、Γ–Specで係数を戻すと同じappLEになる。 -/
theorem schemeScalarPerfectRestriction_cancel
    (f : N ⟶ Spec (CommRingCat.of R)) (W : N.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (hS : (p : Γ(Spec (CommRingCat.of R), ⊤)) = 0)
    (hW : (p : N.presheaf.obj (op W)) = 0)
    (z : FrobeniusDirectLimit Γ(Spec (CommRingCat.of R), ⊤) p hp hS) :
    frobeniusDirectLimitMap p hp hR hW
      ((N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op).hom.comp (schemeScalarHom N f))
      (frobeniusDirectLimitMap p hp hS hR (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom z) =
      frobeniusDirectLimitMap p hp hS hW (f.appLE ⊤ W (by simp)).hom z := by
  let β := (N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op).hom.comp
    (schemeScalarHom N f)
  have hc : CommRingCat.ofHom β = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      f.appLE ⊤ W (by simp) := by
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) ≫
      N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op = _
    rw [Category.assoc]
    rfl
  have he : β.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom =
      (f.appLE ⊤ W (by simp)).hom := by
    have hec : (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom β =
        f.appLE ⊤ W (by simp) := by
      rw [hc, Iso.hom_inv_id_assoc]
    exact congrArg (fun m ↦ m.hom) hec
  have hm := congrArg (fun m ↦ m z) (frobeniusDirectLimitMap_comp p hp hS hR
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hW β)
  rw [he] at hm
  exact hm

end SerrePositivity.AlgebraicGeometry

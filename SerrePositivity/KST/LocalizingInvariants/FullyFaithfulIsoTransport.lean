module

public import SerrePositivity.KST.LocalizingInvariants.FunctorHomArrowTransport
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
概要：充満忠実関手の像の指定同型を、指定端点の元の圏へ持ち上げる。
方針：端点の等号で同型を輸送し、充満忠実性の逆像の像を計算する。
規約：像の射は端点を含む Arrow 等号で保持。使われ方：右辺を固定する相対 fiber 比較。
-/

@[expose] public section
noncomputable section
universe u v u' v'
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  (F : C ⥤ D) (hF : F.FullyFaithful) {a b : C} {x y : D}
  (hx : F.obj a = x) (hy : F.obj b = y) (e : x ≅ y)

def transportedPreimageIso : a ≅ b :=
  hF.preimageIso (eqToIso hx ≪≫ e ≪≫ eqToIso hy.symm)

lemma transportedPreimageIso_map_arrow :
    Arrow.mk (F.map (transportedPreimageIso F hF hx hy e).hom) = Arrow.mk e.hom := by
  rw [transportedPreimageIso, Functor.FullyFaithful.preimageIso_hom, hF.map_preimage]
  simp only [Iso.trans_hom, eqToIso.hom]
  exact (arrow_mk_eqToHom_comp hx (e.hom ≫ eqToHom hy.symm)).trans
    (arrow_mk_comp_eqToHom e.hom hy.symm)

end SerrePositivity.KST.LocalizingInvariants

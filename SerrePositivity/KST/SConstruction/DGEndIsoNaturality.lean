module
public import SerrePositivity.KST.SConstruction.DGEndIsoConjugation

/-! # 全 Hom の自然な閉同型と End 共役の回収
概要：同じ閉同型に関する全 Hom 自然性から、共役後の元の作用を回収する。
方針：前後合成の交換と、元の閉同型の逆律を使う。
規約：全次数の鎖写像の等号。使われ方：代表加群の延長比較を通す元の dg 射の回収。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D]
  {x y : ClosedCategory R D} (e : x ≅ y)

/-- 同じ閉同型に全 Hom 自然なら、元の End 作用を共役により厳密に回収する。 -/
lemma dgEndIsoHom_of_naturality {K : Complex R}
    (f : K ⟶ (x ⟶[Complex R] x)) (g : K ⟶ (y ⟶[Complex R] y))
    (h : f ≫ eHomWhiskerLeft (Complex R) x e.hom =
      g ≫ eHomWhiskerRight (Complex R) e.hom y) :
    f ≫ dgEndIsoHom R e = g := by
  unfold dgEndIsoHom
  rw [← eHom_whisker_exchange (Complex R) e.inv e.hom, ← Category.assoc, h, Category.assoc,
    ← eHomWhiskerRight_comp, e.inv_hom_id, eHomWhiskerRight_id, Category.comp_id]

end SerrePositivity.KST.SConstruction

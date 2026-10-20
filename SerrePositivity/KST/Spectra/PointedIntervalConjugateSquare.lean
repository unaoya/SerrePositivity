module

public import SerrePositivity.KST.Spectra.PointedIntervalCoordinateNaturality
public import SerrePositivity.KST.Spectra.SquareBoundaryFamilies

/-!
概要：自己作用の元の自然性正方形を、同型による同じ前後合成の座標へ移す。
方針：元の二次元射に一つの座標射を後合成し、同じ二つの実辺を照合する。
規約：辺や正方形を再選択しない。使われ方：普遍源の自然性を loop 座標へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

variable {A A' B B' : PointedSimplicialSet.{u}} {a b : A ⟶ A} {c d : B ⟶ B}
  (P : VerticalPath (PointedObject.toPoint A) a b)
  (Q : VerticalPath (PointedObject.toPoint B) c d) (v : A ⟶ B)
  (H : SSet.Homotopy ((P.basedPost v).path) ((Q.pre v).path))
  (e : A ≅ A') (f : B ≅ B') (w : A' ⟶ B') (hc : e.hom ≫ w = v ≫ f.hom)

include hc in
/-- 同じ座標の逆射も、元の前後合成と厳密に可換。 -/
lemma conjugateSquare_inverse : w ≫ f.inv = e.inv ≫ v := by
  apply (cancel_mono f.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hc, Iso.inv_hom_id_assoc]

/-- 元の二次元射そのものを同型で共役した、同じ実辺の自然性正方形。 -/
def conjugateSquare :
    SSet.Homotopy ((((P.basedPost e.hom).pre e.inv).basedPost w).path)
      ((((Q.basedPost f.hom).pre f.inv).pre w).path) where
  h := H.h ≫ (coordinateMap e.inv f.hom).right
  h₀ := by
    rw [← Category.assoc, H.h₀]
    exact (P.coordinate_post_path e f v w hc).symm
  h₁ := by
    rw [← Category.assoc, H.h₁]
    exact (Q.coordinate_pre_path e f v w (conjugateSquare_inverse v e f w hc)).symm
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

end SerrePositivity.KST.Spectra.PointedMapping

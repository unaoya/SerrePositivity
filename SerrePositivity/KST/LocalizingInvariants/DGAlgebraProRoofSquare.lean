module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProRoof
public import SerrePositivity.KST.LocalizingInvariants.ProInverseSquareTriangles

/-!
概要：各段の準同型比較を保つ正方形に沿って、実 dg roof の pro 逆を反映する。
方針：元の右比較・指定 roof・左比較の MappingPath 逆を実 pullback で合成する。
規約：span は反転関手より先に選ぶ。使われ方：元の Postnikov 射への roof 移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision SurjectiveRoof
variable (R : Type u) [CommRing R] {D : Type v} [Category.{w} D]
  {X Y X' Y' : Tower (Mon (Complex R))}

lemma HasSurjectiveRoofProInverse.of_square (f : LevelHom X Y) (g : LevelHom X' Y')
    (a : LevelHom X X') (b : LevelHom Y Y') (hs : f.comp b = a.comp g)
    (ha : ∀ i, QuasiIso (a.app i).hom) (hb : ∀ i, QuasiIso (b.app i).hom)
    (hg : HasSurjectiveRoofProInverse R (D := D) g) :
    HasSurjectiveRoofProInverse R (D := D) f := by
  intro i
  obtain ⟨m, hi, r, hr⟩ := hg i
  let q := ofQuasiIsoInverse R (a.app i) (ha i)
  let t := comp R (comp R (ofHom R (b.app m)) r) q
  refine ⟨m, hi, t, ?_⟩
  intro L hL
  have := hL (b.app i) (hb i)
  have : Mono ((b.map L).app i) := by
    change Mono (L.map (b.app i))
    infer_instance
  have he : SurjectiveRoof.value R L hL t =
      (L.map (b.app m) ≫ SurjectiveRoof.value R L hL r) ≫
        SurjectiveRoof.value R L hL q := by
    dsimp only [t]
    rw [comp_value, comp_value, ofHom_value]
  rw [he]
  apply TowerDiagram.inverse_square_triangles (f.map L) (g.map L) (a.map L) (b.map L)
    ?_ hi (SurjectiveRoof.value R L hL r) (hr L hL).1 (hr L hL).2 (SurjectiveRoof.value R L hL q)
    (comp_inverse_value R (a.app i) L hL (ha i))
    (inverse_value_comp R (a.app i) L hL (ha i))
  rw [← TowerDiagram.levelHom_map_comp, ← TowerDiagram.levelHom_map_comp, hs]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

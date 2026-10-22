module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseConnectiveRoof
public import SerrePositivity.KST.LocalizingInvariants.ProInverseSquareTriangles

/-!
概要：connective 準同型の反転だけで正方形に沿う実 dg roof の逆を反映する。
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

lemma HasConnectiveRoofProInverse.of_square (f : LevelHom X Y) (g : LevelHom X' Y')
    (a : LevelHom X X') (b : LevelHom Y Y') (hs : f.comp b = a.comp g)
    (ha : ∀ i, QuasiIso (a.app i).hom) (hb : ∀ i, QuasiIso (b.app i).hom)
    (hY : ∀ i, IsConnective R (Y.obj i))
    (hX' : ∀ i, IsConnective R (X'.obj i)) (hY' : ∀ i, IsConnective R (Y'.obj i))
    (hg : HasConnectiveRoofProInverse R (D := D) g hY') :
    HasConnectiveRoofProInverse R (D := D) f hY := by
  intro i
  obtain ⟨m, hi, r, hr⟩ := hg i
  let q := ofQuasiIsoInverse R (a.app i) (ha i)
  let t := comp R (comp R (ofHom R (b.app m)) r) q
  refine ⟨m, hi, t, ?_⟩
  intro L hL
  have := hL (hY i) (hY' i) (b.app i) (hb i)
  have : Mono ((b.map L).app i) := by
    change Mono (L.map (b.app i))
    infer_instance
  have he : SurjectiveRoof.connectiveValue R L hL (hY m) t =
      (L.map (b.app m) ≫ SurjectiveRoof.connectiveValue R L hL (hY' m) r) ≫
        SurjectiveRoof.connectiveValue R L hL (hX' i) q := by
    dsimp only [t]
    rw [comp_connectiveValue R L hL (hY m) (hX' i),
      comp_connectiveValue R L hL (hY m) (hY' m), ofHom_connectiveValue]
  rw [he]
  apply TowerDiagram.inverse_square_triangles (f.map L) (g.map L) (a.map L) (b.map L)
    ?_ hi (SurjectiveRoof.connectiveValue R L hL (hY' m) r) (hr L hL).1 (hr L hL).2
    (SurjectiveRoof.connectiveValue R L hL (hX' i) q)
    (comp_inverse_connectiveValue R (a.app i) L hL (hX' i) (ha i))
    (inverse_connectiveValue_comp R (a.app i) L hL (hX' i) (ha i))
  rw [← TowerDiagram.levelHom_map_comp, ← TowerDiagram.levelHom_map_comp, hs]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

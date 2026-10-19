module

public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimit
public import SerrePositivity.KST.Spectra.PointedWeightedEndCotensorWeight
public import SerrePositivity.KST.Spectra.PointedWeightedEndBifunctor

/-!
概要：重みへの前合成は end の loop 交換の逆と随伴構造射に可換。
方針：loop 交換の自然性を同型で消去し、係数の後合成との交換を合成する。
規約：任意の小圏と重みについての厳密な射の等式。
使われ方：Goerss–Jardine VIII §1、HA §1.4.2。通常 Tot と BK end の列の比較。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedWeightedEnd
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I] {W V : I ⥤ SSet.{u}}

/-- loop 交換の逆と重みの前合成の厳密な可換式。 -/
lemma preMap_cotensorIso_inv (A : PointedSimplicialSet.{u}) (θ : W ⟶ V)
    (D : I ⥤ PointedSimplicialSet.{u}) :
    preMap θ (D ⋙ ihom A) ≫ (cotensorIso A W D).inv =
    (cotensorIso A V D).inv ≫ (ihom A).map (preMap θ D) := by
  apply (cancel_mono (cotensorIso A W D).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    cotensorIso_preMap, Iso.inv_hom_id_assoc]

/-- 重みの前合成は任意の Kan 列の end の随伴構造と可換。 -/
lemma preMap_adjoint (θ : W ⟶ V) (D : I ⥤ KanSequence.{u}) (n : ℕ) :
    preMap θ (KanSequence.levelDiagram D n) ≫
      (map W (KanSequence.adjointTransformation D n) ≫
        (cotensorIso PointedSimplicialSet.circle.{u} W
          (KanSequence.levelDiagram D (n + 1))).inv) =
    (map V (KanSequence.adjointTransformation D n) ≫
      (cotensorIso PointedSimplicialSet.circle.{u} V
        (KanSequence.levelDiagram D (n + 1))).inv) ≫
      (ihom PointedSimplicialSet.circle.{u}).map
        (preMap θ (KanSequence.levelDiagram D (n + 1))) := by
  rw [← Category.assoc, ← map_preMap, Category.assoc, preMap_cotensorIso_inv,
    ← Category.assoc]

end
end SerrePositivity.KST.Spectra.PointedWeightedEnd

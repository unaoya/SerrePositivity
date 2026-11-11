module

public import SerrePositivity.KST.Spectra.SequenceIntervalRectification
public import SerrePositivity.KST.Spectra.KanSequenceMappingFunctor

/-!
概要：元の全列区間へ厳密な列射を後合成し、同じ両端境界を保つ。
方針：自由区間・境界の mapping の自然性と、境界の両端評価を使う。
規約：新しい区間を選ばない。使われ方：源区間を全パラメータの loop 作用へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra

private lemma pointedIhom_map (A : PointedSimplicialSet.{u})
    {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    (ihom A).map p = PointedObject.basedHomMap A p := rfl

private lemma closedUnitEvaluation_natural {C : Type*} [Category C]
    [MonoidalCategory C] [MonoidalClosed C] {B Y Z : C} (p : Y ⟶ Z) (e : 𝟙_ C ⟶ B) :
    (ihom B).map p ≫ ((MonoidalClosed.pre e).app Z ≫ (unitIsoSelf (X := Z)).hom) =
      ((MonoidalClosed.pre e).app Y ≫ (unitIsoSelf (X := Y)).hom) ≫ p := by
  have hu : (ihom (𝟙_ C)).map p ≫ (unitIsoSelf (X := Z)).hom =
      (unitIsoSelf (X := Y)).hom ≫ p := (unitNatIso (C := C)).inv.naturality p
  rw [← Category.assoc, (MonoidalClosed.pre e).naturality p, Category.assoc, hu,
    Category.assoc]

/-- 境界の終点評価は、標的の後合成について自然。 -/
lemma freeBoundaryHomEnd_natural {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} p ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Z =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Y ≫ p := by
  simpa only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd, ← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre,
    pointedIhom_map, PointedObject.ihom_obj_eq_basedHom] using
    closedUnitEvaluation_natural p _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd.{u}

/-- 境界の始点評価も、標的の後合成について自然。 -/
lemma freeBoundaryHomStart_natural {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) :
    PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} p ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Z =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Y ≫ p := by
  simpa only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart, ← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre,
    pointedIhom_map, PointedObject.ihom_obj_eq_basedHom] using
    closedUnitEvaluation_natural p _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart.{u}

/-- 自由境界の元の両端族は、同じ後合成の両端族へ厳密に移る。 -/
lemma freeBoundaryHomPair_post {T Y Z : PointedSimplicialSet.{u}}
    (f g : T ⟶ Y) (p : Y ⟶ Z) :
    freeBoundaryHomPair f g ≫ PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} p =
      freeBoundaryHomPair (f ≫ p) (g ≫ p) := by
  apply freeBoundaryHom_hom_ext
  · rw [Category.assoc]
    rw [freeBoundaryHomEnd_natural]
    rw [← Category.assoc, freeBoundaryHomPair_end, freeBoundaryHomPair_end]
  · rw [Category.assoc]
    rw [freeBoundaryHomStart_natural]
    rw [← Category.assoc, freeBoundaryHomPair_start, freeBoundaryHomPair_start]

namespace KanSequence

/-- 同じ全列区間へ列射を後合成し、元の両端を後合成した全列区間を得る。 -/
def StrictInterval.post {X Y Z : KanSequence.{u}} {f g : Hom X Y}
    (H : StrictInterval f g) (p : Hom Y Z) : StrictInterval (f.comp p) (g.comp p) where
  hom := H.hom.comp (mappingPost _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} p)
  boundary n := by
    change (H.hom.app n ≫ PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} (p.app n)) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u} (Z.level n).space =
      freeBoundaryHomPair (f.app n ≫ p.app n) (g.app n ≫ p.app n)
    have hn := (MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u}).naturality (p.app n)
    simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
    rw [Category.assoc]
    erw [hn]
    rw [← Category.assoc]
    have hb := H.boundary n
    change H.hom.app n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion.{u} (Y.level n).space =
      freeBoundaryHomPair (f.app n) (g.app n) at hb
    rw [hb, pointedIhom_map, freeBoundaryHomPair_post]

end KanSequence
end SerrePositivity.KST.Spectra

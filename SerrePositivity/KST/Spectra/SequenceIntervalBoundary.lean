module

public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreeIntervalBoundary
public import SerrePositivity.KST.Spectra.MappingKanSequence

/-!
概要：二つの厳密な列射を自由区間の境界上の同じ厳密な列射へ束ねる。
方針：境界内部 Hom の実際の積表示を使い、両端評価で構造可換式を検査する。
規約：段ごとの区間の存在から整合性は仮定しない。使われ方：全列区間の相対延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra

/-- 境界からの Hom に値を取る射は、両端への評価で決まる。 -/
lemma freeBoundaryHom_hom_ext {T Y : PointedSimplicialSet.{u}}
    {f g : T ⟶ PointedObject.basedHom _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} Y}
    (he : f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Y = g ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Y)
    (hs : f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Y = g ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Y) : f = g := by
  apply Under.UnderMorphism.ext
  apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIsLimit Y).hom_ext
  rintro ⟨i⟩
  cases i
  · exact congrArg Under.Hom.right he
  · exact congrArg Under.Hom.right hs

/-- 二つの点つき射を、同じ両端を持つ境界内部 Hom の族へ束ねる。 -/
def freeBoundaryHomPair {T Y : PointedSimplicialSet.{u}} (f g : T ⟶ Y) :
    T ⟶ PointedObject.basedHom _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} Y := by
  let r := prod.lift g.right f.right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).inv
  refine Under.homMk r ?_
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).hom).1
  apply prod.hom_ext
  · change T.hom ≫ (prod.lift g.right f.right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).inv) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).hom ≫ prod.fst =
      (PointedObject.basedHom _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary Y).hom ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).hom ≫ prod.fst
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [prod.lift_fst, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_fst, Under.w, Under.w]
  · change T.hom ≫ (prod.lift g.right f.right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).inv) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).hom ≫ prod.snd =
      (PointedObject.basedHom _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary Y).hom ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).hom ≫ prod.snd
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [prod.lift_snd, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_snd, Under.w, Under.w]

/-- 境界の終点は、指定した第二の射そのもの。 -/
@[reassoc]
lemma freeBoundaryHomPair_end {T Y : PointedSimplicialSet.{u}} (f g : T ⟶ Y) :
    freeBoundaryHomPair f g ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd Y = g := by
  apply Under.UnderMorphism.ext
  change (prod.lift g.right f.right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).inv) ≫ _ = _
  calc
    _ = (prod.lift g.right f.right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).inv) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).hom ≫ prod.fst :=
      congrArg ((prod.lift g.right f.right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).inv) ≫ ·)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_fst Y).symm
    _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_assoc, prod.lift_fst]

/-- 境界の始点は、指定した第一の射そのもの。 -/
@[reassoc]
lemma freeBoundaryHomPair_start {T Y : PointedSimplicialSet.{u}} (f g : T ⟶ Y) :
    freeBoundaryHomPair f g ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart Y = f := by
  apply Under.UnderMorphism.ext
  change (prod.lift g.right f.right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).inv) ≫ _ = _
  calc
    _ = (prod.lift g.right f.right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).inv) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).hom ≫ prod.snd :=
      congrArg ((prod.lift g.right f.right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso Y).inv) ≫ ·)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEvaluationIso_snd Y).symm
    _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_assoc, prod.lift_snd]

namespace KanSequence

/-- 自由境界上の列からの終点評価は、元の列への厳密な射。 -/
def intervalBoundaryEnd (Y : KanSequence.{u}) : Hom (mapping _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary Y) Y :=
  (mappingPre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd Y).comp (mappingUnitEvaluation Y)

/-- 自由境界上の列からの始点評価は、元の列への厳密な射。 -/
def intervalBoundaryStart (Y : KanSequence.{u}) : Hom (mapping _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary Y) Y :=
  (mappingPre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart Y).comp (mappingUnitEvaluation Y)

/-- 二つの厳密な列射を、同じ両端を持つ厳密な境界列射へ束ねる。 -/
def intervalBoundaryPair {X Y : KanSequence.{u}} (f g : Hom X Y) :
    Hom X (mapping _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary Y) where
  app n := freeBoundaryHomPair (f.app n) (g.app n)
  comm n := by
    have he (k : ℕ) : freeBoundaryHomPair (f.app k) (g.app k) ≫
        (intervalBoundaryEnd Y).app k = g.app k := freeBoundaryHomPair_end _ _
    have hs (k : ℕ) : freeBoundaryHomPair (f.app k) (g.app k) ≫
        (intervalBoundaryStart Y).app k = f.app k := freeBoundaryHomPair_start _ _
    apply freeBoundaryHom_hom_ext
    · change _ ≫ (intervalBoundaryEnd Y).app (n + 1) =
        _ ≫ (intervalBoundaryEnd Y).app (n + 1)
      rw [Category.assoc, ← (intervalBoundaryEnd Y).comm n, ← Category.assoc,
        ← whiskerLeft_comp, he, Category.assoc, he]
      exact g.comm n
    · change _ ≫ (intervalBoundaryStart Y).app (n + 1) =
        _ ≫ (intervalBoundaryStart Y).app (n + 1)
      rw [Category.assoc, ← (intervalBoundaryStart Y).comm n, ← Category.assoc,
        ← whiskerLeft_comp, hs, Category.assoc, hs]
      exact f.comm n

end KanSequence
end SerrePositivity.KST.Spectra

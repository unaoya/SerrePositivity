module

public import SerrePositivity.InfinityCategories.F2.Ind.TwistedSourceElementsComparison
public import SerrePositivity.InfinityCategories.F2.Ind.TwistedElementsBaseChange

/-!
概要：始点固定の全族を元の共同射影の底変換へ厳密に移す往復の射。
方針：同じ twisted arrow と終点成分を保持し、引き戻しの普遍性を使う。
規約：元の全族・元の比較射を保持する。
使われ方：共同 Hom の同じ復元射を密度評価図式へ底変換する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)

/-- 同じ始点固定の比較は、共同射影の始点固定の正方形を可換にする。 -/
lemma twistedSourceElementsComparison_projection :
    twistedSourceElementsComparison p b ≫ twistedElementsProjection p =
      pullback.fst p (twistedArrowSourceProjection b) ≫
        lift (SSet.const (SSet.opObjEquiv.symm b)) (𝟙 E) := by
  apply CartesianMonoidalCategory.hom_ext
  · have ht := congrArg (fun f => f ≫ fst B.op B)
      (pullback.condition (f := twistedArrowProjection B) (g := twistedArrowSourceInclusion b))
    simp only [Category.assoc, twistedArrowProjection_fst, twistedArrowSourceInclusion,
      lift_fst, SSet.comp_const] at ht
    change pullback.fst (twistedArrowProjection B) (twistedArrowSourceInclusion b) ≫
      edgewiseLeft B = SSet.const (SSet.opObjEquiv.symm b) at ht
    simp only [Category.assoc, twistedElementsProjection, lift_fst, SSet.comp_const]
    rw [← Category.assoc, twistedSourceElementsComparison_fst, Category.assoc,
      ht, SSet.comp_const]
  · simp only [Category.assoc, twistedElementsProjection, lift_snd,
      twistedSourceElementsComparison_snd, Category.comp_id]

/-- 元の始点固定の全族から、同じ共同射影の底変換への射。 -/
def twistedSourceElementsToBaseChange : twistedSourceElements p b ⟶
    pullback (twistedElementsProjection p)
      (lift (SSet.const (SSet.opObjEquiv.symm b)) (𝟙 E)) :=
  pullback.lift (twistedSourceElementsComparison p b)
    (pullback.fst p (twistedArrowSourceProjection b))
    (twistedSourceElementsComparison_projection p b)

/-- 底変換に記録された元の twisted arrow は、指定始点を持つ。 -/
lemma twistedSourceElementsFromBaseChange_over :
    (pullback.fst (twistedElementsProjection p)
      (lift (SSet.const (SSet.opObjEquiv.symm b)) (𝟙 E)) ≫
        pullback.fst (edgewiseRight B) p) ≫ twistedArrowProjection B =
      (pullback.snd (twistedElementsProjection p)
        (lift (SSet.const (SSet.opObjEquiv.symm b)) (𝟙 E)) ≫ p) ≫
          twistedArrowSourceInclusion b := by
  have hs := congrArg (fun f => f ≫ snd B.op E)
    (pullback.condition (f := twistedElementsProjection p)
      (g := lift (SSet.const (SSet.opObjEquiv.symm b)) (𝟙 E)))
  simp only [Category.assoc, twistedElementsProjection, lift_snd, Category.comp_id] at hs
  apply CartesianMonoidalCategory.hom_ext
  · have ht := congrArg (fun f => f ≫ fst B.op E)
      (pullback.condition (f := twistedElementsProjection p)
        (g := lift (SSet.const (SSet.opObjEquiv.symm b)) (𝟙 E)))
    simpa only [Category.assoc, twistedArrowProjection_fst, twistedElementsProjection,
      lift_fst, twistedArrowSourceInclusion, SSet.comp_const] using ht
  · simp only [Category.assoc, twistedArrowProjection_snd, twistedArrowSourceInclusion,
      lift_snd, Category.comp_id]
    rw [pullback.condition, ← Category.assoc]
    exact congrArg (fun f => f ≫ p) hs

/-- 同じ共同射影の底変換から、元の始点固定の全族への射。 -/
def twistedSourceElementsFromBaseChange :
    pullback (twistedElementsProjection p)
      (lift (SSet.const (SSet.opObjEquiv.symm b)) (𝟙 E)) ⟶ twistedSourceElements p b :=
  pullback.lift (f := p) (g := twistedArrowSourceProjection b) (pullback.snd _ _)
    (pullback.lift (f := twistedArrowProjection B) (g := twistedArrowSourceInclusion b)
      (pullback.fst _ _ ≫ pullback.fst (edgewiseRight B) p)
      (pullback.snd _ _ ≫ p) (twistedSourceElementsFromBaseChange_over p b))
    (pullback.lift_snd _ _ _).symm

end SerrePositivity.InfinityCategories.F2.Ind

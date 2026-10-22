module

public import SerrePositivity.InfinityCategories.F2.Ind.TwistedSourceElementsBaseChangeMaps

/-!
概要：同じ始点固定の全族は、元の共同射影の始点固定の底変換と厳密に同型。
方針：元の二成分を保持する往復を、引き戻しの両射影で検査する。
規約：同型の全体側の射影は元の twistedSourceElementsComparison。
使われ方：元の共同 Hom の復元射の底変換を、同じ全族の評価へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)

/-- 同じ始点固定の全族と、元の共同射影の同じ底変換の厳密な同型。 -/
def twistedSourceElementsBaseChangeIso : twistedSourceElements p b ≅
    pullback (twistedElementsProjection p)
      (lift (SSet.const (SSet.opObjEquiv.symm b)) (𝟙 E)) where
  hom := twistedSourceElementsToBaseChange p b
  inv := twistedSourceElementsFromBaseChange p b
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [twistedSourceElementsToBaseChange, twistedSourceElementsFromBaseChange,
        Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · apply pullback.hom_ext
      · simp only [twistedSourceElementsToBaseChange, twistedSourceElementsFromBaseChange,
          Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          Category.id_comp]
        rw [twistedSourceElementsComparison_fst]
      · simp only [twistedSourceElementsToBaseChange, twistedSourceElementsFromBaseChange,
          Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp]
        exact pullback.condition
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [twistedSourceElementsToBaseChange, twistedSourceElementsFromBaseChange,
          Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [twistedSourceElementsComparison_fst]
        simp only [pullback.lift_fst, pullback.lift_snd_assoc]
      · simp only [twistedSourceElementsToBaseChange, twistedSourceElementsFromBaseChange,
          Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [twistedSourceElementsComparison_snd]
        simp only [pullback.lift_fst]
        have h := congrArg (fun f => f ≫ snd B.op E)
          (pullback.condition (f := twistedElementsProjection p)
            (g := lift (SSet.const (SSet.opObjEquiv.symm b)) (𝟙 E)))
        simpa only [Category.assoc, twistedElementsProjection, lift_snd, Category.comp_id]
          using h.symm
    · simp only [twistedSourceElementsToBaseChange, twistedSourceElementsFromBaseChange,
        Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]

/-- 同じ底変換表示の全体成分は、元の大域評価への同じ比較。 -/
lemma twistedSourceElementsBaseChangeIso_fst :
    (twistedSourceElementsBaseChangeIso p b).hom ≫ pullback.fst _ _ =
      twistedSourceElementsComparison p b := pullback.lift_fst _ _ _

/-- 同じ底変換表示の底成分は、元の終点の全空間成分。 -/
lemma twistedSourceElementsBaseChangeIso_snd :
    (twistedSourceElementsBaseChangeIso p b).hom ≫ pullback.snd _ _ =
      pullback.fst p (twistedArrowSourceProjection b) := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.F2.Ind

module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TwistedSourceElementsBaseChangeMaps

/-!
概要：同じ始点固定の全族は、元の共同射影の始点固定の底変換と厳密に同型。
方針：元の二成分を保持する往復を、引き戻しの両射影で検査する。
規約：同型の全体側の射影は元の twistedSourceElementsComparison。
使われ方：元の共同 Hom の復元射の底変換を、同じ全族の評価へ接続する。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)

/-- 同じ始点固定の全族と、元の共同射影の同じ底変換の厳密な同型。 -/
def twistedSourceElementsBaseChangeIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElements p b ≅
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsProjection p)
      (lift (SSet.const (SSet.opObjEquiv.symm b)) (𝟙 E)) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsToBaseChange p b
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsFromBaseChange p b
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsToBaseChange, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsFromBaseChange,
        Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · apply pullback.hom_ext
      · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsToBaseChange, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsFromBaseChange,
          Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          Category.id_comp]
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsComparison_fst]
      · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsToBaseChange, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsFromBaseChange,
          Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp]
        exact pullback.condition
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsToBaseChange, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsFromBaseChange,
          Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsComparison_fst]
        simp only [pullback.lift_fst, pullback.lift_snd_assoc]
      · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsToBaseChange, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsFromBaseChange,
          Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsComparison_snd]
        simp only [pullback.lift_fst]
        have h := congrArg (fun f => f ≫ snd B.op E)
          (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsProjection p)
            (g := lift (SSet.const (SSet.opObjEquiv.symm b)) (𝟙 E)))
        simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsProjection, lift_snd, Category.comp_id]
          using h.symm
    · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsToBaseChange, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsFromBaseChange,
        Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]

/-- 同じ底変換表示の全体成分は、元の大域評価への同じ比較。 -/
lemma twistedSourceElementsBaseChangeIso_fst :
    (twistedSourceElementsBaseChangeIso p b).hom ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsComparison p b := pullback.lift_fst _ _ _

/-- 同じ底変換表示の底成分は、元の終点の全空間成分。 -/
lemma twistedSourceElementsBaseChangeIso_snd :
    (twistedSourceElementsBaseChangeIso p b).hom ≫ pullback.snd _ _ =
      pullback.fst p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection b) := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

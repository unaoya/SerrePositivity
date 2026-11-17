module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowBoundaryLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowLatchingNaturality

/-!
概要：barの元の相対latching射は、各係数射がleft anodyneならleft anodyneである。
方針：実際のpushoutの持ち上げ問題を、元の退化境界を固定する行の持ち上げへ戻す。
規約：元の相対latching射と両脚を保持する。別の射の条件つき判定に置き換えない。
使われ方：IS-W2 R03f.2の対角への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory Limits SSet
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open scoped Simplicial
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
  (hη : ∀ i, leftAnodyneExtensions (η.app i))

include hη

/-- 元の相対latchingの全持ち上げ問題は、同じ退化境界を保持して解ける。 -/
theorem simplicialReplacementRowsMap_relative_leftAnodyne (n : ℕ) :
    leftAnodyneExtensions (relativeLatchingMap simplexOp (Opposite.op ⦋n⦌)
      (simplicialReplacementRowsMap η)) := by
  intro E B p hp
  haveI : LeftFibration p := ⟨hp⟩
  constructor
  intro a b sq
  let lm := (latchingEvaluation simplexOp (Opposite.op ⦋n⦌)).map (simplicialReplacementRowsMap η)
  let cf := (latchingComparison simplexOp (Opposite.op ⦋n⦌)).app (simplicialReplacementRows F)
  let cg := (latchingComparison simplexOp (Opposite.op ⦋n⦌)).app (simplicialReplacementRows G)
  let r := relativeLatchingMap simplexOp (Opposite.op ⦋n⦌) (simplicialReplacementRowsMap η)
  let ig := pushout.inl lm cf
  let iff := pushout.inr lm cf
  have hf : iff ≫ r = simplicialReplacementRowMap η n :=
    inr_relativeLatchingMap simplexOp (Opposite.op ⦋n⦌) (simplicialReplacementRowsMap η)
  have hg : ig ≫ r = cg :=
    inl_relativeLatchingMap simplexOp (Opposite.op ⦋n⦌) (simplicialReplacementRowsMap η)
  have hpo : lm ≫ ig = cf ≫ iff := pushout.condition
  let d := (simplicialReplacementRowLatchingIso G n).inv ≫ ig ≫ a
  have sq0 : CommSq (iff ≫ a) (simplicialReplacementRowMap η n) p b := by
    constructor
    rw [Category.assoc, sq.w, ← Category.assoc, hf]
  have hdp : (ig ≫ a) ≫ p = cg ≫ b := by
    rw [Category.assoc, sq.w, ← Category.assoc, hg]
  have hd : d ≫ p = (simplicialReplacementDegenerateRow G n).ι ≫ b := by
    calc
      d ≫ p = (simplicialReplacementRowLatchingIso G n).inv ≫ ((ig ≫ a) ≫ p) := by
        simp only [d, Category.assoc]
      _ = (simplicialReplacementRowLatchingIso G n).inv ≫ (cg ≫ b) := by rw [hdp]
      _ = (simplicialReplacementDegenerateRow G n).ι ≫ b := by
        rw [← Category.assoc, simplicialReplacementRowLatchingIso_inv_inclusion]
  have ha : simplicialReplacementRowPartMap η n ((nerve I).degenerate n) ≫ d =
      (simplicialReplacementDegenerateRow F n).ι ≫ (iff ≫ a) := by
    calc
      simplicialReplacementRowPartMap η n ((nerve I).degenerate n) ≫ d =
          (simplicialReplacementRowPartMap η n ((nerve I).degenerate n) ≫
            (simplicialReplacementRowLatchingIso G n).inv) ≫ ig ≫ a := by
              simp only [d, Category.assoc]
      _ = ((simplicialReplacementRowLatchingIso F n).inv ≫ lm) ≫ ig ≫ a := by
        rw [simplicialReplacementRowLatchingIso_inv_naturality]
      _ = (simplicialReplacementRowLatchingIso F n).inv ≫ (lm ≫ ig) ≫ a := by
        simp only [Category.assoc]
      _ = (simplicialReplacementRowLatchingIso F n).inv ≫ (cf ≫ iff) ≫ a := by rw [hpo]
      _ = ((simplicialReplacementRowLatchingIso F n).inv ≫ cf) ≫ iff ≫ a := by
        simp only [Category.assoc]
      _ = (simplicialReplacementDegenerateRow F n).ι ≫ iff ≫ a := by
        rw [simplicialReplacementRowLatchingIso_inv_inclusion]
  obtain ⟨l, hl, hlp, hld⟩ := simplicialReplacementRowBoundary_lift η hη n p (iff ≫ a) b d sq0 hd ha
  have hlg : cg ≫ l = ig ≫ a := by
    change (latchingComparison simplexOp (Opposite.op ⦋n⦌)).app (simplicialReplacementRows G) ≫ l = _
    rw [← simplicialReplacementRowLatchingIso_inclusion n G, Category.assoc, hld]
    change (simplicialReplacementRowLatchingIso G n).hom ≫
      ((simplicialReplacementRowLatchingIso G n).inv ≫ ig ≫ a) = _
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := hlp }
  apply pushout.hom_ext
  · change ig ≫ (r ≫ l) = ig ≫ a
    rw [← Category.assoc, hg, hlg]
  · change iff ≫ (r ≫ l) = iff ≫ a
    rw [← Category.assoc, hf, hl]

/-- 全ての元の相対latching射がleft anodyneなので、同じbarの射はReedy left anodyne。 -/
theorem simplicialReplacementRowsMap_reedy_leftAnodyne :
    reedyLeft simplexOp leftAnodyneExtensions (simplicialReplacementRowsMap η) := by
  intro j
  induction j using Opposite.rec with | _ j =>
    induction j using SimplexCategory.rec with | _ n =>
      exact simplicialReplacementRowsMap_relative_leftAnodyne η hη n

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

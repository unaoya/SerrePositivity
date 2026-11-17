module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.LeftFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftKanFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

/-!
概要：Kan標的へのanodyne射はleft anodyneである。
方針：left fibrationの持ち上げ問題をKan標的へ引き戻し、全ホーンの持ち上げ性を使う。
規約：単体集合のモデル構造の公理を仮定しない。元の射そのものの左持ち上げ性。
使われ方：IS-W2 R03f.1、係数のEx∞単位の相対的な比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open CategoryTheory Limits SSet _root_.HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open scoped Simplicial

/-- Kan基底上のleft fibrationの全空間はKanである。 -/
theorem leftFibration_total_kanComplex {E B : SSet.{u}} [KanComplex B]
    (p : E ⟶ B) [LeftFibration p] : KanComplex E := by
  apply kanComplex_of_leftHornFillers
  intro n i hi a
  obtain ⟨b, hb⟩ := KanComplex.hornFilling (a ≫ p)
  have : HasLiftingProperty (horn (n+1) i).ι p :=
    LeftFibration.mem (p := p) _ (leftHornInclusions.intro i hi)
  have sq : CommSq a (horn (n+1) i).ι p b := ⟨hb⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- Kan標的へのanodyne射は、すべてのleft fibrationに対して左持ち上げ性を持つ。 -/
theorem anodyneExtensions_leftAnodyne_of_kanTarget
    {X Y : SSet.{u}} [KanComplex Y] (f : X ⟶ Y)
    (hf : SSet.anodyneExtensions f) : leftAnodyneExtensions f := by
  intro E B p hp
  letI : LeftFibration p := ⟨hp⟩
  constructor
  intro a b sq
  let q : pullback p b ⟶ Y := pullback.snd p b
  haveI : LeftFibration q :=
    ⟨leftFibrations.pullback_snd p b hp⟩
  haveI : KanComplex (pullback p b) := leftFibration_total_kanComplex q
  haveI : Fibration q := leftFibration_fibration_of_kanComplex q
  have : HasLiftingProperty f q := hf q (by
    rw [← _root_.HomotopicalAlgebra.fibration_iff]
    infer_instance)
  let a' : X ⟶ pullback p b := pullback.lift a f sq.w
  have sq' : CommSq a' f q (𝟙 Y) := ⟨by
    dsimp only [a', q]
    rw [pullback.lift_snd, Category.comp_id]⟩
  refine CommSq.HasLift.mk' { l := sq'.lift ≫ pullback.fst p b, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc, sq'.fac_left]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (sq'.lift ≫ q) ≫ b = b
    rw [sq'.fac_right, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

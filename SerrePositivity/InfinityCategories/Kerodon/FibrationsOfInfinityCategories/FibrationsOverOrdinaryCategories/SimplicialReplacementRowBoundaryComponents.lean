module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowInclusionLaws
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct

/-!
概要：各基底射列で、指定された退化境界を保つ係数の持ち上げを作る。
方針：退化成分では元の境界値を使い、それ以外では同じ係数射のleft anodyne性で持ち上げる。
規約：元の二つの脚と、元の退化境界の値を厳密に保持する。
使われ方：IS-W2 R03f.2の相対latchingの直接の持ち上げ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
  (hη : ∀ i, leftAnodyneExtensions (η.app i)) (n : ℕ)
  {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (a : simplicialReplacementRow F n ⟶ E) (b : simplicialReplacementRow G n ⟶ B)
  (d : (simplicialReplacementDegenerateRow G n : SSet.{u}) ⟶ E)
  (sq : CommSq a (simplicialReplacementRowMap η n) p b)
  (hd : d ≫ p = (simplicialReplacementDegenerateRow G n).ι ≫ b)
  (ha : simplicialReplacementRowPartMap η n ((nerve I).degenerate n) ≫ d =
    (simplicialReplacementDegenerateRow F n).ι ≫ a)

include hη sq hd ha

/-- 元の各係数射の持ち上げを、指定された同じ退化成分での値を固定して取れる。 -/
theorem simplicialReplacementRowBoundary_component (σ : ComposableArrows I n) :
    ∃ l : G.obj (σ.obj 0) ⟶ E,
      η.app (σ.obj 0) ≫ l = simplicialReplacementRowInclusion F n σ ≫ a ∧
      l ≫ p = simplicialReplacementRowInclusion G n σ ≫ b ∧
      ∀ hσ : σ ∈ (nerve I).degenerate n,
        l = simplicialReplacementRowPartInclusion n G ((nerve I).degenerate n) σ hσ ≫ d := by
  classical
  by_cases hσ : σ ∈ (nerve I).degenerate n
  · refine ⟨simplicialReplacementRowPartInclusion n G ((nerve I).degenerate n) σ hσ ≫ d,
      ?_, ?_, fun _ => rfl⟩
    · rw [← Category.assoc, simplicialReplacementRowPartInclusion_map, Category.assoc, ha,
        ← Category.assoc, simplicialReplacementRowPartInclusion_inclusion]
    · rw [Category.assoc, hd, ← Category.assoc, simplicialReplacementRowPartInclusion_inclusion]
  · have : HasLiftingProperty (η.app (σ.obj 0)) p := hη (σ.obj 0) p (LeftFibration.mem (p := p))
    have s : CommSq (simplicialReplacementRowInclusion F n σ ≫ a) (η.app (σ.obj 0)) p
        (simplicialReplacementRowInclusion G n σ ≫ b) := by
      constructor
      calc
        (simplicialReplacementRowInclusion F n σ ≫ a) ≫ p =
            (simplicialReplacementRowInclusion F n σ ≫ simplicialReplacementRowMap η n) ≫ b := by
              rw [Category.assoc, sq.w, ← Category.assoc]
        _ = η.app (σ.obj 0) ≫ (simplicialReplacementRowInclusion G n σ ≫ b) := by
          rw [simplicialReplacementRowInclusion_map, Category.assoc]
    exact ⟨s.lift, s.fac_left, s.fac_right, fun h => (hσ h).elim⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

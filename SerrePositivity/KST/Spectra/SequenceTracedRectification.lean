module

public import SerrePositivity.KST.Spectra.PointedBasedPathComposition
public import SerrePositivity.KST.Spectra.PointedHomotopyExtension
public import SerrePositivity.KST.Spectra.KanSequence

/-!
概要：元の比較区間と実際の構造三角形を保持して、ホモトピー可換な Kan 列を厳密化する。
方針：構造区間と前段修正を実三角形で貼り、その区間そのものを構造単射に沿って延長する。
規約：次段修正の制限を厳密に保持。使われ方：境界比較のトレース恒等性を得る帰納構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.KanSequence
variable {X Y : KanSequence.{u}} (hX : ∀ n, Mono (X.sigma n).right)
  (f : ∀ n, (X.level n).space ⟶ (Y.level n).space)
  (h : ∀ n, PointedMapping.VerticalPath (PointedObject.toPoint (Y.level (n + 1)).space)
    (X.sigma n ≫ f (n + 1)) (PointedSimplicialSet.circle.{u} ◁ f n ≫ Y.sigma n))

/-- 修正済みの段射と、元の段射からの実際の比較区間を保持する帰納状態。 -/
structure TracedRectificationStage (n : ℕ) where
  map : (X.level n).space ⟶ (Y.level n).space
  comparison : PointedMapping.VerticalPath (PointedObject.toPoint (Y.level n).space) (f n) map

/-- 前段の比較区間を、同じ懸垂・標的構造射で次段の構造 Hom へ移す。 -/
def tracedRectificationStepPath (n : ℕ) (s : TracedRectificationStage f n) :=
  s.comparison.suspension.forgetProjection.basedPost (Y.sigma n)

/-- 元の構造区間と前段の修正区間を貼る、対角区間と実合成三角形。 -/
def tracedRectificationComposite (n : ℕ) (s : TracedRectificationStage f n) :
    PointedMapping.BasedPathComposite (h n) (tracedRectificationStepPath f n s) :=
  PointedMapping.BasedPathComposite.choose _ _

/-- 選んだ合成区間そのものを延長し、次段の厳密可換性と区間全体の制限を保つ。 -/
def tracedRectificationNext (n : ℕ) (s : TracedRectificationStage f n) :
    { t : TracedRectificationStage f (n + 1) //
      X.sigma n ≫ t.map = PointedSimplicialSet.circle.{u} ◁ s.map ≫ Y.sigma n ∧
      (X.sigma n).right ▷ (Δ[1] : SSet.{u}) ≫ t.comparison.homotopy.h =
        (tracedRectificationComposite f h n s).path.homotopy.h } := by
  let sigmaMono : Mono (X.sigma n).right := hX n
  let P := (tracedRectificationComposite f h n s).path
  let hex := PointedExtension.exists_homotopy_from_zero (X.sigma n) (f (n + 1))
    (PointedSimplicialSet.circle.{u} ◁ s.map ≫ Y.sigma n) P.homotopy P.homotopy_base
  let V := hex.choose_spec.2.choose
  let hb := hex.choose_spec.2.choose_spec.1
  let Q := PointedMapping.VerticalPath.ofHomotopy
    (p := PointedObject.toPoint (Y.level (n + 1)).space) V hb (toUnit_unique _ _)
  refine ⟨⟨hex.choose, Q⟩, hex.choose_spec.1, ?_⟩
  rw [PointedMapping.VerticalPath.ofHomotopy_h]
  exact hex.choose_spec.2.choose_spec.2

/-- 零段を保持し、比較区間を全段に保持する逐次厳密化。 -/
def tracedRectificationStage : (n : ℕ) → TracedRectificationStage f n
  | 0 => ⟨f 0, PointedMapping.basedPathOfEdge (SSet.Edge.id (PointedMapping.familyVertex (f 0)))⟩
  | n + 1 => (tracedRectificationNext hX f h n (tracedRectificationStage n)).val

/-- 元の構造区間から構成した、実際の厳密な Kan 列の射。 -/
def tracedRectify : Hom X Y where
  app n := (tracedRectificationStage hX f h n).map
  comm n := (tracedRectificationNext hX f h n
    (tracedRectificationStage hX f h n)).property.1.symm

/-- 厳密化の各段には、元の段射からの同じ実際の比較区間が残る。 -/
def tracedRectifyComparison (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (Y.level n).space) (f n)
      ((tracedRectify hX f h).app n) :=
  (tracedRectificationStage hX f h n).comparison

/-- 次段比較の構造射への制限は、帰納段で選んだ合成区間そのもの。 -/
lemma tracedRectifyComparison_restriction (n : ℕ) :
    (X.sigma n).right ▷ (Δ[1] : SSet.{u}) ≫
        (tracedRectifyComparison hX f h (n + 1)).homotopy.h =
      (tracedRectificationComposite f h n (tracedRectificationStage hX f h n)).path.homotopy.h :=
  (tracedRectificationNext hX f h n (tracedRectificationStage hX f h n)).property.2

/-- 零段の射は厳密に元の射のまま。 -/
lemma tracedRectify_zero : (tracedRectify hX f h).app 0 = f 0 := rfl

end SerrePositivity.KST.Spectra.KanSequence

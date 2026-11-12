module

public import SerrePositivity.KST.Spectra.PointedVerticalPathComposition
public import SerrePositivity.KST.Spectra.PointedRelativeHomotopyAdjustment
public import SerrePositivity.KST.Spectra.KanSequence
public import SerrePositivity.KST.Spectra.PointedBasedPathComposition

/-!
概要：指定した厳密な列への射影を保ち、実垂直区間と構造三角形を保持して列を厳密化する。
方針：元の構造区間と前段修正を同じ Hom fiber 内で貼り、その区間を射影固定で延長する。
規約：次段の区間の制限も厳密に保持。使われ方：全列の比較の段方向の整合性の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.KanSequence
variable {X Y Z : KanSequence.{u}} (hX : ∀ n, Mono (X.sigma n).right)
  (q : Hom Y Z) (hq : ∀ n, SSet.modelCategoryQuillen.J.rlp (q.app n).right)
  (b : Hom X Z) (f : ∀ n, (X.level n).space ⟶ (Y.level n).space)
  (hb : ∀ n, f n ≫ q.app n = b.app n)
  (h : ∀ n, PointedMapping.VerticalPath (q.app (n + 1))
    (X.sigma n ≫ f (n + 1)) (PointedSimplicialSet.circle.{u} ◁ f n ≫ Y.sigma n))

/-- 指定射影、元の段射、同じ射影を固定する実区間を保持した帰納状態。 -/
structure RelativeTracedRectificationStage (n : ℕ) where
  map : (X.level n).space ⟶ (Y.level n).space
  projection : map ≫ q.app n = b.app n
  comparison : PointedMapping.VerticalPath (q.app n) (f n) map

/-- 前段の実区間を、同じ射影を固定した次段の構造 Hom へ移す。 -/
def relativeTracedStepPath (n : ℕ) (s : RelativeTracedRectificationStage q b f n) :=
  s.comparison.suspension.post (q.app (n + 1)) (Y.sigma n) (Z.sigma n) (q.comm n).symm

/-- 元の構造区間と前段修正を、同じ fiber の実合成三角形で貼り合わせる。 -/
def relativeTracedComposite (n : ℕ) (s : RelativeTracedRectificationStage q b f n) :
    PointedMapping.VerticalPathComposite (h n) (relativeTracedStepPath q b f n s) :=
  PointedMapping.VerticalPathComposite.choose (hq (n + 1)) _ _

/-- 同じ射影の上で合成区間を延長し、次段の可換性と区間全体の制限を保持する。 -/
def relativeTracedNext (n : ℕ) (s : RelativeTracedRectificationStage q b f n) :
    { t : RelativeTracedRectificationStage q b f (n + 1) //
      X.sigma n ≫ t.map = PointedSimplicialSet.circle.{u} ◁ s.map ≫ Y.sigma n ∧
      (X.sigma n).right ▷ (Δ[1] : SSet.{u}) ≫ t.comparison.homotopy.h =
        (relativeTracedComposite q hq b f h n s).path.homotopy.h } := by
  let sigmaMono : Mono (X.sigma n).right := hX n
  let P := (relativeTracedComposite q hq b f h n s).path
  have hRight := congrArg Under.Hom.right (hb (n + 1))
  change (f (n + 1)).right ≫ (q.app (n + 1)).right = (b.app (n + 1)).right at hRight
  have hOver : P.homotopy.h ≫ (q.app (n + 1)).right =
      fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space).right (Δ[1] : SSet.{u}) ≫
        (X.sigma n).right ≫ (b.app (n + 1)).right := by
    have hp := P.homotopy_over
    simpa only [Under.comp_right, Category.assoc, hRight] using hp
  let hex := PointedExtension.exists_homotopy_from_zero_over (q.app (n + 1)) (hq (n + 1))
    (X.sigma n) (f (n + 1)) (PointedSimplicialSet.circle.{u} ◁ s.map ≫ Y.sigma n)
    (b.app (n + 1)) (hb (n + 1)) P.homotopy P.homotopy_base hOver
  let V := hex.choose_spec.2.2.choose
  have hV := hex.choose_spec.2.2.choose_spec
  have hVertical : V.h ≫ (q.app (n + 1)).right =
      fst (X.level (n + 1)).space.right (Δ[1] : SSet.{u}) ≫
        (f (n + 1)).right ≫ (q.app (n + 1)).right := by
    rw [hRight]
    exact hV.2.2
  let Q := PointedMapping.VerticalPath.ofHomotopy V hV.1 hVertical
  refine ⟨⟨hex.choose, hex.choose_spec.2.1, Q⟩, hex.choose_spec.1, ?_⟩
  rw [PointedMapping.VerticalPath.ofHomotopy_h]
  exact hV.2.1

/-- 零段の射と全射影を保ち、実比較区間を全段に保持する帰納構成。 -/
def relativeTracedStage : (n : ℕ) → RelativeTracedRectificationStage q b f n
  | 0 => ⟨f 0, hb 0, PointedMapping.VerticalPath.refl (q.app 0) (f 0)⟩
  | n + 1 => (relativeTracedNext hX q hq b f hb h n (relativeTracedStage n)).val

/-- 実垂直区間と構造三角形を保持した、指定射影上の厳密な列射。 -/
def relativeTracedRectify : Hom X Y where
  app n := (relativeTracedStage hX q hq b f hb h n).map
  comm n := (relativeTracedNext hX q hq b f hb h n
    (relativeTracedStage hX q hq b f hb h n)).property.1.symm

/-- 元の指定した厳密な列への射影は、全段で保持される。 -/
lemma relativeTracedRectify_projection (n : ℕ) :
    (relativeTracedRectify hX q hq b f hb h).app n ≫ q.app n = b.app n :=
  (relativeTracedStage hX q hq b f hb h n).projection

/-- 同じ射影を固定する元の実比較区間を、修正後も各段で回収する。 -/
def relativeTracedRectifyComparison (n : ℕ) :
    PointedMapping.VerticalPath (q.app n) (f n)
      ((relativeTracedRectify hX q hq b f hb h).app n) :=
  (relativeTracedStage hX q hq b f hb h n).comparison

/-- 次段比較を構造射へ制限すると、帰納段で貼った同じ対角区間になる。 -/
lemma relativeTracedRectifyComparison_restriction (n : ℕ) :
    (X.sigma n).right ▷ (Δ[1] : SSet.{u}) ≫
        (relativeTracedRectifyComparison hX q hq b f hb h (n + 1)).homotopy.h =
      (relativeTracedComposite q hq b f h n
        (relativeTracedStage hX q hq b f hb h n)).path.homotopy.h :=
  (relativeTracedNext hX q hq b f hb h n (relativeTracedStage hX q hq b f hb h n)).property.2

end SerrePositivity.KST.Spectra.KanSequence

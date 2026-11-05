module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.CoherentCosliceEvaluationComparison
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.CosliceUnderlyingValueNaturality
/-!
概要：線形 Hom の同じ係数図式と、native 基礎空間値の実辺作用を比較する。
方針：coherent coslice と始点固定 Tw の二つの輸送比較を合成する。
規約：係数の射と元の coherent 辺を保持し、strict 図式への置換は行わない。
使われ方：評価コホモロジーチャートを元の native 図式の実脚へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DoldKanComparison SSet
open scoped _root_.Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

/-- 比較関手の同じ像を始点とする native 基礎空間関手。 -/
def dgBarCompactCoherentUnderlyingValueFunctor (x : ClosedCategory R D) :=
  dgBarCompactUnderlyingValueFunctor
    ((coherentComparison (R := R) (D := D)).app (Opposite.op ⦋0⦌) (coherentNerveVertex x))

/-- 同じ線形 Hom から、同じ基礎空間関手の持ち上げた実値への比較。 -/
def dgBarCompactLinearUnderlyingValueComparison (x y : ClosedCategory R D) :=
  (SSet.uliftFunctor.{max u v + 1, max u v}).map
      (dgBarCompactCoherentCosliceComparison R D x y) ≫
    dgBarCompactCosliceUnderlyingValueComparison
      ((coherentComparison (R := R) (D := D)).app (Opposite.op ⦋0⦌) (coherentNerveVertex x))
      ((coherentComparison (R := R) (D := D)).app (Opposite.op ⦋0⦌) (coherentNerveVertex y))

lemma dgBarCompactLinearUnderlyingValueComparison_isQCatEquivalence
    (x y : ClosedCategory R D) :
    IsQCatEquivalence (dgBarCompactLinearUnderlyingValueComparison R D x y) := by
  have h := (dgBarCompactCoherentCosliceComparison_isQCatEquivalence R D x y).ulift.{max u v, max u v + 1}
  exact h.comp (dgBarCompactCosliceUnderlyingValueComparison_isQCatEquivalence _ _)

/-- 全係数の実射と、その native 基礎空間値での実辺作用の比較。 -/
def dgBarCompactLinearUnderlyingValueComparison_transportIso
    {I : Type u} [Category.{u} I] (F : I ⥤ ClosedCategory R D)
    (x : ClosedCategory R D) {i j : I} (f : i ⟶ j) :
    FunctorIso
      ((SSet.uliftFunctor.{max u v + 1, max u v}).map
          ((SSet.uliftFunctor.{v, u}).map
            ((HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map f)) ≫
        dgBarCompactLinearUnderlyingValueComparison R D x (F.obj j))
      (dgBarCompactLinearUnderlyingValueComparison R D x (F.obj i) ≫
        (SSet.uliftFunctor.{max u v + 1, max u v}).map
          (F2.spaceInfinityEdgeValue
            ((SSet.Edge.ofTruncated
              (X := (SSet.uliftFunctor.{max u v + 1, max u v}).obj (dgNerve R D))
              (uliftTruncatedEdge.{max u v, max u v + 1}
                ((coherentNerveEdge (F.map f)).map
                  (coherentComparison (R := R) (D := D))))).map
                    (dgBarCompactCoherentUnderlyingValueFunctor R D x)))) := by
  let q := coherentComparison (R := R) (D := D)
  let a := q.app (Opposite.op ⦋0⦌) (coherentNerveVertex x)
  have h₁ := (dgBarCompactCoherentCosliceComparison_transportIso R D F x f).ulift.{max u v, max u v + 1}
  have h₁' := h₁.postcomp (dgBarCompactCosliceUnderlyingValueComparison a
    (q.app (Opposite.op ⦋0⦌) (coherentNerveVertex (F.obj j))))
  have h₂ := (dgBarCompactCosliceUnderlyingValueComparison_transportIso a
    ((coherentNerveEdge (F.map f)).map q)).precomp
      ((SSet.uliftFunctor.{max u v + 1, max u v}).map
        (dgBarCompactCoherentCosliceComparison R D x (F.obj i)))
  dsimp only [a, q] at h₁' h₂
  simp only [Functor.map_comp, Category.assoc] at h₁' h₂
  dsimp only [dgBarCompactLinearUnderlyingValueComparison,
    dgBarCompactCoherentUnderlyingValueFunctor]
  rw [Category.assoc]
  exact h₁'.trans h₂


end SerrePositivity.InfinityCategories

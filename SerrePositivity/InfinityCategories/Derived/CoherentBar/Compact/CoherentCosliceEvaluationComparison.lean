module
public import SerrePositivity.InfinityCategories.Derived.DGPointCosliceTransport
public import SerrePositivity.InfinityCategories.Derived.DGCoherentCosliceTransport
public import SerrePositivity.InfinityCategories.DoldKanComparison.ComparisonEquivalence
/-!
概要：同じ線形 Hom の coslice 比較を、dg nerve の実 coslice fiber へ渡す。
方針：coherent 比較関手の全 fiber 射と既存の輸送正方形を合成する。
規約：各辺の実輸送を保持し、点ごとの同値だけで自然性を代用しない。
使われ方：線形ホモロジーチャートと native 評価の実辺作用の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DoldKanComparison SSet
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

/-- 標準線形 Hom の同じ比較を、比較関手の実像上の dg coslice fiber へ送る。 -/
def dgBarCompactCoherentCosliceComparison (x y : ClosedCategory R D) :=
  HomotopyLimits.coherentCosliceFiberComparison x y ≫
    pointCosliceFiberMap (coherentComparison (R := R) (D := D))
      (coherentNerveVertex x) (coherentNerveVertex y)

lemma dgBarCompactCoherentCosliceComparison_isQCatEquivalence
    (x y : ClosedCategory R D) :
    IsQCatEquivalence (dgBarCompactCoherentCosliceComparison R D x y) := by
  let : Quasicategory (SimplicialNerve (ClosedCategory R D)) :=
    Coherent.simplicialNerve_quasicategory (ClosedCategory R D)
  have h₁ :=
    (HomotopyLimits.coherentCosliceFiberComparison_homotopyEquivalence x y).isQCatEquivalence
  have h₂ := (pointCosliceFiberMap_equivalence_iff_pinchedHomMap
    (coherentComparison (R := R) (D := D)) (coherentNerveVertex x)
      (coherentNerveVertex y)).mpr
        (coherentComparison_fullyFaithful (R := R) (D := D) _ _)
  exact h₁.comp h₂

/-- 同じ線形係数の実射と、dg nerve 内の同じ辺の輸送との全比較。 -/
def dgBarCompactCoherentCosliceComparison_transportIso
    {I : Type u} [Category.{u} I] (F : I ⥤ ClosedCategory R D)
    (x : ClosedCategory R D) {i j : I} (f : i ⟶ j) :
    FunctorIso
      ((SSet.uliftFunctor.{v, u}).map
          ((HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map f) ≫
        dgBarCompactCoherentCosliceComparison R D x (F.obj j))
      (dgBarCompactCoherentCosliceComparison R D x (F.obj i) ≫
        edgeTransport
          (sliceUnderProjection (SSet.yonedaEquiv.symm
            ((coherentComparison (R := R) (D := D)).app (Opposite.op ⦋0⦌)
              (coherentNerveVertex x))))
          ((coherentNerveEdge (F.map f)).map
            (coherentComparison (R := R) (D := D)))) := by
  let : Quasicategory (SimplicialNerve (ClosedCategory R D)) :=
    Coherent.simplicialNerve_quasicategory (ClosedCategory R D)
  let q := coherentComparison (R := R) (D := D)
  let a := coherentNerveVertex x
  have h := dgLeftFibrationSquareTransportIso
    (sliceUnderProjection (SSet.yonedaEquiv.symm a))
    (sliceUnderProjection (SSet.yonedaEquiv.symm (q.app (Opposite.op ⦋0⦌) a)))
    (dgPointCoslicePostcomp q a) q (dgPointCoslicePostcomp_projection q a)
    (coherentNerveEdge (F.map f))
  erw [dgPointCoslicePostcomp_fiber q a (coherentNerveVertex (F.obj j)),
    dgPointCoslicePostcomp_fiber q a (coherentNerveVertex (F.obj i))] at h
  have H := ((coherentCosliceFiberComparison_transportIso F x f).postcomp
    (pointCosliceFiberMap q a (coherentNerveVertex (F.obj j)))).trans
      (h.precomp (HomotopyLimits.coherentCosliceFiberComparison x (F.obj i)))
  simpa only [dgBarCompactCoherentCosliceComparison, Category.assoc] using H

end SerrePositivity.InfinityCategories

module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.FilteredLeftFibrationRelativeDetection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.ContinuousKanUnitHomotopy

/-!
概要：全空間の Kan 模型で充填できる有限境界を一つの fiber 内で充填する。
方針：境界固定の相対検出の後、fiber の単位による充填の反映を使う。
規約：元の境界へのホモトピーと、輸送後の境界の厳密な充填を返す。
使われ方：一般 coherent な filtered 図式の全空間模型の有限球面の検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：全空間模型で充填できる指定境界は、輸送後に一つの fiber 内で充填できる。
方針：標準境界と単体へ相対検出を使い、fiber の Kan 性で置換を除く。
規約：元の指定境界への実際のホモトピーも保持する。使われ方：有限境界の検出。 -/
lemma continuousKanLeftFibration_finite_boundary_detection {E B : SSet.{u}}
    [Quasicategory B] [IsFilteredInfinity B] (p : E ⟶ B) [LeftFibration p]
    (n : ℕ) (a : (boundary n : SSet.{u}) ⟶ E)
    (w : (Δ[n] : SSet.{u}) ⟶ continuousKanReplacement.obj E)
    (hw : (boundary n).ι ≫ w = a ≫ continuousKanReplacementUnit.app E) :
    ∃ b : B _⦋0⦌, ∃ t : (boundary n : SSet.{u}) ⟶ vertexFiber p b,
      ∃ v : (Δ[n] : SSet.{u}) ⟶ vertexFiber p b,
        (boundary n).ι ≫ v = t ∧ Nonempty (SSet.Homotopy a (t ≫ vertexFiberι p b)) := by
  obtain ⟨b, t, g, hg, Ht, _⟩ :=
    continuousKanLeftFibration_finite_relative_detection p (boundary n).ι a w hw.symm
  obtain ⟨v, hv⟩ := continuousKanReplacementUnit_reflects_boundaryFilling n t ⟨g, hg⟩
  exact ⟨b, t, v, hv, Ht⟩

end SerrePositivity.InfinityCategories.F2

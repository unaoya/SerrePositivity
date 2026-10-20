module

public import SerrePositivity.InfinityCategories.F2.RelativePathValuePoint
public import SerrePositivity.InfinityCategories.F2.ContinuousKanRelativeReflection

/-!
概要：輸送した有限 path 模型の Kan 像を、元の値へ全相対境界を固定して反映する。
方針：元の単位の強変形 retract による相対反映を使い、元の値の引き戻し射を読む。
規約：比較円柱は全相対境界上で定値、返す値の射は元の境界値と厳密に一致する。
使われ方：一般 coherent filtered 引き戻しの境界付き相対有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：輸送した指定 Kan path は全相対境界を固定して元の値へ反映できる。
方針：単位の自然性で全境界を照合し、相対反映と三座標の持ち上げを使う。
規約：元の境界値との制限式は等式。使われ方：相対有限検出の元の値の充填。 -/
lemma relativePath_model_reflection {K M E D H B : SSet.{u}}
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H) (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g)
    (m : relativePathBoundaryShape A ⟶ M) (q : M ⟶ H)
    (d : RelativePathInputTransportData p f g A u v a m q)
    (w : M ⟶ vertexFiber p d.vertex) (hw : m ≫ w = relativePathTransportTargetFiber d)
    (z : (Δ[1] : SSet.{u}) ⊗ K ⟶ continuousKanReplacement.obj M)
    (hz : relativePathBoundaryι A ≫ z = m ≫ continuousKanReplacementUnit.app M) :
    ∃ (r : (Δ[1] : SSet.{u}) ⊗ K ⟶ vertexFiber p d.vertex)
      (hr : relativePathBoundaryι A ≫ r = relativePathTransportTargetFiber d),
      ∃ G : SSet.Homotopy (r ≫ continuousKanReplacementUnit.app (vertexFiber p d.vertex))
        (z ≫ continuousKanReplacement.map w),
        (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ G.h =
          fst (relativePathBoundaryShape A) (Δ[1] : SSet.{u}) ≫
            relativePathTransportTargetFiber d ≫
              continuousKanReplacementUnit.app (vertexFiber p d.vertex) ∧
        A.ι ≫ relativePathValuePoint d r hr = d.boundaryValue := by
  have := vertexFiber_kanComplex_of_leftFibration p d.vertex
  have h : relativePathBoundaryι A ≫ (z ≫ continuousKanReplacement.map w) =
      relativePathTransportTargetFiber d ≫
        continuousKanReplacementUnit.app (vertexFiber p d.vertex) := by
    rw [← Category.assoc, hz, Category.assoc, ← continuousKanReplacementUnit.naturality,
      Functor.id_map, ← Category.assoc, hw]
  obtain ⟨r, hr, G, hG⟩ := continuousKanReplacement_relative_reflection
    (relativePathBoundaryι A) (relativePathTransportTargetFiber d)
    (z ≫ continuousKanReplacement.map w) h
  exact ⟨r, hr, G, hG, relativePathValuePoint_restrict d r hr⟩

end SerrePositivity.InfinityCategories.F2

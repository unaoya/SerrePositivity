module

public import SerrePositivity.InfinityCategories.F2.RelativePathModelReflection
public import SerrePositivity.InfinityCategories.F2.RelativePathBoundaryTransportHomotopy
public import SerrePositivity.InfinityCategories.F2.ContinuousKanSpecifiedHomotopy
public import SerrePositivity.InfinityCategories.F2.RelativeHomotopyZigzag

/-!
概要：有限 path 模型の近似・輸送・反映を全相対境界円柱を保って合成する。
方針：輸送を指定円柱のまま Kan 置換へ移し、相対反映を含めた zigzag を合成する。
規約：元の全境界輸送との一致を厳密な等式で返す。
使われ方：標的 Kan 引き戻し内の境界付き比較の正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の全相対境界輸送を保つ、元の値へ反映した path との比較。
方針：指定輸送の延長・相対反映・境界固定 zigzag の合成。
規約：反映後の射も元の境界値に一致。使われ方：相対有限検出の実際の比較。 -/
lemma relativePath_model_comparison {K M E D H B : SSet.{u}}
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H) (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g)
    (m : relativePathBoundaryShape A ⟶ M) (q : M ⟶ H)
    (d : RelativePathInputTransportData p f g A u v a m q)
    (hk : (relativePathBoundarySide A ≫ m) ≫ q = fiberwisePullbackPathPrism p f g a)
    (he : (relativePathBoundaryEnds A ≫ m) ≫ q = intervalBoundaryDiagram (u ≫ f) (v ≫ g))
    (w : M ⟶ vertexFiber p d.vertex) (hw : m ≫ w = relativePathTransportTargetFiber d)
    (G : SSet.Homotopy q (w ≫ vertexFiberι p d.vertex))
    (hG : (m ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      (relativePathBoundaryTransportHomotopy d hk he).h)
    (z : (Δ[1] : SSet.{u}) ⊗ K ⟶ continuousKanReplacement.obj M)
    (hz : relativePathBoundaryι A ≫ z = m ≫ continuousKanReplacementUnit.app M)
    (r₀ : (Δ[1] : SSet.{u}) ⊗ K ⟶ continuousKanReplacement.obj H)
    (U : SSet.Homotopy r₀ (z ≫ continuousKanReplacement.map q))
    (hU : (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (relativePathBoundaryShape A) (Δ[1] : SSet.{u}) ≫
        m ≫ q ≫ continuousKanReplacementUnit.app H) :
    ∃ (r : (Δ[1] : SSet.{u}) ⊗ K ⟶ vertexFiber p d.vertex)
      (hr : relativePathBoundaryι A ≫ r = relativePathTransportTargetFiber d),
      ∃ T : SSet.Homotopy r₀ (r ≫ vertexFiberι p d.vertex ≫ continuousKanReplacementUnit.app H),
        (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ T.h =
          (relativePathBoundaryTransportHomotopy d hk he).h ≫
            continuousKanReplacementUnit.app H ∧
        A.ι ≫ relativePathValuePoint d r hr = d.boundaryValue := by
  obtain ⟨V, hV⟩ := continuousKanReplacement_specified_homotopy_precomp G
    (relativePathBoundaryι A) m z hz
  obtain ⟨r, hr, R, hR, ha⟩ := relativePath_model_reflection p f g A u v a m q d w hw z hz
  let W : SSet.Homotopy
      (r ≫ vertexFiberι p d.vertex ≫ continuousKanReplacementUnit.app H)
      (z ≫ continuousKanReplacement.map (w ≫ vertexFiberι p d.vertex)) :=
    { h := R.h ≫ continuousKanReplacement.map (vertexFiberι p d.vertex)
      h₀ := by
        change SSet.ι₀ ≫ R.h ≫ continuousKanReplacement.map (vertexFiberι p d.vertex) =
          r ≫ vertexFiberι p d.vertex ≫ continuousKanReplacementUnit.app H
        rw [← Category.assoc, R.h₀, Category.assoc,
          ← continuousKanReplacementUnit.naturality, Functor.id_map]
      h₁ := by
        change SSet.ι₁ ≫ R.h ≫ continuousKanReplacement.map (vertexFiberι p d.vertex) =
          z ≫ continuousKanReplacement.map (w ≫ vertexFiberι p d.vertex)
        rw [← Category.assoc, R.h₁, Category.assoc, ← Functor.map_comp]
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  have hW : (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ W.h =
      fst (relativePathBoundaryShape A) (Δ[1] : SSet.{u}) ≫
        relativePathBoundaryι A ≫ r ≫ vertexFiberι p d.vertex ≫
          continuousKanReplacementUnit.app H := by
    change (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫
      R.h ≫ continuousKanReplacement.map (vertexFiberι p d.vertex) = _
    rw [← Category.assoc, hR, Category.assoc, Category.assoc,
      ← continuousKanReplacementUnit.naturality, Functor.id_map, ← hr]
    simp only [Category.assoc]
  have hU' : (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (relativePathBoundaryShape A) (Δ[1] : SSet.{u}) ≫
        relativePathBoundaryι A ≫ z ≫ continuousKanReplacement.map q := by
    rw [hU, ← Category.assoc (relativePathBoundaryι A), hz, Category.assoc,
      ← continuousKanReplacementUnit.naturality, Functor.id_map]
  obtain ⟨T, hT⟩ := exists_relativeHomotopyZigzag (Subcomplex.unionProd (boundary 1) A)
    U V W hU' hW
  change (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ T.h =
    (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ V.h at hT
  refine ⟨r, hr, T, ?_, ha⟩
  rw [hT, hV, ← Category.assoc, hG]

end SerrePositivity.InfinityCategories.F2

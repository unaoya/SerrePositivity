module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentInnerVertexInjective
public import SerrePositivity.EInfinity.SimplexCuts.CompositePositionDecomposition

/-!
# 元の挿入色の全頂点から同じ内側切断への写像

Berger–Fresse §2.2.6、M14 L12a のC451の指定面の比較。
元の合成位置の部分語分解を使い、同じ内側頂点を読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の挿入色の全頂点を、同じ内側Cutの同じ色の頂点へ送る（BF §2.2.6）。 -/
def insertedColorPathMap {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b)) →
      ↥(colorPositions (positiveCompositeInnerCut u v k c) (positiveWord v).val b) := by
  intro x
  have hxLabel : (positiveCompositeCutWord u v k c.1).val (c.2.horizontal x.val) =
      BarrattEccles.insertedPosition m (n + 1) k b := (Finset.mem_filter.mp x.property).2
  let hs := positiveCompositePosition_of_inserted_label u v k c.1 (c.2.horizontal x.val) b hxLabel
  let i := Classical.choose hs
  let z := Classical.choose (Classical.choose_spec hs)
  have hx := Classical.choose_spec (Classical.choose_spec hs)
  refine ⟨positiveCompositeSegmentInnerVertex u v k c i z x.val hx,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  apply Surjection.insertedPosition_injective m (n + 1) k
  exact (positiveCompositeSegmentInnerVertex_label u v k c i z x.val hx).symm.trans hxLabel

/-- 元の挿入色の写像は、二段の指定面で同じ高さを読む（BF §2.2.6）。 -/
lemma insertedColorPathMap_vertices {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1))
    (x : ↥(colorPositions c.2 (positiveCompositeCutWord u v k c.1).val
      (BarrattEccles.insertedPosition m (n + 1) k b))) :
    vertices (positiveCompositeOuterCut u v k c) (positiveWord u) k
      ((positiveCompositeInnerCut u v k c).vertical (insertedColorPathMap u v k c b x).val) =
        c.2.vertical x.val := by
  unfold insertedColorPathMap
  exact positiveCompositeSegmentInnerVertex_vertices _ _ _ _ _ _ _ _

/-- 元の挿入色の全頂点の写像は単射（BF §2.2.6）。 -/
lemma insertedColorPathMap_injective {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    Function.Injective (insertedColorPathMap u v k c b) := by
  intro x y h
  unfold insertedColorPathMap at h
  apply Subtype.ext
  exact positiveCompositeSegmentInnerVertex_source_injective u v k c _ _ x.val _ _ _ y.val _
    (congrArg Subtype.val h)

end SerrePositivity.EInfinity.SimplexCuts

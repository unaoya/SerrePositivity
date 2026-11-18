module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositeSegmentInnerVertexInjective
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CompositePositionDecomposition

/-!
模型。文献の定義との比較は後で
# 元の挿入色の全頂点から同じ内側切断への写像

Berger–Fresse §2.2.6、M14 L12a のC451の指定面の比較。
元の合成位置の部分語分解を使い、同じ内側頂点を読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の挿入色の全頂点を、同じ内側Cutの同じ色の頂点へ送る（BF §2.2.6）。 -/
def insertedColorPathMap {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k c.1).val
      (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m (n + 1) k b)) →
      ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord v).val b) := by
  intro x
  have hxLabel : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k c.1).val (c.2.horizontal x.val) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m (n + 1) k b := (Finset.mem_filter.mp x.property).2
  let hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositePosition_of_inserted_label u v k c.1 (c.2.horizontal x.val) b hxLabel
  let i := Classical.choose hs
  let z := Classical.choose (Classical.choose_spec hs)
  have hx := Classical.choose_spec (Classical.choose_spec hs)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentInnerVertex u v k c i z x.val hx,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.insertedPosition_injective m (n + 1) k
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentInnerVertex_label u v k c i z x.val hx).symm.trans hxLabel

/-- 元の挿入色の写像は、二段の指定面で同じ高さを読む（BF §2.2.6）。 -/
lemma insertedColorPathMap_vertices {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q) (b : Fin (n + 1))
    (x : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions c.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeCutWord u v k c.1).val
      (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m (n + 1) k b))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeOuterCut u v k c) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeInnerCut u v k c).vertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.insertedColorPathMap u v k c b x).val) =
        c.2.vertical x.val := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.insertedColorPathMap
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentInnerVertex_vertices _ _ _ _ _ _ _ _

/-- 元の挿入色の全頂点の写像は単射（BF §2.2.6）。 -/
lemma insertedColorPathMap_injective {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveCompositeCutIndex u v k q) (b : Fin (n + 1)) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.insertedColorPathMap u v k c b) := by
  intro x y h
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.insertedColorPathMap at h
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveCompositeSegmentInnerVertex_source_injective u v k c _ _ x.val _ _ _ y.val _
    (congrArg Subtype.val h)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

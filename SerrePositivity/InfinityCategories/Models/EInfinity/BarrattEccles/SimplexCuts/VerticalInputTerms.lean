module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VerticalBoundarySigns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VerticalMappedVertices
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MappedDeletedTensors

/-!
模型。文献の定義との比較は後で
# 垂直出力境界項と同じ入力面の項

Berger–Fresse §2.2.6–7、M14 L09a。
実符号と指定面の比較を、元の正規化生成元の境界項へ接続する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C246：同じ語と一つ小さい入力次数の共通次数の一致。 -/
lemma verticalDeletion_degree_eq {m q r : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) :
    -((m + q + 1 - r : ℕ) : ℤ) = -((m + (q + 1) + 1 - r : ℕ) : ℤ) + 1 := by
  have hr := v.arity_le_length
  omega

/-- C247：垂直削除の指定座標から、同じ入力面の符号付き実境界項へ戻す。 -/
lemma outputBoundaryTerm_vertical_of_coordinates {m q r : ℕ} (S : SSet.{0})
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q + 1)) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1))
    (k : Fin (m + (q + 1) + 1)) (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) + 1))
    (hj : j.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank s v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) k) (x : S _⦋q + 1⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val k) j x =
      (-1 : ℤ) ^ (m + 1 - r + (s.vertical k).val) •
        (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).X z)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalDeletion_degree_eq (q := q) v))).hom
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S t v (S.δ (s.vertical k) x)) := by
  have hd := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_pos_vertical s v k hk
  have hl : ∀ c, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList s v.val k c =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList t v.val c).map (SimplexCategory.δ (s.vertical k)).toOrderHom := by
    intro c
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedVerticesList_vertical_of_coordinates s t v.val k hh hv c
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm
  rw [dite_eq_left hd, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySign_eq_at_of_rank s v k j hj,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySignAt_vertical_of_coordinates s t v k hk hh hv,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedCutTensor_eq_mapped_cutTensorAt A S s t v v k hd
      (SimplexCategory.δ (s.vertical k)) hl j hj x (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalDeletion_degree_eq v)]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm, map_zsmul, mul_smul]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

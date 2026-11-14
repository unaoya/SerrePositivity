module

public import SerrePositivity.EInfinity.SimplexCuts.VerticalBoundarySigns
public import SerrePositivity.EInfinity.SimplexCuts.VerticalMappedVertices
public import SerrePositivity.EInfinity.SimplexCuts.MappedDeletedTensors

/-!
# 垂直出力境界項と同じ入力面の項

Berger–Fresse §2.2.6–7、M14 L09a。
実符号と指定面の比較を、元の正規化生成元の境界項へ接続する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C246：同じ語と一つ小さい入力次数の共通次数の一致。 -/
lemma verticalDeletion_degree_eq {m q r : ℕ} (v : Surjection.Word r (m + 1)) :
    -((m + q + 1 - r : ℕ) : ℤ) = -((m + (q + 1) + 1 - r : ℕ) : ℤ) + 1 := by
  have hr := v.arity_le_length
  omega

/-- C247：垂直削除の指定座標から、同じ入力面の符号付き実境界項へ戻す。 -/
lemma outputBoundaryTerm_vertical_of_coordinates {m q r : ℕ} (S : SSet.{0})
    (s : Cut m (q + 1)) (t : Cut m q) (v : Surjection.Word r (m + 1))
    (k : Fin (m + (q + 1) + 1)) (hk : boundaryVertexKind s k = .vertical)
    (hh : ∀ j : Fin (m + q + 1), s.horizontal (k.succAbove j) = t.horizontal j)
    (hv : ∀ j : Fin (m + q + 1), s.vertical (k.succAbove j) =
      (s.vertical k).succAbove (t.vertical j))
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q + 1⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x =
      (-1 : ℤ) ^ (m + 1 - r + (s.vertical k).val) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (verticalDeletion_degree_eq (q := q) v))).hom
            (cutTerm A S t v (S.δ (s.vertical k) x)) := by
  have hd := outputDegree_pos_vertical s v k hk
  have hl : ∀ c, deletedVerticesList s v.val k c =
      (verticesList t v.val c).map (SimplexCategory.δ (s.vertical k)).toOrderHom := by
    intro c
    exact deletedVerticesList_vertical_of_coordinates s t v.val k hh hv c
  unfold outputBoundaryTerm
  rw [dite_eq_left hd, outputBoundarySign_eq_at_of_rank s v k j hj,
    outputBoundarySignAt_vertical_of_coordinates s t v k hk hh hv,
    deletedCutTensor_eq_mapped_cutTensorAt A S s t v v k hd
      (SimplexCategory.δ (s.vertical k)) hl j hj x (verticalDeletion_degree_eq v)]
  simp only [cutTerm, map_zsmul, mul_smul]
  rfl

end SerrePositivity.EInfinity.SimplexCuts

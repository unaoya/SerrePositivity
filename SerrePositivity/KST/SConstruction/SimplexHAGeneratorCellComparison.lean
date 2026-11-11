module
public import SerrePositivity.KST.SConstruction.SimplexHAGeneratorStandardCell
public import SerrePositivity.KST.SConstruction.SimplexHADecodeCells
public import SerrePositivity.KST.SConstruction.SimplexHAGeneratorValues

/-! # 元の全生成元読み替えと実標準面像の一致
概要：零・一端点と辺を読む全 bead 語の実鎖射を、元の標準面像と同定する。
方針：自由座標を保つ両者の三再帰と、実 Serre 分割合成の比較で帰納する。
規約：元の端点と自由次元を保持。使われ方：native HA 成分からの逆 Hom 射の構成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 零次元読み替えは、同じ右側 bead の実鎖射を回収する。 -/
lemma simplexHABeadWordDecode_base_cell {k : ℕ} (i : SerreCubeGeneratorIndex 0)
    (v : Fin 1 ↪o Fin (k + 1)) (T : Finset (Fin (k + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last 0) < t) :
    HEq (simplexHABeadWordCell A (simplexHABeadWordDecode 0 i v T hT hb))
      (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v 0) hb)) :=
  simplexHABeadWordCell_reindex A rfl
    (show T.card - 1 = serreCubeGeneratorFreeDimension 0 i + T.card - 1 by
      simp only [serreCubeGeneratorFreeDimension, zero_add]) _

/-- 全生成元の元の読み替え実鎖射は、同じ読み替え次元の標準面像そのもの。 -/
lemma simplexHABeadWordDecode_cell_standard {k : ℕ} (m : ℕ)
    (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1) ↪o Fin (k + 1))
    (T : Finset (Fin (k + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last m) < t) :
    simplexHABeadWordCell A (simplexHABeadWordDecode m i v T hT hb) =
      simplexHAGeneratorStandardCell A m i v T hT hb := by
  apply eq_of_heq
  induction m generalizing T with
  | zero =>
    exact (simplexHABeadWordDecode_base_cell A i v T hT hb).trans
      (simplexHAGeneratorStandardCell_zero A i v T hT hb).symm
  | succ m ih =>
    obtain ⟨i, j⟩ := i
    fin_cases j
    · exact (heq_of_eq (simplexHABeadWordDecode_zero_cell A m i v T hT hb)).trans
        ((ih i (Fin.castSuccOrderEmb.trans v) T hT
          (simplexHADecodePrefix_tail m v T hb)).trans
            (heq_of_eq (simplexHAGeneratorStandardCell_point_zero A m i v T hT hb).symm))
    · have hl := ih i (Fin.castSuccOrderEmb.trans v)
        {v (Fin.last (m + 1))} (Finset.singleton_nonempty _)
        (simplexHADecodePrefix_cut m v)
      have hc := serreCubeChainComposition_heq A rfl rfl rfl rfl rfl
        (simplexHABeadWordCell A (simplexHABeadWordDecode m i (Fin.castSuccOrderEmb.trans v)
          {v (Fin.last (m + 1))} (Finset.singleton_nonempty _) (simplexHADecodePrefix_cut m v)))
        (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (m + 1))) hb))
        (simplexHAGeneratorStandardCell A m i (Fin.castSuccOrderEmb.trans v)
          {v (Fin.last (m + 1))} (Finset.singleton_nonempty _) (simplexHADecodePrefix_cut m v))
        (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT (v (Fin.last (m + 1))) hb)) hl HEq.rfl
      exact (simplexHABeadWordDecode_one_cell A m i v T hT hb).trans
        (hc.trans (simplexHAGeneratorStandardCell_point_one A m i v T hT hb).symm)
    · exact (simplexHABeadWordDecode_edge_cell A m i v T hT hb).trans
        ((ih i (Fin.castSuccOrderEmb.trans v) (insert (v (Fin.last (m + 1))) T)
          (Finset.insert_nonempty _ T) (simplexHADecodePrefix_insert m v T hb)).trans
            (simplexHAGeneratorStandardCell_edge A m i v T hT hb).symm)

/-- 元の生成元語の実鎖射は、元の標準面を同じ部分集合生成射へ前合成した射。 -/
lemma simplexHAGeneratorWord_cell_standard {k : ℕ} (m : ℕ)
    (i : SerreCubeGeneratorIndex m) (v : Fin (m + 1) ↪o Fin (k + 1))
    (b : Fin (k + 1)) (hb : v (Fin.last m) < b) :
    simplexHABeadWordCell A (simplexHAGeneratorWord m i v b hb) =
      (serreCubeFaceNormal A (serreCubeGeneratorFaceNormal m i)).hom ≫
        simplexHADecodeSubsetCell A m v {b} (Finset.singleton_nonempty b)
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) := by
  have h := simplexHABeadWordDecode_cell_standard A m i v {b} (Finset.singleton_nonempty b)
    (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)
  exact h.trans (congrArg (fun f => f ≫ simplexHADecodeSubsetCell A m v {b}
    (Finset.singleton_nonempty b) (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb))
      (serreCubeGeneratorDecodeFace_singleton A m i b))

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.InfinityCategories.Kan.CubeCoordinateCompletion

/-! # 空の support の定数出力を元へ戻す面の補完
概要：空でない出力の評価から、零・一の定数出力を挿入して元の全出力を回収する。
方針：元の零頂点での値を背景に取り、support の空性で二つの場合を判定する。
規約：定数一と定数零を区別する。使われ方：入力削除・max・面の具体的な因数分解。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 空でない support を持つ出力では、元の零頂点の値は零。 -/
lemma cubeSupportOutputEmbedding_zero {n m : ℕ} (s : CubeJoinNormalForm n m)
    (a : Fin (cubeSupportNonemptyOutputs s).card) :
    cubeJoinNormalFormEval s ⊥ (cubeSupportOutputEmbedding s a) = false := by
  have ha : (cubeJoinNormalFormSupport s (cubeSupportOutputEmbedding s a)).Nonempty :=
    (mem_cubeSupportNonemptyOutputs s _).mp (Finset.orderEmbOfFin_mem _ rfl a)
  cases hs : s (cubeSupportOutputEmbedding s a) with
  | none => simp [cubeJoinNormalFormSupport, hs] at ha
  | some t => simp [cubeJoinNormalFormEval, hs, cubeJoinTermEval_bot]

/-- 空の support の出力は、元の零頂点と同じ定数値。 -/
lemma cubeJoinNormalFormEval_outside {n m : ℕ} (s : CubeJoinNormalForm n m)
    (x : CubeVertex n) (j : Fin m) (hj : j ∉ cubeSupportNonemptyOutputs s) :
    cubeJoinNormalFormEval s x j = cubeJoinNormalFormEval s ⊥ j := by
  have ht : cubeJoinNormalFormSupport s j = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hn
    exact hj ((mem_cubeSupportNonemptyOutputs s j).mpr hn)
  cases hs : s j with
  | none => simp [cubeJoinNormalFormEval, hs, cubeJoinTermEval]
  | some t =>
    have htempty : t = ∅ := by simpa only [cubeJoinNormalFormSupport, hs, Option.getD_some] using ht
    simp [cubeJoinNormalFormEval, hs, htempty, cubeJoinTermEval]

/-- 元の表示の空の support に指定した零・一を挿入する実際の面の合成。 -/
def cubeSupportOutputCompletion {n m : ℕ} (s : CubeJoinNormalForm n m) :
    ConcreteCube.mk (cubeSupportNonemptyOutputs s).card ⟶ ConcreteCube.mk m :=
  ⟨cubeCoordinateComplete (cubeSupportOutputEmbedding s) (cubeJoinNormalFormEval s ⊥),
    cubeCoordinateComplete_generated _ (cubeSupportOutputEmbedding s).strictMono _
      (cubeSupportOutputEmbedding_zero s)⟩

/-- 元の表示の非定数出力を選択して補完すると、元の全評価を回収する。 -/
lemma cubeSupportOutputCompletion_recover {n m : ℕ} (s : CubeJoinNormalForm n m)
    (x : CubeVertex n) :
    (cubeSupportOutputCompletion s).val
      (cubeCoordinateSelect (cubeSupportOutputEmbedding s) (cubeJoinNormalFormEval s x)) =
        cubeJoinNormalFormEval s x := by
  funext j
  by_cases hj : j ∈ Set.range (cubeSupportOutputEmbedding s)
  · obtain ⟨a, rfl⟩ := hj
    exact cubeCoordinateComplete_image _ (cubeSupportOutputEmbedding s).injective _
      (cubeSupportOutputEmbedding_zero s) _ a
  · change cubeCoordinateComplete _ _ _ j = _
    rw [cubeCoordinateComplete_outside _ _ _ j hj]
    have hnot : j ∉ cubeSupportNonemptyOutputs s := by
      simpa only [cubeSupportOutputEmbedding, Finset.range_orderEmbOfFin, Finset.mem_coe] using hj
    exact (cubeJoinNormalFormEval_outside s x j hnot).symm

/-- 元のブロック max の後で定数出力を補完すると、元の表示を全て回収する。 -/
lemma cubeSupportMax_completion_eval {n m : ℕ} {s : CubeJoinNormalForm n m}
    (h : CubeSupportPartition s) (x : CubeVertex n) :
    (cubeSupportOutputCompletion s).val ((cubeSupportMax h).val x) =
      cubeJoinNormalFormEval s x := by
  have hmax : (cubeSupportMax h).val x =
      cubeCoordinateSelect (cubeSupportOutputEmbedding s) (cubeJoinNormalFormEval s x) := by
    funext a
    exact cubeSupportBlockMap_eval h x a
  rw [hmax]
  exact cubeSupportOutputCompletion_recover s x

/-- 全入力を使う元の具体射は、隣接 max の射と定数面の補完との元の合成。 -/
lemma cubeSupportMax_completion {X Y : ConcreteCube} (f : X ⟶ Y)
    (h : CubeSupportPartition (concreteCubeNormalForm f)) :
    cubeSupportMax h ≫ cubeSupportOutputCompletion (concreteCubeNormalForm f) = f := by
  apply Subtype.ext
  funext x
  exact (cubeSupportMax_completion_eval h x).trans (concreteCubeNormalForm_eval f x)

/-- 元の任意の具体射の、入力削除・隣接 max・定数面による厳密な因数分解。 -/
lemma concreteCube_deletion_max_face_factorization {X Y : ConcreteCube} (f : X ⟶ Y) :
    cubeNormalFormInputSelection (concreteCubeNormalForm f) ≫
      cubeSupportMax (concreteCubeInputCompressedSupportPartition f) ≫
        cubeSupportOutputCompletion (concreteCubeNormalForm (concreteCubeInputCompressed f)) =
          f := by
  rw [cubeSupportMax_completion, concreteCubeInputSelection_compressed]

end SerrePositivity.KST.SConstruction

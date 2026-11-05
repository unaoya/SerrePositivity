module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CubeCoordinateCompletion

/-! # 空の support の定数出力を元へ戻す面の補完
概要：空でない出力の評価から、零・一の定数出力を挿入して元の全出力を回収する。
方針：元の零頂点での値を背景に取り、support の空性で二つの場合を判定する。
規約：定数一と定数零を区別する。使われ方：入力削除・max・面の具体的な因数分解。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 空でない support を持つ出力では、元の零頂点の値は零。 -/
lemma cubeSupportOutputEmbedding_zero {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m)
    (a : Fin (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportNonemptyOutputs s).card) :
    _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s ⊥ (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s a) = false := by
  have ha : (_root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s a)).Nonempty :=
    (_root_.SerrePositivity.InfinityCategories.Kan.mem_cubeSupportNonemptyOutputs s _).mp (Finset.orderEmbOfFin_mem _ rfl a)
  cases hs : s (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s a) with
  | none => simp [_root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport, hs] at ha
  | some t => simp [_root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval, hs, _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinTermEval_bot]

/-- 空の support の出力は、元の零頂点と同じ定数値。 -/
lemma cubeJoinNormalFormEval_outside {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m)
    (x : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n) (j : Fin m) (hj : j ∉ _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportNonemptyOutputs s) :
    _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s x j = _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s ⊥ j := by
  have ht : _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport s j = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hn
    exact hj ((_root_.SerrePositivity.InfinityCategories.Kan.mem_cubeSupportNonemptyOutputs s j).mpr hn)
  cases hs : s j with
  | none => simp [_root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval, hs, _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinTermEval]
  | some t =>
    have htempty : t = ∅ := by simpa only [_root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormSupport, hs, Option.getD_some] using ht
    simp [_root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval, hs, htempty, _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinTermEval]

/-- 元の表示の空の support に指定した零・一を挿入する実際の面の合成。 -/
def cubeSupportOutputCompletion {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m) :
    _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportNonemptyOutputs s).card ⟶ _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube.mk m :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s) (_root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s ⊥),
    _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete_generated _ (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s).strictMono _
      (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding_zero s)⟩

/-- 元の表示の非定数出力を選択して補完すると、元の全評価を回収する。 -/
lemma cubeSupportOutputCompletion_recover {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m)
    (x : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n) :
    (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputCompletion s).val
      (_root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s) (_root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s x)) =
        _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s x := by
  funext j
  by_cases hj : j ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s)
  · obtain ⟨a, rfl⟩ := hj
    exact _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete_image _ (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s).injective _
      (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding_zero s) _ a
  · change _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete _ _ _ j = _
    rw [_root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateComplete_outside _ _ _ j hj]
    have hnot : j ∉ _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportNonemptyOutputs s := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding, Finset.range_orderEmbOfFin, Finset.mem_coe] using hj
    exact (_root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormEval_outside s x j hnot).symm

/-- 元のブロック max の後で定数出力を補完すると、元の表示を全て回収する。 -/
lemma cubeSupportMax_completion_eval {n m : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm n m}
    (h : _root_.SerrePositivity.InfinityCategories.Kan.CubeSupportPartition s) (x : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n) :
    (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputCompletion s).val ((_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax h).val x) =
      _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s x := by
  have hmax : (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax h).val x =
      _root_.SerrePositivity.InfinityCategories.Kan.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding s) (_root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval s x) := by
    funext a
    exact _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportBlockMap_eval h x a
  rw [hmax]
  exact _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputCompletion_recover s x

/-- 全入力を使う元の具体射は、隣接 max の射と定数面の補完との元の合成。 -/
lemma cubeSupportMax_completion {X Y : _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube} (f : X ⟶ Y)
    (h : _root_.SerrePositivity.InfinityCategories.Kan.CubeSupportPartition (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm f)) :
    _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax h ≫ _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputCompletion (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm f) = f := by
  apply Subtype.ext
  funext x
  exact (_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax_completion_eval h x).trans (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm_eval f x)

/-- 元の任意の具体射の、入力削除・隣接 max・定数面による厳密な因数分解。 -/
lemma concreteCube_deletion_max_face_factorization {X Y : _root_.SerrePositivity.InfinityCategories.Kan.ConcreteCube} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kan.cubeNormalFormInputSelection (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm f) ≫
      _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeInputCompressedSupportPartition f) ≫
        _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputCompletion (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeInputCompressed f)) =
          f := by
  rw [_root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax_completion, _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeInputSelection_compressed]

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCube_deletion_max_face_factorization := _root_.SerrePositivity.InfinityCategories.Kan.concreteCube_deletion_max_face_factorization

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinNormalFormEval_outside := _root_.SerrePositivity.InfinityCategories.Kan.cubeJoinNormalFormEval_outside

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportMax_completion := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax_completion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportMax_completion_eval := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportMax_completion_eval

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputCompletion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportOutputCompletion := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputCompletion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportOutputCompletion_recover := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputCompletion_recover

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportOutputEmbedding_zero := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputEmbedding_zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSupportOutputCompletion._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeSupportOutputCompletion._proof_1

module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShufflePath
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWFaces

/-!
# shuffle の隣接ステップ交換と混合面

概要：隣接する二つのステップを交換しても、その間の頂点を削除した二つの写像は変わらない。
方針：交換した二つのステップの両方が前半にあるか、両方が後半にある場合の計数を使う。
規約：KST Construction A.5 の標準 shuffle。符号の相殺は別に検証する。
使われ方：水平・垂直の混合境界項の対による相殺。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：二つのステップを交換した shuffle。
方針：選択集合を交換の置換で移す。濃度は保たれる。
規約：KST A.5、水平ステップ数を保つ。
使われ方：混合境界項の相手の shuffle を作る。 -/
def ShuffleIndex.swapSteps {p n : ℕ} (s : ShuffleIndex p n) (a b : Fin n) : ShuffleIndex p n :=
  ⟨s.val.map (Equiv.swap a b).toEmbedding, by rw [Finset.card_map, s.property]⟩

/-- 概要：隣接ステップの間の頂点以外では第一座標は交換で変わらない。
方針：前半のステップ集合を交換で移す計数の同値を使う。
規約：KST A.5、ステップ k と k+1 を交換。
使われ方：混合面の削除後の第一写像の同定。 -/
lemma ShuffleIndex.swapSteps_left_prefix {p n : ℕ} (s : ShuffleIndex p (n + 2))
    (k : Fin (n + 1)) (x : Fin (n + 3)) (hx : (x : ℕ) ≠ (k : ℕ) + 1) :
    ((s.swapSteps k.castSucc k.succ).left.toOrderHom x : ℕ) = (s.left.toOrderHom x : ℕ) := by
  rw [ShuffleIndex.left_apply, ShuffleIndex.left_apply]
  change (((s.val.map (Equiv.swap k.castSucc k.succ).toEmbedding).filter
    (fun j : Fin (n + 2) ↦ (j : ℕ) < (x : ℕ))).card) = _
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro j _
  change ((Equiv.swap k.castSucc k.succ j : Fin (n + 2)) : ℕ) < (x : ℕ) ↔
    (j : ℕ) < (x : ℕ)
  rw [Equiv.swap_apply_def]
  split_ifs with ha hb
  · subst j
    change ((k : ℕ) + 1 < (x : ℕ)) ↔ (k : ℕ) < (x : ℕ)
    omega
  · subst j
    change ((k : ℕ) < (x : ℕ)) ↔ (k : ℕ) + 1 < (x : ℕ)
    omega
  · rfl

/-- 概要：隣接ステップの間の頂点以外では第二座標も交換で変わらない。
方針：二つの座標の和が頂点番号であることと第一座標の一致を使う。
規約：KST A.5、全ステップ数 n+2=p+q。
使われ方：混合面の削除後の第二写像の同定。 -/
lemma ShuffleIndex.swapSteps_right_prefix {p q n : ℕ} (s : ShuffleIndex p (n + 2))
    (h : p + q = n + 2) (k : Fin (n + 1)) (x : Fin (n + 3))
    (hx : (x : ℕ) ≠ (k : ℕ) + 1) :
    (((s.swapSteps k.castSucc k.succ).right h).toOrderHom x : ℕ) =
      ((s.right h).toOrderHom x : ℕ) := by
  have h₁ := (s.swapSteps k.castSucc k.succ).coordinates_add h x
  have h₂ := s.coordinates_add h x
  have h₃ := s.swapSteps_left_prefix k x hx
  omega

/-- 概要：隣接ステップの間の頂点を削除した面はその頂点を通らない。
方針：指定頂点を飛ばす順序包含の二つの分岐を評価する。
規約：KST A.5、内部の混合面。
使われ方：交換で変わらない前半ステップ数の公式の適用。 -/
lemma shuffleMixedFaceVertex_ne {n : ℕ} (k : Fin (n + 1)) (j : Fin (n + 2)) :
    (((SimplexCategory.δ k.succ.castSucc).toOrderHom j) : ℕ) ≠ (k : ℕ) + 1 := by
  rw [awFace_apply]
  change (if (j : ℕ) < (k : ℕ) + 1 then (j : ℕ) else (j : ℕ) + 1) ≠ (k : ℕ) + 1
  split_ifs <;> omega

/-- 概要：間の頂点を削除すると、隣接ステップの交換前後の第一写像は一致。
方針：面の像の各頂点で前半ステップ数の不変性を適用する。
規約：KST A.5 の標準 shuffle。
使われ方：混合境界項の二つの退化写像の同定。 -/
lemma ShuffleIndex.swapSteps_left_face {p n : ℕ} (s : ShuffleIndex p (n + 2))
    (k : Fin (n + 1)) :
    SimplexCategory.δ k.succ.castSucc ≫ (s.swapSteps k.castSucc k.succ).left =
      SimplexCategory.δ k.succ.castSucc ≫ s.left := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  exact s.swapSteps_left_prefix k _ (shuffleMixedFaceVertex_ne k j)

/-- 概要：間の頂点を削除すると、隣接ステップの交換前後の第二写像も一致。
方針：面の像の各頂点で第二座標の不変性を適用する。
規約：KST A.5 の標準 shuffle。
使われ方：混合境界項の二つの退化写像の同定。 -/
lemma ShuffleIndex.swapSteps_right_face {p q n : ℕ} (s : ShuffleIndex p (n + 2))
    (h : p + q = n + 2) (k : Fin (n + 1)) :
    SimplexCategory.δ k.succ.castSucc ≫ (s.swapSteps k.castSucc k.succ).right h =
      SimplexCategory.δ k.succ.castSucc ≫ s.right h := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  exact s.swapSteps_right_prefix h k _ (shuffleMixedFaceVertex_ne k j)

/-- 概要：隣接ステップを交換した二つの shuffle の混合面の実テンソル写像は等しい。
方針：二つの単体写像の混合面の一致を反変な整数加群に送り、テンソルする。
規約：KST A.5、交代符号を付ける前の等式。
使われ方：逆転数の符号の反転と組み合わせる混合境界項の相殺。 -/
lemma shuffleSwapMixedFace_map
    (C D : SimplicialObject (ModuleCat.{u} ℤ)) {p q n : ℕ} (s : ShuffleIndex p (n + 2))
    (h : p + q = n + 2) (k : Fin (n + 1)) :
    integerTensorMap (C.map (s.swapSteps k.castSucc k.succ).left.op)
        (D.map ((s.swapSteps k.castSucc k.succ).right h).op) ≫
      integerTensorMap (C.δ k.succ.castSucc) (D.δ k.succ.castSucc) =
    integerTensorMap (C.map s.left.op) (D.map (s.right h).op) ≫
      integerTensorMap (C.δ k.succ.castSucc) (D.δ k.succ.castSucc) := by
  have hc := congrArg (fun f ↦ C.map f.op) (s.swapSteps_left_face k)
  have hd := congrArg (fun f ↦ D.map f.op) (s.swapSteps_right_face h k)
  simp only [op_comp, C.map_comp] at hc
  simp only [op_comp, D.map_comp] at hd
  rw [← integerTensorMap_comp, ← integerTensorMap_comp]
  exact congrArg₂ integerTensorMap hc hd

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories



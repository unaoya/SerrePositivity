module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CubeNormalFormRestriction

/-! # 選択した入力を元の座標へ戻す零面挿入
概要：順序を保つ座標選択に対し、他の座標を零で埋める実際の逆向き射を作る。
方針：各座標の有限 max で定義し、未使用座標の零面挿入による次元帰納を使う。
規約：選択との合成は恒等。使われ方：圧縮した表示も元の具体的 cubical 射として実現する。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 指定された入力座標だけを戻し、他の座標を零で埋める元の頂点関数。 -/
def cubeCoordinateInsert {n m : ℕ} (e : Fin m → Fin n) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n :=
  fun x i => (Finset.univ.filter (fun j => e j = i)).sup x

/-- 零埋め挿入の真の値は、元の選択の同じ添字で検出される。 -/
lemma cubeCoordinateInsert_true_iff {n m : ℕ} (e : Fin m → Fin n)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert e x i = true ↔ ∃ j, e j = i ∧ x j = true := by
  change (Finset.univ.filter (fun j => e j = i)).sup x = ⊤ ↔ _
  rw [Finset.sup_eq_top_iff]
  simp

/-- 入力を戻してから同じ座標を選ぶと、元の全頂点を厳密に回収する。 -/
lemma cubeCoordinateSelect_insert {n m : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect e (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert e x) = x := by
  funext j
  apply Bool.eq_iff_iff.mpr
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert e x (e j) = true ↔ x j = true
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert_true_iff]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact he hi ▸ hx
  · intro hx
    exact ⟨j, rfl, hx⟩

/-- 元の零埋め挿入は、低次元の挿入と元の未使用座標への零面の合成。 -/
lemma cubeCoordinateInsert_lower {n m : ℕ} (e : Fin m → Fin (n + 1))
    (p : Fin (n + 1)) (hp : ∀ j, e j ≠ p) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert e = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace false n p ∘
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower e p hp) := by
  funext x k
  refine Fin.succAboveCases p ?_ (fun k => ?_) k
  · apply Bool.eq_iff_iff.mpr
    change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert e x p = true ↔ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace false n p _ p = true
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert_true_iff]
    simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, hp]
  · apply Bool.eq_iff_iff.mpr
    change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert e x (p.succAbove k) = true ↔
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace false n p _ (p.succAbove k) = true
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, Fin.insertNth_apply_succAbove, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert_true_iff]
    apply exists_congr
    intro j
    rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower_spec e p hp j,
      (Fin.strictMono_succAbove p).injective.eq_iff]

/-- 順序を保つ選択に対する零埋め挿入は、元の零面の合成として生成される。 -/
lemma cubeCoordinateInsert_generated {n m : ℕ} (e : Fin m → Fin n) (he : StrictMono e) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert e) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero =>
      have h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert e = (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex 0 → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex 0) := by
        funext x j
        exact Fin.elim0 j
      rw [h]
      exact .id 0
    | succ m => exact Fin.elim0 (e 0)
  | succ n ih =>
    by_cases hs : Function.Surjective e
    · have hm : m = n + 1 := by
        simpa only [Fintype.card_fin] using Fintype.card_of_bijective ⟨he.injective, hs⟩
      subst m
      have hid : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert e = (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1) → _) := by
        funext x j
        apply Bool.eq_iff_iff.mpr
        rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert_true_iff, he.eq_id]
        simp
      rw [hid]
      exact .id (n + 1)
    · simp only [Function.Surjective, not_forall, not_exists] at hs
      obtain ⟨p, hp⟩ := hs
      rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert_lower e p hp]
      exact .comp (ih _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower_strictMono e p hp he)) (.face false n p)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

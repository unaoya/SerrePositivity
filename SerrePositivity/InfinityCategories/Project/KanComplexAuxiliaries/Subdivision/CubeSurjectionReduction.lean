module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Pullbacks.CubeAdjacentFiber

/-! # 単調全射の隣接同値座標による縮約
概要：同じ値を持つ隣接二入力を一つにまとめ、元の単調全射を低次元へ移す。
方針：片方を飛ばす順序埋め込みで制限し、Fin.predAbove との合成を回収する。
規約：元の入力順序を保持する。使われ方：fiber max の隣接 connection による生成。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 隣接二座標の先の一方を除いた元の座標写像。 -/
def cubeSurjectionLower {n m : ℕ} (q : Fin (n + 2) → Fin m)
    (p : Fin (n + 1)) : Fin (n + 1) → Fin m :=
  q ∘ p.castSucc.succAbove

/-- 隣接二入力が同じ値なら、元の写像を縮約と同一視の合成から回収する。 -/
lemma cubeSurjectionLower_factor {n m : ℕ} (q : Fin (n + 2) → Fin m)
    (p : Fin (n + 1)) (hp : q p.castSucc = q p.succ) :
    q = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSurjectionLower q p ∘ p.predAbove := by
  funext i
  by_cases hi : i = p.castSucc
  · subst i
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSurjectionLower, hp]
  · simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSurjectionLower, Fin.succAbove_predAbove hi]

/-- 縮約した元の座標写像も単調。 -/
lemma cubeSurjectionLower_monotone {n m : ℕ} (q : Fin (n + 2) → Fin m)
    (p : Fin (n + 1)) (hq : Monotone q) : Monotone (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSurjectionLower q p) :=
  hq.comp (Fin.strictMono_succAbove p.castSucc).monotone

/-- 隣接二入力が同じ値なら、縮約した元の写像も全射。 -/
lemma cubeSurjectionLower_surjective {n m : ℕ} (q : Fin (n + 2) → Fin m)
    (p : Fin (n + 1)) (hp : q p.castSucc = q p.succ) (hq : Function.Surjective q) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSurjectionLower q p) := by
  intro j
  obtain ⟨i, hi⟩ := hq j
  exact ⟨p.predAbove i, (congrFun (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSurjectionLower_factor q p hp) i).symm.trans hi⟩

/-- 厳密単調でない単調写像には、同じ値を持つ隣接二入力がある。 -/
lemma cubeMonotone_exists_adjacent_eq {n m : ℕ} (q : Fin (n + 2) → Fin m)
    (hq : Monotone q) (hn : ¬ StrictMono q) :
    ∃ p : Fin (n + 1), q p.castSucc = q p.succ := by
  rw [Fin.strictMono_iff_lt_succ] at hn
  simp only [not_forall, not_lt] at hn
  obtain ⟨p, hp⟩ := hn
  exact ⟨p, le_antisymm (hq p.castSucc_le_succ) hp⟩

/-- 同じ隣接入力を縮約した fiber max は、元の connection の後で評価できる。 -/
lemma cubeFiberMax_lower {n m : ℕ} (q : Fin (n + 2) → Fin m)
    (p : Fin (n + 1)) (hp : q p.castSucc = q p.succ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax q = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSurjectionLower q p) ∘ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n p := by
  conv_lhs => rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSurjectionLower_factor q p hp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_comp, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_predAbove]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

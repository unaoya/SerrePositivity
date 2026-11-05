module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CubeAdjacentFiber

/-! # 単調全射の隣接同値座標による縮約
概要：同じ値を持つ隣接二入力を一つにまとめ、元の単調全射を低次元へ移す。
方針：片方を飛ばす順序埋め込みで制限し、Fin.predAbove との合成を回収する。
規約：元の入力順序を保持する。使われ方：fiber max の隣接 connection による生成。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction

/-- 隣接二座標の先の一方を除いた元の座標写像。 -/
def cubeSurjectionLower {n m : ℕ} (q : Fin (n + 2) → Fin m)
    (p : Fin (n + 1)) : Fin (n + 1) → Fin m :=
  q ∘ p.castSucc.succAbove

/-- 隣接二入力が同じ値なら、元の写像を縮約と同一視の合成から回収する。 -/
lemma cubeSurjectionLower_factor {n m : ℕ} (q : Fin (n + 2) → Fin m)
    (p : Fin (n + 1)) (hp : q p.castSucc = q p.succ) :
    q = cubeSurjectionLower q p ∘ p.predAbove := by
  funext i
  by_cases hi : i = p.castSucc
  · subst i
    simp [cubeSurjectionLower, hp]
  · simp [cubeSurjectionLower, Fin.succAbove_predAbove hi]

/-- 縮約した元の座標写像も単調。 -/
lemma cubeSurjectionLower_monotone {n m : ℕ} (q : Fin (n + 2) → Fin m)
    (p : Fin (n + 1)) (hq : Monotone q) : Monotone (cubeSurjectionLower q p) :=
  hq.comp (Fin.strictMono_succAbove p.castSucc).monotone

/-- 隣接二入力が同じ値なら、縮約した元の写像も全射。 -/
lemma cubeSurjectionLower_surjective {n m : ℕ} (q : Fin (n + 2) → Fin m)
    (p : Fin (n + 1)) (hp : q p.castSucc = q p.succ) (hq : Function.Surjective q) :
    Function.Surjective (cubeSurjectionLower q p) := by
  intro j
  obtain ⟨i, hi⟩ := hq j
  exact ⟨p.predAbove i, (congrFun (cubeSurjectionLower_factor q p hp) i).symm.trans hi⟩

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
    cubeFiberMax q = cubeFiberMax (cubeSurjectionLower q p) ∘ cubeVertexConnection n p := by
  conv_lhs => rw [cubeSurjectionLower_factor q p hp]
  rw [cubeFiberMax_comp, cubeFiberMax_predAbove]

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeFiberMax_lower := _root_.SerrePositivity.InfinityCategories.Kan.cubeFiberMax_lower

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeMonotone_exists_adjacent_eq := _root_.SerrePositivity.InfinityCategories.Kan.cubeMonotone_exists_adjacent_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeSurjectionLower (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSurjectionLower := _root_.SerrePositivity.InfinityCategories.Kan.cubeSurjectionLower

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSurjectionLower_factor := _root_.SerrePositivity.InfinityCategories.Kan.cubeSurjectionLower_factor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSurjectionLower_monotone := _root_.SerrePositivity.InfinityCategories.Kan.cubeSurjectionLower_monotone

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSurjectionLower_surjective := _root_.SerrePositivity.InfinityCategories.Kan.cubeSurjectionLower_surjective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeSurjectionLower.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeSurjectionLower.eq_1

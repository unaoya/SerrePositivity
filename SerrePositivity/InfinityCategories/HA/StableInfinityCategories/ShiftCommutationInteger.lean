module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ShiftCommutationGroup

/-! # 一回シフトとの比較から全整数シフトへの延長

概要：任意の関手の一回シフトとの交換同型を、全整合条件を満たす CommShift ℤ へ延長する。
方針：次数一の交換同型を次数付き交換同型群の元とし、その整数冪を取る。
規約：一回の比較を厳密に復元する。使われ方：S6 の h C 上の三角関手。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u v' u'
open CategoryTheory
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasShift C ℤ] [HasShift D ℤ] {F : C ⥤ D}

local instance : Group (Σ n : ℤ, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutationIso F n) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableShiftCommutation_group F

/-- 概要：次数の等式で交換同型の添字を移す。
方針：等式による輸送を使う。
規約：同型の成分は変更しない。使われ方：整数冪から指定次数の比較を取り出す。 -/
def stableShiftCommutationIsoOfDegree (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F) {n : ℤ}
    (h : e.1 = n) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutationIso F n := h ▸ e.2

/-- 概要：次数を輸送した比較を再び束ねると元の元に戻る。
方針：次数の等式で帰納する。
規約：依存和の厳密な等式。使われ方：整数冪の単位・積の転送。 -/
lemma stableShiftCommutationIsoOfDegree_mk (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F) {n : ℤ}
    (h : e.1 = n) :
    (⟨n, stableShiftCommutationIsoOfDegree e h⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F) = e := by
  cases e with
  | mk m e =>
    dsimp at h
    subst n
    rfl

/-- 概要：一回シフトの比較を次数一の群の元にする。
方針：次数と同型を束ねる。
規約：整数冪を取る対象の型を明示する。使われ方：全整数への延長の生成元。 -/
def stableShiftCommutationGenerator (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutationIso F 1) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F := ⟨1, e⟩

/-- 概要：次数一の比較の n 乗から次数 n の交換同型を得る。
方針：整数冪の次数の式で添字を輸送する。
規約：負の n も含む。使われ方：CommShift の同型の族。 -/
def stableShiftCommutationPower (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutationIso F 1) (n : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutationIso F n :=
  stableShiftCommutationIsoOfDegree ((stableShiftCommutationGenerator e) ^ n)
    (by simpa only [stableShiftCommutationGenerator, mul_one] using
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableShiftCommutation_zpow_degree F (stableShiftCommutationGenerator e) n)

/-- 概要：整数冪から得た比較を束ねると群の整数冪そのもの。
方針：添字輸送の復元を適用する。
規約：全整数。使われ方：シフトの整合条件の転送。 -/
lemma stableShiftCommutationPower_mk (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutationIso F 1) (n : ℤ) :
    (⟨n, stableShiftCommutationPower e n⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F) =
      (stableShiftCommutationGenerator e) ^ n :=
  stableShiftCommutationIsoOfDegree_mk _ _

/-- 概要：一回シフトとの任意の交換同型は整合的な整数シフトとの交換へ延長される。
方針：次数付き交換同型群の零乗・和の冪の式を同型の族へ移す。
規約：始域・終域の任意の整数シフトに適用できる。使われ方：完全関手の CommShift。 -/
@[instance_reducible]
def stableCommShiftOfOne (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutationIso F 1) : F.CommShift ℤ where
  commShiftIso n := stableShiftCommutationPower e n
  commShiftIso_zero := by
    apply sigma_mk_injective (i := (0 : ℤ))
    exact (stableShiftCommutationPower_mk e 0).trans (zpow_zero _)
  commShiftIso_add n m := by
    apply sigma_mk_injective (i := n + m)
    calc
      (⟨n + m, stableShiftCommutationPower e (n + m)⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F) =
          (stableShiftCommutationGenerator e) ^ (n + m) := stableShiftCommutationPower_mk e _
      _ = (stableShiftCommutationGenerator e) ^ n *
          (stableShiftCommutationGenerator e) ^ m := zpow_add _ _ _
      _ = (⟨n + m, Functor.CommShift.isoAdd (stableShiftCommutationPower e n)
          (stableShiftCommutationPower e m)⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F) := by
        rw [← stableShiftCommutationPower_mk e n, ← stableShiftCommutationPower_mk e m]
        rfl

/-- 概要：延長した CommShift の一回シフトの比較は元の同型と一致する。
方針：群の一乗の等式を比較に戻す。
規約：厳密な同型の等式。使われ方：三角形の第三射の照合。 -/
lemma stableCommShiftOfOne_one (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutationIso F 1) :
    letI := stableCommShiftOfOne e
    F.commShiftIso (1 : ℤ) = e := by
  change stableShiftCommutationPower e 1 = e
  apply sigma_mk_injective (i := (1 : ℤ))
  exact (stableShiftCommutationPower_mk e 1).trans (zpow_one _)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

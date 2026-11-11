module
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # 基底の部分集合による線形射影

概要：基底の指定部分集合に属する座標だけを残す射影を構成する。
方針：有限台関数を filter し、基底の座標同型で戻す。
規約：部分集合の有限性は不要。使われ方：semibasis の段と商の次数付き分裂。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
attribute [local instance] Classical.propDecidable
variable {S : Type u} [CommRing S] {V : Type v} [AddCommGroup V] [Module S V]
  {I : Type v} (E : Module.Basis I S V)

/-- 概要：指定部分集合の基底座標だけを残す線形射影。
方針：座標同型・有限台関数の filter・逆座標同型を合成する。
規約：部分集合は任意。使われ方：次数付き分裂の成分。 -/
def basisCoordinateCut (s : Set I) : V →ₗ[S] V := by
  classical
  let q : (I →₀ S) →ₗ[S] (I →₀ S) :=
    { toFun := Finsupp.filter (· ∈ s)
      map_add' _ _ := Finsupp.filter_add
      map_smul' _ _ := Finsupp.filter_smul }
  exact E.repr.symm.toLinearMap.comp (q.comp E.repr.toLinearMap)

/-- 概要：射影の座標は部分集合上で元の座標に等しく、それ以外は零。
方針：座標同型の逆写像の法則と filter の評価。
規約：古典的な所属判定を使う。使われ方：射影の代数的法則の証明。 -/
theorem basisCoordinateCut_repr (s : Set I) (x : V) (i : I) :
    E.repr (basisCoordinateCut E s x) i = if i ∈ s then E.repr x i else 0 := by
  classical
  change E.repr (E.repr.symm ((E.repr x).filter (· ∈ s))) i = _
  rw [E.repr.apply_symm_apply, Finsupp.filter_apply]

/-- 概要：射影の像は指定した基底元の線形包に入る。
方針：線形包の所属を基底座標の台で判定する。
規約：部分集合は無限でもよい。使われ方：射影の値域制限。 -/
theorem basisCoordinateCut_mem (s : Set I) (x : V) :
    basisCoordinateCut E s x ∈ Submodule.span S (E '' s) := by
  classical
  apply E.mem_span_image.mpr
  intro i hi
  by_contra hn
  have hc := Finsupp.mem_support_iff.mp hi
  rw [basisCoordinateCut_repr, ite_eq_right hn] at hc
  exact hc rfl

/-- 概要：指定した線形包上では射影は恒等である。
方針：指定集合外の基底座標は零である。
規約：同じ基底と部分集合を使う。使われ方：包含と retraction の単位則。 -/
theorem basisCoordinateCut_eq_self (s : Set I) {x : V}
    (hx : x ∈ Submodule.span S (E '' s)) : basisCoordinateCut E s x = x := by
  classical
  apply E.repr.injective
  apply Finsupp.ext
  intro i
  rw [basisCoordinateCut_repr]
  split_ifs with hi
  · rfl
  · exact (Finsupp.notMem_support_iff.mp
      (fun hm => hi (E.mem_span_image.mp hx hm))).symm

/-- 概要：互いに素な基底部分集合への二つの射影の合成は零である。
方針：各座標で二つの所属条件を同時に満たせない。
規約：射影の順序を明示する。使われ方：section と retraction の直交性。 -/
theorem basisCoordinateCut_disjoint (s t : Set I) (hst : Disjoint s t) (x : V) :
    basisCoordinateCut E s (basisCoordinateCut E t x) = 0 := by
  classical
  apply E.repr.injective
  apply Finsupp.ext
  intro i
  simp only [basisCoordinateCut_repr, map_zero, Finsupp.zero_apply]
  by_cases hs : i ∈ s
  · have ht : i ∉ t := fun ht => Set.disjoint_left.mp hst hs ht
    simp only [ite_eq_left hs, ite_eq_right ht]
  · simp only [ite_eq_right hs]

/-- 概要：互いに素な二つの基底部分集合で生成される要素は二つの射影に分解する。
方針：各座標がどちらに属するかで場合分けし、集合外の座標の零性を使う。
規約：分解する要素だけに生成条件を課す。使われ方：次数付き分裂の分解則。 -/
theorem basisCoordinateCut_add (s t : Set I) (hst : Disjoint s t) {x : V}
    (hx : x ∈ Submodule.span S (E '' (s ∪ t))) :
    basisCoordinateCut E s x + basisCoordinateCut E t x = x := by
  classical
  apply E.repr.injective
  apply Finsupp.ext
  intro i
  simp only [map_add, Finsupp.add_apply, basisCoordinateCut_repr]
  by_cases hs : i ∈ s
  · have ht : i ∉ t := fun ht => Set.disjoint_left.mp hst hs ht
    simp only [ite_eq_left hs, ite_eq_right ht, add_zero]
  · by_cases ht : i ∈ t
    · simp only [ite_eq_right hs, ite_eq_left ht, zero_add]
    · have hz : E.repr x i = 0 := Finsupp.notMem_support_iff.mp
        (fun hm => by
          rcases E.mem_span_image.mp hx hm with h | h
          · exact hs h
          · exact ht h)
      simp only [ite_eq_right hs, ite_eq_right ht, hz, zero_add]

end SerrePositivity.InfinityCategories.Project.DerivedCategories

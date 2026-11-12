module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Basic

/-!
概要：球面的境界の交代和と一面の簡約による保存。
方針：二つの非定数面の類の積を加法的な和へ移す。
規約：実際の次数は二以上であり、ホモトピー群の可換性を使う。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の微分の符号計算。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SphericalBoundary
end SerrePositivity.KST.Spectra.SphericalBoundary
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups


noncomputable section

variable {X : SSet.{u}} [KanComplex X] {n : ℕ} {x : X _⦋0⦌}

/-- 概要：境界定数単体の加法的ホモトピー類。
方針：構成済みの可換群を Additive で加法表示する。
規約：実際の次数は n + 2。
使われ方：Goerss–Jardine I §7。交代境界の各項。 -/
def additiveClass (a : X.PtSimplex (n + 2) x) :
    Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x) := Additive.ofMul (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk a)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups (additiveClass)


/-- 概要：定数単体の加法的な類は零。
方針：定数単体が乗法表示の単位元であることを使う。
規約：正次数の群の標準基点。
使われ方：Goerss–Jardine I §7。境界簡約の零の項。 -/
@[simp] theorem additiveClass_const :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass (RelativeMorphism.const : X.PtSimplex (n + 2) x) = 0 := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups (additiveClass_const)


/-- 概要：球面的な面の族のホモトピー類の交代和。
方針：各面の類に零から始まる交代符号を掛ける。
規約：和は可換群の中の有限和。
使われ方：Goerss–Jardine I §7、VIII §1。境界の向きの関係。 -/
def alternatingClass (a : Fin (n + 4) → X.PtSimplex (n + 2) x) :
    Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X (n + 1) x) :=
  ∑ j, (-1 : ℤ) ^ j.val • _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass (a j)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups (alternatingClass)


/-- 概要：二箇所以外が同じ有限和は、その二項の和の比較に帰着する。
方針：指定した二点を有限集合から順に除く。
規約：係数群は任意の可換加法群。
使われ方：Goerss–Jardine I §7。境界簡約による交代和の保存。 -/
private theorem sum_pair {ι A : Type*} [Fintype ι] [AddCommGroup A]
    (f g : ι → A) (i j : ι) (hij : j ≠ i)
    (hpair : f i + f j = g i + g j)
    (hrest : ∀ k, k ≠ i → k ≠ j → f k = g k) : ∑ k, f k = ∑ k, g k := by
  classical
  have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
  have hj : j ∈ (Finset.univ : Finset ι).erase i := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ f hi, ← Finset.add_sum_erase _ g hi,
    ← Finset.add_sum_erase _ f hj, ← Finset.add_sum_erase _ g hj,
    ← add_assoc, ← add_assoc, hpair]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact hrest k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    (Finset.mem_erase.mp hk).1

/-- 概要：逆元と積の充填による一面の簡約は交代和を保つ。
方針：二つの充填を群の等式に送り、二つ離れた面の符号の一致を使う。
規約：p より前の面は定数。簡約後の族は reduced。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。境界の反復簡約。 -/
theorem alternatingClass_reduce
    {a : Fin (n + 4) → X.PtSimplex (n + 2) x} {p : Fin (n + 2)}
    {ia b : X.PtSimplex (n + 2) x}
    (hi : PtSimplex.MulStruct ia (a p.castSucc.castSucc) .const p)
    (hb : PtSimplex.MulStruct b ia (a p.succ.succ) p)
    (hlower : ∀ j, j.val < p.val → a j = .const) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduced a p b) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass a := by
  have hinv := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq_at hi
  have hmul := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mul_eq_at hb
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a p.succ.succ) * _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (a p.castSucc.castSucc) := by
    rw [← hmul, mul_assoc, hinv, show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
      (RelativeMorphism.const : X.PtSimplex (n + 2) x) = 1 from rfl, mul_one]
  have hadd : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass b = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass (a p.succ.succ) +
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass (a p.castSucc.castSucc) := congrArg Additive.ofMul he
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass
  apply sum_pair _ _ p.castSucc.castSucc p.succ.succ
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduced, Fin.val_castSucc, Fin.val_succ,
      le_refl, ↓reduceIte, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass_const, smul_zero, zero_add]
    have hp : ¬p.val + 1 + 1 ≤ p.val := by omega
    simp only [hp, ↓reduceIte, hadd, smul_add]
    rw [show (-1 : ℤ) ^ (p.val + 1 + 1) = (-1 : ℤ) ^ p.val by
      simp [pow_succ]]
    exact add_comm _ _
  · intro j hj hj'
    have h0 : j.val ≠ p.val := fun h ↦ hj (Fin.ext h)
    have h2 : j.val ≠ p.val + 2 := fun h ↦ hj' (Fin.ext (by simpa using h))
    by_cases hlow : j.val ≤ p.val
    · rw [hlower j (by omega)]
      simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduced, hlow]
    · simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction.reduced, hlow, h2]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundary export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups (alternatingClass_reduce)


end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.additiveClass := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.additiveClass_const := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass_const

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.alternatingClass := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SphericalBoundary.alternatingClass_reduce := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.alternatingClass_reduce

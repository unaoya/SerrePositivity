module
public import Mathlib.AlgebraicTopology.SimplicialObject.Op
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# 単体の順序反転と交代面写像の符号

概要：単体的加群の順序反転で交代境界に現れる符号を計算する。
方針：面の添字を rev で置換し、二つの符号の積を比較する。
規約：KST Proposition 4.14、SW92 §1.2 の反対モノイドの bar の鎖比較。
使われ方：行側と列側の比較の自然な実鎖同型の符号。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：交代境界の順序反転で二つの面の符号を比較する。
方針：rev と元の添字の和は n+1 であり、各符号の二乗は 1。
規約：SW92 §1.2 の実鎖比較。使われ方：反転した交代境界の計算。 -/
lemma neg_one_pow_fin_rev (n : ℕ) (i : Fin (n + 2)) :
    (-1 : ℤ) ^ i.rev.val = (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ i.val := by
  have hs : (-1 : ℤ) ^ i.val * (-1 : ℤ) ^ i.val = 1 := by rw [← mul_pow]; simp
  have hp : (-1 : ℤ) ^ i.rev.val * (-1 : ℤ) ^ i.val = (-1 : ℤ) ^ (n + 1) := by
    rw [← pow_add, Fin.rev_add_cast]
  calc
    (-1 : ℤ) ^ i.rev.val =
        ((-1 : ℤ) ^ i.rev.val * (-1 : ℤ) ^ i.val) * (-1 : ℤ) ^ i.val := by
      rw [mul_assoc, hs, mul_one]
    _ = _ := by rw [hp]

/-- 概要：次数 n の順序反転の鎖符号。
方針：零次を 1 とし、次の次数で境界の反転符号を掛ける。
規約：閉式は (−1)^{n(n+1)/2}。使われ方：実反転鎖写像の各成分。 -/
def reversalChainSign : ℕ → ℤ
  | 0 => 1
  | n + 1 => (-1 : ℤ) ^ (n + 1) * reversalChainSign n

/-- 概要：順序反転の各次数の符号の二乗は 1。
方針：各 (−1) 冪の二乗と帰納法を使う。
規約：SW92 §1.2 の実鎖同型。使われ方：逆の鎖写像も同じ符号とする。 -/
lemma reversalChainSign_mul_self (n : ℕ) : reversalChainSign n * reversalChainSign n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs : (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1) = 1 := by rw [← mul_pow]; simp
    change ((-1 : ℤ) ^ (n + 1) * reversalChainSign n) *
      ((-1 : ℤ) ^ (n + 1) * reversalChainSign n) = 1
    calc
      _ = ((-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1)) *
          (reversalChainSign n * reversalChainSign n) := by ac_rfl
      _ = 1 := by rw [hs, ih, one_mul]

/-- 概要：順序を反転した単体的加群の交代境界の符号公式。
方針：面の自然同型を使い、有限和を rev によって再添字付けする。
規約：KST Proposition 4.14、SW92 §1.2 の反対 bar 比較の鎖部分。
使われ方：符号付き反転の実鎖写像の可換性。 -/
lemma alternatingReversalDifferential (X : SimplicialObject (ModuleCat.{u} ℤ)) (n : ℕ) :
    AlgebraicTopology.AlternatingFaceMapComplex.objD (SimplicialObject.opFunctor.obj X) n ≫
        SimplicialObject.opObjIso.hom =
      (-1 : ℤ) ^ (n + 1) •
        (SimplicialObject.opObjIso.hom ≫ AlgebraicTopology.AlternatingFaceMapComplex.objD X n) := by
  simp only [AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp,
    Preadditive.zsmul_comp, SimplicialObject.opFunctor_obj_δ, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Preadditive.comp_sum, Preadditive.comp_zsmul, Finset.smul_sum]
  refine Finset.sum_bij (fun (i : Fin (n + 2)) _ ↦ i.rev) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
  · intro i hi j hj hij
    exact Fin.rev_injective hij
  · intro j hj
    exact ⟨j.rev, Finset.mem_univ _, Fin.rev_rev j⟩
  · intro i hi
    rw [smul_smul, ← neg_one_pow_fin_rev n i.rev, Fin.rev_rev]

end SerrePositivity.KST.ProExcision

module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-!
概要：整数複体の左半分への制限は、非境界の全正次数で非輪状性を保つ。
方針：隣接三項の標準同型で完全性を元の整数複体へ移す。
規約：自然数鎖複体の零次数の完全性はここでは主張しない。
使われ方：Stacks Lemma 19.12.2、TT §3・§8、Toën §3.2 の小さい部分複体の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C]

/--
概要：非輪状な整数複体を左へ制限すると全正鎖次数で完全となる。
方針：隣接三項の制限同型を使う。
規約：上端の次数 top は任意。
使われ方：Stacks 19.12.2、TT §3 の自然数方向の帰納への入力。
-/
lemma leftRestriction_exactAt_succ (M : CochainComplex C ℤ) (hM : M.Acyclic)
    (top : ℤ) (n : ℕ) :
    (M.restriction (ComplexShape.embeddingUpIntLE top)).ExactAt (n + 1) := by
  let e := ComplexShape.embeddingUpIntLE top
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  let E := HomologicalComplex.restriction.sc'Iso M e (n + 2) (n + 1) n
    (i' := top - (n + 2)) (j' := top - (n + 1)) (k' := top - n) rfl rfl rfl
    (by simp <;> omega) (by simp <;> omega)
  apply (ShortComplex.exact_iff_of_iso E).mpr
  exact (HomologicalComplex.exactAt_iff' M (top - (n + 2)) (top - (n + 1))
    (top - n) (by simp <;> omega) (by simp <;> omega)).mp (hM _)

end SerrePositivity.KST.DerivedGeometry

module

public import SerrePositivity.AlgebraicGeometry.CechConstantComplex

/-!
概要：同じ複体を定数余単体図式にした二重複体の微分の評価。
方針：交代和の0/id公式を、各縦次数の同じ定数加群列へ渡す。
規約：係数環と加群の宇宙を分け、同じ複体と微分を保つ。
使われ方：F8の定数基底図式の正次数の商。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped BigOperators
universe u v
variable {R : Type v} [CommRing R] (A : CochainComplex (ModuleCat.{u} R) ℕ)

/-- 同じ複体を定数図式として既存の交代余面複体へ代入する。 -/
def cechConstantCochainComplex : CochainComplex (CochainComplex (ModuleCat.{u} R) ℕ) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} R) ℕ)).obj
    ((Functor.const SimplexCategory).obj A)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ定数二重複体の外微分は0と恒等を交互に取る。 -/
theorem cechConstantCochainComplex_d (n : ℕ) :
    (cechConstantCochainComplex A).d n (n + 1) = if Even (n + 2) then 0 else 𝟙 A := by
  dsimp only [cechConstantCochainComplex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (𝟙 A)) = _
  rw [← Finset.sum_smul, Fin.sum_neg_one_pow]
  split_ifs <;> simp only [zero_smul, one_smul]

set_option backward.isDefEq.respectTransparency false in
/-- 外微分の各縦成分は、同じ元の定数加群列の微分。 -/
theorem cechConstantCochainComplex_d_f (n b : ℕ) :
    ((cechConstantCochainComplex A).d n (n + 1)).f b =
      (cechConstantComplex (A.X b)).d n (n + 1) := by
  have h := congrArg (fun f : A ⟶ A ↦ f.f b) (cechConstantCochainComplex_d A n)
  have h' := cechConstantComplex_d (A.X b) n
  by_cases hn : Even (n + 2)
  · exact (h.trans (congrArg (fun f : A ⟶ A ↦ f.f b) (ite_eq_left hn))).trans
      (h'.trans (ite_eq_left hn)).symm
  · exact (h.trans (congrArg (fun f : A ⟶ A ↦ f.f b) (ite_eq_right hn))).trans
      (h'.trans (ite_eq_right hn)).symm

end SerrePositivity.AlgebraicGeometry

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData

/-! # 有限次数錐が次の図式単体に指定する全面

概要：次次数の図式単体と、既存の錐の下面から次の錐単体の全境界面を作る。
方針：零面に元の図式、正番号面に既存錐を置き、全共有面を照合する。
規約：零次からの最初の一段も含む。使われ方：実境界写像への貼り合わせ。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {f : K ⟶ X} {N : ℕ} (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N)

/-- 次次数の単体の零面は元の図式、残る面は既存の同じ錐単体。 -/
def truncatedConeNextFace (σ : K _⦋N + 1⦌) : Fin (N + 3) → X _⦋N + 1⦌ :=
  Fin.cases (f.app _ σ) (fun i => C.simplex N le_rfl (K.δ i σ))

/-- 次の単体に指定する全境界面は、全ての共有面上で厳密に一致する。 -/
lemma truncatedConeNextFace_compatible (σ : K _⦋N + 1⦌) (j k : Fin (N + 3)) (hjk : j < k) :
    X.δ (k.pred (Fin.ne_zero_of_lt hjk)) (truncatedConeNextFace C σ j) =
      X.δ (j.castPred (Fin.ne_last_of_lt hjk)) (truncatedConeNextFace C σ k) := by
  induction j using Fin.cases with
  | zero =>
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
    change X.δ k (f.app _ σ) = X.δ 0 (C.simplex N le_rfl (K.δ k σ))
    rw [C.face_zero]
    exact (ConcreteCategory.congr_hom (f.naturality (SimplexCategory.δ k).op) σ).symm
  | succ j =>
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
    have hjk' : j < k := Fin.succ_lt_succ_iff.mp hjk
    simp only [truncatedConeNextFace, Fin.cases_succ, Fin.pred_succ]
    rw [← Fin.succ_castPred_eq_castPred_succ (Fin.ne_last_of_lt hjk')]
    cases N with
    | zero =>
      have hj : j = (0 : Fin 2) := Fin.ext (by
        change j.val = 0
        have := j.isLt
        have := k.isLt
        omega)
      have hk : k = (1 : Fin 2) := Fin.ext (by
        change k.val = 1
        have := j.isLt
        have := k.isLt
        omega)
      subst j
      subst k
      change X.δ 1 (C.simplex 0 le_rfl (K.δ 0 σ)) =
        X.δ 1 (C.simplex 0 le_rfl (K.δ 1 σ))
      have he := (C.first_vertex 0 le_rfl (K.δ 0 σ)).trans
        (C.first_vertex 0 le_rfl (K.δ 1 σ)).symm
      rw [show SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 = SimplexCategory.δ (1 : Fin 2) from by decide]
        at he
      exact he
    | succ n =>
      have hk₀ : k ≠ 0 := Fin.ne_zero_of_lt hjk'
      have hl := C.face_positive n (by omega) (K.δ j σ) (k.pred hk₀)
      rw [Fin.succ_pred] at hl
      have hr := C.face_positive n (by omega) (K.δ k σ) (j.castPred (Fin.ne_last_of_lt hjk'))
      rw [hl, hr]
      apply congrArg (C.simplex n (by omega))
      have hK := ConcreteCategory.congr_hom (K.δ_comp_δ'
        (i := j.castPred (Fin.ne_last_of_lt hjk')) (j := k)
        (by simpa only [Fin.castSucc_castPred] using hjk')) σ
      simp only [Fin.castSucc_castPred] at hK
      exact hK.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories

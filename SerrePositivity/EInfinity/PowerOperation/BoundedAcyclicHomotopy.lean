module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-!
# 片側有界な非輪状係数へのホモトピー消滅

DAG XIII Construction 2.2.6 の周期解像度による完全入力の比較に用いる補助。
無限周期の解像度を無条件に K 射影的とは扱わず、係数側の有界性を仮定する。
Mathlib の同じ余鎖帰納法で、始域側の零範囲から帰納を開始する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex Opposite
variable {C : Type u} [Category.{v} C] [Abelian C]

open Cochain.InductionUp in
/-- 下に有界な非輪状複体から、各項が単射的な複体への射は零にホモトピック。 -/
lemma homotopyZero_of_acyclic_boundedBelow {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (d : ℤ) [K.IsStrictlyGE d] [∀ n, Injective (L.X n)]
    (hK : K.Acyclic) : Nonempty (Homotopy f 0) := by
  let X (n : ℕ) : Set (Cochain K L (-1)) :=
    Set.ofPred (fun α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n + d - 1))
  let x₀ : X 0 := ⟨0, fun p q hpq hp =>
    IsZero.eq_of_src (K.isZero_of_isStrictlyGE d _ (by omega)) _ _⟩
  let φ (n : ℕ) (α : X n) : X (n + 1) :=
    ⟨_, (CochainComplex.isKInjective_of_injective_aux f α.1
      (n + d - 1) ((n + 1 : ℕ) + d - 1) (by omega) (hK _) α.2).choose_spec⟩
  have hφ (n : ℕ) (x : X n) : (φ n x).1.EqUpTo x.1 (d + n) := fun a b hab ha => by
    dsimp [φ]
    rw [add_eq_left, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero]
  ext n
  let n₀ := (n - d + 1).toNat
  rw [← (sequence φ x₀ n₀).2 n n (add_zero n) (by omega),
    δ_v (-1) 0 (neg_add_cancel 1) _ n n (by omega) (n - 1) (n + 1) rfl (by omega),
    δ_v (-1) 0 (neg_add_cancel 1) _ n n (by omega) (n - 1) (n + 1) rfl (by omega),
    limitSequence_eqUpTo φ hφ x₀ n₀ n (n - 1) (by omega) (by omega),
    limitSequence_eqUpTo φ hφ x₀ n₀ (n + 1) n (by omega) (by omega)]

/-- 各項が射影的な複体から、上に有界な非輪状複体への射は零にホモトピック。 -/
lemma homotopyZero_to_acyclic_boundedAbove {P M : CochainComplex C ℤ}
    (f : P ⟶ M) (d : ℤ) [M.IsStrictlyLE d] [∀ n, Projective (P.X n)]
    (hM : M.Acyclic) : Nonempty (Homotopy f 0) := by
  let K := (opEquivalence C).functor.obj (op M)
  let L := (opEquivalence C).functor.obj (op P)
  have (n : ℤ) : Injective (L.X n) := by
    change Injective (op (P.X (-n)))
    infer_instance
  have : K.IsStrictlyGE (-d) := by
    rw [isStrictlyGE_iff]
    intro i hi
    change IsZero (op (M.X (-i)))
    exact (M.isZero_of_isStrictlyLE d (-i) (by omega)).op
  obtain ⟨h⟩ := homotopyZero_of_acyclic_boundedBelow
    ((opEquivalence C).functor.map f.op) (-d) (acyclic_op hM)
  exact ⟨homotopyUnop (h.trans (.ofEq (by simp)))⟩

end SerrePositivity.EInfinity.PowerOperation

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
概要：同じ基底上の有限個の固有なスキームの周辺を、実際の有限回の pullback で組み立てる。
方針：Fin n の族に関する帰納法で、射影の固有性と実際の lift を同時に供給する。
規約：有限積は固有な周辺として用い、Segre 埋め込みは要求しない。
使われ方：C06 の共通の開からのグラフの閉包を取る周辺。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 有限個の固有な基底上のスキームを、固有な射影と実際の lift を持つ周辺へまとめる。 -/
theorem exists_finite_proper_product (S : Scheme.{u}) (n : ℕ)
    (P : Fin n → Scheme.{u}) (p : ∀ i, P i ⟶ S) (hp : ∀ i, IsProper (p i)) :
    ∃ (Q : Scheme.{u}) (q : Q ⟶ S) (pr : ∀ i, Q ⟶ P i),
      IsProper q ∧ (∀ i, IsProper (pr i)) ∧ (∀ i, pr i ≫ p i = q) ∧
        ∀ (T : Scheme.{u}) (t : T ⟶ S) (l : ∀ i, T ⟶ P i)
          (_ : ∀ i, l i ≫ p i = t),
          ∃ a : T ⟶ Q, a ≫ q = t ∧ ∀ i, a ≫ pr i = l i := by
  induction n with
  | zero =>
      refine ⟨S, 𝟙 S, (fun i ↦ Fin.elim0 i), inferInstance,
        (fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i), ?_⟩
      intro T t l hl
      exact ⟨t, by simp, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨Q, q, pr, hq, hpr, hbase, hlift⟩ := ih (fun i ↦ P i.succ)
        (fun i ↦ p i.succ) (fun i ↦ hp i.succ)
      letI : IsProper q := hq
      letI : IsProper (p 0) := hp 0
      let Q' := pullback q (p 0)
      let q' := pullback.fst q (p 0) ≫ q
      let pr' : ∀ i : Fin (n + 1), Q' ⟶ P i :=
        Fin.cases (pullback.snd q (p 0)) (fun i ↦ pullback.fst q (p 0) ≫ pr i)
      have hpr' (i : Fin (n + 1)) : IsProper (pr' i) := by
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · dsimp [pr']
          infer_instance
        · letI : IsProper (pr j) := hpr j
          dsimp [pr']
          infer_instance
      have hbase' (i : Fin (n + 1)) : pr' i ≫ p i = q' := by
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact (pullback.condition).symm
        · dsimp [pr', q']
          rw [Category.assoc, hbase j]
      refine ⟨Q', q', pr', inferInstance, hpr', hbase', ?_⟩
      intro T t l hl
      obtain ⟨a, ha, hproj⟩ := hlift T t (fun i ↦ l i.succ) (fun i ↦ hl i.succ)
      let a' : T ⟶ Q' := pullback.lift a (l 0) (ha.trans (hl 0).symm)
      refine ⟨a', ?_, ?_⟩
      · simp only [a', q', ← Category.assoc, pullback.lift_fst, ha]
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp [a', pr']
        · simp only [pr', Fin.cases_succ, ← Category.assoc, a', pullback.lift_fst, hproj j]

end SerrePositivity.AlgebraicGeometry

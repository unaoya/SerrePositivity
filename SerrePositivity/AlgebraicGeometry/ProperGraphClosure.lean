module

public import SerrePositivity.AlgebraicGeometry.FiniteProperProduct
public import SerrePositivity.AlgebraicGeometry.ImmersionProperClosure

/-!
概要：同じ基底上の有限個の immersion を、実際の固有なグラフ閉包へまとめる。
方針：有限個の固有な周辺へ lift し、その射の実際の像を取る。
規約：ここでの Noether 性は共通の始域に要求し、射影と元の各射の可換式を保持する。
使われ方：C06 の共通の開のグラフの閉包。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 空でない有限個の固有な周辺への immersion は、実際の固有なグラフ閉包を持つ。 -/
theorem exists_proper_graph_closure {U S : Scheme.{u}} [IsNoetherian U]
    (n : ℕ) (hn : 0 < n) (P : Fin n → Scheme.{u}) (p : ∀ i, P i ⟶ S)
    (hp : ∀ i, IsProper (p i)) (u : U ⟶ S) (l : ∀ i, U ⟶ P i)
    (hi : ∀ i, IsImmersion (l i)) (hcomm : ∀ i, l i ≫ p i = u) :
    ∃ (Z : Scheme.{u}) (j : U ⟶ Z) (q : Z ⟶ S) (π : ∀ i, Z ⟶ P i),
      IsOpenImmersion j ∧ IsSchemeTheoreticallyDominant j ∧ IsProper q ∧
        (∀ i, IsProper (π i)) ∧ j ≫ q = u ∧
        (∀ i, π i ≫ p i = q) ∧ ∀ i, j ≫ π i = l i := by
  obtain ⟨Q, q, pr, hq, hpr, hbase, hlift⟩ := exists_finite_proper_product S n P p hp
  obtain ⟨a, ha, hproj⟩ := hlift U u l hcomm
  haveI : IsProper q := hq
  haveI : IsImmersion a := by
    let i : Fin n := ⟨0, hn⟩
    haveI : IsImmersion (a ≫ pr i) := by rw [hproj i]; exact hi i
    exact IsImmersion.of_comp a (pr i)
  obtain ⟨Z, j, c, hj, hd, hc, hqc, hjc⟩ := exists_immersion_proper_closure a q
  letI : IsClosedImmersion c := hc
  let π (i : Fin n) := c ≫ pr i
  have hπ (i : Fin n) : IsProper (π i) := by
    letI : IsProper (pr i) := hpr i
    dsimp [π]
    infer_instance
  refine ⟨Z, j, c ≫ q, π, hj, hd, hqc, hπ, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hjc, ha]
  · intro i
    dsimp [π]
    rw [Category.assoc, hbase i]
  · intro i
    dsimp [π]
    rw [← Category.assoc, hjc, hproj i]

end SerrePositivity.AlgebraicGeometry

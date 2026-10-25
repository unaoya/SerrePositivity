module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.LastPostcomposition
/-!
概要：斉次後合成で得た単体データが HA を満たせば、後合成射の微分が元の成分を消す。
方針：全次数 Leibniz 則から元の HA 右辺を相殺する。
規約：後合成射を最初から閉と仮定しない。
使われ方：任意余錐から回収した Hom の候補の閉性を全 native 列で判定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]

lemma dgCoherentBarPostLastData_residual {n : ℕ} (s : DGNerve.Simplex R C (n + 1))
    (Y : C) (ρ : GradedHom R (s.obj (Fin.last (n + 1))) Y 0)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (heq : differential R ((dgCoherentBarPostLastData s.toSimplexData Y ρ).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk) =
      (dgCoherentBarPostLastData s.toSimplexData Y ρ).rhs
        J a (Fin.last (n + 1)) k hJ ha hb hk) :
    compose R (differential R ρ) (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) rfl = 0 := by
  have hx := SimplexData.lastReplacementObj_of_ne s.toSimplexData Y a
    (ha ▸ PinchedHom.min_ne_last J hJ)
  have hy := SimplexData.lastReplacementObj_last s.toSimplexData Y
  have hh := dgCoherentBarPostLastData_hom_last s.toSimplexData Y ρ J a k hJ ha hb hk
  have hd := gradedHom_differential_heq hx hy rfl _ _ hh
  have he : differential R
      (compose R ρ (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk) (add_zero k)) =
      compose R ρ (s.toSimplexData.rhs J a (Fin.last (n + 1)) k hJ ha hb hk)
        (add_zero (k + 1)) :=
    eq_of_heq (hd.symm.trans ((heq_of_eq heq).trans
      (dgCoherentBarPostLastData_rhs s.toSimplexData Y ρ J a k hJ ha hb hk)))
  rw [differential_compose, s.equation, Int.negOnePow_zero, one_smul] at he
  exact add_right_cancel (he.trans (zero_add _).symm)

end SerrePositivity.InfinityCategories

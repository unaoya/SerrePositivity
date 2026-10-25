module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionSourceGraphKoszul

/-! # 任意根族の評価核の有限座標支持による検出 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "β" => deltaDivisionSourceEval D a

/-- 有限個の実座標グラフ関係で生成される源イデアル。 -/
abbrev deltaDivisionEvaluationFiniteSupportIdeal (S : Finset (σ × ℕ)) : Ideal L :=
  Ideal.span (deltaDivisionSourceGraphRelation D a '' (S : Set (σ × ℕ)))

/-- 座標集合の包含は、同じ源環内の関係イデアルの包含を与える。 -/
theorem deltaDivisionEvaluationFiniteSupportIdeal_mono :
    Monotone (deltaDivisionEvaluationFiniteSupportIdeal D a) := by
  intro S T h
  exact Ideal.span_mono (Set.image_mono h)

/-- 任意添字の有限座標イデアルは、有限和集合により有向である。 -/
theorem deltaDivisionEvaluationFiniteSupportIdeal_directed :
    Directed (· ≤ ·) (deltaDivisionEvaluationFiniteSupportIdeal D a) := by
  classical
  intro S T
  exact ⟨S ∪ T, deltaDivisionEvaluationFiniteSupportIdeal_mono D a Finset.subset_union_left,
    deltaDivisionEvaluationFiniteSupportIdeal_mono D a Finset.subset_union_right⟩

/-- 任意根族の実評価核は、有限座標グラフイデアルの上限。 -/
theorem deltaDivisionEvaluation_ker_eq_iSup_finiteSupport :
    RingHom.ker β = ⨆ S : Finset (σ × ℕ), deltaDivisionEvaluationFiniteSupportIdeal D a S := by
  classical
  rw [deltaDivisionSourceEval_ker]
  change Ideal.span (Set.range (deltaDivisionSourceGraphRelation D a)) = _
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨z, rfl⟩
    exact (le_iSup (fun S : Finset (σ × ℕ) =>
      deltaDivisionEvaluationFiniteSupportIdeal D a S) {z})
      (Ideal.subset_span ⟨z, by simp, rfl⟩)
  · apply iSup_le
    intro S
    apply Ideal.span_mono
    rintro x ⟨z, _, rfl⟩
    exact ⟨z, rfl⟩

/-- 元の評価射の等式は、一つの有限座標商での標準像の等式として検出できる。 -/
theorem deltaDivisionEvaluation_eq_iff_finiteSupport (x y : L) :
    β x = β y ↔ ∃ S : Finset (σ × ℕ),
      Ideal.Quotient.mk (deltaDivisionEvaluationFiniteSupportIdeal D a S) x =
        Ideal.Quotient.mk (deltaDivisionEvaluationFiniteSupportIdeal D a S) y := by
  have hmem : β x = β y ↔ x - y ∈ RingHom.ker β := by
    change β x = β y ↔ β (x - y) = 0
    rw [map_sub, sub_eq_zero]
  rw [hmem, deltaDivisionEvaluation_ker_eq_iSup_finiteSupport]
  rw [Submodule.mem_iSup_of_directed _ (deltaDivisionEvaluationFiniteSupportIdeal_directed D a)]
  exact exists_congr fun S => (Ideal.Quotient.mk_eq_mk_iff_sub_mem x y).symm

end SerrePositivity.BhattScholze

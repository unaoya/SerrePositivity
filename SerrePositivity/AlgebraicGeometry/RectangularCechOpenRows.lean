module

public import SerrePositivity.AlgebraicGeometry.SchemeCechTupleAffine
public import SerrePositivity.AlgebraicGeometry.FiniteAffineOpenFamilyCechExact

/-!
概要：矩形タプルの同じ開の等号と、同じ有限交叉族の平坦な行を供給する。
方針：有限交叉と逆像を交換し、同じ有限アフィン族の完全性に代入する。
規約：元の被覆・基底・余積射を保持し、非アフィンな始域の Γ の平坦性を要求しない。
使われ方：相対二重 Čech の実際の係数の行。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite TopologicalSpace
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι κ : Type} (U : ι → Y.Opens)

/-- 同じ矩形タプルを転置しても、元の nerve の実際の開は同じ。 -/
theorem schemeCechTupleOpen_iInf [Finite κ] (n : SimplexCategory)
    (t : Fin (n.len + 1) → κ → ι) :
    schemeCechTupleOpen f (fun a : κ → ι ↦ ⨅ r, U (a r)) (op n) t =
      ⨅ r : κ, schemeCechTupleOpen f U (op n) (fun j ↦ t j r) := by
  simp only [schemeCechTupleOpen, schemePreimage_finite_iInf]
  exact iInf_comm

/-- 非空交叉の全タプルの族は、元の開被覆と同じ全体を覆う。 -/
theorem openIntersectionFamily_iSup [Finite κ] [Nonempty κ]
    (hU : (⨆ i, U i) = ⊤) :
    (⨆ a : κ → ι, ⨅ r, U (a r)) = ⊤ := by
  apply le_antisymm le_top
  intro y hy
  have hyU : y ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hyU
  apply Opens.mem_iSup.mpr
  refine ⟨fun _ ↦ i, ?_⟩
  exact (show U i ≤ ⨅ _ : κ, U i from le_iInf (fun _ ↦ le_rfl)) hi

/-- 同じ非空有限交叉のアフィン性は、元の被覆とアフィン対角から得る。 -/
theorem openIntersectionFamily_isAffine [Finite κ] [Nonempty κ]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (hU : ∀ i, IsAffineOpen (U i)) (a : κ → ι) :
    IsAffineOpen (⨅ r, U (a r)) :=
  IsAffineOpen.iInf (fun r ↦ hU (a r))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ有限交叉族と平坦全射の合成の、実際の Frobenius 係数の行の完全性。 -/
theorem finiteAffineOpenIntersectionFamilyFrobeniusCech_exact [Finite ι] [Finite κ] [Nonempty κ]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    [IsAffine S] [Flat f] [Surjective f]
    (hU : ∀ i, IsAffineOpen (U i)) (hc : (⨆ i, U i) = ⊤)
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients
        (Arrow.mk (Scheme.Γ.map (Sigma.desc
          (fun a : κ → ι ↦ (⨅ r, U (a r)).ι ≫ f)).op)) p hp hS) := by
  haveI (a : κ → ι) : IsAffine (⨅ r, U (a r)).toScheme :=
    openIntersectionFamily_isAffine U hU a
  apply finiteAffineOpenFamilyFrobeniusCech_exact f (fun a : κ → ι ↦ (⨅ r, U (a r)).ι)
    ?_ p hp hS
  apply Set.eq_univ_of_forall
  intro y
  have hy : y ∈ ⨆ a : κ → ι, ⨅ r, U (a r) := by
    rw [openIntersectionFamily_iSup U hc]; trivial
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hy
  refine Set.mem_iUnion.mpr ⟨a, ?_⟩
  rw [Scheme.Opens.range_ι]
  exact ha

end SerrePositivity.AlgebraicGeometry

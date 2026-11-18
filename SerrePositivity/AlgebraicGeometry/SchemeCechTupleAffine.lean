module

public import SerrePositivity.AlgebraicGeometry.SchemeCechTupleCover
public import SerrePositivity.AlgebraicGeometry.SchemePullbackAffineTupleOpen
public import SerrePositivity.AlgebraicGeometry.FiniteFiberPowerUnit

/-!
概要：同じ被覆のタプル開は、アフィン基底上でアフィン開である。
方針：有限交叉の逆像と、既存の有限ファイバー冪の Cartesian な帰納を使う。
規約：全ての次数で元のタプル開を保持する。
使われ方：一つの有限アフィン被覆による二重 Čech の整合性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u

/-- 有限個の開の交叉は、同じスキームの射の逆像と可換。 -/
theorem schemePreimage_finite_iInf {X Y : Scheme.{u}} (g : X ⟶ Y)
    {ι : Type} [Finite ι] (V : ι → Y.Opens) :
    g ⁻¹ᵁ (⨅ i, V i) = ⨅ i, g ⁻¹ᵁ V i := by
  apply Opens.ext
  simp only [Scheme.Hom.coe_preimage, Opens.coe_iInf, Set.preimage_iInter]

variable {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type} (U : ι → X.Opens)

/-- 同じタプル開を、末尾の冪と先頭の一個の Cartesian square に沿って表す。 -/
theorem schemeCechTupleOpen_succ (n : ℕ) (t : Fin (n + 1 + 1) → ι) :
    let a := (fun _ : Fin (n + 1 + 1) ↦ f)
    let b := (fun _ : Fin (n + 1) ↦ f)
    let v := WidePullback.lift (WidePullback.base a)
      (fun j : Fin (n + 1) ↦ WidePullback.π a j.succ)
      (fun j ↦ WidePullback.π_arrow a j.succ)
    schemeCechTupleOpen f U (op (SimplexCategory.mk (n + 1))) t =
      v ⁻¹ᵁ schemeCechTupleOpen f U (op (SimplexCategory.mk n)) (fun j ↦ t j.succ) ⊓
        WidePullback.π a 0 ⁻¹ᵁ U (t 0) := by
  dsimp only
  have hi : ∀ (L : Fin (n + 1 + 1) →
      ((Arrow.mk f).cechNerve.obj (op (SimplexCategory.mk (n + 1)))).Opens),
      (⨅ j, L j) = L 0 ⊓ ⨅ j : Fin (n + 1), L j.succ := by
    intro L
    apply le_antisymm
    · exact le_inf (iInf_le L 0) (le_iInf (fun j ↦ iInf_le L j.succ))
    · apply le_iInf
      intro j
      exact Fin.cases inf_le_left (fun k ↦ inf_le_right.trans (iInf_le _ k)) j
  rw [schemeCechTupleOpen, hi]
  rw [schemeCechTupleOpen, schemePreimage_finite_iInf]
  have he : ∀ j : Fin (n + 1),
      (WidePullback.lift (WidePullback.base (fun _ : Fin (n + 1 + 1) ↦ f))
        (fun j : Fin (n + 1) ↦ WidePullback.π (fun _ : Fin (n + 1 + 1) ↦ f) j.succ)
        (fun j ↦ WidePullback.π_arrow (fun _ : Fin (n + 1 + 1) ↦ f) j.succ)) ⁻¹ᵁ
        ((WidePullback.π (fun _ : Fin (n + 1) ↦ f) j) ⁻¹ᵁ U (t j.succ)) =
      WidePullback.π (fun _ : Fin (n + 1 + 1) ↦ f) j.succ ⁻¹ᵁ U (t j.succ) := by
    intro j
    rw [← Scheme.Hom.comp_preimage, WidePullback.lift_π]
  simp_rw [he]
  exact inf_comm _ _

/-- 同じタプル被覆は、アフィン基底上で全てアフィン開からなる。 -/
theorem schemeCechTupleOpen_isAffine [IsAffine S] (hU : ∀ i, IsAffineOpen (U i))
    (n : ℕ) (t : Fin (n + 1) → ι) :
    IsAffineOpen (schemeCechTupleOpen f U (op (SimplexCategory.mk n)) t) := by
  induction n with
  | zero =>
    have ha := (hU (t 0)).preimage (finiteFiberPowerZeroIso f).hom
    simpa [schemeCechTupleOpen, finiteFiberPowerZeroIso] using ha
  | succ n ih =>
    rw [schemeCechTupleOpen_succ]
    exact isPullbackAffineOpen_inf (isPullback_finiteFiberPowerSucc f n)
      (ih (fun j ↦ t j.succ)) (hU (t 0))

end SerrePositivity.AlgebraicGeometry

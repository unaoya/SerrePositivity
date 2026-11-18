module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleRightCenterTotalIso
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleLeftTotalShortComplex

/-!
概要：同じ中心の増大totalの完全性を、元のF8の右側の同じ核の完全性へ渡す。
方針：中心自身の左側、unsigned successor、元のkernelSequenceの順に移す。
規約：元の中心の完全性は入力であり、一般の固有降下の完成とは主張しない。
使われ方：閉像のNoether帰納の中心側の仮定を、元のF8へ代入する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u
local notation "up" => ComplexShape.up ℕ
local notation "ee" => ComplexShape.embeddingUp'Add (1 : ℕ) 1
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 元の右側の同じ基底射影のkernelSequenceは短完全。 -/
private theorem cechRightOriginalKernel_shortExact :
    (ShortComplex.kernelSequence
      (schemePerfectCechTupleSquarePositiveBaseRightProjection f g F q hq U p hp hR hS)).ShortExact := by
  let P := schemePerfectCechTupleSquarePositiveBaseRightProjection f g F q hq U p hp hR hS
  letI : Abelian (HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) :=
    inferInstanceAs (Abelian (CochainComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) ℕ))
  letI : Epi P := HomologicalComplex.epi_of_epi_f P (fun a ↦
    HomologicalComplex.epi_of_epi_f _ (fun b ↦ (ModuleCat.epi_iff_surjective _).mpr
      (schemePerfectCechTupleSquarePositiveBaseRightProjection_surjective f g F q hq U p hp hR hS a b)))
  exact { exact := ShortComplex.kernelSequence_exact P
          mono_f := inferInstanceAs (Mono (kernel.ι P))
          epi_g := inferInstanceAs (Epi P) }

set_option backward.isDefEq.respectTransparency false in
/-- 中心の同じ増大totalが完全なら、元の右側の同じkernelのtotalは完全。 -/
theorem schemePerfectCechTupleRightKernelTotal_acyclic_of_center
    (hCenter : (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble f (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS) up).Acyclic) :
    ((schemePerfectCechTupleSquareRightKernel f g F q hq U p hp hR hS).total up).Acyclic := by
  let K := (schemePerfectCechTupleCenterLeftDouble f (g := g) F U p hp hS).total up
  have hK : K.Acyclic := (schemePerfectCechTupleLeftWholeTotal_acyclic_iff f f (𝟙 _) (RingHom.id S)
    (schemePerfectCechTupleCenterIdentity_right f) (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS hS).mpr hCenter
  have hE : (K.extend ee).Acyclic := by
    intro n
    cases n with
    | zero => exact K.extend_exactAt ee 0 (by intro i; change i + 1 ≠ 0; omega)
    | succ n => exact (K.extend_exactAt_iff ee (j := n) (j' := n + 1) rfl).mpr (hK n)
  have hW : ((schemePerfectCechTupleRightPositiveDouble f g F q hq U p hp hR hS).total up).Acyclic :=
    fun n ↦ (hE n).of_iso (schemePerfectCechTupleRightCenterTotalIso f g F q hq U p hp hR hS)
  have hQ := cechConstantPositiveDouble_total_acyclic
    (schemePerfectCechTupleSquareBaseRightComplex f g F q hq U p hp hR hS)
  have hs := cechIntegerLiftTotal_shortExact
    (ShortComplex.kernelSequence
      (schemePerfectCechTupleSquarePositiveBaseRightProjection f g F q hq U p hp hR hS))
    (cechRightOriginalKernel_shortExact f g F q hq U p hp hR hS)
  apply hs.acyclic_X₁
  constructor
  intro n
  exact (_root_.quasiIsoAt_iff_exactAt _ n (hW n)).mpr (hQ n)

end SerrePositivity.AlgebraicGeometry

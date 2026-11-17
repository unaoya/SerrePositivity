module

public import SerrePositivity.AlgebraicGeometry.AffinePerfectCechAugmentedExact
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechAugmentation

/-!
概要：実際の大域切断からの増大写像で、アフィンの Frobenius 係数の Čech 完全性を述べる。
方針：同じ空タプルの項と大域切断の同型で、検証した増大完全性を移す。
規約：元の増大写像と同じ後続微分を使う Čech 版。
使われ方：実際の単一複体とタプル被覆の係数の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
variable (Y : Scheme.{u}) (p : ℕ) (hp : p.Prime)
variable (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
variable {ι : Type} [LinearOrder ι]

set_option backward.isDefEq.respectTransparency false in
/-- 大域切断の恒等スカラーの実際の増大写像は、同じ前層の対角の制限。 -/
theorem schemeStructurePerfectCechAugmentation_id (U : ι → Y.Opens) :
    schemeStructurePerfectCechAugmentation Y (RingHom.id Γ(Y, ⊤)) p hp (hY (op ⊤)) hY U =
      openCoverCechAugmentation (frobeniusRingDiagram Y.presheaf p hp hY) U := by
  unfold schemeStructurePerfectCechAugmentation
  rw [frobeniusDirectLimitMap_id]
  apply LinearMap.ext
  intro x
  rfl

variable [IsAffine Y] [Fintype ι]

/-- 同じ有限アフィン被覆の、実際の大域切断の Frobenius 係数からの増大写像は単射。
Stacks 30.2.6 に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem affineSchemeStructurePerfectCechAugmentation_injective
    (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) :
    Function.Injective
      (schemeStructurePerfectCechAugmentation Y (RingHom.id Γ(Y, ⊤)) p hp (hY (op ⊤)) hY U) := by
  rw [schemeStructurePerfectCechAugmentation_id, ← openCoverCechAugmentation_eq]
  exact (affineSchemeStructurePerfectCech_augmentedExact Y p hp hY U hU hcU).1.comp
    (openCoverCechZeroEquiv (frobeniusRingDiagram Y.presheaf p hp hY) U).symm.injective

set_option backward.isDefEq.respectTransparency false in
/-- 同じ有限アフィン被覆の、実際の増大写像は後続の微分と完全。
Stacks 30.2.6 に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem affineSchemeStructurePerfectCechAugmentation_exact
    (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) :
    Function.Exact
      (schemeStructurePerfectCechAugmentation Y (RingHom.id Γ(Y, ⊤)) p hp (hY (op ⊤)) hY U)
      ((fullCechComplex (openCoverCechDiagram
        (frobeniusRingDiagram Y.presheaf p hp hY) U)).d 0 1).hom := by
  change Function.Exact
    (schemeStructurePerfectCechAugmentation Y (RingHom.id Γ(Y, ⊤)) p hp (hY (op ⊤)) hY U)
    (fullCechDifferential (openCoverCechDiagram (frobeniusRingDiagram Y.presheaf p hp hY) U) 1)
  rw [schemeStructurePerfectCechAugmentation_id, ← openCoverCechAugmentation_eq]
  have he := (openCoverCechZeroEquiv (frobeniusRingDiagram Y.presheaf p hp hY) U).symm.surjective
  exact he.comp_exact_iff_exact.mpr
    ((affineSchemeStructurePerfectCech_augmentedExact Y p hp hY U hU hcU).2 0)

end SerrePositivity.AlgebraicGeometry

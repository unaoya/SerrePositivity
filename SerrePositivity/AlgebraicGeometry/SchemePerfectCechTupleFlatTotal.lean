module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleConstantTotal
public import SerrePositivity.AlgebraicGeometry.CechAugmentedDoubleRows
public import SerrePositivity.AlgebraicGeometry.RectangularPerfectAugmentedRowIso
public import SerrePositivity.AlgebraicGeometry.RectangularCechOpenRows

/-!
概要：元の平坦全射の有限アフィン被覆の、同じ二重Čechの完全性。
方針：各非空有限交叉族の既存の完全性を同じ増大行へ移し、既存の行の判定とretractを使う。
規約：元の係数・被覆・増大・全複体を保持するČech版。
使われ方：相対proper fppfの選択した有限アフィン被覆での完全性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
local notation "up" => ComplexShape.up ℕ
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
variable (f : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ増大行の完全性から、元のタプル二重Čechのtotalの完全性を得る。 -/
theorem schemePerfectCechTupleDouble_acyclic_of_augmented_rows
    (h : ∀ k, (SerrePositivity.Cech.augmentedCochain.obj
      (rectangularPerfectAugmentedRow f U p hp hR k)).Acyclic) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble f U p hp hR) up).Acyclic := by
  apply schemePerfectCechTupleDouble_acyclic_of_constant
  exact cechIntegerAugmentedDouble_acyclic_of_rows _ h

set_option backward.isDefEq.respectTransparency false in
/-- 平坦全射の同じ有限アフィン被覆の二重Čechの完全性のČech版。 -/
theorem schemePerfectCechTupleDouble_acyclic_of_flat_surjective
    [IsAffineHom (pullback.diagonal (terminal.from Y))] [Flat f] [Surjective f]
    (hU : ∀ i, IsAffineOpen (U i)) (hc : (⨆ i, U i) = ⊤) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble f U p hp hR) up).Acyclic := by
  apply schemePerfectCechTupleDouble_acyclic_of_augmented_rows
  intro k
  let g := Sigma.desc (fun b : Fin (k + 1) → ι ↦ (⨅ r, U (b r)).ι ≫ f)
  haveI (b : Fin (k + 1) → ι) : IsAffine (⨅ r, U (b r)).toScheme :=
    openIntersectionFamily_isAffine U hU b
  let hS : (p : Γ(Spec (CommRingCat.of R), ⊤)) = 0 :=
    schemeScalarPresheaf_primeCast (Spec (CommRingCat.of R)) (𝟙 _) p hR (op ⊤)
  let hN : ∀ n : SimplexCategory,
      (p : (rectangularPerfectRowGammaFunctor f U k).obj n) = 0 := fun n ↦ by
    have hz := congrArg
      (Scheme.Γ.map ((Arrow.mk g).augmentedCechNerve.hom.app (op n)).op).hom hS
    simpa only [map_natCast, map_zero] using hz
  have hx := finiteAffineOpenIntersectionFamilyFrobeniusCech_exact
    (κ := Fin (k + 1)) f U hU hc p hp hS
  have hy := (ringCechExact_iff_integer_acyclic _).mp hx
  let e := affineGammaPerfectAugmentedCoefficientsIso g p hp hS hN ≪≫
    rectangularPerfectAugmentedRowIso f U p hp hR k hS hN
  intro n
  exact (hy n).of_iso (SerrePositivity.Cech.augmentedCochain.mapIso e)

end SerrePositivity.AlgebraicGeometry

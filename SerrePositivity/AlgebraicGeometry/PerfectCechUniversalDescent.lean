module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleFlatTotal
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
概要：Noether アフィン試験基底上の、実際の完全構造層の普遍 Čech 降下を定義する。
方針：同じ底変換と有限アフィン被覆のタプル二重複体の完全性を量化する。
規約：この中間述語の試験基底だけを Noether にし、最終出力の型を変えない。
使われ方：相対 fppf 比較と Noether 閉像の帰納（計画 D01）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- 各 Noether アフィン試験基底と有限アフィン被覆で、元のタプル二重複体が完全。 -/
def PerfectCechUniversalDescent (p : ℕ) (hp : p.Prime)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : (p : R) = 0) (t : Spec (CommRingCat.of R) ⟶ Y)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (U : ι → (pullback f t).Opens),
    (∀ i, IsAffineOpen (U i)) → (⨆ i, U i) = ⊤ →
      (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        (schemePerfectCechTupleDouble (pullback.snd f t) U p hp hR)
        (ComplexShape.up ℕ)).Acyclic

/-- 平坦全射の元のタプル Čech 完全性を、全ての試験基底へ適用する（計画 D03）。 -/
theorem perfectCechUniversalDescent_flat_surjective
    (p : ℕ) (hp : p.Prime) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [IsSeparated f] [QuasiCompact f]
    [LocallyOfFinitePresentation f] : PerfectCechUniversalDescent p hp f := by
  intro R _ _ hR t ι _ _ U hU hcU
  letI : (pullback f t).IsSeparated := ⟨by
    rw [← terminal.comp_from (pullback.snd f t)]
    infer_instance⟩
  exact schemePerfectCechTupleDouble_acyclic_of_flat_surjective
    (pullback.snd f t) U p hp hR hU hcU

end SerrePositivity.AlgebraicGeometry

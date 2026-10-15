module

public import SerrePositivity.BhattScholze.DeltaPDivisionFiniteKoszulTransitions

/-! # 実有限KoszulのH⁰図式と標準有限商図式

元ごとの標準単位で正規化した比較を、共通の自由環の加群圏における自然同型にする。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 通常有限商の標準遷移射を元の自由環上の線形写像として表す。 -/
def deltaPDivisionFiniteQuotientTransitionLinear (N : ℕ) :
    (L₀ ⧸ I₀ N) →ₗ[L₀] (L₀ ⧸ I₀ (N + 1)) where
  toFun := deltaPDivisionFiniteQuotientTransition D y N
  map_add' := map_add _
  map_smul' r z := by
    change deltaPDivisionFiniteQuotientTransition D y N (Ideal.Quotient.mk (I₀ N) r * z) =
      Ideal.Quotient.mk (I₀ (N + 1)) r * deltaPDivisionFiniteQuotientTransition D y N z
    rw [map_mul, deltaPDivisionFiniteQuotientTransition_mk]

omit [Unique σ] in
/-- 線形遷移写像の元上の式は、元の標準商環射。 -/
theorem deltaPDivisionFiniteQuotientTransitionLinear_apply (N : ℕ) (z : L₀ ⧸ I₀ N) :
    deltaPDivisionFiniteQuotientTransitionLinear D y N z =
      deltaPDivisionFiniteQuotientTransition D y N z := rfl

/-- 通常有限商を共通の自由環の加群として繋いだ具体的な逐次図式。 -/
def deltaPDivisionFiniteQuotientModuleDiagram : ℕ ⥤ ModuleCat L₀ :=
  Functor.ofSequence (fun N => ModuleCat.ofHom (deltaPDivisionFiniteQuotientTransitionLinear D y N))

omit [Unique σ] in
/-- 商加群図式の隣接射は、標準商遷移射の線形化。 -/
theorem deltaPDivisionFiniteQuotientModuleDiagram_map_succ (N : ℕ) :
    (deltaPDivisionFiniteQuotientModuleDiagram (σ := σ) D y).map (homOfLE (Nat.le_succ N)) =
      ModuleCat.ofHom (deltaPDivisionFiniteQuotientTransitionLinear D y N) :=
  Functor.ofSequence_map_homOfLE_succ _ N

/-- 実有限Koszul図式のH⁰と標準有限商図式は、正規化された自然同型で一致する。 -/
def deltaPDivisionFiniteKoszulH0DiagramIso :
    deltaPDivisionFiniteKoszulDiagram (σ := σ) D y ⋙
        HomologicalComplex.homologyFunctor (ModuleCat L₀) (ComplexShape.up ℤ) 0 ≅
      deltaPDivisionFiniteQuotientModuleDiagram D y := by
  let η : deltaPDivisionFiniteKoszulDiagram (σ := σ) D y ⋙
        HomologicalComplex.homologyFunctor (ModuleCat L₀) (ComplexShape.up ℤ) 0 ⟶
      deltaPDivisionFiniteQuotientModuleDiagram D y :=
    NatTrans.ofSequence (fun N => (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso.hom)
      (by
        intro N
        simp only [Functor.comp_map, deltaPDivisionFiniteKoszulDiagram_map_succ,
          deltaPDivisionFiniteQuotientModuleDiagram_map_succ]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        exact deltaPDivisionFiniteKoszulH0Equiv_transition D y N z)
  exact NatIso.ofComponents (fun N => (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso)
    (fun f => η.naturality f)

/-- 自然同型の各成分は、前工程の標準単位で正規化したH⁰同型。 -/
theorem deltaPDivisionFiniteKoszulH0DiagramIso_app (N : ℕ) :
    (deltaPDivisionFiniteKoszulH0DiagramIso (σ := σ) D y).hom.app N =
      (deltaPDivisionFiniteKoszulH0Equiv D y N).toModuleIso.hom := rfl

end SerrePositivity.BhattScholze

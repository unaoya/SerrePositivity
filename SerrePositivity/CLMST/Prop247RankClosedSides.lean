module

public import SerrePositivity.CLMST.Prop247RankCompleteness
public import SerrePositivity.CLMST.Prop247RankAssembly
public import SerrePositivity.CommutativeAlgebra.DerivedCompletePrincipalIdeal

/-! # Prop 2.4.7：元の rank 四角形のイデアルと閉側の導来完備性

S→∏Si と元の I=(g) の像を固定し、離散な環の四頂点と二つのイデアルの
導来 p 完備性を供給する。Cor 8.12 の E∞ 四角形の引き戻し性は主張しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- 原典の実 rank 底変換写像と元の主イデアルについて、離散な閉側の完備入力を供給する。 -/
theorem prop247_rankSource_closedSide_completeness
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : R)
    {ι : Type} [Finite ι] (T : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    (hT : ∀ i, IsIntegralPerfectoid (T i) p) :
    let X := (i : ι) → T i ⊗[R] S
    let I := Ideal.span {algebraMap R S g}
    let J := I.map (prop247_rankTensorUnit R S T).toRingHom
    IsModuleComplete S (p : S) (ModuleCat.of S S) ∧
      IsModuleComplete X (p : X) (ModuleCat.of X X) ∧
      IsModuleComplete S (p : S) (ModuleCat.of S I) ∧
      IsModuleComplete X (p : X) (ModuleCat.of X J) ∧
      IsModuleComplete (S ⧸ I) (p : S ⧸ I) (ModuleCat.of (S ⧸ I) (S ⧸ I)) ∧
      IsModuleComplete (X ⧸ J) (p : X ⧸ J) (ModuleCat.of (X ⧸ J) (X ⧸ J)) := by
  let X := (i : ι) → T i ⊗[R] S
  let I := Ideal.span {algebraMap R S g}
  let J := I.map (prop247_rankTensorUnit R S T).toRingHom
  have hS : IsModuleComplete S (p : S) (ModuleCat.of S S) := by
    have h := (isModuleComplete_algebraMap_iff R S (p : R) S).mpr
      (prop247_source_isModuleComplete R S p hR)
    simpa only [map_natCast] using h
  have hX : IsModuleComplete X (p : X) (ModuleCat.of X X) := by
    have h := (isModuleComplete_algebraMap_iff R X (p : R) X).mpr
      (prop247_rankBaseChangeProduct_isModuleComplete R p T hT S)
    simpa only [map_natCast] using h
  have hJ : J = Ideal.span {algebraMap R X g} := by
    change (Ideal.span {algebraMap R S g}).map (prop247_rankTensorUnit R S T).toRingHom = _
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x : X => Ideal.span {x}) ((prop247_rankTensorUnit R S T).commutes g)
  refine ⟨hS, hX, isModuleComplete_principal_ideal S (p : S) (algebraMap R S g) hS, ?_,
    isModuleComplete_principal_quotient_natCast S p (algebraMap R S g) hS, ?_⟩
  · change IsModuleComplete X (p : X) (ModuleCat.of X J)
    rw [hJ]
    exact isModuleComplete_principal_ideal X (p : X) (algebraMap R X g) hX
  · change IsModuleComplete (X ⧸ J) (p : X ⧸ J) (ModuleCat.of (X ⧸ J) (X ⧸ J))
    rw [hJ]
    exact isModuleComplete_principal_quotient_natCast X p (algebraMap R X g) hX

end SerrePositivity.CLMST

module

public import SerrePositivity.AlgebraicGeometry.FiniteTypePushoutSurjectivityLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
概要：affine な Cartesian な極限図式で、閉埋め込み性を有限段へ降ろす。
方針：実際の極限の Γ の余極限と Cartesian 正方形の pushout を用い、07RH を適用する。
規約：実際の cone と射を保つ。標的の Noether 性は仮定しない。
使われ方：Stacks 01ZP の一般の閉埋め込み性の降下の affine な部分。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits Opposite
universe u

/-- affine な Cartesian 図式の極限射が閉埋め込みなら、ある後段の射も閉埋め込み。 -/
theorem exists_closedImmersion_stage_of_affine_cartesian_limit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D E : J ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)] [∀ j, IsAffine (E.obj j)]
    (τ : E ⟶ D) (cD : Cone D) (cE : Cone E) (hD : IsLimit cD) (hE : IsLimit cE)
    (φ : cE.pt ⟶ cD.pt) [IsClosedImmersion φ]
    (hcomm : ∀ j, cE.π.app j ≫ τ.app j = φ ≫ cD.π.app j)
    (i : J) [LocallyOfFiniteType (τ.app i)]
    (hcartesian : ∀ (j : J) (f : j ⟶ i),
      IsPullback (E.map f) (τ.app j) (τ.app i) (D.map f)) :
    ∃ (j : J) (_ : j ⟶ i), IsClosedImmersion (τ.app j) := by
  haveI : ∀ j, IsAffine (D.op.obj j).unop := by dsimp; infer_instance
  haveI : ∀ j, IsAffine (E.op.obj j).unop := by dsimp; infer_instance
  haveI : IsAffine cD.pt := Scheme.isAffine_of_isLimit cD hD
  let τΓ : D.op ⋙ Scheme.Γ ⟶ E.op ⋙ Scheme.Γ := Functor.whiskerRight (NatTrans.op τ) Scheme.Γ
  have hsurj : Function.Surjective φ.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine φ).2
  have hfinite : (τΓ.app (op i)).hom.FiniteType := by
    exact HasRingHomProperty.appTop (P := @LocallyOfFiniteType) (τ.app i) inferInstance
  have hcommΓ (j : Jᵒᵖ) : (Scheme.Γ.mapCocone cD.op).ι.app j ≫ φ.appTop =
      τΓ.app j ≫ (Scheme.Γ.mapCocone cE.op).ι.app j := by
    simpa [τΓ, Scheme.Hom.comp_appTop] using
      (congrArg (fun f ↦ Scheme.Hom.appTop f) (hcomm j.unop)).symm
  have hcartesianΓ (j : Jᵒᵖ) (f : op i ⟶ j) :
      IsPushout (τΓ.app (op i)) ((D.op ⋙ Scheme.Γ).map f)
        ((E.op ⋙ Scheme.Γ).map f) (τΓ.app j) :=
    isPushout_appTop_of_isPullback (hcartesian j.unop f.unop)
  obtain ⟨j, f, hj⟩ := exists_surjective_stage_of_finiteType_pushouts
    (D.op ⋙ Scheme.Γ) (E.op ⋙ Scheme.Γ) τΓ
    (Scheme.Γ.mapCocone cD.op) (Scheme.Γ.mapCocone cE.op)
    (isColimitOfPreserves Scheme.Γ hD.op) (isColimitOfPreserves Scheme.Γ hE.op)
    φ.appTop hsurj hcommΓ (op i) hfinite hcartesianΓ
  exact ⟨j.unop, f.unop, IsClosedImmersion.of_surjective_of_isAffine (τ.app j.unop) hj⟩

end SerrePositivity.AlgebraicGeometry

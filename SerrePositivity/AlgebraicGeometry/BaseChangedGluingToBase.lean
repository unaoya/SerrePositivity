module

public import SerrePositivity.AlgebraicGeometry.BaseChangedOpenTransitionGlueData
public import SerrePositivity.AlgebraicGeometry.FinitePresentationGluingBase

/-!
概要：後段の実際の gluing datum の構造射を貼り合わせ、有限表示性を供給する。
方針：各チャートの構造射の可換式と局所有限表示性を、既存の gluing の局所性へ渡す。
規約：Noether 性は後段の基底にだけ用い、元の環へ仮定しない。
使われ方：G2 の実際の有限表示模型の構造射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry.OpenTransitionCandidate
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {S B : Scheme.{u}} (C : OpenTransitionCandidate S) (γ : B ⟶ S)

/-- 後段のチャートの構造射は反転と開包含に関して可換。 -/
theorem baseChangedToBase_compat (i j : C.J) :
    C.baseChangedF γ i j ≫ pullback.fst γ (C.p i) =
      C.baseChangedT γ i j ≫ C.baseChangedF γ j i ≫ pullback.fst γ (C.p j) := by
  simp [Category.assoc]

/-- 後段の実際の gluing datum の、同じ基底への構造射。 -/
def baseChangedToBase (h : C.BaseChangedEquations γ) :
    (C.baseChangedOpenTransitionGlueData γ h).glued ⟶ B :=
  glueDataToBase (C.baseChangedOpenTransitionGlueData γ h)
    (fun i ↦ pullback.fst γ (C.p i)) (C.baseChangedToBase_compat γ)

/-- 貼り合わせた構造射は全チャート上で選んだ構造射に一致する。 -/
@[reassoc] theorem baseChangedToBase_ι (h : C.BaseChangedEquations γ) (i : C.J) :
    (C.baseChangedOpenTransitionGlueData γ h).ι i ≫ C.baseChangedToBase γ h =
      pullback.fst γ (C.p i) :=
  glueDataToBase_ι (C.baseChangedOpenTransitionGlueData γ h)
    (fun i ↦ pullback.fst γ (C.p i)) (C.baseChangedToBase_compat γ) i

/-- チャートの構造射の局所有限表示性は底変換して貼り合わせても保たれる。 -/
theorem locallyOfFinitePresentation_baseChangedToBase (h : C.BaseChangedEquations γ)
    (hp : ∀ i, LocallyOfFinitePresentation (C.p i)) :
    LocallyOfFinitePresentation (C.baseChangedToBase γ h) := by
  apply locallyOfFinitePresentation_glueDataToBase
  intro i
  letI : LocallyOfFinitePresentation (C.p i) := hp i
  infer_instance

/-- 有限個の affine チャートと後段の局所 Noether 基底から、全体の qcqs な局所有限表示性。 -/
theorem finitePresentation_baseChangedToBase (h : C.BaseChangedEquations γ)
    [Finite C.J] [IsLocallyNoetherian B] [∀ i, IsAffine (pullback γ (C.p i))]
    (hp : ∀ i, LocallyOfFinitePresentation (C.p i)) :
    LocallyOfFinitePresentation (C.baseChangedToBase γ h) ∧
      QuasiCompact (C.baseChangedToBase γ h) ∧ QuasiSeparated (C.baseChangedToBase γ h) := by
  let D := C.baseChangedOpenTransitionGlueData γ h
  haveI : Finite D.J := inferInstanceAs (Finite C.J)
  haveI (i : D.J) : IsAffine (D.U i) := inferInstanceAs (IsAffine (pullback γ (C.p i)))
  have hN (i : D.J) : IsNoetherianRing Γ(D.U i, ⊤) := by
    letI : LocallyOfFinitePresentation (C.p i) := hp i
    letI : IsLocallyNoetherian (D.U i) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst γ (C.p i))
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (D.U i)⟩
  apply finitePresentation_glueDataToBase_of_noetherian_charts D
    (fun i ↦ pullback.fst γ (C.p i)) (C.baseChangedToBase_compat γ) hN
  intro i
  letI : LocallyOfFinitePresentation (C.p i) := hp i
  infer_instance

end SerrePositivity.AlgebraicGeometry.OpenTransitionCandidate

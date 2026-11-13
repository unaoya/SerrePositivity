module

public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechPullback
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechRefinedPullback

/-!
概要：Frobenius 後の実際の構造層の引き戻しを、逆像被覆の細分へ移す。
方針：引き戻しと細分を合成し、各タプルを実際の appLE の順極限で表示する。
規約：平坦性を要求せず、空の開集合と零環も許す。
使われ方：F8 の閉厚化と Proj の標準開の比較の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (p : ℕ) (hp : p.Prime)
variable (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
variable (hX : ∀ O, (p : X.presheaf.obj O) = 0)
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
variable (U : ι → Y.Opens) (V : κ → X.Opens)
variable (ρ : κ → ι) (hρ : ∀ j, V j ≤ f ⁻¹ᵁ U (ρ j))

/-- 逆像への実際の引き戻しと細分の合成。 -/
def schemeStructurePerfectCechRefinedPullbackMap :
    fullCechComplex (openCoverCechDiagram (frobeniusRingDiagram Y.presheaf p hp hY) U) ⟶
      fullCechComplex (openCoverCechDiagram (frobeniusRingDiagram X.presheaf p hp hX) V) :=
  schemeStructurePerfectCechPullbackMap f p hp hY hX U ≫
    openCoverCechRefinementMap (frobeniusRingDiagram X.presheaf p hp hX)
      (fun i ↦ f ⁻¹ᵁ U i) V ρ hρ

/-- 各タプルの写像は、実際の appLE の環準同型の Frobenius 順極限。 -/
theorem schemeStructurePerfectCechRefinedPullbackMap_apply (q : ℕ)
    (a : (fullCechComplex (openCoverCechDiagram
      (frobeniusRingDiagram Y.presheaf p hp hY) U)).X q) (t : Fin (q + 1) → κ) :
    ((schemeStructurePerfectCechRefinedPullbackMap f p hp hY hX U V ρ hρ).f q).hom a t =
      frobeniusDirectLimitMap p hp
        (hY (op (cechOpenIntersection U (cechTupleSupport (ρ ∘ t)))))
        (hX (op (cechOpenIntersection V (cechTupleSupport t))))
        (f.appLE (cechOpenIntersection U (cechTupleSupport (ρ ∘ t)))
          (cechOpenIntersection V (cechTupleSupport t))
          (schemeCechRefinedPullbackIntersection_le f U V ρ hρ t)).hom (a (ρ ∘ t)) := by
  let W := cechOpenIntersection U (cechTupleSupport (ρ ∘ t))
  let W' := cechOpenIntersection (fun i ↦ f ⁻¹ᵁ U i) (cechTupleSupport (ρ ∘ t))
  let Z := cechOpenIntersection V (cechTupleSupport t)
  have he : f ⁻¹ᵁ W = W' := cechOpenIntersection_scheme_preimage f U _
  have hr : Z ≤ W' := cechOpenIntersection_refinement (fun i ↦ f ⁻¹ᵁ U i) V ρ hρ t
  have hZ : Z ≤ f ⁻¹ᵁ W := schemeCechRefinedPullbackIntersection_le f U V ρ hρ t
  have hc : X.presheaf.map (eqToHom (congrArg op he)) ≫
      X.presheaf.map (homOfLE hr).op = X.presheaf.map (homOfLE hZ).op := by
    rw [← X.presheaf.map_comp]
    congr 1
  have hv := congrArg (fun m ↦ m.hom) hc
  obtain ⟨n, x, hx⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (Y.presheaf.obj (op W)) p hp (hY (op W))) (a (ρ ∘ t))
  change frobeniusDirectLimitMap p hp _ _ (X.presheaf.map (homOfLE hr).op).hom
      (frobeniusDirectLimitMap p hp _ _ (X.presheaf.map (eqToHom (congrArg op he))).hom
        (frobeniusDirectLimitMap p hp _ _ (f.app W).hom (a (ρ ∘ t)))) = _
  rw [hx]
  change frobeniusDirectLimitOf _ p hp _ n
      ((X.presheaf.map (homOfLE hr).op).hom
        ((X.presheaf.map (eqToHom (congrArg op he))).hom ((f.app W).hom x))) =
    frobeniusDirectLimitOf _ p hp _ n ((X.presheaf.map (homOfLE hZ).op).hom ((f.app W).hom x))
  exact congrArg (frobeniusDirectLimitOf _ p hp _ n)
    (congrArg (fun m ↦ m ((f.app W).hom x)) hv)

end SerrePositivity.AlgebraicGeometry

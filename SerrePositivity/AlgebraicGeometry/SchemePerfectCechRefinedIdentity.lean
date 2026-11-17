module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechPullbackComposition

/-!
概要：実際の Frobenius 係数の refinedPullback は恒等射を保つ。
方針：同じタプルで appLE の恒等則と Frobenius 順極限の恒等則を使う。
規約：元の全タプル複体と実際の写像を保持する。
使われ方：Čech nerve の同じ被覆の係数図式の単位則。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 恒等スキーム射と恒等細分は、同じ複体の恒等射を与える。 -/
theorem schemeStructurePerfectCechRefinedPullbackMap_id (X : Scheme.{u})
    (p : ℕ) (hp : p.Prime) (hX : ∀ O, (p : X.presheaf.obj O) = 0)
    {ι : Type} [DecidableEq ι] (U : ι → X.Opens) :
    schemeStructurePerfectCechRefinedPullbackMap (𝟙 X) p hp hX hX
      U U id (fun _ ↦ le_rfl) = 𝟙 (fullCechComplex
        (openCoverCechDiagram (frobeniusRingDiagram X.presheaf p hp hX) U)) := by
  apply fullCechComplex_hom_ext
    (D := openCoverCechDiagram (frobeniusRingDiagram X.presheaf p hp hX) U)
    (E := openCoverCechDiagram (frobeniusRingDiagram X.presheaf p hp hX) U)
  intro q a t
  rw [schemeStructurePerfectCechRefinedPullbackMap_apply]
  let O := cechOpenIntersection U (cechTupleSupport t)
  have hi : O ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ O := by
    rw [Scheme.Hom.id_preimage]
  have he : ((𝟙 X : X ⟶ X).appLE O O hi).hom = RingHom.id Γ(X, O) := by
    have hc : (𝟙 X : X ⟶ X).appLE O O hi = 𝟙 (Γ(X, O)) := by
      change (𝟙 (Γ(X, O))) ≫ X.presheaf.map (𝟙 (op O)) = 𝟙 (Γ(X, O))
      exact (Category.id_comp _).trans (X.presheaf.map_id (op O))
    exact congrArg (fun k : Γ(X, O) ⟶ Γ(X, O) ↦ k.hom) hc
  change frobeniusDirectLimitMap p hp (hX (op O)) (hX (op O))
    ((𝟙 X : X ⟶ X).appLE O O hi).hom (a t) = a t
  rw [he]
  change frobeniusDirectLimitMap p hp (hX (op O)) (hX (op O))
    (RingHom.id Γ(X, O)) (a t) = a t
  rw [frobeniusDirectLimitMap_id]
  rfl

/-- 同じ射と添字の単位の等式を、同じ refinedPullback の単位へ渡す。 -/
theorem schemeStructurePerfectCechRefinedPullbackMap_eq_id_of_eq {X : Scheme.{u}}
    (f : X ⟶ X) (hf : f = 𝟙 X) (p : ℕ) (hp : p.Prime)
    (hX : ∀ O, (p : X.presheaf.obj O) = 0)
    {ι : Type} [DecidableEq ι] (U : ι → X.Opens) (ρ : ι → ι) (hρ : ρ = id)
    (hc : ∀ i, U i ≤ f ⁻¹ᵁ U (ρ i)) :
    schemeStructurePerfectCechRefinedPullbackMap f p hp hX hX U U ρ hc =
      𝟙 (fullCechComplex
        (openCoverCechDiagram (frobeniusRingDiagram X.presheaf p hp hX) U)) := by
  subst f
  subst ρ
  exact schemeStructurePerfectCechRefinedPullbackMap_id X p hp hX U

end SerrePositivity.AlgebraicGeometry

module

public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechPullback

/-!
概要：逆像被覆をさらに細分した、実際の構造層の Čech の引き戻しを作る。
方針：既存の逆像比較に細分写像を合成し、各成分を appLE で表示する。
規約：平坦性は要求せず、有限交叉での実際の切断の写像を用いる。
使われ方：Proj の標準開、閉厚化と模型の遷移の同じ写像による比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (f : X ⟶ Y) (φY : R →+* Γ(Y, ⊤)) (φX : R →+* Γ(X, ⊤))
variable (hφ : φX = f.appTop.hom.comp φY)
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
variable (U : ι → Y.Opens) (V : κ → X.Opens)
variable (ρ : κ → ι) (hρ : ∀ j, V j ≤ f ⁻¹ᵁ U (ρ j))

include hρ in
/-- 逆像被覆の細分の有限交叉は、元の有限交叉の逆像に含まれる。 -/
theorem schemeCechRefinedPullbackIntersection_le {k : ℕ} (t : Fin k → κ) :
    cechOpenIntersection V (cechTupleSupport t) ≤
      f ⁻¹ᵁ cechOpenIntersection U (cechTupleSupport (ρ ∘ t)) := by
  rw [cechOpenIntersection_scheme_preimage]
  exact cechOpenIntersection_refinement (fun i ↦ f ⁻¹ᵁ U i) V ρ hρ t

/-- 逆像被覆への引き戻しと、さらに細分する写像の合成。 -/
def schemeStructureCechRefinedPullbackMap :
    fullCechComplex (openCoverCechDiagram
      (schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars φY) U) ⟶
    fullCechComplex (openCoverCechDiagram
      (schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars φX) V) :=
  schemeStructureCechPullbackMap f φY φX hφ U ≫
    openCoverCechRefinementMap (schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars φX)
      (fun i ↦ f ⁻¹ᵁ U i) V ρ hρ

/-- 各タプルでの Čech の引き戻しは、実際の構造層の appLE そのもの。 -/
theorem schemeStructureCechRefinedPullbackMap_apply (q : ℕ)
    (a : (fullCechComplex (openCoverCechDiagram
      (schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars φY) U)).X q)
    (t : Fin (q + 1) → κ) :
    ((schemeStructureCechRefinedPullbackMap f φY φX hφ U V ρ hρ).f q).hom a t =
      (f.appLE (cechOpenIntersection U (cechTupleSupport (ρ ∘ t)))
        (cechOpenIntersection V (cechTupleSupport t))
        (schemeCechRefinedPullbackIntersection_le f U V ρ hρ t)).hom (a (ρ ∘ t)) := by
  let W := cechOpenIntersection U (cechTupleSupport (ρ ∘ t))
  let W' := cechOpenIntersection (fun i ↦ f ⁻¹ᵁ U i) (cechTupleSupport (ρ ∘ t))
  let Z := cechOpenIntersection V (cechTupleSupport t)
  have he : f ⁻¹ᵁ W = W' := cechOpenIntersection_scheme_preimage f U _
  have hr : Z ≤ W' := cechOpenIntersection_refinement (fun i ↦ f ⁻¹ᵁ U i) V ρ hρ t
  have hZ : Z ≤ f ⁻¹ᵁ W := schemeCechRefinedPullbackIntersection_le f U V ρ hρ t
  change ((X.presheaf.map (eqToHom (congrArg op he)) ≫
      X.presheaf.map (homOfLE hr).op).hom ((f.app W).hom (a (ρ ∘ t)))) =
    (X.presheaf.map (homOfLE hZ).op).hom ((f.app W).hom (a (ρ ∘ t)))
  rw [← X.presheaf.map_comp]
  congr 2

end SerrePositivity.AlgebraicGeometry

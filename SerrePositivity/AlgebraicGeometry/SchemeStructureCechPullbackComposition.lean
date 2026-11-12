module

public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechRefinedPullback

/-!
概要：実際の構造層の Čech の引き戻しは、細分を含めてスキームの射の合成を保つ。
方針：各タプルで appLE の合成に戻す。
規約：同じ添字の被覆の細分を扱い、スカラー作用の整合性を明示する。
使われ方：閉厚化の I 進遷移と比較同型の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {A B C : Scheme.{u}}
variable {ι : Type} [DecidableEq ι]

/-- 同じ逆像被覆への恒等細分を合成しても、実際の引き戻しは変わらない。 -/
theorem schemeStructureCechPullbackMap_eq_refined (f : B ⟶ A)
    (φA : R →+* Γ(A, ⊤)) (φB : R →+* Γ(B, ⊤))
    (hφ : φB = f.appTop.hom.comp φA) (U : ι → A.Opens) :
    schemeStructureCechPullbackMap f φA φB hφ U =
      schemeStructureCechRefinedPullbackMap f φA φB hφ U (fun i ↦ f ⁻¹ᵁ U i)
        id (fun _ ↦ le_rfl) := by
  simp only [schemeStructureCechRefinedPullbackMap, openCoverCechRefinementMap_id,
    Category.comp_id]

/-- 同じ添字で細分した、構造層の実際の引き戻しはスキームの射の合成と可換。 -/
theorem schemeStructureCechRefinedPullbackMap_comp (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A)
    (he : g ≫ f = k) (φA : R →+* Γ(A, ⊤)) (φB : R →+* Γ(B, ⊤))
    (φC : R →+* Γ(C, ⊤)) (hφf : φB = f.appTop.hom.comp φA)
    (hφg : φC = g.appTop.hom.comp φB) (hφk : φC = k.appTop.hom.comp φA)
    (U : ι → A.Opens) (V : ι → B.Opens) (W : ι → C.Opens)
    (hV : ∀ i, V i ≤ f ⁻¹ᵁ U i) (hW : ∀ i, W i ≤ g ⁻¹ᵁ V i)
    (hUW : ∀ i, W i ≤ k ⁻¹ᵁ U i) :
    schemeStructureCechRefinedPullbackMap f φA φB hφf U V id hV ≫
        schemeStructureCechRefinedPullbackMap g φB φC hφg V W id hW =
      schemeStructureCechRefinedPullbackMap k φA φC hφk U W id hUW := by
  subst k
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  funext t
  change ((schemeStructureCechRefinedPullbackMap g φB φC hφg V W id hW).f q).hom
      (((schemeStructureCechRefinedPullbackMap f φA φB hφf U V id hV).f q).hom a) t = _
  rw [schemeStructureCechRefinedPullbackMap_apply, schemeStructureCechRefinedPullbackMap_apply,
    schemeStructureCechRefinedPullbackMap_apply]
  have hc :
      f.appLE (cechOpenIntersection U (cechTupleSupport t))
        (cechOpenIntersection V (cechTupleSupport t))
        (schemeCechRefinedPullbackIntersection_le f U V id hV t) ≫
      g.appLE (cechOpenIntersection V (cechTupleSupport t))
        (cechOpenIntersection W (cechTupleSupport t))
        (schemeCechRefinedPullbackIntersection_le g V W id hW t) =
      (g ≫ f).appLE (cechOpenIntersection U (cechTupleSupport t))
        (cechOpenIntersection W (cechTupleSupport t))
        (schemeCechRefinedPullbackIntersection_le (g ≫ f) U W id hUW t) := by
    rw [Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun F : Γ(A, cechOpenIntersection U (cechTupleSupport t)) ⟶
      Γ(C, cechOpenIntersection W (cechTupleSupport t)) ↦ F.hom (a t)) hc

/-- 共通の元のスカラーを合成して引き戻すと、各段で引き戻したスカラーの合成になる。 -/
theorem schemeStructureCechPullbackScalar_comp (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A)
    (he : g ≫ f = k) (φ : R →+* Γ(A, ⊤)) :
    k.appTop.hom.comp φ = g.appTop.hom.comp (f.appTop.hom.comp φ) := by
  subst k
  rfl

/-- 共通の射への可換な三角形は、逆像被覆の細分を与える。 -/
theorem schemeStructureCechPreimage_refinement (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A)
    (he : g ≫ f = k) (U : ι → A.Opens) :
    ∀ i, k ⁻¹ᵁ U i ≤ g ⁻¹ᵁ (f ⁻¹ᵁ U i) := by
  intro i
  rw [← Scheme.Hom.comp_preimage, he]

end SerrePositivity.AlgebraicGeometry

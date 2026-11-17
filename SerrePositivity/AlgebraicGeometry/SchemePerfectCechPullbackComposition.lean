module

public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechRefinedPullback
public import SerrePositivity.AlgebraicGeometry.FullCechComplexHomExt

/-!
概要：実際の構造層の Frobenius 係数の引き戻しを、同じ添字の細分と合成に自然にする。
方針：各タプルで既存の appLE の合成と Frobenius 順極限の合成則を使う。
規約：平坦性や表示の選択の同型性を仮定せず、実際の余鎖写像を保つ。
使われ方：射影表示の同型から実際のブローアップへの四角形の移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {A B C : Scheme.{u}} {ι : Type} [DecidableEq ι]

/-- 逆像被覆への恒等細分を合成しても、実際の Frobenius 係数の引き戻しは同じ。 -/
theorem schemeStructurePerfectCechPullbackMap_eq_refined (f : B ⟶ A)
    (p : ℕ) (hp : p.Prime)
    (hA : ∀ O, (p : A.presheaf.obj O) = 0)
    (hB : ∀ O, (p : B.presheaf.obj O) = 0) (U : ι → A.Opens) :
    schemeStructurePerfectCechPullbackMap f p hp hA hB U =
      schemeStructurePerfectCechRefinedPullbackMap f p hp hA hB U (fun i ↦ f ⁻¹ᵁ U i)
        id (fun _ ↦ le_rfl) := by
  simp only [schemeStructurePerfectCechRefinedPullbackMap, openCoverCechRefinementMap_id,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ添字での Frobenius 係数の引き戻しの合成を、各次数の各タプルで表す。 -/
theorem schemeStructurePerfectCechRefinedPullbackMap_comp_apply
    (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A) (he : g ≫ f = k)
    (p : ℕ) (hp : p.Prime)
    (hA : ∀ O, (p : A.presheaf.obj O) = 0)
    (hB : ∀ O, (p : B.presheaf.obj O) = 0)
    (hC : ∀ O, (p : C.presheaf.obj O) = 0)
    (U : ι → A.Opens) (V : ι → B.Opens) (W : ι → C.Opens)
    (hV : ∀ i, V i ≤ f ⁻¹ᵁ U i) (hW : ∀ i, W i ≤ g ⁻¹ᵁ V i)
    (hUW : ∀ i, W i ≤ k ⁻¹ᵁ U i)
    (q : ℕ) (a : (fullCechComplex (openCoverCechDiagram
      (frobeniusRingDiagram A.presheaf p hp hA) U)).X q) (t : Fin (q + 1) → ι) :
    ((schemeStructurePerfectCechRefinedPullbackMap g p hp hB hC V W id hW).f q).hom
      (((schemeStructurePerfectCechRefinedPullbackMap f p hp hA hB U V id hV).f q).hom a) t =
        ((schemeStructurePerfectCechRefinedPullbackMap k p hp hA hC U W id hUW).f q).hom a t := by
  subst k
  rw [schemeStructurePerfectCechRefinedPullbackMap_apply,
    schemeStructurePerfectCechRefinedPullbackMap_apply,
    schemeStructurePerfectCechRefinedPullbackMap_apply]
  let Oa := cechOpenIntersection U (cechTupleSupport t)
  let Ob := cechOpenIntersection V (cechTupleSupport t)
  let Oc := cechOpenIntersection W (cechTupleSupport t)
  let α := f.appLE Oa Ob (schemeCechRefinedPullbackIntersection_le f U V id hV t)
  let β := g.appLE Ob Oc (schemeCechRefinedPullbackIntersection_le g V W id hW t)
  let γ := (g ≫ f).appLE Oa Oc
    (schemeCechRefinedPullbackIntersection_le (g ≫ f) U W id hUW t)
  have hc : α ≫ β = γ := by
    dsimp only [α, β, γ]
    rw [Scheme.Hom.appLE_comp_appLE]
  have hr : β.hom.comp α.hom = γ.hom := congrArg (fun m : Γ(A, Oa) ⟶ Γ(C, Oc) ↦ m.hom) hc
  have h := congrArg (fun m : FrobeniusDirectLimit Γ(A, Oa) p hp (hA (op Oa)) →+*
      FrobeniusDirectLimit Γ(C, Oc) p hp (hC (op Oc)) ↦ m (a t))
    (frobeniusDirectLimitMap_comp p hp (hA (op Oa)) (hB (op Ob)) α.hom (hC (op Oc)) β.hom)
  rw [hr] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- 同じ添字の被覆の細分を含め、Frobenius 係数の実際の引き戻しは合成を保つ。 -/
theorem schemeStructurePerfectCechRefinedPullbackMap_comp
    (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A) (he : g ≫ f = k)
    (p : ℕ) (hp : p.Prime)
    (hA : ∀ O, (p : A.presheaf.obj O) = 0)
    (hB : ∀ O, (p : B.presheaf.obj O) = 0)
    (hC : ∀ O, (p : C.presheaf.obj O) = 0)
    (U : ι → A.Opens) (V : ι → B.Opens) (W : ι → C.Opens)
    (hV : ∀ i, V i ≤ f ⁻¹ᵁ U i) (hW : ∀ i, W i ≤ g ⁻¹ᵁ V i)
    (hUW : ∀ i, W i ≤ k ⁻¹ᵁ U i) :
    schemeStructurePerfectCechRefinedPullbackMap f p hp hA hB U V id hV ≫
        schemeStructurePerfectCechRefinedPullbackMap g p hp hB hC V W id hW =
      schemeStructurePerfectCechRefinedPullbackMap k p hp hA hC U W id hUW := by
  apply fullCechComplex_hom_ext
    (D := openCoverCechDiagram (frobeniusRingDiagram A.presheaf p hp hA) U)
    (E := openCoverCechDiagram (frobeniusRingDiagram C.presheaf p hp hC) W)
  intro q a t
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using
    schemeStructurePerfectCechRefinedPullbackMap_comp_apply
      f g k he p hp hA hB hC U V W hV hW hUW q a t

end SerrePositivity.AlgebraicGeometry

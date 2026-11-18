module

public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechRefinedPullback
public import SerrePositivity.AlgebraicGeometry.FullCechComplexHomExt

/-!
概要：実際の構造層の Frobenius 係数の引き戻しを、異なる添字の細分と合成に自然にする。
方針：各タプルで既存の appLE の合成と Frobenius 順極限の合成則を使う。
規約：平坦性や表示の選択の同型性を仮定せず、実際の余鎖写像を保つ。
使われ方：射影表示の同型から実際のブローアップへの四角形の移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u w
variable {A B C : Scheme.{u}} {ι κ ν : Type} [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

/-- 異なる添字型の全タプル複体の射も、同じ target のタプルで外延的に比較できる。 -/
theorem fullCechComplex_hom_ext_index {R : Type w} [CommRing R]
    {D : Finset ι ⥤ ModuleCat.{u} R} {E : Finset ν ⥤ ModuleCat.{u} R}
    {f g : fullCechComplex D ⟶ fullCechComplex E}
    (h : ∀ (q : ℕ) (a : FullCechCochains D (q + 1)) (t : Fin (q + 1) → ν),
      (f.f q).hom a t = (g.f q).hom a t) : f = g := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact funext (h q a)

set_option backward.isDefEq.respectTransparency false in
/-- 異なる添字での Frobenius 係数の引き戻しの合成を、各次数の各タプルで表す。 -/
theorem schemeStructurePerfectCechRefinedPullbackMap_compIndex_apply
    (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A) (he : g ≫ f = k)
    (p : ℕ) (hp : p.Prime)
    (hA : ∀ O, (p : A.presheaf.obj O) = 0)
    (hB : ∀ O, (p : B.presheaf.obj O) = 0)
    (hC : ∀ O, (p : C.presheaf.obj O) = 0)
    (U : ι → A.Opens) (V : κ → B.Opens) (W : ν → C.Opens)
    (ρ : κ → ι) (σ : ν → κ)
    (hV : ∀ i, V i ≤ f ⁻¹ᵁ U (ρ i)) (hW : ∀ i, W i ≤ g ⁻¹ᵁ V (σ i))
    (hUW : ∀ i, W i ≤ k ⁻¹ᵁ U (ρ (σ i)))
    (q : ℕ) (a : (fullCechComplex (openCoverCechDiagram
      (frobeniusRingDiagram A.presheaf p hp hA) U)).X q) (t : Fin (q + 1) → ν) :
    ((schemeStructurePerfectCechRefinedPullbackMap g p hp hB hC V W σ hW).f q).hom
      (((schemeStructurePerfectCechRefinedPullbackMap f p hp hA hB U V ρ hV).f q).hom a) t =
        ((schemeStructurePerfectCechRefinedPullbackMap k p hp hA hC U W (ρ ∘ σ) hUW).f q).hom a t := by
  subst k
  rw [schemeStructurePerfectCechRefinedPullbackMap_apply,
    schemeStructurePerfectCechRefinedPullbackMap_apply,
    schemeStructurePerfectCechRefinedPullbackMap_apply]
  let Oa := cechOpenIntersection U (cechTupleSupport (fun j ↦ ρ (σ (t j))))
  let Ob := cechOpenIntersection V (cechTupleSupport (fun j ↦ σ (t j)))
  let Oc := cechOpenIntersection W (cechTupleSupport t)
  let α := f.appLE Oa Ob (schemeCechRefinedPullbackIntersection_le f U V ρ hV (fun j ↦ σ (t j)))
  let β := g.appLE Ob Oc (schemeCechRefinedPullbackIntersection_le g V W σ hW t)
  let γ := (g ≫ f).appLE Oa Oc
    (schemeCechRefinedPullbackIntersection_le (g ≫ f) U W (ρ ∘ σ) hUW t)
  have hc : α ≫ β = γ := by
    dsimp only [α, β, γ]
    rw [Scheme.Hom.appLE_comp_appLE]
  have hr : β.hom.comp α.hom = γ.hom := congrArg (fun m : Γ(A, Oa) ⟶ Γ(C, Oc) ↦ m.hom) hc
  have h := congrArg (fun m : FrobeniusDirectLimit Γ(A, Oa) p hp (hA (op Oa)) →+*
      FrobeniusDirectLimit Γ(C, Oc) p hp (hC (op Oc)) ↦ m (a (fun j ↦ ρ (σ (t j)))))
    (frobeniusDirectLimitMap_comp p hp (hA (op Oa)) (hB (op Ob)) α.hom (hC (op Oc)) β.hom)
  rw [hr] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- 三つの添字型の被覆の細分を含め、Frobenius 係数の実際の引き戻しは合成を保つ。 -/
theorem schemeStructurePerfectCechRefinedPullbackMap_compIndex
    (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A) (he : g ≫ f = k)
    (p : ℕ) (hp : p.Prime)
    (hA : ∀ O, (p : A.presheaf.obj O) = 0)
    (hB : ∀ O, (p : B.presheaf.obj O) = 0)
    (hC : ∀ O, (p : C.presheaf.obj O) = 0)
    (U : ι → A.Opens) (V : κ → B.Opens) (W : ν → C.Opens)
    (ρ : κ → ι) (σ : ν → κ)
    (hV : ∀ i, V i ≤ f ⁻¹ᵁ U (ρ i)) (hW : ∀ i, W i ≤ g ⁻¹ᵁ V (σ i))
    (hUW : ∀ i, W i ≤ k ⁻¹ᵁ U (ρ (σ i))) :
    schemeStructurePerfectCechRefinedPullbackMap f p hp hA hB U V ρ hV ≫
        schemeStructurePerfectCechRefinedPullbackMap g p hp hB hC V W σ hW =
      schemeStructurePerfectCechRefinedPullbackMap k p hp hA hC U W (ρ ∘ σ) hUW := by
  apply fullCechComplex_hom_ext_index
    (D := openCoverCechDiagram (frobeniusRingDiagram A.presheaf p hp hA) U)
    (E := openCoverCechDiagram (frobeniusRingDiagram C.presheaf p hp hC) W)
  intro q a t
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using
    schemeStructurePerfectCechRefinedPullbackMap_compIndex_apply
      f g k he p hp hA hB hC U V W ρ σ hV hW hUW q a t

end SerrePositivity.AlgebraicGeometry

module
public import SerrePositivity.DifferentialGraded.Perfect.Compact

/-! # compact性と標準Hom直和比較の全単射性 -/
@[expose] public section
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def derivedPostcomposeLinearMap {X Y Z : DerivedModuleCategory A D} (g : Y ⟶ Z) :
    (X ⟶ Y) →ₗ[A] (X ⟶ Z) where
  toFun f := f ≫ g
  map_add' f h := Preadditive.add_comp _ _ _ f h g
  map_smul' a f := Linear.smul_comp _ _ _ a f g

def moduleCompactComparison {J : Type u} (X : DerivedModuleCategory A D)
    (F : J → DerivedModuleCategory A D) :
    DirectSum J (fun j => X ⟶ F j) →ₗ[A] (X ⟶ ∐ F) :=
  DirectSum.toModule A J _ (fun j => derivedPostcomposeLinearMap A D (Sigma.ι F j))

lemma moduleCompactComparison_lof {J : Type u} (X : DerivedModuleCategory A D)
    (F : J → DerivedModuleCategory A D) (j : J) (f : X ⟶ F j) :
    moduleCompactComparison A D X F (DirectSum.lof A J (fun j => X ⟶ F j) j f) =
      f ≫ Sigma.ι F j :=
  by
    change DirectSum.toModule A J _
      (fun j => derivedPostcomposeLinearMap A D (Sigma.ι F j))
        (DirectSum.lof A J (fun j => X ⟶ F j) j f) =
      (derivedPostcomposeLinearMap A D (Sigma.ι F j)) f
    exact DirectSum.toModule_lof A (M := fun i => X ⟶ F i)
      (φ := fun j => derivedPostcomposeLinearMap A D (Sigma.ι F j)) j f

lemma moduleCompactComparison_injective {J : Type u} (X : DerivedModuleCategory A D)
    (F : J → DerivedModuleCategory A D) :
    Function.Injective (moduleCompactComparison A D X F) := by
  classical
  intro a b hab
  apply DFinsupp.ext
  intro j
  let p : (∐ F) ⟶ F j := Sigma.desc (Pi.single j (𝟙 (F j)))
  have he : (derivedPostcomposeLinearMap A D p).comp (moduleCompactComparison A D X F) =
      DirectSum.component A J (fun i => X ⟶ F i) j := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro f
    change moduleCompactComparison A D X F (DirectSum.lof A J (fun i => X ⟶ F i) i f) ≫ p = _
    rw [moduleCompactComparison_lof, Category.assoc]
    change f ≫ (Sigma.ι F i ≫ p) = (DirectSum.of (fun i => X ⟶ F i) i f) j
    by_cases hij : i = j
    · subst i
      simp [p]
    · rw [DirectSum.of_eq_of_ne (β := fun i => X ⟶ F i) i j f (Ne.symm hij)]
      simp [p, hij]
  have ha := congrArg (fun k => k a) he
  have hb := congrArg (fun k => k b) he
  exact ha.symm.trans ((congrArg (fun k => k ≫ p) hab).trans hb)

lemma moduleCompact_iff_comparison_surjective (X : DerivedModuleCategory A D) :
    moduleCompact A D X ↔ ∀ (J : Type u) (F : J → DerivedModuleCategory A D),
      Function.Surjective (moduleCompactComparison A D X F) := by
  classical
  constructor
  · intro h J F f
    obtain ⟨t, g, hg⟩ := h J F f
    refine ⟨∑ j ∈ t, DirectSum.lof A J (fun j => X ⟶ F j) j (g j), ?_⟩
    simpa only [map_sum, moduleCompactComparison_lof] using hg
  · intro h J F f
    obtain ⟨a, ha⟩ := h J F f
    refine ⟨a.support, fun j => a j, ?_⟩
    have he := congrArg (moduleCompactComparison A D X F) (DirectSum.sum_support_of a)
    have hterm (j : J) : moduleCompactComparison A D X F
        (DirectSum.of (fun i => X ⟶ F i) j (a j)) = a j ≫ Sigma.ι F j :=
      moduleCompactComparison_lof A D X F j (a j)
    simpa only [map_sum, hterm, ha] using he

lemma moduleCompact_iff_comparison_bijective (X : DerivedModuleCategory A D) :
    moduleCompact A D X ↔ ∀ (J : Type u) (F : J → DerivedModuleCategory A D),
      Function.Bijective (moduleCompactComparison A D X F) := by
  rw [moduleCompact_iff_comparison_surjective]
  constructor
  · intro h J F
    exact ⟨moduleCompactComparison_injective A D X F, h J F⟩
  · intro h J F
    exact (h J F).2

def moduleCompactHomLinearEquiv {X : DerivedModuleCategory A D} (hX : moduleCompact A D X)
    {J : Type u} (F : J → DerivedModuleCategory A D) :
    DirectSum J (fun j => X ⟶ F j) ≃ₗ[A] (X ⟶ ∐ F) :=
  LinearEquiv.ofBijective (moduleCompactComparison A D X F)
    ((moduleCompact_iff_comparison_bijective A D X).mp hX J F)

end SerrePositivity.DifferentialGraded

module
public import SerrePositivity.DifferentialGraded.Complexes.Cells
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # u-smallなacyclic複体の直積

各cycleの原像を成分ごとに選び、各次数の直積普遍性で組み立てる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] {J : Type w} [Small.{u} J]

/-- 各次数で複体の直積射影が直積を与える。 -/
def complexProductDegreeIsLimit (F : J → Complex A) (n : ℤ) :
    IsLimit (Fan.mk ((∏ᶜ F).X n) (fun j => (Pi.π F j).f n)) :=
  isLimitOfHasProductOfPreservesLimit (HomologicalComplex.eval (ModuleCat A) (.up ℤ) n) F

lemma complexProductDegree_hom_ext (F : J → Complex A) (n : ℤ)
    {P : ModuleCat.{u} A} {f g : P ⟶ (∏ᶜ F).X n}
    (h : ∀ j, f ≫ (Pi.π F j).f n = g ≫ (Pi.π F j).f n) : f = g := by
  apply (complexProductDegreeIsLimit A F n).hom_ext
  intro j
  exact h j.as

lemma complexProduct_acyclic (F : J → Complex A) (hF : ∀ j, (F j).Acyclic) :
    (∏ᶜ F).Acyclic := by
  intro p
  apply (HomologicalComplex.exactAt_iff' (K := ∏ᶜ F)
    (i := p - 1) (j := p) (k := p + 1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : (∏ᶜ F).X p, (∏ᶜ F).d p (p + 1) z = 0 →
    ∃ t : (∏ᶜ F).X (p - 1), (∏ᶜ F).d (p - 1) p t = z
  intro z hz
  have hj : ∀ j : J, ∃ t : (F j).X (p - 1),
      (F j).d (p - 1) p t = (Pi.π F j).f p z := by
    intro j
    have he := (HomologicalComplex.exactAt_iff' (K := F j)
      (i := p - 1) (j := p) (k := p + 1) (by simp) (by simp)).1 (hF j p)
    rw [ShortComplex.moduleCat_exact_iff] at he
    apply he
    have hc := congrArg (fun a => a z) ((Pi.π F j).comm p (p + 1))
    change (F j).d p (p + 1) ((Pi.π F j).f p z) =
      (Pi.π F j).f (p + 1) ((∏ᶜ F).d p (p + 1) z) at hc
    rw [hz, map_zero] at hc
    exact hc
  let tj := fun j => Classical.choose (hj j)
  let f : (𝟙_ (ModuleCat A)) ⟶ (∏ᶜ F).X (p - 1) :=
    Fan.IsLimit.lift (complexProductDegreeIsLimit A F (p - 1))
      (fun j => moduleElementMap A _ (tj j))
  let t := f (1 : A)
  have ht : ∀ j : J, (Pi.π F j).f (p - 1) t = tj j := by
    intro j
    have h := congrArg (fun a => a (1 : A))
      (Fan.IsLimit.fac (complexProductDegreeIsLimit A F (p - 1))
        (fun j => moduleElementMap A _ (tj j)) j)
    change (Pi.π F j).f (p - 1) t = (1 : A) • tj j at h
    exact h.trans (one_smul A _)
  refine ⟨t, ?_⟩
  have hm : moduleElementMap A _ ((∏ᶜ F).d (p - 1) p t) = moduleElementMap A _ z := by
    apply complexProductDegree_hom_ext A F p
    intro j
    apply (moduleElementEquiv A _).injective
    change (Pi.π F j).f p ((1 : A) • ((∏ᶜ F).d (p - 1) p t)) =
      (Pi.π F j).f p ((1 : A) • z)
    simp only [one_smul]
    have hc := congrArg (fun a => a t) ((Pi.π F j).comm (p - 1) p)
    change (F j).d (p - 1) p ((Pi.π F j).f (p - 1) t) =
      (Pi.π F j).f p ((∏ᶜ F).d (p - 1) p t) at hc
    exact hc.symm.trans ((congrArg ((F j).d (p - 1) p) (ht j)).trans (Classical.choose_spec (hj j)))
  have he := congrArg (fun a => a (1 : A)) hm
  change (1 : A) • ((∏ᶜ F).d (p - 1) p t) = (1 : A) • z at he
  simpa only [one_smul] using he

end SerrePositivity.DifferentialGraded

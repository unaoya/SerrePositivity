module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：有限被覆の全タプル Čech の各項は filtered 余極限を保つ。
方針：有限個の代表元と等式を一つの有限段へ送り、canonical な比較の全単射性を示す。
規約：被覆の添字を有限かつ固定する。無限積との交換は主張しない。
使われ方：実際の標準開の近似図式を Čech コホモロジーへ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]

/-- 全タプル版 Čech の固定した長さの項を、係数図式の関手として扱う。 -/
def projectiveCechCochainsFunctor (k : ℕ) :
    (Finset ι ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R where
  obj D := ModuleCat.of R (FullCechCochains D k)
  map η := ModuleCat.ofHom (fullCechCochainsMap η k)
  map_id _ := by ext a t; rfl
  map_comp _ _ := by ext a t; rfl

variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (D : J ⥤ Finset ι ⥤ ModuleCat.{u} R)

/-- 係数図式の余極限の各交叉の切断は、一つの有限段の代表元を持つ。 -/
theorem projectiveCoefficientColimit_exists_rep (s : Finset ι) (x : (colimit D).obj s) :
    ∃ (j : J) (a : (D.obj j).obj s), ((colimit.ι D j).app s).hom a = x := by
  exact Concrete.isColimit_exists_rep
    (D ⋙ (evaluation (Finset ι) (ModuleCat.{u} R)).obj s)
    (isColimitOfPreserves ((evaluation _ _).obj s) (colimit.isColimit D)) x

/-- 同じ段の係数が余極限で等しいことは、一つ先の段で等しいことと同値。 -/
theorem projectiveCoefficientColimit_eq_iff {j : J} (s : Finset ι)
    (a b : (D.obj j).obj s) :
    ((colimit.ι D j).app s).hom a = ((colimit.ι D j).app s).hom b ↔
      ∃ (l : J) (f : j ⟶ l), ((D.map f).app s).hom a = ((D.map f).app s).hom b := by
  exact (isColimitOfPreserves ((evaluation (Finset ι) (ModuleCat.{u} R)).obj s)
    (colimit.isColimit D)).eq_iff' a b

/-- canonical な Čech 各項の余極限比較は、有限段のタプル成分をそのまま送る。 -/
theorem projectiveCechColimitCochainsMap_ι (k : ℕ) (j : J)
    (a : FullCechCochains (D.obj j) k) :
    (colimit.post D (projectiveCechCochainsFunctor (R := R) (ι := ι) k)).hom
        ((colimit.ι (D ⋙ projectiveCechCochainsFunctor k) j).hom a) =
      fullCechCochainsMap (colimit.ι D j) k a := by
  exact congrArg (fun f ↦ f.hom a)
    (colimit.ι_post D (projectiveCechCochainsFunctor (R := R) (ι := ι) k) j)

variable [Fintype ι]

/-- 有限被覆の Čech 各項の filtered 余極限比較は全射。 -/
theorem projectiveCechColimitCochainsMap_surjective (k : ℕ) :
    Function.Surjective
      (colimit.post D (projectiveCechCochainsFunctor (R := R) (ι := ι) k)).hom := by
  classical
  intro a
  choose j x hx using fun t : Fin k → ι ↦
    projectiveCoefficientColimit_exists_rep D (cechTupleSupport t) (a t)
  obtain ⟨l, hl⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let f : ∀ t, j t ⟶ l := fun t ↦ (hl (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)).some
  let b : FullCechCochains (D.obj l) k := fun t ↦ ((D.map (f t)).app _).hom (x t)
  refine ⟨(colimit.ι (D ⋙ projectiveCechCochainsFunctor k) l).hom b, ?_⟩
  rw [projectiveCechColimitCochainsMap_ι]
  funext t
  change ((colimit.ι D l).app (cechTupleSupport t)).hom
    (((D.map (f t)).app (cechTupleSupport t)).hom (x t)) = a t
  have h := congrArg (fun η ↦ (η.app (cechTupleSupport t)).hom (x t)) (colimit.w D (f t))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.trans (hx t)

/-- 有限被覆の Čech 各項の filtered 余極限比較は単射。 -/
theorem projectiveCechColimitCochainsMap_injective (k : ℕ) :
    Function.Injective
      (colimit.post D (projectiveCechCochainsFunctor (R := R) (ι := ι) k)).hom := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  obtain ⟨j, b, rfl⟩ := Concrete.colimit_exists_rep
    (D ⋙ projectiveCechCochainsFunctor (R := R) (ι := ι) k) z
  have hz' : fullCechCochainsMap (colimit.ι D j) k b = 0 := by
    change (colimit.post D (projectiveCechCochainsFunctor (R := R) (ι := ι) k)).hom
      ((colimit.ι (D ⋙ projectiveCechCochainsFunctor k) j).hom b) = 0 at hz
    rwa [projectiveCechColimitCochainsMap_ι] at hz
  have heq (t : Fin k → ι) :
      ∃ (l : J) (f : j ⟶ l), ((D.map f).app (cechTupleSupport t)).hom (b t) = 0 := by
    have ht := congrFun hz' t
    change ((colimit.ι D j).app (cechTupleSupport t)).hom (b t) = 0 at ht
    obtain ⟨l, f, hf⟩ := (projectiveCoefficientColimit_eq_iff D (cechTupleSupport t) (b t) 0).mp
      (by simpa only [map_zero] using ht)
    exact ⟨l, f, by simpa only [map_zero] using hf⟩
  choose l f hf using heq
  obtain ⟨m, g, h, hh⟩ := IsFiltered.wideSpan f
  have hb : ((D ⋙ projectiveCechCochainsFunctor k).map g).hom b = 0 := by
    funext t
    change ((D.map g).app (cechTupleSupport t)).hom (b t) = 0
    rw [← hh t, D.map_comp]
    change ((D.map (h t)).app (cechTupleSupport t)).hom
      (((D.map (f t)).app (cechTupleSupport t)).hom (b t)) = 0
    rw [hf t, map_zero]
  have hw := congrArg (fun f ↦ f.hom b)
    (colimit.w (D ⋙ projectiveCechCochainsFunctor (R := R) (ι := ι) k) g)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hb, map_zero] at hw
  exact hw.symm

/-- 有限被覆の全タプル Čech の各項は、filtered 余極限を保つ。 -/
instance projectiveCechCochainsFunctorPreservesFilteredColimits (k : ℕ) :
    PreservesColimitsOfShape J (projectiveCechCochainsFunctor (R := R) (ι := ι) k) where
  preservesColimit {D} := by
    have : IsIso (colimit.post D (projectiveCechCochainsFunctor (R := R) (ι := ι) k)) :=
      (ConcreteCategory.isIso_iff_bijective
        (colimit.post D (projectiveCechCochainsFunctor (R := R) (ι := ι) k))).mpr
        ⟨projectiveCechColimitCochainsMap_injective D k,
          projectiveCechColimitCochainsMap_surjective D k⟩
    exact preservesColimit_of_isIso_post (projectiveCechCochainsFunctor k) D

end SerrePositivity.AlgebraicGeometry

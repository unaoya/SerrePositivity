module
public import SerrePositivity.InfinityCategories.Derived.DGModuleExtensionYonedaNerveIso
public import SerrePositivity.InfinityCategories.Derived.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.InfinityCategories.Derived.DGPerfectYoneda
public import SerrePositivity.KST.SConstruction.PerfectDGExtension

/-!
概要：実懸垂の対象宇宙で、元の dg Yoneda と実 Perf 延長の全関手自然性を保つ。
方針：正本の加群延長・Yoneda 同型を元の Perf 包含で反映し、同じ始域を回収する。
規約：基礎環と Small の宇宙 u を変更しない。固定 ν/K の定義を変えない。
使われ方：K-7 e の実商同値を、同じ厳密射の Perf 延長へ移送する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (C D : Type (max (u + 1) v))
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D] (f : DGFunctor R C D)

/-- 同じ任意宇宙の実 dg 射の Yoneda・Perf 延長四角形を保つ全関手比較。 -/
def dgKappaPerfectYonedaNaturality :
    FunctorIso (dgNerve.map (dgPerfectYoneda R C) ≫ dgNerve.map (perfectDGExtension R C D f))
      (dgNerve.map f ≫ dgNerve.map (dgPerfectYoneda R D)) := by
  let W := (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C).comp
    ((dgPerfectYoneda R C).comp (perfectDGExtension R C D f))
  let Z := (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C).comp
    (f.comp (dgPerfectYoneda R D))
  have hw : W.comp (perfectDGModuleInclusion R D Set.univ) =
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C).comp
        ((dgYoneda R C).comp (dgModuleExtension R C D f)) := by
    dsimp only [W]
    simp only [strictDGFunctor_comp_assoc]
    rw [perfectDGExtension_inclusion,
      ← strictDGFunctor_comp_assoc (dgPerfectYoneda R C)
        (perfectDGModuleInclusion R C Set.univ) (dgModuleExtension R C D f),
      dgPerfectYoneda_inclusion]
  have hz : Z.comp (perfectDGModuleInclusion R D Set.univ) =
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C).comp
        (f.comp (dgYoneda R D)) := by
    dsimp only [Z]
    rw [strictDGFunctor_comp_assoc, strictDGFunctor_comp_assoc, dgPerfectYoneda_inclusion]
  have h : FunctorIso (dgNerve.map W ≫ dgNerve.map (perfectDGModuleInclusion R D Set.univ))
      (dgNerve.map Z ≫ dgNerve.map (perfectDGModuleInclusion R D Set.univ)) := by
    rw [← dgNerve.map_comp, ← dgNerve.map_comp, hw, hz]
    exact dgModuleExtensionYonedaNerveIso R C D f
  have e := (dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R D)
    (modulePerfectProjectiveOver R D Set.univ)).preimageFunctorIso h
  have p := e.precomp (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))
  rw [← dgNerve.map_comp, ← dgNerve.map_comp] at p
  change FunctorIso (dgNerve.map ((dgPerfectYoneda R C).comp (perfectDGExtension R C D f)))
    (dgNerve.map (f.comp (dgPerfectYoneda R D))) at p
  simpa only [dgNerve.map_comp] using p

end SerrePositivity.KST.NonConnective

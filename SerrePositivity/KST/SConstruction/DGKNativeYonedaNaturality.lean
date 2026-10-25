module
public import SerrePositivity.KST.SConstruction.DGKNativeValueComparison
public import SerrePositivity.InfinityCategories.Derived.DGModuleExtensionYonedaNerveIso
public import SerrePositivity.InfinityCategories.Derived.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition
public import SerrePositivity.KST.SConstruction.DGFunctorCoherence
public import SerrePositivity.DifferentialGraded.Perfect.Enhancement
public import SerrePositivity.DifferentialGraded.Category.FullSubcategory

/-!
概要：元の小 dg 関手と実 Perf 延長の Yoneda 四角形を全関手同型で比較する。
方針：D の全 Hom 自然な加群比較を同じ Perf 包含で反映し、元始域を回収する。
規約：入力 dg 関手と元の Yoneda を保持し、Small Perf を仮定しない。
使われ方：d④ の native 二辺と固定 ν 二辺の比較の基礎。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D E : Type (u + 1))
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]

/-- 概要：同じ元 dg 関手による実 Perf 延長は元対象像の Yoneda と全自然に同型。
方針：D の同じ加群自然性を Perf の充満忠実包含で反映する。
規約：始域の一時的な宇宙持ち上げを厳密に消去する。
使われ方：固定 ν 比較の同じ二辺を照合する全自然性。 -/
def dgKNativeYonedaExtensionComparison (F : DGFunctor R D E) : FunctorIso
    (dgNerve.map (dgPerfectYoneda R D) ≫ dgNerve.map (perfectDGExtension R D E F))
    (dgNerve.map F ≫ dgNerve.map (dgPerfectYoneda R E)) := by
  let W := (dgUniverseLiftDown.{u, u + 1, u + 1} R D).comp
    ((dgPerfectYoneda R D).comp (perfectDGExtension R D E F))
  let Z := (dgUniverseLiftDown.{u, u + 1, u + 1} R D).comp
    (F.comp (dgPerfectYoneda R E))
  have hw : W.comp (perfectDGModuleInclusion R E Set.univ) =
      (dgUniverseLiftDown.{u, u + 1, u + 1} R D).comp
        ((dgYoneda R D).comp (dgModuleExtension R D E F)) := by
    dsimp only [W]
    simp only [strictDGFunctor_comp_assoc]
    rw [perfectDGExtension_inclusion,
      ← strictDGFunctor_comp_assoc (dgPerfectYoneda R D)
        (perfectDGModuleInclusion R D Set.univ) (dgModuleExtension R D E F),
      dgPerfectYoneda_inclusion]
  have hz : Z.comp (perfectDGModuleInclusion R E Set.univ) =
      (dgUniverseLiftDown.{u, u + 1, u + 1} R D).comp (F.comp (dgYoneda R E)) := by
    dsimp only [Z]
    rw [strictDGFunctor_comp_assoc, strictDGFunctor_comp_assoc, dgPerfectYoneda_inclusion]
  have m : FunctorIso (dgNerve.map W ≫ dgNerve.map (perfectDGModuleInclusion R E Set.univ))
      (dgNerve.map Z ≫ dgNerve.map (perfectDGModuleInclusion R E Set.univ)) := by
    rw [← dgNerve.map_comp, ← dgNerve.map_comp, hw, hz]
    exact dgModuleExtensionYonedaNerveIso R D E F
  have e := (dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R E)
    (modulePerfectProjectiveOver R E Set.univ)).preimageFunctorIso m
  have p := e.precomp (dgNerve.map (dgUniverseLiftUp.{u, u + 1, u + 1} R D))
  rw [← dgNerve.map_comp, ← dgNerve.map_comp] at p
  change FunctorIso (dgNerve.map ((dgPerfectYoneda R D).comp (perfectDGExtension R D E F)))
    (dgNerve.map (F.comp (dgPerfectYoneda R E))) at p
  simpa only [dgNerve.map_comp] using p

end SerrePositivity.KST.SConstruction

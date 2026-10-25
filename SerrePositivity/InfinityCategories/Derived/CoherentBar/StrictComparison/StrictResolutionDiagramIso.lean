module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DerivedBarDiagram
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ResolvedCoherentHomology
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactor

/-!
概要：正本の strict 導来図式を、全加群上の同じ分解を使う図式へ全関手同型で比較する。
方針：閉零ラベルの付け外しと、実分解の raw factor 比較を合わせる。
規約：頂点だけでなく全 HA 単体の比較。
使われ方：C2 の比較値を正本 DGKappaStrictFilteredColimitComparison へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarRightModuleRelabel_forget :
    (dgBarRightModuleRelabel R D).comp (dgConeModuleForget R D) =
      DGFunctor.id (RightModule R D) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro M N
  simp only [EnrichedFunctor.comp_map, EnrichedFunctor.id_map,
    dgBarRightModuleRelabel, dgConeModuleForget, Category.id_comp]
  rfl

def dgBarRightModuleDerived_resolutionIso :
    FunctorIso (dgBarRightModuleDerived R D) (dgBarModuleResolution R D) := by
  have e := (dgModuleResolvedInfinity_rawFactorIso R (ModuleCategory R D) D
    (dgConeModuleForget R D)).precomp (dgNerve.map (dgBarRightModuleRelabel R D))
  rw [← Category.assoc, ← dgNerve.map_comp, dgBarRightModuleRelabel_forget,
    dgNerve.map_id, Category.id_comp] at e
  exact e

def dgBarStrictResolutionDiagramIso {J : Type u} [Category.{u} J]
    (F : J ⥤ ModuleCategory R D) :
    FunctorIso (dgKappaStrictModuleDiagram R D F)
      (dgCoherentBarStrictDiagram R D F ≫ dgBarModuleResolution R D) := by
  have e := (dgBarRightModuleDerived_resolutionIso R D).precomp (dgCoherentBarStrictDiagram R D F)
  rw [dgBarRightModuleDerived_strictDiagram] at e
  exact e

end SerrePositivity.InfinityCategories

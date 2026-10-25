module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeColimit
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.StrictComparison
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Diagram

/-!
概要：B の全加群 dg nerve の bar 図式を、正本の実導来図式へ接続する。
方針：同じ全 dg Hom を保つ閉零ラベルを付け、指定された実分解関手へ送る。
規約：頂点だけでなく元の strict 図式の全単体上の一致を要求する。
使われ方：native bar 余錐の実導来像と C1 の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def dgBarRightModuleRelabel : DGFunctor R (RightModule R D) (ModuleCategory R D) where
  obj M := ForgetEnrichment.of (Complex R) M
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp _ _ _ := by
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
    rfl

def dgBarRightModuleDerived :
    dgNerve R (RightModule R D) ⟶ dgModuleDerivedInfinityCategory R D :=
  dgNerve.map (dgBarRightModuleRelabel R D) ≫ dgConeModuleDerived R D

lemma dgBarRightModuleDerived_strictDiagram {J : Type u} [Category J]
    (F : J ⥤ ModuleCategory R D) :
    dgCoherentBarStrictDiagram R D F ≫ dgBarRightModuleDerived R D =
      dgKappaStrictModuleDiagram R D F := by
  rfl

def dgKappaStrictDerivedBarCocone {J : Type u} [Category J]
    (F : J ⥤ ModuleCategory R D) : JoinCocone (dgKappaStrictModuleDiagram R D F) :=
  ⟨(dgCoherentBarNormalizedNativeCoconeUnconditional R D
      (dgCoherentBarStrictDiagram R D F)).val ≫ dgBarRightModuleDerived R D,
    by rw [← Category.assoc,
      (dgCoherentBarNormalizedNativeCoconeUnconditional R D
        (dgCoherentBarStrictDiagram R D F)).property, dgBarRightModuleDerived_strictDiagram]⟩

lemma dgKappaStrictDerivedBarCocone_vertex {J : Type u} [Category J]
    (F : J ⥤ ModuleCategory R D) :
    (dgKappaStrictDerivedBarCocone R D F).vertex =
      dgConeModuleDerivedVertex R D
        (ForgetEnrichment.of (Complex R) (dgCoherentBarStrictNormalizedModule R D F)) := by
  change (dgBarRightModuleDerived R D).app _
    (dgCoherentBarNormalizedNativeCoconeUnconditional R D
      (dgCoherentBarStrictDiagram R D F)).vertex = _
  rw [dgCoherentBarNormalizedNativeCocone_vertex]
  rfl

end SerrePositivity.InfinityCategories

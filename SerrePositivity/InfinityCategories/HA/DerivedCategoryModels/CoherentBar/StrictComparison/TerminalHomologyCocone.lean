module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictNativeCocone
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ResolvedCoherentHomology
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictHomologyDiagram

/-!
概要：WithTerminal 上のホモロジー図式から同じ通常の余錐を回収する。
方針：新しい終頂点への射を脚とし、全図式上の自然同型で余極限性を移す。
規約：拡張図式と同じ頂点・同じ脚を保持する。
使われ方：実分解 augmentation の図式と余錐の同時比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits
variable (R : Type u) [CommRing R] {J : Type u} [Category.{u} J]

def dgBarTerminalHomologyCocone (A : WithTerminal J ⥤ ModuleCat.{u} R) :
    Cocone ((WithTerminal.incl : J ⥤ WithTerminal J) ⋙ A) where
  pt := A.obj WithTerminal.star
  ι :=
    { app j := A.map (WithTerminal.homFrom j)
      naturality i j f := by
        change A.map (WithTerminal.incl.map f) ≫ A.map (WithTerminal.homFrom j) = _ ≫ 𝟙 _
        rw [← Functor.map_comp, Category.comp_id]
        congr 1 }

def dgBarTerminalHomologyCoconeIso
    {A B : WithTerminal J ⥤ ModuleCat.{u} R} (e : A ≅ B) :
    (Cocone.precompose (Functor.isoWhiskerLeft WithTerminal.incl e).hom).obj
        (dgBarTerminalHomologyCocone R B) ≅ dgBarTerminalHomologyCocone R A :=
  Cocone.ext (e.app WithTerminal.star).symm (by
    intro j
    change e.hom.app (WithTerminal.of j) ≫ B.map (WithTerminal.homFrom j) ≫
      e.inv.app WithTerminal.star = A.map (WithTerminal.homFrom j)
    rw [← e.hom.naturality_assoc, e.hom_inv_id_app, Category.comp_id])

def dgBarTerminalHomologyIsColimit_of_iso
    {A B : WithTerminal J ⥤ ModuleCat.{u} R} (e : A ≅ B)
    (hB : IsColimit (dgBarTerminalHomologyCocone R B)) :
    IsColimit (dgBarTerminalHomologyCocone R A) :=
  IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (Functor.isoWhiskerLeft WithTerminal.incl e) _).symm hB)
    (dgBarTerminalHomologyCoconeIso R e)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

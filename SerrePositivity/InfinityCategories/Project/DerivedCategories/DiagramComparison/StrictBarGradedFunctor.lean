module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Structure.DGCoherentBarGraded
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram

/-!
概要：小さいstrict図式のcoherent barのgraded直和を、元の自然変換に関手的にする。
方針：各射列の先頭の自然変換を同じ次数だけシフトし、同じラベルの余積で束ねる。
規約：ここではMC微分を変更する前の直和だけを扱う。bar微分との可換性は別の等式。
使われ方：3b-3 R6、正規化barと指定余錐の全パラメーター比較の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元の各射列ラベルで、同じ先頭の自然変換を同じシフトへ写す。 -/
def strictBarGradedMap {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) :
    dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F) ⟶
      dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A G) :=
  Sigma.desc (fun s =>
    (moduleShiftFunctor A PUnit.{1} (s.1 : ℤ)).map (η.app (s.2.down.obj 0)) ≫
      Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A G)) s)

/-- barのgraded直和の自然変換による像は、各余積因子で元のシフトした成分。 -/
@[reassoc]
lemma strictBarGradedMap_ι {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G)
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s ≫
        strictBarGradedMap A J η =
      (moduleShiftFunctor A PUnit.{1} (s.1 : ℤ)).map (η.app (s.2.down.obj 0)) ≫
        Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A G)) s := by
  exact Sigma.ι_comp_desc _ _

/-- 元のstrict図式と自然変換に関手的な、同じbarのgraded直和。 -/
def strictBarGradedFunctor : (J ⥤ ModuleCategory A PUnit.{1}) ⥤ ModuleCategory A PUnit.{1} where
  obj F := dgCoherentBarGraded A PUnit.{1} (smallStrictBarDiagram A F)
  map η := strictBarGradedMap A J η
  map_id F := by
    apply Sigma.hom_ext
    intro s
    rw [strictBarGradedMap_ι]
    simp
  map_comp η θ := by
    apply Sigma.hom_ext
    intro s
    rw [strictBarGradedMap_ι, strictBarGradedMap_ι_assoc, strictBarGradedMap_ι]
    simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

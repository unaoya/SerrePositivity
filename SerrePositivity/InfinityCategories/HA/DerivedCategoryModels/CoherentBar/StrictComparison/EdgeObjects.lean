module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Diagram

/-!
概要：strict bar の辺の両端の頂点を元の図式の頂点として同定する。
方針：nerve の face と tail の頂点を計算する。
規約：単体と次数を保つ。
使われ方：augmentation の辺の係数の端点輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {J : Type u} [Category J]

lemma dgStrictEdgeFace_obj (s : (nerve J) _⦋1⦌) :
    ((nerve J).δ (1 : Fin 2) s).obj (0 : Fin 1) = s.obj (0 : Fin 2) := rfl

lemma dgStrictEdgeTail_obj (s : (nerve J) _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s 1 (by decide)).2.obj (0 : Fin 1) = s.obj (1 : Fin 2) := rfl

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (F : J ⥤ ModuleCategory R D)

lemma dgStrictEdgeFamily (s : (nerve J) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨1, s⟩ =
      ForgetEnrichment.of (Complex R)
        (shiftModule 1 (ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)))) := rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

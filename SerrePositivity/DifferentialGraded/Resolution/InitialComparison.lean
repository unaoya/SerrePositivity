module
public import SerrePositivity.DifferentialGraded.Resolution.Initial
public import SerrePositivity.DifferentialGraded.Resolution.CycleCoverFunctor

/-! # dg関手による初期自由cycle coverの比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCategoryCycleCover
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def map : DGFunctor A (Source A D) (Source A E) :=
  FreeDGCategory.lift A D (Source A E) (edges A D) F.obj
    (fun x y => complexCycleCoverMap A (F.map x y) ≫
      FreeDGCategory.edgeInclusion A E (edges A E) (F.obj x) (F.obj y))

lemma map_obj (x : D) : (map A D E F).obj x = F.obj x := rfl

lemma edge_map (x y : D) :
    FreeDGCategory.edgeInclusion A D (edges A D) x y ≫ (map A D E F).map x y =
    complexCycleCoverMap A (F.map x y) ≫
      FreeDGCategory.edgeInclusion A E (edges A E) (F.obj x) (F.obj y) :=
  FreeDGCategory.lift_edge A D (Source A E) (edges A D) F.obj _ x y

lemma map_augmentation :
    (map A D E F).comp (augmentation A E) = (augmentation A D).comp F := by
  apply (FreeDGCategory.universalEquiv A D E (edges A D)).injective
  change (⟨F.obj, fun x y => FreeDGCategory.edgeInclusion A D (edges A D) x y ≫
    ((map A D E F).map x y ≫ (augmentation A E).map (F.obj x) (F.obj y))⟩ :
      FreeDGCategory.GeneratorMap A D E (edges A D)) =
    ⟨F.obj, fun x y => FreeDGCategory.edgeInclusion A D (edges A D) x y ≫
      ((augmentation A D).map x y ≫ F.map x y)⟩
  congr 1
  funext x y
  rw [← Category.assoc, edge_map, Category.assoc, edge_augmentation,
    ← Category.assoc, complexCycleCoverMap_π, edge_augmentation]

end SerrePositivity.DifferentialGraded.DGCategoryCycleCover

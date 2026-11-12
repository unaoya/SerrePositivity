module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTargetPointedDisplay
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFullSubcategoryNerve
/-!
概要：充満 dg 部分圏の同じ固定始点 Hom 関手を、周囲の Hom 関手の実制限へ同定する。
方針：同じ全 Hom 複体と元の全 dg 合成を保持する。
規約：対象条件の閉性や Small 性は不要。使われ方：導来出力の表現可能 Hom 試験。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (P : C → Prop) (x : _root_.SerrePositivity.DifferentialGraded.DGFullSubcategory C P)
/-- 同じ全 Hom 関手の充満部分圏への厳密制限。 -/
lemma dgFullSubcategoryHomTargetModuleLift :
    (dgFullSubcategoryInclusion R C P).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift R C x.val) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift R (DGFullSubcategory C P) x := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgFullSubcategoryInclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift,
    Category.id_comp, Category.comp_id, eqToHom_refl]
/-- 同じ全 Hom 関手の充満部分圏への厳密制限。 -/
lemma dgFullSubcategoryHomTargetUnderlyingSpaceInfinity :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R C P)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R C x.val =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (DGFullSubcategory C P) x := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity, ← Category.assoc,
    ← Functor.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, dgFullSubcategoryHomTargetModuleLift]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories

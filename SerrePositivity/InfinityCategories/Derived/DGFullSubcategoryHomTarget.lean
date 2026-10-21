module
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetPointedDisplay
public import SerrePositivity.InfinityCategories.Derived.DGFullSubcategoryNerve
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (P : C → Prop) (x : DGFullSubcategory C P)
/-- 同じ全 Hom 関手の充満部分圏への厳密制限。 -/
lemma dgFullSubcategoryHomTargetModuleLift :
    (dgFullSubcategoryInclusion R C P).comp (dgHomTargetModuleLift R C x.val) =
      dgHomTargetModuleLift R (DGFullSubcategory C P) x := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgFullSubcategoryInclusion, dgHomTargetModuleLift,
    Category.id_comp, Category.comp_id, eqToHom_refl]
/-- 同じ全 Hom 関手の充満部分圏への厳密制限。 -/
lemma dgFullSubcategoryHomTargetUnderlyingSpaceInfinity :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (dgNerve.map (dgFullSubcategoryInclusion R C P)) ≫
        dgHomTargetUnderlyingSpaceInfinity R C x.val =
      dgHomTargetUnderlyingSpaceInfinity R (DGFullSubcategory C P) x := by
  simp only [dgHomTargetUnderlyingSpaceInfinity, ← Category.assoc,
    ← Functor.map_comp, ← dgNerve.map_comp, dgFullSubcategoryHomTargetModuleLift]
  rfl
end SerrePositivity.InfinityCategories

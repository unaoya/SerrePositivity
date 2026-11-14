module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGHomTargetUnitComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGHomTargetCosliceComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGClosedHomWhiskerNaturality
/-!
概要：同じ Hom 単位による比較鎖同型を、対象だけの共通宇宙持ち上げ後にも保つ。
方針：実 dg 関手の閉前合成自然性と、その恒等 Hom 鎖写像を使う。
規約：入力の小ささも元の出力の射影性も不要。使われ方：実 Hom 単位の全 coslice fiber 同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x y : C)
/-- 対象宇宙持ち上げ後の同じ比較鎖写像も、元の同じ dg Yoneda 同型の逆。 -/
lemma dgHomTargetUnitLiftHomMap_eq :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift R C x).map x y ≫
      eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x))
        (ForgetEnrichment.of (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift R C x).obj y)) =
      (dgYonedaIso R PUnit.unit ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y)).inv := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorHom_precompose
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1}))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x)
    (ForgetEnrichment.of (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y))
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, Category.comp_id, Category.id_comp] at h
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift, EnrichedFunctor.comp_map]
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).map x y ≫ 𝟙 _) ≫
    eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x))
      (ForgetEnrichment.of (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift R C x).obj y)) = _
  rw [Category.comp_id]
  erw [← h]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnitHomMap_eq R C x y
/-- 持ち上げた同じ実 Hom 単位の比較鎖写像は全次数の鎖同型。 -/
lemma dgHomTargetUnitLiftHomMap_isIso :
    IsIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift R C x).map x y ≫
      eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x))
        (ForgetEnrichment.of (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift R C x).obj y))) := by
  rw [dgHomTargetUnitLiftHomMap_eq]
  infer_instance
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.YonedaNerveIso
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ProjectiveHomCriterion
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
/-!
概要：代表 Hom と評価との全比較を、実 R 加群値の coherent 関手へ送る。
方針：共通宇宙の nerve 関手同型を、同じ ringConstantDG の nerve で後合成する。
規約：全 Hom の dg 作用を保ち、対象だけの比較へ弱めない。
使われ方：coherent C1 の評価比較と native Hom 空間関手の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- 元の Hom と評価を R 加群値にした二つの全 coherent 関手の同型。 -/
def dgBarCompactYoneda_ringNerveIso (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        ((_root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.SerrePositivity.DifferentialGraded.representable R x)).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluationDG R D x).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R))) := by
  have e := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactYoneda_nerveIso.{u, v, w} R D x).postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, u + 1, u + 1, max (u + 1) v w} (ringConstantDG R))
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_comp.{u, max (u + 1) v, u + 1, u + 1, w}
    (R := R) (_root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.SerrePositivity.DifferentialGraded.representable R x)) (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_comp.{u, max (u + 1) v, u + 1, u + 1, w}
    (R := R) (_root_.SerrePositivity.DifferentialGraded.moduleEvaluationDG R D x) (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R)
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
      (_root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.SerrePositivity.DifferentialGraded.representable R x)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, u + 1, u + 1, max (u + 1) v w} (ringConstantDG R) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
      ((_root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.SerrePositivity.DifferentialGraded.representable R x)).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R)) at h₁
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
      (_root_.SerrePositivity.DifferentialGraded.moduleEvaluationDG R D x) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, u + 1, u + 1, max (u + 1) v w} (ringConstantDG R) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
      ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluationDG R D x).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R)) at h₂
  rw [h₁, h₂] at e
  exact e

/-- 同じ射影的入力を、その x 評価の実 R 加群へ送る dg 関手。 -/
def dgBarCompactProjectiveEvaluationModuleDG (x : D) :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) (RightModule R PUnit.{1}) :=
  (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).comp
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluationDG R D x).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R))

/-- 射影的部分圏に制限した同じ代表 Hom は、元の実 Hom 加群値関手と一致する。 -/
lemma dgBarCompactProjectiveHomModuleDG_eq (x : D) :
    (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).comp
        ((_root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.SerrePositivity.DifferentialGraded.representable R x)).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactRepresentableProjective R D x) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro M N
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion,
    Category.id_comp, eqToHom_refl, Category.comp_id]

/-- 射影的模型の同じ代表 Hom と評価の、全 R 加群値 coherent 関手比較。 -/
def dgBarCompactProjectiveEvaluationModuleNerveIso (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactRepresentableProjective R D x)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        (dgBarCompactProjectiveEvaluationModuleDG R D x)) := by
  have e := (dgBarCompactYoneda_ringNerveIso.{u, v, w} R D x).precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) v, max (u + 1) v w}
      (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)))
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_comp.{u, max (u + 1) v, max (u + 1) v, u + 1, w}
    (R := R)
    (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D))
    ((_root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.SerrePositivity.DifferentialGraded.representable R x)).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R))
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_comp.{u, max (u + 1) v, max (u + 1) v, u + 1, w}
    (R := R)
    (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D))
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluationDG R D x).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R))
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) v, max (u + 1) v w}
      (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        ((_root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.SerrePositivity.DifferentialGraded.representable R x)).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
      ((dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).comp
        ((_root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.SerrePositivity.DifferentialGraded.representable R x)).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R))) at h₁
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) v, max (u + 1) v w}
      (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluationDG R D x).comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
      (dgBarCompactProjectiveEvaluationModuleDG R D x) at h₂
  rw [h₁, h₂, dgBarCompactProjectiveHomModuleDG_eq] at e
  exact e

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact

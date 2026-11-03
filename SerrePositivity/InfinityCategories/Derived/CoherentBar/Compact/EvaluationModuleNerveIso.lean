module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.YonedaNerveIso
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ProjectiveHomCriterion
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 元の Hom と評価を R 加群値にした二つの全 coherent 関手の同型。 -/
def dgBarCompactYoneda_ringNerveIso (x : D) :
    FunctorIso
      (dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        ((leftRepresentable R (representable R x)).comp (ringConstantDG R)))
      (dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        ((moduleEvaluationDG R D x).comp (ringConstantDG R))) := by
  have e := (dgBarCompactYoneda_nerveIso.{u, v, w} R D x).postcomp
    (dgNerveCommonMap.{u, u + 1, u + 1, max (u + 1) v w} (ringConstantDG R))
  have h₁ := dgNerveCommonMap_comp.{u, max (u + 1) v, u + 1, u + 1, w}
    (R := R) (leftRepresentable R (representable R x)) (ringConstantDG R)
  have h₂ := dgNerveCommonMap_comp.{u, max (u + 1) v, u + 1, u + 1, w}
    (R := R) (moduleEvaluationDG R D x) (ringConstantDG R)
  change dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
      (leftRepresentable R (representable R x)) ≫
      dgNerveCommonMap.{u, u + 1, u + 1, max (u + 1) v w} (ringConstantDG R) =
    dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
      ((leftRepresentable R (representable R x)).comp (ringConstantDG R)) at h₁
  change dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
      (moduleEvaluationDG R D x) ≫
      dgNerveCommonMap.{u, u + 1, u + 1, max (u + 1) v w} (ringConstantDG R) =
    dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
      ((moduleEvaluationDG R D x).comp (ringConstantDG R)) at h₂
  rw [h₁, h₂] at e
  exact e

/-- 同じ射影的入力を、その x 評価の実 R 加群へ送る dg 関手。 -/
def dgBarCompactProjectiveEvaluationModuleDG (x : D) :
    DGFunctor R (ProjectiveDGModules R D) (RightModule R PUnit.{1}) :=
  (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)).comp
    ((moduleEvaluationDG R D x).comp (ringConstantDG R))

/-- 射影的部分圏に制限した同じ代表 Hom は、元の実 Hom 加群値関手と一致する。 -/
lemma dgBarCompactProjectiveHomModuleDG_eq (x : D) :
    (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)).comp
        ((leftRepresentable R (representable R x)).comp (ringConstantDG R)) =
      dgHomTargetModuleDG R (ProjectiveDGModules R D)
        (dgBarCompactRepresentableProjective R D x) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro M N
  simp only [EnrichedFunctor.comp_map, dgFullSubcategoryInclusion,
    Category.id_comp, eqToHom_refl, Category.comp_id]

/-- 射影的模型の同じ代表 Hom と評価の、全 R 加群値 coherent 関手比較。 -/
def dgBarCompactProjectiveEvaluationModuleNerveIso (x : D) :
    FunctorIso
      (dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        (dgHomTargetModuleDG R (ProjectiveDGModules R D)
          (dgBarCompactRepresentableProjective R D x)))
      (dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        (dgBarCompactProjectiveEvaluationModuleDG R D x)) := by
  have e := (dgBarCompactYoneda_ringNerveIso.{u, v, w} R D x).precomp
    (dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) v, max (u + 1) v w}
      (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)))
  have h₁ := dgNerveCommonMap_comp.{u, max (u + 1) v, max (u + 1) v, u + 1, w}
    (R := R)
    (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D))
    ((leftRepresentable R (representable R x)).comp (ringConstantDG R))
  have h₂ := dgNerveCommonMap_comp.{u, max (u + 1) v, max (u + 1) v, u + 1, w}
    (R := R)
    (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D))
    ((moduleEvaluationDG R D x).comp (ringConstantDG R))
  change dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) v, max (u + 1) v w}
      (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)) ≫
      dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        ((leftRepresentable R (representable R x)).comp (ringConstantDG R)) =
    dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
      ((dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)).comp
        ((leftRepresentable R (representable R x)).comp (ringConstantDG R))) at h₁
  change dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) v, max (u + 1) v w}
      (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)) ≫
      dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        ((moduleEvaluationDG R D x).comp (ringConstantDG R)) =
    dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
      (dgBarCompactProjectiveEvaluationModuleDG R D x) at h₂
  rw [h₁, h₂, dgBarCompactProjectiveHomModuleDG_eq] at e
  exact e

end SerrePositivity.InfinityCategories

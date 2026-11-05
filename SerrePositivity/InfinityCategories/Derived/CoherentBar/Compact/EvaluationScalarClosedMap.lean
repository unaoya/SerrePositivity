module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationPiChart
/-!
概要：実評価を一対象環の加群として読み戻しても、元の全閉射作用を保つ。
方針：ringConstant の全 Hom 評価の逆同型を相殺する。
規約：元の dg 評価関手と同じ射を使う。
使われ方：native 評価チャートの係数自然性を元の bar ホモロジーへ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarCompactEvaluationScalarDG_eq (x : D) :
    ((dgBarCompactProjectiveEvaluationModuleDG R D x).comp
      (moduleEvaluationDG R PUnit.{1} PUnit.unit)) =
      (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)).comp
        (moduleEvaluationDG R D x) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgBarCompactProjectiveEvaluationModuleDG R D x).comp
      (moduleEvaluationDG R PUnit.{1} PUnit.unit))
    (G := (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)).comp
      (moduleEvaluationDG R D x)) (fun _ => rfl)
  intro M N
  change ((𝟙 _ ≫ moduleHomπ R D M.val N.val x) ≫
      (ringConstantHomIso R (M.val.obj (Opposite.op x)) (N.val.obj (Opposite.op x))).inv) ≫
        (ringConstantHomIso R (M.val.obj (Opposite.op x)) (N.val.obj (Opposite.op x))).hom =
      𝟙 _ ≫ moduleHomπ R D M.val N.val x
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma dgBarCompactEvaluationScalarClosedMap (x : D)
    {M N : ClosedCategory R (ProjectiveDGModules R D)} (f : M ⟶ N) :
    (moduleEvaluation R PUnit.{1} PUnit.unit).map
      ((dgBarCompactProjectiveEvaluationModuleDG R D x).onClosed.map f) =
      (moduleEvaluation R D x).map
        ((dgFullSubcategoryInclusion R (RightModule R D)
          (dgModuleProjectiveProperty R D)).onClosed.map f) := by
  have h := congrArg (fun F => F.onClosed ⋙ closedToComplex R)
    (dgBarCompactEvaluationScalarDG_eq R D x)
  have hh {F G : ClosedCategory R (ProjectiveDGModules R D) ⥤ Complex R}
      (he : F = G) : HEq (F.map f) (G.map f) := by subst G; rfl
  exact eq_of_heq (hh h)

end SerrePositivity.InfinityCategories

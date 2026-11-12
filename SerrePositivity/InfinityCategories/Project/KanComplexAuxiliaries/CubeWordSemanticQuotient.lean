module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordRealization

/-! # 生成語の意味による商と具体的立方体圏の比較
概要：同じ具体的関数を表す語を同一視した商が、元の具体的立方体圏と同値であることを示す。
方針：語評価の充満性・対象全射性と、関手の核による既存の商構成を使う。
規約：生成関係式の完全性は仮定しない。使われ方：Serre 語評価が降下すべき正確な商。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 具体的な立方体圏への語評価は本質的全射。 -/
instance cubeWordConcreteFunctor_essSurj : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.EssSurj :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.essSurj_of_surj _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor_obj_surjective

/-- 元の具体的な関数として等しい語の商。 -/
abbrev CubeWordSemanticQuotient := CategoryTheory.Quotient _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.homRel

/-- 同じ具体的な関数を表す語を同一視する関手。 -/
def cubeWordSemanticProjection : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordSemanticQuotient :=
  CategoryTheory.Quotient.functor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.homRel

/-- 生成語の意味による商から、元の具体的立方体圏への比較関手。 -/
def cubeWordSemanticComparison : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordSemanticQuotient ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube :=
  CategoryTheory.Quotient.lift _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.homRel _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor (by simp)

/-- 元の具体的関数の圏との比較は実際の圏同値。 -/
instance cubeWordSemanticComparison_isEquivalence : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticComparison.IsEquivalence := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticComparison
  infer_instance

/-- 語の商への射影と比較の合成は、元の具体的な評価を回収する。 -/
lemma cubeWordSemanticProjection_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticProjection ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticComparison = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- 意味による商での語の等号は、元の具体的な有限 max 表示の等号と同値。 -/
lemma cubeWordSemanticProjection_map_eq_iff {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords} (p q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticProjection.map p = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticProjection.map q ↔
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map p) =
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map q) := by
  exact (CategoryTheory.Quotient.functor_map_eq_iff _ p q).trans
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor_map_eq_iff_normalForm p q)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordSemanticQuotient (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordSemanticQuotient := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordSemanticQuotient

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor_essSurj (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordConcreteFunctor_essSurj := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor_essSurj

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordSemanticComparison := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticComparison_isEquivalence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordSemanticComparison_isEquivalence := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticComparison_isEquivalence

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticProjection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordSemanticProjection := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticProjection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordSemanticProjection_comparison := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticProjection_comparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordSemanticProjection_map_eq_iff := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticProjection_map_eq_iff

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordSemanticComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordSemanticComparison._proof_1

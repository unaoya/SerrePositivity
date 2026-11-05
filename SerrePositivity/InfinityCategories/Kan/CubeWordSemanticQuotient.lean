module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CubeWordRealization

/-! # 生成語の意味による商と具体的立方体圏の比較
概要：同じ具体的関数を表す語を同一視した商が、元の具体的立方体圏と同値であることを示す。
方針：語評価の充満性・対象全射性と、関手の核による既存の商構成を使う。
規約：生成関係式の完全性は仮定しない。使われ方：Serre 語評価が降下すべき正確な商。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 具体的な立方体圏への語評価は本質的全射。 -/
instance cubeWordConcreteFunctor_essSurj : cubeWordConcreteFunctor.EssSurj :=
  cubeWordConcreteFunctor.essSurj_of_surj cubeWordConcreteFunctor_obj_surjective

/-- 元の具体的な関数として等しい語の商。 -/
abbrev CubeWordSemanticQuotient := CategoryTheory.Quotient cubeWordConcreteFunctor.homRel

/-- 同じ具体的な関数を表す語を同一視する関手。 -/
def cubeWordSemanticProjection : CubeWords ⥤ CubeWordSemanticQuotient :=
  CategoryTheory.Quotient.functor cubeWordConcreteFunctor.homRel

/-- 生成語の意味による商から、元の具体的立方体圏への比較関手。 -/
def cubeWordSemanticComparison : CubeWordSemanticQuotient ⥤ ConcreteCube :=
  CategoryTheory.Quotient.lift cubeWordConcreteFunctor.homRel cubeWordConcreteFunctor (by simp)

/-- 元の具体的関数の圏との比較は実際の圏同値。 -/
instance cubeWordSemanticComparison_isEquivalence : cubeWordSemanticComparison.IsEquivalence := by
  unfold cubeWordSemanticComparison
  infer_instance

/-- 語の商への射影と比較の合成は、元の具体的な評価を回収する。 -/
lemma cubeWordSemanticProjection_comparison :
    cubeWordSemanticProjection ⋙ cubeWordSemanticComparison = cubeWordConcreteFunctor :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- 意味による商での語の等号は、元の具体的な有限 max 表示の等号と同値。 -/
lemma cubeWordSemanticProjection_map_eq_iff {X Y : CubeWords} (p q : X ⟶ Y) :
    cubeWordSemanticProjection.map p = cubeWordSemanticProjection.map q ↔
      concreteCubeNormalForm (cubeWordConcreteFunctor.map p) =
        concreteCubeNormalForm (cubeWordConcreteFunctor.map q) := by
  exact (CategoryTheory.Quotient.functor_map_eq_iff _ p q).trans
    (cubeWordConcreteFunctor_map_eq_iff_normalForm p q)

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeWordSemanticQuotient (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeWordSemanticQuotient := _root_.SerrePositivity.InfinityCategories.Kan.CubeWordSemanticQuotient

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor_essSurj (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordConcreteFunctor_essSurj := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor_essSurj

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeWordSemanticComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordSemanticComparison := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordSemanticComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeWordSemanticComparison_isEquivalence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordSemanticComparison_isEquivalence := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordSemanticComparison_isEquivalence

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeWordSemanticProjection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordSemanticProjection := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordSemanticProjection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordSemanticProjection_comparison := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordSemanticProjection_comparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordSemanticProjection_map_eq_iff := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordSemanticProjection_map_eq_iff

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordSemanticComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordSemanticComparison._proof_1

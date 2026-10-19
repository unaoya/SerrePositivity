module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalAlgebraDiagram
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGAlgebraDiagram
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalChartSquare

/-!
概要：KST v4 Def 3.1・Lemma 3.6（pp.11–14）の例外因子射を係数 dg 代数図式の自然変換にする。
方針：局所包含を共通基底環へ制限し、有限重なりの総外積上の可換式を使う。
規約：係数代数の射は幾何の閉埋め込みと反変。層・dg 加群の降下は別の比較。
使われ方：blowup と例外因子の cartesian 加群模型の間の関手。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：共通基底環上の blowup チャートから例外因子への dg 係数射。
方針：元の局所 dg 包含を構造射に沿って係数制限する。
規約：KST Lemma 3.6。使われ方：係数代数図式の自然変換の頂点成分。 -/
def finiteOverlapExceptionalBaseInclusionDGFunctor (a : I → R) (i : I) (T : Finset I) :
    DGFunctor R (FiniteOverlapBaseKoszulObject R a i T)
      (FiniteOverlapExceptionalBaseObject R a i T) :=
  restrictDGFunctor (algebraMap R (FiniteOverlapRing R i T))
    (finiteOverlapExceptionalInclusionDGFunctor R a i T)

set_option maxHeartbeats 2000000 in
-- 局所化環の dg 包含と基底環上のモノイド対象の構造射を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：有限重なりの blowup dg 代数から例外因子の dg 代数への指定射。
方針：基底制限した dg 包含の Hom 写像と単位・積保存を使う。
規約：KST Def 3.1・Lemma 3.6。使われ方：全重なりの係数代数自然変換。 -/
def finiteOverlapExceptionalDGAlgebraInclusion (a : I → R) (i : I) (T : Finset I) :
    finiteOverlapDGAlgebra R a i T ⟶ finiteOverlapExceptionalDGAlgebra R a i T :=
  Mon.Hom.mk' ((finiteOverlapExceptionalBaseInclusionDGFunctor R a i T).map .point .point)
    ((finiteOverlapExceptionalBaseInclusionDGFunctor R a i T).map_id .point)
    ((finiteOverlapExceptionalBaseInclusionDGFunctor R a i T).map_comp .point .point .point)

set_option maxHeartbeats 4000000 in
-- 二つの局所化環の dg 制限と全 Hom の成分を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子への指定 dg 代数射は有限重なり遷移と可換。
方針：Hom の各次数に戻し、指定局所射の総外積公式と基底変換の可換式を使う。
規約：KST Def 3.1・Lemma 3.6。使われ方：係数図式の自然性条件。 -/
theorem finiteOverlapExceptionalDGAlgebraInclusion_natural (a : I → R) (i k : I)
    {T U : Finset I} (h : T ⊆ U) (hi : i ∈ T) :
    finiteOverlapDGAlgebraMap R a i k h hi ≫ finiteOverlapExceptionalDGAlgebraInclusion R a k U =
      finiteOverlapExceptionalDGAlgebraInclusion R a i T ≫
        finiteOverlapExceptionalDGAlgebraMap R a i k h hi := by
  apply Mon.Hom.ext
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((finiteOverlapExceptionalBaseInclusionDGFunctor R a k U).map .point .point).f q)
      ((((finiteOverlapBaseDGTransition R a i k h hi).map .point .point).f q) z) =
    (((finiteOverlapExceptionalBaseDGTransition R a i k h hi).map .point .point).f q)
      ((((finiteOverlapExceptionalBaseInclusionDGFunctor R a i T).map .point .point).f q) z)
  rw [finiteOverlapBaseDGTransition_apply, finiteOverlapExceptionalBaseDGTransition_apply]
  change (((finiteOverlapExceptionalInclusionDGFunctor R a k U).map .point .point).f q)
      ((((finiteOverlapDGTransition R a i k h hi).map .point .point).f q) z) =
    (((finiteOverlapExceptionalDGTransition R a i k h hi).map .point .point).f q)
      ((((finiteOverlapExceptionalInclusionDGFunctor R a i T).map .point .point).f q) z)
  apply exteriorCochainInclusion_injective
    (Finsupp.linearCombination (FiniteOverlapRing R k U)
      (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R k U) (a j))
        (finiteOverlapCoordinates R k U) k)) q
  change exteriorCochainInclusion
      (Finsupp.linearCombination (FiniteOverlapRing R k U)
        (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R k U) (a j))
          (finiteOverlapCoordinates R k U) k)) q
      ((exteriorKoszulCochainMap (exceptionalChartGeneratorInclusion k) _ _ _).f q
        (((finiteOverlapDGTransition R a i k h hi).map .point .point).f q z)) =
    exteriorCochainInclusion
      (Finsupp.linearCombination (FiniteOverlapRing R k U)
        (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R k U) (a j))
          (finiteOverlapCoordinates R k U) k)) q
      (((finiteOverlapExceptionalDGTransition R a i k h hi).map .point .point).f q
        ((exteriorKoszulCochainMap (exceptionalChartGeneratorInclusion i) _ _ _).f q z))
  rw [exteriorCochainInclusion_map, finiteOverlapDGTransition_inclusion,
    finiteOverlapExceptionalDGTransition_inclusion, exteriorCochainInclusion_map]
  rw [freeExteriorScalarMap_natural (finiteOverlapChartMap R i k h hi).toRingHom
    (exceptionalChartGeneratorInclusion i) (exceptionalChartGeneratorInclusion i)
    (exceptionalChartGeneratorInclusion_scalarMap (finiteOverlapChartMap R i k h hi).toRingHom i)]
  rw [finiteOverlapChartMap_coordinates, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  exact congrArg (fun f => ExteriorAlgebra.map f
    (freeExteriorScalarMap (finiteOverlapChartMap R i k h hi).toRingHom
      (exteriorCochainInclusion (chartKoszulDifferential
        (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
        (finiteOverlapCoordinates R i T) i) q z)))
    (exceptionalTransitionEquiv_chart k i (finiteOverlapCoordinates R k U)
      (finiteOverlapUnit R k U i (h hi)) (by simp [finiteOverlapCoordinates])
      (finiteOverlapUnit_val R k U i (h hi))).symm

/-- 概要：blowup から例外因子への全有限重なりの指定係数 dg 代数自然変換。
方針：各選択 pivot の局所包含を成分とし、証明済みの遷移の可換式を使う。
規約：KST Lemma 3.6、層の閉埋め込みとの比較は別に残す。
使われ方：図式加群の制限・係数拡大と大域の例外因子関手。 -/
def finiteOverlapExceptionalDGAlgebraInclusionNatTrans (a : I → R) :
    finiteOverlapDGAlgebraDiagram R a ⟶ finiteOverlapExceptionalDGAlgebraDiagram R a where
  app T := finiteOverlapExceptionalDGAlgebraInclusion R a (finiteOverlapIndexPivot T) T.val
  naturality {T U} f := finiteOverlapExceptionalDGAlgebraInclusion_natural R a
    (finiteOverlapIndexPivot T) (finiteOverlapIndexPivot U)
    (leOfHom f) (finiteOverlapIndexPivot_mem T)

end SerrePositivity.KST.DerivedBlowup

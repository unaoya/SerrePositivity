module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalProductDiagram

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の共通 Koszul 図式の遷移を標準係数変更と同定する。
方針：指定局所同型の逆で任意の元を戻し、半線形遷移と共通表示比較の可換式を使う。
規約：共役による図式の定義だけで同定済みとはせず、全次数の元の像を証明する。
使われ方：E∩U_i の Ko(A;a)[S] 表示を通常の係数環図式として使用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 4000000 in
-- 二つの局所化環の複体同型と係数制限の全次数の像を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と共通基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：共通 Koszul 表示の指定図式遷移は標準の外積係数変更を与える。
方針：任意の元を指定局所同型の逆へ通し、共通表示比較と半線形遷移の式を使う。
規約：KST Lemma 3.6、実際の有限重なり環射に沿う全次数の同定。
使われ方：共役で構成した図式と Ko(A;a) の係数変更図式の同定。 -/
theorem finiteOverlapExceptionalProductMap_inclusion (a : I → R) (i k : I)
    {T U : Finset I} (h : T ⊆ U) (hi : i ∈ T) (q : ℤ)
    (z : (exteriorKoszulCochain (Finsupp.linearCombination (FiniteOverlapRing R i T)
      (fun j => algebraMap R (FiniteOverlapRing R i T) (a j)))).X q) :
    exteriorCochainInclusion (Finsupp.linearCombination (FiniteOverlapRing R k U)
        (fun j => algebraMap R (FiniteOverlapRing R k U) (a j))) q
        (((finiteOverlapExceptionalProductMap R a i k h hi).hom.f q) z) =
      freeExteriorScalarMap (finiteOverlapChartMap R i k h hi).toRingHom
        (exteriorCochainInclusion (Finsupp.linearCombination (FiniteOverlapRing R i T)
          (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))) q z) := by
  let e := finiteOverlapExceptionalProductIso R a i T
  let x := (e.inv.hom.f q) z
  have hx : (e.hom.hom.f q) x = z := by
    have he : e.inv.hom ≫ e.hom.hom = 𝟙 _ := congrArg Mon.Hom.hom e.inv_hom_id
    exact congrArg (fun f : (finiteOverlapExceptionalProductAlgebra R a i T).X ⟶
      (finiteOverlapExceptionalProductAlgebra R a i T).X => (f.f q) z) he
  have hx' : ExteriorAlgebra.map
      (exceptionalGeneratorMap i (finiteOverlapCoordinates R i T))
      (exteriorCochainInclusion (Finsupp.linearCombination (FiniteOverlapRing R i T)
        (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
          (finiteOverlapCoordinates R i T) i)) q x) =
      exteriorCochainInclusion (Finsupp.linearCombination (FiniteOverlapRing R i T)
        (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))) q z := by
    have hc := congrArg (exteriorCochainInclusion
      (Finsupp.linearCombination (FiniteOverlapRing R i T)
        (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))) q) hx
    change exteriorCochainInclusion (Finsupp.linearCombination (FiniteOverlapRing R i T)
        (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))) q
        ((exteriorKoszulCochainMap
          (exceptionalGeneratorMap i (finiteOverlapCoordinates R i T)) _ _
          (exceptionalGeneratorMap_differential
            (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
            (finiteOverlapCoordinates R i T) i)).f q x) = _ at hc
    rw [exteriorCochainInclusion_map] at hc
    exact hc
  change exteriorCochainInclusion (Finsupp.linearCombination (FiniteOverlapRing R k U)
      (fun j => algebraMap R (FiniteOverlapRing R k U) (a j))) q
      ((exteriorKoszulCochainMap
        (exceptionalGeneratorMap k (finiteOverlapCoordinates R k U)) _ _
        (exceptionalGeneratorMap_differential
          (fun j => algebraMap R (FiniteOverlapRing R k U) (a j))
          (finiteOverlapCoordinates R k U) k)).f q
        (((finiteOverlapExceptionalBaseDGTransition R a i k h hi).map .point .point).f q x)) = _
  rw [exteriorCochainInclusion_map, finiteOverlapExceptionalBaseDGTransition_apply,
    finiteOverlapExceptionalDGTransition_inclusion]
  have hm : (exceptionalGeneratorMap k (finiteOverlapCoordinates R k U)).comp
      (exceptionalTransitionEquiv k i (finiteOverlapCoordinates R k U)
        ((finiteOverlapChartMap R i k h hi).toRingHom ∘
          finiteOverlapCoordinates R i T)).toLinearMap =
      exceptionalGeneratorMap i
        ((finiteOverlapChartMap R i k h hi).toRingHom ∘ finiteOverlapCoordinates R i T) := by
    apply LinearMap.ext
    exact exceptionalTransitionEquiv_comparison k i (finiteOverlapCoordinates R k U) _
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hm]
  rw [← freeExteriorScalarMap_natural (finiteOverlapChartMap R i k h hi).toRingHom
    (exceptionalGeneratorMap i (finiteOverlapCoordinates R i T))
    (exceptionalGeneratorMap i
      ((finiteOverlapChartMap R i k h hi).toRingHom ∘ finiteOverlapCoordinates R i T))
    (exceptionalGeneratorMap_scalarMap (finiteOverlapChartMap R i k h hi).toRingHom
      i (finiteOverlapCoordinates R i T)), hx']

end SerrePositivity.KST.DerivedBlowup

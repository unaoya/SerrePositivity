module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaLocalUnitComparison

/-!
概要：comma fiber の任意の点からの局所比較を輸送円柱で実現する。
方針：指定三辺の合成三角形を正方形にして、固定始域の comma に戻す。
規約：始点は元の点であり、底は Y の普遍区間族そのもの。
使われ方：局所比較と普遍輸送の関手同型の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {X Y : SSet.{u}} [Quasicategory X]
variable {G : Y ⟶ X} {x : X _⦋0⦌} {y₀ : Y _⦋0⦌}

/-- 概要：局所合成正方形を固定始域のホモトピーとして読む。
方針：元の三角形から得る正方形の端点を正規化する。
規約：標的の普遍辺を保つ。
使われ方：comma 円柱の入力。 -/
def unitCommaCompositionCoherenceAt
    (v : (vertexFiber (F1B.unitCommaFiberProjection G x) y₀) _⦋0⦌)
    (y : Y _⦋0⦌) :
    SSet.Homotopy
      (SSet.const x : (Δ[1] : SSet.{u}) ⊗
        intervalMappingSpace y₀ y ⟶ X)
      (intervalMappingUncurry (𝟙 (intervalMappingSpace y₀ y)) ≫ G) where
  h := (functorSquareCoherence
    (functorSquareOfCompositionTriangle (unitIntervalCompositionTriangleAt v y))).h
  h₀ := (functorSquareCoherence
    (functorSquareOfCompositionTriangle (unitIntervalCompositionTriangleAt v y))).h₀
  h₁ := by
    have h := (functorSquareCoherence
      (functorSquareOfCompositionTriangle (unitIntervalCompositionTriangleAt v y))).h₁
    change SSet.ι₁ ≫ _ = _ at h ⊢
    apply h.trans
    change (β_ (Δ[1] : SSet.{u}) _).hom ≫
      ((β_ _ (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry
        (intervalFunctorMap G y₀ y)) = _
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
    change intervalMappingUncurry (intervalFunctorMap G _ _) =
      intervalMappingUncurry (𝟙 _) ≫ G
    simpa only [Category.id_comp] using intervalFunctorMap_uncurry
      (𝟙 (intervalMappingSpace y₀ y)) G
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：局所三角形から comma 内の円柱を構成する。
方針：正方形のホモトピーを comma に curry する。
規約：底の全区間辺を覆う。
使われ方：局所輸送比較。 -/
def unitCommaCompositionPrismAt
    (v : (vertexFiber (F1B.unitCommaFiberProjection G x) y₀) _⦋0⦌)
    (y : Y _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ intervalMappingSpace y₀ y ⟶
      unitCommaFiber G x :=
  unitCommaFiberCurry G x (intervalMappingUncurry (𝟙 _))
    (unitCommaCompositionCoherenceAt v y)

/-- 概要：局所円柱の底を計算する。
方針：comma の curry の射影公式を使う。
規約：Y の普遍区間辺と厳密に一致。
使われ方：輸送の一意性への入力。 -/
lemma unitCommaCompositionPrismAt_projection
    (v : (vertexFiber (F1B.unitCommaFiberProjection G x) y₀) _⦋0⦌)
    (y : Y _⦋0⦌) :
    unitCommaCompositionPrismAt v y ≫ F1B.unitCommaFiberProjection G x =
      intervalMappingUncurry (𝟙 (intervalMappingSpace y₀ y)) :=
  unitCommaFiberCurry_target _ _ _ _

/-- 概要：局所円柱の始点は元の comma 点に定値。
方針：標的と矢印の二成分で比較する。
規約：元の点の辺の代表を保つ。
使われ方：指定点で評価した輸送との照合。 -/
lemma unitCommaCompositionPrismAt_zero
    (v : (vertexFiber (F1B.unitCommaFiberProjection G x) y₀) _⦋0⦌)
    (y : Y _⦋0⦌) :
    prismEndpoint 0 (intervalMappingSpace y₀ y) ≫
      unitCommaCompositionPrismAt v y = SSet.const v.val := by
  dsimp only [unitCommaCompositionPrismAt]
  apply unitCommaFiber_hom_ext
  · rw [unitCommaFiberTarget_precomp, unitCommaFiberCurry_target,
      intervalFamily_zero]
    change SSet.const y₀ = (SSet.const v.val) ≫ F1B.unitCommaFiberProjection G x
    rw [SSet.const_comp]
    congr 1
    have hv : (F1B.unitCommaFiberProjection G x).app (Opposite.op ⦋0⦌) v.val = y₀ := by
      simpa only [pinchedConstant_zero] using v.property
    exact hv.symm
  · rw [unitCommaFiberHomotopy_precomp, unitCommaFiberCurry_homotopy]
    exact (functorSquareCoherence_left
      (functorSquareOfCompositionTriangle (unitIntervalCompositionTriangleAt v y))).trans
        (commaTargetFiber_constant_homotopy v)

end SerrePositivity.InfinityCategories.HomotopyLimits

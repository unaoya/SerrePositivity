module
public import SerrePositivity.KST.SConstruction.ObjectKClassInvariance
public import SerrePositivity.KST.SConstruction.KZeroPiZeroPoint
public import SerrePositivity.KST.SConstruction.SInterchangeEvaluations

/-! # 元の零対象の実際の K 類
概要：任意の零対象は、元の退化 loop により実際の BF K 群の零元を表す。
方針：零図式の S₁ 評価と零段の退化の定数 loop への厳密な式を使う。
規約：指定した零対象の選択を保つ。使われ方：三角圏 K₀ の零対象と対象類の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open Spectra
open scoped Simplicial

/-- 元の S₁ 零図式の評価は指定した元の零対象。 -/
lemma sOneComparison_zeroVertex (X : StableModel.{u}) (z : X.carrier _⦋0⦌)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) :
    (sOneComparison X.carrier).app _ (sConstructionZeroVertex 1 z hz) = z := by
  rw [sOneComparison_eq_evaluation]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X.carrier)
    (ComposableArrows.mk₀ (arObj (0 : Fin 2) 1 (by decide)))).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z : arNerve 1 ⟶ X.carrier)) = z
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  simp [SSet.const]

/-- 任意の零対象の元の K loop 類は定数 loop の成分。 -/
lemma objectKPiZeroClass_of_isZero (X : StableModel.{u}) (z : X.carrier _⦋0⦌)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) :
    objectKPiZeroClass X z = SSet.π₀.mk (boundaryKSpaceFunctor.obj X).basepoint := by
  let b := coreSConstructionZeroVertex 0 z hz
  let d := coreSConstructionZeroVertex 1 z hz
  have hd : ((iteratedSRealizationDiagram 0 X).map (SimplexCategory.σ (0 : Fin 1)).op).app
      (Opposite.op ⦋0⦌) b = d :=
    coreSMap_zeroVertex (SimplexCategory.σ (0 : Fin 1)).toOrderHom z hz
  have hl := congrArg (fun f => f.app (Opposite.op ⦋0⦌) b)
    (zeroRowLoopComparison_degeneracy 0 X)
  change (zeroRowLoopComparison 0 X).app _
    (((iteratedSRealizationDiagram 0 X).map (SimplexCategory.σ (0 : Fin 1)).op).app _ b) =
      (boundaryKSpaceFunctor.obj X).basepoint at hl
  rw [hd] at hl
  have h := objectKPiZeroClass_sOne X d
  have he : (sOneComparison X.carrier).app _ d.val = z := sOneComparison_zeroVertex X z hz
  rw [he, hl] at h
  exact h

/-- 任意の零対象は実際の加法記法の零次 BF K 群で零元を表す。 -/
lemma objectKClass_of_isZero (X : StableModel.{u}) (z : X.carrier _⦋0⦌)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) : objectKClass X z = 0 := by
  apply Additive.toMul.injective
  apply (kHomotopyZeroPiZeroEquiv X).injective
  rw [objectKClass_piZero]
  change objectKPiZeroClass X z = kHomotopyZeroPiZeroEquiv X 1
  rw [objectKPiZeroClass_of_isZero X z hz, kHomotopyZeroPiZeroEquiv_one]

end SerrePositivity.KST.SConstruction

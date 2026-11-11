module

public import SerrePositivity.KST.Spectra.SpectrumNativeCircleEvaluationFiber

/-!
概要：点ごとの円評価四角形の二つの対角頂点を、元の BF cotensor と入力へ同定する。
方針：上側の参照零三角形を全体として保持し、その両端で評価する。
規約：両零角と同じ実際の四角形を使う。使われ方：指定 cospan 上での極限性の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleSquareVerticesSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 点ごとの四角形の上側は、元の参照零三角形の同じ頂点での制限そのもの。 -/
lemma nativeCircleEvaluationSquare_upper (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ nativeCircleEvaluationSquare z =
      lift (SSet.const z) (𝟙 (Δ[2] : SSet.{u + 1})) ≫
        nativeZeroEvaluationTriangleFamily PointedSimplicialSet.circle := by
  rw [nativeCircleEvaluationSquare_evaluation, ← Category.assoc,
    circleEvaluationFunctorSquare_upper, circleZeroFunctorTriangle, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]

/-- 元の Sp 上の零三角形の終点は、選んだ逆射と源射影の合成。 -/
lemma nativeZeroEvaluationTriangleFamily_two (A : PointedSimplicialSet.{u}) :
    lift (𝟙 Sp.{u}) (SSet.const (stdSimplex.obj₀Equiv.symm (2 : Fin 3))) ≫
        nativeZeroEvaluationTriangleFamily A =
      (CotensorCompatible.sourceInfinityEquivalence A).inv ≫
        CotensorCompatible.sourceInfinityMap A := by
  rw [nativeZeroEvaluationTriangleFamily_vertex,
    CotensorCompatible.zeroEvaluationTriangleFamily_two]

/-- 点ごとの四角形の左下は、逆射が選んだ入力の実際の BF cotensor。 -/
lemma nativeCircleEvaluationSquare_source (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (nativeCircleEvaluationSquare z) 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (nativeCircleEvaluationSquare_upper z) (Opposite.op ⦋0⦌))
    (stdSimplex.obj₀Equiv.symm (0 : Fin 3))
  have hz := ConcreteCategory.congr_hom (NatTrans.congr_app
    (nativeZeroEvaluationTriangleFamily_zero PointedSimplicialSet.circle) (Opposite.op ⦋0⦌)) z
  change (nativeCircleEvaluationSquare z).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 3))) =
    (nativeZeroEvaluationTriangleFamily PointedSimplicialSet.circle).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 0, stdSimplex.obj₀Equiv.symm (0 : Fin 3)) at hu
  change (nativeZeroEvaluationTriangleFamily PointedSimplicialSet.circle).app _
      (z, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) 0) =
    (nativeCotensor PointedSimplicialSet.circle).app _ z at hz
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at hu hz
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 1} 0).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) =
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) := by
    apply Prod.ext <;> decide
  rw [hs] at hu
  exact hu.trans (hz.trans (nativeCotensor_fiber_vertex _ z))

/-- 点ごとの四角形の右上は、逆射が選んだ元の BF 入力そのもの。 -/
lemma nativeCircleEvaluationSquare_target (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (nativeCircleEvaluationSquare z) 1 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (nativeCotensorInput PointedSimplicialSet.circle z).val := by
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (nativeCircleEvaluationSquare_upper z) (Opposite.op ⦋0⦌))
    (stdSimplex.obj₀Equiv.symm (2 : Fin 3))
  have hz := ConcreteCategory.congr_hom (NatTrans.congr_app
    (nativeZeroEvaluationTriangleFamily_two PointedSimplicialSet.circle) (Opposite.op ⦋0⦌)) z
  change (nativeCircleEvaluationSquare z).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (2 : Fin 3))) =
    (nativeZeroEvaluationTriangleFamily PointedSimplicialSet.circle).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 0, stdSimplex.obj₀Equiv.symm (2 : Fin 3)) at hu
  change (nativeZeroEvaluationTriangleFamily PointedSimplicialSet.circle).app _
      (z, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) 0) = _ at hz
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at hu hz
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 1} 0).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) =
        (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) := by
    apply Prod.ext <;> decide
  rw [hs] at hu
  exact hu.trans (hz.trans (nativeCotensorEvaluationFamily_target_vertex _ z))

end SerrePositivity.KST.Spectra.OmegaSpectrum

module

public import SerrePositivity.KST.Spectra.SpectrumCircleEvaluationCompanion

/-!
概要：円の生成辺から作った二つの零三角形を、元の Sp 上の四角形の族へ貼る。
方針：関手 quasicategory 内で対角に沿う二セルの pushout を使い、全体を uncurry する。
規約：二つの三角形と零角を保持する。使われ方：cotensor Hom 比較による極限性の検査。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 円の生成辺を保持する、Sp の自己関手の quasicategory 内の四角形。 -/
def circleEvaluationFunctorSquare : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ (ihom Sp.{u}).obj Sp.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc circleZeroFunctorTriangle circleZeroCompanionTriangle
    circleZeroCompanionTriangle_diagonal.symm

/-- 四角形の上側の三角形は元の参照零三角形。 -/
lemma circleEvaluationFunctorSquare_upper :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ circleEvaluationFunctorSquare.{u} = circleZeroFunctorTriangle :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc ..

/-- 四角形の下側の三角形は、ホーン充填で構成したもう一方の零三角形。 -/
lemma circleEvaluationFunctorSquare_lower :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ circleEvaluationFunctorSquare.{u} = circleZeroCompanionTriangle :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc ..

/-- 元の Sp 上の、円の評価から作った実際の coherent な四角形の族。 -/
def nativeCircleEvaluationSquareFamily :
    Sp.{u} ⊗ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⟶ Sp.{u} :=
  uncurry circleEvaluationFunctorSquare

/-- 四角形の族の上側の三角形は、元の零三角形の族そのもの。 -/
lemma nativeCircleEvaluationSquareFamily_upper :
    (𝟙 Sp.{u} ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0) ≫ nativeCircleEvaluationSquareFamily =
      nativeZeroEvaluationTriangleFamily PointedSimplicialSet.circle := by
  change Sp.{u} ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ uncurry circleEvaluationFunctorSquare = _
  rw [← uncurry_natural_left, circleEvaluationFunctorSquare_upper,
    circleZeroFunctorTriangle, uncurry_curry]

/-- 四角形の族の下側も、選んだもう一方の零三角形の族を厳密に保持。 -/
lemma nativeCircleEvaluationSquareFamily_lower :
    (𝟙 Sp.{u} ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1) ≫ nativeCircleEvaluationSquareFamily =
      uncurry circleZeroCompanionTriangle := by
  change Sp.{u} ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ uncurry circleEvaluationFunctorSquare = _
  rw [← uncurry_natural_left, circleEvaluationFunctorSquare_lower]

/-- もう一方の零三角形の中間の図式は、参照三角形と厳密に同じ図式。 -/
lemma circleZeroCompanionTriangle_middle :
    (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 3)) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[2]) ≫
        circleZeroCompanionTriangle =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 3)) ≫ circleZeroFunctorTriangle := by
  have hs : (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 3)) :
      (Δ[0] : SSet.{u + 1}) ⟶ Δ[2]) =
        stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [hs, Category.assoc, circleZeroCompanionTriangle_initial, Category.assoc]

/-- 参照三角形の中間の自己関手は、元の定値零関手そのもの。 -/
lemma circleZeroFunctorTriangle_middle :
    (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 3)) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[2]) ≫
        circleZeroFunctorTriangle = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (constantZeroDiagram Sp.{u})) := by
  apply uncurry_injective
  rw [uncurry_natural_left, circleZeroFunctorTriangle, uncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  change (fst Sp.{u} (Δ[0] : SSet.{u + 1}) ≫
    lift (𝟙 Sp.{u}) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 3)))) ≫ _ = _
  rw [Category.assoc, nativeZeroEvaluationTriangleFamily_one]

/-- 四角形の二つの非対角頂点は、ともに実際の定値零関手に厳密一致。 -/
lemma circleEvaluationFunctorSquare_zeroCorner (i : Fin 2) :
    (SSet.const (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm i.rev) :
      (Δ[0] : SSet.{u + 1}) ⟶ Δ[1] ⊗ Δ[1]) ≫ circleEvaluationFunctorSquare =
        SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (constantZeroDiagram Sp.{u})) := by
  have hs : (SSet.const (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm i.rev) :
      (Δ[0] : SSet.{u + 1}) ⟶ Δ[1] ⊗ Δ[1]) =
        SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 3)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> apply SSet.stdSimplex.ext
    all_goals
      intro k
      fin_cases i <;> fin_cases k <;> decide
  rw [hs, Category.assoc]
  fin_cases i
  · erw [circleEvaluationFunctorSquare_upper, circleZeroFunctorTriangle_middle]
  · erw [circleEvaluationFunctorSquare_lower, circleZeroCompanionTriangle_middle,
      circleZeroFunctorTriangle_middle]

/-- 四角形の非対角の二つの自己関手は、関手 quasicategory の実際の零対象。 -/
lemma circleEvaluationFunctorSquare_zeroCorner_isZero (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (circleEvaluationFunctorSquare.{u}.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm i.rev)) := by
  have h := congrArg SSet.yonedaEquiv (circleEvaluationFunctorSquare_zeroCorner.{u} i)
  change circleEvaluationFunctorSquare.{u}.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm i.rev) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (constantZeroDiagram Sp.{u}) at h
  rw [h]
  exact (functorZeroVertex Sp.{u}).isZero

end SerrePositivity.KST.Spectra.OmegaSpectrum

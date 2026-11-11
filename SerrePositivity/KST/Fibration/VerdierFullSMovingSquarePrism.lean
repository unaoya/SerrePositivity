module
public import SerrePositivity.KST.Fibration.VerdierFullSLowerDeformationSource
public import SerrePositivity.KST.Fibration.VerdierFullSSquarePrismIso
public import SerrePositivity.KST.Fibration.VerdierFullSLowerKernelTriangle
public import SerrePositivity.KST.Fibration.QuotientSKernelFullSquareIso

/-!
概要：元の下側変形と同じ動く共有対角を持つ上側比較から、全四角柱を組み立てる。
方針：既存の四角柱貼合せを指定 Verdier 下側三角柱へ特殊化する。
規約：上側全族の実供給に条件付き。存在入力を主経路に追加せず、境界だけの一致で代用しない。
使われ方：K-6 c4 の上下全二胞体・全共有対角を保持する比較の利用側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
  (Q : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ Q = SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)))

/-- 概要：指定終端の下側が同じ最大化二胞体なら、元の下側変形を両四角形に接続できる。
方針：元の全三角柱の射を保持し、既存の端点等式だけを読み替える。
規約：元の短辺と動く対角を変更しない。
使われ方：上側全族と貼る指定下側三角柱。 -/
def verdierFullSMovingLowerPrism : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ verdierFullSTransportedSquare d) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ Q) where
  h := (verdierFullSLowerDeformation d).h
  h₀ := (verdierFullSLowerDeformation d).h₀.trans
    ((verdierFullSLowerSimplex_original d).trans
      (verdierFullSTransportedSquare_lower d).symm)
  h₁ := (verdierFullSLowerDeformation d).h₁.trans hQ.symm
  rel := by ext n t; exact False.elim t.1.2

variable
  (U : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ verdierFullSTransportedSquare d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ Q))
  (hdiag : (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ U.h =
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (verdierFullSLowerDeformation d).h)

/-- 概要：指定上側全族が元の動く対角を保つと、同じ全四角柱が得られる。
方針：元の全下側三角柱と上側全族を既存の押し出しで貼る。
規約：上側供給と厳密な全対角条件に条件付き。その存在は主張しない。
使われ方：K-6 c4 の元の全四角形から指定終端への実比較。 -/
def verdierFullSMovingSquarePrism : SSet.Homotopy (verdierFullSTransportedSquare d) Q :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHomotopyOfTriangleHomotopies U (verdierFullSMovingLowerPrism d Q hQ) hdiag

/-- 概要：同じ全四角柱の上側は供給された全三角柱そのもの。
方針：既存の貼合せの上側制限を使う。
規約：全パラメータの射の厳密な等式。
使われ方：指定上側二胞体の回収。 -/
theorem verdierFullSMovingSquarePrism_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ (Δ[1] : SSet.{u + 1})) ≫
      (verdierFullSMovingSquarePrism d Q hQ U hdiag).h = U.h :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHomotopyOfTriangleHomotopies_upper _ _ _

/-- 概要：同じ全四角柱の下側は元の実下側変形そのもの。
方針：既存の貼合せの下側制限を使う。
規約：固定下側や独立に選んだ変形に置き換えない。
使われ方：元の全二胞体とその動く共有対角の回収。 -/
theorem verdierFullSMovingSquarePrism_lower :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ (Δ[1] : SSet.{u + 1})) ≫
      (verdierFullSMovingSquarePrism d Q hQ U hdiag).h =
        (verdierFullSLowerDeformation d).h :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHomotopyOfTriangleHomotopies_lower _ _ _

variable (hU : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge U k).toTruncated)

include hU in
/-- 概要：供給上側の縦辺が可逆なら、同じ全四角柱の四頂点でも可逆。
方針：上側三頂点と元の下側三頂点で四頂点を覆い、元の全柱制限から辺を回収する。
規約：元の下側変形の恒等縦辺を使い、追加の可逆性入力を課さない。
使われ方：同じ実四角柱から全関手同型を作る。 -/
theorem verdierFullSMovingSquarePrism_pointwise :
    ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (verdierFullSMovingSquarePrism d Q hQ U hdiag) k).toTruncated := by
  have hu (a : (Δ[2] : SSet.{u + 1}) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
        (verdierFullSMovingSquarePrism d Q hQ U hdiag)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0).app (Opposite.op ⦋0⦌) a)).toTruncated := by
    have he := congrArg (fun f : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =>
      f.app (Opposite.op ⦋1⦌) (((Δ[2] : SSet.{u + 1}).σ 0 a), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge))
        (verdierFullSMovingSquarePrism_upper d Q hQ U hdiag)
    change (verdierFullSMovingSquarePrism d Q hQ U hdiag).h.app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0).app (Opposite.op ⦋1⦌) ((Δ[2] : SSet.{u + 1}).σ 0 a),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _ at he
    rw [σ_naturality_apply] at he
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr (hU a)
  have hl (a : (Δ[2] : SSet.{u + 1}) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
        (verdierFullSMovingSquarePrism d Q hQ U hdiag)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1).app (Opposite.op ⦋0⦌) a)).toTruncated := by
    have he := congrArg (fun f : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =>
      f.app (Opposite.op ⦋1⦌) (((Δ[2] : SSet.{u + 1}).σ 0 a), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge))
        (verdierFullSMovingSquarePrism_lower d Q hQ U hdiag)
    change (verdierFullSMovingSquarePrism d Q hQ U hdiag).h.app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1).app (Opposite.op ⦋1⦌) ((Δ[2] : SSet.{u + 1}).σ 0 a),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _ at he
    rw [σ_naturality_apply] at he
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr (verdierFullSLowerDeformation_pointwise d a)
  rintro ⟨k₀, k₁⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k₀
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k₁
  fin_cases i <;> fin_cases j
  · exact hu (stdSimplex.obj₀Equiv.symm 0)
  · exact hu (stdSimplex.obj₀Equiv.symm 1)
  · exact hl (stdSimplex.obj₀Equiv.symm 1)
  · exact hu (stdSimplex.obj₀Equiv.symm 2)

/-- 概要：動く対角を厳密に共有する全族に条件付きで、元の Verdier 四角形との全関手同型。
方針：元の中間対象変更の逆同型と、同じ全四角柱の実辺の同型を合成する。
規約：指定二胞体・元の下側変形を保持し、上側供給の存在は主張しない。
使われ方：K-6 c4 の全四角形比較への条件付き利用側。 -/
def verdierFullSMovingSquareIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) Q :=
  (verdierFullSSquarePrismIso d).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy _
      (verdierFullSMovingSquarePrism_pointwise d Q hQ U hdiag hU)

include hQ U hdiag hU in
/-- 概要：同じ全族の比較は元の Verdier 四角形の引き戻し性を両方向に保つ。
方針：指定全四角形の同型に既存の引き戻し移送を適用する。
規約：上側全族・全対角の厳密一致と可逆性に条件付き。
使われ方：全四角形比較の実供給後に K-6 c4 の引き戻し判定を移す。 -/
theorem verdierFullSMovingSquare_isPullback_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  ⟨fun hp => hp.of_functorIso (verdierFullSMovingSquareIso d Q hQ U hdiag hU).symm,
    fun hp => hp.of_functorIso (verdierFullSMovingSquareIso d Q hQ U hdiag hU)⟩

/-- 概要：同じ全 S• 商核四角形の下側は元の下側二胞体の最大化に厳密一致する。
方針：同じ実包含・商の標準合成二胞体へ双方を戻す。
規約：零角の同型による変更後も、全下側二胞体そのものを保持する。
使われ方：動く対角比較の終端を実商核四角形へ固定する。 -/
theorem quotientSKernelFullInfinitySquare_lower_maximalization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ quotientSKernelFullInfinitySquare d.isVerdier =
      SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) := by
  rw [quotientSKernelFullInfinitySquare, exInfinityCommSqInfinitySquare,
    kanCommSqInfinitySquare_lower_compStruct,
    verdierFullSLowerMaximalization_eq_kernelCompStruct]
  rfl

variable
  (V : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ verdierFullSTransportedSquare d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ quotientSKernelFullInfinitySquare d.isVerdier))
  (hVdiag : (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ V.h =
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (verdierFullSLowerDeformation d).h)
  (hV : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge V k).toTruncated)

/-- 概要：指定上側全族に条件付きで、元の Verdier 四角形を同じ実商核四角形へ比較する。
方針：動く対角で貼った全四角形同型と、既存の全 S• 零角輸送の逆を合成する。
規約：同じ元の商核・全二胞体を保持する。V の存在は主張しない。
使われ方：K-6 c4 の残る上側供給を受ける実商核への接続。 -/
def verdierFullSMovingKernelSquareIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))
      (quotientSKernelInfinitySquare d.inclusion d.projection) :=
  verdierFullSMovingSquareIso d (quotientSKernelFullInfinitySquare d.isVerdier)
    (quotientSKernelFullInfinitySquare_lower_maximalization d) V hVdiag hV ≪≫
      (quotientSKernelFullSquareIso d.isVerdier).symm

end SerrePositivity.KST.Fibration

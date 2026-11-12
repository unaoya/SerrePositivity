module
public import SerrePositivity.KST.Fibration.VerdierReadoutBoundaryTriangles
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary

/-!
概要：元の二つの指定境界二単体を、区間境界上の一つの実全図式へ貼る。
方針：同じ単位合成二単体を選び、既存の二端点図式で全次数を同時に回収する。
規約：Ind-S (9) や厳密切断に依存しない。内部への延長はまだ主張しない。
使われ方：K-6 c4 の境界を固定した長 Hom 合成への実境界入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
  (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
    (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
  (hL : VerdierLowerNativeReadoutRecovery d L)
  (hfull : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      verdierLowerReconstructionCompositeFamily d Δ[1])

private theorem nativeBoundaryMap_exists
    {a b c : (verdierNativeLongHomTarget d) _⦋0⦌}
    (l : (verdierNativeLongHomTarget d).Edge a b)
    (r : (verdierNativeLongHomTarget d).Edge b c)
    (z : (verdierNativeLongHomTarget d) _⦋1⦌)
    (h : ∃ e : (verdierNativeLongHomTarget d).Edge a c,
      ∃ _T : SSet.Edge.CompStruct l r e, e.edge = z) :
    ∃ F : (Δ[2] : SSet.{u + 1}) ⟶ verdierNativeLongHomTarget d,
      stdSimplex.δ (0 : Fin 3) ≫ F = SSet.yonedaEquiv.symm r.edge ∧
      stdSimplex.δ (2 : Fin 3) ≫ F = SSet.yonedaEquiv.symm l.edge ∧
      stdSimplex.δ (1 : Fin 3) ≫ F = SSet.yonedaEquiv.symm z := by
  obtain ⟨e, T, hz⟩ := h
  refine ⟨SSet.yonedaEquiv.symm T.simplex, ?_, ?_, ?_⟩
  all_goals rw [stdSimplex.δ_comp_yonedaEquiv_symm]
  · exact congrArg SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.d₀ T)
  · exact congrArg SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.d₂ T)
  · exact congrArg SSet.yonedaEquiv.symm ((SSet.Edge.CompStruct.d₁ T).trans hz)

/-- 概要：同じ直接端 境界二単体を三つの実指定辺とともに取り出す。
方針：既存の同じ合成二単体から全二単体写像と三面を同時に得る。
規約：同じ実辺を保持し、再構成供給の仮定を使わない。
使われ方：全境界図式の指定端点。 -/
theorem verdierReadoutDirectBoundaryMap_exists :
    ∃ F : (Δ[2] : SSet.{u + 1}) ⟶ verdierNativeLongHomTarget d,
      stdSimplex.δ (0 : Fin 3) ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
          (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}))).edge ∧
      stdSimplex.δ (2 : Fin 3) ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
          (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}))).edge ∧
      stdSimplex.δ (1 : Fin 3) ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
          (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}))).edge :=
  nativeBoundaryMap_exists d
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
          (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u})))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
          (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u})))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
          (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}))).edge
    (verdierReadoutDirectBoundaryTriangle_exists d L hL)

/-- 概要：三つの実指定辺を持つ同じ直接端 境界図式。
方針：三面回収を含む同じ存在証拠の写像を使う。
規約：面の照合の間に実図式を変更しない。
使われ方：二端点を同時に持つ全境界図式。 -/
def verdierReadoutDirectBoundaryMap :
    (Δ[2] : SSet.{u + 1}) ⟶ verdierNativeLongHomTarget d :=
  (verdierReadoutDirectBoundaryMap_exists d L hL).choose

/-- 概要：同じ直接端 境界図式の面 0 を元の実成分へ戻す。
方針：写像と同時に供給された三面の同じ回収式を使う。
規約：実一単体の厳密等式を保持する。
使われ方：全境界図式の面適合条件。 -/
theorem verdierReadoutDirectBoundaryMap_last :
    stdSimplex.δ (0 : Fin 3) ≫ verdierReadoutDirectBoundaryMap d L hL =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
          (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}))).edge :=
  (verdierReadoutDirectBoundaryMap_exists d L hL).choose_spec.1

/-- 概要：同じ直接端 境界図式の面 2 を元の実成分へ戻す。
方針：写像と同時に供給された三面の同じ回収式を使う。
規約：実一単体の厳密等式を保持する。
使われ方：全境界図式の面適合条件。 -/
theorem verdierReadoutDirectBoundaryMap_first :
    stdSimplex.δ (2 : Fin 3) ≫ verdierReadoutDirectBoundaryMap d L hL =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
          (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}))).edge :=
  (verdierReadoutDirectBoundaryMap_exists d L hL).choose_spec.2.1

/-- 概要：同じ直接端 境界図式の面 1 を元の実成分へ戻す。
方針：写像と同時に供給された三面の同じ回収式を使う。
規約：実一単体の厳密等式を保持する。
使われ方：全境界図式の面適合条件。 -/
theorem verdierReadoutDirectBoundaryMap_long :
    stdSimplex.δ (1 : Fin 3) ≫ verdierReadoutDirectBoundaryMap d L hL =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
          (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}))).edge :=
  (verdierReadoutDirectBoundaryMap_exists d L hL).choose_spec.2.2

include hfull in
/-- 概要：同じ合成端 境界二単体を三つの実指定辺とともに取り出す。
方針：既存の同じ合成二単体から全二単体写像と三面を同時に得る。
規約：同じ実辺を保持し、再構成供給の仮定を使わない。
使われ方：全境界図式の指定端点。 -/
theorem verdierReadoutFullBoundaryMap_exists :
    ∃ F : (Δ[2] : SSet.{u + 1}) ⟶ verdierNativeLongHomTarget d,
      stdSimplex.δ (0 : Fin 3) ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
          (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u}))).edge ∧
      stdSimplex.δ (2 : Fin 3) ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
          (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u}))).edge ∧
      stdSimplex.δ (1 : Fin 3) ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
          (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u}))).edge := by
  obtain ⟨e, T, hz⟩ := verdierReadoutFullBoundaryTriangle_exists d L hL hfull
  refine ⟨SSet.yonedaEquiv.symm T.simplex, ?_, ?_, ?_⟩
  all_goals rw [stdSimplex.δ_comp_yonedaEquiv_symm]
  · exact congrArg SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.d₀ T)
  · exact congrArg SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.d₂ T)
  · exact congrArg SSet.yonedaEquiv.symm ((SSet.Edge.CompStruct.d₁ T).trans hz)

/-- 概要：三つの実指定辺を持つ同じ合成端 境界図式。
方針：三面回収を含む同じ存在証拠の写像を使う。
規約：面の照合の間に実図式を変更しない。
使われ方：二端点を同時に持つ全境界図式。 -/
def verdierReadoutFullBoundaryMap :
    (Δ[2] : SSet.{u + 1}) ⟶ verdierNativeLongHomTarget d :=
  (verdierReadoutFullBoundaryMap_exists d L hL hfull).choose

/-- 概要：同じ合成端 境界図式の面 0 を元の実成分へ戻す。
方針：写像と同時に供給された三面の同じ回収式を使う。
規約：実一単体の厳密等式を保持する。
使われ方：全境界図式の面適合条件。 -/
theorem verdierReadoutFullBoundaryMap_last :
    stdSimplex.δ (0 : Fin 3) ≫ verdierReadoutFullBoundaryMap d L hL hfull =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
          (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u}))).edge :=
  (verdierReadoutFullBoundaryMap_exists d L hL hfull).choose_spec.1

/-- 概要：同じ合成端 境界図式の面 2 を元の実成分へ戻す。
方針：写像と同時に供給された三面の同じ回収式を使う。
規約：実一単体の厳密等式を保持する。
使われ方：全境界図式の面適合条件。 -/
theorem verdierReadoutFullBoundaryMap_first :
    stdSimplex.δ (2 : Fin 3) ≫ verdierReadoutFullBoundaryMap d L hL hfull =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
          (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u}))).edge :=
  (verdierReadoutFullBoundaryMap_exists d L hL hfull).choose_spec.2.1

/-- 概要：同じ合成端 境界図式の面 1 を元の実成分へ戻す。
方針：写像と同時に供給された三面の同じ回収式を使う。
規約：実一単体の厳密等式を保持する。
使われ方：全境界図式の面適合条件。 -/
theorem verdierReadoutFullBoundaryMap_long :
    stdSimplex.δ (1 : Fin 3) ≫ verdierReadoutFullBoundaryMap d L hL hfull =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
          (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u}))).edge :=
  (verdierReadoutFullBoundaryMap_exists d L hL hfull).choose_spec.2.2

/-- 概要：二つの実境界二単体を区間境界上の全図式にする。
方針：同じ二写像を既存の境界図式へ代入する。
規約：各頂点だけでなく全単体の図式を返す。
使われ方：境界を固定した合成二単体族の延長入力。 -/
def verdierReadoutBoundaryDiagram :
    (boundary 1 : SSet.{u + 1}) ⊗ Δ[2] ⟶ verdierNativeLongHomTarget d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (verdierReadoutDirectBoundaryMap d L hL)
    (verdierReadoutFullBoundaryMap d L hL hfull)

/-- 概要：同じ境界図式の零端は元の直接端二単体そのもの。
方針：既存の境界図式の零端回収を適用する。
規約：実全図式の厳密等式。
使われ方：指定した直接端境界の照合。 -/
theorem verdierReadoutBoundaryDiagram_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 Δ[2] ≫ verdierReadoutBoundaryDiagram d L hL hfull =
      verdierReadoutDirectBoundaryMap d L hL :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero _ _

/-- 概要：同じ境界図式の一端は元の合成端二単体そのもの。
方針：既存の境界図式の一端回収を適用する。
規約：実全図式の厳密等式。
使われ方：指定した合成端境界の照合。 -/
theorem verdierReadoutBoundaryDiagram_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 Δ[2] ≫ verdierReadoutBoundaryDiagram d L hL hfull =
      verdierReadoutFullBoundaryMap d L hL hfull :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one _ _

/-- 概要：全境界図式の面 0 は同じ元の二つの境界成分の全図式。
方針：境界図式の自然性と同じ二単体の面回収を合成する。
規約：全次数の実写像の等式。点ごとの照合で代用しない。
使われ方：指定境界を保つ合成二単体族への面適合条件。 -/
theorem verdierReadoutBoundaryDiagram_last :
    ((boundary 1 : SSet.{u + 1}) ◁ stdSimplex.δ (0 : Fin 3)) ≫
      verdierReadoutBoundaryDiagram d L hL hfull =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram
        (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
            (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath))).edge)
        (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
            (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath))).edge) := by
  rw [verdierReadoutBoundaryDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality,
    verdierReadoutDirectBoundaryMap_last, verdierReadoutFullBoundaryMap_last]

/-- 概要：全境界図式の面 2 は同じ元の二つの境界成分の全図式。
方針：境界図式の自然性と同じ二単体の面回収を合成する。
規約：全次数の実写像の等式。点ごとの照合で代用しない。
使われ方：指定境界を保つ合成二単体族への面適合条件。 -/
theorem verdierReadoutBoundaryDiagram_first :
    ((boundary 1 : SSet.{u + 1}) ◁ stdSimplex.δ (2 : Fin 3)) ≫
      verdierReadoutBoundaryDiagram d L hL hfull =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram
        (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
            (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath))).edge)
        (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
            (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath))).edge) := by
  rw [verdierReadoutBoundaryDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality,
    verdierReadoutDirectBoundaryMap_first, verdierReadoutFullBoundaryMap_first]

/-- 概要：全境界図式の面 1 は同じ元の二つの境界成分の全図式。
方針：境界図式の自然性と同じ二単体の面回収を合成する。
規約：全次数の実写像の等式。点ごとの照合で代用しない。
使われ方：指定境界を保つ合成二単体族への面適合条件。 -/
theorem verdierReadoutBoundaryDiagram_long :
    ((boundary 1 : SSet.{u + 1}) ◁ stdSimplex.δ (1 : Fin 3)) ≫
      verdierReadoutBoundaryDiagram d L hL hfull =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram
        (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
            (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath))).edge)
        (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d)
            (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath))).edge) := by
  rw [verdierReadoutBoundaryDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality,
    verdierReadoutDirectBoundaryMap_long, verdierReadoutFullBoundaryMap_long]

end SerrePositivity.KST.Fibration

module
public import SerrePositivity.KST.NonConnective.DGKappaNativeBFOneStage
public import SerrePositivity.KST.NonConnective.DGKappaNativeStructure

/-!
概要：一回の未完備 S• fibration と同じ cone の零性から、固定 K の実構造辺を作る。
方針：元の実 fiber 比較を同じ実 loop 同型へ送り、元の P・Yoneda 比較で固定 K へ戻す。
規約：有限 BF・共終性・一回の S• 比較に条件付き。全段の Sp 引き戻し性は要求しない。
使われ方：K-7 c5・d3 の採用済み連結主経路。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance nativeBFConnectiveSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance nativeBFConnectiveHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (hBF : dgKappaNativeBFSquareComparison R D I)

private theorem nativeBFCanonicalFiber_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (dgKappaNativeBFCanonicalFiberSquare R D I hBF).square =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgKappaNativeBFSquare R D I hBF := by
  rw [(dgKappaNativeBFCanonicalFiberSquare R D I hBF).right_edge, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge]
  exact SSet.yonedaEquiv.symm_apply_apply _

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
  (Z : DGKappaZeroInput R D I)

/-- 概要：同じ元の実 fiber は同じ未完備実商 K の loop 四角形。
方針：元の右辺・零角を保つ実極限錐と同じ実 cone の K 零性を使う。
規約：有限 BF と共終性に条件付き。元の BF 四角形の引き戻し性は仮定しない。
使われ方：元の実 fiber 比較を同じ未完備実商の loop へ送る。 -/
def dgKappaNativeBFConnectiveLoopSquare :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
      (stableCategoryModel (dgKappaNativeSuspensionCategory R D I)))) where
  toZeroTriangle := (dgKappaNativeBFCanonicalFiberSquare R D I hBF).toZeroTriangle
  target_eq := by
    have ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaNativeBFCanonicalFiberSquare R D I hBF).square 1 1 =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaNativeBFSquare R D I hBF) 1 1 := by
      rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target, nativeBFCanonicalFiber_right, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target]
    exact ht.trans (dgKappaNativeBFSquare_target R D I hBF)
  other_zero := by
    have hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaNativeBFCanonicalFiberSquare R D I hBF).square 1 0 =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaNativeBFSquare R D I hBF) 1 0 := by
      rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source, nativeBFCanonicalFiber_right, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source]
    rw [hs, dgKappaNativeBFSquare_middle]
    exact dgKappaNativeResolvedConeK_isZeroVertex R D I hcofinal Z
  isPullback := (dgKappaNativeBFCanonicalFiberSquare R D I hBF).isPullback

/-- 概要：同じ実 fiber の loop 比較同型の逆を表す元の実辺。
方針：同じ Sp 正本の比較同型の逆の代表辺を取る。
規約：全 S• や固定 K の Sp 引き戻し性は仮定しない。
使われ方：元の実未完備比較に後合成する可逆辺。 -/
def dgKappaNativeBFConnectiveLoopInverseEdge :
    Truncated.Edge (X := (truncation 2).obj Sp.{max (u + 1) v})
      (dgKappaNativeBFConnectiveLoopSquare R D I hBF hcofinal Z).vertex
      ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
          (stableCategoryModel (dgKappaNativeSuspensionCategory R D I))))) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _
    (OmegaSpectrum.nativeLoopVertexIso
      (dgKappaNativeBFConnectiveLoopSquare R D I hBF hcofinal Z)).inv)

/-- 概要：同じ元の逆比較辺は実 loop 比較同型の逆を表す。
方針：同じ代表辺の選択仕様を回収する。
規約：元の実 fiber と同じ比較同型を保持する。
使われ方：同じ実構造辺の非負次数判定。 -/
theorem dgKappaNativeBFConnectiveLoopInverseEdge_hom :
    Truncated.HomotopyCategory.homMk
      (dgKappaNativeBFConnectiveLoopInverseEdge R D I hBF hcofinal Z) =
        (OmegaSpectrum.nativeLoopVertexIso
          (dgKappaNativeBFConnectiveLoopSquare R D I hBF hcofinal Z)).inv :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ _)

/-- 概要：元の実 fiber 比較を経る、同じ未完備実核 K から実商の loop への実辺。
方針：同じ全比較辺に同じ実 loop 比較同型の逆辺を後合成する。
規約：別の fibration 辺の存在は仮定しない。
使われ方：固定 K への元の完備化比較の前の実辺。 -/
def dgKappaNativeBFConnectiveFibrationEdge : Sp.{max (u + 1) v}.Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
      (stableCategoryModel (dgKappaNativeKernelCategory R D I))))
    ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
        (stableCategoryModel (dgKappaNativeSuspensionCategory R D I))))) :=
  SSet.Edge.ofTruncated
    ((dgKappaNativeBFFiberVertexComparison R D I hBF).toTruncated.comp
      (dgKappaNativeBFConnectiveLoopInverseEdge R D I hBF hcofinal Z))

/-- 概要：一回の S• fibration に条件付きで、同じ実未完備構造辺は非負次数 π 同型。
方針：同じ実 fiber 比較の非負次数同型と元の実 loop 同型を合成する。
規約：全段の Sp 引き戻し性や零次全射性は要求しない。
使われ方：K-7 c5・d3 の連結主経路の隣接安定化。 -/
theorem dgKappaNativeBFConnectiveFibrationEdge_nonnegative
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaNativeBFConnectiveFibrationEdge R D I hBF hcofinal Z).toTruncated) j) := by
  let a := (dgKappaNativeBFFiberVertexComparison R D I hBF).toTruncated
  let b := dgKappaNativeBFConnectiveLoopInverseEdge R D I hBF hcofinal Z
  have hb : IsIso (Truncated.HomotopyCategory.homMk b) := by
    rw [show Truncated.HomotopyCategory.homMk b = _ from
      dgKappaNativeBFConnectiveLoopInverseEdge_hom R D I hBF hcofinal Z]
    infer_instance
  have hbj : Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk b) j) :=
    ConcreteCategory.bijective_of_isIso ((SpectrumHo.piFunctor j).map
      (Truncated.HomotopyCategory.homMk b))
  change Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk (a.comp b)) j)
  rw [← Truncated.HomotopyCategory.homMk_comp_homMk (a.compStruct b), SpectrumHo.piMap_comp]
  exact hbj.comp (dgKappaNativeBFFiberVertexComparison_nonnegative R D I hBF hS j hj)

/-- 概要：同じ実 fiber を経る元の固定 K の実構造辺。
方針：同じ未完備実比較を元の P・Yoneda 比較に挟む。
規約：有限 BF と共終性に条件付き。固定 S・ν・K と同じ I を保持する。
使われ方：K-7 c5 の元の反復列への実構造辺。 -/
def dgKappaNativeBFConnectiveFixedStructureEdge :=
  dgKappaNativeStructureEdge R D I
    (dgKappaNativeBFConnectiveFibrationEdge R D I hBF hcofinal Z)

/-- 概要：同じ実構造射は、一回の S• fibration に条件付きで非負次数 π 同型。
方針：同じ連結比較と元の Yoneda 完備化の loop の非負次数比較を合成する。
規約：全段の Sp 引き戻し性は仮定しない。未供給の fibration と供給命題は明示する。
使われ方：K-7 d3 の同じ実余錐への連結比較。 -/
theorem dgKappaNativeBFConnectiveFixedStructureMap_nonnegative
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaNativeStructureMap R D I
      (dgKappaNativeBFConnectiveFibrationEdge R D I hBF hcofinal Z)) j) :=
  dgKappaNativeStructureMap_nonnegative R D I _ hcofinal
    (fun k hk => dgKappaNativeBFConnectiveFibrationEdge_nonnegative R D I hBF hcofinal Z hS k hk) j hj

end SerrePositivity.KST.NonConnective

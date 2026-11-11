module
public import SerrePositivity.KST.NonConnective.DGKappaSuppliedBFVertexComparison
public import SerrePositivity.KST.NonConnective.DGKappaNativeStructure

/-!
概要：実供給の新 BF 構造辺を、採用済み二頂点比較で同じ固定 K へ戻す。
方針：元の実核比較と実商の逆 loop 比較を前後に合成し、元の P・Yoneda 比較を続ける。
規約：I・Z・共終性・一回の S• fibration に条件付き。全入力自然性は主張しない。
使われ方：K-7 c5・d3 の固定 K の実構造辺と非負次数比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance suppliedBFFixedCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance suppliedBFFixedHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：元の実核 K から新 BF 全錐始点へ入る同じ指定同型の代表辺。
方針：二頂点比較の始点同型の順方向を表す実辺を選ぶ。
規約：K-S• の同じ実供給同型を使う。
使われ方：元の固定 K 構造辺の前の実 fibration 始点。 -/
def dgKappaSuppliedBFSourceEdge :
    Truncated.Edge (X := (truncation 2).obj Sp.{max (u + 1) v})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
        (stableCategoryModel (dgKappaNativeKernelCategory R D I))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (dgKappaNativeCoherentBFSquare R D I)).vertex :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _
    (dgKappaSuppliedBFSourceIso R D I).hom)

/-- 概要：同じ実始点辺は指定された二頂点同型を表す。
方針：代表辺の同じ選択仕様を回収する。
規約：別の同型へ選び直さない。
使われ方：全整数 π の可逆性を保持する。 -/
theorem dgKappaSuppliedBFSourceEdge_hom :
    Truncated.HomotopyCategory.homMk (dgKappaSuppliedBFSourceEdge R D I) =
      (dgKappaSuppliedBFSourceIso R D I).hom :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ _)

/-- 概要：同じ新 BF 商 loop から旧実商 K の loop へ戻る指定同型。
方針：実商頂点比較の逆を同じ nativeLoop に送る。
規約：loop の対象や実商を選び直さない。
使われ方：元の Yoneda 完備化 loop 比較の前の戻し。 -/
def dgKappaSuppliedBFLoopTargetBackIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (dgKappaSuppliedBFTargetIso R D I).symm
    OmegaSpectrum.nativeLoop.{max (u + 1) v}

/-- 概要：同じ実商 loop の逆比較を表す実辺。
方針：同じ nativeLoop の同型の順方向を代表辺へ戻す。
規約：公開済みの同じ実商頂点同型を使う。
使われ方：新 BF 上の構造辺を旧 K の実辺へ戻す後辺。 -/
def dgKappaSuppliedBFLoopTargetBackEdge :
    Truncated.Edge (X := (truncation 2).obj Sp.{max (u + 1) v})
      ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaNativeCoherentBFSquare R D I) 1 1))
      ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
          (stableCategoryModel (dgKappaNativeSuspensionCategory R D I))))) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _
    (dgKappaSuppliedBFLoopTargetBackIso R D I).hom)

/-- 概要：同じ loop の実後辺は指定された逆比較同型を表す。
方針：同じ代表辺の選択仕様を使う。
規約：元の実商の loop 同型を保持する。
使われ方：全整数 π の可逆性を同じ実辺で使う。 -/
theorem dgKappaSuppliedBFLoopTargetBackEdge_hom :
    Truncated.HomotopyCategory.homMk (dgKappaSuppliedBFLoopTargetBackEdge R D I) =
      (dgKappaSuppliedBFLoopTargetBackIso R D I).hom :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ _)

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
  (Z : DGKappaZeroInput R D I)

/-- 概要：元の旧実核 K から旧実商 K の loop への同じ実 fibration 辺。
方針：実供給構造辺に同じ二頂点比較を前後から合成する。
規約：I・Z・共終性に条件付き。旧右辺の fiber 同定は主張しない。
使われ方：固定 K への元の P・Yoneda 比較へ入る実辺。 -/
def dgKappaSuppliedBFOldFibrationEdge : Sp.{max (u + 1) v}.Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
      (stableCategoryModel (dgKappaNativeKernelCategory R D I))))
    ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
        (stableCategoryModel (dgKappaNativeSuspensionCategory R D I))))) :=
  SSet.Edge.ofTruncated
    (((dgKappaSuppliedBFSourceEdge R D I).comp
      (dgKappaSuppliedBFConnectiveFibrationEdge R D I hcofinal Z).toTruncated).comp
        (dgKappaSuppliedBFLoopTargetBackEdge R D I))

/-- 概要：同じ旧二頂点間の実 fibration 辺は一回の S• 比較で非負次数 π 同型。
方針：実供給構造辺の同型性に、同じ二つの実同型辺の全整数可逆性を続ける。
規約：共終性と同じ未完備 S• 比較に条件付き。全段の Sp 引き戻し性は使わない。
使われ方：固定 K の構造射の非負次数比較。 -/
theorem dgKappaSuppliedBFOldFibrationEdge_nonnegative
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaSuppliedBFOldFibrationEdge R D I hcofinal Z).toTruncated) j) := by
  let a := dgKappaSuppliedBFSourceEdge R D I
  let b := (dgKappaSuppliedBFConnectiveFibrationEdge R D I hcofinal Z).toTruncated
  let c := dgKappaSuppliedBFLoopTargetBackEdge R D I
  have ha : IsIso (Truncated.HomotopyCategory.homMk a) := by
    rw [show Truncated.HomotopyCategory.homMk a = _ from
      dgKappaSuppliedBFSourceEdge_hom R D I]
    infer_instance
  have hc : IsIso (Truncated.HomotopyCategory.homMk c) := by
    rw [show Truncated.HomotopyCategory.homMk c = _ from
      dgKappaSuppliedBFLoopTargetBackEdge_hom R D I]
    infer_instance
  have haj := ConcreteCategory.bijective_of_isIso
    ((SpectrumHo.piFunctor j).map (Truncated.HomotopyCategory.homMk a))
  have hcj := ConcreteCategory.bijective_of_isIso
    ((SpectrumHo.piFunctor j).map (Truncated.HomotopyCategory.homMk c))
  change Function.Bijective (SpectrumHo.piMap
    (Truncated.HomotopyCategory.homMk ((a.comp b).comp c)) j)
  rw [← Truncated.HomotopyCategory.homMk_comp_homMk ((a.comp b).compStruct c),
    SpectrumHo.piMap_comp,
    ← Truncated.HomotopyCategory.homMk_comp_homMk (a.compStruct b), SpectrumHo.piMap_comp]
  exact hcj.comp ((dgKappaSuppliedBFConnectiveFibrationEdge_nonnegative
    R D I hcofinal Z hS j hj).comp haj)

/-- 概要：同じ実供給と二頂点比較から元の固定 K の実構造辺を作る。
方針：旧実二頂点へ戻した同じ辺を元の P・Yoneda 比較へ渡す。
規約：供給命題は明示引数で、固定 S・ν・K と同じ I を保持する。
使われ方：反復懸垂列の同じ固定 K の隣接辺。 -/
def dgKappaSuppliedBFFixedStructureEdge :=
  dgKappaNativeStructureEdge R D I
    (dgKappaSuppliedBFOldFibrationEdge R D I hcofinal Z)

/-- 概要：同じ固定 K の実構造射は一回の S• fibration に条件付きで非負次数 π 同型。
方針：元の旧二頂点の実 fibration 比較を既存の固定 K 比較へ渡す。
規約：共終性と同じ未完備 S• 比較に条件付きで、全入力自然性は主張しない。
使われ方：K-7 d3 の同じ逐次列と連結比較への代入。 -/
theorem dgKappaSuppliedBFFixedStructureMap_nonnegative
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaNativeStructureMap R D I
      (dgKappaSuppliedBFOldFibrationEdge R D I hcofinal Z)) j) :=
  dgKappaNativeStructureMap_nonnegative R D I _ hcofinal
    (dgKappaSuppliedBFOldFibrationEdge_nonnegative R D I hcofinal Z hS) j hj

end SerrePositivity.KST.NonConnective

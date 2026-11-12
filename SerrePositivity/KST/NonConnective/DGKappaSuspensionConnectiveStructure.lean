module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionConnectiveLoop
public import SerrePositivity.KST.LocalizingInvariants.SpectrumEdgePi
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
概要：連結版の元の実 fiber 比較を、同じ平坦懸垂の固定 native loop 構造射へ送る。
方針：同じ実 loop の比較同型だけを後合成し、各整数 π の全単射性をそのまま移送する。
規約：実四角形・零角・cone の K 零性に条件付き。Sp 引き戻し性と ν の Verdier 認証は使わない。
使われ方：K-7 c5 と d。非負次数の連結 fibration が供給する比較を元の構造射へ接続する。
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
open SerrePositivity.KST.Fibration SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance connectiveStructureSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance connectiveStructureSpectrumHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v)) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (Z : DGKappaZeroInput R D I)
  (F : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶
    dgKInputInfinity.{u, max (u + 1) v} R)
  (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (F ≫ dgKInputK R) 0 1))
  (hMiddle : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaResolvedConeKInput R D I))
  (hRight : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R D I))


/-- 明示四角形に条件付きで、同じ実 loop から固定 native loop への逆比較を実辺で表す。 -/
def dgKappaSuspensionConnectiveLoopInverseEdge :
    Truncated.Edge (X := (truncation 2).obj Sp.{max (u + 1) v})
      (dgKappaSuspensionConnectiveLoopSquare R D I Z F hz hMiddle hRight).vertex
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaSuspensionKInput R D I)))) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _
    (OmegaSpectrum.nativeLoopVertexIso
      (dgKappaSuspensionConnectiveLoopSquare R D I Z F hz hMiddle hRight)).inv)

/-- 明示四角形に条件付きで、同じ逆比較辺は実 native loop 同型の逆を表す。 -/
theorem dgKappaSuspensionConnectiveLoopInverseEdge_hom :
    Truncated.HomotopyCategory.homMk
      (dgKappaSuspensionConnectiveLoopInverseEdge R D I Z F hz hMiddle hRight) =
        (OmegaSpectrum.nativeLoopVertexIso
          (dgKappaSuspensionConnectiveLoopSquare R D I Z F hz hMiddle hRight)).inv :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ _)

variable (A : PerfDGInput.{u, max (u + 1) v} R)
  (hLeft : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)

/-- 明示四角形に条件付きで、元の固定 K 核から同じ懸垂の native loop への実構造辺。 -/
def dgKappaSuspensionConnectiveStructureEdge :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R A))
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaSuspensionKInput R D I)))) :=
  SSet.Edge.ofTruncated
    ((dgKappaSuspensionConnectiveLoopComparison R D I Z F hz hMiddle hRight A hLeft).toTruncated.comp
      (dgKappaSuspensionConnectiveLoopInverseEdge R D I Z F hz hMiddle hRight))

/-- 明示四角形に条件付きで、同じ全構造辺を表す実 BF 射。 -/
def dgKappaSuspensionConnectiveStructureMap :=
  SpectrumHo.edgeMap
    (dgKappaSuspensionConnectiveStructureEdge R D I Z F hz hMiddle hRight A hLeft)

/-- 明示四角形に条件付きで、元の実 BF 構造射は同じ構造辺の全一単体を保持する。 -/
theorem dgKappaSuspensionConnectiveStructureMap_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (dgKappaSuspensionConnectiveStructureMap R D I Z F hz hMiddle hRight A hLeft)).edge =
        (dgKappaSuspensionConnectiveStructureEdge R D I Z F hz hMiddle hRight A hLeft).edge :=
  SpectrumHo.edgeMap_edge _

/-- 明示四角形に条件付きで、構造射の指定次数の全単射性は、同じ実 fiber 比較の全単射性と同値。 -/
theorem dgKappaSuspensionConnectiveStructureMap_bijective_iff (j : ℤ) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgKappaSuspensionConnectiveStructureMap R D I Z F hz hMiddle hRight A hLeft) j) ↔
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaSuspensionConnectiveLoopComparison R D I Z F hz hMiddle hRight A hLeft).toTruncated) j) := by
  let f := (dgKappaSuspensionConnectiveLoopComparison R D I Z F hz hMiddle hRight A hLeft).toTruncated
  let g := dgKappaSuspensionConnectiveLoopInverseEdge R D I Z F hz hMiddle hRight
  letI : IsIso (Truncated.HomotopyCategory.homMk g) := by
    change IsIso (Truncated.HomotopyCategory.homMk
      (dgKappaSuspensionConnectiveLoopInverseEdge R D I Z F hz hMiddle hRight))
    rw [dgKappaSuspensionConnectiveLoopInverseEdge_hom]
    infer_instance
  have hg : Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk g) j) :=
    ConcreteCategory.bijective_of_isIso
      ((SpectrumHo.piFunctor j).map (Truncated.HomotopyCategory.homMk g))
  rw [dgKappaSuspensionConnectiveStructureMap, ← SpectrumHo.piMap_edge]
  change Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk (f.comp g)) j) ↔ _
  rw [← Truncated.HomotopyCategory.homMk_comp_homMk (f.compStruct g), SpectrumHo.piMap_comp]
  exact hg.of_comp_iff' _

end SerrePositivity.KST.NonConnective

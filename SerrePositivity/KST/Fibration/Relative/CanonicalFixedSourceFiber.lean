module
public import SerrePositivity.KST.Fibration.Relative.CanonicalSingleStageDetection
public import SerrePositivity.KST.NonConnective.DGKappaSuppliedBFFixedStructure

/-!
概要：同じ実供給 BF fiber 比較の始点を元の固定 K(D) へ戻す。
方針：元の実核 K 比較と指定 Sp 頂点同型を、同じ全錐比較の前に合成する。
規約：c5 の標準単体比較だけを残す。実供給右辺の fiber を保持する。
使われ方：K-6 d の固定始点を持つ実比較と、K-B3 への非負次数 π 同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.NonConnective
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative
local instance canonicalFixedSourceSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance canonicalFixedSourceHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：元の固定 K(D) から同じ実供給右辺の Sp fiber への実比較辺。
方針：同じ実核への BF 射・供給済み始点同型・元の実 fiber 比較を合成する。
規約：群の抽象同型から実辺を作らず、商側の fixed K への輸送は主張しない。
使われ方：d の始点を元の固定 K に保った非負次数判定。 -/
def dgKappaCanonicalFixedSourceFiberComparison :
    Sp.{max (u + 1) v}.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R D))
      (dgKappaSuppliedBFKLimitCone R D I).vertex :=
  SSet.Edge.ofTruncated
    ((((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeKernelKComparison R D I)).toTruncated).comp
      (dgKappaSuppliedBFSourceEdge R D I)).comp (dgKappaSuppliedBFFiberComparison R D I))

/-- 概要：固定 K(D) 始点の同じ実 fiber 比較は、c5 の下で非負次数 π 同型。
方針：実核比較の全整数 π 同型・実始点同型・単回検出の非負次数同型を合成する。
規約：共終性・Z・ν 像の Verdier 認証や固定 K 四角形の引き戻し性は入力にしない。
使われ方：元の固定 K 始点を保持する K-6 d の条件付き結論。 -/
theorem dgKappaCanonicalFixedSourceFiberComparison_nonnegative
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeFirstRowSimplexQuotient (dgKappaNativeVerdierDiagram R D I).projection n)))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaCanonicalFixedSourceFiberComparison R D I).toTruncated) j) := by
  let a := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeKernelKComparison R D I)).toTruncated
  let b := dgKappaSuppliedBFSourceEdge R D I
  let c := dgKappaSuppliedBFFiberComparison R D I
  have ha : IsIso (Truncated.HomotopyCategory.homMk a) :=
    OmegaSpectrum.isInvertible_of_piIsomorphism _
      (dgKappaNativeKernelKComparison_piIsomorphism R D I)
  have haj := ConcreteCategory.bijective_of_isIso
    ((SpectrumHo.piFunctor j).map (Truncated.HomotopyCategory.homMk a))
  have hb : IsIso (Truncated.HomotopyCategory.homMk b) := by
    rw [show Truncated.HomotopyCategory.homMk b = _ from
      dgKappaSuppliedBFSourceEdge_hom R D I]
    infer_instance
  have hbj := ConcreteCategory.bijective_of_isIso
    ((SpectrumHo.piFunctor j).map (Truncated.HomotopyCategory.homMk b))
  change Function.Bijective (SpectrumHo.piMap
    (Truncated.HomotopyCategory.homMk ((a.comp b).comp c)) j)
  rw [← Truncated.HomotopyCategory.homMk_comp_homMk ((a.comp b).compStruct c),
    SpectrumHo.piMap_comp,
    ← Truncated.HomotopyCategory.homMk_comp_homMk (a.compStruct b), SpectrumHo.piMap_comp]
  exact (dgKappaCanonicalFiberComparison_nonnegative R D I hq j hj).comp (hbj.comp haj)

end SerrePositivity.KST.Fibration.Relative

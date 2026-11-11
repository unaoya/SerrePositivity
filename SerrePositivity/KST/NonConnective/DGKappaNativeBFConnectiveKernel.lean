module
public import SerrePositivity.KST.NonConnective.DGKappaNativeBFConnectiveStructure

/-!
概要：同じ未完備商核の指定全二胞体比較を、BF の実 fiber・固定 K の構造射へ渡す。
方針：元の動く共有対角の全四角柱と正段商比較から一回の S• fibration を消費する。
規約：有限 BF・共終性と K-6 の指定上側全族・正段商比較に条件付き。全段の Sp 引き戻し性は使わない。
使われ方：K-6 c4・c5 から K-7 c5・d3 への同じ実列上の接続。
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
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.NonConnective
local instance nativeBFKernelSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
variable
  (V : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ verdierFullSTransportedSquare.{max (u + 1) v}
      (dgKappaNativeVerdierDiagram R D I))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ quotientSKernelFullInfinitySquare.{max (u + 1) v}
      (dgKappaNativeVerdierDiagram R D I).isVerdier))
  (hdiag : (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{max (u + 1) v + 1})) ≫ V.h =
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{max (u + 1) v + 1})) ≫
      (verdierFullSLowerDeformation.{max (u + 1) v} (dgKappaNativeVerdierDiagram R D I)).h)
  (hV : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge V k).toTruncated)


variable (hBF : dgKappaNativeBFSquareComparison R D I)

include V hdiag hV in
/-- 概要：同じ実商核の指定全比較と正段商比較から、元の実 fiber 比較の非負次数同型を得る。
方針：同じ全四角形の一回の S• 引き戻しを同じ BF 第一正段へ渡す。
規約：各未供給命題は明示引数であり、存在や無条件 K-6 を主張しない。
使われ方：K-6 c4・c5 の残りの供給を同じ実 fiber 比較へ代入する。 -/
theorem dgKappaNativeBFFiber_nonnegative_of_kernel
    (hstage : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeSQuotientMap (dgKappaNativeQuotient R D I) (n + 1))))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaNativeBFFiberVertexComparison R D I hBF).toTruncated) j) :=
  dgKappaNativeBFFiberVertexComparison_nonnegative R D I hBF
    (dgKappaNativeFullSSquare_isPullback R D I V hdiag hV hstage) j hj

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
  (Z : DGKappaZeroInput R D I)

include V hdiag hV in
/-- 概要：同じ指定全比較と正段商比較から、元の固定 K 構造射の非負次数同型へ接続する。
方針：同じ一回の S• fibration と実 cone の零性を経て、元の完備化比較を続ける。
規約：有限 BF と共終性に条件付き。K₀ 全射性や固定 K の Sp 引き戻し性は要求しない。
使われ方：K-7 c5・d3 の同じ cone の構造射の受け渡し。 -/
theorem dgKappaNativeBFFixedStructure_nonnegative_of_kernel
    (hstage : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeSQuotientMap (dgKappaNativeQuotient R D I) (n + 1))))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaNativeStructureMap R D I
      (dgKappaNativeBFConnectiveFibrationEdge R D I hBF hcofinal Z)) j) :=
  dgKappaNativeBFConnectiveFixedStructureMap_nonnegative R D I hBF hcofinal Z
    (dgKappaNativeFullSSquare_isPullback R D I V hdiag hV hstage) j hj

include V hdiag hV in
/-- 概要：同じ実商の有限第一行比較から、元の固定 K 構造射の非負次数同型へ接続する。
方針：同じ指定全 S• 四角形を一回の BF fiber 比較と同じ cone の零性へ渡す。
規約：上側全族・有限 BF・共終性・第一行比較に条件付き。固定 K の Sp 引き戻し性は使わない。
使われ方：K-6 c5 の Sp 供給を K-7 c5・d3 の元の実構造辺へ代入する。 -/
theorem dgKappaNativeBFFixedStructure_nonnegative_of_firstRows
    (hrow : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeFirstRowQuotient (dgKappaNativeQuotient R D I) (n + 1))))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaNativeStructureMap R D I
      (dgKappaNativeBFConnectiveFibrationEdge R D I hBF hcofinal Z)) j) :=
  dgKappaNativeBFConnectiveFixedStructureMap_nonnegative R D I hBF hcofinal Z
    (dgKappaNativeFullSSquare_isPullback_of_firstRows R D I V hdiag hV hrow) j hj

end SerrePositivity.KST.NonConnective

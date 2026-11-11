module
public import SerrePositivity.KST.NonConnective.DGKappaNativeKernelKComparison
public import SerrePositivity.KST.NonConnective.DGKappaRawSuspensionCompletion

/-!
概要：完備化前の実 fibration と同じ実商の完備化を経る固定 K の構造辺。
方針：元の P を通る始点比較・実 fibration 辺・元の Yoneda 比較の loop を合成する。
規約：実 fibration 辺とその非負次数比較、共終性に条件付き。存在や全入力自然性は主張しない。
使われ方：K-7 c5・d3 の採用済み経路を、元の固定 K の二頂点の間へ戻す。
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
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance nativeStructureSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance nativeStructureSpectrumHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
variable (ρ : Sp.{max (u + 1) v}.Edge
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum (stableCategoryModel (dgKappaNativeKernelCategory R D I))))
  ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
      (stableCategoryModel (dgKappaNativeSuspensionCategory R D I))))))

/-- 概要：同じ実 fibration 辺に条件付きで、元の固定 K の間の実構造辺を作る。
方針：元の始点比較と同じ実商の loop 完備化比較を元の辺の前後に続ける。
規約：元の I・P・実商と固定 K の頂点を保持し、既存の条件付き屋根を置換しない。
使われ方：採用経路による段別構造辺の利用側。 -/
def dgKappaNativeStructureEdge : Sp.{max (u + 1) v}.Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R D))
    ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaSuspensionKInput R D I)))) :=
  SSet.Edge.ofTruncated
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeKernelKComparison R D I)).toTruncated.comp ρ.toTruncated).comp
      (dgKappaRawSuspensionToFixedLoopEdge R D I).toTruncated)

/-- 概要：同じ実構造辺に対応する実 BF 射。
方針：Sp 正本の辺回収を同じ元の全一単体へ適用する。
規約：実 fibration 辺に条件付きで、別の頂点や固定 K を選ばない。
使われ方：同じ構造辺の非負次数比較を逐次 BF 列へ渡す。 -/
def dgKappaNativeStructureMap := SpectrumHo.edgeMap (dgKappaNativeStructureEdge R D I ρ)

/-- 概要：回収した BF 射は元の構造辺の全一単体を保持する。
方針：Sp 正本の辺回収則を適用する。
規約：元の実 fibration 辺を含む合成辺の厳密等式。
使われ方：構造辺と元の実逐次遷移射の照合。 -/
theorem dgKappaNativeStructureMap_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeStructureMap R D I ρ)).edge =
      (dgKappaNativeStructureEdge R D I ρ).edge := SpectrumHo.edgeMap_edge _

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
    (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))

include hcofinal in
/-- 概要：実 fibration の非負次数比較と共終性に条件付きで、元の実構造射は非負次数 π 同型。
方針：同じ三辺の π 写像の合成と元の Yoneda 比較の自然な次数移動を使う。
規約：K₀ 全射性、固定連結 K の Sp 引き戻し性、全入力自然性は要求しない。
使われ方：K-7 c5・d3 の同じ元の構造射からの隣接安定化。 -/
theorem dgKappaNativeStructureMap_nonnegative
    (hρ : ∀ j : ℤ, 0 ≤ j → Function.Bijective
      (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk ρ.toTruncated) j))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaNativeStructureMap R D I ρ) j) := by
  let a := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeKernelKComparison R D I)).toTruncated
  let b := ρ.toTruncated
  let c := (dgKappaRawSuspensionToFixedLoopEdge R D I).toTruncated
  have ha : Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk a) j) := by
    rw [SpectrumHo.piMap_edge]
    change Function.Bijective (OmegaSpectrum.homotopyMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeKernelKComparison R D I))) j)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom_edge]
    exact dgKappaNativeKernelKComparison_piIsomorphism R D I j
  have hc := dgKappaRawSuspensionToFixedLoopEdge_nonnegative R D I hcofinal j hj
  rw [dgKappaNativeStructureMap, ← SpectrumHo.piMap_edge]
  change Function.Bijective (SpectrumHo.piMap
    (Truncated.HomotopyCategory.homMk ((a.comp b).comp c)) j)
  rw [← Truncated.HomotopyCategory.homMk_comp_homMk ((a.comp b).compStruct c),
    SpectrumHo.piMap_comp,
    ← Truncated.HomotopyCategory.homMk_comp_homMk (a.compStruct b), SpectrumHo.piMap_comp]
  exact hc.comp ((hρ j hj).comp ha)

end SerrePositivity.KST.NonConnective

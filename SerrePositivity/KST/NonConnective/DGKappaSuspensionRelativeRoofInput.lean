module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionLoopComparison
public import SerrePositivity.KST.Spectra.SpectrumNativeLoopFunctor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv

/-!
概要：同じ平坦 dg 懸垂の実相対四角形を明示入力に隔離し、元の固定 K の構造比較を作る。
方針：同じ商射を保つ四角形の実 fiber を、固定 native loop の値へ比較する。
規約：全利用側の定理はこの入力に条件付き。この入力の存在と元の Perf・P への照合は未供給。I・P の型は変更しない。
使われ方：K-7 c5 の採用済み明示供給境界。実供給済みの非連結 K 構成とは数えない。
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
local instance : SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory
local instance (X Y : OmegaSpectrum.{w}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v)) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 元の平坦 cone と実商射を保持する相対 dg 四角形の、未供給の実入力。 -/
structure DGKappaSuspensionRelativeRoofInput where
  /-- D-9：同じ平坦商の実小 dg 核。 -/
  kernel : PerfDGInput.{u, max (u + 1) v} R
  /-- Sp-6：固定 ν の実相対 Verdier 四角形。平坦屋根の供給は D-9。 -/
  diagram : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, max (u + 1) v} R)
  /-- D-9・Sp-6：同じ実核への始点照合。元の Perf・P との照合は別途 K-B。 -/
  left_eq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex diagram.square 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex kernel
  /-- D-9・Sp-6：同じ平坦 cone の指定入力頂点への照合。 -/
  middle_eq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex diagram.square 1 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaResolvedConeKInput R D I)
  /-- D-9・Sp-6：同じ平坦商の指定懸垂頂点への照合。 -/
  right_eq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex diagram.square 1 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R D I)
  /-- D-9・Sp-6：元の平坦商射の全一単体との厳密一致。 -/
  quotient : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ diagram.square =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaResolvedSuspensionInputMap R D I)).edge

variable (ρ : DGKappaSuspensionRelativeRoofInput R D I) (Z : DGKappaZeroInput R D I)

/-- 同じ実四角形の canonical fiber を、同じ K 懸垂の loop 四角形として保持する。 -/
def DGKappaSuspensionRelativeRoofInput.loopSquare :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaSuspensionKInput R D I))) :=
  dgKappaSuspensionLoopSquare R D I Z ρ.diagram ρ.middle_eq ρ.right_eq

/-- 同じ元の核 K 頂点から、同じ実 fiber loop への実比較辺。 -/
def DGKappaSuspensionRelativeRoofInput.loopComparison :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R ρ.kernel))
      (ρ.loopSquare R D I Z).vertex :=
  dgKappaSuspensionLoopComparison R D I Z ρ.diagram ρ.middle_eq ρ.right_eq ρ.kernel ρ.left_eq

/-- 元の実 loop と固定 native loop の同型の逆を表す、一本の実辺。 -/
def DGKappaSuspensionRelativeRoofInput.nativeLoopInverseEdge :
    Truncated.Edge (X := (truncation 2).obj Sp.{max (u + 1) v}) (ρ.loopSquare R D I Z).vertex
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaSuspensionKInput R D I)))) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _
    (OmegaSpectrum.nativeLoopVertexIso (ρ.loopSquare R D I Z)).inv)

/-- 明示相対屋根に条件付きで、選んだ実辺は、同じ固定 native loop 比較の逆同型そのものを表す。 -/
theorem DGKappaSuspensionRelativeRoofInput.nativeLoopInverseEdge_hom :
    Truncated.HomotopyCategory.homMk (ρ.nativeLoopInverseEdge R D I Z) =
      (OmegaSpectrum.nativeLoopVertexIso (ρ.loopSquare R D I Z)).inv :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ _)

/-- 明示相対屋根に条件付きで、同じ固定 native loop への比較辺は可逆。 -/
theorem DGKappaSuspensionRelativeRoofInput.nativeLoopInverseEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (ρ.nativeLoopInverseEdge R D I Z) := by
  change IsIso (Truncated.HomotopyCategory.homMk (ρ.nativeLoopInverseEdge R D I Z))
  rw [ρ.nativeLoopInverseEdge_hom R D I Z]
  infer_instance

/-- 元の核 K から固定 native loop K(Σ) への、同じ二辺を合成した全一単体。 -/
def DGKappaSuspensionRelativeRoofInput.nativeStructureEdge :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R ρ.kernel))
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaSuspensionKInput R D I)))) :=
  SSet.Edge.ofTruncated
    ((ρ.loopComparison R D I Z).toTruncated.comp (ρ.nativeLoopInverseEdge R D I Z))

/-- 固定 native loop への比較は、元の fiber 比較と同じ実合成二胞体を持つ。 -/
def DGKappaSuspensionRelativeRoofInput.nativeStructureTriangle :
    SSet.Edge.CompStruct (ρ.loopComparison R D I Z)
      (SSet.Edge.ofTruncated (ρ.nativeLoopInverseEdge R D I Z)) (ρ.nativeStructureEdge R D I Z) :=
  SSet.Edge.CompStruct.ofTruncated
    ((ρ.loopComparison R D I Z).toTruncated.compStruct (ρ.nativeLoopInverseEdge R D I Z))

/-- 明示相対屋根に条件付きで、固定 native loop 比較の可逆性は、同じ元の相対 K 四角形の引き戻し性と同値。 -/
theorem DGKappaSuspensionRelativeRoofInput.nativeStructureEdge_isInvertible_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (ρ.nativeStructureEdge R D I Z) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (ρ.diagram.square ≫ dgKInputK R) := by
  letI : IsIso (Truncated.HomotopyCategory.homMk (ρ.nativeLoopInverseEdge R D I Z)) :=
    ρ.nativeLoopInverseEdge_isInvertible R D I Z
  change IsIso (Truncated.HomotopyCategory.homMk
    ((ρ.loopComparison R D I Z).toTruncated.comp (ρ.nativeLoopInverseEdge R D I Z))) ↔ _
  rw [← Truncated.HomotopyCategory.homMk_comp_homMk
    ((ρ.loopComparison R D I Z).toTruncated.compStruct (ρ.nativeLoopInverseEdge R D I Z)),
    isIso_comp_right_iff]
  exact dgKappaSuspensionLoopComparison_isInvertible_iff R D I Z ρ.diagram
    ρ.middle_eq ρ.right_eq ρ.kernel ρ.left_eq

/-- 固定 native loop の元の頂点を、同じ実 BF spectrum として保持する。 -/
def dgKappaSuspensionNativeLoopSpectrum : OmegaSpectrum.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgKappaSuspensionKInput R D I))))

/-- 同じ構造比較の全一単体から回収する、元の核 BF K からの厳密 spectrum 射。 -/
def DGKappaSuspensionRelativeRoofInput.nativeStructureBFMap :
    dgKInputSpectrum R ρ.kernel ⟶ dgKappaSuspensionNativeLoopSpectrum R D I :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom ((ρ.nativeStructureEdge R D I Z).ofEq rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm)

/-- 明示相対屋根に条件付きで、回収した厳密 BF 射の辺は、同じ元の構造比較の全一単体そのもの。 -/
theorem DGKappaSuspensionRelativeRoofInput.nativeStructureBFMap_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (ρ.nativeStructureBFMap R D I Z)).edge =
      (ρ.nativeStructureEdge R D I Z).edge := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom ((ρ.nativeStructureEdge R D I Z).ofEq rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm)
  exact congrArg (fun e => e.edge) he

end SerrePositivity.KST.NonConnective

module
public import SerrePositivity.KST.SConstruction.DGOdotTailLaxComparison
public import SerrePositivity.KST.SConstruction.DGOdotTailKernelLowerTriangle
public import SerrePositivity.KST.SConstruction.DGOdotCatPerfInput

/-!
概要：四完備性と実 resolved 商を保持し、③ の三認証を一回受け取って LT へ接続する。
方針：既存 ActualRectangleInput を変更せず明示引数に取り、同じ実二面と全長方形を消費する。
規約：三認証の存在は主張しない。resolved 完備化先と元 ⊙ の比較を混同しない。
使われ方：K-10 e② の供給待ち骨格。実構成到着後は同じ引数への代入だけを行う。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
  Spectra
open scoped Simplicial
local instance : SimplicialCategory OmegaSpectrum.{u + 1} := OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元四対象の完備性・実商・共通長方形の三認証を保持する接続データ。
方針：四完備性は D 正本由来、実商は同じ resolved 商の完備化、長方形は明示入力。
規約：入力存在の証明ではない。使われ方：三認証到着時の一回代入。 -/
structure DGOdotTailCatPerfConnection where
  fourComplete : DGOdotCatPerfInput R d
  quotient : PerfectLaxQuotient (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)
  quotient_eq : quotient = dgOdotMilnorCompletedLaxQuotient R d h
  actual : DGOdotMilnorActualRectangleInput R d h

/-- 概要：三認証以外の完備性・実商の入力を全て充足した e② 接続。
方針：D 由来の四完備性と Milnor の実完備化を代入する。
規約：共通実長方形の存在は明示引数。使われ方：到着した実構成を一回だけ代入する入口。 -/
def dgOdotTailCatPerfConnection (v : DGOdotMilnorActualRectangleInput R d h) :
    DGOdotTailCatPerfConnection R d h where
  fourComplete := dgOdotCatPerfInput R d
  quotient := dgOdotMilnorCompletedLaxQuotient R d h
  quotient_eq := rfl
  actual := v

/-- 概要：三認証を個別の明示引数として受ける e② の接続口。
方針：確認済みの各フィールドの型を変えず、同じ実長方形入力へ一回束ねる。
規約：いずれの認証の存在も主張しない。使われ方：③ の認証を段階的に型照合する。 -/
def dgOdotTailCatPerfConnectionOfCertificates
    (diagram : (Δ[2] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R)
    (rightBoundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso (dgOdotMilnorActualRightDiagram R d h).square
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ diagram ≫ dgKInputPerfectNu R))
    (rightComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso (dgOdotMilnorActualRightDiagram R d h).square
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 0 ≫ diagram ≫ dgKInputPerfectNu R) rightBoundary)
    (outerBoundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso (dgOdotMilnorActualOuterDiagram R d h).square
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ diagram ≫ dgKInputPerfectNu R))
    (outerComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareDiagramIso (dgOdotMilnorActualOuterDiagram R d h).square
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ diagram ≫ dgKInputPerfectNu R) outerBoundary)
    (boundary : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleBoundaryIso (diagram ≫ dgKInputPerfectNu R)
      (dgOdotMilnorCompletedLaxQuotient R d h).rectangleDiagram)
    (comparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierRectangleDiagramIso (diagram ≫ dgKInputPerfectNu R)
      (dgOdotMilnorCompletedLaxQuotient R d h).rectangleDiagram boundary)
    (kernel_vertex : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex ((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 2) 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d)) :
    DGOdotTailCatPerfConnection R d h :=
  dgOdotTailCatPerfConnection R d h
    ⟨diagram, rightBoundary, rightComparison, outerBoundary, outerComparison,
      boundary, comparison, kernel_vertex⟩

namespace DGOdotTailCatPerfConnection
variable {R d h} (c : DGOdotTailCatPerfConnection R d h)

/-- 概要：同じ実商の列を任意の局所化不変量が fiber 列へ送る。
方針：実列の提示へ既存定理を適用する。規約：三認証と商存在を混同しない。
使われ方：e② の実商側結論。 -/
theorem isFiber {E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}}
    (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence (hE.fiberTriangle c.quotient.sequence.presentation) :=
  hE.fiberTriangle_isFiber _

/-- 概要：共通 S 長方形の比較面を同じ不変量が引き戻しへ送る。
方針：明示入力された実右面・外周認証を消費する。
規約：個別恒等面の認証で代用しない。使われ方：e② の実 S 面の結論。 -/
theorem actual_isPullback {E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}}
    (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare c.actual.diagram 2) ≫
      dgKInputPerfectNu R ≫ E) := c.actual.comparison_isPullback hE

/-- 概要：上下指定二単体を保つ全比較で同じ実商の LT 比較面へ接続する。
方針：第三認証を含む既存輸送を適用する。
規約：三認証を全て保持。使われ方：e② の Cat^perf 長方形側結論。 -/
theorem completed_isPullback {E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}}
    (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare c.quotient.rectangleDiagram 2) ≫ E) := by
  rw [c.quotient_eq]
  exact c.actual.completedComparison_isPullback hE

/-- 概要：同じ実商・完備化後の二脚と元始域値を持つ LT 錐は極限。
方針：接続に保持した実商を Tamme の実錐の定理へ渡す。
規約：実面の三認証とは別の同値先を選ばない。使われ方：e② の LT 極限結論。 -/
theorem landTammeCone_isLimit {E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}}
    (hE : IsPerfectLocalizingInvariant E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (c.quotient.valuePullbackCone hE) :=
  c.quotient.valuePullbackCone_isLimit hE

/-- 概要：元対角始域の値を、実増大屋根と全長方形の同じ始域成分で回収する。
方針：三認証入力の既存始域同型を実商へ照合する。
規約：元始域を別頂点へ置き換えない。使われ方：LT の元始域値の保持。 -/
def sourceValueIso (E : perfectStableInfinity.{u + 1} ⟶ Sp.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((dgKInputPerfectNu R ≫ E).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotDiagonalSourceInput R d)))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (((β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare c.quotient.rectangleDiagram 2) ≫ E) 0 0) := by
  rw [c.quotient_eq]
  exact c.actual.sourceValueIso E
end DGOdotTailCatPerfConnection
end SerrePositivity.KST.SConstruction

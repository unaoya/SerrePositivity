module
public import SerrePositivity.KST.NonConnective.DGKappaNativeFibration
public import SerrePositivity.KST.Fibration.VerdierFullSMovingSquarePrism

/-!
概要：同じ D-9 の native 実四角形を、指定全二胞体を保つ比較の利用側へ接続する。
方針：同じ元の Verdier 提示を動く共有対角の四角柱に代入し、実商核の引き戻しを移す。
規約：上側全族・全対角条件と正段商比較に条件付き。存在を主張しない。
使われ方：K-6 c4 の残る F1 供給と c5 の正段比較を、同じ完備化前の実列で消費する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Fibration SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
variable
  (V : SSet.Homotopy
    (squareTriangle 0 ≫ verdierFullSTransportedSquare.{max (u + 1) v}
      (dgKappaNativeVerdierDiagram R D I))
    (squareTriangle 0 ≫ quotientSKernelFullInfinitySquare.{max (u + 1) v}
      (dgKappaNativeVerdierDiagram R D I).isVerdier))
  (hdiag : (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{max (u + 1) v + 1})) ≫ V.h =
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{max (u + 1) v + 1})) ≫
      (verdierFullSLowerDeformation.{max (u + 1) v} (dgKappaNativeVerdierDiagram R D I)).h)
  (hV : ∀ k, IsInvertibleEdge (simplicialHomotopyVertexEdge V k).toTruncated)

/-- 概要：同じ実上側全族の供給に条件付きで、D-9 の元の全 S• 四角形を同じ実商核へ比較する。
方針：指定上下二胞体と動く共有対角を保つ既存の四角柱へ同じ実列を代入する。
規約：全関手同型であり、境界だけの一致や未指定ホーン充填で代用しない。
使われ方：K-6 c4 の実供給後に同じ native 列の引き戻し性を移す。 -/
def dgKappaNativeFullSSquareIso :
    FunctorIso ((dgKappaNativeVerdierDiagram R D I).square ≫
      coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0))
      (quotientSKernelInfinitySquare (dgKappaNativeKernelInclusion R D I)
        (dgKappaNativeQuotient R D I)) :=
  verdierFullSMovingKernelSquareIso.{max (u + 1) v} (dgKappaNativeVerdierDiagram R D I) V hdiag hV

include V hdiag hV in
/-- 概要：同じ実上側全族と正段比較に条件付きで、完備化前の実 Verdier 四角形の全 S• 像は引き戻し。
方針：元の実商核の引き戻しを同じ全四角形同型の逆で移す。
規約：固定 K の Sp 引き戻し性を結論せず、正段比較と上側全族の存在も主張しない。
使われ方：K-6 c4・c5 の独立した残りを同じ実列で接続する。 -/
theorem dgKappaNativeFullSSquare_isPullback
    (hstage : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeSQuotientMap (dgKappaNativeQuotient R D I) (n + 1)))) :
    IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
      coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)) :=
  (dgKappaNativeQuotientSKernel_isPullback R D I hstage).of_functorIso
    (dgKappaNativeFullSSquareIso R D I V hdiag hV).symm

end SerrePositivity.KST.NonConnective

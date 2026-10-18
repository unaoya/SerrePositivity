module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.QuotientRepresentability
public import SerrePositivity.KST.DerivedGeometry.DGResolution.VerdierTransport

/-!
概要：半自由分解後の商から元の Verdier 商への比較で代表対象の像を計算する。
方針：既存の商の代表対象の同型、局所化の正方形、増大関手の代表加群の比較を合成する。
規約：同じ商関手と同じ増大準同値を使う。
使われ方：Drinfeld Lemma 13.5・Thm 3.4・§3.5、KST D4・§10-7 の Dqc の対象条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.DGResolution
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/--
概要：分解後の商の代表対象の像は元の増大像の代表対象の Verdier 局所化と同型。
方針：商の tria 同値を逆に戻し、Verdier 移送の正方形と導来延長の計算を使う。
規約：代表対象を別の解消で取り替えない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4 の元の導来像との比較。
-/
def quotientTriaOriginalRepresentableIso (N : Set D) (x : Objects A D) :
    (quotientToOriginalVerdierEquivalence A D N).functor.obj
        (triaRepresentable A (Quotient A D N) ⟨x⟩) ≅
      (triaQuotient A D N).obj (triaRepresentable A D ((augmentation A D).obj x)) := by
  let E := quotientTriaEquivalence A D N
  let V := verdierEquivalence A D N
  let Q := triaQuotient A (Objects A D) (nullObjects A D N)
  let R := triaRepresentable A (Objects A D) x
  let e : E.functor.obj (Q.obj R) ≅ triaRepresentable A (Quotient A D N) ⟨x⟩ :=
    DGQuotient.localQuotientTriaRepresentableIso A (Objects A D) (nullObjects A D N) x
  let e' : E.inverse.obj (triaRepresentable A (Quotient A D N) ⟨x⟩) ≅ Q.obj R :=
    E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app (Q.obj R)
  exact V.functor.mapIso e' ≪≫ (verdierSquare A D N).app R ≪≫
    (triaQuotient A D N).mapIso ((derivedFiniteCellOver A D Set.univ).isoMk
      (dgDerivedExtensionRepresentableIso A (Objects A D) D (augmentation A D) x))

/--
概要：商自体の H⁰ の対象の像は元の増大像の代表対象の Verdier 局所化と同型。
方針：H⁰ の Yoneda 像の計算同型に証明済みの商の代表対象の計算を合成する。
規約：H⁰ の対象を元の商の対象として保持する。
使われ方：Drinfeld Lemma 13.5・Thm 3.4、KST D4・§10-7 の層コホモロジーの比較。
-/
def quotientHomotopyOriginalRepresentableIso (N : Set D) [(yonedaToTria A D).EssSurj]
    (x : Objects A D) :
    ((quotientHomotopyTriaEquivalence A D N).trans
      (quotientToOriginalVerdierEquivalence A D N)).functor.obj
        ((toHomotopy A (Quotient A D N)).obj (ForgetEnrichment.of (Complex A) ⟨x⟩)) ≅
      (triaQuotient A D N).obj (triaRepresentable A D ((augmentation A D).obj x)) :=
  (quotientToOriginalVerdierEquivalence A D N).functor.mapIso
    (yonedaToTria_objIso A (Quotient A D N) _) ≪≫ quotientTriaOriginalRepresentableIso A D N x

end SerrePositivity.KST.DerivedGeometry.DGResolution

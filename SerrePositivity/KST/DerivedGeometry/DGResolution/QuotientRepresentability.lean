module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.YonedaTria
public import SerrePositivity.KST.DerivedGeometry.DGResolution.Quotient
public import SerrePositivity.KST.DerivedGeometry.DGResolution.RepresentabilityTransport

/-!
概要：前三角的な dg 圏の平坦な path 商の H⁰ と tria を比較する。
方針：指定 Verdier 商の本質的全射性と代表対象の比較同型を合成する。
規約：商の H⁰ を tria と定義し直さず、冪等完備化を導入しない。
使われ方：Drinfeld §2.4・Thm 3.4・§3.5、KST D4・§10-7。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.DerivedGeometry.DGResolution
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/--
概要：元の H⁰ が tria を表現すれば、平坦な path 商の H⁰ も商の tria を表現する。
方針：Verdier 局所化の対象を元へ戻し、元の代表対象を同じ商の代表対象へ移す。
規約：片側 K-flat 条件は既存の比較定理だけに渡す。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4・§10-7 の商自体の H⁰。
-/
theorem pathQuotient_yonedaToTria_essSurj (S : Set D)
    (hflat : DGQuotient.localKFlat A D S) [(yonedaToTria A D).EssSurj] :
    (yonedaToTria A (DGQuotient.QuotientObject D S)).EssSurj where
  mem_essImage X := by
    let E := DGQuotient.localQuotientTriaEquivalence A D S hflat
    let Q := triaQuotient A D S
    let Y := E.functor.objPreimage X
    let Z := Q.objPreimage Y
    let T := (yonedaToTria A D).objPreimage Z
    let d := ForgetEnrichment.to (Complex A) T.as
    let e : triaRepresentable A D d ≅ Z :=
      (yonedaToTria_objIso A D T).symm ≪≫ (yonedaToTria A D).objObjPreimageIso Z
    let q : DGQuotient.QuotientObject D S := ⟨d⟩
    refine ⟨(toHomotopy A (DGQuotient.QuotientObject D S)).obj
      (ForgetEnrichment.of (Complex A) q), ⟨?_⟩⟩
    exact yonedaToTria_objIso A (DGQuotient.QuotientObject D S) _ ≪≫
      (DGQuotient.localQuotientTriaRepresentableIso A D S d).symm ≪≫
      E.functor.mapIso (Q.mapIso e) ≪≫ E.functor.mapIso (Q.objObjPreimageIso Y) ≪≫
      E.functor.objObjPreimageIso X

/--
概要：半自由分解後の商の H⁰ はその tria の全対象を表現する。
方針：増大準同値に沿って代表可能性を移し、証明済みの K-flat 性を使う。
規約：元の Hom に平坦性を仮定しない。
使われ方：Drinfeld Lemma 13.5・Thm 3.4、KST D4 の層複体の商。
-/
theorem quotient_yonedaToTria_essSurj (N : Set D) [(yonedaToTria A D).EssSurj] :
    (yonedaToTria A (Quotient A D N)).EssSurj := by
  let : (yonedaToTria A (Objects A D)).EssSurj :=
    yonedaToTria_essSurj_of_quasiEquivalence A (Objects A D) D (augmentation A D)
      (augmentation_quasiEquivalence A D)
  exact pathQuotient_yonedaToTria_essSurj A (Objects A D) (nullObjects A D N)
    (localKFlat A D (nullObjects A D N))

/--
概要：半自由分解後の商自体の H⁰ と tria の同値。
方針：一般の導来 Yoneda の完全忠実性と商の代表可能性を束ねる。
規約：前三角化の追加を定義で消さず、冪等完備化も加えない。
使われ方：Drinfeld §2.4・Lemma 13.5・Thm 3.4、KST D4・§10-7。
-/
def quotientHomotopyTriaEquivalence (N : Set D) [(yonedaToTria A D).EssSurj] :
    HomotopyCategory A (Quotient A D N) ≌ TriaCategory A (Quotient A D N) := by
  let : (yonedaToTria A (Quotient A D N)).EssSurj := quotient_yonedaToTria_essSurj A D N
  let : (yonedaToTria A (Quotient A D N)).IsEquivalence := {}
  exact (yonedaToTria A (Quotient A D N)).asEquivalence

end SerrePositivity.KST.DerivedGeometry.DGResolution

module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.YonedaTria
public import SerrePositivity.KST.DerivedGeometry.DGResolution.Pretriangulation

/-!
概要：H⁰ が前三角化を表現する性質を dg 準同値に沿って移送する。
方針：H⁰ と tria の二つの同値と、導来延長の代表加群の計算同型を使う。
規約：代表可能性の未証明のフィールドは導入しない。
使われ方：Drinfeld §2.4・Lemma 13.5、KST D4・§10-7 の半自由分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.DerivedGeometry.DGResolution
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/--
概要：準同値の先で H⁰ が tria を表現すれば、元でも表現する。
方針：tria の対象を移送し、H⁰ の本質的全射性で代表対象を戻す。
規約：戻した同型は同じ導来延長の完全忠実性で持ち上げる。
使われ方：Drinfeld §2.4・Lemma 13.5、KST D4 の分解後の前三角性。
-/
theorem yonedaToTria_essSurj_of_quasiEquivalence (hF : QuasiEquivalence F)
    [(yonedaToTria A E).EssSurj] : (yonedaToTria A D).EssSurj where
  mem_essImage X := by
    let : F.onHomotopy.EssSurj := hF.2
    let G := (triaEquivalence A D E F hF).functor
    let Y := (yonedaToTria A E).objPreimage (G.obj X)
    let T := F.onHomotopy.objPreimage Y
    let d := ForgetEnrichment.to (Complex A) T.as
    let e₁ : G.obj (triaRepresentable A D d) ≅ triaRepresentable A E (F.obj d) :=
      (derivedFiniteCellOver A E Set.univ).isoMk
        (dgDerivedExtensionRepresentableIso A D E F d)
    let e₂ : triaRepresentable A E (F.obj d) ≅ G.obj X :=
      (yonedaToTria_objIso A E (F.onHomotopy.obj T)).symm ≪≫
        (yonedaToTria A E).mapIso (F.onHomotopy.objObjPreimageIso Y) ≪≫
        (yonedaToTria A E).objObjPreimageIso (G.obj X)
    refine ⟨(toHomotopy A D).obj (ForgetEnrichment.of (Complex A) d), ⟨?_⟩⟩
    exact yonedaToTria_objIso A D _ ≪≫ G.preimageIso (e₁ ≪≫ e₂)

end SerrePositivity.KST.DerivedGeometry.DGResolution

module

public import SerrePositivity.AlgebraicGeometry.RingDirectLimitIntNaturality
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitMap

/-!
概要：実際の環の Frobenius 順極限の射を、整数加群の余極限の射と照合する。
方針：環の有向系の比較の自然性を反復 Frobenius に適用する。
規約：標数条件は p = 0 とし、零環も含める。
使われ方：F6 の標準開の制限と閉厚化の環の射に同じ比較を適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
variable (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
variable (f : A →+* B)

/-- 環の射が誘導する整数加群としての反復 Frobenius 系の自然変換。 -/
abbrev frobeniusIntDirectSystemNatTrans :
    linearDirectSystemFunctor (ringDirectSystemIntMap (frobeniusDirectSystemMap A p hp hA)) ⟶
      linearDirectSystemFunctor (ringDirectSystemIntMap (frobeniusDirectSystemMap B p hp hB)) :=
  linearDirectSystemNatTrans
    (ringDirectSystemIntMap (frobeniusDirectSystemMap A p hp hA))
    (ringDirectSystemIntMap (frobeniusDirectSystemMap B p hp hB))
    (fun _ ↦ f.toAddMonoidHom.toIntLinearMap)
    (frobeniusDirectSystemMap_naturality p hp hA hB f)

/-- Frobenius 順極限の環の射と整数加群の余極限の射は比較同型を介して一致する。 -/
theorem frobeniusDirectLimitIntColimitIso_naturality :
    ModuleCat.ofHom (frobeniusDirectLimitMap p hp hA hB f).toAddMonoidHom.toIntLinearMap ≫
        (ringDirectLimitIntColimitIso (frobeniusDirectSystemMap B p hp hB)).hom =
      (ringDirectLimitIntColimitIso (frobeniusDirectSystemMap A p hp hA)).hom ≫
        colim.map (frobeniusIntDirectSystemNatTrans p hp hA hB f) :=
  ringDirectLimitIntColimitIso_naturality
    (frobeniusDirectSystemMap A p hp hA) (frobeniusDirectSystemMap B p hp hB)
    (fun _ ↦ f) (frobeniusDirectSystemMap_naturality p hp hA hB f)

end SerrePositivity.AlgebraicGeometry

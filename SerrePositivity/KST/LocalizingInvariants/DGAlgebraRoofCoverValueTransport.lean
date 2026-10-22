module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverInvertingFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSurjectiveRoofConnectiveValue

/-!
概要：cover 前合成で証明した実 roof 値の正方形を、元の connective な値へ戻す。
方針：元の分子・分母に counit の自然性を適用し、源で可逆な counit を消去する。
規約：全代数上の準同型反転を元の関手に仮定しない。使われ方：具体的不変量の候補比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
variable (R : Type u) [CommRing R] {D : Type v} [Category.{w} D]
  (L : Mon (Complex R) ⥤ D) (hL : InvertsConnectiveQuasiIsos R L)

lemma connectiveValue_cover_naturality {A B : Mon (Complex R)} (hA : IsConnective R A)
    (r : SurjectiveRoof R A B) :
    L.map (connectiveCoverInclusion R A) ≫ connectiveValue R L hL hA r =
      value R (connectiveCoverFunctor R ⋙ L) (invertsQuasiIsos_coverFunctor R L hL) r ≫
        L.map (connectiveCoverInclusion R B) := by
  have := invertsQuasiIsos_coverFunctor R L hL r.denominator r.denominator_quasiIso
  apply (cancel_epi ((connectiveCoverFunctor R ⋙ L).map r.denominator)).1
  rw [← Category.assoc, coverCounit_naturality_value, Category.assoc,
    denominator_connectiveValue, ← Category.assoc, denominator_value]
  exact (coverCounit_naturality_value R L r.numerator).symm

lemma connectiveValue_square_of_cover {A B C E : Mon (Complex R)}
    (hA : IsConnective R A) (hC : IsConnective R C)
    (r : SurjectiveRoof R A B) (s : SurjectiveRoof R C E) (a : A ⟶ C) (b : B ⟶ E)
    (h : value R (connectiveCoverFunctor R ⋙ L) (invertsQuasiIsos_coverFunctor R L hL) r ≫
        (connectiveCoverFunctor R ⋙ L).map b =
      (connectiveCoverFunctor R ⋙ L).map a ≫
        value R (connectiveCoverFunctor R ⋙ L) (invertsQuasiIsos_coverFunctor R L hL) s) :
    connectiveValue R L hL hA r ≫ L.map b = L.map a ≫ connectiveValue R L hL hC s := by
  have := hL (connectiveCover_isConnective R A) hA (connectiveCoverInclusion R A)
    (connectiveCoverInclusion_quasiIso R A hA)
  apply (cancel_epi (L.map (connectiveCoverInclusion R A))).1
  rw [← Category.assoc, connectiveValue_cover_naturality, Category.assoc,
    ← coverCounit_naturality_value, ← Category.assoc, h, Category.assoc,
    ← connectiveValue_cover_naturality, ← Category.assoc, coverCounit_naturality_value,
    Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof

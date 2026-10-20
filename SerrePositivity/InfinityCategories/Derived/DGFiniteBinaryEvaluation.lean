module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingBinaryEvaluation
public import SerrePositivity.InfinityCategories.Derived.DGQuotientHomRoofRepresentation
/-!
概要：有限な二商 Hom 族に、実屋根表示・同時細分・任意標的の三作用族の評価比較を供給する。
方針：実屋根比較の弱同値による表示を取り、商内と任意反転標的で同じ細分を評価する。
規約：各入力への全輸送と全降下選択空間上の三関手同型を保持する。使われ方：合成整合性。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (x y z : D) {K Y : SSet.{max u v}} [Quasicategory Y]
variable (F : dgNerve A D ⟶ Y)
variable (b : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
  ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y))
variable (c : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
  ((DGQuotient.inclusion A D P).obj y) ((DGQuotient.inclusion A D P).obj z))
/-- 有限な二商 Hom 族の実屋根表示・共通細分と、同じ三作用族の実合成評価。 -/
structure DGFiniteBinaryEvaluation where
  firstRoof : K ⟶ dgRoofCorrespondence A D P x y
  secondRoof : K ⟶ dgRoofCorrespondence A D P y z
  firstComparison : SSet.Homotopy (firstRoof ≫ dgRoofCorrespondenceMap A D P x y)
    (b ≫ dgQuotientFixedHomRoofMap A D P x y)
  secondComparison : SSet.Homotopy (secondRoof ≫ dgRoofCorrespondenceMap A D P y z)
    (c ≫ dgQuotientFixedHomRoofMap A D P y z)
  source : DGInvertingFiniteRoofComposition A D P x y z (dgQuotientNerveProjection A D P)
    firstRoof secondRoof
  evaluation : DGInvertingBinaryEvaluation A D P x y z F firstRoof secondRoof source b c
/-- 任意の有限二商 Hom 族を、任意反転標的で全選択空間上の三作用族と同時に実評価できる。 -/
lemma dgFiniteBinaryEvaluation_nonempty [K.Finite] (hP : DGQuotient.localKFlat A D P)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) :
    Nonempty (DGFiniteBinaryEvaluation A D P x y z F b c) := by
  obtain ⟨r, ⟨Hr⟩⟩ := dgQuotientHomFinite_actualRoofLift A D P hP x y b
  obtain ⟨s, ⟨Hs⟩⟩ := dgQuotientHomFinite_actualRoofLift A D P hP y z c
  obtain ⟨C⟩ := dgInvertingFiniteRoofComposition_nonempty A D P x y z
    (dgQuotientNerveProjection A D P) r s hP
      (dgQuotientNerveProjection_invertsVerdierEdges A D P hP)
  obtain ⟨E⟩ := dgInvertingBinaryEvaluation_nonempty A D P x y z F r s C b c hP hF Hr Hs
  exact ⟨⟨r, s, Hr, Hs, C, E⟩⟩
end SerrePositivity.InfinityCategories

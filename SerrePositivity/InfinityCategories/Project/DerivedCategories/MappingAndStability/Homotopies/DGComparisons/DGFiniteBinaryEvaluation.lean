module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGInvertingBinaryEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientHomRoofRepresentation
/-!
概要：有限な二商 Hom 族に、実屋根表示・同時細分・任意標的の三作用族の評価比較を供給する。
方針：実屋根比較の弱同値による表示を取り、商内と任意反転標的で同じ細分を評価する。
規約：各入力への全輸送と全降下選択空間上の三関手同型を保持する。使われ方：合成整合性。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x y z : D) {K Y : SSet.{max u v}} [Quasicategory Y]
variable (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
variable (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
variable (c : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj z))
/-- 有限な二商 Hom 族の実屋根表示・共通細分と、同じ三作用族の実合成評価。 -/
structure DGFiniteBinaryEvaluation where
  firstRoof : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y
  secondRoof : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P y z
  firstComparison : SSet.Homotopy (firstRoof ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
    (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y)
  secondComparison : SSet.Homotopy (secondRoof ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P y z)
    (c ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P y z)
  source : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingFiniteRoofComposition A D P x y z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
    firstRoof secondRoof
  evaluation : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingBinaryEvaluation A D P x y z F firstRoof secondRoof source b c
/-- 任意の有限二商 Hom 族を、任意反転標的で全選択空間上の三作用族と同時に実評価できる。 -/
lemma dgFiniteBinaryEvaluation_nonempty [K.Finite] (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) :
    Nonempty (DGFiniteBinaryEvaluation A D P x y z F b c) := by
  obtain ⟨r, ⟨Hr⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientHomFinite_actualRoofLift A D P hP x y b
  obtain ⟨s, ⟨Hs⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientHomFinite_actualRoofLift A D P hP y z c
  obtain ⟨C⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFiniteRoofComposition_nonempty A D P x y z
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) r s hP
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_invertsVerdierEdges A D P hP)
  obtain ⟨E⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingBinaryEvaluation_nonempty A D P x y z F r s C b c hP hF Hr Hs
  exact ⟨⟨r, s, Hr, Hs, C, E⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories

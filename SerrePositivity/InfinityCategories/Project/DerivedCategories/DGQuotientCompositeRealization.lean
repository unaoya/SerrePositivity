module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientFiniteRoofComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofHomotopyComposition
/-!
概要：元の実屋根の合成候補から、入力商 Hom 二族の実 AW 合成への実比較を構成する。
方針：指定商評価への比較と商内の合成評価の同定を、実二三角形のまま貼る。
規約：同時細分・三評価族・両比較と合成三角形を保持する。使われ方：任意標的の三作用族。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x y z : D) {K : SSet.{max u v}}
variable (r : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y) (s : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P y z)
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingFiniteRoofComposition A D P x y z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) r s)
variable (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
variable (c : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj z))
/-- 指定商評価を経由する、実合成候補から実 AW 合成への全パラメータ実比較。 -/
structure DGQuotientCompositeRealization where
  evaluation : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofFamilyRealization A D P x z (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
    C.source.compositeDenominator C.source.compositeNumerator C.composite
  valueHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFamilyEvaluationValue A D P x z C.source.compositeDenominator
      C.source.compositeNumerator C.composite) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily b c)
  comparison : SSet.Homotopy
    (C.source.compositeDiagram ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x z)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily b c ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x z)
  triangle : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFamilyEvaluationHomotopy A D P x z C.source.compositeDenominator
      C.source.compositeNumerator C.composite evaluation)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp valueHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x z)) comparison
/-- 指定入力の商側比較と同時細分に、実 AW 合成への二比較と実合成三角形が存在する。 -/
lemma dgQuotientCompositeRealization_nonempty (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (Hr : SSet.Homotopy (r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
      (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y))
    (Hs : SSet.Homotopy (s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P y z)
      (c ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P y z)) :
    Nonempty (DGQuotientCompositeRealization A D P x y z r s C b c) := by
  obtain ⟨E⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFamilyRealization_nonempty A D P x z
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) C.source.compositeDenominator
      C.source.compositeNumerator C.composite
  obtain ⟨H⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientCompositeEvaluation_homotopy A D P x y z r s C hP b c Hr Hs
  obtain ⟨J, ⟨T⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofHomotopyComposition_exists
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFamilyEvaluationHomotopy A D P x z C.source.compositeDenominator
      C.source.compositeNumerator C.composite E)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x z))
  exact ⟨⟨E, H, J, T⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientFamilyEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingFiniteRoofComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedFamilyCompositionTransport
/-!
概要：商内の同時細分の実合成評価族を、入力商 Hom 二族の実 AW 合成に同定する。
方針：三評価族の実三角形を標準頂点へ輸送し、両入力の実ホモトピーと AW 合成則を使う。
規約：元の同時細分と指定三評価族を保持する。使われ方：実合成候補の商側比較。
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
/-- 指定三評価族の三角形は、標準商頂点間の同じ三族の合成方程式を与える。 -/
lemma dgQuotientEvaluationValues_comp :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (DGQuotient.QuotientObject D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFamilyEvaluationValue A D P x y C.source.first.denominator
        C.source.first.coefficient C.first) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (DGQuotient.QuotientObject D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFamilyEvaluationValue A D P y z C.source.second.denominator
        C.source.second.coefficient C.second) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (DGQuotient.QuotientObject D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFamilyEvaluationValue A D P x z C.source.compositeDenominator
        C.source.compositeNumerator C.composite) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedFamilyHom_comp_endpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) z)
    C.first.value C.second.value C.composite.value
    (Truncated.HomotopyCategory.homMk_comp_homMk C.triangle)
/-- 同じ合成評価族は、元の二商 Hom 族の全次元 AW 合成と実ホモトピック。 -/
lemma dgQuotientCompositeEvaluation_homotopy (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
    (c : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj z))
    (Hr : SSet.Homotopy (r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
      (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y))
    (Hs : SSet.Homotopy (s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P y z)
      (c ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P y z)) :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFamilyEvaluationValue A D P x z C.source.compositeDenominator
        C.source.compositeNumerator C.composite) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily b c)) := by
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientPresentedFamilyEvaluation_homotopy A D P x y hP r C.source.first C.first b Hr
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientPresentedFamilyEvaluation_homotopy A D P y z hP s C.source.second
    C.second c Hs
  have h₁ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilyHom_eq_iff_homotopy).mpr hr
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilyHom_eq_iff_homotopy).mpr hs
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilyHom_eq_iff_homotopy).mp
  exact (dgQuotientEvaluationValues_comp A D P x y z r s C).symm.trans
    ((congrArg₂ (fun a b => a ≫ b) h₁ h₂).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom_comp A (DGQuotient.QuotientObject D P) b c))
end SerrePositivity.InfinityCategories.Project.DerivedCategories

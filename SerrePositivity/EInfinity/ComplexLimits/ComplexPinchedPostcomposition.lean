module

public import SerrePositivity.EInfinity.ComplexLimits.ComplexPinchedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPostcompositionInterval

/-!
# 元の複体射の Hom 後合成と dg nerve の同じ全区間族

概要：同じ複体射の実 Hom 後合成は同じ閉辺の後合成を任意パラメータで表す。
方針：元の閉射への変換と豊穣後合成を照合し、元の全族合成式を使う。
規約：全複体・同じ射・任意 K を保ち、小ささを仮定しない。
使われ方：正規化 frame の実 augmentation の全族評価方程式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

lemma complexToClosed_postcomposition (X : Complex A) {P Q : Complex A} (f : P ⟶ Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition A (Complex A) (x := X) ((complexToClosed A).map f) =
      homPostcompose X f := by
  change (ρ_ (homComplex A X P)).inv ≫
    homComplex A X P ◁ ForgetEnrichment.homTo (Complex A) ((complexToClosed A).map f) ≫
      enrichedComposition X P Q = homPostcompose X f
  rw [complexToClosed_homTo]
  exact (homPostcompose_closedMap A X f).symm

lemma complexPinchedPostcomposition_family (X : Complex A) {P Q : Complex A} (f : P ⟶ Q)
    (K : SSet.{u + 1}) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A) (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (homPostcompose X f)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A) g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K
      (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((complexToClosed A).map f))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom_comp A (Complex A) g
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (Complex A) ((complexToClosed A).map f)))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomCompositionFamily_closed_post] at h
  have hc : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A)
      (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (Complex A) ((complexToClosed A).map f))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((complexToClosed A).map f))) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilyHom_const_vertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) _
  rw [hc] at h
  change _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A) (g ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Complex A) (E := Complex A) (x := X) (y := P) (x' := X) (y' := Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition A (Complex A) (x := X) ((complexToClosed A).map f))) at h
  rw [complexToClosed_postcomposition] at h
  exact h.symm

end SerrePositivity.EInfinity.ComplexLimits

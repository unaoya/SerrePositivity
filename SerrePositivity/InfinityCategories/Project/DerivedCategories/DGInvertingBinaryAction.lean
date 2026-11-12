module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteBinaryEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedFamilyCompositionEvaluation
/-!
概要：任意有限二商 Hom 族について、全降下選択を同時に動かす実作用族の合成を証明する。
方針：同じ三実評価族への全選択空間上の同型を、任意共通選択パラメータ上で展開する。
規約：三対象対の選択を独立に動かせる。使われ方：局所化延長の二入力合成整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 商 Hom の作用を、商 Hom パラメータと任意の降下選択パラメータ上で同時に評価する。 -/
def dgInvertingHomFamilyValue (P : Set D) (x y : D) {K Y S : SSet.{max u v}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
    (p : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomDescentSpace A D P x y F) :
    K ⊗ S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) :=
  uncurry (p ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamily A D P x y F ≫ (pre b).app _))
variable (P : Set D) (x y z : D) {K Y : SSet.{max u v}} [Quasicategory Y]
variable (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
variable (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
variable (c : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj z))
/-- 同じ実三評価を持つ三作用族は、任意の共通選択パラメータ上で合成する。 -/
lemma dgInvertingBinaryAction_of_evaluation
    (E : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteBinaryEvaluation A D P x y z F b c)
    (S : SSet.{max u v}) (p₁ : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomDescentSpace A D P x y F)
    (p₂ : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomDescentSpace A D P y z F)
    (p₃ : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomDescentSpace A D P x z F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (dgInvertingHomFamilyValue A D P x y F b p₁ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (dgInvertingHomFamilyValue A D P y z F c p₂ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (dgInvertingHomFamilyValue A D P x z F
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily b c) p₃ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedFamilyComposition_evaluation _ _ _
    E.evaluation.first.value E.evaluation.second.value E.evaluation.composite.value
    E.evaluation.firstIso E.evaluation.secondIso E.evaluation.compositeIso
    (Truncated.HomotopyCategory.homMk_comp_homMk E.evaluation.triangle) S p₁ p₂ p₃
/-- 任意有限二商 Hom 族の作用は、全選択空間を同時に動かすパラメータ全体で合成する。 -/
lemma dgInvertingBinaryAction_comp [K.Finite] (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
    (S : SSet.{max u v}) (p₁ : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomDescentSpace A D P x y F)
    (p₂ : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomDescentSpace A D P y z F)
    (p₃ : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomDescentSpace A D P x z F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (dgInvertingHomFamilyValue A D P x y F b p₁ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (dgInvertingHomFamilyValue A D P y z F c p₂ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (dgInvertingHomFamilyValue A D P x z F
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily b c) p₃ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) := by
  obtain ⟨E⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteBinaryEvaluation_nonempty A D P x y z F b c hP hF
  exact dgInvertingBinaryAction_of_evaluation A D P x y z F b c E S p₁ p₂ p₃
/-- 同じ全選択パラメータ上で、三作用族の実合成三角形を取れる。 -/
lemma dgInvertingBinaryAction_triangle_nonempty [K.Finite] (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
    (S : SSet.{max u v}) (p₁ : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomDescentSpace A D P x y F)
    (p₂ : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomDescentSpace A D P y z F)
    (p₃ : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomDescentSpace A D P x z F) :
    Nonempty (Truncated.Edge.CompStruct
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (dgInvertingHomFamilyValue A D P x y F b p₁ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (dgInvertingHomFamilyValue A D P y z F c p₂ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (dgInvertingHomFamilyValue A D P x z F
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily b c) p₃ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
  exact dgInvertingBinaryAction_comp A D P x y z F b c hP hF S p₁ p₂ p₃
end SerrePositivity.InfinityCategories.Project.DerivedCategories

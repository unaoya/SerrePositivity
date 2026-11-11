module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.RightHomotopySquare
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightIntervalEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-!
概要：全パラメータの定値関手間の Hom による写像空間の充満忠実性の判定。
方針：標的の普遍区間族の逆像を選び、族の単射性で両合成のホモトピーを構成する。
規約：単なる h 圏の充満忠実性ではなく、全パラメータ上の条件を要求する。
使われ方：comma の前合成の Hom 対応を実際の写像空間の比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：後合成が定値関手間の Hom に誘導する写像。
方針：h Fun の後合成の両端を定値関手の標準同型で揃える。
規約：パラメータの quasicategory 性は不要。
使われ方：区間写像空間の族の作用を表す。 -/
def constantHomPostcomp {X Y : SSet.{u}} (F : X ⟶ Y)
    (A : SSet.{u}) (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x y → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A Y
      (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) := fun α ↦
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A x F).inv ≫
    (hoFunctor.map ((ihom A).map F)).toFunctor.map α ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A y F).hom

/-- 概要：全パラメータの Hom 全単射から指定区間写像のホモトピー同値を得る。
方針：普遍族の逆像を区間族で表し、順写像の族での単射性から逆則を証明する。
規約：実際の intervalFunctorMap 自身の逆と両ホモトピーを構成する。
使われ方：h Fun の全パラメータ比較を写像空間の同値へ強める。 -/
lemma intervalFunctorMap_equivalence_of_constantHom_bijective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) (x y : X _⦋0⦌)
    (h : ∀ (A : SSet.{u}) [Quasicategory A],
      Function.Bijective (constantHomPostcomp F A x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x y) := by
  let m := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x y
  let B := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y)
  obtain ⟨α, hα⟩ := (h B).2 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 B))
  obtain ⟨r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_surjective B X x y α
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (r ≫ m) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 B) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorMap_familyHom, hr]
    exact hα
  refine ⟨r, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy he⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy
  apply (h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)).1
  change constantHomPostcomp F _ x y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (m ≫ r)) =
    constantHomPostcomp F _ x y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 _))
  unfold constantHomPostcomp
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorMap_familyHom, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorMap_familyHom]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_precomp, he,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_precomp, Category.comp_id, Category.id_comp]

/-- 概要：定値関手間の全パラメータ Hom 全単射は右 pinched 写像空間の同値を与える。
方針：区間模型の同値を自然な pinched 比較の可換正方形で移す。
規約：指定された pinchedHomMap 自身の同値性。
使われ方：元の関手圏への前合成を写像空間で判定する。 -/
lemma pinchedHomMap_equivalence_of_constantHom_bijective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) (x y : X _⦋0⦌)
    (h : ∀ (A : SSet.{u}) [Quasicategory A],
      Function.Bijective (constantHomPostcomp F A x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x y) := by
  have hi := intervalFunctorMap_equivalence_of_constantHom_bijective F x y h
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).comp hi.isQCatEquivalence
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedIntervalComparison_naturality] at hc
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence _ _).cancel_right hc
  exact hp.isSimplicialHomotopyEquivalence

/-- 概要：全パラメータの関手圏の h における充満忠実性は写像空間の充満忠実性を導く。
方針：定値関手間の Hom に制限し、端点の同型の前後合成で全単射を得る。
規約：元の h 圏だけの充満忠実性ではなく、全ての関手圏を検査する。
使われ方：前合成と内部 Hom の交換による写像空間の判定。 -/
lemma isFullyFaithful_of_parameterized_hoFullyFaithful {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y)
    (h : ∀ (A : SSet.{u}) [Quasicategory A],
      (hoFunctor.map ((ihom A).map F)).toFunctor.FullyFaithful) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful F := by
  intro x y
  apply pinchedHomMap_equivalence_of_constantHom_bijective F x y
  intro A _
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x y ≃
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((SSet.const x : A ⟶ X) ≫ F) ((SSet.const y : A ⟶ X) ≫ F) :=
    (h A).homEquiv
  exact (e.trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A x F).homCongr (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A y F))).bijective

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

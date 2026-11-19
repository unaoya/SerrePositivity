module

public import SerrePositivity.KST.LocalizingInvariants.MappingTargetIso

/-!
概要：反射の左関手は、右随伴の像に同型な任意の終点への元の写像空間を保つ。
方針：定値化した終点同型で Hom 全単射を移し、区間模型から右 pinched 模型へ戻す。
規約：元の pinchedHomMap 自体の同値。使われ方：零始点矢印に対する cofiber 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful G)

include a hG in
lemma reflectiveIsoTargetConstantMap_bijective (A : SSet.{u}) [Quasicategory A]
    (x z : X _⦋0⦌) (y : Y _⦋0⦌) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso z (G.app (Opposite.op ⦋0⦌) y)) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.constantFunctorPostMap F A x z) := by
  let d := constantVertexIso A e ≪≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A y G).symm
  have h := functorMap_bijective_of_targetIso
    (hoFunctor.map ((ihom A).map F)).toFunctor
    (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X))) _ _ d
    (reflectiveTargetHom_bijective a hG (SSet.const x) (SSet.const y))
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A x F).homCongr (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso A z F)
    ).bijective.comp h

include a hG in
lemma reflectiveIsoTargetPinchedHomMap_equivalence (x z : X _⦋0⦌) (y : Y _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso z (G.app (Opposite.op ⦋0⦌) y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x z) := by
  have hi := intervalFunctorMap_equivalence_of_constantHom_bijective F x z
    (fun A _ => reflectiveIsoTargetConstantMap_bijective a hG A x z y e)
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x z).comp hi.isQCatEquivalence
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedIntervalComparison_naturality] at h
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) z)).cancel_right h
  ).isSimplicialHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants

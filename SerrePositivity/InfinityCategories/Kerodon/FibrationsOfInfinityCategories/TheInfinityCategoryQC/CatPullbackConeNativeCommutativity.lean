module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackConeTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatTriangleFaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackConeProjections

/-!
概要：Cat_∞ の引き戻し錐そのものが与える可換関手同型。
方針：左右の native な三角形を指定関手同型へ読み戻して合成する。
規約：指定 path との整合は次元三の比較で別に検証する。
使われ方：native な可換性と候補の可逆 path の照合。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：錐の射上の native な三角形は中心側の脚と二射の合成の関手同型。
方針：三辺を指定関手に同定し、元の二単体の精密化の像を読む。
規約：別の同型の代表を存在から選ばない。
使われ方：左右の native な三角形の同時の可換性。 -/
def catPullbackConeLegTriangleIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeFunctorLeg p q j)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeFunctorLeg p q i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagram p q).map f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityTriangleIso_of_faces _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTriangle p q f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTriangle_two p q f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTriangle_zero p q f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTriangle_one p q f)
/-- 概要：native な引き戻し錐の左右二脚が与える可換関手同型。
方針：中心への同じ脚からの二つの三角形の同型を合成する。
規約：向きは左脚と p の合成から右脚と q の合成。
使われ方：catPullbackCommutativity の指定 path との比較。 -/
def catPullbackConeNativeCommutativity (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeFst p q ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeSnd p q ≫ q) :=
  (catPullbackConeLegTriangleIso p q (AsSmall.up.map WalkingCospan.Hom.inl)).symm ≪≫
    catPullbackConeLegTriangleIso p q (AsSmall.up.map WalkingCospan.Hom.inr)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

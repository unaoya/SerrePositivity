module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackLastTetrahedronRelation
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PrismIsoCancellation

/-!
概要：各脚の指定比較同型の図式の射に沿う整合式。
方針：三つの比較三単体の関係から二つの共有面の同型を消去する。
規約：元の錐と図式円柱の指定三角形の同型を保持する。
使われ方：strict な面を簡約して二射影の指定比較と指定 path を照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：各脚の指定比較は元と置換後の錐の三角形と図式の指定比較に対して整合する。
方針：元の三つの四面の合成則を使い、内部同型を消去する。
規約：各同型の存在だけでなく指定された値の合成の等式。
使われ方：native な錐の可換性と候補の指定可逆 path の一致を証明する。 -/
lemma catPullbackConeLegSectionIso_naturality (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    (catPullbackConeLegTriangleIso p q f).postcomp
        ((catPullbackReplacementNatTrans p q).app j) ≪≫
      (catPullbackDiagramComparisonIso p q f).precomp
        (show catPullback p q ⟶ ((catPullbackDiagram p q).obj i).obj from
          catPullbackConeFunctorLeg p q i) ≪≫
      (catPullbackConeLegSectionIso p q i).postcomp
        ((catPullbackReplacementDiagram p q).map f) =
    catPullbackConeLegSectionIso p q j ≪≫
      (catPullbackReplacementTriangleIso p q f).precomp (𝟙 (catPullback p q)) := by
  have h := prismIso_cancel
    (catPullbackConeUpperComparisonIso p q j)
    ((catPullbackReplacementTriangleIso p q f).precomp (𝟙 (catPullback p q)))
    (catPullbackFirstInteriorIso p q f)
    ((catPullbackConeUpperComparisonIso p q i).postcomp
      ((catPullbackReplacementDiagram p q).map f))
    (catPullbackSecondInteriorIso p q f)
    ((catPullbackDiagramUpperComparisonIso p q f).precomp
      (show catPullback p q ⟶ ((catPullbackDiagram p q).obj i).obj from
        catPullbackConeFunctorLeg p q i))
    ((catPullbackConeLowerComparisonIso p q i).postcomp
      ((catPullbackReplacementDiagram p q).map f))
    ((catPullbackDiagramLowerComparisonIso p q f).precomp
      (show catPullback p q ⟶ ((catPullbackDiagram p q).obj i).obj from
        catPullbackConeFunctorLeg p q i))
    (catPullbackConeLowerComparisonIso p q j)
    ((catPullbackConeLegTriangleIso p q f).postcomp
      ((catPullbackReplacementNatTrans p q).app j))
    (catPullbackFirstTetrahedron_relation p q f)
    (catPullbackMiddleTetrahedron_relation p q f)
    (catPullbackLastTetrahedron_relation p q f)
  simpa only [catPullbackDiagramComparisonIso, catPullbackConeLegSectionIso,
    functorIso_precomp_trans, functorIso_precomp_symm,
    functorIso_postcomp_trans, functorIso_postcomp_symm, Iso.trans_assoc] using h

end SerrePositivity.InfinityCategories.F2

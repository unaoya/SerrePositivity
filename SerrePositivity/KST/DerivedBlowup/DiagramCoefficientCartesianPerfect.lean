module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientCartesianComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraCartesianIsomorphism

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の cartesian perfect 図式加群の表示同値。
方針：指定比較の可逆性と局所 perfect 性の保存・反映で全導来同値を制限する。
規約：層の Perf との比較とは区別した図式加群模型上の同値。
使われ方：例外因子の元の表示と共通 Koszul 表示の大域候補比較。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.DerivedBlowup
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)}
variable [Small.{u} (DiagramModuleCoefficientObject F)]
variable [Small.{u} (DiagramModuleCoefficientObject G)]

/-- 概要：係数図式同型の導来制限は cartesian perfect 条件を保存・反映する。
方針：指定比較の可逆性と局所 perfect 性の二つの iff を組み合わせる。
規約：KST §3.1・Lemma 3.6。使われ方：指定導来同値の部分圏への制限。 -/
theorem diagramCoefficientDerivedRestriction_cartesianPerfect_iff (e : F ≅ G)
    (X : DerivedAllDiagramModules G) :
    diagramAlgebraCartesianPerfect F ((diagramCoefficientDerivedRestriction e).obj X) ↔
      diagramAlgebraCartesianPerfect G X :=
  and_congr (diagramCoefficientDerivedRestriction_cartesian_iff e X)
    (diagramCoefficientDerivedRestriction_locallyPerfect_iff e X)

/-- 概要：係数図式同型による cartesian perfect 導来図式加群の指定圏同値。
方針：全図式加群の指定延長–制限同値を保存・反映する対象条件で制限する。
規約：KST Lemma 3.6、図式加群模型による再構成。
使われ方：二つの例外因子表示の大域 Perf 候補の比較。 -/
def diagramCoefficientCartesianPerfectEquivalence (e : F ≅ G) :
    (diagramAlgebraCartesianPerfect F).FullSubcategory ≌
      (diagramAlgebraCartesianPerfect G).FullSubcategory :=
  ((diagramCoefficientDerivedEquivalence e).symm.congrFullSubcategory
    (P := diagramAlgebraCartesianPerfect G) (Q := diagramAlgebraCartesianPerfect F)
    (by
      funext X
      exact propext (diagramCoefficientDerivedRestriction_cartesianPerfect_iff e X))).symm

end SerrePositivity.KST.DerivedBlowup

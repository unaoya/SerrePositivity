module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientEvaluation
public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientDerivedEquivalence
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraLocallyPerfect
public import SerrePositivity.KST.DerivedBlowup.AlgebraVertexIso
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数図式同型は局所 perfect 条件を保存・反映する。
方針：指定局所評価の自然同型と、局所係数 dg 準同値に沿う導来制限の perfect 判定を使う。
規約：局所 perfect 部分圏の比較。canonical な cartesian 比較射の整合性は別義務。
使われ方：例外因子の二つの表示を大域 Perf 候補へ制限する準備。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)}
variable [Small.{u} (DiagramModuleCoefficientObject F)]
variable [Small.{u} (DiagramModuleCoefficientObject G)]

omit [DecidableLE J] [Small.{u} (DiagramModuleCoefficientObject F)]
  [Small.{u} (DiagramModuleCoefficientObject G)] in
/-- 概要：図式同型の局所成分に沿う導来制限は perfect 性を保存・反映する。
方針：局所代数同型の一対象表示の opposite の準同値に既存の Morita 判定を使う。
規約：KST Lemma 3.6。使われ方：全局所評価の perfect 性の比較。 -/
theorem diagramCoefficientLocalDerivedRestriction_perfect_iff (e : F ≅ G) (i : J)
    (X : DerivedModuleCategory R (AlgebraVertex (G.obj i))ᵒᵖ) :
    modulePerfect R (AlgebraVertex (F.obj i))ᵒᵖ
        ((diagramCoefficientLocalDerivedRestriction e.hom i).obj X) ↔
      modulePerfect R (AlgebraVertex (G.obj i))ᵒᵖ X :=
  quasiEquivalenceRestriction_perfect_iff R (AlgebraVertex (F.obj i))ᵒᵖ
    (AlgebraVertex (G.obj i))ᵒᵖ (algebraVertexMap (e.hom.app i)).op
    (quasiEquivalence_op _ (algebraVertexMap_quasiEquivalence (e.app i))) X

/-- 概要：係数図式同型の指定導来制限は任意の図式対象の局所 perfect 性を保存・反映。
方針：局所評価の指定自然同型を通し、局所 Morita 同値の perfect 判定へ帰着する。
規約：KST §3.1・Lemma 3.6、cartesian 条件はまだ要求しない。
使われ方：局所 perfect 部分圏への表示同値の制限。 -/
theorem diagramCoefficientDerivedRestriction_locallyPerfect_iff (e : F ≅ G)
    (X : DerivedAllDiagramModules G) :
    diagramAlgebraLocallyPerfect F ((diagramCoefficientDerivedRestriction e).obj X) ↔
      diagramAlgebraLocallyPerfect G X := by
  constructor
  · intro h i
    have hp := (modulePerfect R (AlgebraVertex (F.obj i))ᵒᵖ).prop_of_iso
      ((diagramCoefficientDerivedEvaluationIso e.hom i).app X) (h i)
    exact (diagramCoefficientLocalDerivedRestriction_perfect_iff e i _).mp hp
  · intro h i
    have hp := (diagramCoefficientLocalDerivedRestriction_perfect_iff e i _).mpr (h i)
    exact (modulePerfect R (AlgebraVertex (F.obj i))ᵒᵖ).prop_of_iso
      ((diagramCoefficientDerivedEvaluationIso e.hom i).app X).symm hp

/-- 概要：係数図式同型による局所 perfect 導来図式加群の指定圏同値。
方針：元の延長–制限同値を、保存・反映する局所 perfect 条件で制限する。
規約：KST Lemma 3.6、cartesian 部分圏と層の Perf との比較は別に残す。
使われ方：例外因子の表示比較の局所有限性部分。 -/
def diagramCoefficientLocallyPerfectEquivalence (e : F ≅ G) :
    (diagramAlgebraLocallyPerfect F).FullSubcategory ≌
      (diagramAlgebraLocallyPerfect G).FullSubcategory :=
  ((diagramCoefficientDerivedEquivalence e).symm.congrFullSubcategory
    (P := diagramAlgebraLocallyPerfect G) (Q := diagramAlgebraLocallyPerfect F)
    (by
      funext X
      exact propext (diagramCoefficientDerivedRestriction_locallyPerfect_iff e X))).symm

end SerrePositivity.KST.DerivedBlowup

module
public import SerrePositivity.KST.Comparison.HomologyFilteredColimits
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-!
# 借用するホモロジーの整数加群模型の順序余極限

概要：K-L2 のアーベル群模型の filtered 保存を整数加群の複体模型に移す。
方針：ℤ 加群とアーベル群の実同値で反映し、三項複体への評価を使う。
規約：KST Proposition 4.14、SW92 Lemma 1.4。H_* の定義は置き換えない。
使われ方：自然な複体模型を持つ借用 H_* の rank 余極限の保存。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits

/-- 概要：K-L2 の三項複体のホモロジー保存を最小の filtered 添字宇宙へ移す。
方針：AB5 による既存の完全余極限保存を filtered 保存の構造に束ねる。
規約：SW92 Lemma 1.4。使われ方：自然数添字の実ホモロジー比較。 -/
lemma abelianShortHomology_preservesSequentialColimits :
    PreservesColimitsOfShape ℕ (ShortComplex.homologyFunctor AddCommGrpCat.{u}) := by
  letI : PreservesFilteredColimitsOfSize.{u, u}
      (ShortComplex.homologyFunctor AddCommGrpCat.{u}) := {
    preserves_filtered_colimits := fun J _ _ ↦
      Comparison.shortComplexHomology_preservesExactColimits (J := J) }
  have : PreservesFilteredColimitsOfSize.{0, 0}
      (ShortComplex.homologyFunctor AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  infer_instance

/-- 概要：整数加群からアーベル群への実同値は三項複体の順序余極限を保つ。
方針：三つの評価で実同値の余極限保存を使う。
規約：KST Proposition 4.14 の模型移送。使われ方：実ホモロジー比較の反映。 -/
instance intForgetShortComplex_preservesSequentialColimits :
    PreservesColimitsOfShape ℕ
      (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapShortComplex where
  preservesColimit {D} := {
    preserves {c} hc := by
      refine ⟨ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_⟩
      · exact isColimitOfPreserves (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})
          (isColimitOfPreserves ShortComplex.π₁ hc)
      · exact isColimitOfPreserves (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})
          (isColimitOfPreserves ShortComplex.π₂ hc)
      · exact isColimitOfPreserves (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})
          (isColimitOfPreserves ShortComplex.π₃ hc) }

/-- 概要：整数加群の三項複体のホモロジーは順序余極限を保存する。
方針：K-L2 の実アーベル群側比較を ℤ 加群との実同値で反映する。
規約：SW92 Lemma 1.4。使われ方：整数加群値の複体ホモロジーの rank 比較。 -/
instance moduleShortHomology_preservesSequentialColimits :
    PreservesColimitsOfShape ℕ (ShortComplex.homologyFunctor (ModuleCat.{u} ℤ)) := by
  let U := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  letI := abelianShortHomology_preservesSequentialColimits.{u}
  have : PreservesColimitsOfShape ℕ (ShortComplex.homologyFunctor (ModuleCat.{u} ℤ) ⋙ U) :=
    preservesColimitsOfShape_of_natIso (ShortComplex.homologyFunctorIso U)
  exact preservesColimitsOfShape_of_reflects_of_preserves _ U

/-- 概要：整数加群値鎖複体の三項評価は順序余極限を保存する。
方針：三つの複体評価の実余極限保存に帰着する。
規約：KST Appendix A の非負次数の模型。使われ方：実鎖ホモロジー保存の証明。 -/
instance moduleShortComplexFunctor_preservesSequentialColimits (i : ℕ) :
    PreservesColimitsOfShape ℕ
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (.down ℕ) i) where
  preservesColimit {D} := {
    preserves {c} hc := by
      refine ⟨ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_⟩
      · exact isColimitOfPreserves
          (HomologicalComplex.eval (ModuleCat.{u} ℤ) (.down ℕ) ((ComplexShape.down ℕ).prev i)) hc
      · exact isColimitOfPreserves (HomologicalComplex.eval (ModuleCat.{u} ℤ) (.down ℕ) i) hc
      · exact isColimitOfPreserves
          (HomologicalComplex.eval (ModuleCat.{u} ℤ) (.down ℕ) ((ComplexShape.down ℕ).next i)) hc }

/-- 概要：整数加群値鎖複体のホモロジーは順序余極限を保存する。
方針：三項評価と実ホモロジーの余極限保存を合成する。
規約：SW92 Lemma 1.4。使われ方：借用する自然な複体模型からの実 filtered 比較。 -/
instance moduleChainHomology_preservesSequentialColimits (i : ℕ) :
    PreservesColimitsOfShape ℕ
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.down ℕ) i) :=
  preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso (ModuleCat.{u} ℤ) (.down ℕ) i).symm

end SerrePositivity.KST.ProExcision

module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedPiZero
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NatTrans
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullSubcategory
public import SerrePositivity.DifferentialGraded.Category.Basic

/-! # dg nerve の具体例と受入検査

概要：一点 dg 圏と非有界複体の dg 圏で二単体の方程式を具体化する。
方針：既存の二つの dg 豊穣構造を使い、複体の場合は Hom 微分と通常の cochain 合成に直す。
規約：HA Example 1.3.1.8、Proposition 1.3.1.10、Kerodon §4.6.5（Tag 01KW）。
使われ方：N6 の対象ビルドと公開宣言の最終公理監査。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded HomologicalComplex
open CochainComplex HomComplex
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A]

/-- 概要：一点 dg 圏の二単体は、三辺の合成の差を高次成分の微分として持つ。
方針：既存の ringEnrichment を選んで二単体の一般公式を具体化する。
規約：HA Example 1.3.1.8。使われ方：一点 dg 圏での N6 の符号検査。 -/
lemma ring_triangle_equation (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A PUnit.{1}) _⦋2⦌) :
    differential A s.triangleHom =
      compose A (s.edgeHom 1 2 (by decide)) (s.edgeHom 0 1 (by decide)) (by decide) -
        s.edgeHom 0 2 (by decide) := s.differential_triangleHom

/-- 概要：複体 dg 圏の通常順斉次合成は Mathlib の cochain 合成。
方針：豊穣合成の純粋 tensor での式を使い、二つの Koszul 符号を相殺する。
規約：HA Construction 1.3.1.6、リポジトリの cochain 規約。使われ方：具体的な二単体の式。 -/
lemma complex_compose {X Y Z : Complex A} {p q n : ℤ}
    (g : Homogeneous Y Z q) (f : Homogeneous X Y p) (h : p + q = n) :
    compose (D := Complex A) A (x := X) (y := Y) (z := Z) g f h = f.comp g h := by
  change (p * q).negOnePow • ((enrichedComposition X Y Z).f n
    (ιTensorObj (homComplex A X Y) (homComplex A Y Z) p q n h (f ⊗ₜ[A] g))) = _
  rw [enrichedComposition_apply]
  simp only [smul_smul, ← Int.negOnePow_add]
  have he : p * q + p * q = 2 * (p * q) := by ring
  rw [he, Int.negOnePow_two_mul, one_smul]

/-- 概要：非有界複体 dg 圏の二単体は通常の cochain Hom 微分で三辺の合成の差を埋める。
方針：二単体の一般公式の通常順合成を Mathlib の cochain 合成へ同定する。
規約：HA Example 1.3.1.8、微分 +1 と高次成分の次数 −1。使われ方：複体での N6 の具体検査。 -/
lemma complex_triangle_equation (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) _⦋2⦌) :
    HomComplex.δ (-1) 0 s.triangleHom =
      @Sub.sub (Cochain (s.obj 0) (s.obj 2) 0) inferInstance
        ((s.edgeHom 0 1 (by decide)).comp (s.edgeHom 1 2 (by decide))
          (show (0 : ℤ) + 0 = 0 from rfl)) (s.edgeHom 0 2 (by decide)) := by
  have h := s.differential_triangleHom
  rw [complex_compose] at h
  exact h

example : SSet.Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A PUnit.{1}) := inferInstance
example : SSet.Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) := inferInstance
example (x y : PUnit.{1}) : SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A PUnit.{1} x y) := inferInstance
example (X Y : Complex A) : SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X Y) := inferInstance

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraReflexiveCoequalizers
public import Mathlib.CategoryTheory.Adjunction.Lifting.Left
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
模型。文献の定義との比較は後で
# オペラッド代数の全余極限

概要：Berger–Moerdijk §1 の代数の圏に一般の小余極限を構成する。
方針：図式圏の忘却もモナド的と示し、定数図式関手への随伴持ち上げを適用する。
規約：一般の余極限を忘却が保つとは仮定しない。
使われ方：右転送定理と小対象論法に必要な余極限を供給する。
-/

@[expose] public section

noncomputable section

universe w v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (J : Type w) [Category.{v} J]

/-- 概要：代数の図式から底の複体の図式への忘却（BM §1）。
方針：既存の忘却関手による後合成を使う。
規約：図式の形を保つ。
使われ方：定数図式関手への随伴を持ち上げる。 -/
abbrev diagramForget : (J ⥤ P.Algebra) ⥤ (J ⥤ Complex A) :=
  (Functor.whiskeringRight J _ _).obj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P)

/-- 概要：図式圏の忘却もモナド的（BM §1）。
方針：点ごとの reflexive coequalizer の存在・保存・同型の反映に Beck の判定を使う。
規約：元の自由・忘却随伴を後合成へ拡張する。
使われ方：一般の図式の余極限を随伴持ち上げで得る。 -/
instance diagramForget_monadic : MonadicRightAdjoint (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.diagramForget P J) := by
  have : HasReflexiveCoequalizers (J ⥤ P.Algebra) :=
    hasReflexiveCoequalizers_iff.1 inferInstance
  have : Monad.PreservesColimitOfIsReflexivePair (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.diagramForget P J) := {
    out {_ _} f g _ := by
      have : PreservesColimit
          (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ ofIsReflexivePair f g)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.diagramForget P J) := inferInstance
      exact preservesColimit_of_iso_diagram (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.diagramForget P J)
        (inclusionWalkingReflexivePairOfIsReflexivePairIso f g) }
  exact Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms
    (P.freeAlgebraAdjunction.whiskerRight J)

/-- 概要：底にある任意の形の余極限は代数にも存在する（BM §1）。
方針：底の定数図式関手の左随伴をモナド的な忘却に沿って持ち上げる。
規約：代数の一般の余極限を忘却が保つという仮定は使わない。
使われ方：完全な右転送の有限余極限と超限合成の存在を保証する。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.instHasColimitsOfShapeOfComplex [HasColimitsOfShape J (Complex A)] : HasColimitsOfShape J P.Algebra := by
  let Q : P.Algebra ⥤ (J ⥤ P.Algebra) := Functor.const J
  have : (Functor.const J : Complex A ⥤ (J ⥤ Complex A)).IsRightAdjoint :=
    hasColimitsOfShape_iff_isRightAdjoint_const.1 inferInstance
  have : (Q ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.diagramForget P J).IsRightAdjoint := by
    let e : Q ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.diagramForget P J ≅ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P ⋙ Functor.const J := Iso.refl _
    exact ((Adjunction.ofIsRightAdjoint (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P ⋙ Functor.const J)).ofNatIsoRight
      e.symm).isRightAdjoint
  have : Q.IsRightAdjoint := isRightAdjoint_triangle_lift_monadic (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.diagramForget P J)
  exact hasColimitsOfShape_iff_isRightAdjoint_const.2 this

/-- 概要：オペラッド代数は全ての小余極限を持つ（BM §1）。
方針：複体の形ごとの余極限から得た存在を束ねる。
規約：係数環の宇宙内の小さい図式を扱う。
使われ方：転送と小対象論法の余極限の入力を供給する。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.instHasColimitsOfSize : HasColimitsOfSize.{u, u} P.Algebra where
  has_colimits_of_shape := inferInstance

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

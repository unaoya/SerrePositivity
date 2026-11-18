module

public import SerrePositivity.DifferentialGraded.Algebras.Monadic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ReflexivePairSifted
public import Mathlib.CategoryTheory.Adjunction.Lifting.Left
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits

/-!
# dg モノイドの全小余極限

概要：元の dg モノイド圏に一般の小余極限を構成する。
方針：図式の忘却のモナド性と定数図式への随伴持ち上げを使う。
規約：大域 instance は追加せず、構成を明示した値として公開する。
使われ方：自由像の小対象論法と実転送モデル構造。
-/

@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DGAlgebra
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded
variable {R : Type u} [CommRing R]

attribute [local instance] _root_.SerrePositivity.DGAlgebra.forgetCreatesSiftedColimits _root_.SerrePositivity.DGAlgebra.hasSiftedColimits _root_.SerrePositivity.DGAlgebra.forgetMonadic

/-- 概要：元の dg モノイドは reflexive coequalizer を持つ。
方針：WalkingReflexivePair の sifted 性を使う。
規約：底の余極限から構成する。
使われ方：図式忘却の Beck 判定。 -/
lemma hasReflexiveCoequalizers : HasReflexiveCoequalizers (Mon (Complex R)) :=
  hasReflexiveCoequalizers_iff.1 inferInstance

/-- 概要：忘却は reflexive coequalizer を保存する。
方針：共通切断を付加した図式の保存を final な包含へ制限する。
規約：一般の coequalizer の保存を仮定しない。
使われ方：図式忘却のモナド性。 -/
lemma forgetPreservesReflexiveCoequalizers :
    Monad.PreservesColimitOfIsReflexivePair (Mon.forget (Complex R)) where
  out {_ _} f g _ := by
    have : PreservesColimit
        (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ ofIsReflexivePair f g)
        (Mon.forget (Complex R)) := inferInstance
    exact preservesColimit_of_iso_diagram (Mon.forget (Complex R))
      (inclusionWalkingReflexivePairOfIsReflexivePairIso f g)

attribute [local instance] _root_.SerrePositivity.DGAlgebra.hasReflexiveCoequalizers _root_.SerrePositivity.DGAlgebra.forgetPreservesReflexiveCoequalizers

/-- 概要：dg モノイドの図式の忘却。
方針：元の忘却による後合成。
規約：図式の形を保つ。
使われ方：随伴持ち上げの三角形。 -/
abbrev diagramForget (J : Type w) [Category.{v} J] :
    (J ⥤ Mon (Complex R)) ⥤ (J ⥤ Complex R) :=
  (Functor.whiskeringRight J _ _).obj (Mon.forget (Complex R))

/-- 概要：図式の忘却もモナド的右随伴。
方針：点ごとの reflexive coequalizer と同型反映へ Beck の判定を使う。
規約：元の自由随伴を図式へ持ち上げる。
使われ方：一般の余極限の存在。 -/
@[instance_reducible]
def diagramForgetMonadic (J : Type w) [Category.{v} J] :
    MonadicRightAdjoint (_root_.SerrePositivity.DGAlgebra.diagramForget (R := R) J) := by
  have : HasReflexiveCoequalizers (J ⥤ Mon (Complex R)) :=
    hasReflexiveCoequalizers_iff.1 inferInstance
  have : Monad.PreservesColimitOfIsReflexivePair (_root_.SerrePositivity.DGAlgebra.diagramForget (R := R) J) := {
    out {_ _} f g _ := by
      have : PreservesColimit
          (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ ofIsReflexivePair f g)
          (_root_.SerrePositivity.DGAlgebra.diagramForget (R := R) J) := inferInstance
      exact preservesColimit_of_iso_diagram (_root_.SerrePositivity.DGAlgebra.diagramForget (R := R) J)
        (inclusionWalkingReflexivePairOfIsReflexivePairIso f g) }
  exact Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms
    (_root_.SerrePositivity.DGAlgebra.freeForgetAdjunction.whiskerRight J)

attribute [local instance] _root_.SerrePositivity.DGAlgebra.diagramForgetMonadic

/-- 概要：底にある形の余極限は dg モノイドにも存在する。
方針：定数図式への右随伴性をモナド的忘却に沿って持ち上げる。
規約：忘却による一般の余極限保存は使わない。
使われ方：有限余極限と超限合成の存在。 -/
lemma hasColimitsOfShape (J : Type w) [Category.{v} J]
    [HasColimitsOfShape J (Complex R)] : HasColimitsOfShape J (Mon (Complex R)) := by
  let Q : Mon (Complex R) ⥤ (J ⥤ Mon (Complex R)) := Functor.const J
  have : (Functor.const J : Complex R ⥤ (J ⥤ Complex R)).IsRightAdjoint :=
    hasColimitsOfShape_iff_isRightAdjoint_const.1 inferInstance
  have : (Q ⋙ _root_.SerrePositivity.DGAlgebra.diagramForget (R := R) J).IsRightAdjoint := by
    let e : Q ⋙ _root_.SerrePositivity.DGAlgebra.diagramForget (R := R) J ≅ Mon.forget (Complex R) ⋙ Functor.const J := Iso.refl _
    exact ((Adjunction.ofIsRightAdjoint (Mon.forget (Complex R) ⋙ Functor.const J)).ofNatIsoRight
      e.symm).isRightAdjoint
  have : Q.IsRightAdjoint := isRightAdjoint_triangle_lift_monadic (_root_.SerrePositivity.DGAlgebra.diagramForget (R := R) J)
  exact hasColimitsOfShape_iff_isRightAdjoint_const.2 this

/-- 概要：元の dg モノイド圏の全小余極限。
方針：形ごとの構成を束ねる。
規約：係数環の宇宙の小図式に対する明示的なクラス値。
使われ方：実モデル構造の局所選択と小対象論法。 -/
lemma hasColimits : HasColimitsOfSize.{u, u} (Mon (Complex R)) where
  has_colimits_of_shape J _ := _root_.SerrePositivity.DGAlgebra.hasColimitsOfShape J

end SerrePositivity.DGAlgebra

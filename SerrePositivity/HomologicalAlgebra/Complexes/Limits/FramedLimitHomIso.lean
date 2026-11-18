module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitDerivedHomSource
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitHomNaturality

/-!
# 元の両変数上の導来 Hom の二変数関手同型

概要：BM 命題 4.1・Hovey §1.3 の導来 Hom 同値と両自然性を関手同型へ束ねる。
方針：同じ Hom 同値を各対象で使い、元の前合成・後合成の式を適用する。
規約：普通の局所化後の元の対象と射を使う。
使われ方：局所化圏全体への Hom 同型の降下。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.Opposite
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：定値図式からの局所化 Hom の二変数関手（Hovey §1.3）。
方針：同じ定値図式と図式局所化に coyoneda を合成する。
規約：元の始域に反変、元の終域図式に共変。
使われ方：導来 Hom 同型の左辺。 -/
def framedLimitRawLeftHom : (Complex A)ᵒᵖ ⥤ (K ⥤ (Complex A)) ⥤ Type (u + 1) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  let QD := (weakEquivalences (K ⥤ (Complex A))).Q
  exact (Functor.const K ⋙ QD).op ⋙ coyoneda ⋙
    (Functor.whiskeringLeft (K ⥤ (Complex A)) _ (Type (u + 1))).obj QD

/-- 概要：計算対象への局所化 Hom の二変数関手（Hovey §1.3）。
方針：元の複体局所化と同じ計算関手に coyoneda を合成する。
規約：同じ普通の局所化を用いる。
使われ方：導来 Hom 同型の右辺。 -/
def framedLimitRawRightHom : (Complex A)ᵒᵖ ⥤ (K ⥤ (Complex A)) ⥤ Type (u + 1) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let Q := (weakEquivalences (Complex A)).Q
  exact Q.op ⋙ coyoneda ⋙
    (Functor.whiskeringLeft (K ⥤ (Complex A)) _ (Type (u + 1))).obj
      (_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K ⋙ Q)

/-- 概要：元の両変数上で導来 Hom 同値は二変数関手の同型（Hovey §1.3）。
方針：同じ対象ごとの Hom 同値と元の両自然性を束ねる。
規約：別の Hom 同値を選ばない。
使われ方：前合成の充満忠実性による局所化圏全体への降下。 -/
def framedLimitRawHomIso : _root_.SerrePositivity.ComplexLimits.framedLimitRawLeftHom A K ≅ _root_.SerrePositivity.ComplexLimits.framedLimitRawRightHom A K := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  refine NatIso.ofComponents (fun Y => NatIso.ofComponents
    (fun F => (_root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K Y.unop F).toIso) ?_) ?_
  · intro F G g
    ext x
    exact _root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv_target A K _ g x
  · intro Y Z f
    ext F x
    exact _root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv_source A K f.unop F x

end SerrePositivity.ComplexLimits

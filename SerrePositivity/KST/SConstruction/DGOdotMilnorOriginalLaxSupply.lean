module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.OriginalInputLaxEquivalence
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCornerEvaluation

/-!
概要：D2 の元二脚の無条件全 lax 比較を、元 corner cone の接続口へ代入する。
方針：供給済みの gluing・fst・snd をそのまま使い、構成済みの corner 評価を固定する。
規約：元 cone の全比較だけを明示入力に残す。恒等二脚の存在は主張しない。
使われ方：d④② の元二脚入力と、続着する元 corner cone 比較の具体的接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：D2 の元二脚比較と同じ corner 評価を使う実 cone の残比較型。
方針：既存 withCone の全関手同型に無条件供給を代入する。
規約：存在証明ではない。使われ方：元 corner cone の残供給型。 -/
abbrev DGOdotMilnorSuppliedOriginalConeComparison := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorNativeLaxComparison R d).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxComparisonInput R d).gluing.hom ≫
        (exactLaxDifference (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotTargetFunctor R d) ≫ (dgOdotMilnorCornerEvaluation R d).hom)

/-- 概要：元二脚の存在引数を除去した、指定元 corner cone 入力。
方針：D2 の無条件三欄を既存 withCone に代入する。
規約：cone 全比較は明示入力。使われ方：d④② の供給済み元二脚の消費。 -/
def dgOdotMilnorOriginalLaxSupplyWithCone
    (c : DGOdotMilnorSuppliedOriginalConeComparison R d) :
    DGOdotMilnorOriginalLaxConeComparisonInput R d :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxComparisonInput R d).withCone R d c

/-- 概要：特殊化後の gluing は供給された元の全同値。
方針：構成の欄を回収する。規約：同値を選び直さない。
使われ方：後続の元二脚の指定辺照合。 -/
lemma dgOdotMilnorOriginalLaxSupplyWithCone_gluing
    (c : DGOdotMilnorSuppliedOriginalConeComparison R d) :
    (dgOdotMilnorOriginalLaxSupplyWithCone R d c).laxComparison.gluing =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalInputLaxEquivalence R d := rfl

/-- 概要：特殊化後の第一射影比較は供給された全関手同型。
方針：構成の欄を回収する。規約：元第一射影を保持。
使われ方：後続の指定第一脚照合。 -/
lemma dgOdotMilnorOriginalLaxSupplyWithCone_fst
    (c : DGOdotMilnorSuppliedOriginalConeComparison R d) :
    (dgOdotMilnorOriginalLaxSupplyWithCone R d c).laxComparison.fst =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalInputLaxEquivalence_fst R d := rfl

/-- 概要：特殊化後の第二射影比較は供給された全関手同型。
方針：構成の欄を回収する。規約：元第二射影を保持。
使われ方：後続の指定第二脚照合。 -/
lemma dgOdotMilnorOriginalLaxSupplyWithCone_snd
    (c : DGOdotMilnorSuppliedOriginalConeComparison R d) :
    (dgOdotMilnorOriginalLaxSupplyWithCone R d c).laxComparison.snd =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalInputLaxEquivalence_snd R d := rfl
end SerrePositivity.KST.SConstruction

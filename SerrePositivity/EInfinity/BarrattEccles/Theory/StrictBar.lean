module

public import SerrePositivity.HomotopicalAlgebra.Bar.StrictAdjunctionBar
public import SerrePositivity.EInfinity.BarrattEccles.OperadStructure
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FreeAlgebraAdjunction

/-!
# Barratt–Eccles の厳密な自由・忘却 bar

概要：HA §4.7.3 による経路 B の厳密な前段。
方針：構成済みの自由・忘却随伴を、一般の随伴の bar と追加退化へ代入する。
規約：実現・局所化との比較、入力の cofibrant 性は主張しない。
使われ方：BS-W16。③-b の橋の後に、自由比較を全代数へ延ばす。
verify 待機中の未検証下書き。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 実際の BE の自由・忘却随伴の余モナド。 -/
abbrev strictBarComonad := (operad A).freeAlgebraAdjunction.toComonad

/-- 任意の厳密な BE 代数に関して自然な、通常の単体圏上の bar 図式。 -/
abbrev strictBarFunctor : (operad A).Algebra ⥤ SimplicialObject (operad A).Algebra :=
  _root_.SerrePositivity.StrictAdjunctionBar.StrictAdjunctionBar.barFunctor (operad A).freeAlgebraAdjunction

/-- 同じ bar の増大を保つ全関手。 -/
abbrev strictBarAugmentedFunctor :
    (operad A).Algebra ⥤ SimplicialObject.Augmented (operad A).Algebra :=
  _root_.SerrePositivity.StrictAdjunctionBar.StrictAdjunctionBar.barAugmentedFunctor (operad A).freeAlgebraAdjunction

/-- 忘却後の、指定された同じ bar の増大。 -/
abbrev strictBarUnderlyingAugmented (X : (operad A).Algebra) :
    SimplicialObject.Augmented (Complex A) :=
  _root_.SerrePositivity.StrictAdjunctionBar.StrictAdjunctionBar.underlyingAugmented (operad A).freeAlgebraAdjunction X

/-- 忘却後の増大には、実際の自由・忘却随伴の単位による追加退化がある。 -/
abbrev strictBarUnderlyingExtraDegeneracy (X : (operad A).Algebra) :
    SimplicialObject.Augmented.ExtraDegeneracy (strictBarUnderlyingAugmented A X) :=
  _root_.SerrePositivity.StrictAdjunctionBar.StrictAdjunctionBar.underlyingExtraDegeneracy (operad A).freeAlgebraAdjunction X

/-- bar の零次の増大は、自由代数から元の代数への指定評価射。 -/
lemma strictBarAugmentation_zero (X : (operad A).Algebra) :
    ((strictBarAugmentedFunctor A).obj X).hom.app (Opposite.op ⦋0⦌) =
      X.evaluationHom := by
  change (operad A).freeAlgebraAdjunction.counit.app X ≫ 𝟙 X = X.evaluationHom
  have hc : (operad A).freeAlgebraAdjunction.counit.app X ≫ 𝟙 X =
      (operad A).freeAlgebraAdjunction.counit.app X := Category.comp_id _
  exact hc.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.freeAlgebraAdjunction_counit_app (operad A) X)

/-- 忘却後の零次の切断は、同じ Schur 自由代数の生成元包含。 -/
lemma strictBarUnderlyingSection_zero (X : (operad A).Algebra) :
    (strictBarUnderlyingExtraDegeneracy A X).s' = (operad A).schurUnit X.carrier :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.freeAlgebraAdjunction_unit_app _ _

end SerrePositivity.EInfinity.BarrattEccles

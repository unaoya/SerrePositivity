module
public import SerrePositivity.InfinityCategories.Core.FiniteLimitsColimits
public import SerrePositivity.InfinityCategories.Stable.OppositeDiagramReturn
public import SerrePositivity.InfinityCategories.Core.FiniteOppositeSSet

/-!
概要：有限極限から反対圏の同じ有限図式の余極限を構成する。
方針：非退化単体の反転同値と、元の図式を回収する二重反転を使う。
規約：元の圏の有限余極限は結論しない。使われ方：一般安定性判定の双対化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ有限図式と極限錐を反転して普遍余錐を得る。 -/
lemma hasColimit_op_of_hasFiniteLimits {X : SSet.{u}} [HasFiniteLimits X]
    {K : SSet.{u}} [K.Finite] (p : K ⟶ X.op) : HasColimit p := by
  let q : K.op ⟶ X := SSet.opFunctor.map p ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
  obtain ⟨c, hc⟩ := HasFiniteLimits.hasLimit (X := X) q
  let d := c.reverseCocone.restrict (SSet.opFunctorCompOpFunctorIso.app K).inv
  have hd : IsColimitCone d :=
    (isLimitCone_iff_reverseCocone_restrict c
      (SSet.opFunctorCompOpFunctorIso.app K).inv).mp hc
  have hp : (SSet.opFunctorCompOpFunctorIso.app K).inv ≫ SSet.opFunctor.map q = p :=
    oppositeDiagram_double_return p
  rw [← hp]
  exact ⟨d, hd⟩

/-- 同じ有限図式と極限錐を反転して普遍余錐を得る。 -/
instance hasFiniteColimits_op_of_hasFiniteLimits {X : SSet.{u}} [HasFiniteLimits X] :
    HasFiniteColimits X.op where
  hasColimit p := hasColimit_op_of_hasFiniteLimits p

end SerrePositivity.InfinityCategories

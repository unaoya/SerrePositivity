module

public import SerrePositivity.InfinityCategories.F2.Ind.TwistedElementsReconstructionPointed
public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityIdentityReconstruction

/-!
概要：元の恒等点復元射の pointed 成分は、同じ Tw 全体から取る恒等点に厳密に定値。
方針：二段の底変換を元へ戻し、Tw の恒等点上の第一射影を照合する。
規約：元の全 fiber パラメータを保ち、恒等点を選び直さない。
使われ方：native 密度評価の同じ区間持ち上げと canonical な普遍輸送の初期値の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
local notation "H" => twistedElementsHomDiagram p
local notation "Dx" => presheafDensityEvaluationDiagram F x
local notation "j" => twistedSourceElementsIdentityInclusion p x

/-- 元の恒等点復元射の pointed 成分は、元の canonical な恒等点に全高次で定値。 -/
lemma presheafDensityIdentityReconstruction_pointed :
    presheafDensityIdentityReconstruction F x ≫ pullback.fst pointedSpaceProjection Dx =
      SSet.const (canonicalYonedaPointedIdentity x).val := by
  change (SSet.uliftFunctor.{u + 1, u}).map j ≫
    (SSet.uliftFunctor.{u + 1, u}).map (presheafDensityEvaluationReconstruction F x) ≫
      smallLeftUnstraighteningPointedMap Dx = _
  rw [← smallLeftUnstraighteningPointedMap_naturality Dx H
    (presheafDensitySourceInclusion F x) (presheafDensitySourceInclusion_source F x),
    ← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
    Category.assoc j, presheafDensityEvaluationReconstruction_map,
    ← Category.assoc j, twistedSourceElementsComparison_identity,
    Functor.map_comp, Category.assoc, twistedElementsReconstruction_pointed,
    ← Category.assoc, ← Functor.map_comp]
  change (SSet.uliftFunctor.{u + 1, u}).map
    (twistedIdentityFiberInclusion p x ≫ pullback.fst (edgewiseRight C) p) ≫
      twistedArrowPointedDisplay C = _
  rw [twistedIdentityFiberInclusion, pullback.lift_fst]
  have hc : (SSet.uliftFunctor.{u + 1, u}).map
      (SSet.const (edgewiseIdentityPoint x) : vertexFiber p x ⟶ _) =
      SSet.const (ULift.up (edgewiseIdentityPoint x)) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  rw [hc, SSet.const_comp]
  apply congrArg SSet.const
  rw [canonicalYonedaPointedIdentity_eq_sourceDisplay]
  change _ = (twistedArrowPointedDisplay C).app (Opposite.op ⦋0⦌)
    (ULift.up ((pullback.fst (twistedArrowProjection C) (twistedArrowSourceInclusion x)).app
      (Opposite.op ⦋0⦌) (twistedArrowSourceIdentity x)))
  rw [twistedArrowSourceIdentity_fst]

end SerrePositivity.InfinityCategories.F2.Ind

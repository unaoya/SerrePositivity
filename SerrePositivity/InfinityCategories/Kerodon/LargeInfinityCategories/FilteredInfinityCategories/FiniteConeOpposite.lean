module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-! # 有限図式の錐条件の反転

概要：全有限図式が錐を持つ条件を、反転後の filtered ∞ 圏へ移す。
方針：非退化単体の反転で有限性を保ち、錐を反転して二重反転の同型で制限する。
規約：通常の圏の nerve に制限しない。使われ方：実 Verdier 分母添字の余 filtered 性。

対応節は Kerodon 9.1（Tag 05WY）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 非退化単体の反転は有限単体集合の有限性を保つ。 -/
lemma finiteSimplicialOpposite (K : SSet.{u}) [K.Finite] : K.op.Finite where
  finite := by
    let φ : K.op.N → K.N := fun s => N.mk (SSet.opObjEquiv s.simplex)
      ((SSet.opObjEquiv_mem_nonDegenerate_iff K s.simplex).mpr s.nonDegenerate)
    let ψ : K.N → K.op.N := fun s => N.mk (SSet.opObjEquiv.symm s.simplex)
      ((SSet.opObjEquiv_mem_nonDegenerate_iff K _).mp s.nonDegenerate)
    have hleft : Function.LeftInverse ψ φ := by
      intro s
      cases s using N.induction
      rfl
    exact Finite.of_injective φ hleft.injective

/-- 全ての有限図式に実錐があれば、反転した ∞ 圏は filtered。 -/
lemma isFilteredInfinity_op_of_finiteCones (X : SSet.{u}) [Quasicategory X]
    (h : ∀ {K : SSet.{u}} [K.Finite] (f : K ⟶ X), Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity X.op where
  cocone_nonempty {K} _ f := by
    let := finiteSimplicialOpposite K
    let g : K.op ⟶ X := SSet.opFunctor.map f ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
    obtain ⟨c⟩ := h g
    let c' := c.reverseCocone.restrict (SSet.opFunctorCompOpFunctorIso.app K).inv
    have he : (SSet.opFunctorCompOpFunctorIso.app K).inv ≫ SSet.opFunctor.map g = f := by
      dsimp [g]
      rw [Functor.map_comp]
      change (SSet.opFunctorCompOpFunctorIso.app K).inv ≫
        (SSet.opFunctor.map (SSet.opFunctor.map f) ≫
          SSet.opFunctor.map (SSet.opFunctorCompOpFunctorIso.app X).hom) = f
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.opFunctorCompOpFunctorIso_coherence]
      exact (congrArg (fun q => (SSet.opFunctorCompOpFunctorIso.app K).inv ≫ q)
        (SSet.opFunctorCompOpFunctorIso.hom.naturality f)).trans
          (Iso.inv_hom_id_assoc (SSet.opFunctorCompOpFunctorIso.app K) f)
    exact ⟨Eq.mp (congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) he) c'⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

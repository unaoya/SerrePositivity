module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleEdgeIntervalExtension
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLiftingIso
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse

/-!
概要：圏論的同値に対する右持ち上げから指定された可逆辺の持ち上げを得る。
方針：標的の指定辺を可逆区間へ厳密に延長し、その終点の包含に対して持ち上げる。
規約：持ち上げた辺の像と終点を厳密に保つ。
使われ方：一般の標的上の相対 Kan 比較の cartesian 輸送。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：単射な圏論的同値を右に持ち上げる射は終点指定の可逆辺を持ち上げる。
方針：指定辺を可逆区間へ延長して終点の包含を持ち上げ、元の標準区間へ制限する。
規約：標的 E のみ quasicategory とし、始域 D の充填性は別途要求しない。
使われ方：内部 Hom と変動する添字の fiber に可逆辺の持ち上げを供給する。 -/
lemma EquivalenceLifting.invertibleTargetLifting {D E : SSet.{u}}
    [Quasicategory E] {U : D ⟶ E} (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLifting U := by
  intro x e he ht
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanEquivalenceInterval_extension_of_invertibleEdge e he
  have hFt : F.app (Opposite.op ⦋0⦌)
      (nerveEquiv.symm (Codiscrete.mk (ULift.up true))) = U.app (Opposite.op ⦋0⦌) x := by
    have hf := congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ E ↦
      k.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) hF
    change F.app (Opposite.op ⦋0⦌)
      (nerveEquiv.symm (Codiscrete.mk (ULift.up true))) =
        e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) at hf
    have hte := congrArg SSet.yonedaEquiv ht
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] at hte
    have hev : e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        E.δ 0 (SSet.yonedaEquiv e) := by
      rw [← SSet.yonedaEquiv.symm_apply_apply e, SSet.yonedaEquiv_symm_app,
        Equiv.apply_symm_apply]
      have hv : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
          SimplexCategory.δ (0 : Fin 2) := by decide
      rw [hv]
      rfl
    exact hf.trans (hev.trans hte)
  have := hU (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint true) inferInstance
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_equivalenceIntervalPoint true)
  let sq : CommSq (SSet.const x : 𝟙_ SSet.{u} ⟶ D) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint true) U F :=
    ⟨by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint, SSet.const_comp, hFt]⟩
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalEdge ≫ sq.lift, ?_, ?_, ?_⟩
  · have hl := congrArg (fun k : 𝟙_ SSet.{u} ⟶ D ↦
      k.app (Opposite.op ⦋0⦌) PUnit.unit) sq.fac_left
    change sq.lift.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (nerveEquiv.symm (Codiscrete.mk (ULift.up true))) 0) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0 at hl
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at hl
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalEdge_one, SSet.const_comp, hl,
      SSet.yonedaEquiv_symm_zero]
  · rw [Category.assoc, sq.fac_right, hF]
  · have : KanComplex _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval.{u} :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isContractibleKan_codiscreteNerve (ULift.{u} Bool)).kanComplex
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalEdge.{u})) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _)
    have hl := hi.map sq.lift
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalEdge)).map
        ((truncation 2).map sq.lift)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalEdge ≫ sq.lift))).edge from
      (SSet.yonedaEquiv_comp _ _).symm)).1 hl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EquivalenceLifting (invertibleTargetLifting)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

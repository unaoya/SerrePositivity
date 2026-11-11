module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSuspensionCospanRestriction

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionGridSuspensionEvaluateShape_noninitial (a b : Fin 2) (hab : a ≠ 0 ∨ b ≠ 0)
    (v : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured (nerveEquiv
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionEvaluateShape a b).app (Opposite.op ⦋0⦌) v)) := by
  let i := (stdSimplex.objEquiv v.1).toOrderHom 0
  let j := (stdSimplex.objEquiv v.2).toOrderHom 0
  change 1 ≤ (if a = 0 then i.val else j.val + 2) +
    (if b = 0 then j.val else i.val + 2)
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not_intro ha)
    rw [ite_eq_left ha, ite_eq_right hb]
    omega
  · rw [ite_eq_right ha]
    split_ifs <;> omega

lemma excisionRawSuspensionFamily_replaced_evaluate {X : SSet.{u}}
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F))
    (a b : Fin 2) (hab : a ≠ 0 ∨ b ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionFamily (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b) =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionFamily F ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b) := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionFamily, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.curry_evaluation_vertex]
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionEvaluateShape a b ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionEvaluateShape a b ≫ F
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial_comp_of_noninitial c _
    (excisionGridSuspensionEvaluateShape_noninitial a b hab)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

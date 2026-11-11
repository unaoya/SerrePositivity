module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FullColimitReflection

/-!
概要：周囲の同じ全余錐を、その頂点が属する全部分圏へ厳密に持ち上げる。
方針：余錐の一点族を全部分 coslice へ持ち上げ、元の頂点として読む。
規約：同じ周囲の全余錐と脚を保持する。
使われ方：Ind 内の κ-filtered 余極限の構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
  (D : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}))
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι)) (hc : P c.vertex)
include hc

/-- 同じ周囲の余錐の頂点族は、指定した全部分圏の頂点条件を満たす。 -/
lemma fullCoconePoint_mem : ∀ a : (Δ[0] : SSet.{u}) _⦋0⦌,
    P (((SSet.yonedaEquiv.symm c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
      (D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι)).app (Opposite.op ⦋0⦌) a) := by
  intro a
  have ha : a = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.obj₀Equiv.injective
    change (_ : Fin 1) = _
    exact Subsingleton.elim _ _
  subst a
  change P ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection _).app (Opposite.op ⦋0⦌)
    ((SSet.yonedaEquiv.symm c).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0]))))
  rw [SSet.yonedaEquiv_symm_app_id]
  exact hc

/-- 元の全部分圏に持ち上げた、同じ全余錐。 -/
def fullCoconeLift : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D :=
  SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullCosliceLift P D (SSet.yonedaEquiv.symm c) (fullCoconePoint_mem P D c hc))

/-- 同じ持ち上げを周囲へ戻すと、元の全余錐そのもの。 -/
lemma fullCoconeLift_inclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι (fullCoconeLift P D c hc) = c := by
  have h := congrArg (fun f ↦ SSet.yonedaEquiv f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullCosliceLift_postcomp P D (SSet.yonedaEquiv.symm c) (fullCoconePoint_mem P D c hc))
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h

/-- 周囲の同じ余錐の余極限性は、その元の全部分圏への持ち上げでも成立する。 -/
lemma fullCoconeLift_isColimit (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (fullCoconeLift P D c hc) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isColimitCone_of_fullInclusion P
  rw [fullCoconeLift_inclusion]
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

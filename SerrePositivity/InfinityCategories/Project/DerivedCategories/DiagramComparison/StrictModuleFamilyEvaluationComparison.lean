module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictModuleCoherentFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictDiagramEvaluation

/-!
概要：全 HA 族の対角評価が、元の strict 図式の同じ有限射列の評価と一致することを示す。
方針：次数零で元の閉零合成を用い、非零次数の元の高次零成分を保持する。
規約：対象ごと・辺ごとの比較に切り下げず、全ての有限部分集合の成分を比較する。
使われ方：3b-3 R6、指定余錐族の下方図式の全高次単体の同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]
  {C : Type (u + 1)} [Category.{u} C]

/-- 元の strict 図式族の対角は、同じ射列を元の閉零圏で評価した全 HA 単体である。 -/
lemma strictModuleCoherentFamily_diagonal (T : C ⥤ (J ⥤ ModuleCategory A PUnit.{1}))
    {n : ℕ} (d : Fin (n + 1) ⥤ C) (s : (nerve J) _⦋n⦌) :
    ((strictModuleCoherentFamily A J T).orderedSimplexFamily d (ULift.up s)).diagonal =
      closedNerveSimplex
        ((strictDiagramEvaluation J (ModuleCategory A PUnit.{1})).app (Opposite.op ⦋n⦌)
          (d ⋙ T, ULift.up s)) := by
  apply Simplex.ext
  apply SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    have hab : a ≤ b := by
      rw [ha, hb]
      exact (I.isLeast_min' _).2 (I.max'_mem _)
    change compose A
        (closedHomEquiv A (RightModule A PUnit.{1}) _ _
          ((T.map (d.map (homOfLE hab))).app (s.obj b))).val
        (closedNerveHom ((T.obj (d.obj a)).map (s.map (homOfLE hab))) k) (add_zero k) =
      closedNerveHom (((T.obj (d.obj a)).map (s.map (homOfLE hab))) ≫
        (T.map (d.map (homOfLE hab))).app (s.obj b)) k
    by_cases hk0 : k = 0
    · subst hk0
      simp only [closedNerveHom_zero]
      exact (closedHom_comp _ _).symm
    · rw [closedNerveHom_of_ne _ _ hk0, closedNerveHom_of_ne _ _ hk0, compose_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

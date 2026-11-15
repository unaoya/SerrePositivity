module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.NerveInclusion
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentLowComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictCubeEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：元の複体の閉零圏のstrict nerveを、同じcoherent比較とdg nerve包含で照合する。
方針：同じ対象と閉零射、strict Homの定数単体からの高次成分を比較する。
規約：IS-W2 C05の既存構成の照合の証明分割。全単体の厳密等式。
使われ方：HA 1.2.4、元のstrict余単体図式と指定導来Tot錐の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 閉零圏の同じstrict nerveは、coherent比較の後で元のdg包含そのもの。 -/
theorem complexClosedNerve_coherentComparison :
    nerveToCoherent (ClosedCategory A (Complex A)) ≫
      coherentComparison (R := A) (D := Complex A) = closedNerveInclusion A (Complex A) := by
  apply NatTrans.ext
  funext d
  rcases d with ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  apply Simplex.ext
  refine SimplexData.ext ?_ ?_
  · funext i
    rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    have hamin : IsLeast (I : Set _) a := by
      rw [ha]
      exact I.isLeast_min' _
    have hbmax : IsGreatest (I : Set _) b := by
      rw [hb]
      exact I.isGreatest_max' _
    have hab : a < b := by
      have h := I.min'_lt_max'_of_card hI
      simpa only [← ha, ← hb] using h
    by_cases hc : I.card = 2
    · have hk0 : k = 0 := by omega
      cases hk0
      have hpair := Index.eq_pair hc hamin hbmax
      subst I
      change (coherentComparison.app _ (nerveToCoherent _ |>.app _ F)).edgeHom a b hab = _
      rw [coherentComparison_edgeHom]
      change standardTopEval _ _ 0
        (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
          (SimplicialCategory.homEquiv' _ _ (F.map (homOfLE hab.le))) 0) = _
      rw [standardTopEval_constant_zero, standardZeroEquiv_homEquiv]
      rfl
    · have hcard := coherentVertexInterior_card.{u} hamin hbmax hab
      have hdeg : k = -((coherentVertexInterior.{u} I a b).card : ℤ) := by omega
      change (coherentSimplexData (nerveToCoherent _ |>.app _ F)).hom I a b k hI ha hb hk = _
      rw [coherentSimplexData_hom_eq_componentAt _ I a b k hI ha hb hk hab hdeg]
      trans 0
      · cases hdeg
        exact coherentCubeComponent_orderDiagram_pos _ _ _ (by omega)
      · exact (SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne
          (F.map (homOfLE hab.le)) k (by omega)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

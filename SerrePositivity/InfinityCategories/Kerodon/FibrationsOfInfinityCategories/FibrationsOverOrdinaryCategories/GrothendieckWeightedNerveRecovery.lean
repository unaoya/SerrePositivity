module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveForward
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveInverseFunctor

/-!
概要：weighted係数から回収した射列のprefixは、元の同じ係数の射列に戻る。
方針：対象は係数の自然性、射はその同じ関手等式の射への評価で照合する。
規約：IS-W2 R03eの右往復の部分。元の係数と同じ底を保つ。
使われ方：厳密なweighted nerve比較の全単体での全射性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (s : weightedNerveSimplex (F ⋙ nerveFunctor) n)

/-- 逆射列の各prefixの対象は、元の同じ係数の対象になる。 -/
theorem grothWeightedPrefixFiber_inverse_obj (i : Fin (n+1)) (k : Fin (i.val+1)) :
    (grothWeightedPrefixFiber F (grothWeightedNerveInverseSimplex F s) i).obj k =
      (grothWeightedNerveFiberChain F s i).obj k := by
  exact grothWeightedNerveInverse_source F s
    (homOfLE (show grothWeightedPrefixIndex i k ≤ i from Nat.le_of_lt_succ k.isLt))

/-- 逆射列の各prefixは、元の同じ係数の全射列になる。 -/
theorem grothWeightedPrefixFiber_inverse (i : Fin (n+1)) :
    grothWeightedPrefixFiber F (grothWeightedNerveInverseSimplex F s) i =
      grothWeightedNerveFiberChain F s i := by
  refine CategoryTheory.Functor.ext (grothWeightedPrefixFiber_inverse_obj F s i) ?_
  intro k l f
  have hc := CategoryTheory.Functor.congr_hom
    (grothWeightedNerveFiberChain_naturality F s
      (homOfLE (show grothWeightedPrefixIndex i l ≤ i from Nat.le_of_lt_succ l.isLt))).symm
    (homOfLE (show grothWeightedNerveInverseIndex
      (homOfLE (show grothWeightedPrefixIndex i k ≤ grothWeightedPrefixIndex i l
        from leOfHom f)) ≤ Fin.last (grothWeightedPrefixIndex i l).val from leOfHom f))
  dsimp only [Functor.comp_map] at hc
  simp only [grothWeightedPrefixFiber, Functor.comp_map,
    SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transport,
    grothWeightedPrefixArrow, grothWeightedNerveInverseSimplex,
    grothWeightedNerveInverseMap, CostructuredArrow.homMk_left,
    CostructuredArrow.mk_hom_eq_self, Functor.map_comp, eqToHom_map, Category.assoc]
  rw [hc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 3

/-- 元のweighted単体からの逆射列を前へ送ると、同じ元の単体に戻る。 -/
theorem grothWeightedNerveSimplex_inverse :
    grothWeightedNerveSimplex F (grothWeightedNerveInverseSimplex F s) = s := by
  refine Sigma.ext (grothWeightedNerveInverseSimplex_base F s) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  change (SSet.yonedaEquiv (X := nerve (F.obj (s.1.obj i)))
    (n := SimplexCategory.mk i.val)).symm
      (grothWeightedPrefixFiber F (grothWeightedNerveInverseSimplex F s) i) = s.2.app i
  rw [grothWeightedPrefixFiber_inverse]
  exact (SSet.yonedaEquiv (X := nerve (F.obj (s.1.obj i)))
    (n := SimplexCategory.mk i.val)).symm_apply_apply _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

module

public import SerrePositivity.KST.LocalizingInvariants.InitialPrismTwoEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary

/-!
概要：第一成分とその像が始対象である lax pullback の頂点は第二射影に相対的に始対象。
方針：第一成分の境界を充填し、矢印の prism を両端固定で延長する。
規約：第二成分の始対象性は要求しない。使われ方：D 包含と第二射影の実随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma lax_snd_initialBoundary {C D E : SSet.{u}} (p : C ⟶ E) (q : D ⟶ E)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋0⦌)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q).app (Opposite.op ⦋0⦌) x))
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (p.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q).app (Opposite.op ⦋0⦌) x))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q) x := by
  intro n a b hfirst sq
  have hcfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q) =
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q).app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, hfirst, SSet.yonedaEquiv_symm_comp]
  obtain ⟨c, hcb⟩ := hc n (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q) hcfirst
  have hav : a.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm 0, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩ = x := by
    apply SSet.yonedaEquiv.symm.injective
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex, SSet.yonedaEquiv_symm_comp] using hfirst
  have hcv : c.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q).app (Opposite.op ⦋0⦌) x := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hcb (Opposite.op ⦋0⦌))
      ⟨stdSimplex.obj₀Equiv.symm 0, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩
    change c.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q).app _ (a.app _ _) at h
    rw [hav] at h
    exact h
  let H := uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q)
  have h₀ : (boundary (n + 1)).ι ≫ (c ≫ p) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry, ← Category.assoc,
      Category.assoc a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow_source, ← Category.assoc, hcb]
  have h₁ : (boundary (n + 1)).ι ≫ (b ≫ q) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow_target, ← Category.assoc]
    exact congrArg (fun f => f ≫ q) sq.w.symm
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((c ≫ p).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0)) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (p.app _ (c.app _ _))
    rw [hcv]
    exact hp
  obtain ⟨P, hPb, hP₀, hP₁⟩ := initial_prism_extend_two_endpoints n H (c ≫ p) (b ≫ q) h₀ h₁ hi
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift p q c b (curry P)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hP₀])
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hP₁])
  refine ⟨f, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_snd ..⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullback_hom_ext p q
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_arrow, ← curry_natural_left, hPb, curry_uncurry]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_fst, hcb]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_snd]
    exact sq.w.symm

end SerrePositivity.KST.LocalizingInvariants

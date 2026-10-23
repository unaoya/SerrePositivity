module

public import SerrePositivity.KST.LocalizingInvariants.InitialPrismTwoEndpoints
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackLift
public import SerrePositivity.InfinityCategories.Stable.RelativeInitialBoundary

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
    (x : (F2.laxPullback p q) _⦋0⦌)
    (hc : IsInitialVertex ((F2.laxPullbackFst p q).app (Opposite.op ⦋0⦌) x))
    (hp : IsInitialVertex (p.app (Opposite.op ⦋0⦌)
      ((F2.laxPullbackFst p q).app (Opposite.op ⦋0⦌) x))) :
    InitialBoundaryLifting (F2.laxPullbackSnd p q) x := by
  intro n a b hfirst sq
  have hcfirst : boundaryVertex n 0 ≫ (a ≫ F2.laxPullbackFst p q) =
      SSet.yonedaEquiv.symm ((F2.laxPullbackFst p q).app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, hfirst, SSet.yonedaEquiv_symm_comp]
  obtain ⟨c, hcb⟩ := hc n (a ≫ F2.laxPullbackFst p q) hcfirst
  have hav : a.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm 0, vertex_mem_boundary n 0⟩ = x := by
    apply SSet.yonedaEquiv.symm.injective
    simpa only [boundaryVertex, SSet.yonedaEquiv_symm_comp] using hfirst
  have hcv : c.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
      (F2.laxPullbackFst p q).app (Opposite.op ⦋0⦌) x := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hcb (Opposite.op ⦋0⦌))
      ⟨stdSimplex.obj₀Equiv.symm 0, vertex_mem_boundary n 0⟩
    change c.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
      (F2.laxPullbackFst p q).app _ (a.app _ _) at h
    rw [hav] at h
    exact h
  let H := uncurry (a ≫ F2.laxPullbackArrow p q)
  have h₀ : (boundary (n + 1)).ι ≫ (c ≫ p) = prismEndpoint 0 _ ≫ H := by
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry, ← Category.assoc,
      Category.assoc a, F2.laxPullbackArrow_source, ← Category.assoc, hcb]
  have h₁ : (boundary (n + 1)).ι ≫ (b ≫ q) = prismEndpoint 1 _ ≫ H := by
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry, Category.assoc,
      F2.laxPullbackArrow_target, ← Category.assoc]
    exact congrArg (fun f => f ≫ q) sq.w.symm
  have hi : IsInitialVertex ((c ≫ p).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0)) := by
    change IsInitialVertex (p.app _ (c.app _ _))
    rw [hcv]
    exact hp
  obtain ⟨P, hPb, hP₀, hP₁⟩ := initial_prism_extend_two_endpoints n H (c ≫ p) (b ≫ q) h₀ h₁ hi
  let f := F2.laxPullbackLift p q c b (curry P)
    (by rw [curry_evaluateFunctorAt_interval, hP₀])
    (by rw [curry_evaluateFunctorAt_interval, hP₁])
  refine ⟨f, ?_, F2.laxPullbackLift_snd ..⟩
  apply F2.laxPullback_hom_ext p q
  · rw [Category.assoc, F2.laxPullbackLift_arrow, ← curry_natural_left, hPb, curry_uncurry]
  · rw [Category.assoc, F2.laxPullbackLift_fst, hcb]
  · rw [Category.assoc, F2.laxPullbackLift_snd]
    exact sq.w.symm

end SerrePositivity.KST.LocalizingInvariants

module

public import SerrePositivity.KST.LocalizingInvariants.TerminalPrismTwoEndpoints
public import SerrePositivity.InfinityCategories.F2.LaxPullbackLift
public import SerrePositivity.InfinityCategories.Core.RelativeTerminalExtension

/-!
概要：第二成分とその像が終対象である lax pullback の頂点は第一射影に相対的に終対象。
方針：第二成分の境界を充填し、矢印の prism を両端固定で延長する。
規約：第一成分の終対象性は要求しない。使われ方：C 包含と第一射影の実随伴。
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

lemma lax_fst_terminalBoundary {C D E : SSet.{u}} (p : C ⟶ E) (q : D ⟶ E)
    (x : (F2.laxPullback p q) _⦋0⦌)
    (hd : IsTerminalVertex ((F2.laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x))
    (hq : IsTerminalVertex (q.app (Opposite.op ⦋0⦌)
      ((F2.laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x))) :
    TerminalBoundaryLifting (F2.laxPullbackFst p q) x := by
  intro n a b hlast sq
  have hdlast : boundaryVertex n (Fin.last (n + 1)) ≫ (a ≫ F2.laxPullbackSnd p q) =
      SSet.yonedaEquiv.symm ((F2.laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, hlast, SSet.yonedaEquiv_symm_comp]
  obtain ⟨d, hdb⟩ := hd n (a ≫ F2.laxPullbackSnd p q) hdlast
  have hav : a.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), vertex_mem_boundary n _⟩ = x := by
    apply SSet.yonedaEquiv.symm.injective
    simpa only [boundaryVertex, SSet.yonedaEquiv_symm_comp] using hlast
  have hdv : d.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) =
      (F2.laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hdb (Opposite.op ⦋0⦌))
      ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), vertex_mem_boundary n _⟩
    change d.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) =
      (F2.laxPullbackSnd p q).app _ (a.app _ _) at h
    rw [hav] at h
    exact h
  let H := uncurry (a ≫ F2.laxPullbackArrow p q)
  have h₀ : (boundary (n + 1)).ι ≫ (b ≫ p) = prismEndpoint 0 _ ≫ H := by
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry, Category.assoc,
      F2.laxPullbackArrow_source, ← Category.assoc]
    exact congrArg (fun f => f ≫ p) sq.w.symm
  have h₁ : (boundary (n + 1)).ι ≫ (d ≫ q) = prismEndpoint 1 _ ≫ H := by
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry, ← Category.assoc,
      Category.assoc a, F2.laxPullbackArrow_target, ← Category.assoc, hdb]
  have hi : IsTerminalVertex ((d ≫ q).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)))) := by
    change IsTerminalVertex (q.app _ (d.app _ _))
    rw [hdv]
    exact hq
  obtain ⟨P, hPb, hP₀, hP₁⟩ := terminal_prism_extend_two_endpoints n H (b ≫ p) (d ≫ q) h₀ h₁ hi
  let f := F2.laxPullbackLift p q b d (curry P)
    (by rw [curry_evaluateFunctorAt_interval, hP₀])
    (by rw [curry_evaluateFunctorAt_interval, hP₁])
  refine ⟨f, ?_, F2.laxPullbackLift_fst ..⟩
  apply F2.laxPullback_hom_ext p q
  · rw [Category.assoc, F2.laxPullbackLift_arrow, ← curry_natural_left, hPb, curry_uncurry]
  · rw [Category.assoc, F2.laxPullbackLift_fst]
    exact sq.w.symm
  · rw [Category.assoc, F2.laxPullbackLift_snd, hdb]

end SerrePositivity.KST.LocalizingInvariants

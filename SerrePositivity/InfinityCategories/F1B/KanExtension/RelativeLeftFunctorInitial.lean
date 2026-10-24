module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftFunctorBoundary
public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialBoundaryHom

/-!
概要：元の相対左 Kan 関手から出る実際の相対制限の写像空間を比較する。
方針：元と底を保つ境界延長から始点境界充填を得て、右 pinched 比較へ渡す。
規約：始点の関手だけに標準局所相対余極限条件を課す。
使われ方：元の相対左 Kan 関手の全部分圏からの制限の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：元の相対左 Kan 条件は元の関手制限の始点境界を充填する。
方針：最初の関手頂点を同定し、元と標的の図式を同時に保つ相対境界延長を使う。
規約：U は右持ち上げ条件を持ち、相手の境界頂点に普遍性は要求しない。
使われ方：元の相対左 Kan 関手から出る写像空間の制限の同値。 -/
lemma kanRelativeLeftFunctor_relative_initialBoundary {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (sr : internalHom.PullbackObjObj (δ) U)
    (H : C ⟶ D)
    (hcol : IsRelativeLeftKanExtendedFrom U δ H) :
    InitialBoundaryLifting sr.π (functorVertex H) := by
  intro n a b hfirst sq
  change (boundary (n + 1) : SSet.{u}) ⟶ (ihom (C)).obj D at a
  have had : a ≫ (pre (δ)).app D =
      (boundary (n + 1)).ι ≫ (b ≫ sr.fst) := by
    have h := congrArg (fun f ↦ f ≫ sr.fst) sq.w
    rw [Category.assoc, sr.π_fst, Category.assoc] at h
    exact h
  have hag : a ≫ (ihom (C)).map U =
      (boundary (n + 1)).ι ≫ (b ≫ sr.snd) := by
    have h := congrArg (fun f ↦ f ≫ sr.snd) sq.w
    rw [Category.assoc, sr.π_snd, Category.assoc] at h
    exact h
  have hdg : (b ≫ sr.fst) ≫ (ihom K).map U =
      (b ≫ sr.snd) ≫ (pre (δ)).app E := by
    have h := congrArg (fun f ↦ b ≫ f) sr.isPullback.w
    change b ≫ (sr.fst ≫ (ihom K).map U) =
      b ≫ (sr.snd ≫ (pre (δ)).app E) at h
    simpa only [Category.assoc] using h
  have hv := congrArg SSet.yonedaEquiv hfirst
  simp only [boundaryVertex, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hv
  have hH : (functorVertexEquiv (C) D).symm
      (a.app (Opposite.op ⦋0⦌)
        ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩) = H := by
    have hv' : a.app (Opposite.op ⦋0⦌)
        ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩ =
          functorVertex H := hv
    exact (congrArg ((functorVertexEquiv (C) D).symm) hv').trans
      ((functorVertexEquiv _ D).symm_apply_apply H)
  obtain ⟨f, hfA, hfd, hfg⟩ := exists_kanRelativeLeft_functor_relative_boundary_extension
    δ hδ U hU n a (b ≫ sr.fst) (b ≫ sr.snd) hdg had hag (by
      intro c
      exact (congrArg (fun L : C ⟶ D ↦
        IsRelativeColimitCone U (leftKanCanonicalCocone δ L c)) hH).mpr (hcol c))
  refine ⟨f, hfA, ?_⟩
  apply sr.hom_ext
  · rw [Category.assoc, sr.π_fst]
    exact hfd
  · rw [Category.assoc, sr.π_snd]
    exact hfg

/-- 概要：局所 U 余極限から出る相対写像空間の制限はホモトピー同値。
方針：相対制限の始点境界充填を右 pinched 写像空間の比較へ渡す。
規約：H の局所普遍性だけを使い、相手 G の普遍性は仮定しない。
使われ方：相対普遍図式全体からの制限の充満忠実性。 -/
lemma kanRelativeLeftFunctor_relative_pinchedHomMap_equivalence {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (sr : internalHom.PullbackObjObj (δ) U)
    (H G : C ⟶ D)
    (hcol : IsRelativeLeftKanExtendedFrom U δ H) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap sr.π (functorVertex H) (functorVertex G)) := by
  have : InnerFibration U := hU.innerFibration
  have : Quasicategory sr.pt := kanRelativeInternalHomTarget_quasicategory U _ sr
  have : Quasicategory
      ((internalHom.obj (Opposite.op (C))).obj D) :=
    inferInstanceAs (Quasicategory ((ihom (C)).obj D))
  exact SerrePositivity.InfinityCategories.F1B.pinchedHomMap_equivalence_of_initialBoundary _ _ _
    (kanRelativeLeftFunctor_relative_initialBoundary δ hδ U hU sr H hcol)

end SerrePositivity.InfinityCategories.F1B

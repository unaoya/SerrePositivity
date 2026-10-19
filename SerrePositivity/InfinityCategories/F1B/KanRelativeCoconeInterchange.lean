module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeHomInterchange
public import SerrePositivity.InfinityCategories.F1B.KanRelativeCoconeBoundary

/-!
概要：相対余錐と部分パラメータの比較の順序交換で、関手圏の相対余錐を判定する。
方針：始域と標的の同型で境界充填を移し、余錐の族を転置した余錐として読む。
規約：相対余錐の操作的な充填条件を用いる。
使われ方：境界を固定する関手 V′ の局所余錐の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：余錐の族を関手単体集合に値を取る一つの余錐へ転置する。
方針：uncurry の二因子を交換して再び curry する。
規約：図式は転置した射の左包含への制限として指定する。
使われ方：相対比較の順序交換後の頂点を余錐として表示する。 -/
def kanCoconeFamilyTranspose {A J D : SSet.{u}}
    (f : A ⟶ (ihom (join J (Δ[0] : SSet.{u}))).obj D) :
    JoinCocone (joinInl J (Δ[0] : SSet.{u}) ≫
      curry ((β_ A (join J (Δ[0] : SSet.{u}))).hom ≫ uncurry f)) :=
  ⟨curry ((β_ A (join J (Δ[0] : SSet.{u}))).hom ≫ uncurry f), rfl⟩

/-- 概要：指定部分の外の単体の始点の相対余錐条件は、転置後の関手圏の相対余錐条件を与える。
方針：相対関手の始点判定を二つの相対内部 Hom の順序交換で移す。
規約：射と単体集合に充填性は要求しない。
使われ方：部分パラメータを固定した局所相対余極限の判定。 -/
lemma kanRelativeCoconeLifting_relativeFunctor_of_first_vertices {A J D E : SSet.{u}}
    (U : D ⟶ E) (A₀ : A.Subcomplex) (sj : internalHom.PullbackObjObj A₀.ι U)
    (f : A ⟶ (ihom (join J (Δ[0] : SSet.{u}))).obj D)
    (hf : ∀ (m : ℕ) (s : A _⦋m + 1⦌), s ∉ A₀.obj (Opposite.op ⦋m + 1⦌) →
      KanRelativeCoconeLifting U (kanCoconeFamilyAt f (simplexFirstVertex s))) :
    KanRelativeCoconeLifting sj.π (kanCoconeFamilyTranspose f) := by
  let si := Functor.PullbackObjObj.ofHasPullback internalHom (joinInl J (Δ[0] : SSet.{u})) U
  let s := Functor.PullbackObjObj.ofHasPullback internalHom A₀.ι si.π
  let t := Functor.PullbackObjObj.ofHasPullback internalHom (joinInl J (Δ[0] : SSet.{u})) sj.π
  have hx : InitialBoundaryLifting s.π (functorVertex f) := by
    apply kanInitialBoundaryLifting_relativeFunctor_of_first_vertices A₀
      (kanRelativeCoconeRestriction J U) s f
    intro m a ha
    have h := hf m a ha
    dsimp only [KanRelativeCoconeLifting] at h
    rwa [kanCoconeFamilyAt_vertex] at h
  have h := kanInitialBoundaryLifting_relativeHom_interchange si sj s t (functorVertex f) hx
  rw [internalHomSwapIso_functorVertex] at h
  exact h

/-- 概要：最初の余錐の相対条件は、境界固定の関手に対する転置後の相対余錐条件を与える。
方針：境界外の標準単体の始点を最初の頂点に同定する。
規約：他のパラメータ頂点の余錐には普遍性を要求しない。
使われ方：Kerodon Proposition 7.3.6.7 の V′ に対する局所余錐の判定。 -/
lemma kanRelativeCoconeLifting_boundaryFunctor {J D E : SSet.{u}}
    (U : D ⟶ E) (n : ℕ) (sj : internalHom.PullbackObjObj (boundary n).ι U)
    (f : (Δ[n] : SSet.{u}) ⟶ (ihom (join J (Δ[0] : SSet.{u}))).obj D)
    (hf : KanRelativeCoconeLifting U
      (kanCoconeFamilyAt f (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))) :
    KanRelativeCoconeLifting sj.π (kanCoconeFamilyTranspose f) := by
  apply kanRelativeCoconeLifting_relativeFunctor_of_first_vertices U (boundary n) sj f
  intro m a ha
  rw [simplexFirstVertex_stdSimplex_of_notMem_boundary a ha]
  exact hf

/-- 概要：最初の余錐が余極限なら、転置した余錐は境界への制限に関して相対余錐の条件を満たす。
方針：終対象上の判定を相対内部 Hom の終対象表示と合わせる。
規約：D は quasicategory、余錐の添字 J は任意。
使われ方：通常の Kan 条件から境界固定の V′ の局所相対普遍性を得る。 -/
lemma kanRelativeCoconeLifting_pre_boundary_of_colimit {J D : SSet.{u}}
    [Quasicategory D] (n : ℕ)
    (f : (Δ[n] : SSet.{u}) ⟶ (ihom (join J (Δ[0] : SSet.{u}))).obj D)
    (hf : IsColimitCone
      (kanCoconeFamilyAt f (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))) :
    KanRelativeCoconeLifting ((pre (boundary n).ι).app D) (kanCoconeFamilyTranspose f) := by
  let U := stdSimplex.isTerminalObj₀.from D
  let sj := Functor.PullbackObjObj.ofIsTerminal internalHom (boundary n).ι U
    stdSimplex.isTerminalObj₀
  apply kanRelativeCoconeLifting_boundaryFunctor U n sj f
  exact (kanRelativeCoconeLifting_iff_isColimit_of_terminal U stdSimplex.isTerminalObj₀ _).2 hf

end SerrePositivity.InfinityCategories.F1B

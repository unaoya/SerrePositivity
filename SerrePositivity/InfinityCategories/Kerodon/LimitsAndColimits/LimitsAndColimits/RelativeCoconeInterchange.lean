module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeHomInterchange
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeCoconeBoundary

/-!
概要：相対余錐と部分パラメータの比較の順序交換で、関手圏の相対余錐を判定する。
方針：始域と標的の同型で境界充填を移し、余錐の族を転置した余錐として読む。
規約：相対余錐の操作的な充填条件を用いる。
使われ方：境界を固定する関手 V′ の局所余錐の普遍性。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：余錐の族を関手単体集合に値を取る一つの余錐へ転置する。
方針：uncurry の二因子を交換して再び curry する。
規約：図式は転置した射の左包含への制限として指定する。
使われ方：相対比較の順序交換後の頂点を余錐として表示する。 -/
def kanCoconeFamilyTranspose {A J D : SSet.{u}}
    (f : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J (Δ[0] : SSet.{u}) ≫
      curry ((β_ A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).hom ≫ uncurry f)) :=
  ⟨curry ((β_ A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).hom ≫ uncurry f), rfl⟩

/-- 概要：指定部分の外の単体の始点の相対余錐条件は、転置後の関手圏の相対余錐条件を与える。
方針：相対関手の始点判定を二つの相対内部 Hom の順序交換で移す。
規約：射と単体集合に充填性は要求しない。
使われ方：部分パラメータを固定した局所相対余極限の判定。 -/
lemma kanRelativeCoconeLifting_relativeFunctor_of_first_vertices {A J D E : SSet.{u}}
    (U : D ⟶ E) (A₀ : A.Subcomplex) (sj : internalHom.PullbackObjObj A₀.ι U)
    (f : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj D)
    (hf : ∀ (m : ℕ) (s : A _⦋m + 1⦌), s ∉ A₀.obj (Opposite.op ⦋m + 1⦌) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt f (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting sj.π (kanCoconeFamilyTranspose f) := by
  let si := Functor.PullbackObjObj.ofHasPullback internalHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J (Δ[0] : SSet.{u})) U
  let s := Functor.PullbackObjObj.ofHasPullback internalHom A₀.ι si.π
  let t := Functor.PullbackObjObj.ofHasPullback internalHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J (Δ[0] : SSet.{u})) sj.π
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting s.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanInitialBoundaryLifting_relativeFunctor_of_first_vertices A₀
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction J U) s f
    intro m a ha
    have h := hf m a ha
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting] at h
    rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt_vertex] at h
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanInitialBoundaryLifting_relativeHom_interchange si sj s t (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) hx
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_functorVertex] at h
  exact h

/-- 概要：最初の余錐の相対条件は、境界固定の関手に対する転置後の相対余錐条件を与える。
方針：境界外の標準単体の始点を最初の頂点に同定する。
規約：他のパラメータ頂点の余錐には普遍性を要求しない。
使われ方：Kerodon Proposition 7.3.6.7（Tag 030F） の V′ に対する局所余錐の判定。 -/
lemma kanRelativeCoconeLifting_boundaryFunctor {J D E : SSet.{u}}
    (U : D ⟶ E) (n : ℕ) (sj : internalHom.PullbackObjObj (boundary n).ι U)
    (f : (Δ[n] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj D)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt f (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting sj.π (kanCoconeFamilyTranspose f) := by
  apply kanRelativeCoconeLifting_relativeFunctor_of_first_vertices U (boundary n) sj f
  intro m a ha
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeInitial.simplexFirstVertex_stdSimplex_of_notMem_boundary a ha]
  exact hf

/-- 概要：最初の余錐が余極限なら、転置した余錐は境界への制限に関して相対余錐の条件を満たす。
方針：終対象上の判定を相対内部 Hom の終対象表示と合わせる。
規約：D は quasicategory、余錐の添字 J は任意。
使われ方：通常の Kan 条件から境界固定の V′ の局所相対普遍性を得る。 -/
lemma kanRelativeCoconeLifting_pre_boundary_of_colimit {J D : SSet.{u}}
    [Quasicategory D] (n : ℕ)
    (f : (Δ[n] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj D)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt f (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting ((pre (boundary n).ι).app D) (kanCoconeFamilyTranspose f) := by
  let U := stdSimplex.isTerminalObj₀.from D
  let sj := Functor.PullbackObjObj.ofIsTerminal internalHom (boundary n).ι U
    stdSimplex.isTerminalObj₀
  apply kanRelativeCoconeLifting_boundaryFunctor U n sj f
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeCoconeLifting_iff_isColimit_of_terminal U stdSimplex.isTerminalObj₀ _).2 hf

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

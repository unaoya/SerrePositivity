module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeInterchange
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeExtension

/-!
概要：指定した境界を保つ局所余錐の存在と、境界制限に関する相対普遍性。
方針：最初の境界頂点での条件から族を延長し、比較の順序交換で普遍性を移す。
規約：正次元の標準単体を使い、全境界頂点を厳密に固定する。
使われ方：Kerodon Proposition 7.3.6.7（Tag 030F） の局所持ち上げ問題の解。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：最初の余錐の相対条件から境界を固定した余錐の族と転置後の相対普遍性を構成する。
方針：相対骨格の始点条件で延長し、境界制限の相対余錐判定を適用する。
規約：元の図式と底の全余錐も同時に保持する。
使われ方：境界を固定する関手 V′ の局所相対余錐の存在。 -/
lemma exists_kanRelativeCocone_boundary_extension {J D E : SSet.{u}}
    (U : D ⟶ E) (n : ℕ) (sj : internalHom.PullbackObjObj (boundary (n + 1)).ι U)
    (a : (boundary (n + 1) : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj D)
    (d : (Δ[n + 1] : SSet.{u}) ⟶ (ihom J).obj D)
    (g : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj E)
    (h : d ≫ (ihom J).map U = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J E)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J D = (boundary (n + 1)).ι ≫ d)
    (hg : a ≫ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).map U = (boundary (n + 1)).ι ≫ g)
    (hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt a
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩)) :
    ∃ f : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj D,
      (boundary (n + 1)).ι ≫ f = a ∧
        f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction J U = pullback.lift d g h ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting sj.π (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanCoconeFamilyTranspose f) := by
  have hA : ∀ v : (Δ[n + 1] : SSet.{u}) _⦋0⦌,
      v ∈ (boundary (n + 1)).obj (Opposite.op ⦋0⦌) := by
    intro v
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv v)
    rwa [Equiv.symm_apply_apply] at h
  obtain ⟨H, hH, hHd, hHU⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_kanRelativeCocone_extension_of_first_vertices
    U (boundary (n + 1)) hA a d g h ha hg (by
      intro m s hs
      have he : (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s, hA _⟩ : (boundary (n + 1)) _⦋0⦌) =
          ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩ :=
        Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeInitial.simplexFirstVertex_stdSimplex_of_notMem_boundary s hs)
      rw [he]
      exact hfirst)
  obtain ⟨f, hfA, hfp⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCocone_lift_iff U (boundary (n + 1)).ι a d g h).2 ⟨H, hH, hHd, hHU⟩
  refine ⟨f, hfA, hfp, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_boundaryFunctor U (n + 1) sj f
  have hv : f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2))) =
      a.app (Opposite.op ⦋0⦌)
        ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩ := by
    exact congrArg (fun z ↦ z.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩) hfA
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting] at hfirst ⊢
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt_vertex, hv]
  rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt_vertex] at hfirst

/-- 概要：最初の境界余錐が余極限なら、境界を固定した延長と境界制限に関する相対普遍性を得る。
方針：終対象上の相対判定と、相対内部 Hom の終対象表示を使う。
規約：他の境界頂点の余錐に余極限性は要求しない。
使われ方：通常の Kan 条件から写像空間の制限定理へ進む局所充填。 -/
lemma exists_kanCocone_boundary_extension_of_first_colimit {J D : SSet.{u}}
    [Quasicategory D] (n : ℕ)
    (a : (boundary (n + 1) : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj D)
    (d : (Δ[n + 1] : SSet.{u}) ⟶ (ihom J).obj D)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J D = (boundary (n + 1)).ι ≫ d)
    (hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt a
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩)) :
    ∃ f : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj D,
      (boundary (n + 1)).ι ≫ f = a ∧ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J D = d ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting ((pre (boundary (n + 1)).ι).app D)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanCoconeFamilyTranspose f) := by
  let U := stdSimplex.isTerminalObj₀.from D
  let sj := Functor.PullbackObjObj.ofIsTerminal internalHom (boundary (n + 1)).ι U
    stdSimplex.isTerminalObj₀
  let g : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj Δ[0] :=
    curry (stdSimplex.isTerminalObj₀.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}) ⊗ Δ[n + 1]))
  obtain ⟨f, hfA, hfp, hf⟩ := exists_kanRelativeCocone_boundary_extension U n sj a d g
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIhom_terminal_hom_ext stdSimplex.isTerminalObj₀ _ _) ha
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIhom_terminal_hom_ext stdSimplex.isTerminalObj₀ _ _)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeCoconeLifting_iff_isColimit_of_terminal U stdSimplex.isTerminalObj₀ _).2 hfirst)
  refine ⟨f, hfA, ?_, hf⟩
  have h := congrArg (fun z ↦ z ≫
    pullback.fst ((ihom J).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J Δ[0])) hfp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction_fst, pullback.lift_fst] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

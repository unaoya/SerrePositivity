module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeKernelPair

/-! # 対称 span 全体の余錐空間とループ模型

概要：始対象へ向かう辺を二度使う span の余錐空間は、共通始点の余錐空間のループ模型と同値。
方針：全体の余錐空間の自己引き戻し表示と、可縮な枝のループ比較を合成する。
規約：比較は基点の選択を含む。使われ方：二枝交換をループの逆射へ移すための空間の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：辺の終点の始対象性はその Yoneda 表示での終点にも成り立つ。
方針：辺の終点への制限の式を Yoneda 同値で読む。
規約：値域の quasicategory 性は不要。使われ方：枝の可縮性の入力を指定終点で与える。 -/
lemma stableEdgeSimplex_target_initial {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (SSet.yonedaEquiv
      (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge)) := by
  have h := congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target f)
  simp only [Equiv.apply_symm_apply] at h
  exact h.symm ▸ hz

/-- 概要：対称 span の全体の余錐空間から共通始点の余錐空間のループ模型への比較。
方針：自己引き戻しの同型を枝の自己引き戻しのループ比較へ合成する。
規約：指定辺の終点の始対象性と枝の余錐の基点を使う。使われ方：交換作用のループ表示。 -/
def symmetricCoconeLoopComparison {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y).app (Opposite.op ⦋0⦌) e)
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y).app (Opposite.op ⦋0⦌) e) :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchKernelPairLoopComparison
    (SSet.yonedaEquiv.symm f.edge) (stableEdgeSimplex_target_initial f hz) y e

/-- 概要：対称 span 全体の余錐空間のループ比較は単体的ホモトピー同値。
方針：自己引き戻しとの同型とループ比較の同値性を合成する。
規約：X の安定性全体は不要。使われ方：Hom 表示と基点付きループ模型の空間そのものの比較。 -/
lemma symmetricCoconeLoopComparison_homotopyEquivalence
    {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (symmetricCoconeLoopComparison f hz y e) := by
  have h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y)).isQCatEquivalence
  have h₂ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchKernelPairLoopComparison_homotopyEquivalence
    (SSet.yonedaEquiv.symm f.edge) (stableEdgeSimplex_target_initial f hz) y e).isQCatEquivalence
  exact (h₁.comp h₂).isSimplicialHomotopyEquivalence

/-- 概要：対称 span の余錐空間の連結成分は共通始点余錐空間の基点の自己射と同値。
方針：自己引き戻しとの同型の π₀ と枝のループの Hom 同値を合成する。
規約：群構造との両立はこの定義だけでは主張しない。使われ方：二枝交換の逆射との比較。 -/
def symmetricCoconePiZeroLoopEquiv {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y) ≃
      ((SSet.HomotopyCategory.mk
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y).app (Opposite.op ⦋0⦌) e) :
          hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace
            (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge) y)) ⟶
        SSet.HomotopyCategory.mk
          ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y).app (Opposite.op ⦋0⦌) e)) :=
  (SSet.π₀Functor.mapIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y)).toEquiv.trans
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchKernelPairPiZeroLoopEquiv (SSet.yonedaEquiv.symm f.edge)
      (stableEdgeSimplex_target_initial f hz) y e)

/-- 概要：対称 span の π₀ の同値は実際のループ比較の π₀ への作用と一致する。
方針：比較射の合成と連結成分の合成の計算則を読む。
規約：固定した枝の基点を使う。使われ方：空間の比較と通常の射の照合。 -/
lemma symmetricCoconePiZeroLoopEquiv_eq_comparison
    {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    symmetricCoconePiZeroLoopEquiv f hz y e a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftPiZeroEquiv _ _ (SSet.mapπ₀ (symmetricCoconeLoopComparison f hz y e) a) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftPiZeroEquiv _ _ (SSet.mapπ₀
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchKernelPairLoopComparison (SSet.yonedaEquiv.symm f.edge)
      (stableEdgeSimplex_target_initial f hz) y e)
    (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom a)) = _
  rw [symmetricCoconeLoopComparison, SSet.mapπ₀_comp_apply]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

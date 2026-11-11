module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairSwapInverse
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeLoopComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeKernelPairSwap

/-! # 対称 span の二枝交換とループの逆射

概要：対称 span の余錐空間の二枝交換はループ比較で基点の自己射の逆射になる。
方針：余錐空間の自己引き戻し表示を通して一般の成分交換公式を適用する。
規約：群の逆射までの主張。使われ方：双積の加法との比較に先立つ交換の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：単体集合の同型の π₀ の同値との合成は包含射の π₀ で評価できる。
方針：同型からの型同値と同値の合成を、抽象的な同型に対して計算する。
規約：充填性の仮定は不要。使われ方：大きな幾何学的同型の定義展開を避ける。 -/
lemma stablePiZeroIsoTrans_apply {A B : SSet.{u}} (i : A ≅ B) {T : Type u}
    (q : SSet.π₀ B ≃ T) (a : SSet.π₀ A) :
    ((SSet.π₀Functor.mapIso i).toEquiv.trans q) a = q (SSet.mapπ₀ i.hom a) := rfl

/-- 概要：対称 span のループ同値の評価は自己引き戻しの同値の評価との合成。
方針：同値の合成の定義を読む。
規約：連結成分を指定する。使われ方：大きな比較定義を展開せず交換公式を転送する。 -/
lemma symmetricCoconePiZeroLoopEquiv_apply
    {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconePiZeroLoopEquiv f hz y e a =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchKernelPairPiZeroLoopEquiv (SSet.yonedaEquiv.symm f.edge)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEdgeSimplex_target_initial f hz) y e
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom a) :=
  stablePiZeroIsoTrans_apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y) _ a

/-- 概要：対称 span の余錐と交換された余錐のループの合成は恒等射。
方針：余錐空間と自己引き戻しの同型の交換可換性と一般のループ公式を合成する。
規約：X は quasicategory、枝の終点は始対象。使われ方：交換を逆射と同定する。 -/
lemma symmetricCoconePiZeroLoopEquiv_comp_swap
    {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconePiZeroLoopEquiv f hz y e a ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconePiZeroLoopEquiv f hz y e (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSwap f y) a) = 𝟙 _ := by
  rw [symmetricCoconePiZeroLoopEquiv_apply, symmetricCoconePiZeroLoopEquiv_apply,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso_swap_piZero]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairPiZeroLoopEquiv_comp_swap
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeMappingSpace_edge_isContractibleKan _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEdgeSimplex_target_initial f hz) y) e _

/-- 概要：対称 span のループ比較の値は可逆。
方針：余錐空間の Kan 性からホモトピー圏が亜群であることを使う。
規約：基点は枝の余錐の制限。使われ方：逆射の明示的な公式の型付け。 -/
instance symmetricCoconePiZeroLoopEquiv_isIso
    {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconePiZeroLoopEquiv f hz y e a) :=
  IsGroupoid.all_isIso (C := hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace
    (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge) y)) _

/-- 概要：対称 span の二枝交換はループ比較で逆射になる。
方針：交換された値との合成の恒等式を可逆な射で消去する。
規約：双積の加法の負号との一致はこの定理では主張しない。使われ方：懸垂交換の符号の証明。 -/
lemma symmetricCoconePiZeroLoopEquiv_swap
    {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconePiZeroLoopEquiv f hz y e (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSwap f y) a) =
      inv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconePiZeroLoopEquiv f hz y e a) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconePiZeroLoopEquiv f hz y e a)).1
  rw [symmetricCoconePiZeroLoopEquiv_comp_swap, IsIso.hom_inv_id]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

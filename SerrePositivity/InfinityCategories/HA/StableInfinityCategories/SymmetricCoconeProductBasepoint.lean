module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairProductBasepoint
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeLoopProductNaturality

/-! # 対称余錐空間のループ積の基点独立性

概要：全体の余錐空間に移したループ積は枝の基点に依存せず、終点輸送は任意の両端の基点で積を保つ。
方針：自己引き戻しの積の基点独立性を標準同型で移し、輸送された基点を任意の基点へ変える。
規約：枝の終点は始対象。使われ方：Hom 上の演算の後合成自然性を任意の基点の選択で述べる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：対称 span 全体の余錐空間の連結成分のループ積は枝の基点に依存しない。
方針：自己引き戻し表示の単射性で、一般のループ積の基点独立性へ帰着する。
規約：X は quasicategory、枝の終点は始対象。使われ方：Hom 表示へ移す演算の基点の自由な選択。 -/
lemma symmetricCoconeLoopProduct_basepoint {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e d : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (b c : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct f hz y e b c = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct f hz y d b c := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableMapPiZeroIso_injective (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y)
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct_kernelPair, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct_kernelPair]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairLoopProduct_basepoint _ _ e d _ _

/-- 概要：両枝と整合する終点輸送は、両端の任意の枝の基点で全体のループ積を保つ。
方針：輸送の像の基点での保存則と基点独立性を合成する。
規約：輸送の両枝との可換性は入力とする。使われ方：Hom の後合成自然性の基点条件を除く。 -/
lemma symmetricCoconeLoopProduct_transport_basepoints {X : SSet.{u}} [Quasicategory X]
    {x z : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z) {y₀ y₁ : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) y₀ y₁)
    (S : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge)) a)
    (T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm f.edge)) a)
    (U : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) a)
    (hT : T.map ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₁ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₀ ≫ S.map)
    (h₁ : U.map ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeFirst f y₁ = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeFirst f y₀ ≫ T.map)
    (h₂ : U.map ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSecond f y₁ = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSecond f y₀ ≫ T.map)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y₀) _⦋0⦌)
    (e' : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y₁) _⦋0⦌)
    (b c : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y₀)) :
    SSet.mapπ₀ U.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct f hz y₀ e b c) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct f hz y₁ e'
        (SSet.mapπ₀ U.map b) (SSet.mapπ₀ U.map c) := by
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct_transport f hz a S T U hT h₁ h₂ e b c).trans
    (symmetricCoconeLoopProduct_basepoint f hz y₁ (T.map.app (Opposite.op ⦋0⦌) e) e' _ _)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

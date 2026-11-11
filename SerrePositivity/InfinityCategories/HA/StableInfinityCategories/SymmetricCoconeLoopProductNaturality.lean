module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeLoopProduct

/-! # 対称余錐空間のループ積と終点輸送

概要：二枝と整合する終点輸送は、枝の基点をその像へ移すとループ積と単位を保つ。
方針：自己引き戻しの表示の可換性を使い、一般のループ積と対角の自然性へ帰着する。
規約：基点の独立性は別の義務。使われ方：Hom へ移す演算の後合成自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：両枝と整合する終点輸送は、枝の基点を像へ変えると全体のループ積を保つ。
方針：自己引き戻しへの π₀ の可換式と、可換正方形に対するループ積の自然性を使う。
規約：X は quasicategory、枝の終点は始対象。輸送の可換性を入力とする。
使われ方：余錐の Hom 表示上の演算に後合成の自然性を与える。 -/
lemma symmetricCoconeLoopProduct_transport {X : SSet.{u}} [Quasicategory X]
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
    (b c : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y₀)) :
    SSet.mapπ₀ U.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct f hz y₀ e b c) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct f hz y₁ (T.map.app (Opposite.op ⦋0⦌) e)
        (SSet.mapπ₀ U.map b) (SSet.mapπ₀ U.map c) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableMapPiZeroIso_injective (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y₁)
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeTransport_kernelPair_piZero f a S T U hT h₁ h₂,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct_kernelPair, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopProduct_kernelPair,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeTransport_kernelPair_piZero f a S T U hT h₁ h₂,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeTransport_kernelPair_piZero f a S T U hT h₁ h₂]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairLoopProduct_naturality
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₀)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₁) T.map S.map hT
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeMappingSpace_edge_isContractibleKan _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEdgeSimplex_target_initial f hz) y₀)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeMappingSpace_edge_isContractibleKan _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEdgeSimplex_target_initial f hz) y₁) e _ _

/-- 概要：両枝と整合する終点輸送は枝の対角から得る単位を像の基点の単位へ送る。
方針：自己引き戻しの表示の可換性と対角の自然性を使う。
規約：値域の充填性や枝の終点の始対象性は不要。使われ方：零射との比較での単位の自然性。 -/
lemma symmetricCoconeLoopUnit_transport {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) {y₀ y₁ : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) y₀ y₁)
    (S : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge)) a)
    (T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm f.edge)) a)
    (U : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) a)
    (hT : T.map ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₁ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₀ ≫ S.map)
    (h₁ : U.map ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeFirst f y₁ = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeFirst f y₀ ≫ T.map)
    (h₂ : U.map ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSecond f y₁ = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSecond f y₀ ≫ T.map)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y₀) _⦋0⦌) :
    SSet.mapπ₀ U.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopUnit f y₀ e) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopUnit f y₁ (T.map.app (Opposite.op ⦋0⦌) e) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableMapPiZeroIso_injective (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y₁)
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeTransport_kernelPair_piZero f a S T U hT h₁ h₂,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopUnit_kernelPair, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopUnit_kernelPair,
    ← SSet.mapπ₀_comp_apply, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairDiagonal_map, SSet.mapπ₀_comp_apply, SSet.mapπ₀_mk]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

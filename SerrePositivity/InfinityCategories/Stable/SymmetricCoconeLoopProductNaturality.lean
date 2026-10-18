module
public import SerrePositivity.InfinityCategories.Stable.SymmetricCoconeLoopProduct

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
namespace SerrePositivity.InfinityCategories

/-- 概要：両枝と整合する終点輸送は、枝の基点を像へ変えると全体のループ積を保つ。
方針：自己引き戻しへの π₀ の可換式と、可換正方形に対するループ積の自然性を使う。
規約：X は quasicategory、枝の終点は始対象。輸送の可換性を入力とする。
使われ方：余錐の Hom 表示上の演算に後合成の自然性を与える。 -/
lemma symmetricCoconeLoopProduct_transport {X : SSet.{u}} [Quasicategory X]
    {x z : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (hz : IsInitialVertex z) {y₀ y₁ : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) y₀ y₁)
    (S : LeftFibrationFiberTransport
      (sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge)) a)
    (T : LeftFibrationFiberTransport (sliceUnderProjection (SSet.yonedaEquiv.symm f.edge)) a)
    (U : LeftFibrationFiberTransport (sliceUnderProjection (edgeSpan f f)) a)
    (hT : T.map ≫ coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₁ =
      coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₀ ≫ S.map)
    (h₁ : U.map ≫ symmetricCoconeFirst f y₁ = symmetricCoconeFirst f y₀ ≫ T.map)
    (h₂ : U.map ≫ symmetricCoconeSecond f y₁ = symmetricCoconeSecond f y₀ ≫ T.map)
    (e : (coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y₀) _⦋0⦌)
    (b c : SSet.π₀ (coconeMappingSpace (edgeSpan f f) y₀)) :
    SSet.mapπ₀ U.map (symmetricCoconeLoopProduct f hz y₀ e b c) =
      symmetricCoconeLoopProduct f hz y₁ (T.map.app (Opposite.op ⦋0⦌) e)
        (SSet.mapπ₀ U.map b) (SSet.mapπ₀ U.map c) := by
  apply stableMapPiZeroIso_injective (symmetricCoconeKernelPairIso f y₁)
  rw [symmetricCoconeTransport_kernelPair_piZero f a S T U hT h₁ h₂,
    symmetricCoconeLoopProduct_kernelPair, symmetricCoconeLoopProduct_kernelPair,
    symmetricCoconeTransport_kernelPair_piZero f a S T U hT h₁ h₂,
    symmetricCoconeTransport_kernelPair_piZero f a S T U hT h₁ h₂]
  exact kanKernelPairLoopProduct_naturality
    (coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₀)
    (coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₁) T.map S.map hT
    (coconeMappingSpace_edge_isContractibleKan _ (stableEdgeSimplex_target_initial f hz) y₀)
    (coconeMappingSpace_edge_isContractibleKan _ (stableEdgeSimplex_target_initial f hz) y₁) e _ _

/-- 概要：両枝と整合する終点輸送は枝の対角から得る単位を像の基点の単位へ送る。
方針：自己引き戻しの表示の可換性と対角の自然性を使う。
規約：値域の充填性や枝の終点の始対象性は不要。使われ方：零射との比較での単位の自然性。 -/
lemma symmetricCoconeLoopUnit_transport {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) {y₀ y₁ : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) y₀ y₁)
    (S : LeftFibrationFiberTransport
      (sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge)) a)
    (T : LeftFibrationFiberTransport (sliceUnderProjection (SSet.yonedaEquiv.symm f.edge)) a)
    (U : LeftFibrationFiberTransport (sliceUnderProjection (edgeSpan f f)) a)
    (hT : T.map ≫ coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₁ =
      coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₀ ≫ S.map)
    (h₁ : U.map ≫ symmetricCoconeFirst f y₁ = symmetricCoconeFirst f y₀ ≫ T.map)
    (h₂ : U.map ≫ symmetricCoconeSecond f y₁ = symmetricCoconeSecond f y₀ ≫ T.map)
    (e : (coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y₀) _⦋0⦌) :
    SSet.mapπ₀ U.map (symmetricCoconeLoopUnit f y₀ e) =
      symmetricCoconeLoopUnit f y₁ (T.map.app (Opposite.op ⦋0⦌) e) := by
  apply stableMapPiZeroIso_injective (symmetricCoconeKernelPairIso f y₁)
  rw [symmetricCoconeTransport_kernelPair_piZero f a S T U hT h₁ h₂,
    symmetricCoconeLoopUnit_kernelPair, symmetricCoconeLoopUnit_kernelPair,
    ← SSet.mapπ₀_comp_apply, kanKernelPairDiagonal_map, SSet.mapπ₀_comp_apply, SSet.mapπ₀_mk]
  rfl

end SerrePositivity.InfinityCategories

module
public import SerrePositivity.InfinityCategories.Stable.SymmetricCoconeEndpointTransport
public import SerrePositivity.InfinityCategories.Stable.KanKernelPairMap

/-! # 対称余錐空間の終点輸送と自己引き戻し表示

概要：両枝と可換な全体の輸送は、自己引き戻し表示で枝の輸送が誘導する写像に一致する。
方針：自己引き戻しの両射影で照合し、その等号を連結成分へ移す。
規約：輸送を指定すれば充填性の仮定は不要。使われ方：ループ積の終点輸送への自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：対称 span 全体の輸送は自己引き戻しの同型を介して枝の輸送の誘導射となる。
方針：両射影で全体と枝の可換性を使う。
規約：三つの輸送とその可換式を入力とする。使われ方：ループ積の自然性の始域の変更。 -/
lemma symmetricCoconeTransport_kernelPair {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) {y₀ y₁ : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) y₀ y₁)
    (S : LeftFibrationFiberTransport
      (sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge)) a)
    (T : LeftFibrationFiberTransport (sliceUnderProjection (SSet.yonedaEquiv.symm f.edge)) a)
    (U : LeftFibrationFiberTransport (sliceUnderProjection (edgeSpan f f)) a)
    (hT : T.map ≫ coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₁ =
      coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₀ ≫ S.map)
    (h₁ : U.map ≫ symmetricCoconeFirst f y₁ = symmetricCoconeFirst f y₀ ≫ T.map)
    (h₂ : U.map ≫ symmetricCoconeSecond f y₁ = symmetricCoconeSecond f y₀ ≫ T.map) :
    U.map ≫ (symmetricCoconeKernelPairIso f y₁).hom =
      (symmetricCoconeKernelPairIso f y₀).hom ≫
        kanKernelPairMap (coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₀)
          (coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₁) T.map S.map hT := by
  apply pullback.hom_ext
  · rw [Category.assoc, symmetricCoconeKernelPairIso_hom_fst, Category.assoc,
      kanKernelPairMap_fst, ← Category.assoc, symmetricCoconeKernelPairIso_hom_fst]
    exact h₁
  · rw [Category.assoc, symmetricCoconeKernelPairIso_hom_snd, Category.assoc,
      kanKernelPairMap_snd, ← Category.assoc, symmetricCoconeKernelPairIso_hom_snd]
    exact h₂

/-- 概要：全体と自己引き戻しの輸送の可換性は連結成分でも成り立つ。
方針：実際の射の等号を連結成分の合成則で移す。
規約：輸送の可換性の前提は実際の射で与える。使われ方：ループ積を π₀ 上で照合する。 -/
lemma symmetricCoconeTransport_kernelPair_piZero {X : SSet.{u}} {x z : X _⦋0⦌}
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
    (b : SSet.π₀ (coconeMappingSpace (edgeSpan f f) y₀)) :
    SSet.mapπ₀ (symmetricCoconeKernelPairIso f y₁).hom (SSet.mapπ₀ U.map b) =
      SSet.mapπ₀ (kanKernelPairMap (coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₀)
        (coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y₁) T.map S.map hT)
          (SSet.mapπ₀ (symmetricCoconeKernelPairIso f y₀).hom b) := by
  rw [← SSet.mapπ₀_comp_apply, symmetricCoconeTransport_kernelPair f a S T U hT h₁ h₂,
    SSet.mapπ₀_comp_apply]

end SerrePositivity.InfinityCategories

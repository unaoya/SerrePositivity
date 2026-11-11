module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeKernelPair

/-! # 対称余錐空間の交換と自己引き戻しの成分交換

概要：全体の余錐空間の自己引き戻し表示は、二枝交換を二成分の交換へ移す。
方針：比較同型の両射影を計算し、引き戻しの一意性を使う。
規約：実際の単体的な射の等号。使われ方：ループ模型で二枝交換を逆射として読む。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：自己引き戻し表示の第一成分は第一枝への制限。
方針：引き戻しの標準比較同型の第一射影の計算を使う。
規約：辺の表示変更を含む。使われ方：成分交換の計算。 -/
lemma symmetricCoconeKernelPairIso_hom_fst {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeFirst f y :=
  IsPullback.isoPullback_hom_fst _

/-- 概要：自己引き戻し表示の第二成分は第二枝への制限。
方針：標準比較同型の第二射影を計算する。
規約：辺の表示変更を含む。使われ方：成分交換の計算。 -/
lemma symmetricCoconeKernelPairIso_hom_snd {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSecond f y :=
  IsPullback.isoPullback_hom_snd _

/-- 概要：対称余錐空間の二枝交換は自己引き戻しの二成分交換に一致する。
方針：二つの射影で、枝への作用と引き戻しの対称性を照合する。
規約：値域の充填性は不要。使われ方：余錐空間の交換とループ反転の比較を自己引き戻しへ帰着する。 -/
lemma symmetricCoconeKernelPairIso_swap {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSwap f y ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom ≫
        (pullbackSymmetry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, symmetricCoconeKernelPairIso_hom_fst,
      pullbackSymmetry_hom_comp_fst, symmetricCoconeKernelPairIso_hom_snd,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSwap_first]
  · simp only [Category.assoc, symmetricCoconeKernelPairIso_hom_snd,
      pullbackSymmetry_hom_comp_snd, symmetricCoconeKernelPairIso_hom_fst,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSwap_second]

/-- 概要：余錐空間と自己引き戻しの連結成分の同型も二つの交換作用と可換。
方針：実際の単体的な射の等号を π₀ に移す。
規約：ループ模型の逆射への作用はまだ含めない。使われ方：ループ反転の計算の始域の変更。 -/
lemma symmetricCoconeKernelPairIso_swap_piZero {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSwap f y) a) =
      SSet.mapπ₀ (pullbackSymmetry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)).hom
          (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom a) := by
  rw [← SSet.mapπ₀_comp_apply, symmetricCoconeKernelPairIso_swap, SSet.mapπ₀_comp_apply]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

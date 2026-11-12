module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
概要：標準単体の最初の頂点の包含の left anodyne 性。
方針：点を左から join した空部分複体の包含を、空 join と標準単体の同型で移す。
規約：最初の頂点は零、宇宙は係数と同じ。
使われ方：Kerodon Lemma 4.3.7.8（Tag 0196）、Theorem 5.3.5.7（Tag 037Q） の有限鎖の尾部への拡張。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：点を左から join した対象への左頂点の包含は left anodyne。
方針：空部分複体の単射を点と join し、空の右 join の単位同型で前合成する。
規約：右因子 K は任意。
使われ方：Kerodon Lemma 4.3.7.8（Tag 0196）、錐の始点からの包含。 -/
lemma joinPoint_inl_leftAnodyne (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.cancel_left_of_respectsIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso (Δ[0] : SSet.{u}) K).inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (⊥ : K.Subcomplex).ι)).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne.joinPoint_mono_leftAnodyne (⊥ : K.Subcomplex).ι)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.joinEmptyIso_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp] using h

/-- 概要：標準単体の最初の頂点の包含。
方針：零頂点を Yoneda 同値で零単体からの射にする。
規約：n=0 も同じ定義を使う。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の辺を尾部へ貼る共通頂点。 -/
def scaffoldFirstVertex (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
  SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))

/-- 概要：標準単体の最初の頂点の包含は単射。
方針：始域の各次数の単体の一意性を使う。
規約：終域の次元は任意。
使われ方：Kerodon Example 4.3.6.5（Tag 0235）、join の相対境界に必要な単射性。 -/
instance scaffoldFirstVertex_mono (n : ℕ) : Mono (scaffoldFirstVertex.{u} n) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨d⟩⟩
  rw [mono_iff_injective]
  intro x y _
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  omega

/-- 概要：標準単体の最初の頂点の包含は left anodyne。
方針：零次元は恒等射、正次元は左頂点の join への包含を標準単体の同型で移す。
規約：全ての次元を扱う。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の辺と尾部から全体への inner anodyne な拡張。 -/
lemma scaffoldFirstVertex_leftAnodyne (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (scaffoldFirstVertex.{u} n) := by
  cases n with
  | zero =>
    have he : scaffoldFirstVertex.{u} 0 = 𝟙 Δ[0] := by
      apply SSet.yonedaEquiv.injective
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      omega
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.id_mem _
  | succ n =>
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.cancel_right_of_respectsIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[n]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 n).hom).mpr
        (joinPoint_inl_leftAnodyne Δ[n])
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl_vertex] at h
    have h' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (scaffoldFirstVertex.{u} (0 + n + 1)) := h
    exact Eq.mp (congrArg (fun k : ℕ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (scaffoldFirstVertex.{u} k))
      (by omega : 0 + n + 1 = n + 1)) h'

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianInnerHornPullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.InnerAnodyneAdjointComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.SSetPullbackAdjoint

/-!
概要：cocartesian fibration に沿う任意の inner anodyne 射の pullback は前合成同値。
方針：生成ホーンの幾何学的な比較を通常の依存積の随伴で全 inner anodyne 射へ拡張する。
規約：底の quasicategory 性も随伴の存在の追加仮定も要求しない。
使われ方：Kerodon Lemma 5.3.6.6（Tag 02RK）、表現空間の制限の trivial Kan 性。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：任意の pullback 表示で内ホーンの cocartesian fibration に沿う逆像は前合成同値。
方針：標準 pullback の比較から普遍同型で移す。
規約：全空間側へ向かう射を比較する。
使われ方：slice の pullback 関手の生成ホーンでの作用。 -/
lemma cocartesianFibration_innerHorn_isPullback_isPrecompositionEquivalence
    {P E : SSet.{u}} (n : ℕ) (k : Fin (n + 1)) (h0 : 0 < k) (hn : k < Fin.last n)
    (p : E ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (i : P ⟶ E) (a : P ⟶ (horn n k : SSet.{u}))
    (hs : IsPullback i a p (horn n k).ι) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i := by
  rw [← hs.isoPullback_hom_fst]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso hs.isoPullback).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianFibration_innerHorn_pullback_isPrecompositionEquivalence n k h0 hn p)

/-- 概要：内ホーンの生成元の任意の pullback 表示に前合成同値性を移す。
方針：生成元の構成子で標準ホーンに戻す。
規約：底 D は生成元の標的で指定される。
使われ方：依存積の随伴を使う一般化の入力。 -/
lemma cocartesianFibration_innerHornInclusion_isPullback_isPrecompositionEquivalence
    {P E A D : SSet.{u}} (f : A ⟶ D) (hf : innerHornInclusions f)
    (p : E ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (i : P ⟶ E) (a : P ⟶ A)
    (hs : IsPullback i a p f) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i := by
  rcases hf with ⟨k, h0, hn⟩
  exact cocartesianFibration_innerHorn_isPullback_isPrecompositionEquivalence _ k h0 hn p i a hs

/-- 概要：cocartesian fibration の通常の slice の pullback は内ホーンを前合成同値に送る。
方針：射の自然性の四角形が pullback であることと生成ホーンの比較を使う。
規約：slice の対象は任意の単体集合上の図式。
使われ方：全 inner anodyne 射への持ち上げ性による移送。 -/
lemma cocartesianFibration_overPullback_innerHorn_isPrecompositionEquivalence {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] {A D : Over B} (i : A ⟶ D)
    (hi : innerHornInclusions i.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map i) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullbackSymmetry D.hom p).hom :=
    ⟨MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations (pullbackSymmetry D.hom p).hom⟩
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration
      ((pullbackSymmetry D.hom p).hom ≫ pullback.snd p D.hom) := inferInstance
  rw [pullbackSymmetry_hom_comp_snd] at hc
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (pullback.fst D.hom p) := hc
  exact cocartesianFibration_innerHornInclusion_isPullback_isPrecompositionEquivalence i.left hi
    (pullback.fst D.hom p) _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackProjection_isPullback p i)

/-- 概要：cocartesian fibration に沿う inner anodyne 射の pullback は前合成同値。
方針：通常の pullback の右随伴を構成済みの依存積から取り、生成ホーンの結果を移す。
規約：全ての底・全空間は任意の単体集合で、追加の instance 仮定はない。
使われ方：Kerodon Lemma 5.3.6.6（Tag 02RK） の一般版、Lemma 5.6.8.10 (2)。 -/
lemma cocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence
    {E A B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (f : A ⟶ B) (hf : innerAnodyneExtensions f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pullback.fst p f) := by
  have : (Over.pullback p).IsLeftAdjoint := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalSSetPullback_isLeftAdjoint p
  have : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).IsLeftAdjoint :=
    inferInstanceAs ((Over.pullback p ⋙ Over.forget E).IsLeftAdjoint)
  let i : Over.mk f ⟶ Over.mk (𝟙 B) := Over.homMk f (by simp)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.innerAnodyne_leftAdjoint_isPrecompositionEquivalence
    (Adjunction.ofIsLeftAdjoint (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p))
    (fun j hj ↦
      cocartesianFibration_overPullback_innerHorn_isPrecompositionEquivalence p j hj) i hf
  have hc := h.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (asIso (pullback.snd (𝟙 B) p)))
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map i ≫ pullback.snd (𝟙 B) p =
      pullback.snd f p := by
    exact pullback.lift_snd _ _ _
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map i ≫ pullback.snd (𝟙 B) p) at hc
  rw [he] at hc
  have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (pullbackSymmetry p f)).comp hc
  rw [pullbackSymmetry_hom_comp_snd] at hs
  exact hs

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

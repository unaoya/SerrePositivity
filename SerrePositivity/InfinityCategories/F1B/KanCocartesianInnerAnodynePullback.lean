module

public import SerrePositivity.InfinityCategories.F1B.KanCocartesianInnerHornPullback
public import SerrePositivity.InfinityCategories.F1.InnerAnodyneAdjointComparison
public import SerrePositivity.InfinityCategories.F1B.SSetPullbackAdjoint

/-!
概要：cocartesian fibration に沿う任意の inner anodyne 射の pullback は前合成同値。
方針：生成ホーンの幾何学的な比較を通常の依存積の随伴で全 inner anodyne 射へ拡張する。
規約：底の quasicategory 性も随伴の存在の追加仮定も要求しない。
使われ方：Kerodon Lemma 5.3.6.6、表現空間の制限の trivial Kan 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：任意の pullback 表示で内ホーンの cocartesian fibration に沿う逆像は前合成同値。
方針：標準 pullback の比較から普遍同型で移す。
規約：全空間側へ向かう射を比較する。
使われ方：slice の pullback 関手の生成ホーンでの作用。 -/
lemma kanCocartesianFibration_innerHorn_isPullback_isPrecompositionEquivalence
    {P E : SSet.{u}} (n : ℕ) (k : Fin (n + 1)) (h0 : 0 < k) (hn : k < Fin.last n)
    (p : E ⟶ (Δ[n] : SSet.{u})) [CocartesianFibration p]
    (i : P ⟶ E) (a : P ⟶ (horn n k : SSet.{u}))
    (hs : IsPullback i a p (horn n k).ι) : IsPrecompositionEquivalence i := by
  rw [← hs.isoPullback_hom_fst]
  exact (isPrecompositionEquivalence_of_iso hs.isoPullback).comp
    (kanCocartesianFibration_innerHorn_pullback_isPrecompositionEquivalence n k h0 hn p)

/-- 概要：内ホーンの生成元の任意の pullback 表示に前合成同値性を移す。
方針：生成元の構成子で標準ホーンに戻す。
規約：底 D は生成元の標的で指定される。
使われ方：依存積の随伴を使う一般化の入力。 -/
lemma kanCocartesianFibration_innerHornInclusion_isPullback_isPrecompositionEquivalence
    {P E A D : SSet.{u}} (f : A ⟶ D) (hf : innerHornInclusions f)
    (p : E ⟶ D) [CocartesianFibration p] (i : P ⟶ E) (a : P ⟶ A)
    (hs : IsPullback i a p f) : IsPrecompositionEquivalence i := by
  rcases hf with ⟨k, h0, hn⟩
  exact kanCocartesianFibration_innerHorn_isPullback_isPrecompositionEquivalence _ k h0 hn p i a hs

/-- 概要：cocartesian fibration の通常の slice の pullback は内ホーンを前合成同値に送る。
方針：射の自然性の四角形が pullback であることと生成ホーンの比較を使う。
規約：slice の対象は任意の単体集合上の図式。
使われ方：全 inner anodyne 射への持ち上げ性による移送。 -/
lemma kanCocartesianFibration_overPullback_innerHorn_isPrecompositionEquivalence {E B : SSet.{u}}
    (p : E ⟶ B) [CocartesianFibration p] {A D : Over B} (i : A ⟶ D)
    (hi : innerHornInclusions i.left) :
    IsPrecompositionEquivalence ((overPullbackUnderlying p).map i) := by
  have : LeftFibration (pullbackSymmetry D.hom p).hom :=
    ⟨MorphismProperty.of_isIso leftFibrations (pullbackSymmetry D.hom p).hom⟩
  have hc : CocartesianFibration
      ((pullbackSymmetry D.hom p).hom ≫ pullback.snd p D.hom) := inferInstance
  rw [pullbackSymmetry_hom_comp_snd] at hc
  have : CocartesianFibration (pullback.fst D.hom p) := hc
  exact kanCocartesianFibration_innerHornInclusion_isPullback_isPrecompositionEquivalence i.left hi
    (pullback.fst D.hom p) _ _ (overPullbackProjection_isPullback p i)

/-- 概要：cocartesian fibration に沿う inner anodyne 射の pullback は前合成同値。
方針：通常の pullback の右随伴を構成済みの依存積から取り、生成ホーンの結果を移す。
規約：全ての底・全空間は任意の単体集合で、追加の instance 仮定はない。
使われ方：Kerodon Lemma 5.3.6.6 の一般版、Lemma 5.6.8.10 (2)。 -/
lemma kanCocartesianFibration_pullback_innerAnodyne_isPrecompositionEquivalence
    {E A B : SSet.{u}} (p : E ⟶ B) [CocartesianFibration p]
    (f : A ⟶ B) (hf : innerAnodyneExtensions f) :
    IsPrecompositionEquivalence (pullback.fst p f) := by
  have : (Over.pullback p).IsLeftAdjoint := cofinalSSetPullback_isLeftAdjoint p
  have : (overPullbackUnderlying p).IsLeftAdjoint :=
    inferInstanceAs ((Over.pullback p ⋙ Over.forget E).IsLeftAdjoint)
  let i : Over.mk f ⟶ Over.mk (𝟙 B) := Over.homMk f (by simp)
  have h := innerAnodyne_leftAdjoint_isPrecompositionEquivalence
    (Adjunction.ofIsLeftAdjoint (overPullbackUnderlying p))
    (fun j hj ↦
      kanCocartesianFibration_overPullback_innerHorn_isPrecompositionEquivalence p j hj) i hf
  have hc := h.comp (isPrecompositionEquivalence_of_iso (asIso (pullback.snd (𝟙 B) p)))
  have he : (overPullbackUnderlying p).map i ≫ pullback.snd (𝟙 B) p =
      pullback.snd f p := by
    exact pullback.lift_snd _ _ _
  change IsPrecompositionEquivalence
    ((overPullbackUnderlying p).map i ≫ pullback.snd (𝟙 B) p) at hc
  rw [he] at hc
  have hs := (isPrecompositionEquivalence_of_iso (pullbackSymmetry p f)).comp hc
  rw [pullbackSymmetry_hom_comp_snd] at hs
  exact hs

end SerrePositivity.InfinityCategories

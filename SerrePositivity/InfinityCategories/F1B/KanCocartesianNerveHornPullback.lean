module

public import SerrePositivity.InfinityCategories.F1.ReplacementInnerHorn
public import SerrePositivity.InfinityCategories.F1B.KanScaffoldArbitraryBaseChange

/-!
概要：strict replacement の内ホーンの逆像の比較を実際の cocartesian fibration へ移す。
方針：scaffold 比較とその底変換の同値性を二対三則で消去する。
規約：内ホーン自体は quasicategory と仮定しない。
使われ方：Kerodon Lemma 5.3.6.6、表現空間の inner anodyne 制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：部分複体の逆像の通常の四角形は pullback。
方針：各次数で元と所属証明の組を一意に回収する。
規約：射の充填性は不要。
使われ方：部分複体による逆像の表示と標準 pullback の同定。 -/
lemma kanSubcomplexInverseImage_isPullback {E B : SSet.{u}} (p : E ⟶ B) (A : B.Subcomplex) :
    IsPullback (A.fromPreimage p) (A.preimage p).ι A.ι p := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · intro x y h
    exact Subtype.ext h.2
  · intro a e h
    have he : p.app d e ∈ A.obj d := by rw [← h]; exact a.property
    exact ⟨⟨e, he⟩, Subtype.ext h.symm, rfl⟩

/-- 概要：逆像部分複体の包含の前合成同値性を標準 pullback の射影へ移す。
方針：pullback の標準同型を消去する。
規約：射影は全空間 E への第二射影。
使われ方：replacement の内ホーンのセル分解を pullback の比較に渡す。 -/
lemma kanIsPrecompositionEquivalence_pullback_snd_of_subcomplexInverseImage
    {E B : SSet.{u}} (p : E ⟶ B) (A : B.Subcomplex)
    (h : IsPrecompositionEquivalence (A.preimage p).ι) :
    IsPrecompositionEquivalence (pullback.snd A.ι p) := by
  let hp := kanSubcomplexInverseImage_isPullback p A
  have hh : hp.isoPullback.hom ≫ pullback.snd A.ι p = (A.preimage p).ι :=
    hp.isoPullback_hom_snd
  rw [← hh] at h
  exact (isPrecompositionEquivalence_of_iso hp.isoPullback).cancel_left h

/-- 概要：replacement の部分底への制限が前合成同値なら実際の cocartesian fibration の制限も同値。
方針：universal scaffold の元の比較と底変換した比較を消去する。
規約：部分底 A は任意の単体集合の部分複体でよい。
使われ方：Kerodon §5.3.6、strict な模型からの内ホーンの逆像の比較。 -/
lemma kanCocartesianFibration_subcomplex_pullback_isPrecompositionEquivalence_of_replacement
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (A : (nerve C).Subcomplex)
    (hA : IsPrecompositionEquivalence
      (pullback.snd A.ι
        (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)))) :
    IsPrecompositionEquivalence (pullback.snd A.ι p) := by
  have h := hA.comp (kanUniversalScaffold_isPrecompositionEquivalence p)
  have he := overPullbackMap_snd
    (Over.homMk
      (U := Over.mk (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)))
      (V := Over.mk p) (kanUniversalScaffold p) (kanUniversalScaffold_projection p)) (Over.mk A.ι)
  change _ ≫ pullback.snd A.ι p =
    pullback.snd A.ι (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)) ≫
      kanUniversalScaffold p at he
  rw [← he] at h
  exact (kanUniversalScaffold_overPullback_isPrecompositionEquivalence p A.ι).cancel_left h

/-- 概要：有限鎖の nerve 上の cocartesian fibration の内ホーンの逆像の射影は前合成同値。
方針：replacement の逆像の inner anodyne 性を scaffold で移す。
規約：全空間の小ささ以外の追加の選択や同値仮定を要求しない。
使われ方：Kerodon Lemma 5.3.6.6 の生成ホーンの場合。 -/
lemma kanCocartesianFibration_nerveHorn_pullback_isPrecompositionEquivalence (n : ℕ)
    (k : Fin (n + 1)) (h0 : 0 < k) (hn : k < Fin.last n) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 1)))) [CocartesianFibration p] :
    IsPrecompositionEquivalence (pullback.snd (replacementNerveHorn n k).ι p) := by
  apply kanCocartesianFibration_subcomplex_pullback_isPrecompositionEquivalence_of_replacement p
  apply kanIsPrecompositionEquivalence_pullback_snd_of_subcomplexInverseImage
  exact isPrecompositionEquivalence_of_innerAnodyne _
    (replacementNerveHorn_preimage_innerAnodyne n k h0 hn (kanCocartesianStrictTransportDiagram p))

end SerrePositivity.InfinityCategories

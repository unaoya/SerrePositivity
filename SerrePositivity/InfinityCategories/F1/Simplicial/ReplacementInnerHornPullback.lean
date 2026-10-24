module

public import SerrePositivity.InfinityCategories.Core.SubcomplexInverseImageComparison

public import SerrePositivity.InfinityCategories.F1.Simplicial.ReplacementInnerHorn
public import SerrePositivity.InfinityCategories.F1.Scaffold.LeftScaffoldArbitraryBaseChange

/-!
概要：strict replacement の内ホーンの逆像の比較を実際の left fibration へ移す。
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

/-- 概要：replacement の部分底への制限が前合成同値なら実際の left fibration の制限も同値。
方針：universal scaffold の元の比較と底変換した比較を消去する。
規約：部分底 A は任意の単体集合の部分複体でよい。
使われ方：Kerodon §5.3.6、strict な模型からの内ホーンの逆像の比較。 -/
lemma leftFibration_subcomplex_pullback_isPrecompositionEquivalence_of_replacement
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (A : (nerve C).Subcomplex)
    (hA : IsPrecompositionEquivalence
      (pullback.snd A.ι (simplicialReplacementProjection (leftStrictTransportDiagram p)))) :
    IsPrecompositionEquivalence (pullback.snd A.ι p) := by
  have h := hA.comp (universalScaffold_isPrecompositionEquivalence p)
  have he := overPullbackMap_snd
    (Over.homMk (U := Over.mk (simplicialReplacementProjection (leftStrictTransportDiagram p)))
      (V := Over.mk p) (universalScaffold p) (universalScaffold_projection p)) (Over.mk A.ι)
  change _ ≫ pullback.snd A.ι p =
    pullback.snd A.ι (simplicialReplacementProjection (leftStrictTransportDiagram p)) ≫
      universalScaffold p at he
  rw [← he] at h
  exact (universalScaffold_overPullback_isPrecompositionEquivalence p A.ι).cancel_left h

/-- 概要：有限鎖の nerve 上の left fibration の内ホーンの逆像の射影は前合成同値。
方針：replacement の逆像の inner anodyne 性を scaffold で移す。
規約：全空間の小ささ以外の追加の選択や同値仮定を要求しない。
使われ方：Kerodon Lemma 5.3.6.6 の生成ホーンの場合。 -/
lemma leftFibration_nerveHorn_pullback_isPrecompositionEquivalence (n : ℕ)
    (k : Fin (n + 1)) (h0 : 0 < k) (hn : k < Fin.last n) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 1)))) [LeftFibration p] :
    IsPrecompositionEquivalence (pullback.snd (replacementNerveHorn n k).ι p) := by
  apply leftFibration_subcomplex_pullback_isPrecompositionEquivalence_of_replacement p
  apply isPrecompositionEquivalence_pullback_snd_of_subcomplexInverseImage
  exact isPrecompositionEquivalence_of_innerAnodyne _
    (replacementNerveHorn_preimage_innerAnodyne n k h0 hn (leftStrictTransportDiagram p))

end SerrePositivity.InfinityCategories

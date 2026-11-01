module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.MappingPrecompositionRetraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PushoutInternalHomPullback
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyRetractionTests
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestDetection

/-!
# 境界に右持ち上げ性を持つ射の単射に沿うpushoutは局所化で可逆となる

## 概要
境界に右持ち上げ性を持つ射の単射に沿うpushoutは局所化で可逆となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。
[棚卸し m0454][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0454
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Push out a boundary-right map along an arbitrary mono

The internal-Hom square is the actual Kan pullback of a strong deformation
retract. Unit-valued postcomposition classes recover the original Kan
tests. No source or target of the original square is assumed Kan.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.MonoRightPushoutEquivalence
variable {A B C P : SSet.{v}} (p : A ⟶ B)
  (hp : (MorphismProperty.monomorphisms SSet.{v}).rlp p)
  (j : A ⟶ C) [Mono j] (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout p j u g)

include hp sq in
lemma tests : KanTestDetection.Tests g := by
  obtain ⟨s, hs⟩ := MonoRightLiftingContraction.exists_section p hp
  obtain ⟨H, hH⟩ := MonoRightLiftingContraction.exists_vertical_contraction p hp s hs
  intro K hK
  have : Fibration (terminal.from K) := (SSet.modelCategoryQuillen.fibration_iff _).mpr hK
  have : SSet.KanComplex K := (isFibrant_iff K).mpr inferInstance
  have hq : SSet.modelCategoryQuillen.J.rlp ((MonoidalClosed.pre j).app K) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  obtain ⟨r, hr, V, _⟩ := KanPullbackDeformation.exists_retraction
    ((MonoidalClosed.pre p).app K) ((MonoidalClosed.pre s).app K)
    (MappingPrecompositionRetraction.retraction p s hs K)
    (MappingPrecompositionRetraction.homotopy p s H K)
    (MappingPrecompositionRetraction.fixed p s H hH K)
    ((MonoidalClosed.pre j).app K) hq ((MonoidalClosed.pre g).app K)
    ((MonoidalClosed.pre u).app K) (PushoutInternalHomPullback.isPullback sq K).flip
  exact HomotopyRetractionTests.pre_bijective_of_restriction_post g
    (HomotopyRetractionTests.post_bijective _ r hr V (𝟙_ SSet.{v}))

include hp sq in
/-- 境界に右持ち上げ性を持つ射の単射に沿うpushoutは局所化で可逆となる。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map g) :=
  (KanTestDetection.anodyneQ_isIso_iff_tests g).mpr (tests p hp j u g sq)

end SerrePositivity.SimplicialModel.MonoRightPushoutEquivalence

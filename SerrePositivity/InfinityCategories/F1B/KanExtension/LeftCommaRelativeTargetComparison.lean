module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaUniversalFamily
public import SerrePositivity.InfinityCategories.Core.RelativeInternalHomTrivialFibration

/-!
概要：元の包含の相対関手制限と comma の相対 join の相対制限の標的の比較。
方針：元の図式を comma の射影で引き戻し、標的図式を普遍図式への前合成で移す。
規約：二つの相対内部 Hom の pullback の選択を明示する。
使われ方：元と標的の図式を同時に固定する族の可換正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：元の関手と標的の図式の整合する組を comma 側の整合する組へ写す。
方針：前合成と後合成の自然性で二成分の一致を示し、pullback へ持ち上げる。
規約：U に充填性を要求しない。
使われ方：元の相対制限と相対 join の相対制限の標的の比較。 -/
def kanLeftCommaRelativeTargetMap {K C D E : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj (relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C)) U) :
    s.pt ⟶ t.pt :=
  t.isPullback.lift (s.fst ≫ (pre (kanLeftCommaSource δ)).app D)
    (s.snd ≫ kanLeftCommaUniversalFamily δ E) (by
      have hs : s.fst ≫ (ihom K).map U = s.snd ≫ (pre δ).app E := s.isPullback.w
      calc
        (s.fst ≫ (pre (kanLeftCommaSource δ)).app D) ≫
            (ihom (kanLeftComma δ)).map U =
          (s.fst ≫ (ihom K).map U) ≫ (pre (kanLeftCommaSource δ)).app E := by
            rw [Category.assoc, pre_comm_ihom_map, ← Category.assoc]
        _ = (s.snd ≫ (pre δ).app E) ≫ (pre (kanLeftCommaSource δ)).app E := by rw [hs]
        _ = (s.snd ≫ kanLeftCommaUniversalFamily δ E) ≫
            (pre (relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C))).app E := by
          rw [Category.assoc, Category.assoc, kanLeftCommaUniversalFamily_inl,
            pre_map, NatTrans.comp_app])

/-- 概要：標的比較の第一成分は元の図式の comma 射影による引き戻し。
方針：pullback の持ち上げの第一成分を計算する。
規約：厳密な単体写像の等式。
使われ方：元の δ による制限との両立の検査。 -/
lemma kanLeftCommaRelativeTargetMap_fst {K C D E : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj (relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C)) U) :
    kanLeftCommaRelativeTargetMap δ U s t ≫ t.fst =
      s.fst ≫ (pre (kanLeftCommaSource δ)).app D := t.isPullback.lift_fst _ _ _

/-- 概要：標的比較の第二成分は標的の図式の普遍図式への前合成。
方針：pullback の持ち上げの第二成分を計算する。
規約：元の U による像をすべての次数で保つ。
使われ方：標的の図式も指定した相対制限の比較。 -/
lemma kanLeftCommaRelativeTargetMap_snd {K C D E : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj (relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C)) U) :
    kanLeftCommaRelativeTargetMap δ U s t ≫ t.snd =
      s.snd ≫ kanLeftCommaUniversalFamily δ E := t.isPullback.lift_snd _ _ _

/-- 概要：元の相対制限と comma 側の相対制限は普遍的な族の比較と可換。
方針：標的の二成分へ合成し、元の図式の制限と U の後合成の自然性を照合する。
規約：頂点だけでなく、相対内部 Hom の単体写像の可換性を示す。
使われ方：相対写像空間の制限定理を元の関手圏へ戻すための可換正方形。 -/
lemma kanLeftCommaUniversalFamily_relativeRestriction {K C D E : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj (relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C)) U) :
    kanLeftCommaUniversalFamily δ D ≫ t.π = s.π ≫ kanLeftCommaRelativeTargetMap δ U s t := by
  apply t.hom_ext
  · rw [Category.assoc, t.π_fst]
    change kanLeftCommaUniversalFamily δ D ≫
      (pre (relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C))).app D =
        (s.π ≫ kanLeftCommaRelativeTargetMap δ U s t) ≫ t.fst
    rw [kanLeftCommaUniversalFamily_inl, Category.assoc, kanLeftCommaRelativeTargetMap_fst,
      ← Category.assoc, s.π_fst]
    change (pre (kanLeftCommaSource δ ≫ δ)).app D =
      (pre δ).app D ≫ (pre (kanLeftCommaSource δ)).app D
    rw [pre_map, NatTrans.comp_app]
  · rw [Category.assoc, t.π_snd]
    change kanLeftCommaUniversalFamily δ D ≫
      (ihom (relativeJoin (kanLeftCommaProjection δ) (𝟙 C))).map U =
        (s.π ≫ kanLeftCommaRelativeTargetMap δ U s t) ≫ t.snd
    rw [kanLeftCommaUniversalFamily_postcomp, Category.assoc,
      kanLeftCommaRelativeTargetMap_snd, ← Category.assoc, s.π_snd]
    rfl

end SerrePositivity.InfinityCategories.F1B

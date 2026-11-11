module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableEnrichedCategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：presentable 圏と保存関手の全 ∞ 圏 Pr^L・Pr^R を定義する。
方針：保存関手圏の豊穣構造を core に移送し、その単体的圏の coherent nerve を取る。
規約：対象の単体は u+1、Pr 自体の単体は u+2。右側は accessible な極限保存関手を使う。
使われ方：Pr^L と Pr^R の双対性、Pr^L の小極限。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：関手同値を豊穣 Hom に持つ保存関手の単体的圏。
方針：core による豊穣構造の移送の後、単位からの射を通常の射にする。
規約：元の全高次関手同値を保持する。
使われ方：Pr の coherent nerve の入力。 -/
def PresentableCoreCategory (left : Bool) :=
  ForgetEnrichment SSet.{u + 1}
    (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u + 1}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableEnrichedObjects.{u} left))

instance presentableCoreCategory_category (left : Bool) :
    Category.{u + 1} (PresentableCoreCategory.{u} left) := by
  dsimp [PresentableCoreCategory]
  infer_instance

instance presentableCoreCategory_simplicialCategory (left : Bool) :
    SimplicialCategory (PresentableCoreCategory.{u} left) := by
  dsimp [PresentableCoreCategory]
  infer_instance

instance presentableCoreCategory_sHom_kanComplex (left : Bool)
    (C D : PresentableCoreCategory.{u} left) :
    KanComplex (SimplicialCategory.sHom C D) := by
  change KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingFunctorHom left C D) : SSet.{u + 1})
  infer_instance

/-- 概要：presentable 圏と小余極限保存関手の全 ∞ 圏。
方針：元の保存関手と全関手同値を持つ単体的圏の coherent nerve。
規約：対象は同じ宇宙 u の小余極限に関して presentable。
使われ方：HTT 5.5.3 の Pr^L。 -/
@[kerodon 06PF]
def PrL : SSet.{u + 2} := SimplicialNerve (PresentableCoreCategory.{u} true)

/-- 概要：presentable 圏と accessible な小極限保存関手の全 ∞ 圏。
方針：右側の保存条件を持つ単体的圏の coherent nerve。
規約：随伴存在判定による同一視は d の比較界面が届いてから行う。
使われ方：HTT 5.5.3 の Pr^R。 -/
@[kerodon 06UG]
def PrR : SSet.{u + 2} := SimplicialNerve (PresentableCoreCategory.{u} false)

instance prL_quasicategory : Quasicategory PrL.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (PresentableCoreCategory.{u} true)

instance prR_quasicategory : Quasicategory PrR.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (PresentableCoreCategory.{u} false)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldReflection

/-!
概要：presentable 圏の小さい辺族に対する局所対象全部分圏は accessible。
方針：構成済みの Bousfield 反射による presentability から accessibility を取り出す。
規約：既存の局所対象を使用し、反射や局所置換の存在を追加入力にしない。
使われ方：HTT 5.5.4.2 の無条件の公開界面。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：任意の小さい辺族の局所対象全部分圏は accessible。
方針：Bousfield 反射から得た presentability の accessibility 成分を使う。
規約：presentable C と Type u で添字付けた辺族だけを入力に取る。
使われ方：元の全関手圏の局所性に基づく HTT 5.5.4.2 の消費。 -/
lemma isAccessible {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) {I : Type u} (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.Category edges) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalObjects_isPresentable hC edges).isAccessible

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

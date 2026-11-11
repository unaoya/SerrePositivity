module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomTransportNaturality

/-!
概要：元の Hom の始点輸送の実装と証明済みの仕様をまとめる。
方針：一般の関手上の cast の実装を不透明な値に保存し、その合成則を射影で使う。
規約：実装と全ての仕様を構成し、輸送や同値の存在を仮定しない。
使われ方：複雑な転置関手へ適用するとき、等式輸送の本体の再展開を避ける。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：始点輸送の全単射とその三つの計算則。
方針：全ての始域・終域の関手に対する輸送と合成保存を保持する。
規約：各仕様はデータと同じ元の Hom に対する証明である。
使われ方：証明済み実装の不透明な境界。 -/
structure HomSourceTransport (A E : SSet.{u}) where
  equiv : ∀ {U U' V : A ⟶ E}, U = U' → _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' V
  comp : ∀ {U U' V W : A ⟶ E} (h : U = U') (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V W),
    equiv h (α ≫ β) = equiv h α ≫ β
  factor : ∀ {U U' V V' W : A ⟶ E} (hU : U = U') (hV : V = V')
      (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V W),
    equiv hU (α ≫ β) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hU hV α ≫ equiv hV β
  eq_congr : ∀ {U U' V : A ⟶ E} (h : U = U') (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V),
    equiv h α = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr h rfl α

/-- 概要：cast による始点輸送と検証済みの仕様の実装。
方針：一般の関手で構成した全単射と三補題をまとめる。
規約：不透明性は再展開を防ぐためであり、全フィールドをここで証明する。
使われ方：端点の関手が大きい場合のカーネル検査の境界。 -/
opaque homSourceTransportPackage (A E : SSet.{u}) : HomSourceTransport A E := {
  equiv := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomSourceEquiv
  comp := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomSourceEquiv_comp
  factor := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomSourceEquiv_factor
  eq_congr := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomSourceEquiv_eq_congr }

/-- 概要：証明済み実装から元の Hom の始点輸送を取り出す。
方針：全単射のフィールドを射影する。
規約：同じ端点の関手と指定等式を保持する。
使われ方：前合成の Hom 対応の入口。 -/
def sourceHomTransportEquiv {A E : SSet.{u}} {U U' V : A ⟶ E} (h : U = U') :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' V :=
  (homSourceTransportPackage A E).equiv h

/-- 概要：不透明な始点輸送の合成保存。
方針：実装と同時に証明した仕様を射影する。
規約：中間点と終点は保持する。
使われ方：前合成の入口の標的自然性。 -/
lemma sourceHomTransportEquiv_comp {A E : SSet.{u}} {U U' V W : A ⟶ E}
    (h : U = U') (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V W) :
    sourceHomTransportEquiv h (α ≫ β) = sourceHomTransportEquiv h α ≫ β :=
  (homSourceTransportPackage A E).comp h α β

/-- 概要：不透明な始点輸送を二因子の両端輸送に分解する。
方針：実装と同時に証明した仕様を射影する。
規約：元の二つの Hom を保持する。
使われ方：前合成の入口の始域自然性。 -/
lemma sourceHomTransportEquiv_factor {A E : SSet.{u}} {U U' V V' W : A ⟶ E}
    (hU : U = U') (hV : V = V') (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V W) :
    sourceHomTransportEquiv hU (α ≫ β) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hU hV α ≫ sourceHomTransportEquiv hV β :=
  (homSourceTransportPackage A E).factor hU hV α β

/-- 概要：不透明な始点輸送を既存の両端輸送に照合する。
方針：実装と同時に証明した仕様を射影する。
規約：同じ端点と Hom を保持する。
使われ方：転置の全パラメータ自然性の接続。 -/
lemma sourceHomTransportEquiv_eq_congr {A E : SSet.{u}} {U U' V : A ⟶ E}
    (h : U = U') (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) :
    sourceHomTransportEquiv h α = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr h rfl α :=
  (homSourceTransportPackage A E).eq_congr h α

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

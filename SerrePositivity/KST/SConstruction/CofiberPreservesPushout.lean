module
public import SerrePositivity.InfinityCategories.Stable.StableSpanPushout
public import SerrePositivity.KST.SConstruction.ColimitComparison
public import SerrePositivity.KST.SConstruction.ColimitDiagramTransport
public import SerrePositivity.KST.SConstruction.StableModels

/-! # cofiber 保存から任意の押し出しの保存へ
概要：安定な源からの零対象と cofiber を保つ射は全ての押し出しを保つ。
方針：押し出しを零角の左・外側四角形で表し、貼り合わせの消去と余錐の同型で戻す。
規約：既存の二つの保存条件の定義は変更しない。使われ方：McCarthy 法での完全関手の pushout 保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零対象と cofiber を保つ射は安定な源の全ての押し出しを保つ。
方針：左と外側が cofiber の長方形で指定 span の押し出しを作り、同型による輸送を使う。
規約：標的の安定性は不要。使われ方：二つの保存条件の同値。 -/
lemma PreservesCofiberData.isPushoutSquare {C D : SSet.{u}} [Quasicategory C] [IsStable C]
    [Quasicategory D] {f : C ⟶ D} (hf : PreservesCofiberData f)
    (R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C) (hR : IsPushoutSquare R) :
    IsPushoutSquare (R ≫ f) := by
  obtain ⟨F, hp, hz, hl, hr, ho⟩ := _root_.SerrePositivity.InfinityCategories.Stable.exists_stable_pushoutPresentation_of_span (pushoutSpan R)
  have hzo : IsZeroVertex (squareVertex (pastingSquare F 1) 0 1) := by
    have he : squareVertex (pastingSquare F 1) 0 1 = squareVertex (pastingSquare F 2) 0 1 := rfl
    rw [he]
    exact hz
  let L : ZeroTriangle C := ⟨pastingSquare F 2, hz⟩
  let O : ZeroTriangle C := ⟨pastingSquare F 1, hzo⟩
  have hl' : IsPushoutSquare (pastingSquare (F ≫ f) 2) := by
    change IsPushoutSquare (pastingSquare F 2 ≫ f)
    exact hf.2 L hl
  have ho' : IsPushoutSquare (pastingSquare (F ≫ f) 1) := by
    change IsPushoutSquare (pastingSquare F 1 ≫ f)
    exact hf.2 O ho
  have hr' := isPushoutSquare_pasting_cancel_left (F ≫ f) hl' ho'
  change IsPushoutSquare (pastingSquare F 0 ≫ f) at hr'
  have es : FunctorIso (pushoutSpan (pastingSquare F 0)) (pushoutSpan R) := by
    rw [hp]
  let e := pushoutSquareIsoOfSpanIso (pastingSquare F 0) R hr hR es
  exact IsPushoutSquare.of_functorIso hr' (e.postcomp f)

/-- 概要：安定な源では cofiber 保存条件から全押し出しを保つ既存の保存条件が従う。
方針：零対象の保存と前定理を組にする。
規約：保存条件そのものを置換しない。使われ方：既存の強い後合成 API との接続。 -/
lemma PreservesCofiberData.toSConstructionData {C D : SSet.{u}} [Quasicategory C] [IsStable C]
    [Quasicategory D] {f : C ⟶ D} (hf : PreservesCofiberData f) : PreservesSConstructionData f :=
  ⟨hf.1, hf.isPushoutSquare⟩

/-- 概要：安定な源の二つの S 構成の保存条件は同値。
方針：既存の制限方向と全押し出しを保つ方向を合わせる。
規約：標的は quasicategory のみ。使われ方：完全関手の型の照合。 -/
lemma preservesSConstructionData_iff_cofiberData {C D : SSet.{u}} [Quasicategory C] [IsStable C]
    [Quasicategory D] (f : C ⟶ D) : PreservesSConstructionData f ↔ PreservesCofiberData f :=
  ⟨PreservesSConstructionData.toCofiberData, PreservesCofiberData.toSConstructionData⟩

/-- 概要：本レーンの安定な模型の全ての射は零対象と任意の押し出しを保つ。
方針：射に格納された cofiber 保存を強い保存条件へ移す。
規約：StableModel の公開の射の型は変更しない。使われ方：加法性の全ての入力射。 -/
lemma stableModelHom_preservesSConstructionData {X Y : StableModel.{u}} (f : X ⟶ Y) :
    PreservesSConstructionData f.val := f.property.toSConstructionData

end SerrePositivity.KST.SConstruction

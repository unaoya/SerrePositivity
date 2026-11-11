module
public import SerrePositivity.KST.Fibration.Relative.StableTrivialPullback

/-!
概要：指定した完全な切断を保持する trivial Kan 基底変換の共通切断。
方針：元の実引き戻しへ同じ切断を持ち上げ、忘却射影で完全性を反映する。
規約：元の選択を保ち、商や核表示に依存しない。
使われ方：閉じた旗と既存 W 列の相対 cofiber 補完を共通化する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration
open Relative
variable {E Y T : StableModel.{u}} (p : E ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val]
  (s : Y ⟶ E) (hs : s ≫ p = 𝟙 Y) (e : T ⟶ Y)

/-- 概要：元の指定切断を保った基底変換の実切断。
方針：同じ引き戻しへ持ち上げ、trivial Kan 射影で完全性を反映する。
規約：新しい逆を選ばない。使われ方：有限旗の相対加法性の実成分。 -/
def stableTrivialPullbackSection : T ⟶ stableTrivialPullback p e := by
  let f : T.carrier ⟶ (stableTrivialPullback p e).carrier := pullback.lift (e ≫ s).val (𝟙 T.carrier) (by
    change ((e ≫ s) ≫ p).val = _
    rw [Category.assoc, hs, Category.comp_id]
    rfl)
  exact ⟨f, by
    apply preservesCofiberData_of_trivialProjection (stableTrivialPullbackSnd p e).val
    change PreservesCofiberData (f ≫ pullback.snd p.val e.val)
    rw [pullback.lift_snd]
    exact preservesCofiberData_id _⟩

/-- 概要：同じ切断の忘却は元の底の恒等射。
方針：実引き戻しの第二成分。規約：厳密等号。使われ方：先行旗の回収。 -/
theorem stableTrivialPullbackSection_snd :
    stableTrivialPullbackSection p s hs e ≫ stableTrivialPullbackSnd p e = 𝟙 T :=
  Subtype.ext (pullback.lift_snd _ _ _)

/-- 概要：同じ切断の第一成分は元の指定切断による補完。
方針：実引き戻しの第一成分。規約：選択を固定。使われ方：同じ cofiber の回収。 -/
theorem stableTrivialPullbackSection_fst :
    stableTrivialPullbackSection p s hs e ≫ stableTrivialPullbackFst p e = e ≫ s :=
  Subtype.ext (pullback.lift_fst _ _ _)

/-- 概要：元の忘却射影と指定切断は同じ完全な同値を構成する。
方針：元の trivial Kan 射影上の関手同型と厳密な切断式を使う。
規約：元の切断を保持。使われ方：同じ補完切断の実現が局所化同型であること。 -/
def stableTrivialPullbackSectionEquivalence :
    StableModelEquivalence (stableTrivialPullback p e) T where
  hom := stableTrivialPullbackSnd p e
  inv := stableTrivialPullbackSection p s hs e
  homInvIso := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (stableTrivialPullbackSnd p e).val _ _ (by
    change ((stableTrivialPullbackSnd p e ≫ stableTrivialPullbackSection p s hs e) ≫
      stableTrivialPullbackSnd p e).val = _
    rw [Category.assoc, stableTrivialPullbackSection_snd, Category.comp_id]
    rfl)
  invHomIso := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (stableTrivialPullbackSection p s hs e ≫
      stableTrivialPullbackSnd p e).val (𝟙 T.carrier)
    rw [stableTrivialPullbackSection_snd]
    exact Iso.refl _

end SerrePositivity.KST.Fibration

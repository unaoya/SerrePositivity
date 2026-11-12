module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.Pushouts

/-!
概要：元の形状 pushout を持ち上げ、任意の元の試験族との積で全族を貼り合わせる。
方針：宇宙持ち上げと左直積の余極限保存を使う。
規約：試験族の有限性を仮定せず、元の全包含を保持する。
使われ方：有限半順序形状の点追加における元の C 全族と全円柱の貼り合わせ。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {J K₁ K₂ K : SSet.{u}} {i : J ⟶ K₁} {j : J ⟶ K₂}
  {r : K₁ ⟶ K} {s : K₂ ⟶ K} (h : IsPushout i j r s)
include h
/-- 概要：元の持ち上げた形状 pushout と任意の全試験族との積は pushout。
方針：二つの余極限保存。規約：全射を保持。使われ方：全族の実貼り合わせ。 -/
lemma tensorShape_isPushout (T : SSet.{u + 1}) :
    IsPushout (T ◁ (SSet.uliftFunctor.{u + 1, u}).map i)
      (T ◁ (SSet.uliftFunctor.{u + 1, u}).map j)
      (T ◁ (SSet.uliftFunctor.{u + 1, u}).map r)
      (T ◁ (SSet.uliftFunctor.{u + 1, u}).map s) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftSSet_isPushout.{u, u + 1} h).map (tensorLeft T)
/-- 概要：共通境界で一致する同じ全試験族上の二族を貼る。
方針：元の積 pushout の降下。規約：全射の指定値。使われ方：全 C 族と全円柱。 -/
def tensorShapeGlue {T X : SSet.{u + 1}}
    (F : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₁ ⟶ X)
    (G : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₂ ⟶ X)
    (hc : (T ◁ (SSet.uliftFunctor.{u + 1, u}).map i) ≫ F =
      (T ◁ (SSet.uliftFunctor.{u + 1, u}).map j) ≫ G) :
    T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ X :=
  (tensorShape_isPushout h T).desc F G hc
/-- 概要：貼り合わせた全族は元の左族自身を回収。
方針：元の pushout。規約：全射の等号。使われ方：指定部分の厳密な保持。 -/
lemma tensorShapeGlue_left {T X : SSet.{u + 1}}
    (F : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₁ ⟶ X)
    (G : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₂ ⟶ X)
    (hc : (T ◁ (SSet.uliftFunctor.{u + 1, u}).map i) ≫ F =
      (T ◁ (SSet.uliftFunctor.{u + 1, u}).map j) ≫ G) :
    (T ◁ (SSet.uliftFunctor.{u + 1, u}).map r) ≫ tensorShapeGlue h F G hc = F :=
  (tensorShape_isPushout h T).inl_desc _ _ _
/-- 概要：貼り合わせた全族は元の右族自身を回収。
方針：元の pushout。規約：全射の等号。使われ方：指定部分の厳密な保持。 -/
lemma tensorShapeGlue_right {T X : SSet.{u + 1}}
    (F : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₁ ⟶ X)
    (G : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₂ ⟶ X)
    (hc : (T ◁ (SSet.uliftFunctor.{u + 1, u}).map i) ≫ F =
      (T ◁ (SSet.uliftFunctor.{u + 1, u}).map j) ≫ G) :
    (T ◁ (SSet.uliftFunctor.{u + 1, u}).map s) ≫ tensorShapeGlue h F G hc = G :=
  (tensorShape_isPushout h T).inr_desc _ _ _
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

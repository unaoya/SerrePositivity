module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
概要：元の点写像で直積の右因子を固定する全射と、その厳密な自然性。
方針：左因子の恒等射と元の点の定値写像を、直積の普遍性で束ねる。
規約：元の点写像を選び直さず、全係数を保持する。
使われ方：余錐積の終端面を、元の同じ終点 comma の全族として読む。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：元の指定点で右因子を固定する全射。
方針：元の二射を直積へ束ねる。規約：全係数を保持。使われ方：同じ終端面の制限。 -/
def tensorRightPoint (A : SSet.{u}) {B : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ B) :
    A ⟶ A ⊗ B := lift (𝟙 A) (SSet.const (SSet.yonedaEquiv p))
/-- 概要：元の指定点で右因子を固定する全射は単射。
方針：元の左射影で恒等射を回収。規約：元の全射。使われ方：指定変換を付加する包含。 -/
instance tensorRightPoint_mono (A : SSet.{u}) {B : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ B) : Mono (tensorRightPoint A p) := by
  dsimp only [tensorRightPoint]
  infer_instance
/-- 概要：元の左因子の全族は同じ指定点での固定後も厳密に保持される。
方針：元の第一射影。規約：全射の等号。使われ方：補間領域の終点面の回収。 -/
lemma tensorRightPoint_fst (A : SSet.{u}) {B : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ B) : tensorRightPoint A p ≫ fst A B = 𝟙 A := lift_fst _ _
/-- 概要：元の試験族の制限を同じ点で厳密に保持する。
方針：直積の自然性。規約：全射の等号。使われ方：終端面の旧族と新頂点。 -/
lemma tensorRightPoint_naturality {A A' B : SSet.{u}} (f : A ⟶ A')
    (p : (Δ[0] : SSet.{u}) ⟶ B) :
    f ≫ tensorRightPoint A' p = tensorRightPoint A p ≫ (f ▷ B) := by
  simp only [tensorRightPoint, comp_lift, lift_whiskerRight, Category.comp_id,
    Category.id_comp, SSet.comp_const]
/-- 概要：同じ点で固定した右因子は元の指定点の定値写像。
方針：元の第二射影。規約：全射の等号。使われ方：同じ終点での全評価。 -/
lemma tensorRightPoint_snd (A : SSet.{u}) {B : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ B) :
    tensorRightPoint A p ≫ snd A B = SSet.const (SSet.yonedaEquiv p) := lift_snd _ _
/-- 概要：右因子の元の写像は、同じ元の点の像での固定と厳密に可換。
方針：元の直積と点の自然性。規約：全射の等号。使われ方：終点面の宇宙表示の比較。 -/
lemma tensorRightPoint_whiskerLeft (A : SSet.{u}) {B B' : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ B) (f : B ⟶ B') :
    tensorRightPoint A p ≫ (A ◁ f) = tensorRightPoint A (p ≫ f) := by
  simp only [tensorRightPoint, lift_whiskerLeft, SSet.const_comp, SSet.yonedaEquiv_comp]
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：同じ底上の cocartesian fibration と、cocartesian 辺を保つ実際の底上の関手の圏。
方針：射影とその fibration 性を束縛し、通常の Over 圏の射に辺の保存条件を課す。
規約：射を同値類で商にせず、元の単体集合の射を使う。
使われ方：Cat∞ 値 straightening の fibration 側の通常の圏。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 全ての元の cocartesian 辺を、標的の cocartesian 辺へ写すという条件。 -/
def PreservesCocartesianEdges {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) : Prop :=
  ∀ e : E _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e →
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (f.app (Opposite.op ⦋1⦌) e)

/-- 恒等関手は同じ cocartesian 辺を保つ。 -/
lemma preservesCocartesianEdges_id {E B : SSet.{u}} (p : E ⟶ B) :
    PreservesCocartesianEdges p p (𝟙 E) := fun _ h ↦ h

/-- cocartesian 辺を保つ二つの実際の関手の合成も辺を保つ。 -/
lemma PreservesCocartesianEdges.comp {E F G B : SSet.{u}}
    {p : E ⟶ B} {q : F ⟶ B} {r : G ⟶ B} {f : E ⟶ F} {g : F ⟶ G}
    (hf : PreservesCocartesianEdges p q f) (hg : PreservesCocartesianEdges q r g) :
    PreservesCocartesianEdges p r (f ≫ g) := fun e he ↦ hg _ (hf e he)

/-- 同じ底上の小さい cocartesian fibration を束縛した対象。 -/
def CocartesianFibrationObject (B : SSet.{u}) := {p : Over B // _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p.hom}

/-- 束縛した対象の射影は、元の cocartesian fibration。 -/
instance cocartesianFibrationObject_projection {B : SSet.{u}} (p : CocartesianFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p.val.hom := p.property

/-- 通常の射は、元の cocartesian 辺を保つ底上の関手。 -/
instance cocartesianFibrationObject_category (B : SSet.{u}) :
    Category.{u} (CocartesianFibrationObject B) where
  Hom p q := {f : p.val ⟶ q.val // PreservesCocartesianEdges p.val.hom q.val.hom f.left}
  id p := ⟨𝟙 p.val, preservesCocartesianEdges_id p.val.hom⟩
  comp f g := ⟨f.val ≫ g.val, f.property.comp g.property⟩
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

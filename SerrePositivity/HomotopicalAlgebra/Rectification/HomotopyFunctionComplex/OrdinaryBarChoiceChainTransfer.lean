module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RetractChainFamily

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceCategory
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChainFamily
public import Mathlib.Combinatorics.Quiver.Path

/-!
# 中断した任意モデル源への一般化：OrdinaryBarChoiceChainTransfer

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Transfer of entire parameterized morphisms of the relative choice category。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0141][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0141
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Transfer of entire parameterized morphisms of the relative choice category

An edge can move along the full parameter, independently of the contraction
coordinates. At zero a junction composes actual choice-category morphisms;
at one it splits transferred families. Arbitrary surrounding chains remain.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev choiceObject (T : SSet.{max u v}) := OrdinaryBarChoiceCategory.Object (C := C) hcof hfib T

def snoc {T : SSet.{max u v}} {a : Cᵒᵖ × C} {X Y : choiceObject (C := C) hcof hfib T}
    (q : OrdinaryBarChainFamily.chain hcof hfib T a X.base) (f : X ⟶ Y)
    (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) : OrdinaryBarChainFamily.chain hcof hfib T a Y.base :=
  q.familySnoc ((OrdinaryBarChoiceCategory.evaluation hcof hfib T).map f) t

lemma snoc_substitute {T U : SSet.{max u v}} (j : U ⟶ T) {a : Cᵒᵖ × C}
    {X Y : choiceObject (C := C) hcof hfib T}
    (q : OrdinaryBarChainFamily.chain hcof hfib T a X.base)
    (f : X ⟶ Y) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    (snoc hcof hfib q f t).substitute j =
      snoc hcof hfib (q.substitute j) ((OrdinaryBarChoiceCategory.reindex hcof hfib j).map f)
        (j ≫ t) := rfl

def ofPath {T : SSet.{max u v}} {X : choiceObject (C := C) hcof hfib T} :
    {Y : choiceObject (C := C) hcof hfib T} → Quiver.Path X Y →
      (ℕ → (T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) →
        OrdinaryBarChainFamily.chain hcof hfib T X.base Y.base
  | _, .nil, _ => .nil
  | _, .cons q f, t => snoc hcof hfib (ofPath q t) f (t q.length)

lemma ofPath_length {T : SSet.{max u v}} {X Y : choiceObject (C := C) hcof hfib T}
    (q : Quiver.Path X Y) (t : ℕ → (T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    (ofPath hcof hfib q t).length = q.length := by
  induction q with
  | nil => rfl
  | cons q f ih => change (ofPath hcof hfib q t).length + 1 = q.length + 1; rw [ih]

lemma reindex_path_length {T U : SSet.{max u v}} (j : U ⟶ T)
    {X Y : choiceObject (C := C) hcof hfib T} (q : Quiver.Path X Y) :
    ((OrdinaryBarChoiceCategory.reindex hcof hfib j).toPrefunctor.mapPath q).length = q.length := by
  induction q with
  | nil => rfl
  | cons q f ih => change _ + 1 = q.length + 1; rw [ih]

lemma ofPath_substitute {T U : SSet.{max u v}} (j : U ⟶ T)
    {X Y : choiceObject (C := C) hcof hfib T} (q : Quiver.Path X Y)
    (t : ℕ → (T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    (ofPath hcof hfib q t).substitute j =
      ofPath hcof hfib ((OrdinaryBarChoiceCategory.reindex hcof hfib j).toPrefunctor.mapPath q)
        (fun k => j ≫ t k) := by
  induction q with
  | nil => rfl
  | cons q f ih =>
    simp only [Prefunctor.mapPath, ofPath]
    rw [snoc_substitute, ih, reindex_path_length]
    rfl

def smallPathFamily {T : SSet.{v}}
    {X Y : choiceObject (C := C) hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T)} (q : Quiver.Path X Y)
    (t : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    small hcof hfib X.base ⊗ T ⟶ small hcof hfib Y.base :=
  OrdinaryBarChainFamily.smallFamily hcof hfib (ofPath hcof hfib q t)

lemma smallPathFamily_nil {T : SSet.{v}}
    (X : choiceObject (C := C) hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T))
    (t : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    smallPathFamily hcof hfib (Quiver.Path.nil : Quiver.Path X X) t =
      ParameterComposition.const T (𝟙 (small hcof hfib X.base)) := by
  ext n x
  exact congrArg ULift.down (types_congr_hom (congr_app (section_fac hcof hfib X.base) n)
    (ULift.up x.1))

lemma smallPathFamily_single {T : SSet.{v}}
    {X Y : choiceObject (C := C) hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T)} (f : X ⟶ Y)
    (t : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    smallPathFamily hcof hfib f.toPath t =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (transferFamily hcof hfib f.base f.extension) := by
  unfold smallPathFamily OrdinaryBarChainFamily.smallFamily OrdinaryBarChainFamily.family
  simp only [Quiver.Hom.toPath, ofPath, snoc]
  rw [RetractChainFamily.transfer_last_family_parameter (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
    (contraction_over hcof hfib)]
  ext n x
  rfl

lemma smallPathFamily_substitute {T U : SSet.{v}} (j : U ⟶ T)
    {X Y : choiceObject (C := C) hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T)} (q : Quiver.Path X Y)
    (t : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    smallPathFamily hcof hfib
        ((OrdinaryBarChoiceCategory.reindex hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map j)).toPrefunctor.mapPath q)
        (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map j ≫ t k) =
      ParameterComposition.substitute j (smallPathFamily hcof hfib q t) := by
  rw [smallPathFamily, ← ofPath_substitute, OrdinaryBarChainFamily.smallFamily_substitute]
  rfl

lemma zero_face {T : SSet.{max u v}} {a d : Cᵒᵖ × C}
    {X Y Z : choiceObject (C := C) hcof hfib T}
    (q : OrdinaryBarChainFamily.chain hcof hfib T a X.base) (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)
    (r : OrdinaryBarChainFamily.chain hcof hfib T Z.base d) :
    OrdinaryBarChainFamily.family hcof hfib
        ((snoc hcof hfib (snoc hcof hfib q f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T)) g t).append r) =
      OrdinaryBarChainFamily.family hcof hfib ((snoc hcof hfib q (f ≫ g) t).append r) := by
  have h := RetractChainFamily.zero_family_face (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib) q
    ((OrdinaryBarChoiceCategory.evaluation hcof hfib T).map f)
    ((OrdinaryBarChoiceCategory.evaluation hcof hfib T).map g) t r
  unfold snoc
  rw [(OrdinaryBarChoiceCategory.evaluation hcof hfib T).map_comp f g]
  exact h

lemma one_face {T : SSet.{max u v}} {a d : Cᵒᵖ × C}
    {X Y : choiceObject (C := C) hcof hfib T}
    (q : OrdinaryBarChainFamily.chain hcof hfib T a X.base) (f : X ⟶ Y)
    (r : OrdinaryBarChainFamily.chain hcof hfib T Y.base d) :
    OrdinaryBarChainFamily.family hcof hfib
        ((snoc hcof hfib q f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one T)).append r) =
      ParameterComposition.comp
        (OrdinaryBarChainFamily.family hcof hfib (snoc hcof hfib q f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T)))
        (OrdinaryBarChainFamily.family hcof hfib r) :=
  RetractChainFamily.one_family_face _ _ _ _ _ (contraction_over hcof hfib) q _ r

lemma small_zero_face {T : SSet.{v}} {a d : Cᵒᵖ × C}
    {X Y Z : choiceObject (C := C) hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T)}
    (q : OrdinaryBarChainFamily.chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) a X.base)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)
    (r : OrdinaryBarChainFamily.chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) Z.base d) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
        ((snoc hcof hfib (snoc hcof hfib q f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero _)) g t).append r) =
      OrdinaryBarChainFamily.smallFamily hcof hfib ((snoc hcof hfib q (f ≫ g) t).append r) :=
  congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (zero_face hcof hfib q f g t r)

lemma small_one_face {T : SSet.{v}} {a d : Cᵒᵖ × C}
    {X Y : choiceObject (C := C) hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T)}
    (q : OrdinaryBarChainFamily.chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) a X.base)
    (f : X ⟶ Y)
    (r : OrdinaryBarChainFamily.chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) Y.base d) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
        ((snoc hcof hfib q f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one _)).append r) =
      ParameterComposition.comp
        (OrdinaryBarChainFamily.smallFamily hcof hfib
          (snoc hcof hfib q f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero _)))
        (OrdinaryBarChainFamily.smallFamily hcof hfib r) := by
  rw [OrdinaryBarChainFamily.smallFamily, one_face]
  ext n x
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer

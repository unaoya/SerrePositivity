module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSmallReference
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SmallDominatedSubcomplex
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SmallSimplicialValue

/-!
# 中断した任意モデル源への一般化：OrdinaryBarSmallSubcomplex

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：An actual small homotopy-equivalent subcomplex inside each Kan bar value。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0223][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0223
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# An actual small homotopy-equivalent subcomplex inside each Kan bar value

The value-side horn replacement needs no large model. The original map to
the small reference extends exactly along its anodyne unit. The resulting
small subcomplexes are individual choices, not a subdiagram on the base.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex
open OrdinaryBarSmallReference
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X : Cᵒᵖ × C)

abbrev ambient : SSet.{max u v} :=
  AnodyneKanReplacement.functor.obj (OrdinaryResolutionBar.functor.obj X)

def toSmall : ambient X ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (value hcof hfib X) :=
  KanHomotopyClasses.extension
    (AnodyneKanReplacement.unit.app (OrdinaryResolutionBar.functor.obj X))
    (AnodyneKanReplacement.unit_anodyne _)
    (UniverseLift.horn_terminal_map (value_kan hcof hfib X)) (toReference hcof hfib X)

lemma unit_toSmall :
    AnodyneKanReplacement.unit.app (OrdinaryResolutionBar.functor.obj X) ≫
      toSmall hcof hfib X = toReference hcof hfib X :=
  KanHomotopyClasses.extension_fac _ _ _ _

lemma toSmall_isIso : IsIso (AnodyneHomotopy.anodyneQ.map (toSmall hcof hfib X)) := by
  have := toReference_isIso hcof hfib X
  have := Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
    (AnodyneKanReplacement.unit_anodyne (OrdinaryResolutionBar.functor.obj X))
  have hc := congrArg AnodyneHomotopy.anodyneQ.map (unit_toSmall hcof hfib X)
  rw [CategoryTheory.Functor.map_comp] at hc
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map
      (AnodyneKanReplacement.unit.app (OrdinaryResolutionBar.functor.obj X)) ≫
        AnodyneHomotopy.anodyneQ.map (toSmall hcof hfib X)) := hc.symm ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hi

def fromSmall : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (value hcof hfib X) ⟶ ambient X := by
  have := toSmall_isIso hcof hfib X
  exact KanLocalizedRepresentatives.representative AnodyneHomotopy.anodyneQ
    (AnodyneKanReplacement.terminal_rlp _) (inv (AnodyneHomotopy.anodyneQ.map
      (toSmall hcof hfib X)))

lemma fromSmall_map : AnodyneHomotopy.anodyneQ.map (fromSmall hcof hfib X) =
    @inv _ _ _ _ (AnodyneHomotopy.anodyneQ.map (toSmall hcof hfib X))
      (toSmall_isIso hcof hfib X) :=
  KanLocalizedRepresentatives.representative_map AnodyneHomotopy.anodyneQ
    (AnodyneKanReplacement.terminal_rlp _) _

def domination : SSet.Homotopy (𝟙 (ambient X))
    (toSmall hcof hfib X ≫ fromSmall hcof hfib X) := by
  have := toSmall_isIso hcof hfib X
  apply Classical.choice
  apply (KanLocalizedRepresentatives.map_eq_iff_homotopy AnodyneHomotopy.anodyneQ
    (AnodyneKanReplacement.terminal_rlp _) _ _).mp
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp, fromSmall_map]
  exact (IsIso.hom_inv_id _).symm

abbrev complex (A : (ambient X).Subcomplex) : (ambient X).Subcomplex :=
  SmallDominatedSubcomplex.complex (fromSmall hcof hfib X) (toSmall hcof hfib X)
    (domination hcof hfib X) A

lemma seed_le (A : (ambient X).Subcomplex) : A ≤ complex hcof hfib X A :=
  SmallDominatedSubcomplex.seed_le _ _ _ _

lemma small (A : (ambient X).Subcomplex) (hA : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure.IsSmall.{v} A) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure.IsSmall.{v} (complex hcof hfib X A) := by
  apply SmallDominatedSubcomplex.small
  · intro n
    change Small.{v} (ULift.{max u v, v} ((value hcof hfib X).obj n))
    exact small_of_injective (f := ULift.down) ULift.down_injective
  · exact hA

def inclusionIso (A : (ambient X).Subcomplex) :
    AnodyneHomotopy.anodyneQ.obj (complex hcof hfib X A).toSSet ≅
      AnodyneHomotopy.anodyneQ.obj (ambient X) :=
  SmallDominatedSubcomplex.inclusionImageIso _ _ _ A AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)

/-- An actual object in the original small universe, after proving degreewise smallness. -/
def smallValue (A : (ambient X).Subcomplex) (hA : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure.IsSmall.{v} A) :
    SSet.{v} :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.shrink (complex hcof hfib X A).toSSet (small hcof hfib X A hA)

def smallInclusion (A : (ambient X).Subcomplex) (hA : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure.IsSmall.{v} A) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (smallValue hcof hfib X A hA) ⟶ ambient X :=
  (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.liftIso (complex hcof hfib X A).toSSet
    (small hcof hfib X A hA)).hom ≫ (complex hcof hfib X A).ι

lemma smallInclusion_isIso (A : (ambient X).Subcomplex)
    (hA : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SmallActionClosure.IsSmall.{v} A) :
    IsIso (AnodyneHomotopy.anodyneQ.map (smallInclusion hcof hfib X A hA)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (complex hcof hfib X A).ι) :=
    (inclusionIso hcof hfib X A).isIso_hom
  rw [smallInclusion, CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex

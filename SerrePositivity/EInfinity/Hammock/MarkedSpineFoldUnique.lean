module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineFoldComposition
public import SerrePositivity.EInfinity.Hammock.MarkedSpineGeneratorPoint

/-!
# 元の指定因子と非指定生成矢からの合成保存拡張の一意性

概要：任意の圏への元の因子列の評価は二つの生成部分上の指定で一意である。
方針：元の cons の三因子分解と合成保存から全因子列で帰納する。
規約：一意性は元の明示的な合成自身について述べる。
使われ方：自由積の普遍性の次数ごとの一意拡張。
-/

@[expose] public section
universe u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData
open CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {n : SimplexCategoryᵒᵖ}
  {D : Type uD} [Category.{vD} D] (F : FoldData W n D)

lemma fold_generatorPoint (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) :
    F.fold (generatorPoint W g n) = F.generator g := by
  change F.marked (AllMarked.nativeUnitPoint W g.val.left n) ≫ F.generator g ≫
    F.fold (unitPoint W g.val.right n) = _
  rw [F.marked_unit, F.fold_unit, Category.id_comp, Category.comp_id]

lemma fold_unique
    (H : ∀ {X Y : Paths C}, MarkedSpine W Y n X → (F.obj X ⟶ F.obj Y))
    (hm : ∀ {X Y} (p : (AllMarked.nativeSpace W X Y).obj n), H (nil X p) = F.marked p)
    (hg : ∀ g, H (generatorPoint W g n) = F.generator g)
    (hc : ∀ {X Y Z} (s : MarkedSpine W Y n X) (t : MarkedSpine W Z n Y),
      H (append s t) = H s ≫ H t) {X Y : Paths C} (t : MarkedSpine W Y n X) :
    H t = F.fold t := by
  induction t with
  | nil X p => exact hm p
  | cons X g p t ih =>
    conv_lhs => rw [cons_decomposition]
    rw [hc, hc, hm, hg, ih]
    rfl

lemma existsUnique_fold :
    ∃! H : ∀ {X Y : Paths C}, MarkedSpine W Y n X → (F.obj X ⟶ F.obj Y),
      (∀ {X Y} (p : (AllMarked.nativeSpace W X Y).obj n), H (nil X p) = F.marked p) ∧
      (∀ g, H (generatorPoint W g n) = F.generator g) ∧
      (∀ {X Y Z} (s : MarkedSpine W Y n X) (t : MarkedSpine W Z n Y),
        H (append s t) = H s ≫ H t) := by
  refine ⟨@F.fold, ⟨fun _ => rfl, F.fold_generatorPoint, F.fold_append⟩, ?_⟩
  intro H hH
  funext X Y t
  exact F.fold_unique H hH.1 hH.2.1 hH.2.2 t

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData

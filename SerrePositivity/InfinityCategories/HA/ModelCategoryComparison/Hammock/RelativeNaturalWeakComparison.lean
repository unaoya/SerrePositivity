module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeNaturalColimitHomotopy
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakArrowActionEquivalences
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HomotopyWeakComparison

/-!
# 相対自然変換による元の hammock 写像の弱同値性の比較

概要：全成分が指定射である自然変換の両関手は同時に弱比較を与える。
方針：端点が動く元のホモトピーと四作用の弱同値性を二対三則で接続する。
規約：元の始域・終域の Kan 性や単体集合のモデル構造を要求しない。
使われ方：有限部分木の変形と DK のホモトピー比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeNatural
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) (X Y : C)

include hη in
lemma weak_iff : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap G X Y) := by
  have hp := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakArrow.postcompose_forward_isWeakHomotopyEquivalence
    (η.app Y) (hη Y) (F.functor.obj X)
  have hq := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakArrow.precompose_forward_isWeakHomotopyEquivalence
    (η.app X) (hη X) (G.functor.obj Y)
  have hh := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.homotopy_weak_iff (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeNatural.homotopy η hη X Y)
  constructor
  · intro hf
    exact hq.cancel_right (hh.mp (hf.comp hp))
  · intro hg
    exact hp.cancel_right (hh.mpr (hg.comp hq))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeNatural

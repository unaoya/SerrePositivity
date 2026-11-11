module

public import SerrePositivity.EInfinity.Hammock.WeakTwoOfSix
public import SerrePositivity.EInfinity.Hammock.RelativeNaturalWeakComparison
public import SerrePositivity.EInfinity.Hammock.RelativeFunctorLaws

/-!
# 相対逆と指定自然変換による元の hammock 関手の弱同値性

概要：元の二つの相対関手と両合成から恒等への指定自然変換から同じ Hom 射を判定する。
方針：元の二つの合成の弱同値性を自然変換で回収し、中間射と二対三則を使う。
規約：端点移送や全語の標準射を別の比較に置き換えない。
使われ方：cofibrant 代数と全代数の元の hammock の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.RelativeEquivalence
open CategoryTheory SerrePositivity.InfinityCategories
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) (G : LocalizerMorphism V W)
  (η : (F.comp G).functor ⟶ 𝟭 C) (hη : ∀ X, W (η.app X))
  (ε : (G.comp F).functor ⟶ 𝟭 D) (hε : ∀ X, V (ε.app X)) (X Y : C)
include G η hη ε hε
lemma colimitMap_weak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap F X Y) := by
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap (F.comp G) X Y) := by
    apply (RelativeNatural.weak_iff (F := F.comp G) (G := LocalizerMorphism.id W) η hη X Y).mpr
    rw [Relative.colimitMap_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id _
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap (G.comp F)
      (F.functor.obj X) (F.functor.obj Y)) := by
    apply (RelativeNatural.weak_iff (F := G.comp F) (G := LocalizerMorphism.id V) ε hε
      (F.functor.obj X) (F.functor.obj Y)).mpr
    rw [Relative.colimitMap_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id _
  rw [Relative.colimitMap_comp] at hc hd
  exact (weak_middle_of_composites _ _ _ hc hd).cancel_right hc
lemma reducedMap_weak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.reducedMap F X Y) := by
  have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (reducedColimitIso W X Y).symm).isWeakHomotopyEquivalence
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (reducedColimitIso V (F.functor.obj X) (F.functor.obj Y))).isWeakHomotopyEquivalence
  exact hs.comp ((colimitMap_weak F G η hη ε hε X Y).comp ht)
end SerrePositivity.EInfinity.Hammock.RelativeEquivalence

module

public import SerrePositivity.EInfinity.Hammock.RelativeEquivalenceWeak

/-!
概要：指定弱同値の成分を持つ二つの単位から元の相対 Hom 射の弱同値性を得る。
方針：元の自然変換の両関手の弱比較と同じ二つの合成を二対三で消去する。
規約：両単位は恒等から逆合成へ向き、元の射と端点を保持する。
使われ方：同じ right frame の fibrant 置換による cofibrant・bifibrant 比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.RelativeEquivalence
open CategoryTheory SerrePositivity.InfinityCategories
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) (G : LocalizerMorphism V W)
  (η : 𝟭 C ⟶ (F.comp G).functor) (hη : ∀ X, W (η.app X))
  (ε : 𝟭 D ⟶ (G.comp F).functor) (hε : ∀ X, V (ε.app X)) (X Y : C)
include G η hη ε hε

/-- 概要：二つの元の単位を持つ相対逆の Hom 射は弱同値。
方針：恒等と二つの元の合成の弱同値性を同じ自然変換で比較する。
規約：元の相対関手の Hom 射自身。使われ方：fibrant 置換側の実 hammock 比較。 -/
lemma colimitMap_weak_of_units : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap F X Y) := by
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap (F.comp G) X Y) := by
    apply (RelativeNatural.weak_iff (F := LocalizerMorphism.id W) (G := F.comp G)
      η hη X Y).mp
    rw [Relative.colimitMap_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id _
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap (G.comp F)
      (F.functor.obj X) (F.functor.obj Y)) := by
    apply (RelativeNatural.weak_iff (F := LocalizerMorphism.id V) (G := G.comp F) ε hε
      (F.functor.obj X) (F.functor.obj Y)).mp
    rw [Relative.colimitMap_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id _
  rw [Relative.colimitMap_comp] at hc hd
  exact (weak_middle_of_composites _ _ _ hc hd).cancel_right hc

/-- 概要：同じ単位による相対逆の reduced Hom 射も弱同値。
方針：元の colimit 比較を同じ reduced Hom の同型で輸送する。
規約：元の実相対射を保つ。使われ方：局所化の写像空間の比較。 -/
lemma reducedMap_weak_of_units : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.reducedMap F X Y) := by
  have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (reducedColimitIso W X Y).symm).isWeakHomotopyEquivalence
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (reducedColimitIso V (F.functor.obj X) (F.functor.obj Y))).isWeakHomotopyEquivalence
  exact hs.comp ((colimitMap_weak_of_units F G η hη ε hε X Y).comp ht)

end SerrePositivity.EInfinity.Hammock.RelativeEquivalence

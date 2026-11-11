module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathMap

/-!
概要：可換正方形が同じ可逆 path 置換に誘導する実射。
方針：path の射と源の射を同じ pullback に組み合わせる。
規約：二つの射影および終点との等号を厳密に保持する。
使われ方：Ind-S (4) の小模型で得た境界充填を元の関手圏へ戻す。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 同じ可換正方形の二成分から、可逆 path 置換間の実射を作る。 -/
def equivalencePathReplacementInduced {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement f ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement g :=
  pullback.lift
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f ≫ a) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint, ← Category.assoc, pullback.condition]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f ≫ f) ≫ b =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f ≫ a) ≫ g
      rw [Category.assoc, h, Category.assoc])

lemma equivalencePathReplacementInduced_projection {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    equivalencePathReplacementInduced f g a b h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f ≫ a := pullback.lift_snd _ _ _

lemma equivalencePathReplacementInduced_path {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    equivalencePathReplacementInduced f g a b h ≫
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y' 0) g =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap b :=
  pullback.lift_fst _ _ _

lemma equivalencePathReplacementInduced_map {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    equivalencePathReplacementInduced f g a b h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f ≫ b := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap
  rw [← Category.assoc, equivalencePathReplacementInduced_path, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint, ← Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

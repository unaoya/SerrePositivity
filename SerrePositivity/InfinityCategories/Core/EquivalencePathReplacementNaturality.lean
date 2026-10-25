module

public import SerrePositivity.InfinityCategories.Core.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Core.EquivalencePathMap

/-!
概要：可換正方形が同じ可逆 path 置換に誘導する実射。
方針：path の射と源の射を同じ pullback に組み合わせる。
規約：二つの射影および終点との等号を厳密に保持する。
使われ方：Ind-S (4) の小模型で得た境界充填を元の関手圏へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 同じ可換正方形の二成分から、可逆 path 置換間の実射を作る。 -/
def equivalencePathReplacementInduced {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) : equivalencePathReplacement f ⟶ equivalencePathReplacement g :=
  pullback.lift
    (pullback.fst (equivalencePathEndpoint Y 0) f ≫ equivalencePathMap b)
    (equivalencePathReplacementProjection f ≫ a) (by
      rw [Category.assoc, equivalencePathMap_endpoint, ← Category.assoc, pullback.condition]
      change (equivalencePathReplacementProjection f ≫ f) ≫ b =
        (equivalencePathReplacementProjection f ≫ a) ≫ g
      rw [Category.assoc, h, Category.assoc])

lemma equivalencePathReplacementInduced_projection {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    equivalencePathReplacementInduced f g a b h ≫ equivalencePathReplacementProjection g =
      equivalencePathReplacementProjection f ≫ a := pullback.lift_snd _ _ _

lemma equivalencePathReplacementInduced_path {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    equivalencePathReplacementInduced f g a b h ≫
        pullback.fst (equivalencePathEndpoint Y' 0) g =
      pullback.fst (equivalencePathEndpoint Y 0) f ≫ equivalencePathMap b :=
  pullback.lift_fst _ _ _

lemma equivalencePathReplacementInduced_map {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    equivalencePathReplacementInduced f g a b h ≫ equivalencePathReplacementMap g =
      equivalencePathReplacementMap f ≫ b := by
  unfold equivalencePathReplacementMap
  rw [← Category.assoc, equivalencePathReplacementInduced_path, Category.assoc,
    equivalencePathMap_endpoint, ← Category.assoc]

end SerrePositivity.InfinityCategories

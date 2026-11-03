module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Presentable.SpaceFamilyStrictification
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinFaces
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinNaturality

/-!
概要：元の coherent な錐族を、同じ添字と WithInitial の積上の一つの strict Kan 図式へ移す。
方針：錐形状の宇宙同型で全錐を読み替え、共同 strictification と同じ逆同型で元へ戻す。
規約：全錐族の関手同型を構成する。各段階の極限性や余極限性の移送は別途必要。
使われ方：μ-filtered 余極限と小さい極限の native な交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable (I : Type u) [SmallCategory I]

/-- WithInitial の nerve と、元の大きい宇宙の錐形状との同型。 -/
def uliftInitialConeIso :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (WithInitial I)) ≅
      join (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) :=
  (SSet.uliftFunctor.{u + 1, u}).mapIso (initialJoinNerveIso I).symm ≪≫
    uliftConeShapeIso (nerve I) 0

/-- 同じ形状同型は、元の図式への包含を厳密に保つ。 -/
@[reassoc] lemma uliftInitialConeIso_inr :
    (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (WithInitial.incl : I ⥤ WithInitial I)) ≫ (uliftInitialConeIso I).hom =
      joinInr (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) := by
  have h : nerveMap (WithInitial.incl : I ⥤ WithInitial I) ≫
      (initialJoinNerveIso I).inv = joinInr (Δ[0] : SSet.{u}) (nerve I) := by
    apply (cancel_mono (initialJoinNerveIso I).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (joinInr_initialJoinNerveMap I).symm
  change (SSet.uliftFunctor.{u + 1, u}).map _ ≫
    ((SSet.uliftFunctor.{u + 1, u}).map (initialJoinNerveIso I).inv ≫
      (uliftConeShapeIso (nerve I) 0).hom) = _
  rw [← Category.assoc, ← Functor.map_comp, h]
  exact uliftConeShapeIso_inr (nerve I) 0

variable {I} {J : Type u} [SmallCategory J]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
    (ihom (join (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj SpaceInfinity.{u})

/-- 元の全錐族を、新しい始対象を付加した同じ圏上の図式の族に読み替える。 -/
def coneFamilyWithInitial :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (WithInitial I)))).obj SpaceInfinity.{u} :=
  F ≫ (pre (uliftInitialConeIso I).hom).app SpaceInfinity

/-- 各段階で選ばず、元の全錐族を一度に復元する strict Kan 図式。 -/
def coneFamilyStrictification : J × WithInitial I ⥤ KanObject.{u} :=
  spaceFamilyStrictification (coneFamilyWithInitial F)

/-- 同じ共同 strict 図式を元の全錐形状に戻した族。 -/
def coneFamilyStrictRealization :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
      (ihom (join (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj SpaceInfinity.{u} :=
  spaceFamilyStrictRealization (coneFamilyWithInitial F) ≫
    (pre (uliftInitialConeIso I).inv).app SpaceInfinity

/-- 元の全単体・全錐を一つの関手同型で同時に回収する。 -/
def coneFamilyStrictificationIso : FunctorIso (coneFamilyStrictRealization F) F := by
  have h := (spaceFamilyStrictificationIso (coneFamilyWithInitial F)).postcomp
    ((pre (uliftInitialConeIso I).inv).app SpaceInfinity)
  simpa only [coneFamilyStrictRealization, coneFamilyWithInitial, Category.assoc,
    ← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id, NatTrans.id_app,
    Category.comp_id] using h

end SerrePositivity.InfinityCategories.F2.Presentable

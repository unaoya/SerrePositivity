module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionColimitFamily
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：余極限へ貼り合わせた族は、同じ底上の cocartesian section の族になる。
方針：底上の等式は余極限の全脚で検査し、各辺は一つの項から回収する。
規約：各項や余極限に quasicategory 性を要求しない。
使われ方：core の所属の降下と合わせた全高次の貼り合わせ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 貼り合わせた元の図式は、指定した底上の同じ図式に重なる。 -/
lemma cocartesianSectionFamilyColimitUncurry_projection {J : Type v} [Category.{w} J]
    {T E B : SSet.{u}} (p : E ⟶ B) {D : J ⥤ Over B} (c : Cocone D)
    (hc : IsColimit ((Over.forget B).mapCocone c))
    (s : ∀ j, T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p (D.obj j).hom)
    (hs : ∀ {j k} (f : j ⟶ k), s j = s k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (D.map f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionFamilyColimitUncurry p c hc s hs ≫ p = fst c.pt.left T ≫ c.pt.hom := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionTensorCocone_isColimit c hc).hom_ext
  intro j
  change ((c.ι.app j).left ▷ T) ≫ (_ ≫ p) =
    ((c.ι.app j).left ▷ T) ≫ (fst c.pt.left T ≫ c.pt.hom)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionFamilyColimitUncurry_fac,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_projection, ← Category.assoc, whiskerRight_fst,
    Category.assoc]
  have hj : (c.ι.app j).left ≫ c.pt.hom = (D.obj j).hom := (c.ι.app j).w
  rw [hj]

/-- 貼り合わせた族は、元の始域方向の全ての辺を cocartesian に送る。 -/
lemma cocartesianSectionFamilyColimitUncurry_cocartesian
    {J : Type v} [Category.{w} J] [Small.{u} J]
    {T E B : SSet.{u}} (p : E ⟶ B) {D : J ⥤ Over B} (c : Cocone D)
    (hc : IsColimit ((Over.forget B).mapCocone c))
    (s : ∀ j, T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p (D.obj j).hom)
    (hs : ∀ {j k} (f : j ⟶ k), s j = s k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (D.map f))
    (x : T _⦋0⦌) (e : c.pt.left _⦋1⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionFamilyColimitUncurry p c hc s hs).app (Opposite.op ⦋1⦌)
        (e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋1⦌)
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective _ (isColimitOfPreserves ev hc) e
  change (c.ι.app j).left.app (Opposite.op ⦋1⦌) t = e at ht
  have hf := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) (t, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionFamilyColimitUncurry_fac p c hc s hs j)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionFamilyColimitUncurry p c hc s hs).app (Opposite.op ⦋1⦌)
    ((c.ι.app j).left.app (Opposite.op ⦋1⦌) t, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) = _ at hf
  rw [ht] at hf
  rw [hf]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_cocartesian (s j) x t

/-- 整合する元の section の族を、余極限上の同じ section の族へ貼り合わせる。 -/
def cocartesianSectionFamilyColimitLift {J : Type v} [Category.{w} J] [Small.{u} J]
    {T E B : SSet.{u}} (p : E ⟶ B) {D : J ⥤ Over B} (c : Cocone D)
    (hc : IsColimit ((Over.forget B).mapCocone c))
    (s : ∀ j, T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p (D.obj j).hom)
    (hs : ∀ {j k} (f : j ⟶ k), s j = s k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (D.map f)) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p c.pt.hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionFamilyColimitUncurry p c hc s hs)
    (cocartesianSectionFamilyColimitUncurry_projection p c hc s hs)
    (cocartesianSectionFamilyColimitUncurry_cocartesian p c hc s hs)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

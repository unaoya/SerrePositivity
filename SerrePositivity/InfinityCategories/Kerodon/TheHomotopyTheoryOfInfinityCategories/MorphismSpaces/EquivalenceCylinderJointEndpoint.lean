module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCylinder
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
概要：可逆円柱の両端を合わせた包含の単射性。
方針：coproduct の各単体は片側から来て、二つの区間の値は相異なる。
規約：パラメーターの単体集合は任意。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の両端を同時に指定した延長。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単体集合の二項 coproduct の各単体は左右いずれかから来る。
方針：評価が coproduct を保つことを使う。
規約：全次数での共同全射性。
使われ方：Kerodon §4.6.4（Tag 01KE） の円柱の両端の単射性。 -/
lemma sset_coprod_jointly_surjective (A B : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (x : (A ⨿ B).obj n) :
    (∃ a, (coprod.inl : A ⟶ A ⨿ B).app n a = x) ∨
      ∃ b, (coprod.inr : B ⟶ A ⨿ B).app n b = x := by
  have hc := isColimitOfPreserves ((evaluation _ (Type u)).obj n) (coprodIsCoprod A B)
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc x
  rcases j with ⟨j⟩
  cases j with
  | left => exact Or.inl ⟨y, hy⟩
  | right => exact Or.inr ⟨y, hy⟩

/-- 概要：可逆円柱の両端の coproduct からの射は単射。
方針：同じ端では第一射影で消し、異なる端では Bool の値の矛盾を使う。
規約：始域の quasicategory 性や非空性は不要。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の端点を厳密に固定する延長。 -/
instance equivalenceCylinderJointEndpoint_mono (A : SSet.{u}) :
    Mono (coprod.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A false) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A true)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  apply (mono_iff_injective _).2
  intro x y h
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ := sset_coprod_jointly_surjective A A n x <;>
    obtain ⟨b, rfl⟩ | ⟨b, rfl⟩ := sset_coprod_jointly_surjective A A n y
  · have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A false).app n a =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A false).app n b := by
      simpa only [← NatTrans.comp_app_apply, coprod.inl_desc] using h
    have hab : a = b := congrArg Prod.fst hh
    subst b
    rfl
  · have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A false).app n a =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A true).app n b := by
      simpa only [← NatTrans.comp_app_apply, coprod.inl_desc, coprod.inr_desc] using h
    have he := congrArg (fun z : (A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval.{u}).obj n ↦ ((z.2.obj 0).as).down) hh
    change false = true at he
    cases he
  · have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A true).app n a =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A false).app n b := by
      simpa only [← NatTrans.comp_app_apply, coprod.inl_desc, coprod.inr_desc] using h
    have he := congrArg (fun z : (A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval.{u}).obj n ↦ ((z.2.obj 0).as).down) hh
    change true = false at he
    cases he
  · have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A true).app n a =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A true).app n b := by
      simpa only [← NatTrans.comp_app_apply, coprod.inr_desc] using h
    have hab : a = b := congrArg Prod.fst hh
    subst b
    rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

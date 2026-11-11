module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
概要：join の二端包含を合わせた射の単射性。
方針：次数評価と型の余積で、左右の切断が異なることを使う。
規約：安定性や有限極限を仮定しない。使われ方：一般安定性判定の全錐比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

private lemma types_coprod_desc_mono {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hd : ∀ x y, f x ≠ g y) : Mono (coprod.desc f g) := by
  let e := Types.binaryCoproductIso X Y
  have he : e.inv ≫ coprod.desc f g = (↾(Sum.elim f g)) := by
    apply ConcreteCategory.hom_ext
    intro z
    cases z with
    | inl x =>
      simp only [comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Sum.elim_inl]
      exact ConcreteCategory.congr_hom (coprod.inl_desc f g) x
    | inr y =>
      simp only [comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Sum.elim_inr]
      exact ConcreteCategory.congr_hom (coprod.inr_desc f g) y
  have : Mono (e.inv ≫ coprod.desc f g) := by
    rw [he]
    apply (mono_iff_injective _).2
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (hf h)
      | inr y => exact False.elim (hd x y h)
    | inr x =>
      cases y with
      | inl y => exact False.elim (hd y x h.symm)
      | inr y => exact congrArg Sum.inr (hg h)
  have hfac : coprod.desc f g = e.hom ≫ (e.inv ≫ coprod.desc f g) := by simp
  rw [hfac]
  infer_instance

/-- join の左右の包含を合わせた射は単射。 -/
lemma joinEndpointPair_mono (K L : SSet.{u}) :
    Mono (coprod.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L)) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  let F := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋n⦌)
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L
  let e := PreservesColimitPair.iso F K L
  have hd : ∀ x y, (F.map a) x ≠ (F.map b) y := by
    intro x y h
    have hc := congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) _⦋n⦌ ↦ z.1.val) h
    change n + 1 = 0 at hc
    omega
  have : Mono (coprod.desc (F.map a) (F.map b)) :=
    types_coprod_desc_mono _ _ ((mono_iff_injective _).mp inferInstance)
      ((mono_iff_injective _).mp inferInstance) hd
  have he : e.hom ≫ F.map (coprod.desc a b) = coprod.desc (F.map a) (F.map b) := by
    change coprod.desc (F.map coprod.inl) (F.map coprod.inr) ≫ F.map (coprod.desc a b) = _
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, ← F.map_comp, coprod.inl_desc, coprod.inl_desc]
    · rw [coprod.inr_desc_assoc, ← F.map_comp, coprod.inr_desc, coprod.inr_desc]
  have : Mono (e.hom ≫ F.map (coprod.desc a b)) := by rw [he]; infer_instance
  have hfac : F.map (coprod.desc a b) = e.inv ≫ (e.hom ≫ F.map (coprod.desc a b)) := by simp
  change Mono (F.map (coprod.desc a b))
  rw [hfac]
  infer_instance
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

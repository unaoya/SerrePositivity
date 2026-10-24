module
public import SerrePositivity.InfinityCategories.Core.SliceMap

/-! General declarations moved verbatim from their original modules. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial

/-- 概要：coslice の二段階の制限は合成した図式の射による制限。
方針：錐の前合成を joinMap の合成則で比較する。
規約：f の後で g に制限する。
使われ方：Kerodon Proposition 5.2.5.1、相対制限の四角形の合成。 -/
lemma sliceUnderRestrict_comp {K L M X : SSet.{u}} (p : K ⟶ X)
    (f : L ⟶ K) (g : M ⟶ L) :
    sliceUnderRestrict p f ≫ sliceUnderRestrict (f ≫ p) g =
      sliceUnderRestrict p (g ≫ f) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  apply Subtype.ext
  change joinMap g (𝟙 _) ≫ (joinMap f (𝟙 _) ≫ σ.val) =
    joinMap (g ≫ f) (𝟙 _) ≫ σ.val
  rw [← Category.assoc, ← joinMap_comp, Category.comp_id]


/-- 概要：図式の同型に沿う coslice 制限は同型。
方針：逆射による錐の前合成が各次数で逆写像になることを示す。
規約：f の IsIso インスタンスを使う。
使われ方：Kerodon §4.3.6、Proposition 5.2.5.1 の標準単体による表示。 -/
instance sliceUnderRestrict_isIso {K L X : SSet.{u}} (p : K ⟶ X)
    (f : L ⟶ K) [IsIso f] : IsIso (sliceUnderRestrict p f) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro n
  apply (isIso_iff_bijective _).2
  constructor
  · intro σ τ h
    apply Subtype.ext
    have hh := congrArg (fun z ↦ joinMap (inv f) (𝟙 _) ≫ z.val) h
    change joinMap (inv f) (𝟙 _) ≫ (joinMap f (𝟙 _) ≫ σ.val) =
      joinMap (inv f) (𝟙 _) ≫ (joinMap f (𝟙 _) ≫ τ.val) at hh
    simpa only [← Category.assoc, ← joinMap_comp, IsIso.inv_hom_id,
      Category.comp_id, joinMap_id, Category.id_comp] using hh
  · intro τ
    refine ⟨⟨joinMap (inv f) (𝟙 _) ≫ τ.val, ?_⟩, ?_⟩
    · rw [← Category.assoc, joinInl_joinMap, Category.assoc, τ.property]
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    · apply Subtype.ext
      change joinMap f (𝟙 _) ≫ (joinMap (inv f) (𝟙 _) ≫ τ.val) = τ.val
      simp only [← Category.assoc, ← joinMap_comp, IsIso.hom_inv_id,
        Category.comp_id, joinMap_id, Category.id_comp]


end SerrePositivity.InfinityCategories

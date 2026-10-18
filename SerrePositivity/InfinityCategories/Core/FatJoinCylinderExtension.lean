module

public import SerrePositivity.InfinityCategories.Core.RelativeCylinderExtension
public import SerrePositivity.InfinityCategories.Core.FatJoinCoproductPushout
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinderJointEndpoint

/-!
概要：右因子を固定する fatJoin 上の可逆ホモトピーの円柱への延長。
方針：二つの端の fatJoin を右因子で貼り、左因子の可逆円柱へ単射で含める。
規約：右因子を全時刻で固定する。
使われ方：Kerodon Lemma 4.6.4.25 の同型から slice の円柱への構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右因子を固定した fatJoin 上の可逆ホモトピーは左因子の可逆円柱上へ延長できる。
方針：fatJoin の二つの端を右因子で貼り、相対的な円柱の延長補題を適用する。
規約：X は quasicategory、A と K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の固定図式上の同型から slice 内の同型への方向。 -/
lemma exists_fatJoinCylinder_extension_of_relative_homotopy (A K X : SSet.{u})
    [Quasicategory X] (f g : fatJoin A K ⟶ X)
    (hfg : fatJoinInr A K ≫ f = fatJoinInr A K ≫ g) (H : SSet.Homotopy f g)
    (hH : (fatJoinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst K Δ[1] ≫ fatJoinInr A K ≫ f)
    (hI : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated) :
    ∃ F : fatJoin (A ⊗ equivalenceInterval) K ⟶ X,
      fatJoinMap (equivalenceCylinderEndpoint A false) (𝟙 K) ≫ F = f ∧
      fatJoinMap (equivalenceCylinderEndpoint A true) (𝟙 K) ≫ F = g := by
  let d := coprod.desc (equivalenceCylinderEndpoint A false) (equivalenceCylinderEndpoint A true)
  let r := fatJoinMap (coprod.inl : A ⟶ A ⨿ A) (𝟙 K)
  let s := fatJoinMap (coprod.inr : A ⟶ A ⨿ A) (𝟙 K)
  let t := fatJoinMap d (𝟙 K)
  let q := fatJoinMap (fst A equivalenceInterval) (𝟙 K)
  have ht : Mono t := by dsimp [t, d]; infer_instance
  have hr : r ≫ t = fatJoinMap (equivalenceCylinderEndpoint A false) (𝟙 K) := by
    dsimp [r, t, d]
    rw [fatJoinMap_comp, coprod.inl_desc, Category.id_comp]
  have hs : s ≫ t = fatJoinMap (equivalenceCylinderEndpoint A true) (𝟙 K) := by
    dsimp [s, t, d]
    rw [fatJoinMap_comp, coprod.inr_desc, Category.id_comp]
  have hrq : r ≫ t ≫ q = 𝟙 _ := by
    rw [← Category.assoc, hr]
    dsimp [q]
    rw [fatJoinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, fatJoinMap_id]
  have hsq : s ≫ t ≫ q = 𝟙 _ := by
    rw [← Category.assoc, hs]
    dsimp [q]
    rw [fatJoinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, fatJoinMap_id]
  obtain ⟨F, h₀, h₁⟩ := exists_relativeCylinder_extension (fatJoinInr A K) r s
    (fatJoin_coproduct_isPushout A A K) t q hrq hsq f g hfg H hH hI
  refine ⟨F, ?_, ?_⟩
  · rw [← Category.assoc, hr] at h₀
    exact h₀
  · rw [← Category.assoc, hs] at h₁
    exact h₁

end SerrePositivity.InfinityCategories

module

public import SerrePositivity.InfinityCategories.Core.RelativeCylinderExtension
public import SerrePositivity.InfinityCategories.Core.JoinCoproductPushout
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinderJointEndpoint

/-!
概要：右因子を固定する join 上の可逆ホモトピーの円柱への延長。
方針：二つの端の join を右因子で貼り、左因子の可逆円柱へ単射で含める。
規約：右因子を全時刻で固定する。
使われ方：Kerodon Lemma 4.6.4.25 の同型から slice の円柱への構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右因子を固定した join 上の可逆ホモトピーは左因子の可逆円柱上へ延長できる。
方針：join の二つの端を右因子で貼り、相対的な円柱の延長補題を適用する。
規約：X は quasicategory、A と K は任意。
使われ方：Kerodon Lemma 4.6.4.25 の固定図式上の同型から slice 内の同型への方向。 -/
lemma exists_joinCylinder_extension_of_relative_homotopy (A K X : SSet.{u})
    [Quasicategory X] (f g : join A K ⟶ X)
    (hfg : joinInr A K ≫ f = joinInr A K ≫ g) (H : SSet.Homotopy f g)
    (hH : (joinInr A K ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst K Δ[1] ≫ joinInr A K ≫ f)
    (hI : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated) :
    ∃ F : join (A ⊗ equivalenceInterval) K ⟶ X,
      joinMap (equivalenceCylinderEndpoint A false) (𝟙 K) ≫ F = f ∧
      joinMap (equivalenceCylinderEndpoint A true) (𝟙 K) ≫ F = g := by
  let d := coprod.desc (equivalenceCylinderEndpoint A false) (equivalenceCylinderEndpoint A true)
  let r := joinMap (coprod.inl : A ⟶ A ⨿ A) (𝟙 K)
  let s := joinMap (coprod.inr : A ⟶ A ⨿ A) (𝟙 K)
  let t := joinMap d (𝟙 K)
  let q := joinMap (fst A equivalenceInterval) (𝟙 K)
  have ht : Mono t := by dsimp [t, d]; infer_instance
  have hr : r ≫ t = joinMap (equivalenceCylinderEndpoint A false) (𝟙 K) := by
    dsimp [r, t, d]
    rw [← joinMap_comp, coprod.inl_desc, Category.id_comp]
  have hs : s ≫ t = joinMap (equivalenceCylinderEndpoint A true) (𝟙 K) := by
    dsimp [s, t, d]
    rw [← joinMap_comp, coprod.inr_desc, Category.id_comp]
  have hrq : r ≫ t ≫ q = 𝟙 _ := by
    rw [← Category.assoc, hr]
    dsimp [q]
    rw [← joinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, joinMap_id]
  have hsq : s ≫ t ≫ q = 𝟙 _ := by
    rw [← Category.assoc, hs]
    dsimp [q]
    rw [← joinMap_comp, equivalenceCylinderEndpoint_fst, Category.id_comp, joinMap_id]
  obtain ⟨F, h₀, h₁⟩ := exists_relativeCylinder_extension (joinInr A K) r s
    (join_coproduct_isPushout A A K) t q hrq hsq f g hfg H hH hI
  refine ⟨F, ?_, ?_⟩
  · rw [← Category.assoc, hr] at h₀
    exact h₀
  · rw [← Category.assoc, hs] at h₁
    exact h₁

end SerrePositivity.InfinityCategories

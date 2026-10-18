module
public import SerrePositivity.InfinityCategories.Stable.RightJoinCoproduct
public import SerrePositivity.InfinityCategories.Core.RelativeCylinderExtension
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinderJointEndpoint

/-! # 余錐の可逆円柱への延長

概要：左図式を固定した可逆ホモトピーを、余錐の右因子の可逆円柱に延長する。
方針：両端を共通の左因子で貼り、相対的な円柱の持ち上げを使う。
規約：通常の join と fat join の両方を扱う。使われ方：余錐の族の比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：左図式を固定した join の可逆ホモトピーは右因子の可逆円柱へ延長できる。
方針：両端を左図式で貼り、相対円柱の延長を使う。
規約：値域は quasicategory。使われ方：coslice 内の同型の構成。 -/
lemma exists_joinRightCylinder_extension_of_relative_homotopy (A K X : SSet.{u})
    [Quasicategory X] (f g : join K A ⟶ X)
    (hfg : joinInl K A ≫ f = joinInl K A ≫ g) (H : SSet.Homotopy f g)
    (hH : (joinInl K A ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst K Δ[1] ≫ joinInl K A ≫ f)
    (hI : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated) :
    ∃ F : join K (A ⊗ equivalenceInterval) ⟶ X,
      joinMap (𝟙 K) (equivalenceCylinderEndpoint A false) ≫ F = f ∧
      joinMap (𝟙 K) (equivalenceCylinderEndpoint A true) ≫ F = g := by
  let d := coprod.desc (equivalenceCylinderEndpoint A false) (equivalenceCylinderEndpoint A true)
  let r := joinMap (𝟙 K) (coprod.inl : A ⟶ A ⨿ A)
  let s := joinMap (𝟙 K) (coprod.inr : A ⟶ A ⨿ A)
  let t := joinMap (𝟙 K) d
  let q := joinMap (𝟙 K) (fst A equivalenceInterval)
  have ht : Mono t := by dsimp [t, d]; infer_instance
  have hr : r ≫ t = joinMap (𝟙 K) (equivalenceCylinderEndpoint A false) := by
    dsimp [r, t, d]
    rw [← joinMap_comp, coprod.inl_desc, Category.id_comp]
  have hs : s ≫ t = joinMap (𝟙 K) (equivalenceCylinderEndpoint A true) := by
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
  obtain ⟨F, h₀, h₁⟩ := exists_relativeCylinder_extension (joinInl K A) r s
    (join_right_coproduct_isPushout A A K) t q hrq hsq f g hfg H hH hI
  refine ⟨F, ?_, ?_⟩
  · rw [← Category.assoc, hr] at h₀
    exact h₀
  · rw [← Category.assoc, hs] at h₁
    exact h₁


/-- 概要：左図式を固定した fatJoin の可逆ホモトピーは右因子の可逆円柱へ延長できる。
方針：両端を左図式で貼り、相対円柱の延長を使う。
規約：値域は quasicategory。使われ方：coslice 内の同型の構成。 -/
lemma exists_fatJoinRightCylinder_extension_of_relative_homotopy (A K X : SSet.{u})
    [Quasicategory X] (f g : fatJoin K A ⟶ X)
    (hfg : fatJoinInl K A ≫ f = fatJoinInl K A ≫ g) (H : SSet.Homotopy f g)
    (hH : (fatJoinInl K A ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst K Δ[1] ≫ fatJoinInl K A ≫ f)
    (hI : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated) :
    ∃ F : fatJoin K (A ⊗ equivalenceInterval) ⟶ X,
      fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A false) ≫ F = f ∧
      fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A true) ≫ F = g := by
  let d := coprod.desc (equivalenceCylinderEndpoint A false) (equivalenceCylinderEndpoint A true)
  let r := fatJoinMap (𝟙 K) (coprod.inl : A ⟶ A ⨿ A)
  let s := fatJoinMap (𝟙 K) (coprod.inr : A ⟶ A ⨿ A)
  let t := fatJoinMap (𝟙 K) d
  let q := fatJoinMap (𝟙 K) (fst A equivalenceInterval)
  have ht : Mono t := by dsimp [t, d]; infer_instance
  have hr : r ≫ t = fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A false) := by
    dsimp [r, t, d]
    rw [fatJoinMap_comp, coprod.inl_desc, Category.id_comp]
  have hs : s ≫ t = fatJoinMap (𝟙 K) (equivalenceCylinderEndpoint A true) := by
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
  obtain ⟨F, h₀, h₁⟩ := exists_relativeCylinder_extension (fatJoinInl K A) r s
    (fatJoin_right_coproduct_isPushout A A K) t q hrq hsq f g hfg H hH hI
  refine ⟨F, ?_, ?_⟩
  · rw [← Category.assoc, hr] at h₀
    exact h₀
  · rw [← Category.assoc, hs] at h₁
    exact h₁


end SerrePositivity.InfinityCategories

module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeCoconeBoundaryOverExtension
public import SerrePositivity.InfinityCategories.Core.JoinCoproductPushout
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinderJointEndpoint
/-!
概要：元の標的全図式を保つ、join 上の可逆円柱への相対延長。
方針：二端の join を右因子で貼り、標的の像を固定する境界延長を適用する。
規約：元の両端、右因子の図式、標的全図式を厳密に保つ。
使われ方：指定始点評価の下での余錐比較の相対反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：両端と右図式を保つ可逆円柱を、標的全図式の下で join 円柱へ延長する。
方針：二端を貼った単射の相対延長を使う。規約：元の全射を保持。使われ方：相対反映。 -/
lemma exists_joinCylinder_extension_of_equivalenceFamily_over
    {A K X Y : SSet.{u}} (p : X ⟶ Y) (hp : F1B.EquivalenceLifting p)
    (f g : join A K ⟶ X) (hfg : joinInr A K ≫ f = joinInr A K ≫ g)
    (V : join A K ⊗ equivalenceInterval ⟶ X)
    (h₀ : equivalenceCylinderEndpoint (join A K) false ≫ V = f)
    (h₁ : equivalenceCylinderEndpoint (join A K) true ≫ V = g)
    (hV : (joinInr A K ▷ equivalenceInterval) ≫ V =
      fst K equivalenceInterval ≫ joinInr A K ≫ f)
    (hVp : V ≫ p = fst (join A K) equivalenceInterval ≫ f ≫ p) :
    ∃ F : join (A ⊗ equivalenceInterval) K ⟶ X,
      joinMap (equivalenceCylinderEndpoint A false) (𝟙 K) ≫ F = f ∧
      joinMap (equivalenceCylinderEndpoint A true) (𝟙 K) ≫ F = g ∧
      F ≫ p = joinMap (fst A equivalenceInterval) (𝟙 K) ≫ f ≫ p := by
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
  let u := q ≫ f
  have hru : r ≫ t ≫ u = f := by simp only [u, ← Category.assoc, hrq, Category.id_comp]
  have hsu : s ≫ t ≫ u = f := by simp only [u, ← Category.assoc, hsq, Category.id_comp]
  obtain ⟨F, hFt, hFf, hFp⟩ := exists_extension_of_equivalenceFamily_fixed_boundary_over
    p hp (join_coproduct_isPushout A A K).flip t u g
    (by rw [hru]; exact hfg.symm) V (h₀.trans hsu.symm) h₁
    (by rw [hru]; exact hV) (by
      change V ≫ p = fst (join A K) equivalenceInterval ≫ s ≫ t ≫ u ≫ p
      rw [← Category.assoc t u p, ← Category.assoc s (t ≫ u) p, hsu]
      exact hVp)
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [← hr, Category.assoc]
    exact hFf.trans hru
  · rw [← hs, Category.assoc]
    exact hFt
  · exact hFp
end SerrePositivity.InfinityCategories.F2.Ind

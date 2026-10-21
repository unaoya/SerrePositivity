module

public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryComparison

/-!
概要：一次元境界の同じ分類比較を両端へ射影すると、元の両端の比較となる。
方針：同じ二つの積分解の往復と射影を計算する。
規約：元の境界の同じ四つの直接制限を保持する。
使われ方：境界全体の同じ比較と元の大域 Hom 作用との整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (i : Fin 2) (σ : (Δ[1] : SSet.{u}) ⟶ nerve C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 同じ境界比較を target の積表示へ戻すと、元の両端の比較の直積。 -/
lemma cocartesianOneBoundaryHomComparison_targetProduct :
    cocartesianOneBoundaryHomComparison i σ p q ≫
      (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom =
    (cocartesianOneBoundaryNativeProductIso i σ p.val.hom q.val.hom).hom ≫
      (cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q ⊗ₘ
        cocartesianOneHornHomComparison i σ p q) := by
  simp only [cocartesianOneBoundaryHomComparison, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- 同じ境界比較の第一射影は、元の面側の端点への制限と同じ零次元比較。 -/
lemma cocartesianOneBoundaryHomComparison_face :
    (cocartesianOneBoundaryHomComparison i σ p q ≫
      (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom) ≫ fst _ _ =
    cocartesianPullbackNativeLiftPre p.val.hom q.val.hom (HornBoundaryOver.faceInclusion 0 i σ) ≫
      cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q := by
  rw [cocartesianOneBoundaryHomComparison_targetProduct, Category.assoc]
  have h := congrArg
    (fun k ↦ (cocartesianOneBoundaryNativeProductIso i σ p.val.hom q.val.hom).hom ≫ k)
    (tensorHom_fst (cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q)
      (cocartesianOneHornHomComparison i σ p q))
  exact h.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k ↦ k ≫ cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q)
      (cocartesianOneBoundaryNativeProductIso_hom_fst i σ p.val.hom q.val.hom)))

/-- 同じ境界比較の第二射影は、元のホーン側の端点への制限と同じ零次元比較。 -/
lemma cocartesianOneBoundaryHomComparison_horn :
    (cocartesianOneBoundaryHomComparison i σ p q ≫
      (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom) ≫ snd _ _ =
    cocartesianPullbackNativeLiftPre p.val.hom q.val.hom (HornBoundaryOver.hornInclusion 0 i σ) ≫
      cocartesianOneHornHomComparison i σ p q := by
  rw [cocartesianOneBoundaryHomComparison_targetProduct, Category.assoc]
  have h := congrArg
    (fun k ↦ (cocartesianOneBoundaryNativeProductIso i σ p.val.hom q.val.hom).hom ≫ k)
    (tensorHom_snd (cocartesianStandardSimplexHomComparison (stdSimplex.δ i ≫ σ) p q)
      (cocartesianOneHornHomComparison i σ p q))
  exact h.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k ↦ k ≫ cocartesianOneHornHomComparison i σ p q)
      (cocartesianOneBoundaryNativeProductIso_hom_snd i σ p.val.hom q.val.hom)))

end SerrePositivity.InfinityCategories

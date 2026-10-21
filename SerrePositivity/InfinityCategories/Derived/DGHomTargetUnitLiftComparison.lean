module
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetUnitComparison
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetCosliceComparison
public import SerrePositivity.InfinityCategories.Derived.DGClosedHomWhiskerNaturality
/-!
概要：同じ Hom 単位による比較鎖同型を、対象だけの共通宇宙持ち上げ後にも保つ。
方針：実 dg 関手の閉前合成自然性と、その恒等 Hom 鎖写像を使う。
規約：入力の小ささも元の出力の射影性も不要。使われ方：実 Hom 単位の全 coslice fiber 同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C] (x y : C)
/-- 対象宇宙持ち上げ後の同じ比較鎖写像も、元の同じ dg Yoneda 同型の逆。 -/
lemma dgHomTargetUnitLiftHomMap_eq :
    (dgHomTargetModuleLift R C x).map x y ≫
      eHomWhiskerRight (Complex R)
        ((dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map
          (dgHomTargetUnit R C x))
        (ForgetEnrichment.of (Complex R) ((dgHomTargetModuleLift R C x).obj y)) =
      (dgYonedaIso R PUnit.unit ((dgHomTargetModuleDG R C x).obj y)).inv := by
  have h := dgFunctorHom_precompose
    (dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1}))
    (dgHomTargetUnit R C x)
    (ForgetEnrichment.of (Complex R) ((dgHomTargetModuleDG R C x).obj y))
  simp only [dgUniverseLiftUp, Category.comp_id, Category.id_comp] at h
  dsimp only [dgHomTargetModuleLift, EnrichedFunctor.comp_map]
  change ((dgHomTargetModuleDG R C x).map x y ≫ 𝟙 _) ≫
    eHomWhiskerRight (Complex R)
      ((dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map
        (dgHomTargetUnit R C x))
      (ForgetEnrichment.of (Complex R) ((dgHomTargetModuleLift R C x).obj y)) = _
  rw [Category.comp_id]
  erw [← h]
  exact dgHomTargetUnitHomMap_eq R C x y
/-- 持ち上げた同じ実 Hom 単位の比較鎖写像は全次数の鎖同型。 -/
lemma dgHomTargetUnitLiftHomMap_isIso :
    IsIso ((dgHomTargetModuleLift R C x).map x y ≫
      eHomWhiskerRight (Complex R)
        ((dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map
          (dgHomTargetUnit R C x))
        (ForgetEnrichment.of (Complex R) ((dgHomTargetModuleLift R C x).obj y))) := by
  rw [dgHomTargetUnitLiftHomMap_eq]
  infer_instance
end SerrePositivity.InfinityCategories

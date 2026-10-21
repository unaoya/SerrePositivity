module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactorAugmentationSquare
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionLocalization
/-!
概要：元の raw factor 比較と全加群の局所化 augmentation の正方形を等式で表す。
方針：恒等 dg 関手の実 augmentation と同じ円柱を保って端点を正規化する。
規約：元の指定切断と同じ類を保つ。使われ方：K-flat 降下比較と指定合成子の経路照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 元の raw factor 比較は、元の局所化 augmentation と同じ型の正方形で可換である。 -/
lemma dgModuleResolvedInfinity_rawFactorIso_augmentation (J : DGFunctor R C (RightModule R E)) :
    ((dgModuleResolvedInfinity_rawFactorIso R C E J).postcomp
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E)))).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp (dgModuleResolutionAugmentationHomotopy R E) (dgNerve.map J))) =
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgModuleResolvedAugmentationHomotopy R C E J)) := by
  let a := (dgModuleResolvedInfinity_rawFactorIso R C E J).postcomp
    (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
      (dgModuleSemifreeProperty R E)))
  let B₀ := functorHomotopyPrecomp
    (dgModuleResolvedAugmentationHomotopy R (RightModule R E) E
      (DGFunctor.id (RightModule R E))) (dgNerve.map J)
  let B₁ := functorHomotopyPrecomp (dgModuleResolutionAugmentationHomotopy R E) (dgNerve.map J)
  have hb := functorHomotopyHom_heq_of_raw_eq B₀ B₁ rfl
  have ht := functorHomotopy_endpoints_of_raw_eq B₀ B₁ rfl
  have hp := functorHom_comp_heq a.hom
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy B₀))
    a.hom (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy B₁))
    rfl ht.1 ht.2 (HEq.refl _) hb
  exact eq_of_heq (hp.symm.trans (dgModuleResolvedInfinity_rawFactorIso_augmentation_heq R C E J))
end SerrePositivity.InfinityCategories

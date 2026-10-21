module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecompAugmentationSquare
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactorNaturality
/-!
概要：元の raw factor 比較と元の実 augmentation の正方形を照合する。
方針：一般前合成正方形を恒等関手へ特殊化し、元の指定比較の厳密な単位輸送を保つ。
規約：生の augmentation の可逆性を要求しない。使われ方：K-flat の同じ合成子の経路比較。
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
private lemma augmentation_hom_heq_of_output_eq
    {F G : DGFunctor R C (RightModule R E)} (h : F = G) :
    HEq (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgModuleResolvedAugmentationHomotopy R C E F)))
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgModuleResolvedAugmentationHomotopy R C E G))) := by
  subst G
  rfl
/-- 元の raw factor 比較と元の実 augmentation は、同じ全関手射の正方形を満たす。 -/
lemma dgModuleResolvedInfinity_rawFactorIso_augmentation_heq (J : DGFunctor R C (RightModule R E)) :
    HEq (((dgModuleResolvedInfinity_rawFactorIso R C E J).postcomp
      (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E)))).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp
          (dgModuleResolvedAugmentationHomotopy R (RightModule R E) E
            (DGFunctor.id (RightModule R E))) (dgNerve.map J))))
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgModuleResolvedAugmentationHomotopy R C E J))) := by
  let I := dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
    (dgModuleSemifreeProperty R E))
  let L : DGFunctor R (RightModule R E) (RightModule R E) :=
    DGFunctor.id (RightModule R E)
  let K := J.comp L
  let p := dgModuleResolvedInfinity_precompIso R C (RightModule R E) E J L
  let b := dgModuleResolvedInfinity_rawFactorIso R C E J
  let T := functorHomotopyPrecomp
    (dgModuleResolvedAugmentationHomotopy R (RightModule R E) E L) (dgNerve.map J)
  have hK : K = J := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [K, L, EnrichedFunctor.comp_map, EnrichedFunctor.id_map,
      eqToHom_refl, Category.comp_id]
  have hs := congrArg (dgModuleResolvedInfinity R C E) hK
  have h1 := F2.functorIso_postcomp_heq_of_heq b p hs.symm rfl
    (dgModuleResolvedInfinity_rawFactorIso_heq R C E J).symm I
  have hHom := functorIso_hom_heq (p.postcomp I) (b.postcomp I)
    (congrArg (fun m => m ≫ I) hs) rfl h1
  have hComp := functorHom_comp_heq (p.postcomp I).hom
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy T))
    (b.postcomp I).hom
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy T))
    (congrArg (fun m => m ≫ I) hs) rfl rfl hHom (HEq.refl _)
  have hSquare := dgModuleResolvedInfinity_precompIso_augmentation_heq
    R C (RightModule R E) E J L
  have hRight := augmentation_hom_heq_of_output_eq R C E hK
  exact hComp.symm.trans (hSquare.trans hRight)
end SerrePositivity.InfinityCategories

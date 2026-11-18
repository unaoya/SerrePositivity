module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductAWLastCut
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerNegativeTensorCoefficients
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedAWRightAugmentationCut
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductFrameCoaction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterAugmentation
/-!
概要：指定AWの右増大写像則。方針：切断和を最後の切断へ帰着する。
規約：元の係数比較と標準単体の増大写像を保持する。IS-W2 A05a。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open AlgebraicTopology AlgebraicTopology.DoldKan HomologicalComplex
open SerrePositivity.HomologicalAlgebra
open scoped Simplicial TensorProduct
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 指定AWの右増大写像則（IS-W2 A05a）。 -/
theorem freeProductAlexanderWhitney_right_augmentation (A : Type u) [CommRing A]
    (φ : simplicialRingCoefficient.{u} →+* A) (Z : SSet.{u}) (n : SimplexCategory) :
  freeProductAlexanderWhitney φ Z
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) ≫
    (𝟙 (freeNegativeChains (A := A) Z) ⊗ₘ
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom) ≫
    (ρ_ (freeNegativeChains (A := A) Z)).hom =
    freeNegativeChainsMap (A := A)
      (fst Z ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n))) := by
  let Y := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)
  let ε : freeNegativeChains (A := A) Y ⟶ 𝟙_ (CochainComplex (ModuleCat A) ℤ) :=
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom
  change freeProductAlexanderWhitney φ Z Y ≫ (𝟙 _ ⊗ₘ ε) ≫ (ρ_ _).hom =
    freeNegativeChainsMap (A := A) (fst Z Y)
  have haug (j : ℕ) (hj : j ≠ 0) :
      ε.f (-(j : ℤ)) = 0 := by
    exact (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) (-(j : ℤ))
      (by omega)).eq_of_tgt _ _
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hq : 0 < q
  · apply (((normalizedMooreComplex (ModuleCat A)).obj
      ((Z ⊗ Y) ⋙ ModuleCat.free A)).isZero_extend_X
        ComplexShape.embeddingDownNat q (fun k hk => by
          change -(k : ℤ) = q at hk
          omega)).eq_of_src
  · have hq' : q ≤ 0 := le_of_not_gt hq
    obtain ⟨k, hk⟩ : ∃ k : ℕ, q = -(k : ℤ) := ⟨(-q).toNat, by omega⟩
    subst q
    let M := (Z ⊗ Y) ⋙ ModuleCat.free A
    let K := (normalizedMooreComplex (ModuleCat A)).obj M
    let e := K.extendXIso ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl
    apply (cancel_epi e.inv).1
    let π := (PInftyToNormalizedMooreComplex M).f k
    have : IsSplitEpi π := IsSplitEpi.mk' {
      section_ := (inclusionOfMooreComplexMap M).f k
      id := congrArg (fun f => f.f k) (splitMonoInclusionOfMooreComplexMap M).id }
    apply (cancel_epi π).1
    apply ModuleCat.free_hom_ext
    intro x
    let e0 := Functor.isoWhiskerRight (linearizedTensorIso Z Y) (integerCoefficientExtension φ) ≪≫
      integerCoefficientSimplicialFreeIso φ (Z ⊗ Y)
    have hsrc (v : M.obj (Opposite.op ⦋k⦌)) :
        ((normalizedMooreComplex (ModuleCat A)).map e0.inv).f k (π v) =
          (PInftyToNormalizedMooreComplex
            (simplicialIntegerTensor (linearizedSpace Z) (linearizedSpace Y) ⋙
              integerCoefficientExtension φ)).f k (e0.inv.app (Opposite.op ⦋k⦌) v) := by
      exact congrArg (fun f => f.f k v)
        (PInftyToNormalizedMooreComplex_naturality e0.inv).symm
    have hproj := congrArg (fun f => f.f k)
      (PInftyToNormalizedMooreComplex_naturality
        (Functor.whiskerRight (fst Z Y) (ModuleCat.free A)))
    change (ModuleCat.free A).map ((fst Z Y).app (Opposite.op ⦋k⦌)) ≫
        (PInftyToNormalizedMooreComplex (Z ⋙ ModuleCat.free A)).f k =
      π ≫ ((normalizedMooreComplex (ModuleCat A)).map
        (Functor.whiskerRight (fst Z Y) (ModuleCat.free A))).f k at hproj
    dsimp only [freeNegativeChainsMap]
    erw [extendMap_f _ ComplexShape.embeddingDownNat (i := k) rfl]
    dsimp only [e, K, M]
    erw [Iso.inv_hom_id_assoc]
    erw [← Category.assoc π (((normalizedMooreComplex (ModuleCat A)).map
      (Functor.whiskerRight (fst Z Y) (ModuleCat.free A))).f k) _, ← hproj]
    simp only [Category.assoc, ModuleCat.comp_apply, ModuleCat.free_map_apply]
    dsimp only [freeProductAlexanderWhitney, integerCoefficientProductChainsIso,
      Functor.mapIso_inv]
    simp only [comp_f, ModuleCat.comp_apply]
    dsimp only [ComplexShape.Embedding.extendFunctor]
    erw [extendMap_f _ ComplexShape.embeddingDownNat (i := k) rfl]
    simp only [ModuleCat.comp_apply]
    erw [Iso.inv_hom_id_apply, hsrc]
    dsimp only [negativeCoefficientAlexanderWhitney]
    simp only [comp_f, ModuleCat.comp_apply]
    erw [extendMap_f _ ComplexShape.embeddingDownNat (i := k) rfl]
    simp only [ModuleCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
    dsimp only [mappedNormalizedAlexanderWhitney, normalizedMooreMapIso,
      normalizedMooreMapInv]
    simp only [comp_f, ModuleCat.comp_apply]
    have hsplit := congrArg
      (fun f => f.f k (e0.inv.app (Opposite.op ⦋k⦌) (ModuleCat.freeMk x)))
      (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap
        (simplicialIntegerTensor (linearizedSpace Z) (linearizedSpace Y) ⋙
          integerCoefficientExtension φ))
    erw [hsplit]
    dsimp only [alternatingFaceMapComplexCompMapHomologicalComplexIso]
    let T := simplicialIntegerTensor (linearizedSpace Z) (linearizedSpace Y)
    let F := integerCoefficientExtension φ
    have hpmap := congrArg (fun f => f.f k) (alternatingMapIso_PInfty F T)
    change F.map ((PInfty (X := T)).f k) ≫ 𝟙 _ =
      𝟙 _ ≫ (PInfty (X := T ⋙ F)).f k at hpmap
    simp only [Category.comp_id, Category.id_comp] at hpmap
    erw [← hpmap]
    erw [← ModuleCat.comp_apply (F.map ((PInfty (X := T)).f k))
      (F.map ((PInftyToNormalizedMooreComplex T).f k))]
    rw [← F.map_comp]
    have hpi := congrArg (fun f => f.f k) (PInfty_comp_PInftyToNormalizedMooreComplex T)
    dsimp only [comp_f] at hpi
    erw [hpi]
    erw [← ModuleCat.comp_apply (F.map ((PInftyToNormalizedMooreComplex T).f k))
      (F.map ((normalizedAlexanderWhitney (linearizedSpace Z) (linearizedSpace Y)).f k))]
    rw [← F.map_comp]
    dsimp only [normalizedAlexanderWhitney, comp_f]
    erw [← Category.assoc ((PInftyToNormalizedMooreComplex T).f k)
      ((inclusionOfMooreComplexMap T).f k) _]
    have hpin := congrArg (fun f => f.f k)
      (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap T)
    dsimp only [comp_f] at hpin
    erw [hpin]
    let NC := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Z)
    let ND := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)
    let out : ((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor NC ND)).X k ⟶
        (freeNegativeChains (A := A) Z).X (-(k : ℤ)) :=
      (((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor NC ND)).extendXIso
        ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl).inv ≫
      ((negativeMooreTensorCoefficientIso φ (linearizedSpace Z) (linearizedSpace Y)).hom ≫
        (tensorIso (integerCoefficientFreeChainsIso φ Z)
          (integerCoefficientFreeChainsIso φ Y)).hom ≫
        (𝟙 _ ⊗ₘ ε) ≫
        (ρ_ (freeNegativeChains (A := A) Z)).hom).f (-(k : ℤ))
    have hout (i j : ℕ) (h : i + j = k) (hj : j ≠ 0) :
        F.map (ιMapBifunctor NC ND integerTensorBifunctor (.down ℕ) i j k h) ≫ out = 0 := by
      dsimp only [out, negativeMooreTensorCoefficientIso, Iso.trans_hom,
        tensorIso_hom, Functor.mapIso_hom]
      simp only [comp_f, Category.assoc]
      erw [reassoc_of% (integerNegativeTensorBaseChangeIso_ι φ NC ND i j k h)]
      rw [DifferentialGraded.ι_tensorHom_assoc,
        DifferentialGraded.ι_tensorHom_assoc, DifferentialGraded.ι_tensorHom_assoc]
      simp only [id_f, haug j hj, MonoidalPreadditive.tensor_zero, Limits.zero_comp, Limits.comp_zero]
    let γ := (chainIntegerTensorMap (PInftyToNormalizedMooreComplex (linearizedSpace Z))
      (PInftyToNormalizedMooreComplex (linearizedSpace Y))).f k
    have hsum : F.map ((alexanderWhitney (linearizedSpace Z) (linearizedSpace Y)).f k ≫ γ) ≫ out =
        F.map (alexanderWhitneySummand (linearizedSpace Z) (linearizedSpace Y)
          k (Fin.last k) ≫ γ) ≫ out := by
      change F.map ((∑ t : Fin (k + 1),
        alexanderWhitneySummand (linearizedSpace Z) (linearizedSpace Y) k t) ≫ γ) ≫ out = _
      rw [Preadditive.sum_comp, F.map_sum, Preadditive.sum_comp]
      apply Finset.sum_eq_single (Fin.last k)
      · intro t _ ht
        have hj : k - (t : ℕ) ≠ 0 := by
          intro hz
          apply ht
          apply Fin.ext
          have := t.isLt
          simp only [Fin.val_last]
          omega
        dsimp only [alexanderWhitneySummand, γ]
        rw [Category.assoc, ι_chainIntegerTensorMap]
        simp only [Functor.map_comp, Category.assoc]
        erw [hout (t : ℕ) (k - t) (awDegrees k t) hj]
        simp only [Limits.comp_zero]
      · intro ht
        exact False.elim (ht (Finset.mem_univ _))
    change out (F.map ((PInfty (X := T)).f k ≫
      (alexanderWhitney (linearizedSpace Z) (linearizedSpace Y)).f k ≫ γ)
      (e0.inv.app (Opposite.op ⦋k⦌) (ModuleCat.freeMk x))) = _
    rw [F.map_comp]
    have hsumx := congrArg (fun f => f (F.map ((PInfty (X := T)).f k)
      (e0.inv.app (Opposite.op ⦋k⦌) (ModuleCat.freeMk x)))) hsum
    erw [hsumx]
    have hlast := freeProductAlexanderWhitney_last_cut_right_augmentation A φ Z n k
    erw [hlast]
    simp only [ModuleCat.comp_apply]
    have heP := PInfty_f_naturality k e0.hom
    have hePx := congrArg (fun f => f (e0.inv.app (Opposite.op ⦋k⦌) (ModuleCat.freeMk x))) heP
    simp only [ModuleCat.comp_apply] at hePx
    erw [hpmap, ← hePx]
    have hc := ConcreteCategory.congr_hom
      (NatTrans.congr_app e0.inv_hom_id (Opposite.op ⦋k⦌)) (ModuleCat.freeMk x)
    erw [hc]
    have hfstP := PInfty_f_naturality k
      (Functor.whiskerRight (fst Z Y) (ModuleCat.free A))
    have hfstPx := congrArg (fun f => f (ModuleCat.freeMk x)) hfstP
    simp only [ModuleCat.comp_apply] at hfstPx
    erw [← hfstPx]
    have hπP := congrArg (fun f => f.f k)
      (PInfty_comp_PInftyToNormalizedMooreComplex (Z ⋙ ModuleCat.free A))
    dsimp only [comp_f] at hπP
    erw [← ModuleCat.comp_apply _ ((PInftyToNormalizedMooreComplex (Z ⋙ ModuleCat.free A)).f k), hπP]
    erw [ModuleCat.free_map_apply]
    rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

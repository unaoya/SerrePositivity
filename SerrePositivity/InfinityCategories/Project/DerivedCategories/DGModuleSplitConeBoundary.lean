module
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

/-!
概要：閉分裂する右 dg 加群の cone 射影に全 dg 自然な収縮を与える。
方針：cone の左右成分と同じ閉射影から次数 −1 の Hom end 要素を構成する。
規約：対象ごとのホモトピーの選択で全 dg 自然性を代用しない。
使われ方：K-B に渡す同じ分裂四角形の cofiber 判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Category Limits DifferentialGraded HomologicalComplex CochainComplex
  HomComplex

lemma complexSplitCone_boundary {A : Type u} [CommRing A] {M N P : Complex A}
    (a : M ⟶ N) (r : N ⟶ M) (b : P ⟶ N) (p : N ⟶ P)
    (har : a ≫ r = 𝟙 M) (hap : a ≫ p = 0) (hs : r ≫ a + p ≫ b = 𝟙 N) :
    δ (-1) 0 (-((mappingCone.snd a).comp
      ((Cochain.ofHom r).comp (mappingCone.inl a) (zero_add (-1))) (zero_add (-1)))) =
      Cochain.ofHom (complexConeDesc a p hap ≫ b ≫ mappingCone.inr a) -
        Cochain.ofHom (𝟙 (mappingCone a)) := by
  simp only [δ_neg, δ_comp (mappingCone.snd a) _ (zero_add (-1)) 1 0 0
      (by decide) (by decide) (by decide),
    δ_ofHom_comp r (mappingCone.inl a) 0, mappingCone.δ_snd, mappingCone.δ_inl]
  rw [mappingCone.ext_cochain_from_iff a (-1) 0 (by decide)]
  constructor
  · simp only [Int.reduceNeg, Cochain.ofHom_comp, Int.negOnePow_neg, Int.negOnePow_one,
    Cochain.neg_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain, smul_neg, Units.neg_smul, one_smul, neg_neg,
      neg_add_rev,
    Cochain.comp_add, Cochain.comp_neg, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc,
      neg_zero, add_zero,
    complexConeDesc_ofHom, Cochain.comp_sub, Cochain.comp_id, zero_sub,
    neg_inj]
    rw [← Cochain.comp_assoc (Cochain.ofHom a) (Cochain.ofHom r)
      (mappingCone.inl a) (zero_add 0) (zero_add (-1)) (show (0 : ℤ) + 0 + (-1) = -1 by decide),
      ← Cochain.ofHom_comp, har]
    simp
  · simp only [Cochain.ofHom_comp, Int.reduceNeg, Int.negOnePow_neg, Int.negOnePow_one,
    Cochain.neg_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain, smul_neg, Units.neg_smul, one_smul, neg_neg,
      neg_add_rev,
    Cochain.comp_add, Cochain.comp_neg, mappingCone.inr_fst_assoc, neg_zero,
      mappingCone.inr_snd_assoc, zero_add,
    complexConeDesc_ofHom, Cochain.comp_sub, Cochain.comp_id]
    simp only [← Cochain.ofHom_comp, ← Cochain.ofHom_neg, ← Cochain.ofHom_sub]
    apply congrArg Cochain.ofHom
    rw [← Category.assoc r a, eq_sub_of_add_eq hs, Preadditive.sub_comp,
      Category.id_comp, neg_sub, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Derived.ComplexMappingCoconeBiprod
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
/-!
概要：二成分の差の mapping cocone は、第二 cocone と第一成分の間の真の短完全列を持つ。
方針：同じ実二射影で r・s の三分裂恒等式を検証し、次数ごとの分裂から短完全性を得る。
規約：準同型性や acyclic 性は仮定しない。使われ方：出力分解 Hom の射影判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex
variable {A : Type u} [Category.{v} A] [Abelian A]
  {K L T : CochainComplex A ℤ} (a : K ⟶ T) (b : L ⟶ T)
/-- 同じ実短複体は、各次数で指定 r・s によって分裂する。 -/
def complexMappingCoconeBiprodSplitting (j : ℤ) :
    ((complexMappingCoconeBiprodShortComplex a b).map
      (HomologicalComplex.eval A (ComplexShape.up ℤ) j)).Splitting where
  r := (complexMappingCoconeBiprodRetraction a b).v j j (add_zero j)
  s := (complexMappingCoconeBiprodSection a b).v j j (add_zero j)
  f_r := by
    change (complexMappingCoconeBiprodInclusion a b).f j ≫
      (complexMappingCoconeBiprodRetraction a b).v j j (add_zero j) = 𝟙 _
    apply complexMappingCocone_X_ext b j
    · rw [Category.assoc, complexMappingCoconeBiprodRetraction_fst, ← Category.assoc]
      rw [complexMappingCoconeBiprodInclusion, complexMappingCoconeMap_f_fst_f]
      rw [Category.assoc, ← HomologicalComplex.comp_f, biprod.inr_snd,
        HomologicalComplex.id_f, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, complexMappingCoconeBiprodRetraction_snd]
      rw [complexMappingCoconeBiprodInclusion, complexMappingCoconeMap_f_snd_v]
      simp only [HomologicalComplex.id_f, Category.comp_id, Category.id_comp]
  s_g := by
    change (complexMappingCoconeBiprodSection a b).v j j (add_zero j) ≫
      ((mappingCocone.fst (biprod.desc a b)).f j ≫ (biprod.fst : K ⊞ L ⟶ K).f j) = 𝟙 _
    rw [← Category.assoc, complexMappingCoconeBiprodSection_fst,
      ← HomologicalComplex.comp_f, biprod.inl_fst, HomologicalComplex.id_f]
  id := by
    change (complexMappingCoconeBiprodRetraction a b).v j j (add_zero j) ≫
        (complexMappingCoconeBiprodInclusion a b).f j +
      (complexMappingCoconeBiprodProjection a b).f j ≫
        (complexMappingCoconeBiprodSection a b).v j j (add_zero j) = 𝟙 _
    apply complexMappingCocone_X_ext (biprod.desc a b) j
    · simp only [Preadditive.add_comp, Category.id_comp]
      rw [Category.assoc, complexMappingCoconeBiprodInclusion,
        complexMappingCoconeMap_f_fst_f, ← Category.assoc,
        complexMappingCoconeBiprodRetraction_fst]
      rw [Category.assoc ((complexMappingCoconeBiprodProjection a b).f j)
        ((complexMappingCoconeBiprodSection a b).v j j (add_zero j))
        ((mappingCocone.fst (biprod.desc a b)).f j), complexMappingCoconeBiprodSection_fst]
      change ((mappingCocone.fst (biprod.desc a b)).f j ≫
          (biprod.snd : K ⊞ L ⟶ L).f j) ≫ (biprod.inr : L ⟶ K ⊞ L).f j +
        ((mappingCocone.fst (biprod.desc a b)).f j ≫
          (biprod.fst : K ⊞ L ⟶ K).f j) ≫ (biprod.inl : K ⟶ K ⊞ L).f j = _
      have ht := congrArg (fun f : K ⊞ L ⟶ K ⊞ L ↦ f.f j)
        (biprod.total (X := K) (Y := L))
      change (biprod.fst : K ⊞ L ⟶ K).f j ≫ (biprod.inl : K ⟶ K ⊞ L).f j +
        (biprod.snd : K ⊞ L ⟶ L).f j ≫ (biprod.inr : L ⟶ K ⊞ L).f j = 𝟙 _ at ht
      rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, add_comm, ht,
        Category.comp_id]
    · simp only [Preadditive.add_comp, Category.id_comp]
      rw [Category.assoc, complexMappingCoconeBiprodInclusion,
        complexMappingCoconeMap_f_snd_v, HomologicalComplex.id_f, Category.comp_id,
        complexMappingCoconeBiprodRetraction_snd]
      rw [Category.assoc, complexMappingCoconeBiprodSection_snd, comp_zero, add_zero]
/-- 同じ実 cocone の短複体は、複体の圏で短完全。 -/
lemma complexMappingCoconeBiprodShortComplex_shortExact :
    (complexMappingCoconeBiprodShortComplex a b).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  exact (complexMappingCoconeBiprodSplitting a b j).shortExact
end SerrePositivity.InfinityCategories

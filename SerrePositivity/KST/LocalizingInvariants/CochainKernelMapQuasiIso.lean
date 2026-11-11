module

public import SerrePositivity.KST.LocalizingInvariants.CochainKernelCoconeQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.CochainMappingCoconeMapQuasiIso

/-!
概要：次数全射な複体射の間の準同型正方形は、実 kernel にも準同型を誘導する。
方針：実 kernel と mapping cocone の標準比較の自然性と二対三を使う。
規約：非有界複体に適用し、元の kernel 射を保つ。使われ方：共通底上の層比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K₁ L₁ K₂ L₂ : Complex R}
  (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
  (h : d₁ ≫ b = a ≫ d₂)

lemma cochainKernelToCocone_naturality :
    kernel.map d₁ d₂ a b h ≫ cochainKernelToCocone d₂ =
      cochainKernelToCocone d₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d₁ d₂ a b h := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext d₂
  · rw [Category.assoc, cochainKernelToCocone_fst, kernel.lift_ι,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, ← Category.assoc,
      cochainKernelToCocone_fst]
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      cochainKernelToCocone_snd, Cochain.comp_zero,
      Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd, ← Cochain.comp_assoc_of_first_is_zero_cochain,
      cochainKernelToCocone_snd, Cochain.zero_comp]

lemma cochainKernelMap_quasiIso [Epi d₁] [Epi d₂]
    (ha : QuasiIso a) (hb : QuasiIso b) : QuasiIso (kernel.map d₁ d₂ a b h) := by
  have : QuasiIso (cochainKernelToCocone d₂) := cochainKernelToCocone_quasiIso d₂
  have : QuasiIso (kernel.map d₁ d₂ a b h ≫ cochainKernelToCocone d₂) := by
    rw [cochainKernelToCocone_naturality]
    exact quasiIso_comp _ _ (hφ := cochainKernelToCocone_quasiIso d₁)
      (hφ' := cochainMappingCoconeMap_quasiIso d₁ d₂ a b h ha hb)
  exact quasiIso_of_comp_right (kernel.map d₁ d₂ a b h) (cochainKernelToCocone d₂)

lemma moduleIsoSpan_comp {X Y Z W : ModuleCat R} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsIso g] (s : X ⟶ W) (t : Y ⟶ W) (z : Z ⟶ W)
    (hs : f ≫ z = s) (ht : g ≫ z = t) : (f ≫ inv g) ≫ t = s := by
  rw [← ht, Category.assoc, IsIso.inv_hom_id_assoc]
  exact hs

lemma moduleIsoSpan_reverse {X Y Z W : ModuleCat R} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsIso f] [IsIso g] (s : X ⟶ W) (t : Y ⟶ W)
    (h : (f ≫ inv g) ≫ t = s) : g ≫ (inv f ≫ s) = t := by
  rw [← h]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc]

end SerrePositivity.KST.LocalizingInvariants

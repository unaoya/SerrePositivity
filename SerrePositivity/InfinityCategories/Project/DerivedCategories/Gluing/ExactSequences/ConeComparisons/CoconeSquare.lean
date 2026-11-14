module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ConeSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeMap
/-! ホモトピー可換な正方形から、第三 cochain を保持する mapping cocone 写像を構成する。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable {R : Type u} [CommRing R] {P Q S T : Complex R}
  (f : P ⟶ Q) (g : S ⟶ T) (μ : P ⟶ S) (ν : Q ⟶ T)
  (h : Cochain P T (-1))
  (hh : δ (-1) 0 h + Cochain.ofHom (μ ≫ g - f ≫ ν) = 0)

def dgGluingCoconeSquarePrimitive : Cochain (mappingCocone μ) T (-1) :=
  (mappingCocone.snd μ).comp (Cochain.ofHom g) (add_zero (-1)) -
    (Cochain.ofHom (mappingCocone.fst μ)).comp h (zero_add (-1))

include hh in
lemma dgGluingCoconeSquarePrimitive_boundary :
    δ (-1) 0 (dgGluingCoconeSquarePrimitive g μ h) +
      Cochain.ofHom (mappingCocone.fst μ ≫ f ≫ ν) = 0 := by
  have hh' : δ (-1) 0 h = Cochain.ofHom (f ≫ ν - μ ≫ g) := by
    have ht := eq_neg_of_add_eq_zero_left hh
    simpa only [← Cochain.ofHom_neg, neg_sub] using ht
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_snd_boundary μ
  have hs' : δ (-1) 0 (mappingCocone.snd μ) =
      - Cochain.ofHom (mappingCocone.fst μ ≫ μ) := eq_neg_of_add_eq_zero_left hs
  simp only [dgGluingCoconeSquarePrimitive, δ_sub, δ_comp_ofHom, δ_ofHom_comp,
    hs', hh', Preadditive.neg_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_neg,
    ← Cochain.ofHom_sub, ← Cochain.ofHom_add, Preadditive.comp_sub, Category.assoc]
  abel_nf
  simp

def dgGluingCoconeSquareMap : mappingCocone μ ⟶ mappingCocone ν :=
  mappingCocone.lift ν (mappingCocone.fst μ ≫ f) (dgGluingCoconeSquarePrimitive g μ h)
    (dgGluingCoconeSquarePrimitive_boundary f g μ ν h hh)

lemma dgGluingCoconeSquareMap_fst :
    dgGluingCoconeSquareMap f g μ ν h hh ≫ mappingCocone.fst ν = mappingCocone.fst μ ≫ f :=
  mappingCocone.lift_fst _ _ _ _

lemma dgGluingCoconeSquareMap_snd :
    (Cochain.ofHom (dgGluingCoconeSquareMap f g μ ν h hh)).comp
      (mappingCocone.snd ν) (zero_add (-1)) =
      dgGluingCoconeSquarePrimitive g μ h := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, dgGluingCoconeSquareMap]
  exact mappingCocone.lift_f_snd_v ν _ _ _ p q hpq

/-- 比較ホモトピーが零なら、既存の厳密正方形の cocone 写像と一致する。 -/
lemma dgGluingCoconeSquareMap_zero (comm : μ ≫ g = f ≫ ν)
    (hh0 : δ (-1) 0 (0 : Cochain P T (-1)) +
      Cochain.ofHom (μ ≫ g - f ≫ ν) = 0) :
    dgGluingCoconeSquareMap f g μ ν 0 hh0 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap μ ν f g comm := by
  unfold dgGluingCoconeSquareMap _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap
  congr 1
  simp only [dgGluingCoconeSquarePrimitive, Cochain.comp_zero, sub_zero]

/-- 第二射影の式を全整数次数の成分で読む。 -/
lemma dgGluingCoconeSquareMap_f_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (dgGluingCoconeSquareMap f g μ ν h hh).f p ≫
        (mappingCocone.snd ν).v p q hpq =
      (mappingCocone.snd μ).v p q hpq ≫ g.f q -
        (mappingCocone.fst μ).f p ≫ h.v p q hpq := by
  have ht := Cochain.congr_v (dgGluingCoconeSquareMap_snd f g μ ν h hh) p q hpq
  simpa only [dgGluingCoconeSquarePrimitive, Cochain.sub_v,
    Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using ht

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

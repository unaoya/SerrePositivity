module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeMap
/-!
概要：二成分からの差写像の mapping cocone を、第二成分の cocone と実入力へ射影する。
方針：実 biprod.inr の正方形と、同じ cocone の二射影を使う。
規約：短完全性の証明に先立つ実短複体。使われ方：出力分解 Hom の射影準同型性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits CochainComplex HomComplex
variable {A : Type u} [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
  {K L T : CochainComplex A ℤ} (a : K ⟶ T) (b : L ⟶ T)
/-- 第二成分の cocone から、同じ二成分の差の cocone への実左射。 -/
def complexMappingCoconeBiprodInclusion :
    mappingCocone b ⟶ mappingCocone (biprod.desc a b) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap b (biprod.desc a b) biprod.inr (𝟙 T) (by simp)
/-- 同じ二成分の cocone から実第一成分への右射影。 -/
def complexMappingCoconeBiprodProjection : mappingCocone (biprod.desc a b) ⟶ K :=
  mappingCocone.fst (biprod.desc a b) ≫ biprod.fst
/-- 実左射と実右射影の合成は厳密に零。 -/
lemma complexMappingCoconeBiprodInclusion_projection :
    complexMappingCoconeBiprodInclusion a b ≫ complexMappingCoconeBiprodProjection a b = 0 := by
  rw [complexMappingCoconeBiprodProjection, ← Category.assoc,
    complexMappingCoconeBiprodInclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst,
    Category.assoc, biprod.inr_fst, comp_zero]
/-- 出力分解 Hom の射影に使う、同じ実 cocone の短複体。 -/
def complexMappingCoconeBiprodShortComplex : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (complexMappingCoconeBiprodInclusion a b)
    (complexMappingCoconeBiprodProjection a b) (complexMappingCoconeBiprodInclusion_projection a b)
/-- 実左射の次数別左逆に使う、全次数の比較 cochain。 -/
def complexMappingCoconeBiprodRetraction :
    Cochain (mappingCocone (biprod.desc a b)) (mappingCocone b) 0 :=
  mappingCocone.liftCochain b
    (Cochain.ofHom (mappingCocone.fst (biprod.desc a b) ≫ biprod.snd))
    (mappingCocone.snd (biprod.desc a b)) (by omega)
/-- 実右射影の次数別右逆に使う、同じ実第一包含 cochain。 -/
def complexMappingCoconeBiprodSection : Cochain K (mappingCocone (biprod.desc a b)) 0 :=
  (Cochain.ofHom biprod.inl).comp (mappingCocone.inl (biprod.desc a b)) (zero_add 0)
/-- 左逆候補の第一射影は、実第二成分の射影そのもの。 -/
@[reassoc] lemma complexMappingCoconeBiprodRetraction_fst (j : ℤ) :
    (complexMappingCoconeBiprodRetraction a b).v j j (add_zero j) ≫
      (mappingCocone.fst b).f j =
        (mappingCocone.fst (biprod.desc a b)).f j ≫ (biprod.snd : K ⊞ L ⟶ L).f j := by
  simpa only [complexMappingCoconeBiprodRetraction, Cochain.ofHom_v,
    HomologicalComplex.comp_f] using mappingCocone.liftCochain_v_fst_f b
      (Cochain.ofHom (mappingCocone.fst (biprod.desc a b) ≫ biprod.snd))
      (mappingCocone.snd (biprod.desc a b)) (by omega) j j (add_zero j)
/-- 左逆候補の比較 cochain は、全体の同じ実比較 cochain。 -/
@[reassoc] lemma complexMappingCoconeBiprodRetraction_snd (j : ℤ) :
    (complexMappingCoconeBiprodRetraction a b).v j j (add_zero j) ≫
      (mappingCocone.snd b).v j (j - 1) (by omega) =
        (mappingCocone.snd (biprod.desc a b)).v j (j - 1) (by omega) :=
  mappingCocone.liftCochain_v_snd_v _ _ _ _ _ _ _ _ _
/-- 右逆候補の第一射影は、実 biprod.inl。 -/
@[reassoc] lemma complexMappingCoconeBiprodSection_fst (j : ℤ) :
    (complexMappingCoconeBiprodSection a b).v j j (add_zero j) ≫
      (mappingCocone.fst (biprod.desc a b)).f j = (biprod.inl : K ⟶ K ⊞ L).f j := by
  simp only [complexMappingCoconeBiprodSection, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Category.assoc, mappingCocone.inl_v_fst_f, Category.comp_id]
/-- 右逆候補の実比較 cochain は零。 -/
@[reassoc] lemma complexMappingCoconeBiprodSection_snd (j : ℤ) :
    (complexMappingCoconeBiprodSection a b).v j j (add_zero j) ≫
      (mappingCocone.snd (biprod.desc a b)).v j (j - 1) (by omega) = 0 := by
  simp only [complexMappingCoconeBiprodSection, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Category.assoc, mappingCocone.inl_v_snd_v, comp_zero]
end SerrePositivity.InfinityCategories.Project.DerivedCategories

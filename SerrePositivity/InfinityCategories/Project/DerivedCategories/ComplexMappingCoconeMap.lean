module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeBoundary
/-!
概要：実可換正方形を、mapping cocone の実射影と比較 cochain を保つ鎖写像へ送る。
方針：同じ第二 cochain の微分式と実持ち上げを使う。
規約：射影の可換性は厳密な等式。使われ方：出力分解 Hom の短完全列の実左射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits CochainComplex HomComplex
variable {A : Type u} [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
  {K₁ L₁ K₂ L₂ : CochainComplex A ℤ} (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : d₁ ≫ b = a ≫ d₂)
include comm in
/-- 実可換正方形の同じ比較 cochain は、標的 mapping cocone への持ち上げ条件を満たす。 -/
lemma complexMappingCoconeMap_boundary :
    δ (-1) 0 ((mappingCocone.snd d₁).comp (Cochain.ofHom b) (add_zero (-1))) +
      Cochain.ofHom ((mappingCocone.fst d₁ ≫ a) ≫ d₂) = 0 := by
  rw [δ_comp_ofHom]
  have h := congrArg (fun t : Cochain (mappingCocone d₁) L₁ 0 ↦
    t.comp (Cochain.ofHom b) (zero_add 0)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_snd_boundary d₁)
  simpa only [Cochain.add_comp, Cochain.zero_comp, ← Cochain.ofHom_comp,
    Category.assoc, comm] using h
/-- 実正方形に沿う、同じ実二成分を保持する mapping cocone の鎖写像。 -/
def complexMappingCoconeMap : mappingCocone d₁ ⟶ mappingCocone d₂ :=
  mappingCocone.lift d₂ (mappingCocone.fst d₁ ≫ a)
    ((mappingCocone.snd d₁).comp (Cochain.ofHom b) (add_zero (-1)))
    (complexMappingCoconeMap_boundary d₁ d₂ a b comm)
/-- 第一射影は、元の同じ実正方形の上辺と厳密に可換。 -/
lemma complexMappingCoconeMap_fst :
    complexMappingCoconeMap d₁ d₂ a b comm ≫ mappingCocone.fst d₂ =
      mappingCocone.fst d₁ ≫ a :=
  mappingCocone.lift_fst _ _ _ _
/-- 比較 cochain も、元の同じ実正方形の下辺との合成に厳密に一致。 -/
lemma complexMappingCoconeMap_snd :
    (Cochain.ofHom (complexMappingCoconeMap d₁ d₂ a b comm)).comp
      (mappingCocone.snd d₂) (zero_add (-1)) =
        (mappingCocone.snd d₁).comp (Cochain.ofHom b) (add_zero (-1)) := by
  ext p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v _ _ _ _ p q hpq
/-- 第一射影との可換性を、同じ実次数の成分で読む。 -/
@[reassoc] lemma complexMappingCoconeMap_f_fst_f (j : ℤ) :
    (complexMappingCoconeMap d₁ d₂ a b comm).f j ≫ (mappingCocone.fst d₂).f j =
      (mappingCocone.fst d₁).f j ≫ a.f j := by
  have h := congrArg (fun f ↦ f.f j) (complexMappingCoconeMap_fst d₁ d₂ a b comm)
  simpa only [HomologicalComplex.comp_f] using h
/-- 比較 cochain との可換性を、同じ実二次数の成分で読む。 -/
@[reassoc] lemma complexMappingCoconeMap_f_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (complexMappingCoconeMap d₁ d₂ a b comm).f p ≫ (mappingCocone.snd d₂).v p q hpq =
      (mappingCocone.snd d₁).v p q hpq ≫ b.f q := by
  have h := congrArg (fun t : Cochain (mappingCocone d₁) L₂ (-1) ↦ t.v p q hpq)
    (complexMappingCoconeMap_snd d₁ d₂ a b comm)
  simpa only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using h
end SerrePositivity.InfinityCategories.Project.DerivedCategories

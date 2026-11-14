module

public import SerrePositivity.EInfinity.PowerOperation.LinearHomComplexFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# 全 Hom と同じ指定 cone の次数ごとの比較

DAG XIII Construction 2.2.6 の完全入力の模型比較に用いる補助。
Mathlib の同じ `mappingCone.liftCochain` を使って、Hom と cone の順序を比べる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex
variable (R : Type w) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C] [Linear R C]
variable (P : CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N)

/-- 同じ cone の全 cochain を二つの指定射影で分解する線形同値。 -/
def linearHomConeDegreeEquiv (n : ℤ) :
    Cochain P (mappingCone f) n ≃ₗ[R] (Cochain P M (n + 1) × Cochain P N n) where
  toFun z := (z.comp (mappingCone.fst f).1 rfl, z.comp (mappingCone.snd f) (add_zero n))
  invFun z := mappingCone.liftCochain f z.1 z.2 rfl
  left_inv z := by
    apply (mappingCone.ext_cochain_to_iff f n (n + 1) rfl).mpr
    constructor <;> simp
  right_inv z := by simp
  map_add' z z' := by simp [Cochain.add_comp]
  map_smul' a z := by simp [Cochain.smul_comp]

/-- 同じ cone の指定射影で分解したときの全 Hom 微分の公式。 -/
lemma linearHomConeDegreeEquiv_d (n : ℤ) (z : Cochain P (mappingCone f) n) :
    linearHomConeDegreeEquiv R P f (n + 1) (δ n (n + 1) z) =
      (-(δ (n + 1) (n + 1 + 1) (linearHomConeDegreeEquiv R P f n z).1),
       δ n (n + 1) (linearHomConeDegreeEquiv R P f n z).2 +
         (linearHomConeDegreeEquiv R P f n z).1.comp (Cochain.ofHom f) (add_zero (n + 1))) := by
  obtain ⟨⟨a, b⟩, hz⟩ := (linearHomConeDegreeEquiv R P f n).symm.surjective z
  change mappingCone.liftCochain f a b rfl = z at hz
  rw [← hz, mappingCone.δ_liftCochain f a b rfl (n + 1 + 1) rfl]
  simp [linearHomConeDegreeEquiv, Cochain.add_comp]

end SerrePositivity.EInfinity.PowerOperation

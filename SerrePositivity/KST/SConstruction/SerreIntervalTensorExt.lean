module
public import SerrePositivity.KST.SConstruction.SerreIntervalDegrees

/-! # 元の鎖区間の tensor 射の全生成元判定
概要：鎖区間の二つの端点と辺の全ての対で、tensor 複体からの chain map を判定する。
方針：各次数の生成元判定と tensor の線形転置を使い、零次数以外も保持する。
規約：三つの標準生成元は元の区間の元。使われ方：max connection の対角保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

/-- 元の二端点と辺の次数。番号は零端点・一端点・辺の順。 -/
def serreIntervalGeneratorDegree : Fin 3 → ℤ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨_ + 2, _⟩ => -1

variable (A : Type u) [CommRing A]

/-- 元の鎖区間の二端点と辺を、その同じ次数でまとめる。 -/
def serreIntervalGenerator : (i : Fin 3) → (serreInterval A).X (serreIntervalGeneratorDegree i)
  | ⟨0, _⟩ => (cycleFromUnit _ (serreIntervalZero A)).val
  | ⟨1, _⟩ => (cycleFromUnit _ (serreIntervalOne A)).val
  | ⟨_ + 2, _⟩ => serreIntervalEdge A

/-- 元の各次数の全生成元での一致から線形射の一致を判定する。 -/
lemma serreInterval_degree_hom_ext (n : ℤ) {V : ModuleCat.{u} A}
    {f g : (serreInterval A).X n ⟶ V}
    (h : ∀ (i : Fin 3) (hi : serreIntervalGeneratorDegree i = n),
      f (eqToHom (congrArg (fun k => (serreInterval A).X k) hi) (serreIntervalGenerator A i)) =
      g (eqToHom (congrArg (fun k => (serreInterval A).X k) hi) (serreIntervalGenerator A i))) :
    f = g := by
  by_cases h₀ : n = 0
  · subst n
    exact serreInterval_degree_zero_ext A (h 0 rfl) (h 1 rfl)
  · by_cases h₁ : n = -1
    · subst n
      exact serreInterval_degree_neg_one_ext A (h 2 rfl)
    · exact (serreInterval_isZero_X A n h₀ h₁).eq_of_src _ _

/-- 元の区間の全生成元の対で一致する tensor chain map は等しい。 -/
lemma serreIntervalTensor_hom_ext {K : Complex A}
    {f g : serreInterval A ⊗ serreInterval A ⟶ K}
    (h : ∀ (i j : Fin 3) (n : ℤ)
      (hn : serreIntervalGeneratorDegree i + serreIntervalGeneratorDegree j = n),
      f.f n (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree i) (serreIntervalGeneratorDegree j) n hn
          (serreIntervalGenerator A i ⊗ₜ[A] serreIntervalGenerator A j)) =
      g.f n (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree i) (serreIntervalGeneratorDegree j) n hn
          (serreIntervalGenerator A i ⊗ₜ[A] serreIntervalGenerator A j))) : f = g := by
  apply tensorHom_ext
  intro p q n hn
  let L := ιTensorObj (serreInterval A) (serreInterval A) p q n hn ≫ f.f n
  let R := ιTensorObj (serreInterval A) (serreInterval A) p q n hn ≫ g.f n
  apply ModuleCat.hom_ext
  change L.hom = R.hom
  apply TensorProduct.curry_injective
  have hc : (ModuleCat.ofHom (TensorProduct.curry L.hom) : (serreInterval A).X p ⟶
      ModuleCat.of A ((serreInterval A).X q →ₗ[A] K.X n)) =
      ModuleCat.ofHom (TensorProduct.curry R.hom) := by
    apply serreInterval_degree_hom_ext A p
    intro i hi
    rcases hi with rfl
    have hd : (ModuleCat.ofHom ((TensorProduct.curry L.hom) (serreIntervalGenerator A i)) :
        (serreInterval A).X q ⟶ K.X n) =
        ModuleCat.ofHom ((TensorProduct.curry R.hom) (serreIntervalGenerator A i)) := by
      apply serreInterval_degree_hom_ext A q
      intro j hj
      rcases hj with rfl
      exact h i j n hn
    exact congrArg ModuleCat.Hom.hom hd
  exact congrArg ModuleCat.Hom.hom hc

end SerrePositivity.KST.SConstruction

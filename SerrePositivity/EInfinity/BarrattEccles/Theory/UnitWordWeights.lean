module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorWordWeights
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin

/-!
# テンソル単位と入力の重み

## 概要
Berger–Moerdijk §1 の零入力を含むテンソルの比較で、単位因子の重みを零とする。

## 方針
単位基底の次数零の生成元と、左単位子の具体式を比較する。

## 規約
単位因子の重みは常に零。

## 使われ方
入力の連結と有限テンソル族の空の族の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
open scoped TensorProduct
variable {A : Type u} [CommRing A]

/-- Every vector belongs to any bound when all basis weights are zero. -/
lemma mem_basisWeightSpan_zero {V : Type u} [AddCommGroup V] [Module A V]
    {I : Type u} (b : Module.Basis I A V) (N : ℕ) (x : V) :
    x ∈ basisWeightSpan b (fun _ => 0) N := by
  rw [mem_basisWeightSpan]
  intro i hi
  exact Nat.zero_le N

/-- The unit basis in degree zero is the standard generator of the tensor unit. -/
lemma unitDegreeBasis_zero_apply (x : unitDegreeIndex.{u} 0) :
    unitDegreeBasis (A := A) 0 x =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) := by
  simp only [unitDegreeBasis]
  simp only [dite_true, id_eq, Module.Basis.map_apply]
  erw [Module.Basis.singleton_apply]
  rfl

/-- The forward left unitor removes the weight-zero unit factor. -/
lemma leftUnitor_mem_basisWeightSpan {K : Complex A} {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i)) (w : (Σ i, I i) → ℕ)
    (i : ℤ) (N : ℕ) {x : (𝟙_ (Complex A) ⊗ K).X i}
    (hx : x ∈ basisWeightSpan (tensorGradedBasis unitDegreeBasis b i)
      (tensorGradedWeight (fun _ => 0) w i) N) :
    (λ_ K).hom.f i x ∈ basisWeightSpan (b i) (fun z => w ⟨i, z⟩) N := by
  apply map_mem_basisWeightSpan (tensorGradedBasis unitDegreeBasis b i) (b i)
    (tensorGradedWeight (fun _ => 0) w i) (fun z => w ⟨i, z⟩)
    ((λ_ K).hom.f i).hom ?_ N hx
  rintro ⟨⟨⟨p, r⟩, h⟩, z, y⟩
  by_cases hp : p = 0
  · subst p
    have hr : r = i := by omega
    subst r
    rw [tensorGradedBasis_apply, unitDegreeBasis_zero_apply (A := A)]
    erw [leftUnitor_hom_generator]
    simpa only [tensorGradedWeight, zero_add] using
      basis_mem_basisWeightSpan (b i) (fun z => w ⟨i, z⟩) y
  · change (if p = 0 then ULift.{u} PUnit else PEmpty) at z
    rw [ite_eq_right hp] at z
    exact z.elim

/-- Inserting a weight-zero unit factor preserves the input bound. -/
lemma leftUnitor_inv_mem_basisWeightSpan {K : Complex A} {I : ℤ → Type u}
    (b : ∀ i, Module.Basis (I i) A (K.X i)) (w : (Σ i, I i) → ℕ)
    (i : ℤ) (N : ℕ) {x : K.X i}
    (hx : x ∈ basisWeightSpan (b i) (fun z => w ⟨i, z⟩) N) :
    (λ_ K).inv.f i x ∈ basisWeightSpan (tensorGradedBasis unitDegreeBasis b i)
      (tensorGradedWeight (fun _ => 0) w i) N := by
  apply map_mem_basisWeightSpan (b i) (tensorGradedBasis unitDegreeBasis b i)
    (fun z => w ⟨i, z⟩) (tensorGradedWeight (fun _ => 0) w i)
    ((λ_ K).inv.f i).hom ?_ N hx
  intro z
  have hz := basis_mem_basisWeightSpan (tensorGradedBasis (unitDegreeBasis (A := A)) b i)
    (tensorGradedWeight (fun _ => 0) w i)
      ⟨⟨(0, i), by omega⟩, show unitDegreeIndex 0 from ULift.up PUnit.unit, z⟩
  rw [tensorGradedBasis_apply, unitDegreeBasis_zero_apply (A := A)] at hz
  rw [complexLeftUnitor_inv_apply]
  simp only [tensorGradedWeight, zero_add] at hz ⊢
  exact hz

end SerrePositivity.EInfinity

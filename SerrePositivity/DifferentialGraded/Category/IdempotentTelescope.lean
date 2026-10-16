module
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # 可算余積による冪等射の分裂

冪等射を遷移射とする可算列のtelescopeを用いる。最初の射の左逆は
各余積成分上で有限和として明示し、一般の余極限の完全性は仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Category Limits Preadditive Pretriangulated
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (X : C) [HasCoproduct (fun _ : ℕ => X)] (p : X ⟶ X)

def idempotentTelescopeShift : (∐ fun _ : ℕ => X) ⟶ (∐ fun _ : ℕ => X) :=
  Sigma.desc (fun n => p ≫ Sigma.ι (fun _ : ℕ => X) (n + 1))

def idempotentTelescopeMap : (∐ fun _ : ℕ => X) ⟶ (∐ fun _ : ℕ => X) :=
  𝟙 _ - idempotentTelescopeShift X p

def idempotentTelescopeRetraction : (∐ fun _ : ℕ => X) ⟶ (∐ fun _ : ℕ => X) :=
  Sigma.desc (fun n =>
    -(∑ k ∈ Finset.range n, p ≫ Sigma.ι (fun _ : ℕ => X) k) +
      (𝟙 X - p) ≫ Sigma.ι (fun _ : ℕ => X) n)

lemma idempotentTelescopeMap_retraction (hp : p ≫ p = p) :
    idempotentTelescopeMap X p ≫ idempotentTelescopeRetraction X p = 𝟙 _ := by
  apply Sigma.hom_ext
  intro n
  have hpp {Z : C} (f : X ⟶ Z) : p ≫ p ≫ f = p ≫ f := by
    rw [← Category.assoc, hp]
  simp only [idempotentTelescopeMap, idempotentTelescopeShift,
    idempotentTelescopeRetraction, comp_sub, comp_id, sub_comp, Category.assoc,
    Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, comp_add, comp_neg, comp_sum,
    hpp, id_comp, Finset.sum_range_succ]
  abel

lemma idempotentTelescopeMap_mono (hp : p ≫ p = p) :
    Mono (idempotentTelescopeMap X p) := by
  constructor
  intro Z f g h
  have := congrArg (fun k => k ≫ idempotentTelescopeRetraction X p) h
  simpa only [Category.assoc, idempotentTelescopeMap_retraction X p hp, comp_id] using this

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A countable coproduct of copies of the source suffices to split an idempotent. -/
theorem idempotent_split_of_countable_coproduct (hp : p ≫ p = p) :
    ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p := by
  let d : (∐ fun _ : ℕ => X) ⟶ X := Sigma.desc (fun _ => p)
  have had : idempotentTelescopeMap X p ≫ d = 0 := by
    apply Sigma.hom_ext
    intro n
    simp only [idempotentTelescopeMap, idempotentTelescopeShift, d, comp_sub,
      sub_comp, Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, id_comp]
    rw [hp, sub_self, comp_zero]
  obtain ⟨Y, c, h, hT⟩ := distinguished_cocone_triangle (idempotentTelescopeMap X p)
  have hh := Triangle.mor₃_eq_zero_of_mono₁ _ hT
    (idempotentTelescopeMap_mono X p hp)
  have : Epi c := Triangle.epi₂ _ hT hh
  obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ _ hT d had
  change d = c ≫ r at hr
  have hac : idempotentTelescopeMap X p ≫ c = 0 :=
    comp_distTriang_mor_zero₁₂ _ hT
  have hc (n : ℕ) : Sigma.ι (fun _ : ℕ => X) n ≫ c =
      p ≫ Sigma.ι (fun _ : ℕ => X) (n + 1) ≫ c := by
    have hn := congrArg (fun k => Sigma.ι (fun _ : ℕ => X) n ≫ k) hac
    simpa only [idempotentTelescopeMap, idempotentTelescopeShift, comp_sub, comp_id,
      sub_comp, Category.assoc, Sigma.ι_comp_desc_assoc, id_comp, comp_zero, sub_eq_zero] using hn
  have hpc (n : ℕ) : p ≫ Sigma.ι (fun _ : ℕ => X) n ≫ c =
      Sigma.ι (fun _ : ℕ => X) n ≫ c := by
    calc
      _ = p ≫ p ≫ Sigma.ι (fun _ : ℕ => X) (n + 1) ≫ c := by rw [← hc n]
      _ = _ := by rw [← Category.assoc p p, hp, ← hc n]
  have hconstant (n : ℕ) : Sigma.ι (fun _ : ℕ => X) n ≫ c =
      Sigma.ι (fun _ : ℕ => X) 0 ≫ c := by
    induction n with
    | zero => rfl
    | succ n ih => rw [← hpc (n + 1), ← hc n, ih]
  refine ⟨Y, r, Sigma.ι (fun _ : ℕ => X) 0 ≫ c, ?_, ?_⟩
  · apply (cancel_epi c).1
    simp only [← Category.assoc, comp_id]
    rw [← hr]
    apply Sigma.hom_ext
    intro n
    simp only [Category.assoc, d, Sigma.ι_comp_desc_assoc]
    rw [hpc 0, hconstant n]
  · rw [Category.assoc, ← hr]
    exact Sigma.ι_comp_desc _ _

end SerrePositivity.DifferentialGraded

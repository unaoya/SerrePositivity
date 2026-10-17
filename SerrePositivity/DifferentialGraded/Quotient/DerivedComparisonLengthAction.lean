module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltrationAction

/-! # 長さ部分複体への全次数作用の制限

純粋 tensor 上の安定性と最終微分の Leibniz 則から、実際の chain map を作る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable (A : Type u) [CommRing A]

/-- 純粋 tensor 上で部分加群を保つ線形写像の制限。 -/
def tensorCodRestrict {V W T : Type u}
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup T]
    [Module A V] [Module A W] [Module A T]
    (P : Submodule A W) (Q : Submodule A T) (g : V ⊗[A] W →ₗ[A] T)
    (hg : ∀ a (b : P), g (a ⊗ₜ[A] b.val) ∈ Q) : V ⊗[A] P →ₗ[A] Q :=
  LinearMap.codRestrict Q (g.comp (TensorProduct.map LinearMap.id P.subtype)) (by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simpa using hg a b
    | add t t' ht ht' => simpa only [map_add] using Q.add_mem ht ht')

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 長さ n の部分加群へ制限した双次数の先頭作用。 -/
def lengthPrependComponent (S : Set D) (x y z : D) (n : ℕ)
    (p q r : ℤ) (hr : p + q = r) :
    (homObject A D x y).X p ⊗ (lengthComplex A D S y z n).X q ⟶
      (lengthComplex A D S x z n).X r :=
  ModuleCat.ofHom (tensorCodRestrict A (lengthSubmodule A D S y z n q)
    (lengthSubmodule A D S x z n r)
    ((ιTensorObj (homObject A D x y) (internalHom A D S y z) p q r hr ≫
      (internalPrepend A D S x y z).f r).hom)
    (fun a b => internalPrepend_mem_length A D S x y z n p q r hr a b.val b.property))

lemma lengthPrependComponent_coe (S : Set D) (x y z : D) (n : ℕ)
    (p q r : ℤ) (hr : p + q = r) (f : (homObject A D x y).X p)
    (t : (lengthComplex A D S y z n).X q) :
    (lengthPrependComponent A D S x y z n p q r hr (f ⊗ₜ[A] t)).val =
      (internalPrepend A D S x y z).f r
        (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q r hr
          (f ⊗ₜ[A] t.val)) := by
  change (internalPrepend A D S x y z).f r
    (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q r hr
      ((TensorProduct.map (LinearMap.id : (homObject A D x y).X p →ₗ[A] _)
        (lengthSubmodule A D S y z n q).subtype) (f ⊗ₜ[A] t))) = _
  rw [TensorProduct.map_tmul]
  rfl

lemma lengthPrependComponent_d (S : Set D) (x y z : D) (n : ℕ) (p q : ℤ) :
    lengthPrependComponent A D S x y z n p q (p + q) rfl ≫
        (lengthComplex A D S x z n).d (p + q) (p + q + 1) =
      ((homObject A D x y).d p (p + 1) ▷ (lengthComplex A D S y z n).X q) ≫
        lengthPrependComponent A D S x y z n (p + 1) q (p + q + 1) (by omega) +
      p.negOnePow • (((homObject A D x y).X p ◁
          (lengthComplex A D S y z n).d q (q + 1)) ≫
        lengthPrependComponent A D S x y z n p (q + 1) (p + q + 1) (by omega)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f t
  rw [lengthComplex_d, lengthComplex_d]
  apply Subtype.ext
  change (lengthDifferential A D S x z n (p + q)
      (lengthPrependComponent A D S x y z n p q (p + q) rfl (f ⊗ₜ[A] t))).val =
    (lengthPrependComponent A D S x y z n (p + 1) q (p + q + 1) (by omega)
      ((homObject A D x y).d p (p + 1) f ⊗ₜ[A] t)).val +
    p.negOnePow • (lengthPrependComponent A D S x y z n p (q + 1) (p + q + 1) (by omega)
      (f ⊗ₜ[A] lengthDifferential A D S y z n q t)).val
  simp only [lengthDifferential_coe, lengthPrependComponent_coe]
  exact internalPrepend_total_d_apply A D S x y z p q (p + q) rfl f t.val

/-- 最終微分を持つ長さ部分複体への先頭作用。 -/
def lengthPrepend (S : Set D) (x y z : D) (n : ℕ) :
    homObject A D x y ⊗ lengthComplex A D S y z n ⟶ lengthComplex A D S x z n :=
  tensorLift (lengthPrependComponent A D S x y z n)
    (lengthPrependComponent_d A D S x y z n)

@[reassoc] lemma lengthPrepend_ι (S : Set D) (x y z : D) (n : ℕ)
    (p q r : ℤ) (hr : p + q = r) :
    ιTensorObj (homObject A D x y) (lengthComplex A D S y z n) p q r hr ≫
        (lengthPrepend A D S x y z n).f r =
      lengthPrependComponent A D S x y z n p q r hr :=
  ι_tensorLift _ _ p q r hr

/-- 長さ部分複体の包含は、最終微分についての先頭作用と可換。 -/
@[reassoc] lemma lengthPrepend_inclusion (S : Set D) (x y z : D) (n : ℕ) :
    lengthPrepend A D S x y z n ≫ lengthInclusion A D S x z n =
      (homObject A D x y ◁ lengthInclusion A D S y z n) ≫ quotientPrepend A D S x y z := by
  apply tensorHom_ext
  intro p q r hr
  rw [HomologicalComplex.comp_f, ← Category.assoc, lengthPrepend_ι,
    HomologicalComplex.comp_f, ← Category.assoc, ι_whiskerLeft, Category.assoc,
    quotientPrepend_ι]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f t
  change (lengthPrependComponent A D S x y z n p q r hr (f ⊗ₜ[A] t)).val = _
  rw [lengthPrependComponent_coe]
  rfl

/-- 長さの上限を増やす包含は、制限した全次数作用と可換。 -/
lemma lengthPrepend_map (S : Set D) (x y z : D) {m n : ℕ} (hmn : m ≤ n) :
    lengthPrepend A D S x y z m ≫ lengthMap A D S x z hmn =
      (homObject A D x y ◁ lengthMap A D S y z hmn) ≫ lengthPrepend A D S x y z n := by
  apply (cancel_mono (lengthInclusion A D S x z n)).mp
  rw [Category.assoc, lengthMap_inclusion, lengthPrepend_inclusion, Category.assoc,
    lengthPrepend_inclusion, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    lengthMap_inclusion]

end SerrePositivity.DifferentialGraded.DGQuotient

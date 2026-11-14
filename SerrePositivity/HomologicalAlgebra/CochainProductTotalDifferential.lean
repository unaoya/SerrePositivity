module
public import SerrePositivity.HomologicalAlgebra.CochainProductTotalComponents
public import SerrePositivity.HomologicalAlgebra.ProductTotalZeroRow

/-!
概要：非負横次数の積全複体の微分を元の二重複体の成分で計算する。
方針：整数添字の積全微分を展開し、零延長同型を縦横の微分に通す。
規約：内部次数に有界性を課さず、横次数 n+1 の二項を指定する。
使われ方：HA 1.2.4、G10 の Hom 比較の微分との可換性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SerrePositivity.DifferentialGraded
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra.CochainProductTotal
variable {A : Type u} [CommRing A] (K : CochainComplex (Complex A) ℕ)

/-- 零延長同型は隣接する横微分を保つ。 -/
theorem rowIso_d (n : ℕ) :
    (K.extend ComplexShape.embeddingUpNat).d (n : ℤ) (n+1 : ℕ) ≫
      (rowIso K (n+1)).hom = (rowIso K n).hom ≫ K.d n (n+1) := by
  erw [K.extend_d_eq ComplexShape.embeddingUpNat (i := n) (j := n+1) rfl rfl]
  simp [rowIso]

/-- 正の横次数への全微分は、横微分と符号付き縦微分の和。 -/
theorem component_d_succ (n : ℕ) (q : ℤ) :
    ((cochainProductTotalizationFunctor (ModuleCat.{u} A)).obj K).d q (q+1) ≫
        componentπ K (n+1) (q+1) =
      componentπ K n q ≫ (K.d n (n+1)).f (q-n) ≫
        eqToHom (by congr 1; push_cast; omega) +
      ((n+1 : ℕ) : ℤ).negOnePow •
        (componentπ K (n+1) q ≫ (K.X (n+1)).d (q-(n+1 : ℕ)) (q+1-(n+1 : ℕ))) := by
  dsimp +instances only [cochainProductTotalizationFunctor, Functor.comp_obj,
    ComplexShape.Embedding.extendFunctor]
  have he : q+1-((n+1 : ℕ) : ℤ) = q-n := by push_cast; omega
  change ((ProductTotal.functor (ModuleCat.{u} A)).obj
    (K.extend ComplexShape.embeddingUpNat)).d q (q+1) ≫
      (ProductTotal.π (K.extend ComplexShape.embeddingUpNat) (n+1) (q+1-(n+1 : ℕ))
        (q+1) (by omega) ≫ (rowIso K (n+1)).hom.f _) =
    (ProductTotal.π (K.extend ComplexShape.embeddingUpNat) n (q-n) q (by omega) ≫
      (rowIso K n).hom.f _) ≫ (K.d n (n+1)).f _ ≫ _ +
    ((n+1 : ℕ) : ℤ).negOnePow •
      ((ProductTotal.π (K.extend ComplexShape.embeddingUpNat) (n+1) (q-(n+1 : ℕ)) q
        (by omega) ≫ (rowIso K (n+1)).hom.f _) ≫ (K.X (n+1)).d _ _)
  rw [← Category.assoc, ProductTotal.d_π]
  rw [Preadditive.add_comp, Linear.units_smul_comp]
  congr 1
  · have hh (a b : ℤ) (ha : a = n) (hb : b = q-n) :
        ProductTotal.π (K.extend ComplexShape.embeddingUpNat) a b q (by omega) ≫
          ((K.extend ComplexShape.embeddingUpNat).d a (n+1 : ℕ)).f b ≫
          (rowIso K (n+1)).hom.f b =
        (ProductTotal.π (K.extend ComplexShape.embeddingUpNat) n (q-n) q (by omega) ≫
          (rowIso K n).hom.f (q-n)) ≫ (K.d n (n+1)).f (q-n) ≫
          eqToHom (by rw [hb]) := by
      subst a; subst b
      rw [← HomologicalComplex.comp_f, rowIso_d, HomologicalComplex.comp_f]
      simp only [eqToHom_refl, Category.comp_id, Category.assoc]
    convert hh ((n : ℤ)+1-1) (q+1-(n+1 : ℕ)) (by omega) (by omega) using 1
    simp only [Int.natCast_add, Int.natCast_one, Category.assoc]
  · have hv (b : ℤ) (hb : b = q-(n+1 : ℕ)) :
        ProductTotal.π (K.extend ComplexShape.embeddingUpNat) (n+1 : ℕ) b q (by omega) ≫
          ((K.extend ComplexShape.embeddingUpNat).X (n+1 : ℕ)).d b (q+1-(n+1 : ℕ)) ≫
          (rowIso K (n+1)).hom.f (q+1-(n+1 : ℕ)) =
        (ProductTotal.π (K.extend ComplexShape.embeddingUpNat) (n+1 : ℕ)
          (q-(n+1 : ℕ)) q (by omega) ≫ (rowIso K (n+1)).hom.f _) ≫
          (K.X (n+1)).d _ _ := by
      subst b
      rw [← (rowIso K (n+1)).hom.comm, Category.assoc]
    convert congrArg (fun f => ((n+1 : ℕ) : ℤ).negOnePow • f)
      (hv (q+1-(n+1 : ℕ)-1) (by omega)) using 1 <;>
      simp only [Int.natCast_add, Int.natCast_one, Category.assoc]

/-- 横次数零では全微分は縦微分だけになる。 -/
theorem component_d_zero (q : ℤ) :
    ((cochainProductTotalizationFunctor (ModuleCat.{u} A)).obj K).d q (q+1) ≫
        componentπ K 0 (q+1) =
      componentπ K 0 q ≫ (K.X 0).d (q-0) (q+1-0) := by
  have hd : (K.extend ComplexShape.embeddingUpNat).d (-1) 0 = 0 :=
    (negativeRow_isZero K (-1) (by omega)).eq_of_src _ _
  have hz (b c : ℤ) (hb : b=q) (hc : c=q+1) :
      ((ProductTotal.functor (ModuleCat.{u} A)).obj
        (K.extend ComplexShape.embeddingUpNat)).d q (q+1) ≫
        ProductTotal.π (K.extend ComplexShape.embeddingUpNat) 0 c (q+1) (by omega) ≫
        (rowIso K 0).hom.f c =
      ProductTotal.π (K.extend ComplexShape.embeddingUpNat) 0 b q (by omega) ≫
        (rowIso K 0).hom.f b ≫ (K.X 0).d b c := by
    cases hb; cases hc
    rw [← Category.assoc, ProductTotal.zeroRow_d _ hd, Category.assoc]
    erw [← (rowIso K 0).hom.comm]
  dsimp +instances only [cochainProductTotalizationFunctor, Functor.comp_obj,
    ComplexShape.Embedding.extendFunctor]
  simpa only [componentπ, Int.natCast_zero, Category.assoc] using
    hz (q-0) (q+1-0) (by omega) (by omega)

end SerrePositivity.HomologicalAlgebra.CochainProductTotal

module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalComponents

/-!
概要：積 Tot の指定 Hom 成分の両変数自然性。
方針：元の componentπ で成分を評価し、その自然性と合成の結合則を使う。
規約：試験対象の射は反変、余単体図式の射は共変。いずれも同じ積射影を保つ。
使われ方：HA 1.2.4、G10 の全関手比較と指定錐の族。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 全次数を固定して評価した Hom 成分は元の積射影との合成。 -/
theorem homTotalComponent_v (P : Complex A) (X : CosimplicialObject (Complex A))
    (p : ℤ) (n : ℕ) (z : Homogeneous P ((productTotalFunctor A).obj X) p) (i : ℤ) :
    (homTotalComponent P X p n z).v i (i + p - n) (by omega) =
      z.v i (i + p) rfl ≫ componentπ X n (i + p) := rfl

/-- 入力図式の射による後合成と、指定 Hom 成分は可換。 -/
theorem homTotalComponent_postcompose (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) (p : ℤ) (n : ℕ)
    (z : Homogeneous P ((productTotalFunctor A).obj X) p) :
    homTotalComponent P Y p n (z.comp (Cochain.ofHom ((productTotalFunctor A).map f))
      (add_zero p)) =
    (homTotalComponent P X p n z).comp (Cochain.ofHom (f.app ⦋n⦌)) (add_zero _) := by
  apply Cochain.ext
  intro i j hij
  have hj : j = i + p - n := by omega
  cases hj
  rw [homTotalComponent_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, homTotalComponent_v]
  simp only [Category.assoc, componentπ_naturality]

/-- 試験対象の射による前合成と、指定 Hom 成分は可換。 -/
theorem homTotalComponent_precompose {P Q : Complex A} (g : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) (p : ℤ) (n : ℕ)
    (z : Homogeneous Q ((productTotalFunctor A).obj X) p) :
    homTotalComponent P X p n ((Cochain.ofHom g).comp z (zero_add p)) =
      (Cochain.ofHom g).comp (homTotalComponent Q X p n z) (zero_add _) := by
  apply Cochain.ext
  intro i j hij
  have hj : j = i + p - n := by omega
  cases hj
  rw [homTotalComponent_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v, homTotalComponent_v]
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

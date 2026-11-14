module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductComponents

/-!
概要：積全複体の全次数 q の対象を、元の余単体次数 n≥0 の成分の積として提示する。
方針：二重複体の対角線の積へ射を作り、負の行を零として取り除く。
規約：積の完全性も有界性も使わず、同じ指定射影の普遍性を証明する。
使われ方：HA 1.2.4、G10 の Hom と積 total の交換、離散加群への制限。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicTopology SerrePositivity.DifferentialGraded
open scoped Simplicial SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 元の非負余単体成分の族から、同じ積全複体の全次数 q への射を作る。 -/
def componentLift (X : CosimplicialObject (Complex A)) {M : ModuleCat.{u} A} (q : ℤ)
    (f : ∀ n : ℕ, M ⟶ (X.obj ⦋n⦌).X (q-n)) :
    M ⟶ ((productTotalFunctor A).obj X).X q :=
  SerrePositivity.HomologicalAlgebra.ProductTotal.lift
    ((doubleComplexFunctor A).obj X) q (fun a b hab =>
      if ha : 0 ≤ a then
        f a.toNat ≫ (rowIso X a.toNat).inv.f (q-a.toNat) ≫
          eqToHom (by rw [Int.toNat_of_nonneg ha]; congr 1; omega)
      else 0)

@[reassoc (attr := simp)]
theorem componentLift_π (X : CosimplicialObject (Complex A)) {M : ModuleCat.{u} A} (q : ℤ)
    (f : ∀ n : ℕ, M ⟶ (X.obj ⦋n⦌).X (q-n)) (n : ℕ) :
    componentLift X q f ≫ componentπ X n q = f n := by
  dsimp only [componentLift, componentπ]
  rw [← Category.assoc, SerrePositivity.HomologicalAlgebra.ProductTotal.lift_π]
  simp only [Int.natCast_nonneg, dite_true, Int.toNat_natCast]
  simp

/-- 頂点を変えず、元の余単体成分への指定射影を持つ積錐。 -/
def componentFan (X : CosimplicialObject (Complex A)) (q : ℤ) :
    Fan (fun n : ℕ => (X.obj ⦋n⦌).X (q-n)) :=
  Fan.mk (((productTotalFunctor A).obj X).X q) (componentπ X · q)

/-- 積全複体の次数 q は、指定射影に関して ∏ n≥0, Xⁿ[q−n] そのもの。 -/
def componentFanIsLimit (X : CosimplicialObject (Complex A)) (q : ℤ) :
    IsLimit (componentFan X q) :=
  Fan.IsLimit.mk _
    (fun s => componentLift X q (fun n => s.π.app ⟨n⟩))
    (by intro s n; exact componentLift_π X q _ n)
    (by intro s m hm; apply component_hom_ext X q; intro n; rw [componentLift_π]; exact hm n)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

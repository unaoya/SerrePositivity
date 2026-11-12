module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductCone
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-!
概要：積 Tot への次数付き Hom を、元の余単体次数ごとの Hom の積として表す。
方針：同じ積射影で前向きの写像を作り、componentLift を逆写像に使う。
規約：試験対象も入力も非有界。ここでは次数付き線形同値を示し、Hom 微分との比較は後続に分ける。
使われ方：HA 1.2.4、G10 の Hom と積全複体の交換。
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

/-- 同じ積射影による、次数 p の Hom の余単体次数 n 成分。 -/
def homTotalComponent (P : Complex A) (X : CosimplicialObject (Complex A)) (p : ℤ) (n : ℕ) :
    Homogeneous P ((productTotalFunctor A).obj X) p →ₗ[A] Homogeneous P (X.obj ⦋n⦌) (p - n) where
  toFun f := Cochain.mk (fun i j hij => f.v i (i + p) rfl ≫
    SerrePositivity.HomologicalAlgebra.ProductTotal.π
      ((doubleComplexFunctor A).obj X) n j (i + p) (by omega) ≫ (rowIso X n).hom.f j)
  map_add' f g := by
    apply Cochain.ext
    intro i j hij
    simp [Cochain.mk_v, add_comp]
  map_smul' a f := by
    apply Cochain.ext
    intro i j hij
    simp [Cochain.mk_v, Linear.smul_comp]

/-- Hom の成分の族から、同じ積 Tot への次数付き射を作る。 -/
def homTotalLift (P : Complex A) (X : CosimplicialObject (Complex A)) (p : ℤ)
    (g : ∀ n : ℕ, Homogeneous P (X.obj ⦋n⦌) (p - n)) :
    Homogeneous P ((productTotalFunctor A).obj X) p :=
  Cochain.mk (fun i j hij => componentLift X j (fun n => (g n).v i (j - n) (by omega)))

/-- 成分の族を積へ戻してから同じ射影を取ると、元の成分になる。 -/
theorem homTotalComponent_lift (P : Complex A) (X : CosimplicialObject (Complex A)) (p : ℤ)
    (g : ∀ n : ℕ, Homogeneous P (X.obj ⦋n⦌) (p - n)) (n : ℕ) :
    homTotalComponent P X p n (homTotalLift P X p g) = g n := by
  apply Cochain.ext
  intro i j hij
  have hj : j = (i + p) - n := by omega
  cases hj
  change componentLift X (i + p) (fun m => (g m).v i ((i + p) - m) (by omega)) ≫
    componentπ X n (i + p) = (g n).v i ((i + p) - n) (by omega)
  exact componentLift_π X (i + p) (fun m => (g m).v i ((i + p) - m) (by omega)) n

/-- 同じ積射影による Hom 成分は、元の次数付き射を判定する。 -/
theorem homTotalComponent_injective (P : Complex A) (X : CosimplicialObject (Complex A)) (p : ℤ)
    {f g : Homogeneous P ((productTotalFunctor A).obj X) p}
    (h : ∀ n, homTotalComponent P X p n f = homTotalComponent P X p n g) : f = g := by
  apply Cochain.ext
  intro i j hij
  subst j
  apply component_hom_ext X (i + p)
  intro n
  exact Cochain.congr_v (h n) i ((i + p) - n) (by omega)

/-- 積へ移した成分を戻す操作は元の次数付き射を保持する。 -/
theorem homTotalLift_component (P : Complex A) (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) :
    homTotalLift P X p (fun n => homTotalComponent P X p n f) = f := by
  apply homTotalComponent_injective P X p
  intro n
  exact homTotalComponent_lift P X p _ n

/-- 元の積射影を保つ、全 Hom 次数の線形同値。 -/
def homTotalComponentsEquiv (P : Complex A) (X : CosimplicialObject (Complex A)) (p : ℤ) :
    Homogeneous P ((productTotalFunctor A).obj X) p ≃ₗ[A]
      (∀ n : ℕ, Homogeneous P (X.obj ⦋n⦌) (p - n)) where
  toFun f n := homTotalComponent P X p n f
  invFun := homTotalLift P X p
  left_inv := homTotalLift_component P X p
  right_inv g := funext (homTotalComponent_lift P X p g)
  map_add' f g := by funext n; exact (homTotalComponent P X p n).map_add f g
  map_smul' a f := by funext n; exact (homTotalComponent P X p n).map_smul a f

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization

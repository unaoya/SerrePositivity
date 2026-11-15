module
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
概要：閉零次射のcochain成分を同じ図式の各点で次数等式を保って評価する。
方針：指定された終次数の等式を消去し、元のofHom成分則を使う。
規約：異種等号で型の移送を明記する既存構成の評価則。
使われ方：HA 1.2.4、IS-W2 B02の実錐代表とAW各切断の次数照合。
-/
@[expose] public noncomputable section
namespace SerrePositivity.HomologicalAlgebra
open CategoryTheory CochainComplex HomComplex
variable {A : Type*} [Ring A] {J : Type*} [Category* J]

/-- 閉零次射の任意の同じ次数成分の各点での値は、元の複体射の値。 -/
theorem cochainOfHom_v_app_heq {F G : CochainComplex (J ⥤ ModuleCat A) ℤ}
    (a : F ⟶ G) (i j : ℤ) (h : i + 0 = j) (k : J) (x : (F.X i).obj k) :
    HEq (((Cochain.ofHom a).v i j h).app k x) ((a.f i).app k x) := by
  have hji : j = i := by omega
  cases hji
  rw [Cochain.ofHom_v]

/-- 二つの閉零次射のcochain合成の成分も、元の合成複体射の各点の値。 -/
theorem cochainOfHom_comp_v_app_heq {F G H : CochainComplex (J ⥤ ModuleCat A) ℤ}
    (a : F ⟶ G) (b : G ⟶ H) (i j : ℤ) (h : i + 0 = j) (k : J)
    (x : (F.X i).obj k) :
    HEq ((((Cochain.ofHom a).comp (Cochain.ofHom b) (zero_add 0)).v i j h).app k x)
      (((a ≫ b).f i).app k x) := by
  rw [← Cochain.ofHom_comp]
  exact cochainOfHom_v_app_heq (a ≫ b) i j h k x

end SerrePositivity.HomologicalAlgebra

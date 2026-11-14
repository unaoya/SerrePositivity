module
public import SerrePositivity.HomologicalAlgebra.ProductTotal
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
概要：非有界積全複体への次数付き Hom の行成分と、その Hom 微分の公式。
方針：元の積射影に全微分の二項公式を適用し、Hom 微分の符号を合わせる。
規約：内部次数と試験複体に有界性を課さない。積の完全性を仮定しない。
使われ方：HA 1.2.4、G10 の Hom と積 Tot の複体比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits Preadditive CochainComplex HomComplex
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra.ProductTotal
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [∀ K : HomologicalComplex₂ Cᵒᵖ (.down ℤ) (.down ℤ), K.HasTotal (.down ℤ)]
variable (P : CochainComplex C ℤ) (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ))

/-- 同じ積射影による、Tot への Hom の横次数 a 成分。 -/
def homRowComponent (p a : ℤ) (f : Cochain P ((functor C).obj K) p) :
    Cochain P (K.X a) (p - a) :=
  Cochain.mk (fun i j hij => f.v i (i + p) rfl ≫ π K a j (i + p) (by omega))

/-- 中間の全次数を指定した、同じ行成分の公式。 -/
theorem homRowComponent_v (p a : ℤ) (f : Cochain P ((functor C).obj K) p)
    (i j : ℤ) (hij : i + (p - a) = j) (t : ℤ) (ht : i + p = t) :
    (homRowComponent P K p a f).v i j hij = f.v i t ht ≫ π K a j t (by omega) := by
  subst t
  rfl

/-- Hom 微分の行成分は、横微分と符号付き行内 Hom 微分の和。 -/
theorem homRowComponent_differential_v (p a : ℤ)
    (f : Cochain P ((functor C).obj K) p) (i j : ℤ) (hij : i + (p + 1 - a) = j) :
    (homRowComponent P K (p + 1) a (δ p (p + 1) f)).v i j hij =
      (homRowComponent P K p (a - 1) f).v i j (by omega) ≫ (K.d (a - 1) a).f j +
      a.negOnePow • (δ (p - a) (p + 1 - a) (homRowComponent P K p a f)).v i j hij := by
  rw [homRowComponent_v P K (p + 1) a _ i j hij (i + p + 1) (by omega),
    δ_v p (p + 1) rfl f i (i + p + 1) (by omega) (i + p) (i + 1) (by omega) rfl,
    homRowComponent_v P K p (a - 1) f i j (by omega) (i + p) rfl,
    δ_v (p - a) (p + 1 - a) (by omega) _ i j hij (j - 1) (i + 1) rfl rfl,
    homRowComponent_v P K p a f i (j - 1) (by omega) (i + p) rfl,
    homRowComponent_v P K p a f (i + 1) j (by omega) (i + p + 1) (by omega)]
  rw [add_comp, Linear.units_smul_comp, Category.assoc,
    d_π K a j (i + p) (by omega), comp_add]
  simp only [Category.assoc, Linear.comp_units_smul, smul_add, smul_smul]
  rw [← Int.negOnePow_add]
  have hsign : a + (p + 1 - a) = p + 1 := by omega
  rw [hsign]
  abel

end SerrePositivity.HomologicalAlgebra.ProductTotal

module
public import SerrePositivity.HomologicalAlgebra.FunctorComplexExchangeEquivalence
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
概要：図式 Hom の斉次成分を各点で評価し、自然性つきの族から組み立てる。
方針：既存の加法関手による cochain の像を評価関手に適用する。
規約：全整数次数と微分を保ち、添字の自然性を明記する。
使われ方：HA 1.2.4、G10 の図式テンソル–Hom 同定。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type (max u v)} [CommRing A] {J : Type v} [SmallCategory J]
variable (P Q : J ⥤ Complex A)
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)

/-- 図式の cochain の同じ点での評価。 -/
def diagramCochainAt {n : ℤ} (z : Cochain ((E).obj P) ((E).obj Q) n) (j : J) :
    Cochain (P.obj j) (Q.obj j) n := z.map ((evaluation J (ModuleCat A)).obj j)

/-- 自然性を持つ各点の cochain を、図式の cochain に組み立てる。 -/
def diagramCochainAssemble {n : ℤ} (g : ∀ j, Cochain (P.obj j) (Q.obj j) n)
    (h : ∀ ⦃i j⦄ (f : i ⟶ j) p q (hpq : p + n = q),
      (P.map f).f p ≫ (g j).v p q hpq = (g i).v p q hpq ≫ (Q.map f).f q) :
    Cochain ((E).obj P) ((E).obj Q) n :=
  Cochain.mk (fun p q hpq =>
    { app := fun j => (g j).v p q hpq
      naturality := fun _ _ f => h f p q hpq })

/-- 評価は元の Hom 微分と可換。 -/
theorem diagramCochainAt_delta {n m : ℤ} (z : Cochain ((E).obj P) ((E).obj Q) n) (j : J) :
    diagramCochainAt P Q (δ n m z) j = δ n m (diagramCochainAt P Q z j) :=
  (δ_map n m z ((evaluation J (ModuleCat A)).obj j)).symm

/-- 各点で一致する図式 cochain は一致する。 -/
theorem diagramCochain_ext {n : ℤ} {z z' : Cochain ((E).obj P) ((E).obj Q) n}
    (h : ∀ j, diagramCochainAt P Q z j = diagramCochainAt P Q z' j) : z = z' := by
  apply Cochain.ext
  intro p q hpq
  apply NatTrans.ext
  funext j
  exact congrArg (fun g => g.v p q hpq) (h j)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

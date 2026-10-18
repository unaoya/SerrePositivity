module

public import SerrePositivity.KST.DerivedGeometry.SectionLocalizationComparison
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
概要：基本開との交叉は非空な族の開集合の積と可換。
方針：各射影から二つの交叉条件への包含を構成する。
規約：空積の保存は主張しない。
使われ方：TT §3、Toën §3.2 の制限後の Čech 各次数の交叉比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits AlgebraicGeometry PrimeSpectrum
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (a : R)

/--
概要：D(a) との交叉の関手は非空な族の積を保つ。
方針：積比較の逆包含を、全成分への射影と一つの成分の D(a) への包含から作る。
規約：非空性を D(a) への包含の構成に使う。
使われ方：TT §3、Toën §3.2 の Čech の非空な有限交叉。
-/
instance basicOpenIntersection_preservesProduct {J : Type v} [Nonempty J]
    (U : J → (Spec R).Opens) :
    PreservesLimit (Discrete.functor U) (basicOpenIntersectionFunctor a) := by
  let F := basicOpenIntersectionFunctor a
  let P := ∏ᶜ (fun j => U j ⊓ basicOpen a)
  have h₁ : P ≤ ∏ᶜ U := leOfHom (Pi.lift
    (fun j => Pi.π (fun j => U j ⊓ basicOpen a) j ≫ homOfLE inf_le_left))
  have h₂ : P ≤ basicOpen a :=
    (leOfHom (Pi.π (fun j => U j ⊓ basicOpen a) (Classical.choice inferInstance))).trans
      inf_le_right
  let g : (∏ᶜ (fun j => F.obj (U j))) ⟶ F.obj (∏ᶜ U) := homOfLE (le_inf h₁ h₂)
  have : IsIso (piComparison F U) :=
    ⟨⟨g, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  exact PreservesProduct.of_iso_comparison F U

end SerrePositivity.KST.DerivedGeometry

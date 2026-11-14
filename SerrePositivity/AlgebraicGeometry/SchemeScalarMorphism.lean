module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
概要：大域スカラーを構造射へ移し、実際の Cartesian square の係数の整合性を得る。
方針：Γ–Spec 随伴の三角恒等式と自然性を使う。
規約：基底環の像を Γ(Spec R) と黙って同一視しない。
使われ方：射影の標準開の計算と、実際の底変換の切断の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] (X : Scheme.{u})

/-- 大域スカラーが定める、Spec R への構造射。 -/
def schemeScalarMorphism (φ : R →+* Γ(X, ⊤)) : X ⟶ Spec (CommRingCat.of R) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)

/-- Spec R への構造射から得られる、大域スカラー。 -/
def schemeScalarHom (i : X ⟶ Spec (CommRingCat.of R)) : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ i.appTop).hom

/-- 構造射に移した大域スカラーを、Γ–Spec の三角恒等式で回収する。 -/
theorem schemeScalarMorphism_appTop (φ : R →+* Γ(X, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (schemeScalarMorphism X φ).appTop =
      CommRingCat.ofHom φ := by
  rw [schemeScalarMorphism, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- 構造射を経由しても、大域スカラーの環準同型は変わらない。 -/
theorem schemeScalarHom_scalarMorphism (φ : R →+* Γ(X, ⊤)) :
    schemeScalarHom X (schemeScalarMorphism X φ) = φ :=
  congrArg (fun f : CommRingCat.of R ⟶ Γ(X, ⊤) ↦ f.hom) (schemeScalarMorphism_appTop X φ)

variable {Y : Scheme.{u}} {A : Type u} [CommRing A]
variable (f : Y ⟶ X) (iX : X ⟶ Spec (CommRingCat.of R))
variable (iY : Y ⟶ Spec (CommRingCat.of A)) (α : R →+* A)
variable (h : f ≫ iX = iY ≫ Spec.map (CommRingCat.ofHom α))

include h in
/-- 実際の構造射の可換な正方形から、切断の引き戻しの scalar の整合性を得る。 -/
theorem schemeScalarHom_naturality :
    (schemeScalarHom Y iY).comp α = f.appTop.hom.comp (schemeScalarHom X iX) := by
  have hc := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop] at hc
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom α)
  have he : CommRingCat.ofHom α ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ iY.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ iX.appTop ≫ f.appTop := by
    rw [← Category.assoc, hn, Category.assoc, ← hc]
  exact congrArg (fun k : CommRingCat.of R ⟶ Γ(Y, ⊤) ↦ k.hom) he

end SerrePositivity.AlgebraicGeometry

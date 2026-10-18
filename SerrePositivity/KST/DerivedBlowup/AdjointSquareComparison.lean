module

public import SerrePositivity.KST.DerivedBlowup.AdjointComparisonCoherence
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
概要：KST §3.1 の局所表示変更に沿う随伴比較の計算。
方針：右随伴の可換四角形を左随伴一意性に移し、比較射を余単位で照合する。
規約：右側の指定自然同型に対応する左側の指定同型を使う。
使われ方：canonical な cartesian 条件の局所 dg 表示不変性。
-/

@[expose] public noncomputable section

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {N : Type u₃} [Category.{v₃} N] {P : Type u₄} [Category.{v₄} P]

/-- 概要：右随伴の指定同型に沿って同じ随伴像を持つ射を比較する。
方針：移した随伴の Hom 同値の単射性と左随伴一意性を使う。
規約：KST §3.1。使われ方：表示比較の合成随伴の射の一致。 -/
theorem adjointComparison_of_rightIso {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (A : L₁ ⊣ R₁) (B : L₂ ⊣ R₂) (e : R₁ ≅ R₂)
    {X : C} {Y : D} (f : L₁.obj X ⟶ Y) (g : L₂.obj X ⟶ Y)
    (h : A.homEquiv X Y f ≫ e.hom.app Y = B.homEquiv X Y g) :
    f = (Adjunction.leftAdjointUniq (A.ofNatIsoRight e) B).hom.app X ≫ g := by
  let A' := A.ofNatIsoRight e
  apply (A'.homEquiv X Y).injective
  rw [A'.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← B.homEquiv_unit]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  exact h

variable {L : C ⥤ D} {R : D ⥤ C} {L' : N ⥤ P} {R' : P ⥤ N}
  {Lᵢ : N ⥤ C} {Rᵢ : C ⥤ N} {Lⱼ : P ⥤ D} {Rⱼ : D ⥤ P}

/-- 概要：右随伴の四角形に対応する左随伴の標準比較同型。
方針：二つの辺の合成随伴を指定右同型に沿って比較する。
規約：KST §3.1。使われ方：導来係数拡大の表示変更。 -/
def adjointSquareIso (Aᵢ : Lᵢ ⊣ Rᵢ) (Aⱼ : Lⱼ ⊣ Rⱼ) (A : L ⊣ R) (B : L' ⊣ R')
    (e : R ⋙ Rᵢ ≅ Rⱼ ⋙ R') : Lᵢ ⋙ L ≅ L' ⋙ Lⱼ :=
  Adjunction.leftAdjointUniq ((Aᵢ.comp A).ofNatIsoRight e) (B.comp Aⱼ)

/-- 概要：右随伴の四角形と整合する比較射は左側でも余単位を介して整合する。
方針：合成随伴の Hom 同値を展開し、三角恒等式で余単位を消去する。
規約：KST §3.1。使われ方：二つの cartesian 比較の可逆性の比較。 -/
theorem adjointSquare_comparison (Aᵢ : Lᵢ ⊣ Rᵢ) (Aⱼ : Lⱼ ⊣ Rⱼ)
    (A : L ⊣ R) (B : L' ⊣ R') (e : R ⋙ Rᵢ ≅ Rⱼ ⋙ R')
    {X : C} {Y : D} (f : L.obj X ⟶ Y) (g : L'.obj (Rᵢ.obj X) ⟶ Rⱼ.obj Y)
    (h : Rᵢ.map (A.homEquiv X Y f) ≫ e.hom.app Y = B.homEquiv _ _ g) :
    L.map (Aᵢ.counit.app X) ≫ f =
      (adjointSquareIso Aᵢ Aⱼ A B e).hom.app (Rᵢ.obj X) ≫
        Lⱼ.map g ≫ Aⱼ.counit.app Y := by
  apply adjointComparison_of_rightIso (Aᵢ.comp A) (B.comp Aⱼ) e
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change Aᵢ.homEquiv _ _ (A.homEquiv _ _ (L.map (Aᵢ.counit.app X) ≫ f)) ≫
      e.hom.app Y = B.homEquiv _ _ (Aⱼ.homEquiv _ _ (Lⱼ.map g ≫ Aⱼ.counit.app Y))
  rw [A.homEquiv_naturality_left]
  dsimp only [Functor.id_obj]
  rw [show Aᵢ.homEquiv (Rᵢ.obj X) (R.obj Y) (Aᵢ.counit.app X ≫ A.homEquiv X Y f) =
      Rᵢ.map (A.homEquiv X Y f) by
    rw [Aᵢ.homEquiv_naturality_right]
    dsimp only [Functor.id_obj]
    have hc : Aᵢ.homEquiv (Rᵢ.obj X) X (Aᵢ.counit.app X) = 𝟙 _ := by
      rw [← Aᵢ.homEquiv_symm_id]
      exact Equiv.apply_symm_apply _ _
    rw [hc, Category.id_comp]]
  rw [show Aⱼ.homEquiv (L'.obj (Rᵢ.obj X)) Y (Lⱼ.map g ≫ Aⱼ.counit.app Y) = g by
    rw [Aⱼ.homEquiv_naturality_left]
    have hc : Aⱼ.homEquiv (Rⱼ.obj Y) Y (Aⱼ.counit.app Y) = 𝟙 _ := by
      rw [← Aⱼ.homEquiv_symm_id]
      exact Equiv.apply_symm_apply _ _
    rw [hc, Category.comp_id]]
  exact h

/-- 概要：局所表示の随伴が同値を与える場合、対応する比較射の可逆性は一致する。
方針：左側の可換式から可逆な標準同型と余単位を消去し、表示関手で可逆性を反映する。
規約：KST §3.1。使われ方：二つの cartesian 条件の iff。 -/
theorem adjointSquare_comparison_isIso_iff (Aᵢ : Lᵢ ⊣ Rᵢ) (Aⱼ : Lⱼ ⊣ Rⱼ)
    (A : L ⊣ R) (B : L' ⊣ R') (e : R ⋙ Rᵢ ≅ Rⱼ ⋙ R')
    {X : C} {Y : D} (f : L.obj X ⟶ Y) (g : L'.obj (Rᵢ.obj X) ⟶ Rⱼ.obj Y)
    [IsIso (Aᵢ.counit.app X)] [IsIso (Aⱼ.counit.app Y)] [Lⱼ.ReflectsIsomorphisms]
    (h : Rᵢ.map (A.homEquiv X Y f) ≫ e.hom.app Y = B.homEquiv _ _ g) :
    IsIso f ↔ IsIso g := by
  have he := adjointSquare_comparison Aᵢ Aⱼ A B e f g h
  calc
    IsIso f ↔ IsIso (L.map (Aᵢ.counit.app X) ≫ f) :=
      (isIso_comp_left_iff _ _).symm
    _ ↔ IsIso ((adjointSquareIso Aᵢ Aⱼ A B e).hom.app (Rᵢ.obj X) ≫
        Lⱼ.map g ≫ Aⱼ.counit.app Y) := by rw [he]
    _ ↔ IsIso (Lⱼ.map g) := by rw [isIso_comp_left_iff, isIso_comp_right_iff]
    _ ↔ IsIso g := isIso_iff_of_reflects_iso g Lⱼ

end SerrePositivity.KST.DerivedBlowup

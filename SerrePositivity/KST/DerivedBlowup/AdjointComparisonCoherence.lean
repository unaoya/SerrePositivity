module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
概要：KST §3.1 の制限比較の整合性を係数拡大比較へ移す随伴計算。
方針：右随伴の標準同型を介して随伴を移し、左随伴の一意性と Hom 同値の単射性を使う。
規約：任意同型の存在ではなく構成済みの標準左随伴同型を指定する。
使われ方：canonical な導来係数拡大比較の単位・合成条件。
-/

@[expose] public noncomputable section

universe u v w x y z

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- 概要：右随伴の標準単位同型から左随伴の標準単位同型を構成する。
方針：右随伴を恒等へ移し、恒等随伴との左随伴の一意性を使う。
規約：KST §3.1。使われ方：導来係数拡大の単位同型。 -/
def adjointComparisonIdIso {L R : C ⥤ C} (A : L ⊣ R) (e : R ≅ 𝟭 C) : L ≅ 𝟭 C :=
  Adjunction.leftAdjointUniq (A.ofNatIsoRight e) (Adjunction.id (C := C))

/-- 概要：右随伴側で単位条件を満たす射は標準左随伴単位同型の成分。
方針：移した随伴の Hom 同値で比較し、左随伴一意性の指定成分を計算する。
規約：KST §3.1。使われ方：canonical な係数拡大比較の単位条件。 -/
theorem adjointComparison_id {L R : C ⥤ C} (A : L ⊣ R) (e : R ≅ 𝟭 C)
    {X : C} (f : L.obj X ⟶ X) (hf : A.homEquiv X X f ≫ e.hom.app X = 𝟙 X) :
    f = (adjointComparisonIdIso A e).hom.app X := by
  apply ((A.ofNatIsoRight e).homEquiv X X).injective
  unfold adjointComparisonIdIso
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app (A.ofNatIsoRight e)
    (Adjunction.id (C := C)) X
  calc
    _ = 𝟙 X := by rw [Adjunction.homEquiv_ofNatIsoRight_apply]; exact hf
    _ = _ := hu.symm

variable {D : Type w} [Category.{x} D] {E : Type y} [Category.{z} E]

/-- 概要：右随伴の標準合成同型から左随伴の標準合成同型を構成する。
方針：二つの随伴を合成し、右側を直接制限へ移して左随伴の一意性を使う。
規約：KST §3.1。使われ方：導来係数拡大の標準合成同型。 -/
def adjointComparisonCompIso {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : D ⥤ E} {R₂ : E ⥤ D} {L₃ : C ⥤ E} {R₃ : E ⥤ C}
    (A₁ : L₁ ⊣ R₁) (A₂ : L₂ ⊣ R₂) (A₃ : L₃ ⊣ R₃) (e : R₂ ⋙ R₁ ≅ R₃) :
    L₁ ⋙ L₂ ≅ L₃ :=
  Adjunction.leftAdjointUniq ((A₁.comp A₂).ofNatIsoRight e) A₃

/-- 概要：右随伴比較が合成と整合すれば対応する左随伴比較も標準同型を介して整合する。
方針：合成して移した随伴の Hom 同値で左右を比較し、自然性と左随伴一意性を使う。
規約：KST §3.1。使われ方：canonical な導来係数拡大比較の三重条件。 -/
theorem adjointComparison_comp {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : D ⥤ E} {R₂ : E ⥤ D} {L₃ : C ⥤ E} {R₃ : E ⥤ C}
    (A₁ : L₁ ⊣ R₁) (A₂ : L₂ ⊣ R₂) (A₃ : L₃ ⊣ R₃) (e : R₂ ⋙ R₁ ≅ R₃)
    {X : C} {Y : D} {Z : E} (f : L₁.obj X ⟶ Y) (g : L₂.obj Y ⟶ Z)
    (k : L₃.obj X ⟶ Z)
    (h : A₁.homEquiv X Y f ≫ R₁.map (A₂.homEquiv Y Z g) ≫ e.hom.app Z =
      A₃.homEquiv X Z k) :
    L₂.map f ≫ g = (adjointComparisonCompIso A₁ A₂ A₃ e).hom.app X ≫ k := by
  let B := (A₁.comp A₂).ofNatIsoRight e
  apply (B.homEquiv X Z).injective
  change B.homEquiv X Z (L₂.map f ≫ g) =
    B.homEquiv X Z ((Adjunction.leftAdjointUniq B A₃).hom.app X ≫ k)
  rw [B.homEquiv_naturality_right ((Adjunction.leftAdjointUniq B A₃).hom.app X) k,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, ← A₃.homEquiv_unit]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change A₁.homEquiv X (R₂.obj Z)
      (A₂.homEquiv (L₁.obj X) Z (L₂.map f ≫ g)) ≫ e.hom.app Z = A₃.homEquiv X Z k
  rw [A₂.homEquiv_naturality_left f g,
    A₁.homEquiv_naturality_right f (A₂.homEquiv Y Z g)]
  simpa only [Category.assoc] using h

end SerrePositivity.KST.DerivedBlowup

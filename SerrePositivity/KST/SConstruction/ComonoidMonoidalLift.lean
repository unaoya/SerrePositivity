module
public import SerrePositivity.KST.SConstruction.ComonoidForgetStructure

/-! # 余モノイド射の比較から強モノイダル構造を持ち上げる
概要：underlying 圏で検証した coherent 法則を余モノイド値関手へ反映する。
方針：忠実な忘却関手の元の結合・単位・tensor 射の回収を使う。
規約：比較同型の underlying 射を変更しない。使われ方：Day Serre 余モノイド関手。
-/
@[expose] public section
universe v w u t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type t} [Category.{w} D] [MonoidalCategory D]

/-- 元の underlying 法則を持つ余モノイド比較を強モノイダル構造へ持ち上げる。 -/
def comonoidCoreMonoidalLift (F : D ⥤ Comon C)
    (ε : 𝟙_ (Comon C) ≅ F.obj (𝟙_ D))
    (μ : ∀ X Y, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y))
    (hnl : ∀ {X Y} (f : X ⟶ Y) X',
      (F.map f).hom ▷ (F.obj X').X ≫ (μ Y X').hom.hom =
        (μ X X').hom.hom ≫ (F.map (f ▷ X')).hom)
    (hnr : ∀ {X Y} X' (f : X ⟶ Y),
      (F.obj X').X ◁ (F.map f).hom ≫ (μ X' Y).hom.hom =
        (μ X' X).hom.hom ≫ (F.map (X' ◁ f)).hom)
    (ha : ∀ X Y Z,
      (μ X Y).hom.hom ▷ (F.obj Z).X ≫ (μ (X ⊗ Y) Z).hom.hom ≫
          (F.map (α_ X Y Z).hom).hom =
        (α_ (F.obj X).X (F.obj Y).X (F.obj Z).X).hom ≫
          (F.obj X).X ◁ (μ Y Z).hom.hom ≫ (μ X (Y ⊗ Z)).hom.hom)
    (hl : ∀ X, (λ_ (F.obj X).X).hom =
      ε.hom.hom ▷ (F.obj X).X ≫ (μ (𝟙_ D) X).hom.hom ≫ (F.map (λ_ X).hom).hom)
    (hr : ∀ X, (ρ_ (F.obj X).X).hom =
      (F.obj X).X ◁ ε.hom.hom ≫ (μ X (𝟙_ D)).hom.hom ≫ (F.map (ρ_ X).hom).hom) :
    F.CoreMonoidal where
  εIso := ε
  μIso := μ
  μIso_hom_natural_left f X' := by
    apply Comon.Hom.ext
    simpa only [Comon.tensorObj_X, comonoidForget_unitObj,
      Comon.comp_hom', Comon.monoidal_whiskerRight_hom] using hnl f X'
  μIso_hom_natural_right X' f := by
    apply Comon.Hom.ext
    simpa only [Comon.tensorObj_X, comonoidForget_unitObj,
      Comon.comp_hom', Comon.monoidal_whiskerLeft_hom] using hnr X' f
  associativity X Y Z := by
    apply Comon.Hom.ext
    simpa only [Comon.tensorObj_X, comonoidForget_unitObj,
      Comon.comp_hom', Comon.monoidal_whiskerRight_hom,
      Comon.monoidal_whiskerLeft_hom, comonoidForget_associator] using ha X Y Z
  left_unitality X := by
    apply Comon.Hom.ext
    simpa only [Comon.tensorObj_X, comonoidForget_unitObj,
      Comon.comp_hom', Comon.monoidal_whiskerRight_hom,
      comonoidForget_leftUnitor] using hl X
  right_unitality X := by
    apply Comon.Hom.ext
    simpa only [Comon.tensorObj_X, comonoidForget_unitObj,
      Comon.comp_hom', Comon.monoidal_whiskerLeft_hom,
      comonoidForget_rightUnitor] using hr X

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionHomNaturality
public import SerrePositivity.DifferentialGraded.Endomorphism.LocalizationHomNaturality

/-! # graph導来延長と導来制限の随伴

## 概要
graph導来延長と導来制限の随伴。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgDerivedExtensionHomEquiv_naturality_right (X : DerivedModuleCategory A D)
    {Y Y' : DerivedModuleCategory A E}
    (φ : (dgDerivedExtension A D E F).obj X ⟶ Y) (g : Y ⟶ Y') :
    dgDerivedExtensionHomEquiv A D E F X Y' (φ ≫ g) =
      dgDerivedExtensionHomEquiv A D E F X Y φ ≫ (dgDerivedRestriction A D E F).map g := by
  apply localizationHom_naturality_right (moduleQuasiIso A E)
    (dgDerivedExtension A D E F) (dgDerivedRestriction A D E F)
    (fun X Y φ => dgDerivedExtensionHomEquiv A D E F X Y φ)
  intro X M M' f φ
  exact dgDerivedExtensionHomEquivOnModules_naturality_right A D E F X.as.obj φ f

lemma dgDerivedExtensionHomEquiv_naturality_left {X X' : DerivedModuleCategory A D}
    (f : X ⟶ X') (Y : DerivedModuleCategory A E)
    (φ : (dgDerivedExtension A D E F).obj X' ⟶ Y) :
    dgDerivedExtensionHomEquiv A D E F X Y ((dgDerivedExtension A D E F).map f ≫ φ) =
      f ≫ dgDerivedExtensionHomEquiv A D E F X' Y φ := by
  apply localizationHom_naturality_left (moduleQuasiIso A D)
    (dgDerivedExtension A D E F) (dgDerivedRestriction A D E F)
    (fun X Y φ => dgDerivedExtensionHomEquiv A D E F X Y φ)
  intro N N' f Y φ
  exact dgDerivedExtensionHomEquivOnModules_naturality_left A D E F Y.as.obj f φ

/-- 任意dg関手のgraph導来延長と導来制限は実際に随伴する。 -/
def dgDerivedExtensionRestrictionAdjunction :
    dgDerivedExtension A D E F ⊣ dgDerivedRestriction A D E F :=
  Adjunction.mkOfHomEquiv {
    homEquiv := dgDerivedExtensionHomEquiv A D E F
    homEquiv_naturality_right := fun φ g =>
      dgDerivedExtensionHomEquiv_naturality_right A D E F _ φ g
    homEquiv_naturality_left_symm := by
      intro X X' Y f g
      apply (dgDerivedExtensionHomEquiv A D E F X Y).injective
      rw [Equiv.apply_symm_apply, dgDerivedExtensionHomEquiv_naturality_left,
        Equiv.apply_symm_apply] }

/-- 射影解像度で構成した主導来延長–制限随伴の単位。 -/
def dgDerivedExtensionUnit : 𝟭 (DerivedModuleCategory A D) ⟶
    dgDerivedExtension A D E F ⋙ dgDerivedRestriction A D E F :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).unit

/-- 射影解像度で構成した主導来延長–制限随伴の余単位。 -/
def dgDerivedExtensionCounit : dgDerivedRestriction A D E F ⋙
    dgDerivedExtension A D E F ⟶ 𝟭 (DerivedModuleCategory A E) :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).counit

lemma dgDerivedExtension_left_triangle (X : DerivedModuleCategory A D) :
    (dgDerivedExtension A D E F).map ((dgDerivedExtensionUnit A D E F).app X) ≫
      (dgDerivedExtensionCounit A D E F).app ((dgDerivedExtension A D E F).obj X) = 𝟙 _ :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).left_triangle_components X

lemma dgDerivedExtension_right_triangle (Y : DerivedModuleCategory A E) :
    (dgDerivedExtensionUnit A D E F).app ((dgDerivedRestriction A D E F).obj Y) ≫
      (dgDerivedRestriction A D E F).map ((dgDerivedExtensionCounit A D E F).app Y) = 𝟙 _ :=
  (dgDerivedExtensionRestrictionAdjunction A D E F).right_triangle_components Y

end SerrePositivity.DifferentialGraded

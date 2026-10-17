module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionHomGeneration

/-! # 任意kernelの実際の導来右随伴

## 概要
任意の主導来kernel作用に右随伴を構成し、そのunit/counitと三角恒等式を公開する。

## 方針
telescopeによる全入力のHom表現と始域自然性からMathlibの随伴構成を適用する。

## 規約と注意
任意可換環・非有界複体、独立対象宇宙。局所Hom K-flat性・kernel列の射影性は不要。
随伴の存在を仮定せず、引用を追加しない。

## 使われ方
U16aの一般随伴、U16c統合時の逆同値との比較とunit/counit可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)

/-- 実際のtelescopeによる、右随伴向きの全入力Hom同値。 -/
def kernelDerivedHomEquiv (X : DerivedModuleCategory A D) (Y : DerivedModuleCategory A E) :
    ((kernelDerivedTensor A D E K).obj X ⟶ Y) ≃
      (X ⟶ (kernelBrownTelescope A D E K Y).obj) :=
  (kernelBrownTelescopeHomEquiv A D E K Y (kernelBrownTelescope A D E K Y) X).symm

/-- Hom同値は始域の全導来射に自然。 -/
lemma kernelDerivedHomEquiv_naturality (X' X : DerivedModuleCategory A D)
    (Y : DerivedModuleCategory A E) (f : X' ⟶ X)
    (g : (kernelDerivedTensor A D E K).obj X ⟶ Y) :
    kernelDerivedHomEquiv A D E K X' Y ((kernelDerivedTensor A D E K).map f ≫ g) =
      f ≫ kernelDerivedHomEquiv A D E K X Y g := by
  let S := kernelBrownTelescope A D E K Y
  let e := kernelBrownTelescopeHomEquiv A D E K Y S
  apply (e X').injective
  change e X' ((e X').symm ((kernelDerivedTensor A D E K).map f ≫ g)) =
    e X' (f ≫ (e X).symm g)
  rw [Equiv.apply_symm_apply]
  change _ = (kernelDerivedTensor A D E K).map (f ≫ (e X).symm g) ≫ S.target
  rw [Functor.map_comp, Category.assoc]
  change _ = (kernelDerivedTensor A D E K).map f ≫ e X ((e X).symm g)
  rw [Equiv.apply_symm_apply]

/-- Hom同値の逆写像はtelescopeの標的射による実際の比較。 -/
lemma kernelDerivedHomEquiv_symm_apply (X : DerivedModuleCategory A D)
    (Y : DerivedModuleCategory A E) (f : X ⟶ (kernelBrownTelescope A D E K Y).obj) :
    (kernelDerivedHomEquiv A D E K X Y).symm f =
      (kernelDerivedTensor A D E K).map f ≫ (kernelBrownTelescope A D E K Y).target := rfl

/-- 任意kernelの実際の導来右随伴。 -/
def kernelDerivedHom : DerivedModuleCategory A E ⥤ DerivedModuleCategory A D :=
  Adjunction.rightAdjointOfEquiv (kernelDerivedHomEquiv A D E K)
    (kernelDerivedHomEquiv_naturality A D E K)

/-- 任意kernel作用と実際の導来Homの随伴。 -/
def kernelDerivedAdjunction : kernelDerivedTensor A D E K ⊣ kernelDerivedHom A D E K :=
  Adjunction.adjunctionOfEquivRight (kernelDerivedHomEquiv A D E K)
    (kernelDerivedHomEquiv_naturality A D E K)

/-- 実際の導来随伴の単位。 -/
def kernelDerivedUnit : 𝟭 (DerivedModuleCategory A D) ⟶
    kernelDerivedTensor A D E K ⋙ kernelDerivedHom A D E K :=
  (kernelDerivedAdjunction A D E K).unit

/-- 実際の導来随伴の余単位。 -/
def kernelDerivedCounit : kernelDerivedHom A D E K ⋙ kernelDerivedTensor A D E K ⟶
    𝟭 (DerivedModuleCategory A E) :=
  (kernelDerivedAdjunction A D E K).counit

/-- 右随伴の値は構成済みtelescopeそのもの。 -/
lemma kernelDerivedHom_obj (Y : DerivedModuleCategory A E) :
    (kernelDerivedHom A D E K).obj Y = (kernelBrownTelescope A D E K Y).obj := rfl

/-- 実際の余単位はtelescopeを構成した標的射と一致する。 -/
lemma kernelDerivedCounit_model (Y : DerivedModuleCategory A E) :
    (kernelDerivedCounit A D E K).app Y = (kernelBrownTelescope A D E K Y).target := by
  change (kernelDerivedTensor A D E K).map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id]
  erw [Category.id_comp]
  rfl

/-- 実際の導来単位・余単位の左三角恒等式。 -/
lemma kernelDerived_left_triangle (X : DerivedModuleCategory A D) :
    (kernelDerivedTensor A D E K).map ((kernelDerivedUnit A D E K).app X) ≫
      (kernelDerivedCounit A D E K).app ((kernelDerivedTensor A D E K).obj X) = 𝟙 _ :=
  (kernelDerivedAdjunction A D E K).left_triangle_components X

/-- 実際の導来単位・余単位の右三角恒等式。 -/
lemma kernelDerived_right_triangle (Y : DerivedModuleCategory A E) :
    (kernelDerivedUnit A D E K).app ((kernelDerivedHom A D E K).obj Y) ≫
      (kernelDerivedHom A D E K).map ((kernelDerivedCounit A D E K).app Y) = 𝟙 _ :=
  (kernelDerivedAdjunction A D E K).right_triangle_components Y

end SerrePositivity.DifferentialGraded.Morita

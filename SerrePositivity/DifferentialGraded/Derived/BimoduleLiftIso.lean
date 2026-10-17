module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleBasic

/-! # 指定局所化への前合成で与えた自然同型を全導来bimodule圏へ移す

## 概要
指定局所化への前合成で与えた自然同型を全導来bimodule圏へ移す。

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
universe u v w z z'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] {T : Type z} [Category.{z'} T]

/-- 局所化への前合成上の自然同型を、指定された二つの導来関手の間へ降ろす。 -/
def bimoduleDerivedIsoOfPrecomp (G H : DerivedBimoduleCategory A B C ⥤ T)
    (e : bimoduleToDerived A B C ⋙ G ≅ bimoduleToDerived A B C ⋙ H) : G ≅ H := by
  letI sourceLifting : Localization.Lifting (bimoduleToDerived A B C)
      (BimoduleCategory.quasiIso A B C) (bimoduleToDerived A B C ⋙ G) G := ⟨Iso.refl _⟩
  letI targetLifting : Localization.Lifting (bimoduleToDerived A B C)
      (BimoduleCategory.quasiIso A B C) (bimoduleToDerived A B C ⋙ H) H := ⟨Iso.refl _⟩
  exact Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (bimoduleToDerived A B C ⋙ G) (bimoduleToDerived A B C ⋙ H) G H e

lemma bimoduleDerivedIsoOfPrecomp_hom_app (G H : DerivedBimoduleCategory A B C ⥤ T)
    (e : bimoduleToDerived A B C ⋙ G ≅ bimoduleToDerived A B C ⋙ H)
    (P : BimoduleCategory A B C) :
    (bimoduleDerivedIsoOfPrecomp A B C G H e).hom.app ((bimoduleToDerived A B C).obj P) =
      e.hom.app P := by
  simp only [bimoduleDerivedIsoOfPrecomp, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  change 𝟙 _ ≫ e.hom.app P ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

lemma bimoduleDerivedIsoOfPrecomp_inv_app (G H : DerivedBimoduleCategory A B C ⥤ T)
    (e : bimoduleToDerived A B C ⋙ G ≅ bimoduleToDerived A B C ⋙ H)
    (P : BimoduleCategory A B C) :
    (bimoduleDerivedIsoOfPrecomp A B C G H e).inv.app ((bimoduleToDerived A B C).obj P) =
      e.inv.app P := by
  simp only [bimoduleDerivedIsoOfPrecomp, Localization.liftNatIso_inv,
    Localization.liftNatTrans_app]
  change 𝟙 _ ≫ e.inv.app P ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

end SerrePositivity.DifferentialGraded

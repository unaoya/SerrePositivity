module
public import SerrePositivity.DifferentialGraded.Module.RestrictionEnriched
public import SerrePositivity.DifferentialGraded.Derived.Restriction
public import SerrePositivity.DifferentialGraded.Endomorphism.ConeTriangleComparison
public import SerrePositivity.DifferentialGraded.Derived.Shift

/-! # 導来制限の全Homモデルと整合的整数shift

## 概要
導来制限の全Homモデルと整合的整数shift。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
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

lemma dgDerivedRestriction_enriched_fac :
    moduleToDerived A E ⋙ dgDerivedRestriction A D E F =
      (dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D := by
  rw [dgModuleRestriction_onClosed_eq]
  exact dgDerivedRestriction_fac A D E F

instance dgDerivedRestriction_enriched_lifting :
    Localization.Lifting (moduleToDerived A E) (moduleQuasiIso A E)
      ((dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D)
      (dgDerivedRestriction A D E F) := ⟨eqToIso (dgDerivedRestriction_enriched_fac A D E F)⟩

/-- U14の全dg関手用shift比較を局所化し、既存の導来制限に与える。 -/
@[instance_reducible]
def dgDerivedRestrictionCommShift : (dgDerivedRestriction A D E F).CommShift ℤ := by
  letI := dgModuleFunctorCommShift A E D (dgModuleRestriction A D E F.op)
  exact Functor.commShiftOfLocalization (moduleToDerived A E) (moduleQuasiIso A E) ℤ
    ((dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D)
    (dgDerivedRestriction A D E F)

section
local instance : (dgModuleRestriction A D E F.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A E D (dgModuleRestriction A D E F.op)
local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F

lemma dgDerivedRestrictionFac_commShift :
    NatTrans.CommShift (eqToIso (dgDerivedRestriction_enriched_fac A D E F)).hom ℤ := by
  change NatTrans.CommShift
    (Localization.Lifting.iso (moduleToDerived A E) (moduleQuasiIso A E)
      ((dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D)
      (dgDerivedRestriction A D E F)).hom ℤ
  exact NatTrans.commShift_iso_hom_of_localization (moduleToDerived A E) (moduleQuasiIso A E) ℤ
    ((dgModuleRestriction A D E F.op).onClosed ⋙ moduleToDerived A D)
    (dgDerivedRestriction A D E F)
end
end SerrePositivity.DifferentialGraded

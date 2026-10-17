module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleModuleEquivalence
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestriction
public import SerrePositivity.DifferentialGraded.Derived.FunctorDerivedEquivalence
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalenceOpposite
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalenceTensor

/-! # 明示した局所K-flat性の下での導来bimodule制限の同値性

## 概要
明示した局所K-flat性の下での導来bimodule制限の同値性。

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
universe u v w z t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A B D) (G : DGFunctor A C E)

def bimoduleRestrictionModuleDerived :
    DerivedModuleCategory A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ ⥤
      DerivedModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ :=
  moduleDerivedRestriction A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
    (bimoduleRestrictionIndex A B C D E F G)

lemma bimoduleRestrictionModuleDerived_fac :
    moduleToDerived A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ ⋙
        bimoduleRestrictionModuleDerived A B C D E F G =
      moduleRestriction A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
        (bimoduleRestrictionIndex A B C D E F G) ⋙
          moduleToDerived A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ :=
  moduleDerivedRestriction_fac _ _ _ _

/-- 制限の積dg圏表示は、閉零の右加群–bimodule比較と自然に可換。 -/
def bimoduleRestrictionModuleIso :
    bimoduleRestriction A B C D E F G ⋙ (rightModuleBimoduleEquivalence A B C).inverse ≅
      (rightModuleBimoduleEquivalence A D E).inverse ⋙
        moduleRestriction A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
          (bimoduleRestrictionIndex A B C D E F G) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (rightModuleBimoduleEquivalence A B C).unitIso.symm ≪≫
          Functor.rightUnitor _)

/-- 既存の実際の導来bimodule制限を右加群の導来制限と比較する全射自然な正方形。 -/
def derivedBimoduleRestrictionModuleIso :
    derivedBimoduleRestriction A B C D E F G ⋙
        (rightModuleBimoduleDerivedEquivalence A B C).inverse ≅
      (rightModuleBimoduleDerivedEquivalence A D E).inverse ⋙
        bimoduleRestrictionModuleDerived A B C D E F G := by
  let Q₁ := bimoduleToDerived A D E
  let W₁ := BimoduleCategory.quasiIso A D E
  let M₁ := moduleToDerived A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
  let M₂ := moduleToDerived A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  let E₁ := rightModuleBimoduleDerivedEquivalence A D E
  let E₂ := rightModuleBimoduleDerivedEquivalence A B C
  let R₀ := bimoduleRestriction A B C D E F G
  let R := bimoduleRestrictionModuleDerived A B C D E F G
  let S := derivedBimoduleRestriction A B C D E F G
  let U := (R₀ ⋙ bimoduleToDerived A B C) ⋙ E₂.inverse
  let V := bimoduleToModuleDerived A D E ⋙ R
  letI : Localization.Lifting Q₁ W₁ U (S ⋙ E₂.inverse) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (derivedBimoduleRestriction_fac A B C D E F G)) E₂.inverse⟩
  letI : Localization.Lifting Q₁ W₁ V (E₁.inverse ⋙ R) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (rightModuleBimoduleDerived_inverse_fac A D E) R⟩
  apply Localization.liftNatIso Q₁ W₁ U V (S ⋙ E₂.inverse) (E₁.inverse ⋙ R)
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R₀ (rightModuleBimoduleDerived_inverse_fac A B C) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (bimoduleRestrictionModuleIso A B C D E F G) M₂ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (eqToIso (bimoduleRestrictionModuleDerived_fac A B C D E F G)).symm ≪≫
    (Functor.associator _ M₁ R).symm

omit [Small.{u} B] [Small.{u} C] [Small.{u} D] [Small.{u} E] in
lemma bimoduleRestrictionDG_quasiEquivalence (hF : QuasiEquivalence F) (hG : QuasiEquivalence G)
    (hC : localHomKFlat A C) (hD : localHomKFlat A D) :
    QuasiEquivalence (F.op.tensor G).op :=
  quasiEquivalence_op _ (quasiEquivalence_tensor F.op G (quasiEquivalence_op F hF) hG hC
    (fun x y => hD y.unop x.unop))

lemma derivedBimoduleRestriction_isEquivalence (hF : QuasiEquivalence F) (hG : QuasiEquivalence G)
    (hC : localHomKFlat A C) (hD : localHomKFlat A D) :
    (derivedBimoduleRestriction A B C D E F G).IsEquivalence := by
  let R := bimoduleRestrictionModuleDerived A B C D E F G
  have : R.IsEquivalence :=
    (dgFunctorDerivedEquivalence A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (F.op.tensor G).op
      (bimoduleRestrictionDG_quasiEquivalence A B C D E F G hF hG hC hD)).isEquivalence_inverse
  have : ((rightModuleBimoduleDerivedEquivalence A D E).inverse ⋙ R).IsEquivalence := inferInstance
  have : (derivedBimoduleRestriction A B C D E F G ⋙
      (rightModuleBimoduleDerivedEquivalence A B C).inverse).IsEquivalence :=
    Functor.isEquivalence_of_iso (derivedBimoduleRestrictionModuleIso A B C D E F G).symm
  exact Functor.isEquivalence_of_comp_right _ (rightModuleBimoduleDerivedEquivalence A B C).inverse

/-- 指定された実際の導来制限を順方向とする同値。 -/
def derivedBimoduleRestrictionEquivalence (hF : QuasiEquivalence F) (hG : QuasiEquivalence G)
    (hC : localHomKFlat A C) (hD : localHomKFlat A D) :
    DerivedBimoduleCategory A D E ≌ DerivedBimoduleCategory A B C := by
  letI := derivedBimoduleRestriction_isEquivalence A B C D E F G hF hG hC hD
  exact (derivedBimoduleRestriction A B C D E F G).asEquivalence

end SerrePositivity.DifferentialGraded

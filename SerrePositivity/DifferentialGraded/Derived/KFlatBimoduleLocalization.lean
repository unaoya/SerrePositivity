module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorFunctor
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorKFlatComparison

/-! # 右相対K-flat因子の準同型局所化上の導来合成関手

## 概要
右相対K-flat因子の準同型局所化上の導来合成関手。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleHomotopy.lean、Derived/
KFlatBimoduleResolution.lean。固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

omit [DGCategory A B] [Small.{u} B] in
def rightKFlatInclusion : RightKFlatBimoduleCategory A C E ⥤ BimoduleCategory A C E :=
  ObjectProperty.ι _

omit [DGCategory A B] [Small.{u} B] in
def rightKFlatQuasiIso : MorphismProperty (RightKFlatBimoduleCategory A C E) :=
  (BimoduleCategory.quasiIso A C E).inverseImage (rightKFlatInclusion A C E)

omit [DGCategory A B] [Small.{u} B] in
abbrev DerivedRightKFlatBimoduleCategory := (rightKFlatQuasiIso A C E).Localization

omit [DGCategory A B] [Small.{u} B] in
abbrev rightKFlatToDerived : RightKFlatBimoduleCategory A C E ⥤
    DerivedRightKFlatBimoduleCategory A C E := (rightKFlatQuasiIso A C E).Q

omit [DGCategory A B] [Small.{u} B] in
def rightKFlatDerivedInclusion : DerivedRightKFlatBimoduleCategory A C E ⥤
    DerivedBimoduleCategory A C E :=
  Localization.Construction.lift (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E)
    (fun _ _ f hf => bimoduleToDerived_inverts A C E f.hom hf)

omit [DGCategory A B] [Small.{u} B] in
lemma rightKFlatDerivedInclusion_fac :
    rightKFlatToDerived A C E ⋙ rightKFlatDerivedInclusion A C E =
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E :=
  Localization.Construction.fac _ _

lemma derivedComposeWithFunctor_inverts :
    (rightKFlatQuasiIso A C E).IsInvertedBy (derivedComposeWithFunctor A B C E) := by
  intro Q Q' g hg
  change IsIso (derivedComposeWithMap A B C E Q.property Q'.property g.hom)
  change IsIso (derivedComposeWithKFlatIso A B C E Q.property Q'.property g.hom hg).hom
  infer_instance

/-- 前の変数の導来圏に値を持つ関手族を、後のK-flat因子の局所化へ降下させる。 -/
def rightFactorLocalizedComposeFunctor : DerivedRightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  Localization.Construction.lift (derivedComposeWithFunctor A B C E)
    (derivedComposeWithFunctor_inverts A B C E)

lemma rightFactorLocalizedComposeFunctor_fac :
    rightKFlatToDerived A C E ⋙ rightFactorLocalizedComposeFunctor A B C E =
      derivedComposeWithFunctor A B C E := Localization.Construction.fac _ _

lemma rightFactorLocalizedComposeFunctor_map_base {Q Q' : RightKFlatBimoduleCategory A C E}
    (g : Q ⟶ Q') :
    (rightFactorLocalizedComposeFunctor A B C E).map ((rightKFlatToDerived A C E).map g) =
      (derivedComposeWithFunctor A B C E).map g :=
  eq_of_heq (Functor.hcongr_hom (rightFactorLocalizedComposeFunctor_fac A B C E) g)

end SerrePositivity.DifferentialGraded.BimoduleTensor

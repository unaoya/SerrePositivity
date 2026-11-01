module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorMaps
public import SerrePositivity.DifferentialGraded.Tensor.Triple

/-! # 対角bimoduleを固定した導来合成の右単位自然同型

## 概要
対角bimoduleを固定した導来合成の右単位自然同型。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleTensorEvaluation.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]
local notation "Δ" => BimoduleCategory.of A C C (Bimodule.diagonal A C)

/-- 元のbimodule単位比較を出力の局所化へ送った自然同型。 -/
def rightUnitLocalizedIso :
    composeWith A B C C Δ ⋙ bimoduleToDerived A B C ≅ bimoduleToDerived A B C :=
  isoWhiskerRight (rightUnitNatIso A B C) (bimoduleToDerived A B C) ≪≫
    Functor.leftUnitor (bimoduleToDerived A B C)

lemma rightUnitLocalizedIso_hom_app (P : BimoduleCategory A B C) :
    (rightUnitLocalizedIso A B C).hom.app P =
      (bimoduleToDerived A B C).map
        (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom := by
  change (bimoduleToDerived A B C).map
      (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- 対角因子は右相対K-flatなので、単位比較を導来圏全体の自然同型に降ろせる。 -/
def derivedRightUnitIso :
    derivedComposeWith A B C C Δ (Bimodule.diagonal_rightRelativeKFlat A C) ≅
      𝟭 (DerivedBimoduleCategory A B C) :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (composeWith A B C C Δ ⋙ bimoduleToDerived A B C) (bimoduleToDerived A B C)
    (derivedComposeWith A B C C Δ (Bimodule.diagonal_rightRelativeKFlat A C))
    (𝟭 (DerivedBimoduleCategory A B C)) (rightUnitLocalizedIso A B C)

lemma derivedRightUnitIso_hom_app (P : BimoduleCategory A B C) :
    (derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P) =
      (derivedComposeWithComputation A B C C Δ (Bimodule.diagonal_rightRelativeKFlat A C) P).hom ≫
        (bimoduleToDerived A B C).map
          (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom := by
  have h := Localization.liftNatTrans_app (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C)
    (composeWith A B C C Δ ⋙ bimoduleToDerived A B C) (bimoduleToDerived A B C)
    (derivedComposeWith A B C C Δ (Bimodule.diagonal_rightRelativeKFlat A C))
    (𝟭 (DerivedBimoduleCategory A B C)) (rightUnitLocalizedIso A B C).hom P
  change (derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P) =
    (derivedComposeWithComputation A B C C Δ (Bimodule.diagonal_rightRelativeKFlat A C) P).hom ≫
      (rightUnitLocalizedIso A B C).hom.app P ≫ 𝟙 _ at h
  rw [Category.comp_id, rightUnitLocalizedIso_hom_app] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor

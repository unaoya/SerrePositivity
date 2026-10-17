module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionResolution
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorEvaluation

/-! # 全後因子上の導来bimodule合成の右単位自然同型

## 概要
全後因子上の導来bimodule合成の右単位自然同型。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionLeftUnit.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

omit [DGCategory A B] [Small.{u} B] in
def rightKFlatDiagonal : RightKFlatBimoduleCategory A C C :=
  ⟨BimoduleCategory.of A C C (Bimodule.diagonal A C), Bimodule.diagonal_rightRelativeKFlat A C⟩

def derivedBimoduleRightUnitIso (hC : localHomKFlat A C) :
    (derivedBimoduleComposeFunctor A B C C hC).obj
        ((bimoduleToDerived A C C).obj (rightKFlatDiagonal A C).obj) ≅
      𝟭 (DerivedBimoduleCategory A B C) :=
  derivedBimoduleComposeKFlatIso A B C C hC (rightKFlatDiagonal A C) ≪≫ derivedRightUnitIso A B C

lemma derivedBimoduleRightUnitIso_base_app (hC : localHomKFlat A C) (P : BimoduleCategory A B C) :
    (derivedBimoduleRightUnitIso A B C hC).hom.app ((bimoduleToDerived A B C).obj P) =
      (derivedBimoduleComposeKFlatValueIso A B C C hC (rightKFlatDiagonal A C) P).hom ≫
        (bimoduleToDerived A B C).map
          (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom := by
  change (derivedBimoduleComposeKFlatValueIso A B C C hC (rightKFlatDiagonal A C) P).hom ≫
    (derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P) = _
  rw [derivedRightUnitIso_base_app]

end SerrePositivity.DifferentialGraded.BimoduleTensor

module
public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleMap
public import SerrePositivity.DifferentialGraded.Tensor.ComposeRightRestriction
public import SerrePositivity.DifferentialGraded.Tensor.UnitBimoduleIso

/-! # 対角のHom比較と中間制限比較による左単位子の保存

## 概要
対角のHom比較と中間制限比較による左単位子の保存。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] (F : DGFunctor A D B)

local notation "RP" P => Functor.obj
  (BimoduleCategory.middleRightRestrictionFunctor A B D C F) P
local notation "LD" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B B D F)
  (BimoduleCategory.of A B B (Bimodule.diagonal A B))

/-- 対角比較と外側右制限比較を続けた射をcoend包含で計算する。 -/
@[reassoc]
lemma ι_leftUnitRestriction_comparison (P : BimoduleCategory A B C) (d x : D) (c : C) :
    BalancedTensor.ι A D ((BimoduleCategory.underlying A D C (RP P)).rightAt c)
        ((Bimodule.diagonal A D).leftAt d) x ≫
      composeValueMap A D D C (Bimodule.diagonalRestrictionMap A D B F) (𝟙 (RP P)) d c ≫
      (composeRightRestrictionValueIso A B D D C F
        (BimoduleCategory.underlying A B D LD) (BimoduleCategory.underlying A D C (RP P))
        d c).hom =
    (𝟙 ((BimoduleCategory.underlying A B C P).value (F.obj x) c) ⊗ₘ F.map d x) ≫
      BalancedTensor.ι A D ((BimoduleCategory.underlying A D C (RP P)).rightAt c)
        ((Bimodule.leftRestriction A B B D F (Bimodule.diagonal A B)).leftAt (F.obj d)) x := by
  have h₁ := ι_composeValueMap A D D C (Bimodule.diagonalRestrictionMap A D B F)
    (𝟙 (RP P)) d x c
  have h₂ := ι_composeRightRestrictionValueIso_hom A B D D C F
    (BimoduleCategory.underlying A B D LD) (BimoduleCategory.underlying A D C (RP P)) d c x
  have h := congrArg (fun k => k ≫ (composeRightRestrictionValueIso A B D D C F
    (BimoduleCategory.underlying A B D LD) (BimoduleCategory.underlying A D C (RP P))
    d c).hom) h₁
  simp only [Bimodule.diagonalRestrictionMap_value, CategoryTheory.Functor.map_id] at h
  refine (Category.assoc _ _ _).symm.trans (h.trans ?_)
  have h₂' := congrArg (fun k =>
    (𝟙 ((BimoduleCategory.underlying A B C P).value (F.obj x) c) ⊗ₘ F.map d x) ≫ k) h₂
  convert h₂' using 1 <;> rfl

/-- 対角比較・外側右制限・中間比較・左単位子を値の複体で照合する。 -/
lemma leftUnitRestriction_value (P : BimoduleCategory A B C) (d : D) (c : C) :
    composeValueMap A D D C (Bimodule.diagonalRestrictionMap A D B F) (𝟙 (RP P)) d c ≫
      (composeRightRestrictionValueIso A B D D C F
        (BimoduleCategory.underlying A B D LD) (BimoduleCategory.underlying A D C (RP P))
        d c).hom ≫
      middleRestrictionComparisonValue A B B D C F (Bimodule.diagonal A B)
        (BimoduleCategory.underlying A B C P) (F.obj d) c ≫
      (leftUnitValueIso A B C (BimoduleCategory.underlying A B C P) (F.obj d) c).hom =
    (leftUnitValueIso A D C (BimoduleCategory.underlying A D C (RP P)) d c).hom := by
  apply BalancedTensor.hom_ext
  intro x
  erw [ι_leftUnitRestriction_comparison_assoc A B D C F P d x c]
  erw [ι_middleRestrictionComparisonValue_assoc A B B D C F (Bimodule.diagonal A B)
    (BimoduleCategory.underlying A B C P) (F.obj d) c x]
  rw [ι_leftUnitValueIso_hom]
  erw [ι_leftUnitValueIso_hom A D C (BimoduleCategory.underlying A D C (RP P)) d x c]
  exact (BalancedTensor.rightAction_restrict A D B F
    ((BimoduleCategory.underlying A B C P).rightAt c) d x).symm

/-- 左単位子は対角のHom比較・外側右制限・中間比較と整合する。 -/
lemma leftUnitRestriction (P : BimoduleCategory A B C) :
    composeMap A D D C (Bimodule.diagonalRestrictionMap A D B F) (𝟙 (RP P)) ≫
      (composeRightRestrictionIso A B D D C F LD (RP P)).hom ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
        (middleRestrictionComparisonMap A B B D C F (Bimodule.diagonal A B)
          (BimoduleCategory.underlying A B C P)) ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
        (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom =
    (leftBimoduleUnitIso A D C (BimoduleCategory.underlying A D C (RP P))).hom := by
  apply BimoduleCategory.value_hom_ext A D C
  intro d c
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    composeRightRestrictionIso_hom_value]
  erw [BimoduleCategory.middleRightRestrictionMap_value_eval A B D C F
    (middleRestrictionComparisonMap A B B D C F (Bimodule.diagonal A B)
      (BimoduleCategory.underlying A B C P)) d c,
    BimoduleCategory.middleRightRestrictionMap_value_eval A B D C F
      (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom d c,
    middleRestrictionComparisonMap_value_eval,
    leftBimoduleUnitIso_hom_value, leftBimoduleUnitIso_hom_value]
  exact leftUnitRestriction_value A B D C F P d c

end SerrePositivity.DifferentialGraded.BimoduleTensor

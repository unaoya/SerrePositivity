module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleSemifreeKFlat
public import Mathlib.Data.ZMod.Basic

/-! # local Hom条件による右相対K-flat bimodule解像度の監査

## 概要
local Hom条件による右相対K-flat bimodule解像度の監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

example (b : B) (c₀ c : C) (K : Complex A) :
    (tensorRightRestriction A B C c).obj
        ((freeAt (A := A) (D := (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
          (op ((op b, c₀) : DGTensorCategory A Bᵒᵖ C))).obj K) ≅
      (freeAt b).obj (K ⊗ (c₀ ⟶[Complex A] c)) :=
  restrictedFreeIso A B C b c₀ c K

example (hC : localHomKFlat A C) (M : BimoduleCategory A B C)
    (P : BimoduleSemifreeResolution A B C M) :
    Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C P.obj) :=
  P.rightRelativeKFlat A B C hC

example (hC : localHomKFlat A C) (M : BimoduleCategory A B C) :
    ∃ (P : BimoduleCategory A B C) (q : P ⟶ M),
      Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C P) ∧
        BimoduleCategory.quasiIso A B C q :=
  exists_rightRelativeKFlat_bimodule_resolution A B C hC M

example (b b₀ : B) (c₀ c : C)
    (h : GradedHom A b b₀ (-1)) (g : GradedHom A c₀ c 1) :
    ((moduleEvaluation A B b).map (restrictedRepresentableIso A B C b₀ c₀ c).hom).f 0
      (ιTensorObj (b ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c) (-1) 1 0 (by decide) (h ⊗ₜ[A] g)) =
    -ιTensorObj (c₀ ⟶[Complex A] c) (b ⟶[Complex A] b₀) 1 (-1) 0 (by decide) (g ⊗ₜ[A] h) := by
  rw [restrictedRepresentableIso_hom_eval]
  exact (signedSwap_apply (b ⟶[Complex A] b₀) (c₀ ⟶[Complex A] c)
    (-1) 1 0 (by decide) h g).trans (by norm_num)

example (B : Type v) (C : Type w) [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    [Small.{0} B] [Small.{0} C] (hC : localHomKFlat (ZMod 2) C)
    (M : BimoduleCategory (ZMod 2) B C) :
    ∃ (P : BimoduleCategory (ZMod 2) B C) (q : P ⟶ M),
      Bimodule.rightRelativeKFlat (ZMod 2) B C (BimoduleCategory.underlying (ZMod 2) B C P) ∧
        BimoduleCategory.quasiIso (ZMod 2) B C q :=
  exists_rightRelativeKFlat_bimodule_resolution (ZMod 2) B C hC M

#print axioms restrictModule_action
#print axioms representable_action
#print axioms moduleAction_units_smul
#print axioms tensorRightRestrictionInclusion_map
#print axioms restrictedRepresentable_action
#print axioms restrictedRepresentableIso
#print axioms restrictedRepresentableIso_hom_eval
#print axioms restrictedRepresentableIso_inv_eval
#print axioms tensorModuleAssociatorIso
#print axioms restrictModule_tensor
#print axioms moduleRestrictionTensorIso
#print axioms restrictedFreeIso
#print axioms restrictedFree_relativeKFlat
#print axioms restrictedSphere_relativeKFlat
#print axioms BimoduleSemifreeResolution.rightRelativeKFlat
#print axioms exists_rightRelativeKFlat_bimodule_resolution

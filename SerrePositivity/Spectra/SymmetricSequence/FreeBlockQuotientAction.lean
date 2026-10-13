module

public import SerrePositivity.Spectra.SymmetricSequence.FreeBlockQuotientMaps
public import SerrePositivity.Spectra.SymmetricSequence.FreeInductionAction

/-! # 明示的なブロック商の対称群作用

商の普遍性から構成した出力の射を対称群作用へまとめる。
各段および誘導図式との比較を作用付きの同型へ持ち上げる。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasColimitsOfSize.{0, 0} C]

/-- 明示的なブロック商上の、出力の対称群作用。 -/
def freeBlockQuotientAction (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    Action C (Equiv.Perm (Fin m)) where
  V := freeBlockQuotient F n X m
  ρ := {
    toFun σ := End.of (freeBlockQuotientOutputMap F n X m (FiniteBijection.permutation m σ))
    map_one' := by
      apply End.ext
      change freeBlockQuotientOutputMap F n X m (FiniteBijection.permutation m 1) = 𝟙 _
      rw [FiniteBijection.permutation_one, freeBlockQuotientOutputMap_id]
    map_mul' σ τ := by
      apply End.ext
      change freeBlockQuotientOutputMap F n X m (FiniteBijection.permutation m (σ * τ)) =
        freeBlockQuotientOutputMap F n X m (FiniteBijection.permutation m τ) ≫
          freeBlockQuotientOutputMap F n X m (FiniteBijection.permutation m σ)
      rw [FiniteBijection.permutation_mul, freeBlockQuotientOutputMap_comp] }

/-- 商の生成元に対する対称群作用は全単射の添字への後合成。 -/
@[reassoc] lemma freeBlockQuotientAction_generator (F : SymmetricSequence C)
    (n : ℕ) (X : C) (m : ℕ) (σ : Equiv.Perm (Fin m)) (h : FreeBlockIndex n m) :
    freeBlockQuotientGenerator F n X m h ≫ ((freeBlockQuotientAction F n X m).ρ σ).asHom =
      freeBlockQuotientGenerator F n X m (h ≫ FiniteBijection.permutation m σ) :=
  freeBlockQuotientGenerator_output F n X m (FiniteBijection.permutation m σ) h

/-- 商への入力の射は出力の対称群に関する同変射。 -/
def freeBlockQuotientActionMap (F : SymmetricSequence C) (n : ℕ) {X Y : C}
    (f : X ⟶ Y) (m : ℕ) : freeBlockQuotientAction F n X m ⟶ freeBlockQuotientAction F n Y m where
  hom := freeBlockQuotientInputMap F n f m
  comm σ := (freeBlockQuotientInputMap_output F n f m (FiniteBijection.permutation m σ)).symm

/-- 固定した出力次数における、作用付きブロック商の関手。 -/
def freeBlockQuotientActionFunctor (F : SymmetricSequence C) (n m : ℕ) :
    C ⥤ Action C (Equiv.Perm (Fin m)) where
  obj X := freeBlockQuotientAction F n X m
  map f := freeBlockQuotientActionMap F n f m
  map_id X := by
    apply Action.hom_ext
    exact freeBlockQuotientInputMap_id F n X m
  map_comp f g := by
    apply Action.hom_ext
    exact freeBlockQuotientInputMap_comp F n f g m

variable [MonoidalClosed C]

/-- 自由convolutionの各段と商との、出力の対称群作用を備えた比較同型。 -/
def freeConvolutionLevelActionIsoBlockQuotient (F : SymmetricSequence C) (n : ℕ) (X : C)
    (m : ℕ) : levelAction (convolution F ((freeAt n).obj X)) m ≅
      freeBlockQuotientAction F n X m :=
  Action.mkIso (freeConvolutionLevelIsoBlockQuotient F n X m)
    (fun σ => freeConvolutionLevelIsoBlockQuotient_output F n X m
      (FiniteBijection.permutation m σ))

/-- 商と誘導図式の余極限との、出力の対称群作用を備えた比較同型。 -/
def freeBlockQuotientActionIsoInduction (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    freeBlockQuotientAction F n X m ≅ freeInductionAction F n X m :=
  (freeConvolutionLevelActionIsoBlockQuotient F n X m).symm ≪≫
    freeConvolutionLevelActionIsoInduction F n X m

/-- 商と誘導図式との作用付き比較は、既存の基礎対象の比較を持ち上げたもの。 -/
lemma freeBlockQuotientActionIsoInduction_hom (F : SymmetricSequence C)
    (n : ℕ) (X : C) (m : ℕ) :
    (freeBlockQuotientActionIsoInduction F n X m).hom.hom =
      (freeBlockQuotientIsoInduction F n X m).hom := rfl

/-- 各段から商を経由した作用付き比較は、元の誘導表示への比較と一致する。 -/
lemma freeConvolutionLevelActionIsoBlockQuotient_trans (F : SymmetricSequence C)
    (n : ℕ) (X : C) (m : ℕ) :
    freeConvolutionLevelActionIsoBlockQuotient F n X m ≪≫
        freeBlockQuotientActionIsoInduction F n X m =
      freeConvolutionLevelActionIsoInduction F n X m := by
  apply Iso.ext
  simp only [freeBlockQuotientActionIsoInduction, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

/-- 商と誘導図式の作用付き比較は入力の射に関して自然。 -/
def freeBlockQuotientActionNatIsoInduction (F : SymmetricSequence C) (n m : ℕ) :
    freeBlockQuotientActionFunctor F n m ≅ freeInductionActionFunctor F n m :=
  NatIso.ofComponents (fun X => freeBlockQuotientActionIsoInduction F n X m) (by
    intro X Y f
    apply Action.hom_ext
    apply freeBlockQuotient_hom_ext
    intro h
    change freeBlockQuotientGenerator F n X m h ≫ freeBlockQuotientInputMap F n f m ≫
        (freeBlockQuotientIsoInduction F n Y m).hom =
      freeBlockQuotientGenerator F n X m h ≫ (freeBlockQuotientIsoInduction F n X m).hom ≫
        freeInductionInputMap F n f m
    rw [freeBlockQuotientGenerator_input_assoc,
      freeBlockQuotientIsoInduction_generator, freeBlockQuotientIsoInduction_generator_assoc]
    exact (freeInductionInputMap_inclusion F n f m
      (CostructuredArrow.mk (Y := FiniteBijection.of (m - n)) h)).symm)

end SerrePositivity.SymmetricSequence

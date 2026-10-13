module

public import SerrePositivity.Spectra.SymmetricSequence.FreePermutationQuotient
public import SerrePositivity.Spectra.SymmetricSequence.FreeBlockQuotientAction

/-! # 対称群で添字付けた誘導商の作用と自然性

出力の対称群は添字に左から掛け、入力の射は第二因子へ作用する。
全単射の商との比較を作用付き自然同型へ持ち上げる。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasColimitsOfSize.{0, 0} C]

/-- 出力の置換を添字への左乗法として誘導商へ降ろす。 -/
def freePermutationOutputMap (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (hm : n ≤ m) (κ : Equiv.Perm (Fin m)) :
    freePermutationQuotient F n X m hm ⟶ freePermutationQuotient F n X m hm :=
  freePermutationQuotientDesc F n X m hm
    (fun τ => freePermutationQuotientGenerator F n X m hm (κ * τ))
    (fun σ τ => by rw [freePermutationQuotientGenerator_relation, mul_assoc])

/-- 出力の置換は誘導商の生成元の添字に左から掛ける。 -/
@[reassoc (attr := simp)] lemma freePermutationQuotientGenerator_output
    (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) (hm : n ≤ m)
    (κ τ : Equiv.Perm (Fin m)) :
    freePermutationQuotientGenerator F n X m hm τ ≫ freePermutationOutputMap F n X m hm κ =
      freePermutationQuotientGenerator F n X m hm (κ * τ) :=
  freePermutationQuotientGenerator_desc F n X m hm _ _ τ

/-- 入力の射を第二因子へ作用させ、誘導商へ降ろす。 -/
def freePermutationInputMap (F : SymmetricSequence C) (n : ℕ) {X Y : C}
    (f : X ⟶ Y) (m : ℕ) (hm : n ≤ m) :
    freePermutationQuotient F n X m hm ⟶ freePermutationQuotient F n Y m hm :=
  freePermutationQuotientDesc F n X m hm
    (fun τ => F.obj (FiniteBijection.of (m - n)) ◁ f ≫
      freePermutationQuotientGenerator F n Y m hm τ)
    (fun σ τ => by rw [← whisker_exchange_assoc, freePermutationQuotientGenerator_relation])

/-- 入力の射は誘導商の生成元の第二因子へ作用する。 -/
@[reassoc (attr := simp)] lemma freePermutationQuotientGenerator_input
    (F : SymmetricSequence C) (n : ℕ) {X Y : C} (f : X ⟶ Y) (m : ℕ) (hm : n ≤ m)
    (τ : Equiv.Perm (Fin m)) :
    freePermutationQuotientGenerator F n X m hm τ ≫ freePermutationInputMap F n f m hm =
      F.obj (FiniteBijection.of (m - n)) ◁ f ≫ freePermutationQuotientGenerator F n Y m hm τ :=
  freePermutationQuotientGenerator_desc F n X m hm _ _ τ

/-- 対称群の左乗法から構成した、誘導商上の出力の作用。 -/
def freePermutationAction (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) (hm : n ≤ m) :
    Action C (Equiv.Perm (Fin m)) where
  V := freePermutationQuotient F n X m hm
  ρ := {
    toFun κ := End.of (freePermutationOutputMap F n X m hm κ)
    map_one' := by
      apply End.ext
      change freePermutationOutputMap F n X m hm 1 = 𝟙 _
      apply freePermutationQuotient_hom_ext
      intro τ
      simp only [freePermutationQuotientGenerator_output, one_mul, Category.comp_id]
    map_mul' κ κ' := by
      apply End.ext
      change freePermutationOutputMap F n X m hm (κ * κ') =
        freePermutationOutputMap F n X m hm κ' ≫ freePermutationOutputMap F n X m hm κ
      apply freePermutationQuotient_hom_ext
      intro τ
      simp only [freePermutationQuotientGenerator_output,
        freePermutationQuotientGenerator_output_assoc, mul_assoc] }

/-- 誘導商の入力の射は出力の対称群に関する同変射。 -/
def freePermutationActionMap (F : SymmetricSequence C) (n : ℕ) {X Y : C} (f : X ⟶ Y)
    (m : ℕ) (hm : n ≤ m) : freePermutationAction F n X m hm ⟶
      freePermutationAction F n Y m hm where
  hom := freePermutationInputMap F n f m hm
  comm κ := by
    change freePermutationOutputMap F n X m hm κ ≫ freePermutationInputMap F n f m hm =
      freePermutationInputMap F n f m hm ≫ freePermutationOutputMap F n Y m hm κ
    apply freePermutationQuotient_hom_ext
    intro τ
    simp only [freePermutationQuotientGenerator_output_assoc,
      freePermutationQuotientGenerator_input, freePermutationQuotientGenerator_input_assoc,
      freePermutationQuotientGenerator_output]

/-- 入力を同変射へ送る、対称群で添字付けた誘導商の関手。 -/
def freePermutationActionFunctor (F : SymmetricSequence C) (n m : ℕ) (hm : n ≤ m) :
    C ⥤ Action C (Equiv.Perm (Fin m)) where
  obj X := freePermutationAction F n X m hm
  map f := freePermutationActionMap F n f m hm
  map_id X := by
    apply Action.hom_ext
    change freePermutationInputMap F n (𝟙 X) m hm = 𝟙 _
    apply freePermutationQuotient_hom_ext
    intro τ
    simp only [freePermutationQuotientGenerator_input, whiskerLeft_id,
      Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply Action.hom_ext
    change freePermutationInputMap F n (f ≫ g) m hm =
      freePermutationInputMap F n f m hm ≫ freePermutationInputMap F n g m hm
    apply freePermutationQuotient_hom_ext
    intro τ
    simp only [freePermutationQuotientGenerator_input,
      freePermutationQuotientGenerator_input_assoc, whiskerLeft_comp, Category.assoc]

/-- 全単射の商から対称群の誘導商への、作用付き比較同型。 -/
def freeBlockActionIsoPermutation (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (hm : n ≤ m) : freeBlockQuotientAction F n X m ≅ freePermutationAction F n X m hm :=
  Action.mkIso (freeBlockQuotientIsoPermutation F n X m hm) (by
    intro κ
    apply freeBlockQuotient_hom_ext
    intro h
    change freeBlockQuotientGenerator F n X m h ≫
        freeBlockQuotientOutputMap F n X m (FiniteBijection.permutation m κ) ≫
          freeBlockToPermutationQuotient F n X m hm =
      freeBlockQuotientGenerator F n X m h ≫ freeBlockToPermutationQuotient F n X m hm ≫
        freePermutationOutputMap F n X m hm κ
    rw [freeBlockQuotientGenerator_output_assoc, freeBlockToPermutationQuotient_generator,
      freeBlockToPermutationQuotient_generator_assoc, freePermutationQuotientGenerator_output,
      freePermutationIndex_output])

/-- 全単射の商と対称群の誘導商との、作用付き自然同型。 -/
def freeBlockActionNatIsoPermutation (F : SymmetricSequence C) (n m : ℕ) (hm : n ≤ m) :
    freeBlockQuotientActionFunctor F n m ≅ freePermutationActionFunctor F n m hm :=
  NatIso.ofComponents (fun X => freeBlockActionIsoPermutation F n X m hm) (by
    intro X Y f
    apply Action.hom_ext
    apply freeBlockQuotient_hom_ext
    intro h
    change freeBlockQuotientGenerator F n X m h ≫ freeBlockQuotientInputMap F n f m ≫
        freeBlockToPermutationQuotient F n Y m hm =
      freeBlockQuotientGenerator F n X m h ≫ freeBlockToPermutationQuotient F n X m hm ≫
        freePermutationInputMap F n f m hm
    rw [freeBlockQuotientGenerator_input_assoc, freeBlockToPermutationQuotient_generator,
      freeBlockToPermutationQuotient_generator_assoc, freePermutationQuotientGenerator_input])

end SerrePositivity.SymmetricSequence

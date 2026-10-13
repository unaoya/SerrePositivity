module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInductionNaturality

/-! # 誘導図式の余極限上の対称群作用

全単射の添字への後合成を対称群作用へまとめる。
入力の射を同変射とし、自由convolutionの各段との比較を作用付き同型へ持ち上げる。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasColimitsOfSize.{0, 0} C]

/-- 誘導図式の余極限に、出力の対称群を添字への後合成で作用させる。 -/
def freeInductionAction (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    Action C (Equiv.Perm (Fin m)) where
  V := colimit (freeInductionDiagram F n X m)
  ρ := {
    toFun σ := End.of (freeInductionOutputMap F n X (FiniteBijection.permutation m σ))
    map_one' := by
      apply End.ext
      change freeInductionOutputMap F n X (FiniteBijection.permutation m 1) = 𝟙 _
      rw [FiniteBijection.permutation_one, freeInductionOutputMap_id]
    map_mul' σ τ := by
      apply End.ext
      change freeInductionOutputMap F n X (FiniteBijection.permutation m (σ * τ)) =
        freeInductionOutputMap F n X (FiniteBijection.permutation m τ) ≫
          freeInductionOutputMap F n X (FiniteBijection.permutation m σ)
      rw [FiniteBijection.permutation_mul, freeInductionOutputMap_comp] }

/-- 対称群の作用は標準包含の全単射の添字へ後合成する。 -/
@[reassoc] lemma freeInductionAction_inclusion (F : SymmetricSequence C) (n : ℕ) (X : C)
    (m : ℕ) (σ : Equiv.Perm (Fin m))
    (d : CostructuredArrow (FiniteBijection.addRight n) (FiniteBijection.of m)) :
    colimit.ι (freeInductionDiagram F n X m) d ≫
        ((freeInductionAction F n X m).ρ σ).asHom =
      colimit.ι (freeInductionDiagram F n X m)
        ((CostructuredArrow.map (FiniteBijection.permutation m σ)).obj d) :=
  freeInductionOutputMap_inclusion F n X (FiniteBijection.permutation m σ) d

/-- 誘導表示への入力の射は出力の対称群に関する同変射。 -/
def freeInductionActionMap (F : SymmetricSequence C) (n : ℕ) {X Y : C}
    (f : X ⟶ Y) (m : ℕ) : freeInductionAction F n X m ⟶ freeInductionAction F n Y m where
  hom := freeInductionInputMap F n f m
  comm σ := (freeInductionInputMap_output F n f (FiniteBijection.permutation m σ)).symm

/-- 固定した出力次数における、作用付き誘導表示の関手。 -/
def freeInductionActionFunctor (F : SymmetricSequence C) (n m : ℕ) :
    C ⥤ Action C (Equiv.Perm (Fin m)) where
  obj X := freeInductionAction F n X m
  map f := freeInductionActionMap F n f m
  map_id X := by
    apply Action.hom_ext
    exact freeInductionInputMap_id F n X m
  map_comp f g := by
    apply Action.hom_ext
    exact freeInductionInputMap_comp F n f g m

variable [MonoidalClosed C]

/-- 各段の誘導表示は出力の対称群作用を備えた同型である。 -/
def freeConvolutionLevelActionIsoInduction (F : SymmetricSequence C) (n : ℕ) (X : C)
    (m : ℕ) : levelAction (convolution F ((freeAt n).obj X)) m ≅
      freeInductionAction F n X m :=
  Action.mkIso (freeConvolutionLevelIsoInduction F n X m)
    (fun σ => freeConvolutionLevelIsoInduction_output F n X (FiniteBijection.permutation m σ))

/-- 入力の射に関する自然性も作用付き同型の基礎となる射について成立する。 -/
lemma freeConvolutionLevelActionIsoInduction_input (F : SymmetricSequence C) (n : ℕ)
    {X Y : C} (f : X ⟶ Y) (m : ℕ) :
    (freeConvolutionInputMap F n f).app (FiniteBijection.of m) ≫
        (freeConvolutionLevelActionIsoInduction F n Y m).hom.hom =
      (freeConvolutionLevelActionIsoInduction F n X m).hom.hom ≫
        (freeInductionActionMap F n f m).hom :=
  freeConvolutionLevelIsoInduction_input F n f m

end SerrePositivity.SymmetricSequence

module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeProRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofCellRefinement

/-!
概要：元の pro 逆を、cell 細分後の厳密な左持ち上げと実右経路を持つ roof で表す。
方針：元の有限 cell augmentation と両三角形の実代数射を全てデータに保持する。
規約：実証人を構成した場合だけ提供する性質。使われ方：高次切断の実底変更。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {X Y : Tower (Mon (Complex R))}

structure CellNativeInverseRoof (f : LevelHom X Y) (i m : ℕ) (hi : i ≤ m) where
  roof : SurjectiveRoof R (Y.obj m) (X.obj i)
  sourceDepth : ℕ
  sourceLift : iteratedCellResolution R (X.obj m) sourceDepth ⟶ roof.apex
  source_denominator : sourceLift ≫ roof.denominator =
    iteratedCellAugmentation R (X.obj m) sourceDepth ≫ f.app m
  source_numerator : sourceLift ≫ roof.numerator =
    iteratedCellAugmentation R (X.obj m) sourceDepth ≫ X.transition hi
  rightPath : Path.Witness R (roof.numerator ≫ f.app i) (roof.denominator ≫ Y.transition hi)

def HasCellNativeRoofProInverse (f : LevelHom X Y) : Prop :=
  ∀ i, ∃ m, ∃ hi : i ≤ m, Nonempty (CellNativeInverseRoof R f i m hi)

lemma HasNativeRoofProInverse.cellNative {f : LevelHom X Y} (h : HasNativeRoofProInverse R f) :
    HasCellNativeRoofProInverse R f := by
  intro i
  obtain ⟨m, hi, r, a, ha, ah, ⟨w⟩⟩ := h i
  refine ⟨m, hi, ⟨⟨r, 0, a, ?_, ?_, w⟩⟩⟩
  · exact ha.trans (Category.id_comp _).symm
  · exact ah.trans (Category.id_comp _).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellNativeProRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofConjugationLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofConjugationPath

/-!
概要：準同型正方形に沿って、元の実三角形付き roof の pro 逆を反映する。
方針：元の左持ち上げ・MappingPath・右経路を実 pullback と有限 cell 細分で移送する。
規約：反転関手での等式を実経路に置き換えない。使われ方：元の有限切断の底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {X Y X' Y' : Tower (Mon (Complex R))}
  (f : LevelHom X Y) (g : LevelHom X' Y') (a : LevelHom X X') (b : LevelHom Y Y')
  (hs : f.comp b = a.comp g)
  (ha : ∀ i, QuasiIso (a.app i).hom) (hb : ∀ i, QuasiIso (b.app i).hom)

/-- 左は三重 cell 後の厳密持ち上げ、右は元の実乗法的経路として移送する。 -/
def CellNativeInverseRoof.reflect {i m : ℕ} (hi : i ≤ m)
    (c : CellNativeInverseRoof R g i m hi) : CellNativeInverseRoof R f i m hi := by
  have hs' (j : ℕ) : f.app j ≫ b.app j = a.app j ≫ g.app j :=
    congrArg (fun t => t.app j) hs
  let t := RoofConjugation.roof R c.roof (b.app m) (a.app i) (ha i)
  let t₁ := t.cellRefinement R 1
  let t₂ := t₁.cellRefinement R 4
  let u := cellResolutionMapLift R (a.app m)
    (iteratedCellAugmentation R (X'.obj m) c.sourceDepth)
    (iteratedCellAugmentation_surjective R (X'.obj m) c.sourceDepth)
    (iteratedCellAugmentation_quasiIso R (X'.obj m) c.sourceDepth)
  have hu : u ≫ iteratedCellAugmentation R (X'.obj m) c.sourceDepth =
      cellAugmentation R (X.obj m) ≫ a.app m := cellResolutionMapLift_projection R _ _ _ _
  let l := u ≫ c.sourceLift
  let z := cellAugmentation R (X.obj m) ≫ f.app m
  let x := cellAugmentation R (X.obj m) ≫ X.transition hi
  have hl : l ≫ c.roof.denominator = z ≫ b.app m := by
    change (u ≫ c.sourceLift) ≫ c.roof.denominator = _
    rw [Category.assoc, c.source_denominator, ← Category.assoc, hu, Category.assoc,
      ← hs', ← Category.assoc]
  have hx : l ≫ c.roof.numerator = x ≫ a.app i := by
    change (u ≫ c.sourceLift) ≫ c.roof.numerator = _
    rw [Category.assoc, c.source_numerator, ← Category.assoc, hu, Category.assoc,
      ← a.naturality hi, ← Category.assoc]
  let l₀ := RoofConjugation.lift R c.roof (b.app m) (a.app i) (ha i) l z x hl hx
  have h₀ : l₀ ≫ t.denominator = z :=
    RoofConjugation.lift_denominator R _ _ _ _ _ _ _ _ _
  have h₁ : l₀ ≫ t.numerator = x :=
    RoofConjugation.lift_numerator R _ _ _ _ _ _ _ _ _
  let l₁ := t.cellRefinementLift R 1 l₀
  let l₂ := t₁.cellRefinementLift R 4 l₁
  let w := RoofConjugation.rightPathAfterComparison R c.roof (b.app m) (a.app i) (ha i)
    (f.app i) (g.app i) (b.app i) (Y.transition hi) (Y'.transition hi) (hs' i)
    (b.naturality hi).symm c.rightPath
  refine ⟨t₂, 3, l₂, ?_, ?_, ?_⟩
  · have he : l₂ ≫ t₂.denominator =
        cellAugmentation R (cellResolution R (cellResolution R (X.obj m))) ≫
          cellAugmentation R (cellResolution R (X.obj m)) ≫ z := by
      rw [SurjectiveRoof.cellRefinementLift_denominator,
        SurjectiveRoof.cellRefinementLift_denominator, h₀]
    simpa only [z, iteratedCellAugmentation, iteratedCellResolution, Category.assoc,
      Category.id_comp, Category.comp_id] using he
  · have he : l₂ ≫ t₂.numerator =
        cellAugmentation R (cellResolution R (cellResolution R (X.obj m))) ≫
          cellAugmentation R (cellResolution R (X.obj m)) ≫ x := by
      rw [SurjectiveRoof.cellRefinementLift_numerator,
        SurjectiveRoof.cellRefinementLift_numerator, h₁]
    simpa only [x, iteratedCellAugmentation, iteratedCellResolution, Category.assoc,
      Category.id_comp, Category.comp_id] using he
  · exact t₁.cellReflectEquation R (f.app i) (Y.transition hi) (b.app i) (hb i) w

include a b hs ha hb in
lemma HasCellNativeRoofProInverse.of_square (hg : HasCellNativeRoofProInverse R g) :
    HasCellNativeRoofProInverse R f := by
  intro i
  obtain ⟨m, hi, ⟨c⟩⟩ := hg i
  exact ⟨m, hi, ⟨c.reflect R f g a b hs ha hb hi⟩⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

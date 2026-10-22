module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellNativeProRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveRoof

/-!
概要：元の実三角形付き逆を、頂点も左細分の源も非正次数の実代数として保持する。
方針：同じ cover 関手で元の左持ち上げを移し、元の右経路は包含で前合成する。
規約：二つの分母の次数全射準同型性を実証する。使われ方：高次 class の底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {X Y : Tower (Mon (Complex R))}

structure NonpositiveInverseRoof (f : LevelHom X Y) (i m : ℕ) (hi : i ≤ m) where
  roof : SurjectiveRoof R (Y.obj m) (X.obj i)
  roof_nonpositive : roof.apex.X.IsStrictlyLE 0
  source : Mon (Complex R)
  source_nonpositive : source.X.IsStrictlyLE 0
  sourceProjection : source ⟶ X.obj m
  sourceProjection_epi : Epi sourceProjection.hom
  sourceProjection_quasiIso : QuasiIso sourceProjection.hom
  sourceLift : source ⟶ roof.apex
  source_denominator : sourceLift ≫ roof.denominator = sourceProjection ≫ f.app m
  source_numerator : sourceLift ≫ roof.numerator = sourceProjection ≫ X.transition hi
  rightPath : Path.Witness R (roof.numerator ≫ f.app i) (roof.denominator ≫ Y.transition hi)

variable {f : LevelHom X Y} {i m : ℕ} {hi : i ≤ m}
  [(X.obj m).X.IsStrictlyLE 0] [(Y.obj m).X.IsStrictlyLE 0]
  (c : CellNativeInverseRoof R f i m hi)

/-- 元の両三角形・射を保つ、非正次数の実 roof と非正次数の実左細分。 -/
def CellNativeInverseRoof.nonpositive : NonpositiveInverseRoof R f i m hi := by
  let Q := iteratedCellResolution R (X.obj m) c.sourceDepth
  let e := iteratedCellAugmentation R (X.obj m) c.sourceDepth
  let S := connectiveCover R Q
  let s := connectiveCoverInclusion R Q ≫ e
  let t := c.roof.nonpositiveNormalization R
  let l := connectiveCoverMap R c.sourceLift
  have hl : l ≫ connectiveCoverInclusion R c.roof.apex =
      connectiveCoverInclusion R Q ≫ c.sourceLift :=
    (connectiveCoverCounit R).naturality c.sourceLift
  refine ⟨t, c.roof.nonpositiveNormalization_apex R, S, coverComplex_nonpositive R Q,
    s, ?_, ?_, l, ?_, ?_, ?_⟩
  · have := iteratedCellAugmentation_epi R (X.obj m) c.sourceDepth
    apply epi_of_epi_f
    intro n
    apply (ModuleCat.epi_iff_surjective _).2
    exact connectiveCoverInclusion_comp_surjective R e
      (fun j => (ModuleCat.epi_iff_surjective _).1 inferInstance)
      (iteratedCellAugmentation_quasiIso R (X.obj m) c.sourceDepth) n
  · exact connectiveCoverInclusion_comp_quasiIso R e
      (iteratedCellAugmentation_quasiIso R (X.obj m) c.sourceDepth)
  · change l ≫ (connectiveCoverInclusion R c.roof.apex ≫ c.roof.denominator) = _
    rw [← Category.assoc, hl, Category.assoc, c.source_denominator, ← Category.assoc]
  · change l ≫ (connectiveCoverInclusion R c.roof.apex ≫ c.roof.numerator) = _
    rw [← Category.assoc, hl, Category.assoc, c.source_numerator, ← Category.assoc]
  · let w := c.rightPath.precomp (connectiveCoverInclusion R c.roof.apex)
    exact { hom := w.hom
            source_eq := by
              simpa only [t, SurjectiveRoof.nonpositiveNormalization, Category.assoc]
                using w.source_eq
            target_eq := by
              simpa only [t, SurjectiveRoof.nonpositiveNormalization, Category.assoc]
                using w.target_eq }

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

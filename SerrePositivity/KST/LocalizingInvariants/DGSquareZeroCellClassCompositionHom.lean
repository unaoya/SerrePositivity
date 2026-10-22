module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeComposedClassEvaluation
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassPath

/-!
概要：cell 合成の指定持ち上げから、class の実二重経路と四辺・全底射影を構成する。
方針：普遍 class 合成で cellCompLift の全経路を写し、元の二評価を計算する。
規約：二重経路の存在を追加仮定にしない。使われ方：cell と affine の合成比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
open DGAlgebra
variable (R : Type u) [CommRing R] {W C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) {f g h : W ⟶ C}
  (v : DGAlgebra.Path.Witness R f g) (w : DGAlgebra.Path.Witness R g h)
  (hv : v.hom ≫ DGAlgebra.Path.map R p = (f ≫ p) ≫ DGAlgebra.Path.diagonal R B)
  (hw : w.hom ≫ DGAlgebra.Path.map R p = (g ≫ p) ≫ DGAlgebra.Path.diagonal R B)

lemma classCellCompLift_source_fixed : (RelativePath.cellCompLift R p hs v w hv hw).hom ≫
    DGAlgebra.Path.map R (RelativeComposedPath.source R p) =
      (cellAugmentation R W ≫ f) ≫ DGAlgebra.Path.diagonal R C := by
  have he := RelativePath.cellPathWitness_relative R (RelativeComposedPath.source R p)
    (RelativeComposedPath.source_surjective R p) (RelativeComposedPath.source_quasiIso R p hs)
    (f ≫ RelativeComposedPath.diagonal R p) (RelativeComposedPath.lift R p v w hv hw)
    (RelativePath.cellCompLift_condition R p v w hv hw)
  simpa only [RelativePath.cellCompLift, Category.assoc,
    RelativeComposedPath.diagonal_source, Category.comp_id] using he

variable (N : Bimod B B) (κ : C ⟶ algebra B N) (hκ : κ ≫ projection B N = p)

lemma relativeClassComposition_lift : RelativeComposedPath.lift R p v w hv hw ≫
    (RelativeComposedPath.classComposition R p N κ hκ).hom =
      (relativeClassComposite R p v hv N κ hκ w hw).hom := by
  apply Mon.Hom.ext
  change (RelativeComposedPath.lift R p v w hv hw ≫
    (RelativeComposedPath.classComposition R p N κ hκ).hom).hom =
    ((relativeClassWitness R p v hv N κ hκ).comp
      (relativeClassSecond R p v hv N κ hκ w hw)).hom.hom
  rw [RelativeComposedPath.classComposition_lift_hom, RelativeWitness.comp_hom_linear]
  change (v.hom ≫ DGAlgebra.Path.map R κ).hom -
      (g ≫ κ ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom +
        (w.hom ≫ DGAlgebra.Path.map R κ).hom =
    (v.hom ≫ DGAlgebra.Path.map R κ).hom -
      ((g ≫ κ) ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom +
        (w.hom ≫ DGAlgebra.Path.map R κ).hom
  rw [Category.assoc]

def cellClassCompositionHom : cellResolution R W ⟶
    DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)) :=
  (RelativePath.cellCompLift R p hs v w hv hw).hom ≫
    DGAlgebra.Path.map R (RelativeComposedPath.classComposition R p N κ hκ).hom

lemma cellClassCompositionHom_source : cellClassCompositionHom R p hs v w hv hw N κ hκ ≫
    DGAlgebra.Path.source R (DGAlgebra.Path.algebra R (algebra B N)) =
      ((cellAugmentation R W ≫ f) ≫ κ) ≫ DGAlgebra.Path.diagonal R (algebra B N) := by
  rw [cellClassCompositionHom, Category.assoc, DGAlgebra.Path.map_source, ← Category.assoc,
    (RelativePath.cellCompLift R p hs v w hv hw).source_eq]
  simp only [Category.assoc, RelativeComposedPath.classComposition_diagonal R p N κ hκ]

lemma cellClassCompositionHom_target : cellClassCompositionHom R p hs v w hv hw N κ hκ ≫
    DGAlgebra.Path.target R (DGAlgebra.Path.algebra R (algebra B N)) =
      (relativeClassAffineRefined R p v hv N κ hκ w hw).hom := by
  rw [cellClassCompositionHom, Category.assoc, DGAlgebra.Path.map_target, ← Category.assoc,
    (RelativePath.cellCompLift R p hs v w hv hw).target_eq]
  rw [Category.assoc, relativeClassComposition_lift]
  rfl

lemma cellClassCompositionHom_source_trace : cellClassCompositionHom R p hs v w hv hw N κ hκ ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.source R (algebra B N)) =
      ((cellAugmentation R W ≫ f) ≫ κ) ≫ DGAlgebra.Path.diagonal R (algebra B N) := by
  rw [cellClassCompositionHom, Category.assoc, ← DGAlgebra.Path.map_comp,
    (RelativeComposedPath.classComposition R p N κ hκ).source_eq, DGAlgebra.Path.map_comp,
    ← Category.assoc, classCellCompLift_source_fixed, Category.assoc,
    DGAlgebra.Path.diagonal_naturality, ← Category.assoc]

lemma cellClassCompositionHom_target_trace : cellClassCompositionHom R p hs v w hv hw N κ hκ ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.target R (algebra B N)) =
      (relativeClassCellComposite R p v hv N κ hκ w hw hs).hom := by
  rw [cellClassCompositionHom, Category.assoc, ← DGAlgebra.Path.map_comp,
    (RelativeComposedPath.classComposition R p N κ hκ).target_eq, DGAlgebra.Path.map_comp,
    ← Category.assoc]
  rfl

lemma cellClassCompositionHom_projection : cellClassCompositionHom R p hs v w hv hw N κ hκ ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
      (((cellAugmentation R W ≫ f) ≫ p) ≫ DGAlgebra.Path.diagonal R B) ≫
        DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R B) := by
  rw [cellClassCompositionHom, Category.assoc, ← DGAlgebra.Path.map_comp,
    (RelativeComposedPath.classComposition R p N κ hκ).projection_eq,
    DGAlgebra.Path.map_comp, DGAlgebra.Path.map_comp, ← Category.assoc, ← Category.assoc,
    classCellCompLift_source_fixed]
  simp only [Category.assoc, reassoc_of% (DGAlgebra.Path.diagonal_naturality R p),
    DGAlgebra.Path.diagonal_naturality R (DGAlgebra.Path.diagonal R B)]

end SerrePositivity.KST.LocalizingInvariants.SquareZero

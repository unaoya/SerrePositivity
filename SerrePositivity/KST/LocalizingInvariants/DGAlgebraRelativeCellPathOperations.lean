module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeComposedPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeCellPathLift

/-!
概要：元の底を固定する経路の反転と合成を、明示した cell 細分の後で構成する。
方針：相対経路・相対二経路の source の全射準同型性で持ち上げる。
規約：底射の次数全射性だけを要求する。使われ方：Postnikov 自然性の経路合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
variable (R : Type u) [CommRing R] {W C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n))
  {f g h : W ⟶ C} (v : Path.Witness R f g) (w : Path.Witness R g h)
  (hv : v.hom ≫ Path.map R p = (f ≫ p) ≫ Path.diagonal R B)
  (hw : w.hom ≫ Path.map R p = (g ≫ p) ≫ Path.diagonal R B)

lemma cellCompLift_condition : (f ≫ RelativeComposedPath.diagonal R p) ≫
    RelativeComposedPath.source R p =
      RelativeComposedPath.lift R p v w hv hw ≫ RelativeComposedPath.source R p := by
  rw [Category.assoc, RelativeComposedPath.diagonal_source, Category.comp_id,
    RelativeComposedPath.lift_source]

def cellCompLift : Path.Witness R
    (cellAugmentation R W ≫ (f ≫ RelativeComposedPath.diagonal R p))
    (cellAugmentation R W ≫ RelativeComposedPath.lift R p v w hv hw) :=
  cellPathWitness R (RelativeComposedPath.source R p)
    (RelativeComposedPath.source_surjective R p) (RelativeComposedPath.source_quasiIso R p hs)
    (f ≫ RelativeComposedPath.diagonal R p) (RelativeComposedPath.lift R p v w hv hw)
    (cellCompLift_condition R p v w hv hw)

def cellComp : Path.Witness R (cellAugmentation R W ≫ f) (cellAugmentation R W ≫ h) where
  hom := (cellCompLift R p hs v w hv hw).hom ≫ Path.map R (RelativeComposedPath.target R p)
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (cellCompLift R p hs v w hv hw).source_eq, Category.assoc, Category.assoc,
      RelativeComposedPath.diagonal_target, Category.comp_id]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (cellCompLift R p hs v w hv hw).target_eq, Category.assoc,
      RelativeComposedPath.lift_target]

lemma cellComp_relative : (cellComp R p hs v w hv hw).hom ≫ Path.map R p =
    ((cellAugmentation R W ≫ f) ≫ p) ≫ Path.diagonal R B := by
  change ((cellCompLift R p hs v w hv hw).hom ≫
    Path.map R (RelativeComposedPath.target R p)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, RelativeComposedPath.target_base,
    Path.map_comp, ← Category.assoc]
  rw [cellCompLift, cellPathWitness_relative]
  rw [Category.assoc f, RelativeComposedPath.diagonal_source, Category.comp_id]
  rw [Category.assoc, Path.diagonal_naturality]
  simp only [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath

module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathProjection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathSurjective

/-!
概要：実可換正方形を mapping-path 因子分解の実代数射へ送る。
方針：経路関手の自然性と元の正方形を、実代数 pullback の普遍性へ渡す。
規約：対象の選択だけの対応にしない。使われ方：塔と cospan の因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.MappingPath
variable (R : Type u) [CommRing R] {A B A' B' : Mon (Complex R)}
  (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') (w : f ≫ b = a ≫ f')

include w in
lemma map_comm :
    (inclusion R f ≫ Path.map R b) ≫ Path.source R B' = (projection R f ≫ a) ≫ f' := by
  rw [Category.assoc, Path.map_source, ← Category.assoc, condition,
    Category.assoc, w, ← Category.assoc]

def map : algebra R f ⟶ algebra R f' :=
  MonoidPullback.lift (Path.source R B') f' (inclusion R f ≫ Path.map R b)
    (projection R f ≫ a) (map_comm R f f' a b w)

@[reassoc]
lemma map_inclusion : map R f f' a b w ≫ inclusion R f' = inclusion R f ≫ Path.map R b :=
  MonoidPullback.lift_fst _ _ _ _ _

@[reassoc]
lemma map_projection : map R f f' a b w ≫ projection R f' = projection R f ≫ a :=
  MonoidPullback.lift_snd _ _ _ _ _

@[reassoc]
lemma map_target : map R f f' a b w ≫ target R f' = target R f ≫ b := by
  change map R f f' a b w ≫ (inclusion R f' ≫ Path.target R B') =
    (inclusion R f ≫ Path.target R B) ≫ b
  rw [← Category.assoc, map_inclusion, Category.assoc, Path.map_target, ← Category.assoc]

lemma section_map : section_ R f ≫ map R f f' a b w = a ≫ section_ R f' := by
  apply MonoidPullback.hom_ext (Path.source R B') f'
  · change (section_ R f ≫ map R f f' a b w) ≫ inclusion R f' =
      (a ≫ section_ R f') ≫ inclusion R f'
    rw [Category.assoc, map_inclusion, ← Category.assoc, section_inclusion,
      Category.assoc, Path.diagonal_naturality, ← Category.assoc, w,
      Category.assoc, Category.assoc, section_inclusion]
  · change (section_ R f ≫ map R f f' a b w) ≫ projection R f' =
      (a ≫ section_ R f') ≫ projection R f'
    rw [Category.assoc, map_projection, ← Category.assoc, section_projection,
      Category.id_comp, Category.assoc, section_projection, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.MappingPath

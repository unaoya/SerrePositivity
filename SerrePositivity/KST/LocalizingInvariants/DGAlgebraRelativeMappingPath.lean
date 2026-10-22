module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePath

/-!
概要：底の射 p の上で定数の経路を使い、実代数射 a の相対 mapping-path を構成する。
方針：相対 source の底変更と、元の相対 target を用いる。
規約：元の底射と両脚を保持。使われ方：底を固定した class 拡大模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeMappingPath
variable (R : Type u) [CommRing R] {C B W : Mon (Complex R)} (p : C ⟶ B) (a : W ⟶ C)

def algebra : Mon (Complex R) := MonoidPullback.obj (RelativePath.source R p) a

def inclusion : algebra R p a ⟶ RelativePath.algebra R p :=
  MonoidPullback.fst (RelativePath.source R p) a

def projection : algebra R p a ⟶ W := MonoidPullback.snd (RelativePath.source R p) a

lemma condition : inclusion R p a ≫ RelativePath.source R p = projection R p a ≫ a :=
  MonoidPullback.condition _ _

def target : algebra R p a ⟶ C := inclusion R p a ≫ RelativePath.target R p

lemma target_base : target R p a ≫ p = projection R p a ≫ a ≫ p := by
  rw [target, Category.assoc, RelativePath.target_projection, ← RelativePath.source_projection,
    ← Category.assoc, condition, Category.assoc]

def section_ : W ⟶ algebra R p a :=
  MonoidPullback.lift (RelativePath.source R p) a (a ≫ RelativePath.diagonal R p) (𝟙 W)
    (by rw [Category.assoc, RelativePath.diagonal_source, Category.comp_id, Category.id_comp])

lemma section_projection : section_ R p a ≫ projection R p a = 𝟙 W :=
  MonoidPullback.lift_snd _ _ _ _ _

lemma section_target : section_ R p a ≫ target R p a = a := by
  rw [section_, target, inclusion, ← Category.assoc, MonoidPullback.lift_fst, Category.assoc,
    RelativePath.diagonal_target, Category.comp_id]

def comparison : algebra R p a ⟶ MappingPath.algebra R a :=
  MappingPath.lift R a (inclusion R p a ≫ RelativePath.inclusion R p) (projection R p a)
    (by rw [Category.assoc]; exact condition R p a)

lemma comparison_projection : comparison R p a ≫ MappingPath.projection R a = projection R p a :=
  MappingPath.lift_projection R _ _ _ _

lemma comparison_target : comparison R p a ≫ MappingPath.target R a = target R p a := by
  rw [comparison, MappingPath.lift_target]
  exact Category.assoc _ _ _

lemma comparison_inclusion : comparison R p a ≫ MappingPath.inclusion R a =
    inclusion R p a ≫ RelativePath.inclusion R p := MappingPath.lift_inclusion R _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeMappingPath

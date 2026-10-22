module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeMappingPathSurjective
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPullbackMapQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathSurjective

/-!
概要：底の経路を固定する相対 cospan 模型と、元の絶対経路模型への比較を構成する。
方針：相対 mapping-path の target を底変更し、元の三成分の比較を使う。
規約：比較の準同型性は p と a≫p の次数全射性から導く。使われ方：相対 class 拡大。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeHomotopyPullback
variable (R : Type u) [CommRing R] {C B W D : Mon (Complex R)}
  (p : C ⟶ B) (a : W ⟶ C) (g : D ⟶ C)

def algebra : Mon (Complex R) := MonoidPullback.obj (RelativeMappingPath.target R p a) g

def left : algebra R p a g ⟶ W :=
  MonoidPullback.fst (RelativeMappingPath.target R p a) g ≫ RelativeMappingPath.projection R p a

def right : algebra R p a g ⟶ D := MonoidPullback.snd (RelativeMappingPath.target R p a) g

def path : algebra R p a g ⟶ Path.algebra R C :=
  MonoidPullback.fst (RelativeMappingPath.target R p a) g ≫
    RelativeMappingPath.inclusion R p a ≫ RelativePath.inclusion R p

def comparison : algebra R p a g ⟶ HomotopyPullbackModel.algebra R a g :=
  PullbackMap.map R (RelativeMappingPath.target R p a) g (MappingPath.target R a) g
    (RelativeMappingPath.comparison R p a) (𝟙 C) (𝟙 D)
    ((RelativeMappingPath.comparison_target R p a).trans (Category.comp_id _).symm) (by simp)

lemma comparison_left : comparison R p a g ≫ HomotopyPullbackModel.left R a g = left R p a g := by
  change comparison R p a g ≫
    (MonoidPullback.fst (MappingPath.target R a) g ≫ MappingPath.projection R a) = _
  rw [← Category.assoc, comparison, PullbackMap.map_fst, Category.assoc,
    RelativeMappingPath.comparison_projection]
  rfl

lemma comparison_right :
    comparison R p a g ≫ HomotopyPullbackModel.right R a g = right R p a g := by
  change comparison R p a g ≫ MonoidPullback.snd _ _ = _
  rw [comparison, PullbackMap.map_snd, Category.comp_id]
  rfl

lemma comparison_path : comparison R p a g ≫ HomotopyPullbackModel.path R a g = path R p a g := by
  change comparison R p a g ≫
    (MonoidPullback.fst (MappingPath.target R a) g ≫ MappingPath.inclusion R a) = _
  rw [← Category.assoc, comparison, PullbackMap.map_fst, Category.assoc,
    RelativeMappingPath.comparison_inclusion]
  rfl

lemma path_source : path R p a g ≫ Path.source R C = left R p a g ≫ a := by
  rw [← comparison_path, Category.assoc, HomotopyPullbackModel.path_source,
    ← Category.assoc, comparison_left]

lemma path_target : path R p a g ≫ Path.target R C = right R p a g ≫ g := by
  rw [← comparison_path, Category.assoc, HomotopyPullbackModel.path_target,
    ← Category.assoc, comparison_right]

lemma path_base : path R p a g ≫ Path.map R p = left R p a g ≫ a ≫ p ≫ Path.diagonal R B := by
  have hm : RelativeMappingPath.inclusion R p a ≫ RelativePath.projection R p =
      RelativeMappingPath.projection R p a ≫ a ≫ p := by
    rw [← RelativePath.source_projection, ← Category.assoc, RelativeMappingPath.condition,
      Category.assoc]
  rw [path, Category.assoc, Category.assoc, RelativePath.condition,
    ← Category.assoc (RelativeMappingPath.inclusion R p a), hm]
  simp only [left, Category.assoc]

lemma right_base : right R p a g ≫ g ≫ p = left R p a g ≫ a ≫ p := by
  have hc := congrArg (fun t => t ≫ p)
    (MonoidPullback.condition (RelativeMappingPath.target R p a) g)
  rw [Category.assoc, RelativeMappingPath.target_base] at hc
  simpa only [left, right, Category.assoc] using hc.symm

lemma comparison_quasiIso
    (hp : ∀ n : ℤ, Function.Surjective (p.hom.f n))
    (hq : ∀ n : ℤ, Function.Surjective ((a ≫ p).hom.f n)) :
    QuasiIso (comparison R p a g).hom := by
  have := RelativeMappingPath.target_epi R p a hq
  have := MappingPath.target_epi R a
  exact PullbackMap.map_quasiIso R _ _ _ _ _ _ _ _ _
    (RelativeMappingPath.comparison_quasiIso R p a hp) (quasiIso_of_isIso _) (quasiIso_of_isIso _)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeHomotopyPullback

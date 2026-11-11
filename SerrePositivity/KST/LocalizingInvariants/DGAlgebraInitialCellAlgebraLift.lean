module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellStages
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInitialCellLift

/-!
概要：自由な初期 cell 段の実 dg 代数を、全射準同型な代数射を通って持ち上げる。
方針：検証済み初期 dg 関手を唯一の自己準同型へ戻し、元の増大との合成を保持する。
規約：後続 cell の持ち上げは別工程。使われ方：代数 cell 分解の持ち上げの帰納法。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)

def initialCellAlgebraLift : cellStage R B 0 ⟶ C := by
  let F := initialCellLiftFunctor R p hs hq
  exact Mon.Hom.mk' (F.map .star .star) (F.map_id .star) (F.map_comp .star .star .star)

lemma initialCellAlgebraLift_projection :
    initialCellAlgebraLift R p hs hq ≫ p = cellStageAugmentation R B 0 := by
  apply Mon.Hom.ext
  exact congrArg (fun F : DGFunctor R
      (DGCategoryCycleCover.Source R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint R B) ↦
      (show (cellStage R B 0).X ⟶ B.X from F.map .star .star))
    (initialCellLift_augmentation R p hs hq)

include hs hq in
lemma cellStage_relative_primitive_lift (n : ℕ) (g : cellStage R B n ⟶ C)
    (hg : g ≫ p = cellStageAugmentation R B n)
    (c : ComplexBoundaryCell R (cellStageAugmentation R B n).hom) :
    ∃ t : C.X.X c.degree,
      C.X.d c.degree (c.degree + 1) t = g.hom.f (c.degree + 1) c.cycle.val ∧
        p.hom.f c.degree t = c.primitive :=
  cochain_relative_primitive_lift p.hom hs hq g.hom (cellStageAugmentation R B n).hom
    (congrArg Mon.Hom.hom hg) c

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

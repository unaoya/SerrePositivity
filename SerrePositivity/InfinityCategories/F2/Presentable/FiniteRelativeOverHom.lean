module

public import SerrePositivity.InfinityCategories.F2.Presentable.RelativeOverHom
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
概要：有限な始域を持つ底上の相対 Hom は、通常の filtered 余極限を保つ。
方針：全次数で底上の有限表示対象からの Hom と自然同型にし、評価で保存性を判定する。
規約：底への元の射と全ての次数の作用を保持する。標的の充填性は不要。
使われ方：前層の有限底上模型の compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 相対 Hom の各次数は、底上の元のパラメータ付き始域からの Hom と自然に同型。 -/
def relativeOverHomEvaluationIso {B : SSet.{u}} (A : Over B) (n : SimplexCategoryᵒᵖ) :
    relativeOverHomFunctor A ⋙ (evaluation _ _).obj n ≅
      coyoneda.obj (Opposite.op (overTensorParameter A (stdSimplex.obj n.unop))) :=
  NatIso.ofComponents (fun X ↦ Equiv.toIso
    (SSet.yonedaEquiv.symm.trans (relativeOverHomTensorEquiv A X (stdSimplex.obj n.unop)))) (by
      intro X Y f
      apply ConcreteCategory.hom_ext
      intro x
      change relativeOverHomTensorEquiv A Y _
        (SSet.yonedaEquiv.symm (((relativeOverHomFunctor A).map f).app n x)) =
          relativeOverHomTensorEquiv A X _ (SSet.yonedaEquiv.symm x) ≫ f
      rw [← SSet.yonedaEquiv_symm_comp]
      exact relativeOverHomTensorEquiv_naturality A _ f _)

instance overTensorParameter_finite {B : SSet.{u}} (A : Over B) [A.left.Finite]
    (n : SimplexCategoryᵒᵖ) : (overTensorParameter A (stdSimplex.obj n.unop)).left.Finite := by
  change (A.left ⊗ stdSimplex.obj n.unop).Finite
  infer_instance

/-- 有限始域の元の相対 Hom 関手は、小さい filtered 余極限を保存する。 -/
instance finiteRelativeOverHom_preservesFilteredColimits {B : SSet.{u}} (A : Over B)
    [A.left.Finite] : PreservesFilteredColimitsOfSize.{u, u} (relativeOverHomFunctor A) where
  preserves_filtered_colimits J _ _ := by
    apply preservesColimitsOfShape_of_evaluation
    intro n
    have : IsFinitelyPresentable.{u} (overTensorParameter A (stdSimplex.obj n.unop)) :=
      finiteOver_isFinitelyPresentable (overTensorParameter A (stdSimplex.obj n.unop)).hom
    have : PreservesColimitsOfShape J
        (coyoneda.obj (Opposite.op (overTensorParameter A (stdSimplex.obj n.unop)))) :=
      inferInstance
    exact preservesColimitsOfShape_of_natIso (relativeOverHomEvaluationIso A n).symm

end SerrePositivity.InfinityCategories.F2.Presentable

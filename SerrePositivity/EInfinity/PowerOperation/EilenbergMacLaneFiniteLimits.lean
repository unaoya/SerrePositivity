module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaPairNaturality
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedHomTargetNaturality
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# 同じ smart 切断の随伴と Γ の有限極限保存

DAG XIII §2.2 の Ω 比較への前段。実延長と smart 切断の既存の Hom 同値を
随伴へ束ね、同じ Γ の台が有限極限を保つことを得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 負次数への実延長は、指定 smart 切断の左随伴である。 -/
def extendSmartTruncationAdjunction :
    (ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat A) ⊣
      (ComplexShape.embeddingUpIntLE 0).truncLE'Functor (ModuleCat A) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun P K => _root_.SerrePositivity.EInfinity.ComplexLimits.extendTruncationHomEquiv P K
    homEquiv_naturality_left_symm := by
      intro P' P K f g
      exact _root_.SerrePositivity.EInfinity.ComplexLimits.extendTruncationHomEquiv_symm_comp K f g
    homEquiv_naturality_right := by
      intro P K L f g
      exact _root_.SerrePositivity.EInfinity.ComplexLimits.extendTruncationHomEquiv_postcomp P f g }

/-- 同じ smart 切断・Γ・加群の台を取る関手は有限極限を保つ。 -/
lemma gammaFunctor_preservesFiniteLimits : PreservesFiniteLimits (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) := by
  have : ((ComplexShape.embeddingUpIntLE 0).truncLE'Functor (ModuleCat A)).IsRightAdjoint :=
    (extendSmartTruncationAdjunction A).isRightAdjoint
  have : PreservesFiniteLimits
      ((ComplexShape.embeddingUpIntLE 0).truncLE'Functor (ModuleCat A)) := inferInstance
  have : (Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤
      SimplicialObject (ModuleCat A)).IsRightAdjoint :=
    (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
      ChainComplex (ModuleCat A) ℕ).toAdjunction.isRightAdjoint
  have : PreservesFiniteLimits (Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤
      SimplicialObject (ModuleCat A)) := inferInstance
  have : PreservesFiniteLimits
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat A) (Type u)).obj
        (forget (ModuleCat A))) := inferInstance
  dsimp only [_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor]
  infer_instance

end SerrePositivity.EInfinity.PowerOperation

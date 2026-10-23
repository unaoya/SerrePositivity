module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionFamilyPointBase
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransportEvaluation
public import SerrePositivity.InfinityCategories.Core.NerveCone

/-!
概要：under 圏の恒等射への制限の底を、元の添字のグラフに同定する。
方針：既存の恒等射の頂点と元の forget 関手への射影を使う。
規約：元の添字を同型で置き換えず厳密に保持する。
使われ方：strict な切断図式と元の fibration の各値の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I]

/-- 元の底と元の添字の同じグラフ。 -/
def underSectionFiberBase (B : SSet.{u}) (i : I) : B ⟶ B ⊗ nerve I :=
  lift (𝟙 B) (SSet.const (nerveVertex i))

/-- 元の恒等射への制限の底は、元の添字の同じグラフ。 -/
lemma underSectionInitialBase (B : SSet.{u}) (i : I) :
    (sectionFamilyProductBase B (nerveMap (Under.forget i)) ≫
      (pre (nervePoint (Under.mk (𝟙 i)))).app (B ⊗ nerve I)) ≫
        (pointFunctorEvaluationIso (B ⊗ nerve I)).hom = underSectionFiberBase B i := by
  rw [sectionFamilyProductBase_point]
  have hv : (nervePoint (Under.mk (𝟙 i))).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
      strictTransportUnderIdentityVertex i := by
    dsimp only [nervePoint]
    rw [SSet.yonedaEquiv_symm_zero]
    change PinchedHom.constant (nerveVertex (Under.mk (𝟙 i))) 0 = _
    rw [pinchedConstant_zero]
    rfl
  rw [hv, strictTransportUnderIdentityVertex_projection]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind

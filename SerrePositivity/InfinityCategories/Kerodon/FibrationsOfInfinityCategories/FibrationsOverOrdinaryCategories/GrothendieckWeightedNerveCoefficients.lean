module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNervePrefixNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Nerve

/-!
概要：同じGrothendieck射列の全prefixを、元のweighted nerveの係数として束ねる。
方針：既存Yonedaの自然性で、同じfiber prefixの全自然性を移す。
規約：IS-W2 R03eの前向きの単体。元の射列と同じ係数を使い、宇宙の置換を増やさない。
使われ方：Grothendieckのnerveからweighted nerveへの前向きの全写像。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (σ : ComposableArrows (Grothendieck F) n)

/-- 元の全prefixを同じ初区間の重みからの一つの自然変換にする。 -/
def grothWeightedNerveCoefficients :
    simplexPrefixWeight n ⟶ (σ ⋙ Grothendieck.forget F) ⋙ (F ⋙ nerveFunctor) where
  app i := (SSet.yonedaEquiv (X := nerve (F.obj (σ.obj i).base)) (n := SimplexCategory.mk i.val)).symm
    (grothWeightedPrefixFiber F σ i)
  naturality i j f := by
    change stdSimplex.map (simplexPrefixInclusion i.val j.val (leOfHom f)) ≫
      (SSet.yonedaEquiv (X := nerve (F.obj (σ.obj j).base)) (n := SimplexCategory.mk j.val)).symm (grothWeightedPrefixFiber F σ j) =
      (SSet.yonedaEquiv (X := nerve (F.obj (σ.obj i).base)) (n := SimplexCategory.mk i.val)).symm (grothWeightedPrefixFiber F σ i) ≫
        nerveMap (F.map (σ.map f).base).toFunctor
    rw [SSet.yonedaEquiv_symm_naturality_left, SSet.yonedaEquiv_symm_comp]
    exact congrArg (fun τ : ComposableArrows (F.obj (σ.obj j).base) i.val =>
      (SSet.yonedaEquiv (X := nerve (F.obj (σ.obj j).base)) (n := SimplexCategory.mk i.val)).symm τ)
        (grothWeightedPrefixFiber_naturality F σ f)

/-- 元のGrothendieck射列の同じ底と係数を持つweighted nerveの単体。 -/
def grothWeightedNerveSimplex : weightedNerveSimplex (F ⋙ nerveFunctor) n :=
  ⟨σ ⋙ Grothendieck.forget F, grothWeightedNerveCoefficients F σ⟩

/-- 前向きの単体は、元の同じ基底の射列を厳密に保つ。 -/
theorem grothWeightedNerveSimplex_base :
    (grothWeightedNerveSimplex F σ).1 = σ ⋙ Grothendieck.forget F := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

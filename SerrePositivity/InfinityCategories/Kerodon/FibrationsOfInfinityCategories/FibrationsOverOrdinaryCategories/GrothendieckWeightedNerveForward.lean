module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveCoefficients

/-!
概要：元のprefix係数を、Grothendieckのnerveからweighted nerveへの全写像にする。
方針：全順序射のprefix制限を同じtransportへ送り、元の重み係数の制限と合わせる。
規約：IS-W2 R03eの前向きの全写像。元の底の射列を厳密に保持する。
使われ方：同じweighted nerve比較同型の前向きの射。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

/-- 同じprefixの脚は、任意の面・退化の再添字付けと両立する。 -/
theorem grothWeightedPrefixArrow_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (Grothendieck F) n.len) (i : Fin (m.len+1)) :
    grothWeightedPrefixArrow F (α.toOrderHom.monotone.functor ⋙ σ) i =
      (simplexPrefixRestriction α i).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixArrow F σ (α.toOrderHom i) := rfl

/-- 同じfiber prefixも、任意の面・退化の再添字付けと両立する。 -/
theorem grothWeightedPrefixFiber_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (Grothendieck F) n.len) (i : Fin (m.len+1)) :
    grothWeightedPrefixFiber F (α.toOrderHom.monotone.functor ⋙ σ) i =
      (simplexPrefixRestriction α i).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixFiber F σ (α.toOrderHom i) := rfl

/-- 同じ前向きの単体は、weighted nerveの実際の全制限と厳密に両立する。 -/
theorem grothWeightedNerveSimplex_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (Grothendieck F) n.len) :
    grothWeightedNerveSimplex F (α.toOrderHom.monotone.functor ⋙ σ) =
      weightedNerveSimplexMap (F ⋙ nerveFunctor) α (grothWeightedNerveSimplex F σ) := by
  apply Sigma.ext rfl
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  change (SSet.yonedaEquiv (X := nerve (F.obj (σ.obj (α.toOrderHom i)).base))
      (n := SimplexCategory.mk i.val)).symm
        (grothWeightedPrefixFiber F (α.toOrderHom.monotone.functor ⋙ σ) i) =
    stdSimplex.map (simplexPrefixRestriction α i) ≫
      (SSet.yonedaEquiv (X := nerve (F.obj (σ.obj (α.toOrderHom i)).base))
        (n := SimplexCategory.mk (α.toOrderHom i).val)).symm
          (grothWeightedPrefixFiber F σ (α.toOrderHom i))
  rw [SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg (fun τ : ComposableArrows (F.obj (σ.obj (α.toOrderHom i)).base) i.val =>
    (SSet.yonedaEquiv (X := nerve (F.obj (σ.obj (α.toOrderHom i)).base))
      (n := SimplexCategory.mk i.val)).symm τ) (grothWeightedPrefixFiber_reindex F α σ i)

/-- 元のGrothendieck射列を同じweighted nerveの単体に送る、一つの全写像。 -/
def grothWeightedNerveForward : nerve (Grothendieck F) ⟶ weightedNerve (F ⋙ nerveFunctor) where
  app _ := ↾grothWeightedNerveSimplex F
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro σ
    exact grothWeightedNerveSimplex_reindex F f.unop σ

/-- 同じ全写像は、元の基底の射列への射影を厳密に保つ。 -/
theorem grothWeightedNerveForward_projection :
    grothWeightedNerveForward F ≫ weightedNerveProjection (F ⋙ nerveFunctor) =
      nerveMap (Grothendieck.forget F) := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

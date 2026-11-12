module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryTensor

public import SerrePositivity.HomotopicalAlgebra.Simplicial.FiniteTensorAdjunction
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.FiniteTensorAdjunction
public import SerrePositivity.KST.Spectra.CosimplicialHornFactorization

/-!
概要：標準単体の余単体図式の latching 射と境界包含の同定。
方針：有限非特異単体集合の表示と境界の latching 添字の同値を使う。
規約：モデル圏構造を仮定せず、通常の単体集合の余極限の同型を構成する。
使われ方：Goerss–Jardine VII §4、HTT A.3.3。通常の Tot の horn 充填の境界条件。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.KST.Spectra.StandardSimplexLatching

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：標準単体の境界 tensor の射は実際の境界包含と同型。
方針：恒等関手による有限 tensor の表示を使う。
規約：同型は arrow 圏の射として与える。
使われ方：Goerss–Jardine VII §4。latching 射との比較の第一段階。 -/
def tensorBoundaryArrowIso (n : ℕ) :
    Arrow.mk (SubcomplexTensor.inclusion (SSet.boundary.{u} n) SSet.stdSimplex) ≅
      Arrow.mk (SSet.boundary.{u} n).ι :=
  Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso (𝟭 SSet.{u})
    (SSet.boundary.{u} n).toSSet) (Iso.refl _) (by
      exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso_inclusion (𝟭 SSet.{u})
        (SSet.boundary.{u} n)).trans (Category.comp_id _).symm)

/-- 概要：境界包含は標準単体の実際の latching 射と同型。
方針：境界 tensor と latching の添字の同値を合成する。
規約：標準単体は次数 n の単体であり、境界の全ての固有面を含む。
使われ方：Goerss–Jardine VII §4、HTT A.3.3。Tot の Reedy 境界。 -/
def boundaryArrowIso (n : ℕ) : Arrow.mk (SSet.boundary.{u} n).ι ≅
    Arrow.mk ((latchingComparison simplex (SimplexCategory.mk n)).app SSet.stdSimplex.{u}) :=
  (tensorBoundaryArrowIso n).symm ≪≫ boundaryTensorArrowIso SSet.stdSimplex.{u} n

/-- 概要：標準単体の余単体図式の全ての latching 射は単射。
方針：実際の境界包含の単射性を arrow 圏の同型で移す。
規約：零次の空な境界も含む。
使われ方：Goerss–Jardine VII §4。標準単体の重みの Reedy 単射性。 -/
lemma mono (j : SimplexCategory) :
    Mono ((latchingComparison simplex j).app SSet.stdSimplex.{u}) := by
  induction j using SimplexCategory.rec with | _ n =>
  exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff (boundaryArrowIso n)).mp
    (inferInstanceAs (Mono (SSet.boundary.{u} n).ι))

end

end SerrePositivity.KST.Spectra.StandardSimplexLatching

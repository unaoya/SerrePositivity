module
public import SerrePositivity.InfinityCategories.Core.CodiscreteNerve
public import SerrePositivity.InfinityCategories.Core.EquivalencePullbackPathLifting
public import SerrePositivity.InfinityCategories.F1.ScaffoldFiniteTotalFibers
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanRelativePathLifting
public import SerrePositivity.InfinityCategories.Stable.LeftFibrationInitialPiZero

/-! # 可縮な Kan 複体上の fiber の包含

概要：可縮な Kan 複体上の Kan fibration の各 fiber の包含は単体的ホモトピー同値である。
方針：点から可縮な底への同値を fibration に沿って引き戻し、頂点 fiber の標準表示を使う。
規約：底の可縮性は全境界の充填条件。使われ方：二枝の引き戻しから固定基点上のループ模型への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：可縮な底の Kan fibration の fiber の包含は quasicategory の同値。
方針：点の包含を可逆 path の相対持ち上げを持つ射に沿って引き戻す。
規約：両端は Kan 複体。使われ方：引き戻し全体を固定点上の fiber へ移す。 -/
lemma vertexFiberι_isQCatEquivalence_of_contractible_base {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (hB : IsContractibleKan B) (b : B _⦋0⦌) : IsQCatEquivalence (vertexFiberι p b) := by
  let j : (Δ[0] : SSet.{u}) ⟶ B := SSet.const b
  have hj : IsQCatEquivalence j := (hB.isPrecompositionEquivalence_point j).isQCatEquivalence
  have := HomotopyLimits.relativeEquivalencePathMapAt_trivialKanFibration_of_fibration p 1
  have hp : IsQCatEquivalence (pullback.snd j p) := hj.pullback_snd_of_relativePath p
  let e : vertexFiber p b ≅ pullback j p := (vertexFiber_isPullback p b).flip.isoPullback
  have he : e.hom ≫ pullback.snd j p = vertexFiberι p b :=
    IsPullback.isoPullback_hom_snd _
  rw [← he]
  exact (qCatEquivalenceOfIso e).isQCatEquivalence.comp hp

/-- 概要：可縮な底の Kan fibration の fiber の包含は単体的ホモトピー同値。
方針：fiber の Kan 性と quasicategory 同値のホモトピー逆を使う。
規約：単なる π₀ の全単射ではなく実際のホモトピー逆を持つ。
使われ方：二枝の引き戻しとループ空間の空間そのものの比較。 -/
lemma vertexFiberι_homotopyEquivalence_of_contractible_base {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (hB : IsContractibleKan B) (b : B _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (vertexFiberι p b) := by
  have : KanComplex (vertexFiber p b) := vertexFiber_kanComplex_of_leftFibration p b
  exact (vertexFiberι_isQCatEquivalence_of_contractible_base p hB b).isSimplicialHomotopyEquivalence

/-- 概要：可縮な底の fiber の包含は連結成分の同値を与える。
方針：実際のホモトピー同値の π₀ の全単射を同値として束ねる。
規約：順方向は包含の π₀ への作用。使われ方：ループの Hom 表示への比較。 -/
def vertexFiberPiZeroEquivOfContractibleBase {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (hB : IsContractibleKan B) (b : B _⦋0⦌) : SSet.π₀ (vertexFiber p b) ≃ SSet.π₀ E :=
  Equiv.ofBijective (SSet.mapπ₀ (vertexFiberι p b))
    (vertexFiberι_homotopyEquivalence_of_contractible_base p hB b).mapPiZero_bijective

end SerrePositivity.InfinityCategories

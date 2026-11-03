module
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.SquareConePostcomp
public import SerrePositivity.InfinityCategories.Stable.FunctorFiniteLimits
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorInitial
public import SerrePositivity.InfinityCategories.Core.FunctorTerminal

/-!
概要：関手圏の零頂点と loop 四角形を点ごとに判定する。
方針：既存の始対象・終対象と全極限錐の点ごとの判定を使う。
規約：元の圏の安定性を仮定しない。
使われ方：一般安定性判定の回転を関手区間の全族に適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：各頂点で零である全関手は関手圏の零頂点である。
方針：始対象性と終対象性をそれぞれ点ごとに検査する。
規約：全関手を任意の図式で置き換えない。
使われ方：loop 四角形の二つの零角。 -/
lemma isZeroVertex_functorVertex_of_pointwise {K X : SSet.{u}} (f : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, IsZeroVertex (f.app (Opposite.op ⦋0⦌) k)) :
    IsZeroVertex (functorVertex f) :=
  ⟨isInitialVertex_functorVertex_of_pointwise f (fun k ↦ (hf k).1),
    isTerminalVertex_functorVertex_of_pointwise f (fun k ↦ (hf k).2)⟩

/-- 概要：関手頂点の全評価が零なら、同じ関手頂点は零である。
方針：実関手による頂点表示へ戻して点ごとの判定を適用する。
規約：頂点の表示は選択に依存しない。
使われ方：全単体の loop 族の零角。 -/
lemma isZeroVertex_of_pointwise_evaluation {K X : SSet.{u}}
    (v : ((ihom K).obj X) _⦋0⦌)
    (hv : ∀ k : K _⦋0⦌,
      IsZeroVertex ((evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋0⦌) v)) :
    IsZeroVertex v := by
  obtain ⟨f, rfl⟩ := (functorVertexEquiv K X).surjective v
  apply isZeroVertex_functorVertex_of_pointwise
  intro k
  have h := hv k
  change IsZeroVertex ((evaluateFunctorAt (Y := X) k).app
    (Opposite.op ⦋0⦌) (functorVertex f)) at h
  rw [evaluateFunctorAt_functorVertex] at h
  exact h

/-- 概要：pointed な圏を値とする関手圏は定値零関手を持つ。
方針：同じ零頂点の定値関手を点ごとに検査する。
規約：始域の有限性は不要。使われ方：関手区間での一般 loop 判定。 -/
lemma hasZeroVertex_functorCategory (K X : SSet.{u}) [HasZeroVertex X] :
    HasZeroVertex ((ihom K).obj X) := by
  let z := chosenZeroVertex X
  refine ⟨functorVertex (SSet.const z.vertex), ?_⟩
  apply isZeroVertex_functorVertex_of_pointwise
  intro k
  change IsZeroVertex (PinchedHom.constant z.vertex 0)
  rw [pinchedConstant_zero]
  exact z.isZero

/-- 概要：関手圏の四角形は全評価で引き戻しであるとき、かつそのときに限り引き戻し。
方針：同じ標準 cospan 錐に極限の点ごとの検出を適用する。
規約：元の圏の有限極限から評価図式の存在条件を満たす。
使われ方：全関手に作用する実 loop 四角形の構成。 -/
lemma isPullbackSquare_functorCategory_iff_pointwise {K X : SSet.{u}}
    [Quasicategory X] [HasFiniteLimits X]
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X) :
    IsPullbackSquare R ↔ ∀ k : K _⦋0⦌,
      IsPullbackSquare (R ≫ evaluateFunctorAt k) := by
  have hp : HasPointwiseLimits (pullbackCospan R) :=
    fun _ ↦ HasFiniteLimits.hasLimit _
  change IsLimitCone (pullbackCone R) ↔ _
  rw [isLimitCone_iff_pointwise_of_hasPointwiseLimits hp]
  change (∀ k : K _⦋0⦌,
    IsLimitCone (mapJoinCone (evaluateFunctorAt k) (pullbackCone R))) ↔ _
  apply forall_congr'
  intro k
  exact F2.isLimitCone_map_pullbackCone_iff _ R

end SerrePositivity.InfinityCategories

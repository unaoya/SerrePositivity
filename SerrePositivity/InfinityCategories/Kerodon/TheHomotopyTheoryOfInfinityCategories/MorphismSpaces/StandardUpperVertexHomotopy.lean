module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionHornFaceEquivalence

/-!
# 標準単体上の頂点との最大値へのホモトピー

概要：解像の一頂点の追加の変形から標準単体上の最大値への変形を得る。
方針：区間の切断で解像へ移し、変形後に最大元の射影を取る。
規約：単体ごとの値は元の頂点か選んだ頂点のいずれか。
使われ方：HA 1.3.1.17、Kerodon Proposition 4.6.7.23（Tag 01LW） の標準ホーン側の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory MonoidalCategory
open scoped _root_.Simplicial

/-- 概要：標準単体の各頂点を単位区間に従って選んだ頂点との最大値へ移す射。
方針：解像の切断、既存の変形、最大元の射影を順に合成する。
規約：全体で定義し、ホーンや面への制限は別に検証する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の標準ホーン内の変形の台。 -/
def standardUpperVertexHomotopyMap {n : ℕ} (i : Fin (n + 1)) :
    (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[n] :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection n ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertHomotopyMap i ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n

/-- 概要：標準単体上の変形の各頂点の値は元の頂点か i との最大値である。
方針：区間の旗の最大元と一頂点の追加の最大元の式を適用する。
規約：全ての単体次数と全ての頂点での式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の標準ホーンの欠落頂点の保存。 -/
lemma standardUpperVertexHomotopyMap_apply {n d : ℕ} (i : Fin (n + 1))
    (σ : (Δ[n] : SSet.{u}) _⦋d⦌) (t : (Δ[1] : SSet.{u}) _⦋d⦌) (r : Fin (d + 1)) :
    ((standardUpperVertexHomotopyMap i).app (Opposite.op ⦋d⦌) (σ, t)) r =
      if t r = 0 then σ r else max i (σ r) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.interval σ.down.toOrderHom) i
    t.down.toOrderHom).maxAt r = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex_maxAt, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.maxAt_interval]
  rfl

/-- 概要：標準単体の恒等射は選んだ頂点との最大値による自己写像とホモトピックである。
方針：変形の単体ごとの公式を零・一端点で評価する。
規約：ここではホーンへの制限を含めない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の解像と標準単体の変形の対応。 -/
def standardUpperVertexHomotopy {n : ℕ} (i : Fin (n + 1)) :
    SSet.Homotopy (𝟙 (Δ[n] : SSet.{u}))
      (SSet.stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i))) where
  h := standardUpperVertexHomotopyMap i
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro σ
    apply SSet.stdSimplex.ext
    intro r
    exact standardUpperVertexHomotopyMap_apply i σ _ r
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro σ
    apply SSet.stdSimplex.ext
    intro r
    exact standardUpperVertexHomotopyMap_apply i σ _ r
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.2

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

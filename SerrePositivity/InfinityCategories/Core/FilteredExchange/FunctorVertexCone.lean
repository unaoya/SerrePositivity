module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Limit

/-!
概要：錐の形状上の関手の頂点を、その元の図式と頂点を保つ実際の錐にする。
方針：関手頂点と元の射の全単射で読み戻し、右因子への制限を固定図式とする。
規約：元の全単体を保持。使われ方：二重の coherent 図式の余極限後の錐の極限性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の錐形状上の関手の頂点から読み戻す、元の射。 -/
def functorVertexConeMap {J X : SSet.{u}}
    (v : ((ihom (join (Δ[0] : SSet.{u}) J)).obj X) _⦋0⦌) : join Δ[0] J ⟶ X :=
  (functorVertexEquiv _ _).symm v

/-- 錐形状上の元の関手の頂点を、元の図式上の錐にする。 -/
def functorVertexCone {J X : SSet.{u}}
    (v : ((ihom (join (Δ[0] : SSet.{u}) J)).obj X) _⦋0⦌) :
    JoinCone (joinInr Δ[0] J ≫ functorVertexConeMap v) := ⟨functorVertexConeMap v, rfl⟩

/-- 錐の頂点は元の関手頂点を錐形状の頂点で評価したもの。 -/
lemma functorVertexCone_vertex {J X : SSet.{u}}
    (v : ((ihom (join (Δ[0] : SSet.{u}) J)).obj X) _⦋0⦌) :
    (functorVertexCone v).vertex =
      (evaluateFunctorAt ((joinInl (Δ[0] : SSet.{u}) J).app (Opposite.op ⦋0⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))).app (Opposite.op ⦋0⦌) v := by
  obtain ⟨f, rfl⟩ := (functorVertexEquiv _ _).surjective v
  let k := (joinInl (Δ[0] : SSet.{u}) J).app (Opposite.op ⦋0⦌)
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
  change (functorVertexCone (functorVertex f)).vertex =
    (evaluateFunctorAt k).app (Opposite.op ⦋0⦌) (functorVertex f)
  rw [evaluateFunctorAt_functorVertex]
  have hf : functorVertexConeMap (functorVertex f) = f :=
    (functorVertexEquiv _ _).symm_apply_apply f
  change SSet.yonedaEquiv (joinInl Δ[0] J ≫ functorVertexConeMap (functorVertex f)) = _
  rw [hf]
  rfl

end SerrePositivity.InfinityCategories.F2

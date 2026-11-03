module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeVertexIsoHomotopy

/-!
概要：底固定円柱の構成に使った同じ相対代表辺と全円柱の表示を公開する。
方針：元の選択と仕様をそのまま取り出し、包含後の Yoneda 表示を計算する。
規約：代表辺を再選択しない。使われ方：同じ fiber 内での指定類の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B)
  {f g : A ⟶ E} (hf : f ≫ p = a) (hg : g ≫ p = a)
  (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg))

/-- 元の底固定円柱の構成に使った同じ相対代表辺。 -/
def relativeIsoRepresentativeEdge :
    Truncated.Edge (X := (truncation 2).obj (relativeFunctorSpace p a))
      (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg) :=
  Classical.choose (homotopyCategory_homMk_surjective _ _ e.hom)

/-- 同じ相対代表辺の類は元の指定同型の順方向の射。 -/
lemma relativeIsoRepresentativeEdge_homMk :
    Truncated.HomotopyCategory.homMk (relativeIsoRepresentativeEdge p a hf hg e) = e.hom :=
  Classical.choose_spec (homotopyCategory_homMk_surjective _ _ e.hom)

/-- 元の全時刻の円柱は同じ相対代表辺の uncurry そのもの。 -/
lemma relativeVertexIsoHomotopy_h_uncurry :
    (relativeVertexIsoHomotopy p a hf hg e).val.h =
      relativeFunctorUncurry
        (SSet.yonedaEquiv.symm (relativeIsoRepresentativeEdge p a hf hg e).edge) := by
  unfold relativeVertexIsoHomotopy relativeIsoRepresentativeEdge
  dsimp only
  let k := Classical.choose (homotopyCategory_homMk_surjective
    (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg) e.hom)
  let i := vertexFiberι ((ihom A).map p) (functorVertex a)
  change uncurry (SSet.yonedaEquiv.symm (i.app (Opposite.op ⦋1⦌) k.edge)) =
    uncurry (SSet.yonedaEquiv.symm k.edge ≫ i)
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.InfinityCategories.F2

module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeIsoFiberRepresentative
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeIsoFiberImage

/-!
概要：底固定円柱の fiber 制限は、元の相対同型の同じ指定像を表す。
方針：同じ代表辺の像を端点表示で輸送し、相対辺の指定類の仕様を適用する。
規約：fiber の包含後の類から反映しない。使われ方：模型比較の全 path の指定類。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ底固定円柱の fiber 制限の類は元の指定相対同型の fiber 像そのもの。 -/
lemma relativeIsoFiberHomotopy_hom {A E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) {f g : A ⟶ E}
    (hf : f ≫ p = a) (hg : g ≫ p = a)
    (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg)) (b : B _⦋0⦌) :
    Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (relativeIsoFiberHomotopy p a hf hg e b)) =
        (relativeIsoFiberImage p a hf hg e b).hom := by
  let k := relativeIsoRepresentativeEdge p a hf hg e
  let j := k.map ((truncation 2).map (relativeFunctorFiberHom a p b))
  have h := homMk_transport (relativeFunctorFiberHom_vertex a p b f hf)
    (relativeFunctorFiberHom_vertex a p b g hg) j
    (functorEdgeOfSimplicialHomotopy (relativeIsoFiberHomotopy p a hf hg e b))
    (relativeIsoFiberHomotopy_edge p a hf hg e b)
  have hj : Truncated.HomotopyCategory.homMk j =
      (VertexIso.map e (relativeFunctorFiberHom a p b)).hom := by
    change (Truncated.mapHomotopyCategory ((truncation 2).map (relativeFunctorFiberHom a p b))).map
      (Truncated.HomotopyCategory.homMk k) = _
    rw [relativeIsoRepresentativeEdge_homMk]
    rfl
  rw [hj] at h
  exact h.symm

end SerrePositivity.InfinityCategories.F2

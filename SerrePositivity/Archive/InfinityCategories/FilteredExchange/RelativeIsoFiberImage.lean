module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFiberRestriction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation

/-!
概要：任意の指定相対頂点同型の fiber 作用を実際の fiber 射の関手同型にする。
方針：fiber Hom の元の指定像を実際の関手頂点へ両端で正規化する。
規約：指定同型の類を保持。使われ方：底固定円柱の fiber 制限の指定類。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) {f g : A ⟶ E}
  (hf : f ≫ p = a) (hg : g ≫ p = a)
  (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg)) (b : B _⦋0⦌)

/-- 元の指定相対同型の同じ fiber 間の実際の作用。 -/
def relativeIsoFiberImage :
    FunctorIso (vertexFiberMap a p f hf b) (vertexFiberMap a p g hg b) :=
  (eqToIso (congrArg SSet.HomotopyCategory.mk
    (relativeFunctorFiberHom_vertex a p b f hf))).symm ≪≫
      VertexIso.map e (relativeFunctorFiberHom a p b) ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk (relativeFunctorFiberHom_vertex a p b g hg))

/-- 実際の両端の表示を外すと元の相対同型の同じ fiber Hom 像を回収する。 -/
lemma relativeIsoFiberImage_heq_map :
    HEq (relativeIsoFiberImage p a hf hg e b)
      (VertexIso.map e (relativeFunctorFiberHom a p b)) := by
  exact iso_endpoints_heq _ _ _

end SerrePositivity.InfinityCategories.F2

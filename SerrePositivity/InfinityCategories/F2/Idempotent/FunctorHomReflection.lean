module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

/-!
概要：充満忠実な関手への後合成で存在する全ホモトピーを、元の関手間へ戻す。
方針：関手空間の充満忠実性で同じ二頂点間の射の類を戻し、実際の辺で表す。
規約：可逆性は要求しない。元のホモトピーとの厳密な一致は主張しない。
使われ方：始対象・終対象を持つ冪等完備化の底の弱可縮性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 充満忠実な元の関手への後合成後に全ホモトピーがあれば、元の二関手間にも存在する。 -/
lemma homotopy_exists_of_fullyFaithful {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (hf : IsFullyFaithful f)
    (F G : A ⟶ X) (H : SSet.Homotopy (F ≫ f) (G ≫ f)) :
    Nonempty (SSet.Homotopy F G) := by
  have h := HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)
  have hp := (hf.postcompose A).homotopyCategoryMap_bijective (functorVertex F)
    (functorVertex G)
  obtain ⟨a, _ha⟩ := hp.surjective h
  obtain ⟨e, _he⟩ := homotopyCategory_homMk_surjective (functorVertex F) (functorVertex G) a
  exact ⟨simplicialHomotopyOfFunctorEdge e⟩

end SerrePositivity.InfinityCategories.F2.Idempotent

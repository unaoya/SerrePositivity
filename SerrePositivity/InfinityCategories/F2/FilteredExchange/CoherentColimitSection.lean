module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitProjection
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TrivialFibrationVertexSection

/-!
概要：構成済みの全空間余極限余錐を全頂点で保つ、普遍余錐射影の厳密な切断。
方針：自明 Kan 射の頂点を指定した切断構成を適用する。
規約：各図式の native 余錐を変更しない。使われ方：元の全空間模型を値に持つ余極限関手。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})

/-- 各頂点が元の全空間余錐である普遍余錐射影の切断が存在。 -/
lemma exists_coherentColimitCoconeSection :
    ∃ s : (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} ⟶
        colimitCocones ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u},
      s ≫ colimitCoconeProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u} =
        𝟙 _ ∧ ∀ v, s.app (Opposite.op ⦋0⦌) v = coherentTotalColimitCoconeVertex B v := by
  have := coherentColimitCoconeProjection_trivialKanFibration B
  exact trivialKanFibration_section_with_vertices _ (coherentTotalColimitCoconeVertex B)
    (coherentTotalColimitCoconeVertex_projection B)

/-- 元の全空間余極限余錐を全頂点で保つ、選んだ coherent な普遍余錐の切断。 -/
def coherentColimitCoconeSection :
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} ⟶
      colimitCocones ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u} :=
  Classical.choose (exists_coherentColimitCoconeSection B)

/-- 選んだ切断の元の図式への制限は全単体で恒等。 -/
lemma coherentColimitCoconeSection_projection :
    coherentColimitCoconeSection B ≫
      colimitCoconeProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u} = 𝟙 _ :=
  (Classical.choose_spec (exists_coherentColimitCoconeSection B)).1

/-- 選んだ切断は、各図式の元の全空間余極限余錐を厳密に保持。 -/
lemma coherentColimitCoconeSection_vertex
    (v : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}) _⦋0⦌) :
    (coherentColimitCoconeSection B).app (Opposite.op ⦋0⦌) v =
      coherentTotalColimitCoconeVertex B v :=
  (Classical.choose_spec (exists_coherentColimitCoconeSection B)).2 v

end SerrePositivity.InfinityCategories.F2

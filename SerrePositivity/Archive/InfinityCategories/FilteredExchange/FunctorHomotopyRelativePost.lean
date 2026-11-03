module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopySourcePostIso

/-!
概要：元の指定ホモトピーの native 全空間作用による相対後合成を固定する。
方針：元の選択済み頂点作用をそのまま相対後合成へ渡す。
規約：作用を選び直さない。使われ方：全単位三単体の共通の六関手と六比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定ホモトピーの同じ native 作用による、全相対始域上の後合成。 -/
def functorHomotopyRelativePost {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy F G) (p : C ⟶ B) :=
  HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection G)
    (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val
    (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property p

end SerrePositivity.InfinityCategories.F2

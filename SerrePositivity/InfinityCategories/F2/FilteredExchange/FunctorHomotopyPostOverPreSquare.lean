module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopyRelativePost
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeFunctorPostOverPre

/-!
概要：元のホモトピーの全空間作用と底上の前合成の厳密な可換四角形を保持する。
方針：同じ native 作用の相対後合成の前合成則を使う。
規約：元の作用と底上の射を保持。使われ方：二面比較全体の同じ全空間への制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の native 作用による後合成は、同じ底上の射の前合成と厳密に可換する。 -/
lemma functorHomotopyRelativePost_overPre_square {B C D : SSet.{u + 1}}
    {F G : B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
    (p : C ⟶ B) (d : D ⟶ B) (t : D ⟶ C) (ht : t ≫ p = d) :
    CommSq (functorHomotopyRelativePost H p)
      (relativeFunctorOverPre (leftUnstraighteningProjection F)
        (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht))
      (relativeFunctorOverPre (leftUnstraighteningProjection G)
        (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht))
      (functorHomotopyRelativePost H d) :=
  ⟨relativeFunctorPost_overPre p d (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection G) t ht
    (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val
    (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property⟩

end SerrePositivity.InfinityCategories.F2

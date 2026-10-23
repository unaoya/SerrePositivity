module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitValueActionOverPre

/-!
概要：元の最後の辺の値の二面比較を、元の最初の辺の native 作用で前合成する。
方針：同じ底上の実射の自然性と、恒等初期値の同じ像の一致を使う。
規約：元の二辺・指定比較を保持。使われ方：三辺の比較を同じ最初の全空間へ戻す。
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
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (l : SSet.Homotopy F G) (r : SSet.Homotopy G J)
local notation "pF" => leftUnstraighteningProjection F
local notation "pG" => leftUnstraighteningProjection G
local notation "xF" => relativeFunctorVertex pF pF (𝟙 (leftUnstraightening F))
  (Category.id_comp pF)
local notation "xG" => relativeFunctorVertex pG pG (𝟙 (leftUnstraightening G))
  (Category.id_comp pG)
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy l))
local notation "z" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "V" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (KanObject.obj (spaceInfinityObject z))

/-- 最後の辺の元の全空間での比較の前合成は、同じ最初の作用で移した初期値の比較。 -/
lemma coherentColimitUnitValueAction_precomp_firstEdge :
    HEq (VertexIso.map (coherentColimitUnitValueAction B r pG xG) ((pre f).app V))
      (coherentColimitUnitValueAction B r pF ((functorHomotopyRelativePost l pF).app _ xF)) := by
  have h := coherentColimitUnitValueAction_overPre_heq B r pG pF f
    (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy l)).property xG
  have hx :
      (relativeFunctorOverPre pG
        (Over.homMk (U := Over.mk pF) («V» := Over.mk pG) f
          (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy l)).property)).app
            (Opposite.op ⦋0⦌) xG = (functorHomotopyRelativePost l pF).app _ xF := by
    apply Subtype.ext
    rfl
  rw [hx] at h
  exact h

end SerrePositivity.InfinityCategories.F2

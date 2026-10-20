module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpanCoconePointHomEnd
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyEndpointTransport
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：元の span の点 Hom end と辺全族 end の間で選択した同じ逆の二ホモトピーを保持する。
方針：既存の choose_spec の代表を使い、元の余錐族に前合成して辺全族へ戻す。
規約：逆の自然性や成分の厳密な式を仮定しない。使われ方：native 経路と辺全族の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X : SSet.{u}} [Quasicategory X] (p : (horn 2 0 : SSet.{u}) ⟶ X) (y : X _⦋0⦌)

/-- 元の選択済み逆の単位側のホモトピーを、その同じ choose_spec から取る。 -/
def spanPointHomEndInverseUnit : SSet.Homotopy
    (spanPointHomToEdgeEnd p y ≫ spanEdgeEndToPointHomEnd p y) (𝟙 _) :=
  (spanPointHomToEdgeEnd_homotopyEquivalence p y).choose_spec.1.some

/-- 元の選択済み逆の余単位側も、その同じ choose_spec の代表を保持する。 -/
def spanPointHomEndInverseCounit : SSet.Homotopy
    (spanEdgeEndToPointHomEnd p y ≫ spanPointHomToEdgeEnd p y) (𝟙 _) :=
  (spanPointHomToEdgeEnd_homotopyEquivalence p y).choose_spec.2.some

/-- 元の余錐から点 Hom end を経て辺全族へ戻る射は、元の辺全族への比較にホモトピック。 -/
def spanCoconePointHomEndReturn : SSet.Homotopy
    (spanCoconeToPointHomEnd p y ≫ spanPointHomToEdgeEnd p y)
    (spanCoconeToEdgeEnd p y) :=
  homotopyEndpointTransport
    (functorHomotopyPrecomp (spanPointHomEndInverseCounit p y) (spanCoconeToEdgeEnd p y))
    (Category.assoc _ _ _).symm (Category.comp_id _)

/-- 戻しの円柱は、元の余錐の辺全族への比較を同じ余単位に前合成した raw な射。 -/
lemma spanCoconePointHomEndReturn_raw :
    (spanCoconePointHomEndReturn p y).h =
      (spanCoconeToEdgeEnd p y ▷ (Δ[1] : SSet.{u})) ≫
        (spanPointHomEndInverseCounit p y).h := rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits

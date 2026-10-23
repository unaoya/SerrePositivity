module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CospanRectificationMaps

/-!
概要：cospan 厳密化の二成分の指定同型と、その底における元の指定値を公開する。
方針：同じ代表円柱の持ち上げを使い、その像から元の関手同型の順方向の射を回収する。
規約：指定類を選び直さない。使われ方：共通の引き戻し内の二脚の底の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X Z X' Z' : SSet.{u}}
  [KanComplex X] [KanComplex Z] [KanComplex X'] [KanComplex Z']
  (f : X ⟶ Z) (f' : X' ⟶ Z') (s : X ⟶ X') (v : Z ⟶ Z')
  (e : FunctorIso (f ≫ v) (s ≫ f'))
local notation "pr" => pullback.snd (NatTrans.app (intervalEndpointNatTrans 0) Z) f

/-- 元の右候補から同じ右厳密化への指定関手同型。 -/
def cospanRectificationRightIso :
    FunctorIso (s ≫ intervalReplacementSection f') (cospanRectificationRightMap f f' s v e) :=
  kanHomotopyRectificationIso _ _ _ _

/-- 元の第一置換からの候補と同じ左厳密化の間の指定関手同型。 -/
def cospanRectificationLeftIso :
    FunctorIso (pr ≫ s ≫ intervalReplacementSection f')
      (cospanRectificationLeftMap f f' s v e) := kanHomotopyRectificationIso _ _ _ _

/-- 右厳密化の指定同型は底で元の指定同型の逆を厳密に回収する。 -/
lemma cospanRectificationRightIso_image :
    functorIsoOfEq ((cospanRectificationRightIso f f' s v e).postcomp
      (intervalReplacementEndpoint f')) rfl (cospanRectificationRightMap_over f f' s v e) =
        cospanRectificationRightBaseIso f f' s v e := by
  unfold cospanRectificationRightIso
  rw [kanHomotopyRectificationIso_image]
  apply Iso.ext
  exact functorHomHomotopy_hom _

/-- 左厳密化の指定同型は底で元の逆比較と元の全 path の指定合成を厳密に回収する。 -/
lemma cospanRectificationLeftIso_image :
    functorIsoOfEq ((cospanRectificationLeftIso f f' s v e).postcomp
      (intervalReplacementEndpoint f')) rfl (cospanRectificationLeftMap_over f f' s v e) =
        cospanRectificationLeftBaseIso f f' s v e := by
  unfold cospanRectificationLeftIso
  rw [kanHomotopyRectificationIso_image]
  apply Iso.ext
  exact functorHomHomotopy_hom _

end SerrePositivity.InfinityCategories.F2

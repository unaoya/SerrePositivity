module

public import SerrePositivity.InfinityCategories.F2.CospanRectificationBaseIsos

/-!
概要：元の指定同型で可換な cospan 比較を、同じ底射に厳密に写る二成分に補正する。
方針：元の底の指定同型の円柱を持ち上げ、切断と入力射影の同値性を保持する。
規約：任意の Kan cospan と指定同型を使用。使われ方：native 値の引き戻し比較。
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
local notation "Hr" => functorHomHomotopy (Iso.hom (cospanRectificationRightBaseIso f f' s v e))
local notation "Hl" => functorHomHomotopy (Iso.hom (cospanRectificationLeftBaseIso f f' s v e))

/-- 元の右入力の指定比較を、置換した右脚上で厳密化する。 -/
def cospanRectificationRightMap : X ⟶ intervalReplacement f' :=
  kanHomotopyRectification (intervalReplacementEndpoint f')
    (s ≫ intervalReplacementSection f') (f ≫ v) Hr

/-- 元の第一置換の指定比較を、置換した左脚上で厳密化する。 -/
def cospanRectificationLeftMap : intervalReplacement f ⟶ intervalReplacement f' :=
  kanHomotopyRectification (intervalReplacementEndpoint f')
    (pr ≫ s ≫ intervalReplacementSection f') (intervalReplacementEndpoint f ≫ v) Hl

/-- 補正した右成分は元の右脚と底射の合成に厳密に写る。 -/
lemma cospanRectificationRightMap_over :
    cospanRectificationRightMap f f' s v e ≫ intervalReplacementEndpoint f' = f ≫ v :=
  kanHomotopyRectification_over _ _ _ _

/-- 補正した左成分も元の置換左脚と底射の合成に厳密に写る。 -/
lemma cospanRectificationLeftMap_over :
    cospanRectificationLeftMap f f' s v e ≫ intervalReplacementEndpoint f' =
      intervalReplacementEndpoint f ≫ v := kanHomotopyRectification_over _ _ _ _

/-- 元の入力比較が同値なら補正した同じ右成分も同値。 -/
lemma cospanRectificationRightMap_homotopyEquivalence (hs : IsSimplicialHomotopyEquivalence s) :
    IsSimplicialHomotopyEquivalence (cospanRectificationRightMap f f' s v e) := by
  apply kanHomotopyRectification_homotopyEquivalence
  have ht := intervalReplacementSection_isWeakHomotopyEquivalence f'
  exact hs.comp ht.isSimplicialHomotopyEquivalence

/-- 元の入力比較が同値なら補正した同じ左成分も同値。 -/
lemma cospanRectificationLeftMap_homotopyEquivalence (hs : IsSimplicialHomotopyEquivalence s) :
    IsSimplicialHomotopyEquivalence (cospanRectificationLeftMap f f' s v e) := by
  have : KanComplex (pullback ((intervalEndpointNatTrans 0).app Z) f) :=
    inferInstanceAs (KanComplex (intervalReplacement f))
  have he := intervalReplacementSection_isWeakHomotopyEquivalence f
  have hp : IsWeakHomotopyEquivalence pr := he.cancel_left (by
    rw [intervalReplacementSection_projection]
    exact isWeakHomotopyEquivalence_id X)
  have ht := intervalReplacementSection_isWeakHomotopyEquivalence f'
  apply kanHomotopyRectification_homotopyEquivalence
  exact hp.isSimplicialHomotopyEquivalence.comp (hs.comp ht.isSimplicialHomotopyEquivalence)

end SerrePositivity.InfinityCategories.F2

module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionMixedAssociativity
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionUnits
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
概要：二対象と全水平合成から実際の単体的豊穣walking adjunctionを構成する。
方針：四つのHom圏のnerveを持ち上げ、全関手の単位則と結合則を各次数で使う。
規約：全単体を含む豊穣圏を構成し、存在を仮定しない。
使われ方：HA §4.7.2–§4.7.3・Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8。
Kerodon Remark 6.2.1.4（Tag 02EN）への忘却前の全随伴の表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：walking adjunctionの四つの全単体的Hom。
方針：構成済みの実Hom圏のnerveを宇宙持ち上げする。
規約：対象の等式だけに切り詰めない。使われ方：Riehl–Verity Remark 3.3.8。 -/
abbrev WalkingAdjunctionHomShape (X Y : WalkingAdjunctionPoint) : SSet.{u} :=
  SSet.uliftFunctor.{u, 0}.obj (nerve (walkingAdjunctionHom X Y))

/-- 概要：各対象の全恒等単体。
方針：空の自己Homを値とする定値関手を全次数で指定する。
規約：構成済みの単位を保持する。使われ方：HA §4.7.2 の全単位。 -/
def walkingAdjunctionUnit (X : WalkingAdjunctionPoint) :
    𝟙_ SSet.{u} ⟶ WalkingAdjunctionHomShape X X where
  app n := ↾fun _ ↦ ULift.up ((Functor.const (Fin (n.unop.len + 1))).obj
    (walkingAdjunctionIdentity X))
  naturality _ _ _ := rfl

/-- 概要：八つの全水平合成の単体写像。
方針：同じ長さの二つの列を実双関手で合成する。
規約：全ての単体作用と可換する。使われ方：Riehl–Verity Remark 3.3.8。 -/
def walkingAdjunctionComposition (X Y Z : WalkingAdjunctionPoint) :
    WalkingAdjunctionHomShape.{u} X Y ⊗ WalkingAdjunctionHomShape.{u} Y Z ⟶
      WalkingAdjunctionHomShape.{u} X Z where
  app _ := ↾fun p ↦ ULift.up (p.1.down.prod' p.2.down ⋙ walkingAdjunctionHorizontal X Y Z)
  naturality _ _ _ := rfl

/-- 概要：構成した全単体的walking adjunction。
方針：四Homと八合成をまとめ、全関手の法則を各単体に適用する。
規約：豊穣圏のinstanceを引数として仮定しない。
使われ方：HA Proposition 4.7.3.3 の全モナドの源、Riehl–Verity Remark 3.3.8。 -/
instance walkingAdjunctionEnrichedCategory : EnrichedCategory SSet.{u} WalkingAdjunctionPoint where
  Hom := WalkingAdjunctionHomShape
  id := walkingAdjunctionUnit
  comp := walkingAdjunctionComposition
  id_comp X Y := by
    ext n p
    apply ULift.ext
    exact walkingAdjunctionHorizontal_leftUnit X Y p.down
  comp_id X Y := by
    ext n p
    apply ULift.ext
    exact walkingAdjunctionHorizontal_rightUnit X Y p.down
  assoc W X Y Z := by
    ext n p
    apply ULift.ext
    exact walkingAdjunctionHorizontal_assoc W X Y Z p.1.down p.2.1.down p.2.2.down

end SerrePositivity.InfinityCategories.HA.Monads

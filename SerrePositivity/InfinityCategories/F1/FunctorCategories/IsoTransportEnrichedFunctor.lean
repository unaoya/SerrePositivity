module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.IsoTransportCategory

/-!
概要：指定された同型の始域と終域の評価を、元の全 Hom に作用する豊穣関手にする。
方針：始域は恒等作用、終域は同じ指定同型による前後合成を使う。
規約：同型と全高次 Hom の作用を選び直さない。
使われ方：結合共役と分類後の Hom 輸送の全局所比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
open CategoryTheory MonoidalCategory
namespace SerrePositivity.InfinityCategories

variable (V : Type u) [Category.{v} V] [MonoidalCategory V]
  (C : Type w) [Category.{z} C] [EnrichedOrdinaryCategory V C]

/-- 始域の同じ全 Hom を、そのまま元の豊穣圏へ評価する。 -/
def isoTransportSourceEnriched : EnrichedFunctor V (IsoTransportObject C) C where
  obj X := X.source
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp X Y Z := by
    change eComp V X.source Y.source Z.source ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 _) ≫ eComp V X.source Y.source Z.source
    simp

/-- 終域の評価は、同じ指定同型による元の全 Hom の共役作用。 -/
def isoTransportTargetEnriched : EnrichedFunctor V (IsoTransportObject C) C where
  obj X := X.target
  map X Y := (Iso.eHomCongr V X.comparison Y.comparison).hom
  map_id X := enrichedHomCongr_identity V X.comparison
  map_comp X Y Z :=
    (enrichedHomCongr_comp_all V X.comparison Y.comparison Z.comparison).symm

end SerrePositivity.InfinityCategories

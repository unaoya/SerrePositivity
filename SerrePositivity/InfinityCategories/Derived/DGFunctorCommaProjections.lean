module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaCategory
/-!
概要：commaの実 dg 圏から、元の入力と実比較対象への二つの dg 関手を構成する。
方針：同じ全 Hom 射影の合成・単位保存を、そのまま豊穣関手へ束ねる。
規約：元の出力の射影性は不要。使われ方：任意の dg 関手の出力の実半自由模型への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
/-- commaの実入力を回収する、全 Hom 射影を持つ実 dg 関手。 -/
def dgFunctorCommaSource :
    DGFunctor R (DGFunctorCommaObject R C E F) C where
  obj X := X.source
  map X Y := dgFunctorCommaSourceHomMap R C E F X Y
  map_id X := dgFunctorCommaIdentity_source R C E F X
  map_comp X Y Z := dgFunctorCommaComposition_source R C E F X Y Z
/-- 同じ分解の実比較対象を回収する、第二実 Hom 射影の dg 関手。 -/
def dgFunctorCommaReplacement :
    DGFunctor R (DGFunctorCommaObject R C E F) E where
  obj X := X.replacement
  map X Y := dgFunctorCommaReplacementHomMap R C E F X Y
  map_id X := dgFunctorCommaIdentity_replacement R C E F X
  map_comp X Y Z := dgFunctorCommaComposition_replacement R C E F X Y Z
end SerrePositivity.InfinityCategories

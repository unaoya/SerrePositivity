module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionCategory
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionProjection
/-!
概要：出力分解の実 dg 圏から、元の入力と実半自由出力への二つの dg 関手を構成する。
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
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 出力分解の実入力を回収する、全 Hom 射影を持つ実 dg 関手。 -/
def dgModuleFunctorResolutionSource :
    DGFunctor R (DGModuleFunctorResolutionObject R C E F) C where
  obj X := X.source
  map X Y := dgModuleFunctorResolutionSourceHomMap R C E F X Y
  map_id X := dgModuleFunctorResolutionIdentity_source R C E F X
  map_comp X Y Z := dgModuleFunctorResolutionComposition_source R C E F X Y Z
/-- 同じ分解の実半自由出力を回収する、第二実 Hom 射影の dg 関手。 -/
def dgModuleFunctorResolutionReplacement :
    DGFunctor R (DGModuleFunctorResolutionObject R C E F) (SemifreeDGModules R E) where
  obj X := X.replacement
  map X Y := dgModuleFunctorResolutionReplacementHomMap R C E F X Y
  map_id X := dgModuleFunctorResolutionIdentity_replacement R C E F X
  map_comp X Y Z := dgModuleFunctorResolutionComposition_replacement R C E F X Y Z
/-- 実入力射影の全 Hom 鎖写像は、すべての整数次数で準同型。 -/
lemma dgModuleFunctorResolutionSource_homQuasiIso :
    HomQuasiIso (dgModuleFunctorResolutionSource R C E F) :=
  dgModuleFunctorResolutionSourceHomMap_quasiIso R C E F
/-- 実入力射影は、実対象上でも全射。 -/
lemma dgModuleFunctorResolutionSource_obj_surjective :
    Function.Surjective (dgModuleFunctorResolutionSource R C E F).obj :=
  dgModuleFunctorResolutionObject_source_surjective R C E F
end SerrePositivity.InfinityCategories

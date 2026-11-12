module
public import SerrePositivity.KST.SConstruction.KCompositionNativeCylinders

/-! # 元の指定区間から端点を合わせた全精密化の三円柱
概要：共通パラメータの三つの元の円柱を、比較三角形の同じ三頂点の間に置く。
方針：指定直通列点の全区間の等号から定数端点の等号を導く。
規約：端点の表示だけを合わせ、全円柱そのものを保持する。
使われ方：全精密化上で全三辺を固定する実比較三角形の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kCompositionNativeFamiliesPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の第一円柱を同じ比較三角形の上頂点から中頂点への族にする。 -/
def kKanCompositionFirstNativeFamily : SSet.Homotopy
    (SSet.const (X := nerve (CompositionStringParameters f g))
      (kKanOriginalCompositionCompatibilityData r F f g).upper)
    (SSet.const (kKanOriginalCompositionCompatibilityData r F f g).middle) :=
  specifiedPointConstantHomotopy (kKanCompositionFirstNativeCylinder r F f g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g))
    (kKanOriginalCompositionCompatibilityData r F f g).first
    (kKanCompositionFirstNativeCylinder_boundary r F f g)

/-- 元の第二円柱を同じ中頂点から下頂点への族にする。 -/
def kKanCompositionSecondNativeFamily : SSet.Homotopy
    (SSet.const (X := nerve (CompositionStringParameters f g))
      (kKanOriginalCompositionCompatibilityData r F f g).middle)
    (SSet.const (kKanOriginalCompositionCompatibilityData r F f g).lower) :=
  specifiedPointConstantHomotopy (kKanCompositionSecondNativeCylinder r F f g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g))
    (kKanOriginalCompositionCompatibilityData r F f g).second
    (kKanCompositionSecondNativeCylinder_boundary r F f g)

/-- 元の合成円柱を同じ上頂点から下頂点への族にする。 -/
def kKanCompositionCompositeNativeFamily : SSet.Homotopy
    (SSet.const (X := nerve (CompositionStringParameters f g))
      (kKanOriginalCompositionCompatibilityData r F f g).upper)
    (SSet.const (kKanOriginalCompositionCompatibilityData r F f g).lower) :=
  specifiedPointConstantHomotopy (kKanCompositionCompositeNativeCylinder r F f g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g))
    (kKanOriginalCompositionCompatibilityData r F f g).composite
    (kKanCompositionCompositeNativeCylinder_boundary r F f g)

/-- 端点を合わせても、元の第一適合区間の全体を同じ指定点で回収する。 -/
lemma kKanCompositionFirstNativeFamily_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
        (kKanCompositionFirstNativeFamily r F f g).h =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityData r F f g).first.edge :=
  kKanCompositionFirstNativeCylinder_boundary r F f g

/-- 元の第二適合区間の全体も、同じ指定点で回収する。 -/
lemma kKanCompositionSecondNativeFamily_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
        (kKanCompositionSecondNativeFamily r F f g).h =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityData r F f g).second.edge :=
  kKanCompositionSecondNativeCylinder_boundary r F f g

/-- 元の合成適合区間の全体も、同じ指定点で回収する。 -/
lemma kKanCompositionCompositeNativeFamily_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
        (kKanCompositionCompositeNativeFamily r F f g).h =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        SSet.yonedaEquiv.symm (kKanOriginalCompositionCompatibilityData r F f g).composite.edge :=
  kKanCompositionCompositeNativeCylinder_boundary r F f g

end SerrePositivity.KST.SConstruction

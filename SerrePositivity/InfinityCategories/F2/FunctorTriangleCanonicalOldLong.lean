module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleLongNaturality
public import SerrePositivity.InfinityCategories.F2.FunctorHomotopyRestrictedData

/-!
概要：元の指定三角形の長辺比較を、F1 指定比較の同じ制限データへ値を保って移す。
方針：元の実延長・実終点を保持し、底・全初期値・終点底の表示だけを揃える。
規約：元の指定値を保持。使われ方：長辺の自然性から元の指定三角形比較を回収する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "Z" => functorHomotopySourceCanonicalWitness c p s hi
local notation "Y" => FunctorTrianglePointedWitness.longWitness
  (functorTrianglePointedCanonicalWitness T p s hi)
local notation "hb" => Eq.trans (Eq.symm (RelativeExtensionEndpointWitness.over Z))
  (functorHomotopyRestricted_base c s)
local notation "hv" => Eq.symm (functorHomotopyRestricted_initial s)
local notation "ha" => Eq.trans (Eq.symm hi) (Eq.symm (functorHomotopyRestricted_apex s))

/-- 元の同じ普遍長辺と指定三角形の長辺を、F1 指定比較の同じ実データで保持する。 -/
def functorTriangleCanonicalOldLongWitness (original : Bool) :=
  (if original then Y else Z).transportData hb hv ha

/-- 元の F1 の制限データで表示した、同じ元の二長辺証拠の指定比較。 -/
def functorTriangleCanonicalOldLongIso :=
  (functorTriangleCanonicalOldLongWitness T p s hi false).iso
    (functorTriangleCanonicalOldLongWitness T p s hi true) (prismEndpoint_zero_leftAnodyne C)
    (functorTriangleCanonicalOldLongWitness T p s hi true).initial_base
    (functorTriangleCanonicalOldLongWitness T p s hi true).endpoint_base

/-- 元の同じ実延長・実終点の底の表示変更は、元の長辺の指定比較の値を保つ。 -/
lemma functorTriangleCanonicalLongSourceIso_heq_old :
    HEq (functorHomotopySourceEndpointIso c p s hi Y)
      (functorTriangleCanonicalOldLongIso T p s hi) :=
  RelativeExtensionEndpointWitness.iso_heq_of_dataEq Z Y
    (functorTriangleCanonicalOldLongWitness T p s hi false)
    (functorTriangleCanonicalOldLongWitness T p s hi true) hb hv ha rfl rfl rfl rfl
    (prismEndpoint_zero_leftAnodyne C) (Y).initial_base
    (functorTriangleCanonicalOldLongWitness T p s hi true).initial_base (Y).endpoint_base
    (functorTriangleCanonicalOldLongWitness T p s hi true).endpoint_base

end SerrePositivity.InfinityCategories.F2

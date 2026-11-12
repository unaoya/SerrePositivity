module
public import SerrePositivity.KST.SConstruction.NecklaceCubeMonoidalCoherence
public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # 元の全 necklace 射の具体的 cube 値強モノイダル関手
概要：元の wedge と一点単位を保つ、全 necklace 射の cube 関手を束ねる。
方針：元の二変数自然同型と結合・左右単位の coherent 法則をそのまま使う。
規約：tensorator は元の比較。使われ方：Day 上の cubical 合成と Serre 鎖の延長。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory

/-- 元の全 necklace 射と元の tensor・単位比較を持つ、モノイダルなデータ。 -/
def necklaceCubeCoreMonoidal : (necklaceConcreteCube.{u}).CoreMonoidal where
  εIso := necklaceCubeUnitIso.{u}
  μIso := necklaceCubeTensorIso
  μIso_hom_natural_left := by
    intro X Y f Z
    change concreteCubeTensorMap (necklaceConcreteCubeMap f)
        (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk Z.down.dimension)) ≫ (necklaceCubeTensorIso Y Z).hom =
      (necklaceCubeTensorIso X Z).hom ≫ necklaceConcreteCubeMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f (𝟙 Z))
    have hid : necklaceConcreteCubeMap (𝟙 Z) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk Z.down.dimension) :=
      necklaceConcreteCube.map_id Z
    simpa only [hid] using necklaceCubeTensorIso_naturality f (𝟙 Z)
  μIso_hom_natural_right := by
    intro X Y Z f
    change concreteCubeTensorMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk Z.down.dimension))
        (necklaceConcreteCubeMap f) ≫ (necklaceCubeTensorIso Z Y).hom =
      (necklaceCubeTensorIso Z X).hom ≫ necklaceConcreteCubeMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap (𝟙 Z) f)
    have hid : necklaceConcreteCubeMap (𝟙 Z) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk Z.down.dimension) :=
      necklaceConcreteCube.map_id Z
    simpa only [hid] using necklaceCubeTensorIso_naturality (𝟙 Z) f
  associativity := necklaceCubeTensor_associativity
  left_unitality := necklaceCubeTensor_left_unitality
  right_unitality := necklaceCubeTensor_right_unitality

/-- 元の wedge・全射・構造同型を保つ具体的 cube 値強モノイダル関手。 -/
instance necklaceCubeMonoidal : (necklaceConcreteCube.{u}).Monoidal :=
  necklaceCubeCoreMonoidal.{u}.toMonoidal

/-- 元の tensorator をモノイダル関手から厳密に回収する。 -/
lemma necklaceCubeMonoidal_tensorator (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    Functor.LaxMonoidal.μ necklaceConcreteCube T U = (necklaceCubeTensorIso T U).hom := rfl

/-- 元の逆 tensor 比較をモノイダル関手から厳密に回収する。 -/
lemma necklaceCubeMonoidal_cotensorator (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    Functor.OplaxMonoidal.δ necklaceConcreteCube T U = (necklaceCubeTensorIso T U).inv := rfl

/-- 元の単位比較をモノイダル関手から厳密に回収する。 -/
lemma necklaceCubeMonoidal_unit :
    Functor.LaxMonoidal.ε necklaceConcreteCube.{u} = necklaceCubeUnitIso.{u}.hom := rfl

/-- 元の逆単位比較をモノイダル関手から厳密に回収する。 -/
lemma necklaceCubeMonoidal_counit :
    Functor.OplaxMonoidal.η necklaceConcreteCube.{u} = necklaceCubeUnitIso.{u}.inv := rfl

end SerrePositivity.KST.SConstruction

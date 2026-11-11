module
public import SerrePositivity.KST.SConstruction.NecklaceCubeMonoidal
public import SerrePositivity.KST.SConstruction.NecklaceCubicalTensorComparison
public import SerrePositivity.KST.SConstruction.CubicalDayYonedaMonoidal

/-! # 元の necklace の Day 値強モノイダル関手
概要：native wedge の全構造を、元の表現可能 cubical set の Day tensor へ送る。
方針：元の cube 関手と元の強モノイダル Yoneda を合成する。
規約：元の全射と正逆の tensor・単位比較を回収。使われ方：cubical 余極限の合成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory

/-- 元の全 necklace 射の cubical 関手を、Day モノイダル圏で読む。 -/
def necklaceCubicalDay : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} ⥤ CubicalDaySet.{u} :=
  necklaceConcreteCube ⋙ cubicalDayYoneda

/-- 元の比較を持つ二つの強モノイダル関手の合成。 -/
instance necklaceCubicalDayMonoidal : necklaceCubicalDay.{u}.Monoidal :=
  inferInstanceAs ((necklaceConcreteCube.{u} ⋙ cubicalDayYoneda.{u}).Monoidal)

/-- 元の対象の cubical set を厳密に回収する。 -/
lemma necklaceCubicalDay_obj (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    (necklaceCubicalDay.obj T).functor = necklaceCubicalSet.obj T := rfl

/-- 元の全 necklace 射の cubical 作用を厳密に回収する。 -/
lemma necklaceCubicalDay_map {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) :
    (necklaceCubicalDay.map f).natTrans = necklaceCubicalSet.map f := rfl

/-- 元の Day tensor 比較の正方向を厳密に回収する。 -/
lemma necklaceCubicalDay_tensorator (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    (Functor.LaxMonoidal.μ necklaceCubicalDay T U).natTrans =
      (necklaceCubicalTensorIso T U).hom := rfl

/-- 元の Day tensor 比較の逆方向を厳密に回収する。 -/
lemma necklaceCubicalDay_cotensorator (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    (Functor.OplaxMonoidal.δ necklaceCubicalDay T U).natTrans =
      (necklaceCubicalTensorIso T U).inv := rfl

/-- 元の Day 単位と元の零次元 cube の比較を、同じ合成として回収する。 -/
lemma necklaceCubicalDay_unit :
    (Functor.LaxMonoidal.ε necklaceCubicalDay.{u}).natTrans =
      cubicalDayUnitProjection ≫ cubicalYoneda.map necklaceCubeUnitIso.{u}.hom := rfl

/-- 元の逆単位比較も、同じ二つの元の射の合成として回収する。 -/
lemma necklaceCubicalDay_counit :
    (Functor.OplaxMonoidal.η necklaceCubicalDay.{u}).natTrans =
      cubicalYoneda.map necklaceCubeUnitIso.{u}.inv ≫ cubicalDayUnitInclusion := rfl

/-- 元の全 cell 上で、強モノイダル構造は既存の Day 比較と同じ具体的射を回収する。 -/
lemma necklaceCubicalDay_tensorator_cell (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (a b : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (p : a ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.down.dimension) (q : b ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk U.down.dimension) :
    (Functor.LaxMonoidal.μ necklaceCubicalDay T U).natTrans.app
        (Opposite.op (concreteCubeTensorObj a b))
        (cubicalDayTensorCell a b (ULift.up p) (ULift.up q)) =
      ULift.up (concreteCubeTensorMap p q ≫ (necklaceCubeTensorIso T U).hom) :=
  necklaceCubicalTensorIso_cell T U a b p q

end SerrePositivity.KST.SConstruction

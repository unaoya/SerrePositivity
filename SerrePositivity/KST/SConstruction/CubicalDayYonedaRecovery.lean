module
public import SerrePositivity.KST.SConstruction.CubicalDayYonedaMonoidal

/-! # 強モノイダル Yoneda の元の cell 作用の回収
概要：元の具体的射・連結射・零次元単位を、構成したモノイダル関手から回収する。
方針：同じ関手と同じ比較射の定義を照合し、元の cell 評価式を使う。
規約：比較を別の選択同型に置換しない。使われ方：元の necklace と Day tensor の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite

/-- 強モノイダル Yoneda の元の射への作用は、同じ underlying Yoneda 射。 -/
lemma cubicalDayYoneda_map_natTrans {c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : c ⟶ d) :
    (cubicalDayYoneda.{u}.map f).natTrans = cubicalYoneda.map f := rfl

/-- 強モノイダル Yoneda の tensorator は、元の表現可能 Day tensor 比較。 -/
lemma cubicalDayYoneda_tensorator_natTrans (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (Functor.LaxMonoidal.μ cubicalDayYoneda.{u} c d).natTrans =
      cubicalDayCubeProjection c d := rfl

/-- 強モノイダル Yoneda の単位射は、元の零次元比較射。 -/
lemma cubicalDayYoneda_unit_natTrans :
    (Functor.LaxMonoidal.ε cubicalDayYoneda.{u}).natTrans = cubicalDayUnitProjection := rfl

/-- 強モノイダル Yoneda の逆 tensorator は、元の恒等 cell の連結の Yoneda 射。 -/
lemma cubicalDayYoneda_cotensorator_natTrans (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (Functor.OplaxMonoidal.δ cubicalDayYoneda.{u} c d).natTrans =
      cubicalDayCubeInclusion c d := rfl

/-- 強モノイダル Yoneda の逆単位射は、元の Day 単位の生成 cell の Yoneda 射。 -/
lemma cubicalDayYoneda_counit_natTrans :
    (Functor.OplaxMonoidal.η cubicalDayYoneda.{u}).natTrans = cubicalDayUnitInclusion := rfl

/-- 元の連結 cell 上で、強モノイダル Yoneda の tensorator は同じ具体的 tensor 射を回収。 -/
lemma cubicalDayYoneda_tensorator_cell (c d a b : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : a ⟶ c) (y : b ⟶ d) :
    (Functor.LaxMonoidal.μ cubicalDayYoneda.{u} c d).natTrans.app
        (op (concreteCubeTensorObj a b))
        (cubicalDayTensorCell a b (ULift.up x) (ULift.up y)) =
      ULift.up (concreteCubeTensorMap x y) :=
  cubicalDayCubeProjection_cell c d a b x y

/-- 強モノイダル Yoneda は元の具体的射に関して忠実。 -/
instance cubicalDayYoneda_faithful : cubicalDayYoneda.{u}.Faithful := by
  dsimp only [cubicalDayYoneda, cubicalYoneda, cubicalDayEquivalence]
  infer_instance

/-- 強モノイダル Yoneda は元の表現可能立方体の射を全て回収する。 -/
instance cubicalDayYoneda_full : cubicalDayYoneda.{u}.Full := by
  dsimp only [cubicalDayYoneda, cubicalYoneda, cubicalDayEquivalence]
  infer_instance

end SerrePositivity.KST.SConstruction

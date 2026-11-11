module
public import SerrePositivity.KST.SConstruction.CubicalDayRepresentable
public import SerrePositivity.KST.SConstruction.CubicalDayTensorLaws

/-! # 元の表現可能 Day tensor 比較の二変数自然性
概要：表現可能立方体の Day tensor 比較が、両因子の全具体的射と可換となる。
方針：元の全連結 cell で、元の二つの射の合成を厳密に回収する。
規約：全前層上の射と元の Yoneda 射を使う。使われ方：cubical 合成の元の連結との比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite

/-- 表現可能 Day tensor の比較は元の両因子の具体的射について自然。 -/
lemma cubicalDayCubeProjection_naturality {c c' d d' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : c ⟶ c') (g : d ⟶ d') :
    cubicalDayTensorMap (cubicalYoneda.{u}.map f) (cubicalYoneda.map g) ≫
        cubicalDayCubeProjection c' d' =
      cubicalDayCubeProjection c d ≫ cubicalYoneda.map (concreteCubeTensorMap f g) := by
  apply cubicalDayTensor_cell_hom_ext
  intro a b x y
  change (cubicalDayCubeProjection c' d').app (op (concreteCubeTensorObj a b))
      ((cubicalDayTensorMap (cubicalYoneda.map f) (cubicalYoneda.map g)).app
        (op (concreteCubeTensorObj a b)) (cubicalDayTensorCell a b x y)) =
    (cubicalYoneda.map (concreteCubeTensorMap f g)).app (op (concreteCubeTensorObj a b))
      ((cubicalDayCubeProjection c d).app (op (concreteCubeTensorObj a b))
        (cubicalDayTensorCell a b x y))
  erw [cubicalDayTensorMap_cell]
  change (cubicalDayCubeProjection c' d').app (op (concreteCubeTensorObj a b))
      (cubicalDayTensorCell a b (ULift.up (x.down ≫ f)) (ULift.up (y.down ≫ g))) =
    ULift.up (((cubicalDayCubeProjection c d).app (op (concreteCubeTensorObj a b))
      (cubicalDayTensorCell a b x y)).down ≫ concreteCubeTensorMap f g)
  erw [cubicalDayCubeProjection_cell, cubicalDayCubeProjection_cell c d a b x.down y.down]
  exact congrArg ULift.up (concreteCubeTensorMap_comp x.down f y.down g)

/-- 元の全前層と元の射からなる Day tensor の二変数関手。 -/
def cubicalDayTensorFunctor : CubicalSet.{u} × CubicalSet.{u} ⥤ CubicalSet.{u} where
  obj P := cubicalDayTensor P.1 P.2
  map f := cubicalDayTensorMap f.1 f.2
  map_id P := cubicalDayTensorMap_id P.1 P.2
  map_comp f g := cubicalDayTensorMap_comp f.1 g.1 f.2 g.2

/-- 元の二つの表現可能立方体の Day tensor 比較を、二変数の自然同型へ束ねる。 -/
def cubicalDayYonedaTensorIso :
    cubicalYoneda.{u}.prod cubicalYoneda ⋙ cubicalDayTensorFunctor ≅
      concreteCubeTensor ⋙ cubicalYoneda :=
  NatIso.ofComponents (fun P => cubicalDayCubeIso P.1 P.2)
    (fun f => cubicalDayCubeProjection_naturality f.1 f.2)

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.CubicalDayRepresentableNaturality
public import SerrePositivity.KST.SConstruction.CubicalDayUnit

/-! # 元の Yoneda 関手と Day tensor 比較のデータ
概要：元の cubical Yoneda 関手を Day 圏へ移し、同じ表現可能 tensor・単位同型を持たせる。
方針：元の前層の射を包み、元の両逆律と二変数自然性を使う。
規約：関手・比較の underlying 前層は元のまま。使われ方：強モノイダル Yoneda の構成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite

/-- 元の表現可能立方体を Day モノイダル圏へ送る Yoneda 関手。 -/
def cubicalDayYoneda : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube ⥤ CubicalDaySet.{u} :=
  cubicalYoneda ⋙ cubicalDayEquivalence.inverse

/-- Day 圏に移した元の表現可能 tensor 比較同型。 -/
def cubicalDayYonedaTensor (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (cubicalDayYoneda.{u}).obj c ⊗ cubicalDayYoneda.obj d ≅
      cubicalDayYoneda.obj (concreteCubeTensorObj c d) where
  hom := .mk (cubicalDayCubeProjection c d)
  inv := .mk (cubicalDayCubeInclusion c d)
  hom_inv_id := DayFunctor.hom_ext (cubicalDayCubeProjection_inclusion c d)
  inv_hom_id := DayFunctor.hom_ext (cubicalDayCubeInclusion_projection c d)

/-- Day 圏に移した元の零次元単位比較同型。 -/
def cubicalDayYonedaUnit : 𝟙_ CubicalDaySet.{u} ≅
    cubicalDayYoneda.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) where
  hom := .mk cubicalDayUnitProjection
  inv := .mk cubicalDayUnitInclusion
  hom_inv_id := DayFunctor.hom_ext cubicalDayUnitProjection_inclusion
  inv_hom_id := DayFunctor.hom_ext cubicalDayUnitInclusion_projection

/-- 元の表現可能 tensor の逆比較も、元の両具体的射について自然。 -/
lemma cubicalDayCubeInclusion_naturality {c c' d d' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : c ⟶ c') (g : d ⟶ d') :
    cubicalDayCubeInclusion.{u} c d ≫
        cubicalDayTensorMap (cubicalYoneda.map f) (cubicalYoneda.map g) =
      cubicalYoneda.map (concreteCubeTensorMap f g) ≫ cubicalDayCubeInclusion c' d' := by
  have h := cubicalDayYonedaTensorIso.{u}.inv.naturality
    (show (c, d) ⟶ (c', d') from (f, g))
  exact h.symm

/-- 元の連結立方体の恒等 cell を、元の二つの恒等 cell の連結へ戻す。 -/
lemma cubicalDayCubeInclusion_identity (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (cubicalDayCubeInclusion.{u} c d).app (op (concreteCubeTensorObj c d))
        (ULift.up (𝟙 (concreteCubeTensorObj c d))) =
      cubicalDayTensorCell c d (ULift.up (𝟙 c)) (ULift.up (𝟙 d)) := by
  change (cubicalDayTensor (cubicalYoneda.obj c) (cubicalYoneda.obj d)).map
    (𝟙 (concreteCubeTensorObj c d)).op _ = _
  simp

/-- 元の零次元恒等 cell を Day 単位の生成 cell へ戻す。 -/
lemma cubicalDayUnitInclusion_identity :
    cubicalDayUnitInclusion.{u}.app (op (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0))
      (ULift.up (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0))) = cubicalDayUnitCell := by
  change cubicalDayUnit.map (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)).op _ = _
  simp

/-- 元の cubical 前層の射と、具体的射による制限の可換性。 -/
lemma cubicalNatTrans_restrict {K L : CubicalSet.{u}} (t : K ⟶ L)
    {a b : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (h : a ⟶ b) (x : K.obj (op b)) :
    t.app (op a) (K.map h.op x) = L.map h.op (t.app (op b) x) :=
  congrArg (fun f => f x) (t.naturality h.op)

end SerrePositivity.KST.SConstruction

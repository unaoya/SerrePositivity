module
public import SerrePositivity.KST.SConstruction.CubicalDayYonedaAssociativity
public import SerrePositivity.KST.SConstruction.CubicalDayYonedaUnitCoherence

/-! # 元の連結積を保持する強モノイダル Yoneda 関手
概要：元の表現可能 tensor・単位の比較を、結合と左右単位を保つ関手へ束ねる。
方針：表現可能始域で検証した逆比較の自然性・結合・単位の法則を適用する。
規約：元の cell に作用する同じ Yoneda 関手を使う。使われ方：cubical 合成と鎖の延長。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory

/-- 元の表現可能 tensor・単位同型と全 coherent 法則を持つ Yoneda のデータ。 -/
def cubicalDayYonedaCoreMonoidal : cubicalDayYoneda.{u}.CoreMonoidal :=
  Functor.CoreMonoidal.mk' (F := cubicalDayYoneda.{u})
    cubicalDayYonedaUnit.{u} cubicalDayYonedaTensor.{u}
    (μIso_inv_natural_left := by
      intro X Y f X'
      rw [← MonoidalCategory.tensorHom_id]
      apply DayFunctor.hom_ext
      change cubicalDayCubeInclusion.{u} X X' ≫
          cubicalDayTensorMap (cubicalYoneda.{u}.map f) (𝟙 (cubicalYoneda.{u}.obj X')) =
        cubicalYoneda.{u}.map (concreteCubeTensorMap f (𝟙 X')) ≫ cubicalDayCubeInclusion Y X'
      have h := cubicalDayCubeInclusion_naturality.{u} f (𝟙 X')
      simpa only [CategoryTheory.Functor.map_id] using h)
    (μIso_inv_natural_right := by
      intro X Y X' f
      rw [← MonoidalCategory.id_tensorHom]
      apply DayFunctor.hom_ext
      change cubicalDayCubeInclusion.{u} X' X ≫
          cubicalDayTensorMap (𝟙 (cubicalYoneda.{u}.obj X')) (cubicalYoneda.{u}.map f) =
        cubicalYoneda.{u}.map (concreteCubeTensorMap (𝟙 X') f) ≫ cubicalDayCubeInclusion X' Y
      have h := cubicalDayCubeInclusion_naturality.{u} (𝟙 X') f
      simpa only [CategoryTheory.Functor.map_id] using h)
    (oplax_associativity := by
      intro X Y Z
      apply DayFunctor.hom_ext
      exact cubicalDayCubeInclusion_associativity X Y Z)
    (oplax_left_unitality := by
      intro X
      apply (cancel_mono (λ_ (cubicalDayYoneda.{u}.obj X)).hom).mp
      rw [Iso.inv_hom_id]
      apply DayFunctor.hom_ext
      change 𝟙 (cubicalYoneda.{u}.obj X) =
        (cubicalYoneda.{u}.map (concreteCubeLeftUnitor X).inv ≫
          cubicalDayCubeInclusion (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) X ≫
            cubicalDayTensorMap cubicalDayUnitInclusion (𝟙 (cubicalYoneda.{u}.obj X))) ≫
          (λ_ (DayFunctor.mk (cubicalYoneda.{u}.obj X))).hom.natTrans
      erw [Category.assoc, Category.assoc]
      exact (cubicalDayYoneda_leftUnit_retraction.{u} X).symm)
    (oplax_right_unitality := by
      intro X
      apply (cancel_mono (ρ_ (cubicalDayYoneda.{u}.obj X)).hom).mp
      rw [Iso.inv_hom_id]
      apply DayFunctor.hom_ext
      change 𝟙 (cubicalYoneda.{u}.obj X) =
        (cubicalYoneda.{u}.map (concreteCubeRightUnitor X).inv ≫
          cubicalDayCubeInclusion X (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) ≫
            cubicalDayTensorMap (𝟙 (cubicalYoneda.{u}.obj X)) cubicalDayUnitInclusion) ≫
          (ρ_ (DayFunctor.mk (cubicalYoneda.{u}.obj X))).hom.natTrans
      erw [Category.assoc, Category.assoc]
      exact (cubicalDayYoneda_rightUnit_retraction.{u} X).symm)

/-- 元の具体的連結積を Day tensor へ移す強モノイダル Yoneda 関手。 -/
instance cubicalDayYonedaMonoidal : cubicalDayYoneda.{u}.Monoidal :=
  cubicalDayYonedaCoreMonoidal.{u}.toMonoidal

end SerrePositivity.KST.SConstruction

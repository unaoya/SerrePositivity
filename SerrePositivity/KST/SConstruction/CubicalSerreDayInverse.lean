module
public import SerrePositivity.KST.SConstruction.CubicalSerreTensorColimit
public import SerrePositivity.KST.SConstruction.CubicalSerreDayAssembly

/-! # 全 cubical sets 上の Day 鎖比較の逆射
概要：元の両 cell の組み立てを、鎖複体の tensor 全体からの射へ降ろす。
方針：元の両立方体の独立な余極限と tensor の各変数の余極限保存を使う。
規約：元の比較射を変更しない。使われ方：全体の同型性と強モノイダル法則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全ての独立な両立方体の鎖を、連結 cell に送る余錐。 -/
def cubicalSerreDayAssemblyCocone (K L : CubicalSet.{u}) :
    Cocone (externalProduct (cubicalSerreDiagram A K) (cubicalSerreDiagram A L)) where
  pt := (cubicalSerreChains A).obj (cubicalDayTensor K L)
  ι :=
    { app := fun j => cubicalSerreDayAssembly A j.1.left j.2.left
        (uliftYonedaEquiv j.1.hom) (uliftYonedaEquiv j.2.hom)
      naturality := fun j k f => by
        dsimp only [externalProduct, externalProductBifunctor_obj_map,
          Functor.const_obj_map, cubicalSerreDiagram, Functor.comp_map,
          CostructuredArrow.proj_map]
        rw [← tensorHom_def]
        change ((serreConcreteCubeComplexFunctor A).map f.1.left ⊗ₘ
            (serreConcreteCubeComplexFunctor A).map f.2.left) ≫
            cubicalSerreDayAssembly A k.1.left k.2.left
              (uliftYonedaEquiv k.1.hom) (uliftYonedaEquiv k.2.hom) =
          cubicalSerreDayAssembly A j.1.left j.2.left
              (uliftYonedaEquiv j.1.hom) (uliftYonedaEquiv j.2.hom) ≫ 𝟙 _
        rw [Category.comp_id, cubicalSerreDayAssembly_restrict]
        have hx : K.map f.1.left.op (uliftYonedaEquiv k.1.hom) =
            uliftYonedaEquiv j.1.hom := by
          erw [uliftYonedaEquiv_naturality, CostructuredArrow.w f.1]
        have hy : L.map f.2.left.op (uliftYonedaEquiv k.2.hom) =
            uliftYonedaEquiv j.2.hom := by
          erw [uliftYonedaEquiv_naturality, CostructuredArrow.w f.2]
        rw [hx, hy] }

/-- 元の両鎖複体の tensor から、元の Day tensor の鎖への比較の逆射。 -/
def cubicalSerreDayInverse (K L : CubicalSet.{u}) :
    (cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj L ⟶
      (cubicalSerreChains A).obj (cubicalDayTensor K L) :=
  (cubicalSerreTensorIsColimit A K L).desc (cubicalSerreDayAssemblyCocone A K L)

/-- 全体の逆射は、元の全ての両 cell 上の組み立てを回収する。 -/
lemma cubicalSerreDayInverse_cell {K L : CubicalSet.{u}}
    (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) (y : L.obj (op d)) :
    (cubicalSerreCell A c x ⊗ₘ cubicalSerreCell A d y) ≫
        cubicalSerreDayInverse A K L = cubicalSerreDayAssembly A c d x y := by
  have h := (cubicalSerreTensorIsColimit A K L).fac
    (cubicalSerreDayAssemblyCocone A K L)
    (CostructuredArrow.mk (cubicalCell c x), CostructuredArrow.mk (cubicalCell d y))
  rw [cubicalSerreTensorCocone_leg] at h
  change (cubicalSerreCell A c x ⊗ₘ cubicalSerreCell A d y) ≫
    cubicalSerreDayInverse A K L = cubicalSerreDayAssembly A c d
      (uliftYonedaEquiv (cubicalCell c x)) (uliftYonedaEquiv (cubicalCell d y)) at h
  simpa only [cubicalCell, Equiv.apply_symm_apply] using h

end SerrePositivity.KST.SConstruction

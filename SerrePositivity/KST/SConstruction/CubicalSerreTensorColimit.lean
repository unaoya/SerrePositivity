module
public import SerrePositivity.KST.SConstruction.CubicalSerreGenerators
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-! # 元の両 cell の tensor による Serre 鎖の表示
概要：二つの鎖複体の tensor を、元の両立方体の鎖の tensor の余極限として表す。
方針：元の生成射の余錐と閉モノイダル構造による各変数の余極限保存を使う。
規約：二つの立方体添字は独立。使われ方：Day 鎖比較の逆射と逆律の構成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 四対象を固定した、元の両 cell の鎖射の tensor。 -/
def cubicalSerreCellTensor {K L : CubicalSet.{u}} (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op c)) (y : L.obj (op d)) :
    (serreConcreteCubeComplexFunctor A).obj c ⊗
        (serreConcreteCubeComplexFunctor A).obj d ⟶
      (cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj L :=
  @tensorHom (Complex A) _ _
    ((serreConcreteCubeComplexFunctor A).obj c) ((cubicalSerreChains A).obj K)
    ((serreConcreteCubeComplexFunctor A).obj d) ((cubicalSerreChains A).obj L)
    (cubicalSerreCell A c x) (cubicalSerreCell A d y)

/-- 元の全生成射を脚とする、元の鎖複体への余錐。 -/
def cubicalSerreGeneratingCocone (K : CubicalSet.{u}) :
    Cocone (cubicalSerreDiagram A K) :=
  cubicalSerreCocone A K ((cubicalSerreChains A).obj K)
    (fun _ φ => cubicalSerreGenerator A φ)
    (fun f φ => cubicalSerreGenerator_relation A f φ)

/-- 元の生成余錐は余極限。 -/
def cubicalSerreGeneratingIsColimit (K : CubicalSet.{u}) :
    IsColimit (cubicalSerreGeneratingCocone A K) := by
  exact Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit cubicalYoneda
    (serreConcreteCubeComplexFunctor A) K

/-- 元の独立な両立方体による、鎖複体の tensor の余極限表示。 -/
def cubicalSerreTensorIsColimit (K L : CubicalSet.{u}) :
    IsColimit ((cubicalSerreGeneratingCocone A K).tensor₂
      (cubicalSerreGeneratingCocone A L)) :=
  (cubicalSerreGeneratingIsColimit A K).tensor₂ (cubicalSerreGeneratingIsColimit A L)

/-- 元の tensor 余錐の脚は、元の両生成射の tensor。 -/
lemma cubicalSerreTensorCocone_leg (K L : CubicalSet.{u})
    (j : CostructuredArrow cubicalYoneda K) (k : CostructuredArrow cubicalYoneda L) :
    ((cubicalSerreGeneratingCocone A K).tensor₂
        (cubicalSerreGeneratingCocone A L)).ι.app (j, k) =
      cubicalSerreGenerator A j.hom ⊗ₘ cubicalSerreGenerator A k.hom := by
  exact (tensorHom_def _ _).symm

/-- 元の全ての両 cell の tensor への制限で射を判定する。 -/
lemma cubicalSerreTensor_hom_ext {K L : CubicalSet.{u}} {T : Complex A}
    {f g : (cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj L ⟶ T}
    (h : ∀ (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) (y : L.obj (op d)),
      cubicalSerreCellTensor A c d x y ≫ f =
        cubicalSerreCellTensor A c d x y ≫ g) : f = g := by
  apply (cubicalSerreTensorIsColimit A K L).hom_ext
  intro j
  rw [cubicalSerreTensorCocone_leg]
  dsimp only [externalProduct, externalProductBifunctor_obj_obj, cubicalSerreDiagram,
    Functor.comp_obj, CostructuredArrow.proj_obj]
  have hx := h j.1.left j.2.left (uliftYonedaEquiv j.1.hom) (uliftYonedaEquiv j.2.hom)
  dsimp only [cubicalSerreCellTensor, cubicalSerreCell] at hx
  erw [cubicalCell_equiv, cubicalCell_equiv] at hx
  exact hx

end SerrePositivity.KST.SConstruction

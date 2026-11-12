module
public import SerrePositivity.KST.SConstruction.CubicalSerreTensorColimit

/-! # 三つの独立な cell による鎖 tensor の射の判定
概要：左結合した三つの Serre 鎖の tensor からの射を元の全三 cell で判定する。
方針：独立な生成余錐の tensor の余極限表示をもう一度適用する。
規約：因子順と左結合を固定。使われ方：Day 鎖比較の結合整合性の証明。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の三つの cell の左結合した鎖射の tensor。 -/
def cubicalSerreCellTriple {K L M : CubicalSet.{u}} (a b c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op a)) (y : L.obj (op b)) (z : M.obj (op c)) :
    ((serreConcreteCubeComplexFunctor A).obj a ⊗
        (serreConcreteCubeComplexFunctor A).obj b) ⊗
          (serreConcreteCubeComplexFunctor A).obj c ⟶
      ((cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj L) ⊗
        (cubicalSerreChains A).obj M :=
  @tensorHom (Complex A) _ _
    ((serreConcreteCubeComplexFunctor A).obj a ⊗ (serreConcreteCubeComplexFunctor A).obj b)
    ((cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj L)
    ((serreConcreteCubeComplexFunctor A).obj c) ((cubicalSerreChains A).obj M)
    (cubicalSerreCellTensor A a b x y) (cubicalSerreCell A c z)

/-- 元の独立な三つの生成余錐の tensor は余極限。 -/
def cubicalSerreTripleIsColimit (K L M : CubicalSet.{u}) :
    IsColimit (((cubicalSerreGeneratingCocone A K).tensor₂
      (cubicalSerreGeneratingCocone A L)).tensor₂ (cubicalSerreGeneratingCocone A M)) :=
  (cubicalSerreTensorIsColimit A K L).tensor₂ (cubicalSerreGeneratingIsColimit A M)

/-- 三つの元の生成射による、左結合した tensor 余錐の脚。 -/
lemma cubicalSerreTripleCocone_leg (K L M : CubicalSet.{u})
    (j : CostructuredArrow cubicalYoneda K) (k : CostructuredArrow cubicalYoneda L)
    (l : CostructuredArrow cubicalYoneda M) :
    (((cubicalSerreGeneratingCocone A K).tensor₂
        (cubicalSerreGeneratingCocone A L)).tensor₂
          (cubicalSerreGeneratingCocone A M)).ι.app ((j, k), l) =
      (cubicalSerreGenerator A j.hom ⊗ₘ cubicalSerreGenerator A k.hom) ⊗ₘ
        cubicalSerreGenerator A l.hom := by
  change (_ ▷ _ ≫ _ ◁ _) = _
  rw [← tensorHom_def, cubicalSerreTensorCocone_leg]
  rfl

/-- 元の独立な三つの鎖 cell による射の判定。 -/
lemma cubicalSerreTriple_hom_ext {K L M : CubicalSet.{u}} {T : Complex A}
    {f g : ((cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj L) ⊗
      (cubicalSerreChains A).obj M ⟶ T}
    (h : ∀ (a b c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op a)) (y : L.obj (op b))
      (z : M.obj (op c)), cubicalSerreCellTriple A a b c x y z ≫ f =
        cubicalSerreCellTriple A a b c x y z ≫ g) : f = g := by
  apply (cubicalSerreTripleIsColimit A K L M).hom_ext
  intro j
  rw [cubicalSerreTripleCocone_leg]
  dsimp only [externalProduct, externalProductBifunctor_obj_obj, cubicalSerreDiagram,
    Functor.comp_obj, CostructuredArrow.proj_obj]
  have hx := h j.1.1.left j.1.2.left j.2.left (uliftYonedaEquiv j.1.1.hom)
    (uliftYonedaEquiv j.1.2.hom) (uliftYonedaEquiv j.2.hom)
  dsimp only [cubicalSerreCellTriple, cubicalSerreCellTensor, cubicalSerreCell] at hx
  erw [cubicalCell_equiv, cubicalCell_equiv, cubicalCell_equiv] at hx
  exact hx

end SerrePositivity.KST.SConstruction

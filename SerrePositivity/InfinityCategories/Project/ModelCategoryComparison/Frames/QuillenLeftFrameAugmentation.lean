module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.ChosenQuillenFrameHom
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.FixedQuillenFrameComparison

/-!
概要：元の Quillen 左像 frame の全族を左導来像の関手上へ augment し、標準解消と比較する。
方針：元の augmentation の左像を自然変換へ束ね、同じ共通 frame の二つの Hom 射を使う。
規約：元の置換・比較射を保持。使われ方：導来 Hom 随伴の二変数の自然な比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u vC vD
open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
noncomputable section
variable {C : Type vC} [Category.{u} C] [ModelCategory C]
  {D : Type vD} [Category.{u} D]
  (L : C ⥤ D) (P : CosimplicialFrameFamily (C := C)) (Q : C ⥤ C)

/-- 元の全族の augmentation の左像は、同じ左像の関手上の自然な augmentation である。 -/
def quillenLeftFrameAugmentation :
    (Q ⋙ P.obj) ⋙ (Functor.whiskeringRight SimplexCategory C D).obj L ⟶
      (Q ⋙ L) ⋙ Functor.const SimplexCategory where
  app X :=
    { app n := L.map ((P.augmentation.app (Q.obj X)).app n)
      naturality n m f := by
        change L.map ((P.obj.obj (Q.obj X)).map f) ≫
          L.map ((P.augmentation.app (Q.obj X)).app m) =
          L.map ((P.augmentation.app (Q.obj X)).app n) ≫ 𝟙 _
        rw [← L.map_comp, Category.comp_id]
        exact congrArg L.map
          (((P.augmentation.app (Q.obj X)).naturality f).trans (Category.comp_id _)) }
  naturality X Y f := by
    ext n
    change L.map ((P.obj.map (Q.map f)).app n) ≫
      L.map ((P.augmentation.app (Q.obj Y)).app n) =
      L.map ((P.augmentation.app (Q.obj X)).app n) ≫ L.map (Q.map f)
    rw [← L.map_comp, ← L.map_comp]
    exact congrArg L.map (congr_app (P.augmentation.naturality (Q.map f)) n)

variable [ModelCategory D] [L.IsLeftAdjoint] [SerrePositivity.Quillen.IsLeftQuillen L]
  (hQ : ∀ X, IsCofibrant (Q.obj X))
  (cofD : MorphismProperty.FunctorialFactorizationData (cofibrations D) (trivialFibrations D))
  (qD : CofibrantResolutionFamily (C := D) simplex)
local notation "Img" => (Q ⋙ CosimplicialFrameFamily.obj P) ⋙
  Functor.obj (Functor.whiskeringRight SimplexCategory C D) L
local notation "aug" => quillenLeftFrameAugmentation L P Q

omit [L.IsLeftAdjoint] in
include hQ in
/-- cofibrant 始域への元の augmentation の左像は、同じ全族で各次数の弱同値。 -/
lemma quillenLeftFrameAugmentation_weak (X : C) (n : SimplexCategory) :
    weakEquivalences D (((aug).app X).app n) := by
  have := hQ X
  exact leftQuillen_frame_augmentation_weakEquivalence L _ (P.cofibrant (Q.obj X))
    (P.augmentation.app (Q.obj X)) (P.weak (Q.obj X)) n

omit [L.IsLeftAdjoint] in
include hQ in
/-- 元の標準解消の Hom から共通 frame の Hom への同じ自然変換はホモトピー同値。 -/
lemma quillenLeftFrameCommon_left_homotopyEquivalence (X : Cᵒᵖ) (Y : D) [IsFibrant Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (((FrameOverFunctor.homLeft cofD qD (Q ⋙ L) Img aug).app X).app Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedFrameOverFunctor_homLeft_homotopyEquivalence cofD qD (Q ⋙ L) Img aug
    (quillenLeftFrameAugmentation_weak L P Q hQ) X Y

include hQ in
/-- 元の左像 frame の Hom から同じ共通 frame の Hom への自然変換もホモトピー同値。 -/
lemma quillenLeftFrameCommon_right_homotopyEquivalence (X : Cᵒᵖ) (Y : D) [IsFibrant Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (((FrameOverFunctor.homRight cofD qD (Q ⋙ L) Img aug).app X).app Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedFrameOverFunctor_homRight_homotopyEquivalence cofD qD (Q ⋙ L) Img aug
    (quillenLeftFrameAugmentation_weak L P Q hQ)
    (fun X ↦ leftQuillen_frame_reedyCofibrant L _ (P.cofibrant (Q.obj X)))
    (fun X {_ _} f ↦ leftQuillen_frame_homotopicallyConstant L _ (P.cofibrant (Q.obj X))
      (P.homotopicallyConstant (Q.obj X)) f) X Y

end
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

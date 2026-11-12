module
public import SerrePositivity.KST.SConstruction.CubicalSerreTensorColimit

/-! # 固定した鎖複体との tensor による cell の射の判定
概要：任意の固定鎖複体と Serre 鎖の tensor からの射を全 cell で判定する。
方針：左右 tensor の余極限保存を元の生成余錐に適用する。
規約：固定因子を立方体とは仮定しない。使われ方：Day 鎖の左右単位法則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 左に固定した因子を持つ tensor からの射を、元の各 cell で判定する。 -/
lemma cubicalSerreWhiskerLeft_hom_ext {K : CubicalSet.{u}} {Q T : Complex A}
    {f g : Q ⊗ (cubicalSerreChains A).obj K ⟶ T}
    (h : ∀ (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)),
      (Q ◁ cubicalSerreCell A c x) ≫ f = (Q ◁ cubicalSerreCell A c x) ≫ g) : f = g := by
  apply (isColimitOfPreserves (tensorLeft Q) (cubicalSerreGeneratingIsColimit A K)).hom_ext
  intro j
  have hx := h j.left (uliftYonedaEquiv j.hom)
  dsimp only [cubicalSerreCell] at hx
  erw [cubicalCell_equiv] at hx
  exact hx

/-- 右に固定した因子を持つ tensor からの射を、元の各 cell で判定する。 -/
lemma cubicalSerreWhiskerRight_hom_ext {K : CubicalSet.{u}} {Q T : Complex A}
    {f g : (cubicalSerreChains A).obj K ⊗ Q ⟶ T}
    (h : ∀ (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)),
      (cubicalSerreCell A c x ▷ Q) ≫ f = (cubicalSerreCell A c x ▷ Q) ≫ g) : f = g := by
  apply (isColimitOfPreserves (tensorRight Q) (cubicalSerreGeneratingIsColimit A K)).hom_ext
  intro j
  have hx := h j.left (uliftYonedaEquiv j.hom)
  dsimp only [cubicalSerreCell] at hx
  erw [cubicalCell_equiv] at hx
  exact hx

end SerrePositivity.KST.SConstruction

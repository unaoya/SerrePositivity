module
public import SerrePositivity.KST.SConstruction.CubicalSerreDayComparison
public import SerrePositivity.KST.SConstruction.CubicalDayRepresentableNaturality

/-! # 元の Day 鎖比較の二変数自然性
概要：元の全連結 cell で鎖射を判定し、全 cubical sets の元の射に関する自然性を証明する。
方針：元の Yoneda 随伴と Day の生成 cell の普遍性を合成する。
規約：元の全 cell への作用を保つ。使われ方：Day tensor と Serre 鎖の自然な比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全連結 cell の鎖射の像で、Day tensor の鎖複体からの射を判定できる。 -/
lemma cubicalSerreDay_hom_ext {K L : CubicalSet.{u}} {T : Complex A}
    {f g : (cubicalSerreChains A).obj (cubicalDayTensor K L) ⟶ T}
    (h : ∀ (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) (y : L.obj (op d)),
      cubicalSerreCell A (concreteCubeTensorObj c d) (cubicalDayTensorCell c d x y) ≫ f =
        cubicalSerreCell A (concreteCubeTensorObj c d) (cubicalDayTensorCell c d x y) ≫ g) :
    f = g := by
  apply ((cubicalSerreAdjunction A).homEquiv _ T).injective
  apply cubicalDayTensor_cell_hom_ext
  intro c d x y
  erw [cubicalSerreAdjunction_homEquiv_cell A f, cubicalSerreAdjunction_homEquiv_cell A g]
  exact congrArg ULift.up (h c d x y)

/-- 元の Day 鎖比較は、元の両 cubical set の射について自然。 -/
lemma cubicalSerreDayComparison_naturality {K K' L L' : CubicalSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') :
    (cubicalSerreChains A).map (cubicalDayTensorMap f g) ≫ cubicalSerreDayComparison A K' L' =
      cubicalSerreDayComparison A K L ≫
        ((cubicalSerreChains A).map f ⊗ₘ (cubicalSerreChains A).map g) := by
  apply cubicalSerreDay_hom_ext A
  intro c d x y
  erw [← Category.assoc, cubicalSerreCell_naturality,
    cubicalDayTensorMap_cell, cubicalSerreDayComparison_cell,
    ← Category.assoc, cubicalSerreDayComparison_cell, cubicalSerreDayPair_naturality]

/-- 元の Day tensor の鎖から両鎖の tensor への、全二変数の自然な比較。 -/
def cubicalSerreDayComparisonNat :
    cubicalDayTensorFunctor ⋙ cubicalSerreChains A ⟶
      (cubicalSerreChains A).prod (cubicalSerreChains A) ⋙ tensor (Complex A) where
  app P := cubicalSerreDayComparison A P.1 P.2
  naturality {P Q} f := by
    change (cubicalSerreChains A).map (cubicalDayTensorMap f.1 f.2) ≫
        cubicalSerreDayComparison A Q.1 Q.2 =
      cubicalSerreDayComparison A P.1 P.2 ≫
        ((cubicalSerreChains A).map f.1 ⊗ₘ (cubicalSerreChains A).map f.2)
    exact cubicalSerreDayComparison_naturality A f.1 f.2

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.CubicalSerreAdjunction
public import SerrePositivity.KST.SConstruction.CubicalSerreDayPair

/-! # 元の Day tensor 全体から Serre 鎖の tensor への比較
概要：元の連結 cell の比較を、全 cubical sets の Day tensor の鎖射へ降ろす。
方針：二つの cell の比較を制限 Yoneda へ移し、Day の普遍性と元の随伴を使う。
規約：元の鎖関手と元の全 cell の作用を保つ。使われ方：Day tensor と Serre 鎖の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
open scoped MonoidalCategory.ExternalProduct
variable (A : Type u) [CommRing A]

/-- 元の二つの cell の鎖比較を制限 Yoneda に値を持つ自然変換へ移す。 -/
def cubicalSerreDayPairTransform (K L : CubicalSet.{u}) :
    K ⊠ L ⟶ tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ ⋙
      (cubicalSerreRestrictedYoneda A).obj
        ((cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj L) where
  app P := TypeCat.ofHom fun z => ULift.up (cubicalSerreDayPair A P.1.unop P.2.unop z.1 z.2)
  naturality {P Q} f := by
    apply ConcreteCategory.hom_ext
    intro z
    change ULift.up (cubicalSerreDayPair A Q.1.unop Q.2.unop
        (K.map f.1 z.1) (L.map f.2 z.2)) =
      ULift.up ((serreConcreteCubeComplexFunctor A).map
        (concreteCubeTensorMap f.1.unop f.2.unop) ≫
          cubicalSerreDayPair A P.1.unop P.2.unop z.1 z.2)
    exact congrArg ULift.up (cubicalSerreDayPair_restrict A f.1.unop f.2.unop z.1 z.2).symm

/-- 元の二つの cell の比較を、元の Day tensor 全体からの自然変換へ延長する。 -/
def cubicalSerreDayTensorAdjoint (K L : CubicalSet.{u}) :
    cubicalDayTensor K L ⟶ (cubicalSerreRestrictedYoneda A).obj
      ((cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj L) :=
  cubicalDayTensorDesc (cubicalSerreDayPairTransform A K L)

/-- 元の全 cubical sets の Day tensor から、元の両鎖複体の tensor への比較。 -/
def cubicalSerreDayComparison (K L : CubicalSet.{u}) :
    (cubicalSerreChains A).obj (cubicalDayTensor K L) ⟶
      (cubicalSerreChains A).obj K ⊗ (cubicalSerreChains A).obj L :=
  ((cubicalSerreAdjunction A).homEquiv _ _).symm (cubicalSerreDayTensorAdjoint A K L)

/-- 全体の鎖比較は、元の二つの連結 cell の比較射そのものを回収する。 -/
lemma cubicalSerreDayComparison_cell {K L : CubicalSet.{u}}
    (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) (y : L.obj (op d)) :
    cubicalSerreCell A (concreteCubeTensorObj c d) (cubicalDayTensorCell c d x y) ≫
        cubicalSerreDayComparison A K L = cubicalSerreDayPair A c d x y := by
  have ha := cubicalSerreAdjunction_inverse_cell A (cubicalSerreDayTensorAdjoint A K L)
    (concreteCubeTensorObj c d) (cubicalDayTensorCell c d x y)
  have hb := cubicalDayTensorDesc_cell (cubicalSerreDayPairTransform A K L) c d x y
  exact ha.trans (congrArg ULift.down hb)

end SerrePositivity.KST.SConstruction

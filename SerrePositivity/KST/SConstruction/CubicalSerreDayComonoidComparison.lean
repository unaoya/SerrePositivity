module
public import SerrePositivity.KST.SConstruction.ComonoidGeneratorCompatibility
public import SerrePositivity.KST.SConstruction.CubicalSerreComonoidCells
public import SerrePositivity.KST.SConstruction.CubicalSerreDayIso

/-! # 元の Day 鎖比較の Serre 対角と増大の保存
概要：全 Day tensor の鎖比較を、既存の Serre 余モノイド間の射に持ち上げる。
方針：元の全連結 cell 上で、余モノイド射の二法則を判定する。
規約：比較と両余モノイド構造を変更しない。使われ方：余モノイド値の強モノイダル関手。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全 Day 鎖比較は、元の Serre 余モノイドの射。 -/
instance cubicalSerreDayComparison_isComonHom (K L : CubicalSet.{u}) :
    IsComonHom (cubicalSerreDayComparison A K L) where
  hom_counit := by
    apply cubicalSerreDay_hom_ext A
    intro c d x y
    let : ComonObj ((serreConcreteCubeComplexFunctor A).obj (concreteCubeTensorObj c d)) :=
      inferInstanceAs
        (ComonObj ((serreConcreteCubeFunctor A).obj (concreteCubeTensorObj c d)).X)
    let : IsComonHom (cubicalSerreCell A (concreteCubeTensorObj c d)
        (cubicalDayTensorCell c d x y)) := by
      change IsComonHom (cubicalSerreComonoidCell A _ (cubicalDayTensorCell c d x y)).hom
      infer_instance
    let : IsComonHom (cubicalSerreCell A (concreteCubeTensorObj c d)
        (cubicalDayTensorCell c d x y) ≫ cubicalSerreDayComparison A K L) := by
      rw [cubicalSerreDayComparison_cell, ← cubicalSerreComonoidDayPair_hom]
      exact (cubicalSerreComonoidDayPair A c d x y).isComonHom_hom
    exact comonoidGenerator_counit_compatibility
      (cubicalSerreCell A _ (cubicalDayTensorCell c d x y)) (cubicalSerreDayComparison A K L)
  hom_comul := by
    apply cubicalSerreDay_hom_ext A
    intro c d x y
    let : ComonObj ((serreConcreteCubeComplexFunctor A).obj (concreteCubeTensorObj c d)) :=
      inferInstanceAs
        (ComonObj ((serreConcreteCubeFunctor A).obj (concreteCubeTensorObj c d)).X)
    let : IsComonHom (cubicalSerreCell A (concreteCubeTensorObj c d)
        (cubicalDayTensorCell c d x y)) := by
      change IsComonHom (cubicalSerreComonoidCell A _ (cubicalDayTensorCell c d x y)).hom
      infer_instance
    let : IsComonHom (cubicalSerreCell A (concreteCubeTensorObj c d)
        (cubicalDayTensorCell c d x y) ≫ cubicalSerreDayComparison A K L) := by
      rw [cubicalSerreDayComparison_cell, ← cubicalSerreComonoidDayPair_hom]
      exact (cubicalSerreComonoidDayPair A c d x y).isComonHom_hom
    exact comonoidGenerator_comul_compatibility
      (cubicalSerreCell A _ (cubicalDayTensorCell c d x y)) (cubicalSerreDayComparison A K L)

/-- 元の Day 鎖比較を underlying 射とする、元の Serre 余モノイドの比較。 -/
def cubicalSerreDayComonoidComparison (K L : CubicalSet.{u}) :
    (cubicalSerreComonoidFunctor A).obj (cubicalDayTensor K L) ⟶
      (cubicalSerreComonoidFunctor A).obj K ⊗ (cubicalSerreComonoidFunctor A).obj L :=
  Comon.Hom.mk (cubicalSerreDayComparison A K L)
    (isComonHom_hom := cubicalSerreDayComparison_isComonHom A K L)

/-- 元の余モノイド比較の underlying 射は、元の Day 鎖比較そのもの。 -/
lemma cubicalSerreDayComonoidComparison_hom (K L : CubicalSet.{u}) :
    (cubicalSerreDayComonoidComparison A K L).hom = cubicalSerreDayComparison A K L := rfl

/-- 元の Day 鎖比較は余モノイド圏でも同型。 -/
instance cubicalSerreDayComonoidComparison_isIso (K L : CubicalSet.{u}) :
    IsIso (cubicalSerreDayComonoidComparison A K L) := by
  let : IsIso ((Comon.forget (Complex A)).map (cubicalSerreDayComonoidComparison A K L)) :=
    cubicalSerreDayComparison_isIso A K L
  exact isIso_of_reflects_iso _ (Comon.forget (Complex A))

/-- 元の全 Day tensor の Serre 対角と増大を保つ比較同型。 -/
def cubicalSerreDayComonoidIso (K L : CubicalSet.{u}) :
    (cubicalSerreComonoidFunctor A).obj (cubicalDayTensor K L) ≅
      (cubicalSerreComonoidFunctor A).obj K ⊗ (cubicalSerreComonoidFunctor A).obj L :=
  @Comon.mkIso' (Complex A) _ _
    ((cubicalSerreComonoidFunctor A).obj (cubicalDayTensor K L))
    ((cubicalSerreComonoidFunctor A).obj K ⊗ (cubicalSerreComonoidFunctor A).obj L)
    (cubicalSerreDayIso A K L) (cubicalSerreDayComparison_isComonHom A K L)

end SerrePositivity.KST.SConstruction

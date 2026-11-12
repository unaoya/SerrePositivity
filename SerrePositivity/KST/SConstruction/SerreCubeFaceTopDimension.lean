module
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImageTransport

/-! # 元の標準面の最高生成元像の始域次元の統一
概要：同じ元の全体 cube の標準面の最高生成元像を、同じ指定次数で一つの始域次元へ移す。
方針：元の面始域の自然数等号を消去する。
規約：元の面座標・後合成・出力次数を保持。使われ方：全面和の全ての項の次元統一。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の同じ全体 cube の面像は、元の面始域次元の等号による統一で変わらない。 -/
lemma serreCubeFaceTopImage_dimension_post {K L : Complex A} (b : Bool)
    {m n d : ℕ} (h : m = n) (hd : d = m + 1) (hd' : d = n + 1)
    (i : Fin d) (k : ℤ) (hm : -(m : ℤ) = k) (hn : -(n : ℤ) = k)
    (f : serreCubeComplex A d ⟶ K) (g : K ⟶ L) :
    eqToHom (congrArg L.X hm) (serreCubeTopCellImage A L m
        (((serreCubeFace A b m (Fin.cast hd i)).hom ≫
          (serreConcreteCubeComplexFunctor A).map
            (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk d)
              (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (m + 1)) hd).inv ≫ f) ≫ g)) =
      eqToHom (congrArg L.X hn) (serreCubeTopCellImage A L n
        (((serreCubeFace A b n (Fin.cast hd' i)).hom ≫
          (serreConcreteCubeComplexFunctor A).map
            (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk d)
              (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + 1)) hd').inv ≫ f) ≫ g)) := by
  cases h
  rfl

end SerrePositivity.KST.SConstruction

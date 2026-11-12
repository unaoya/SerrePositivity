module
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImage
public import SerrePositivity.KST.SConstruction.SerreCubeDimensionTransport

/-! # 元の最高生成元像の次元・後合成移送
概要：元の Serre 次元移送を通した最高生成元像を、同じ次数の元として回収する。
方針：元の次元等号を消去し、元の関手の恒等保存を使う。
規約：向き補正と元の鎖射を保持。使われ方：necklace 次元から HA の成分次数への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の最高生成元像は、元の鎖射の後合成を回収する。 -/
lemma serreCubeTopCellImage_post {K L : Complex A} (n : ℕ)
    (f : serreCubeComplex A n ⟶ K) (g : K ⟶ L) :
    serreCubeTopCellImage A L n (f ≫ g) = g.f (-(n : ℤ)) (serreCubeTopCellImage A K n f) := rfl

/-- 元の指定次数への移送と、元の鎖射による最高生成元像の後合成は可換。 -/
lemma serreCubeTopCellImage_cast_post {K L : Complex A} (n : ℕ) (k : ℤ)
    (hk : -(n : ℤ) = k) (f : serreCubeComplex A n ⟶ K) (g : K ⟶ L) :
    g.f k (eqToHom (congrArg K.X hk) (serreCubeTopCellImage A K n f)) =
      eqToHom (congrArg L.X hk) (serreCubeTopCellImage A L n (f ≫ g)) := by
  cases hk
  rfl

/-- 元の次元移送の前合成は、同じ指定次数への最高生成元像を保つ。 -/
lemma serreCubeTopCellImage_cast_dimension {K : Complex A} {m n : ℕ} (h : m = n)
    (k : ℤ) (hm : -(m : ℤ) = k) (hn : -(n : ℤ) = k) (f : serreCubeComplex A n ⟶ K) :
    eqToHom (congrArg K.X hm)
        (serreCubeTopCellImage A K m
          ((serreConcreteCubeComplexFunctor A).map
            (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m) (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n) h).hom ≫
            f)) =
      eqToHom (congrArg K.X hn) (serreCubeTopCellImage A K n f) := by
  cases h
  apply congrArg (fun w => eqToHom (congrArg K.X hm) w)
  apply congrArg (serreCubeTopCellImage A K m)
  exact (congrArg (fun g => g ≫ f) ((serreConcreteCubeComplexFunctor A).map_id _)).trans
    (Category.id_comp _)

/-- 元の次元移送後の最高生成元像は、元の後合成を保って同じ指定次数へ移る。 -/
lemma serreCubeTopCellImage_cast_dimension_post {K L : Complex A} {m n : ℕ}
    (h : m = n) (k : ℤ) (hm : -(m : ℤ) = k) (hn : -(n : ℤ) = k)
    (f : serreCubeComplex A n ⟶ K) (g : K ⟶ L) :
    eqToHom (congrArg L.X hm)
        (serreCubeTopCellImage A L m
          (((serreConcreteCubeComplexFunctor A).map
            (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m) (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n) h).hom ≫
              f) ≫ g)) =
      eqToHom (congrArg L.X hn) (serreCubeTopCellImage A L n (f ≫ g)) := by
  exact (congrArg (fun l => eqToHom (congrArg L.X hm) (serreCubeTopCellImage A L m l))
    (Category.assoc _ _ _)).trans
      (serreCubeTopCellImage_cast_dimension A h k hm hn (f ≫ g))

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.CubicalSerreDiagonal
public import SerrePositivity.KST.SConstruction.ComonoidGeneratorLaws

/-! # 全 cubical sets の Serre 鎖余モノイド
概要：余極限で延長した実対角と増大が余結合・左右余単位律を満たすことを証明する。
方針：元の全 cell 上で各法則を判定し、鎖立方体の元の余モノイド則を移す。
規約：対角と増大は前段の実鎖射そのもの。使われ方：Λ の oplax tensor の入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Opposite MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全 cell で判定した左余単位律。 -/
lemma cubicalSerreDiagonal_left_counit (K : CubicalSet.{u}) :
    cubicalSerreDiagonal A K ≫ (cubicalSerreAugmentation A K ⊗ₘ 𝟙 _) =
      (λ_ ((cubicalSerreChains A).obj K)).inv := by
  apply cubicalSerreChains_hom_ext A
  intro c x
  let : ComonObj ((serreConcreteCubeComplexFunctor A).obj c) :=
    inferInstanceAs (ComonObj ((serreConcreteCubeFunctor A).obj c).X)
  exact comonoidGenerator_left_counit (cubicalSerreGenerator A (cubicalCell c x))
    (cubicalSerreDiagonal A K) (cubicalSerreAugmentation A K)
    (cubicalSerreDiagonal_generator A K _) (cubicalSerreAugmentation_generator A K _)

/-- 元の全 cell で判定した右余単位律。 -/
lemma cubicalSerreDiagonal_right_counit (K : CubicalSet.{u}) :
    cubicalSerreDiagonal A K ≫ (𝟙 _ ⊗ₘ cubicalSerreAugmentation A K) =
      (ρ_ ((cubicalSerreChains A).obj K)).inv := by
  apply cubicalSerreChains_hom_ext A
  intro c x
  let : ComonObj ((serreConcreteCubeComplexFunctor A).obj c) :=
    inferInstanceAs (ComonObj ((serreConcreteCubeFunctor A).obj c).X)
  exact comonoidGenerator_right_counit (cubicalSerreGenerator A (cubicalCell c x))
    (cubicalSerreDiagonal A K) (cubicalSerreAugmentation A K)
    (cubicalSerreDiagonal_generator A K _) (cubicalSerreAugmentation_generator A K _)

/-- 元の全 cell で判定した Serre 対角の余結合則。 -/
lemma cubicalSerreDiagonal_coassoc (K : CubicalSet.{u}) :
    cubicalSerreDiagonal A K ≫ (cubicalSerreDiagonal A K ⊗ₘ 𝟙 _) ≫
        (α_ ((cubicalSerreChains A).obj K) ((cubicalSerreChains A).obj K)
          ((cubicalSerreChains A).obj K)).hom =
      cubicalSerreDiagonal A K ≫ (𝟙 _ ⊗ₘ cubicalSerreDiagonal A K) := by
  apply cubicalSerreChains_hom_ext A
  intro c x
  let : ComonObj ((serreConcreteCubeComplexFunctor A).obj c) :=
    inferInstanceAs (ComonObj ((serreConcreteCubeFunctor A).obj c).X)
  exact comonoidGenerator_coassoc (cubicalSerreGenerator A (cubicalCell c x))
    (cubicalSerreDiagonal A K) (cubicalSerreDiagonal_generator A K _)

/-- 延長した元の対角・増大による全 cubical sets の実余モノイド構造。 -/
instance cubicalSerreComonObj (K : CubicalSet.{u}) :
    ComonObj ((cubicalSerreChains A).obj K) where
  counit := cubicalSerreAugmentation A K
  comul := cubicalSerreDiagonal A K
  counit_comul := by
    simpa only [tensorHom_id] using cubicalSerreDiagonal_left_counit A K
  comul_counit := by
    simpa only [id_tensorHom] using cubicalSerreDiagonal_right_counit A K
  comul_assoc := by
    simpa only [tensorHom_id, id_tensorHom] using (cubicalSerreDiagonal_coassoc A K).symm

/-- 元の鎖関手と全表示関係を保つ、全 cubical sets 上の余モノイド値関手。 -/
def cubicalSerreComonoidFunctor : CubicalSet.{u} ⥤ Comon (Complex A) where
  obj K := Comon.mk ((cubicalSerreChains A).obj K)
  map f := Comon.Hom.mk' ((cubicalSerreChains A).map f)
    (cubicalSerreAugmentation_naturality A f) (cubicalSerreDiagonal_naturality A f)
  map_id K := Comon.Hom.ext ((cubicalSerreChains A).map_id K)
  map_comp f g := Comon.Hom.ext ((cubicalSerreChains A).map_comp f g)

end SerrePositivity.KST.SConstruction

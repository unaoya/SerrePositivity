module
public import SerrePositivity.KST.SConstruction.CubicalSerreDayIso
public import SerrePositivity.KST.SConstruction.CubicalSerreDayUnit
public import SerrePositivity.KST.SConstruction.CubicalSerreWhiskerColimit
public import SerrePositivity.KST.SConstruction.CubicalDayStructuralCells

/-! # 全 cubical sets 上の Serre 鎖比較の左右単位法則
概要：元の Day 単位比較と鎖の組み立てが左右単位子を保存すると示す。
方針：元の各 cell 上で Day 単位子を回収し、Serre 関手の単位法則を使う。
規約：単位比較は元の単位生成 cell の逆射。使われ方：強モノイダル構造の構成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の Day 鎖の組み立ては左単位子を保存する。 -/
lemma cubicalSerreDayInverse_leftUnit (K : CubicalSet.{u}) :
    (λ_ ((cubicalSerreChains A).obj K)).hom =
      (cubicalSerreDayUnitGeneratorIso A).hom ▷ (cubicalSerreChains A).obj K ≫
        cubicalSerreDayInverse A cubicalDayUnit K ≫
          (cubicalSerreChains A).map (λ_ (DayFunctor.mk K)).hom.natTrans := by
  apply cubicalSerreWhiskerLeft_hom_ext
  intro c x
  rw [← Category.assoc, ← tensorHom_def', cubicalSerreDayUnitGeneratorIso_hom]
  erw [← Category.assoc, cubicalSerreDayInverse_cell A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) c
    cubicalDayUnitCell x, Category.assoc]
  dsimp only [cubicalSerreDayAssembly]
  erw [Category.assoc, cubicalSerreCell_naturality, cubicalDayLeftUnitor_cell,
    ← cubicalSerreCell_restrict A (concreteCubeLeftUnitor c).hom x]
  erw [← Category.assoc
    (Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) c)
    ((serreConcreteCubeComplexFunctor A).map (concreteCubeLeftUnitor c).hom)
    (cubicalSerreCell A c x)]
  have h := Functor.LaxMonoidal.left_unitality (serreConcreteCubeComplexFunctor A) c
  change (λ_ ((serreConcreteCubeComplexFunctor A).obj c)).hom =
    (𝟙 (𝟙_ (Complex A))) ▷ (serreConcreteCubeComplexFunctor A).obj c ≫
      Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) c ≫
        (serreConcreteCubeComplexFunctor A).map (concreteCubeLeftUnitor c).hom at h
  rw [id_whiskerRight, Category.id_comp] at h
  erw [← h, leftUnitor_naturality]
  rfl

/-- 元の Day 鎖の組み立ては右単位子を保存する。 -/
lemma cubicalSerreDayInverse_rightUnit (K : CubicalSet.{u}) :
    (ρ_ ((cubicalSerreChains A).obj K)).hom =
      (cubicalSerreChains A).obj K ◁ (cubicalSerreDayUnitGeneratorIso A).hom ≫
        cubicalSerreDayInverse A K cubicalDayUnit ≫
          (cubicalSerreChains A).map (ρ_ (DayFunctor.mk K)).hom.natTrans := by
  apply cubicalSerreWhiskerRight_hom_ext
  intro c x
  rw [← Category.assoc, ← tensorHom_def, cubicalSerreDayUnitGeneratorIso_hom]
  erw [← Category.assoc, cubicalSerreDayInverse_cell A c (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)
    x cubicalDayUnitCell, Category.assoc]
  dsimp only [cubicalSerreDayAssembly]
  erw [Category.assoc, cubicalSerreCell_naturality, cubicalDayRightUnitor_cell,
    ← cubicalSerreCell_restrict A (concreteCubeRightUnitor c).hom x]
  erw [← Category.assoc
    (Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A) c (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0))
    ((serreConcreteCubeComplexFunctor A).map (concreteCubeRightUnitor c).hom)
    (cubicalSerreCell A c x)]
  have h := Functor.LaxMonoidal.right_unitality (serreConcreteCubeComplexFunctor A) c
  change (ρ_ ((serreConcreteCubeComplexFunctor A).obj c)).hom =
    (serreConcreteCubeComplexFunctor A).obj c ◁ (𝟙 (𝟙_ (Complex A))) ≫
      Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A) c (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) ≫
        (serreConcreteCubeComplexFunctor A).map (concreteCubeRightUnitor c).hom at h
  rw [whiskerLeft_id, Category.id_comp] at h
  erw [← h, rightUnitor_naturality]
  rfl

end SerrePositivity.KST.SConstruction

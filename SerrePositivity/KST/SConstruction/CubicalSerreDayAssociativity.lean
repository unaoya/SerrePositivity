module
public import SerrePositivity.KST.SConstruction.CubicalSerreDayTripleAssembly

/-! # 全 cubical sets 上の Serre 鎖組み立ての結合法則
概要：元の Day tensor の結合子と鎖 tensor の結合子の可換性を証明する。
方針：三つの独立な cell へ制限し、元の Serre 関手の結合法則へ帰着する。
規約：全体の比較同型を別の射へ変更しない。使われ方：強モノイダル関手の構成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 全 cubical sets 上の元の鎖の組み立ては Day 結合子を保存する。 -/
lemma cubicalSerreDayInverse_associativity (K L M : CubicalSet.{u}) :
    cubicalSerreDayInverse A K L ▷ (cubicalSerreChains A).obj M ≫
        cubicalSerreDayInverse A (cubicalDayTensor K L) M ≫
        (cubicalSerreChains A).map
          (α_ (DayFunctor.mk K) (DayFunctor.mk L) (DayFunctor.mk M)).hom.natTrans =
      (α_ ((cubicalSerreChains A).obj K) ((cubicalSerreChains A).obj L)
        ((cubicalSerreChains A).obj M)).hom ≫
        (cubicalSerreChains A).obj K ◁ cubicalSerreDayInverse A L M ≫
          cubicalSerreDayInverse A K (cubicalDayTensor L M) := by
  apply cubicalSerreTriple_hom_ext
  intro a b c x y z
  have hL := congrArg (fun f :
      ((serreConcreteCubeComplexFunctor A).obj a ⊗
        (serreConcreteCubeComplexFunctor A).obj b) ⊗
          (serreConcreteCubeComplexFunctor A).obj c ⟶
            (cubicalSerreChains A).obj (cubicalDayTensor (cubicalDayTensor K L) M) =>
      f ≫ (cubicalSerreChains A).map
        (show cubicalDayTensor (cubicalDayTensor K L) M ⟶
          cubicalDayTensor K (cubicalDayTensor L M) from
          (α_ (DayFunctor.mk K) (DayFunctor.mk L) (DayFunctor.mk M)).hom.natTrans))
    (cubicalSerreDayInverse_leftTriple A a b c x y z)
  simp only [Category.assoc] at hL
  refine hL.trans (Eq.trans ?_
    (cubicalSerreDayInverse_rightTriple A a b c x y z).symm)
  erw [cubicalSerreCell_naturality, cubicalDayAssociator_cell,
    ← cubicalSerreCell_restrict A (concreteCubeAssociator a b c).hom
      (cubicalDayTensorCell a (concreteCubeTensorObj b c) x
        (cubicalDayTensorCell b c y z))]
  have h := Functor.LaxMonoidal.associativity (serreConcreteCubeComplexFunctor A) a b c
  change Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A) a b ▷
      (serreConcreteCubeComplexFunctor A).obj c ≫
      Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A)
        (concreteCubeTensorObj a b) c ≫
      (serreConcreteCubeComplexFunctor A).map (concreteCubeAssociator a b c).hom =
    (α_ ((serreConcreteCubeComplexFunctor A).obj a)
      ((serreConcreteCubeComplexFunctor A).obj b)
      ((serreConcreteCubeComplexFunctor A).obj c)).hom ≫
      (serreConcreteCubeComplexFunctor A).obj a ◁
        Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A) b c ≫
      Functor.LaxMonoidal.μ (serreConcreteCubeComplexFunctor A)
        a (concreteCubeTensorObj b c) at h
  have hh := congrArg (fun f :
      ((serreConcreteCubeComplexFunctor A).obj a ⊗
        (serreConcreteCubeComplexFunctor A).obj b) ⊗
          (serreConcreteCubeComplexFunctor A).obj c ⟶
            (serreConcreteCubeComplexFunctor A).obj
              (concreteCubeTensorObj a (concreteCubeTensorObj b c)) =>
      f ≫ cubicalSerreCell A
    (concreteCubeTensorObj a (concreteCubeTensorObj b c))
    (cubicalDayTensorCell a (concreteCubeTensorObj b c) x
      (cubicalDayTensorCell b c y z))) h
  simpa only [Category.assoc] using hh

end SerrePositivity.KST.SConstruction

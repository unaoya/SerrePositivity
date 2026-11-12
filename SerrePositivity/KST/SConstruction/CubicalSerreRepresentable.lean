module
public import SerrePositivity.KST.SConstruction.CubicalSerreComonoid

/-! # 表現可能立方体上の Serre 余モノイドの自然な回収
概要：余極限で延長した余モノイド関手が、元の全鎖立方体を自然な同型で回収する。
方針：元の単位射が各立方体の対角・増大を保つことを、生成射での回収式から示す。
規約：比較の鎖射は元の左 Kan 延長の単位。使われ方：cubical rigidification の標準片。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Opposite MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 表現可能立方体上の元の単位射は、Serre 余モノイドの射へ束ねられる。 -/
def cubicalSerreComonoidCubeUnit : serreConcreteCubeFunctor A ⟶
    cubicalYoneda ⋙ cubicalSerreComonoidFunctor A where
  app c := Comon.Hom.mk' ((cubicalSerreChainsCubeUnit A).app c)
    (by
      change (cubicalSerreChainsCubeUnit A).app c ≫
        cubicalSerreAugmentation A (cubicalYoneda.obj c) = serreConcreteCubeAugmentation A c
      have h := cubicalSerreAugmentation_generator A (cubicalYoneda.obj c) (𝟙 _)
      rw [cubicalSerreGenerator_id] at h
      exact h)
    (by
      change (cubicalSerreChainsCubeUnit A).app c ≫
        cubicalSerreDiagonal A (cubicalYoneda.obj c) = serreConcreteCubeDiagonal A c ≫
          ((cubicalSerreChainsCubeUnit A).app c ⊗ₘ (cubicalSerreChainsCubeUnit A).app c)
      have h := cubicalSerreDiagonal_generator A (cubicalYoneda.obj c) (𝟙 _)
      rw [cubicalSerreGenerator_id] at h
      exact h)
  naturality c d f := by
    apply Comon.Hom.ext
    exact (cubicalSerreChainsCubeUnit A).naturality f

/-- 元の鎖立方体との各比較は、余モノイド圏で同型。 -/
instance cubicalSerreComonoidCubeUnit_app_isIso (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    IsIso ((cubicalSerreComonoidCubeUnit A).app c) := by
  let : IsIso ((Comon.forget (Complex A)).map
      ((cubicalSerreComonoidCubeUnit A).app c)) := by
    change IsIso ((cubicalSerreChainsCubeIso A).hom.app c)
    infer_instance
  exact isIso_of_reflects_iso _ (Comon.forget (Complex A))

/-- 元の全 Serre 鎖立方体を、対角・増大も保つ自然な同型で回収する。 -/
def cubicalSerreComonoidCubeIso : serreConcreteCubeFunctor A ≅
    cubicalYoneda ⋙ cubicalSerreComonoidFunctor A :=
  NatIso.ofComponents (fun c => asIso ((cubicalSerreComonoidCubeUnit A).app c))
    (fun f => (cubicalSerreComonoidCubeUnit A).naturality f)

end SerrePositivity.KST.SConstruction

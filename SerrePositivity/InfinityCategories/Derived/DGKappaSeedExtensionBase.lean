module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPerfectSeedRefinement
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedFreeExtension
public import SerrePositivity.InfinityCategories.Derived.DGKappaClosedProjectiveOperations
public import SerrePositivity.InfinityCategories.Derived.DGModuleHomotopyRangeClosure
/-!
概要：κ-small 出発提示の基底 seed の実延長像を標的の閉代表族へ戻す。
方針：sphere-free 基底は保持したラベル比較、perfect 基底は射影的ホモトピー被覆を使う。
規約：元の延長関手と全 Hom を保持し、代表化はホモトピー同型として明示する。
使われ方：c′ の共通源精密化の、超限閉包に入る前の二種類の基底分岐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D)
  (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 < κ)

include hκ in
lemma dgKappaClosedProjectiveBase_extension_homotopyRange
    (i : (dgKappaClosedProjectiveBaseFamily R C κ).1) :
    dgModuleHomotopyRange R D (dgKappaClosedProjectiveObjects R D κ)
      ((dgModuleExtension R C D F).onClosed.obj
        (((dgKappaClosedProjectiveBaseFamily R C κ).2 i).val)) := by
  rcases i with i | i
  · refine ⟨dgKappaSphereFreeModule R D (dgKappaSphereFreeLabelMap R F i),
      dgKappaClosedProjectiveObjects_sphereFree R D hκ _, ?_⟩
    exact ⟨(moduleToHomotopy R D).mapIso
      (dgKappaPresentedFreeExtensionIso R C D F κ ⟨i⟩).symm⟩
  · obtain ⟨j, hj⟩ := dgKappaPerfectSeed_extension_homotopyCovers R C D F κ
      (ne_of_gt (lt_trans Cardinal.aleph0_pos hκ))
      (dgKappaPerfectRepresentative R C i)
      (dgKappaPerfectRepresentative_projective R C i)
      (perfectDGModuleRepresentative R C Set.univ i).property.2
    exact ⟨_, ⟨j, rfl⟩, hj⟩

end SerrePositivity.InfinityCategories

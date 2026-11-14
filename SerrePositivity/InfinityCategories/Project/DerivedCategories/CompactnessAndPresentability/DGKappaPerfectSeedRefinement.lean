module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaClosedPerfectHomotopyCover
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction

/-!
概要：perfect seed の実延長像を共通出発圏の閉代表族へホモトピー同型まで精密化する。
方針：同じ射影的 seed による実延長計算と perfect 性の保存を代表被覆へ渡す。
規約：perfect 条件を明記し、非 perfect な可算 cell の同時精密化を結論しない。
使われ方：c′ ゲート3の、異なる提示を共通源へ送る際の perfect 基底分岐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D)

lemma dgKappaPerfectSeed_extension_homotopyCovers (κ : Cardinal.{u}) (hκ : κ ≠ 0)
    (M : ModuleCategory R C) (hp : moduleHomotopicallyProjective R C M)
    (hM : modulePerfect R C ((moduleToDerived R C).obj M)) :
    ∃ i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R D κ).1,
      Nonempty ((moduleToHomotopy R D).obj
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R D κ).2 i).val) ≅
        (moduleToHomotopy R D).obj ((dgModuleExtension R C D F).onClosed.obj M)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily_perfectHomotopyCovers R D κ hκ
  · exact dgModuleExtension_homotopicallyProjective R C D F hp
  · let Q := moduleIdentityProjectiveResolution R C M hp
    exact (modulePerfect R D).prop_of_iso
      (dgDerivedExtensionResolutionComputation R C D F Q)
      (dgDerivedExtension_perfect R C D F hM)

end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberHomCoordinates
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-! # shifted cone への Hom の逆座標

概要：fiber Hom の二成分からの復元を全 Hom end 内で明示する。
方針：cone の比較射を通して復元し、shift の斉次単位で戻す。
規約：第二座標に負号を付ける。使われ方：β3 の fiber の原始元の微分計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {T M N : ModuleCategory A D}

/-- fiber の逆座標は符号付き cone lift を shift の閉斉次単位で戻した元。 -/
lemma dgModuleFiberHomCoordinates_symm (f : M ⟶ N) (n : ℤ)
    (a : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) (n + 1))
    (b : GradedHom A (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f n).symm (a, b) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)) n).symm
          (moduleConeLiftElement A D f n a (-b)) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories

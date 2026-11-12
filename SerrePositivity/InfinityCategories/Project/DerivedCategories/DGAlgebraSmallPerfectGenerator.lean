module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SmallPerfectRepresentableGenerator
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraDerivedInfinity

/-!
概要：非可換 dg 代数の実小完全加群圏の自由生成元。
方針：既存の実評価・導来 tensor と完全加群の厚い閉包を使う。
規約：生成性の結論を追加仮定にしない。使われ方：β5 と K-S• の実自由代表。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
local notation "C" => SmallPerfectDGModuleOver R D Set.univ

abbrev dgAlgebraSmallPerfectGenerator (B : CategoryTheory.Mon (Complex R))
    (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRepresentablePoint R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) d

lemma dgAlgebraSmallPerfectGenerator_generates (B : CategoryTheory.Mon (Complex R))
    (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) :
    modulePerfectOver R (SmallPerfectDGModuleOver R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) Set.univ)
      {dgAlgebraSmallPerfectGenerator R B d} =
      modulePerfect R (SmallPerfectDGModuleOver R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) Set.univ) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRepresentablePoint_generates_of_subsingleton R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) d

def dgAlgebraSmallPerfectGenerator_homotopyComparison (B : CategoryTheory.Mon (Complex R))
    (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) :
    (smallPerfectDGModuleInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) Set.univ).onHomotopy.obj
      ((toHomotopy R (SmallPerfectDGModuleOver R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) Set.univ)).obj
        (ForgetEnrichment.of (Complex R) (dgAlgebraSmallPerfectGenerator R B d))) ≅
      (toHomotopy R (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B))).obj
        (ForgetEnrichment.of (Complex R)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRepresentableDGPoint R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) d)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectRepresentablePoint_homotopyComparison R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) d

end SerrePositivity.InfinityCategories.Project.DerivedCategories

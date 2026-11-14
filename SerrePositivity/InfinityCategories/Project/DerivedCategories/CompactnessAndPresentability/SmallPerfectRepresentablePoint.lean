module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.SmallPerfectEvaluationBimodule

/-!
概要：表現可能完全加群の実小代表と元の完全加群との比較。
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

def smallPerfectRepresentableClass (d : D) : PerfectModuleCategoryOver R D Set.univ :=
  ⟨(moduleToDerived R D).obj (ForgetEnrichment.of (Complex R) (representable R d)),
    modulePerfectOver_representable R D d (Set.mem_univ _)⟩

def smallPerfectRepresentablePoint (d : D) : SmallPerfectDGModuleOver R D Set.univ :=
  smallPerfectDGModuleObject R D Set.univ
    ((equivSmallModel.{u} (PerfectModuleCategoryOver R D Set.univ)).functor.obj
      (smallPerfectRepresentableClass R D d))

def smallPerfectRepresentablePoint_comparison (d : D) :
    (smallPerfectDGModuleToPerfect R D Set.univ).obj
      ((toHomotopy R (SmallPerfectDGModuleOver R D Set.univ)).obj
        (ForgetEnrichment.of (Complex R) (smallPerfectRepresentablePoint R D d))) ≅
      smallPerfectRepresentableClass R D d := by
  let e := equivSmallModel.{u} (PerfectModuleCategoryOver R D Set.univ)
  let i := e.functor.obj (smallPerfectRepresentableClass R D d)
  change (smallPerfectDGModuleToPerfect R D Set.univ).obj
    ((toHomotopy R (SmallPerfectDGModuleOver R D Set.univ)).obj
      (ForgetEnrichment.of (Complex R) (smallPerfectDGModuleObject R D Set.univ i))) ≅ _
  rw [smallPerfectDGModuleObject_comparison]
  exact (perfectDGModuleHomotopyEquivalence R D Set.univ).counitIso.app
    (e.inverse.obj i) ≪≫ (e.unitIso.app (smallPerfectRepresentableClass R D d)).symm

def smallPerfectRepresentableDGPoint (d : D) : PerfectDGModule R D :=
  ⟨representable R d, representable_homotopicallyProjective R D d,
    modulePerfectOver_representable R D d (Set.mem_univ _)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories

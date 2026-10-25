module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyColimit
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictAugmentationQuasiIso
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered

/-!
概要：正則 κ の filtered poset に対する coherent C1 と strict 特殊化を公開する。
方針：より強い通常の filtered 版を、IsCardinalFiltered からの帰結で適用する。
規約：native 余錐の普遍性を仮定せず、coherent 入力の全 HA 成分を保つ。
使われ方：D-bar B 到着後の strict/native 比較 C2。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular]
  {J : Type u} [PartialOrder J] [IsCardinalFiltered J κ]

def dgKappaCoherentBarHomologyColimitIso
    (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
      dgNerve R (RightModule R D)) (x : D) (q : ℤ) :
    ((dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).homology q ≅
      colimit (dgCoherentBarHomologyDiagram R D G x q) := by
  letI := isFiltered_of_isCardinalFiltered J κ
  exact dgCoherentBarHomologyColimitIso R D G x q

include κ in
lemma dgKappaStrictBarColimitAugmentation_quasiIso (F : J ⥤ ModuleCategory R D) :
    moduleQuasiIso R D (dgCoherentBarStrictColimitAugmentation R D F) := by
  letI := isFiltered_of_isCardinalFiltered J κ
  exact dgCoherentBarStrictColimitAugmentation_quasiIso R D F

end SerrePositivity.InfinityCategories

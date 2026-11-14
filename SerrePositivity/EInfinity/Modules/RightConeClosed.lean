module
public import SerrePositivity.EInfinity.Modules.RightConeComponents
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-!
概要：実加群右 cone の指定終端への全成分の微分は零である。
方針：同じ閉 augmentation の斉次成分へ移し、零次の閉性と他次数の零を使う。
規約：HA Construction 1.3.1.6・1.3.1.13、全有限集合・全次数。使われ方：終端 HA 方程式の左辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeData_differential_last {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    differential A ((moduleRightConeData A D η).hom I a b k hI ha hb hk) = 0 := by
  have han : a ≠ Fin.last (n + 1) := by rw [ha]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last I hI
  have hx : (moduleRightConeData A D η).obj a =
      s.obj ((Fin.last n).predAboveOrderHom a) := moduleRightConeObj_ne_last A D s M a han
  have hy : (moduleRightConeData A D η).obj b = (ForgetEnrichment.to (Complex A) M) := by
    change moduleRightConeObj A D s M b = (ForgetEnrichment.to (Complex A) M)
    rw [hbl, moduleRightConeObj_last]
  have he := moduleRightConeData_hom_last A D η I a b k hI ha hb hk hbl
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := A) hx hy rfl _ _ he
  have hz : differential A
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (η.app ((Fin.last n).predAboveOrderHom a)) k)
        = 0 := by
    by_cases hk0 : k = 0
    · subst hk0
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero]
      exact (ModuleSimplexAugmentation.cycle A D η _).property
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ k hk0]
      exact map_zero _
  exact eq_of_heq (hd.trans ((heq_of_eq hz).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := A) (k := k + 1) (l := k + 1) hx hy rfl).symm))

end SerrePositivity.EInfinity.Modules

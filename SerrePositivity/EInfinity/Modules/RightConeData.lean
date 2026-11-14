module
public import SerrePositivity.EInfinity.Modules.SimplexAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedRecoverIndex

/-!
概要：指定 augmentation を持つ実加群の dg 単体に、同じ終端を追加する生データを作る。
方針：元の前面を最後の退化で延長し、終端成分だけ同じ閉 augmentation に置き換える。
規約：HA Construction 1.3.1.6・1.3.1.13、全 HA 方程式は別に検証する。使われ方：元の cone の大域三角形。
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

def moduleRightConeObj {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n) (M : ModuleCategory A D)
    (i : Fin (n + 2)) : RightModule A D :=
  if i = Fin.last (n + 1) then (ForgetEnrichment.to (Complex A) M) else s.obj ((Fin.last n).predAboveOrderHom i)

lemma moduleRightConeObj_last {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n) (M : ModuleCategory A D) :
    moduleRightConeObj A D s M (Fin.last (n + 1)) = (ForgetEnrichment.to (Complex A) M) := by
  simp only [moduleRightConeObj, ite_true]

lemma moduleRightConeObj_ne_last {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n) (M : ModuleCategory A D)
    (i : Fin (n + 2)) (hi : i ≠ Fin.last (n + 1)) :
    moduleRightConeObj A D s M i = s.obj ((Fin.last n).predAboveOrderHom i) := by
  simp only [moduleRightConeObj, ite_eq_right hi]

lemma moduleRightConeObj_castSucc {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n) (M : ModuleCategory A D)
    (i : Fin (n + 1)) : moduleRightConeObj A D s M i.castSucc = s.obj i := by
  rw [moduleRightConeObj_ne_last A D s M _ (ne_of_lt (Fin.castSucc_lt_last i))]
  congr 1
  simp

def moduleRightConeData {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) (n + 1) where
  obj := moduleRightConeObj A D s M
  hom I a b k hI ha hb hk := by
    have han : a ≠ Fin.last (n + 1) := by rw [ha]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last I hI
    by_cases hbl : b = Fin.last (n + 1)
    · exact cast (by rw [moduleRightConeObj_ne_last A D s M a han, hbl,
          moduleRightConeObj_last]; rfl)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (η.app ((Fin.last n).predAboveOrderHom a)) k)
    · exact cast (by rw [moduleRightConeObj_ne_last A D s M a han,
          moduleRightConeObj_ne_last A D s M b hbl]; rfl)
        ((s.toSimplexData.pullback (Fin.last n).predAboveOrderHom).hom I a b k hI ha hb hk)

end SerrePositivity.EInfinity.Modules

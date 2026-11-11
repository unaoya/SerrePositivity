module
public import SerrePositivity.EInfinity.ComplexLimits.ComplexSimplexAugmentation

/-!
概要：指定 augmentation を持つ実複体の dg 単体に、同じ終端を追加する生データを作る。
方針：元の前面を最後の退化で延長し、終端成分だけ同じ閉 augmentation に置き換える。
規約：全 HA 方程式は別に検証する。使われ方：元の cone の大域三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

def complexRightConeObj {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) (X : Complex A)
    (i : Fin (n + 2)) : Complex A :=
  if i = Fin.last (n + 1) then X else s.obj ((Fin.last n).predAboveOrderHom i)

lemma complexRightConeObj_last {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) (X : Complex A) :
    complexRightConeObj A s X (Fin.last (n + 1)) = X := by
  simp only [complexRightConeObj, ite_true]

lemma complexRightConeObj_ne_last {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) (X : Complex A)
    (i : Fin (n + 2)) (hi : i ≠ Fin.last (n + 1)) :
    complexRightConeObj A s X i = s.obj ((Fin.last n).predAboveOrderHom i) := by
  simp only [complexRightConeObj, ite_eq_right hi]

lemma complexRightConeObj_castSucc {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) (X : Complex A)
    (i : Fin (n + 1)) : complexRightConeObj A s X i.castSucc = s.obj i := by
  rw [complexRightConeObj_ne_last A s X _ (ne_of_lt (Fin.castSucc_lt_last i))]
  congr 1
  simp

def complexRightConeData {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : ComplexSimplexAugmentation A s X) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) (n + 1) where
  obj := complexRightConeObj A s X
  hom I a b k hI ha hb hk := by
    have han : a ≠ Fin.last (n + 1) := by rw [ha]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last I hI
    by_cases hbl : b = Fin.last (n + 1)
    · exact cast (by rw [complexRightConeObj_ne_last A s X a han, hbl,
          complexRightConeObj_last]; rfl)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map (η.app ((Fin.last n).predAboveOrderHom a))) k)
    · exact cast (by rw [complexRightConeObj_ne_last A s X a han,
          complexRightConeObj_ne_last A s X b hbl]; rfl)
        ((s.toSimplexData.pullback (Fin.last n).predAboveOrderHom).hom I a b k hI ha hb hk)

end SerrePositivity.EInfinity.ComplexLimits

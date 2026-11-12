module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorIsPullbackMaps
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices

/-!
概要：任意の pullback 表示の相対関手空間の比較は厳密な同型。
方針：元の二射への展開で逆性を検査し、指定した底上の関手の頂点を回収する。
規約：構成は単体集合の同型であり、充填性や逆射の選択を要求しない。
使われ方：cocartesian 条件を保った局所 Hom の厳密な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

variable {X P E A B : SSet.{u}} {i : P ⟶ E} {r : P ⟶ A} {p : E ⟶ B} {f : A ⟶ B}
  (hs : IsPullback i r p f) (a : X ⟶ A) (b : X ⟶ B) (hab : a ≫ f = b)

/-- pullback の相対関手空間と、元の標的への同じ底上の相対関手空間は厳密に同型。 -/
def relativeFunctorIsPullbackIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r a ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p b where
  hom := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackForward hs a b hab
  inv := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackBackward hs a b hab
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective r a
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackBackward_uncurry]
    apply hs.hom_ext
    · rw [hs.lift_fst, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackForward, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry]
    · rw [hs.lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection]
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p b
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackForward_uncurry, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackBackward,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, hs.lift_fst]

/-- 同じ厳密な同型の頂点作用は、元の全空間への射による実際の後合成。 -/
lemma relativeFunctorIsPullbackIso_vertex (g : X ⟶ P) (hg : g ≫ r = a) :
    (relativeFunctorIsPullbackIso hs a b hab).hom.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex r a g hg) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p b (g ≫ i) (by
      rw [Category.assoc, hs.w, ← Category.assoc, hg, hab]) := by
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseJoin

/-! # join の宇宙同型の自然性と二包含

概要：join の宇宙持ち上げの実同型は両因子の射と左右包含を保つ。
方針：切断は恒等のまま、二つの augObj の自然性を適用する。
規約：空区間の成分も保持。使われ方：slice/coslice の固定図式の照合。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet

/-- join の宇宙同型の順射は二因子の射に関して自然。 -/
lemma uliftJoinIso_hom_naturality {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso K' L').hom =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso K L).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g) := by
  ext n s
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp_hom f _ _
  · exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp_hom g _ _

/-- join の宇宙同型の逆射も二因子の射に関して自然。 -/
lemma uliftJoinIso_inv_naturality {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso K' L').inv =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso K L).inv ≫ (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) := by
  ext n s
  apply ULift.ext
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugDown_hom f _ _
  · exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugDown_hom g _ _

/-- 左包含の持ち上げは大きい宇宙の左包含と一致。 -/
lemma uliftJoinIso_inl (K L : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L) ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso K L).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{v, u}).obj K) ((SSet.uliftFunctor.{v, u}).obj L) := by
  ext n s
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinAugUp_eq_of_zero L _ (Nat.sub_self _) _ _

/-- 右包含の持ち上げは大きい宇宙の右包含と一致。 -/
lemma uliftJoinIso_inr (K L : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L) ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso K L).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((SSet.uliftFunctor.{v, u}).obj K) ((SSet.uliftFunctor.{v, u}).obj L) := by
  ext n s
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · exact @Subsingleton.elim PUnit inferInstance _ _
  · rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

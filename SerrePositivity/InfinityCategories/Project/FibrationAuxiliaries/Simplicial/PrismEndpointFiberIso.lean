module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedPrismSourceFiberTrivial

/-!
概要：同時端点射の頂点 fiber と始点・終点を順に固定した fiber の同型。
方針：直積値の等式を二つの成分の等式に分ける。
規約：全ての高次単体をそのまま保持する。
使われ方：始点を同値に制限した同時端点射の fiber の可縮性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 概要：二射の組の fiber は第一成分の fiber 上で第二成分を固定した fiber と同型。
方針：同じ単体に付ける条件の対を部分型の入れ子に並べ直す。
規約：fibration 性や quasicategory 性は要求しない。
使われ方：反復した両端固定 lift 空間から実際の同時 fiber への移行。 -/
def vertexFiberPairIso {S M N : SSet.{u}} (s : S ⟶ M) (t : S ⟶ N)
    (m : M _⦋0⦌) (n : N _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (lift s t) (m, n) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι s m ≫ t) n where
  hom := {
    app d := ↾fun x ↦ ⟨⟨x.val, congrArg Prod.fst x.property⟩, congrArg Prod.snd x.property⟩
    naturality := by intros; rfl }
  inv := {
    app d := ↾fun x ↦ ⟨x.val.val, Prod.ext x.val.property x.property⟩
    naturality := by intros; rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    ext x
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro d
    ext x
    rfl

/-- 概要：同値な始点と任意の終点での実際の同時端点射の fiber は可縮。
方針：反復 fiber の可縮性を二成分の fiber の同型で移す。
規約：始点と終点の全ての高次 lift を含む。
使われ方：同時端点射の始点同値への制限の trivial Kan fibration 判定。 -/
lemma pointedPrismEndpointFiber_isContractibleKan {K : SSet.{u + 1}}
    [Quasicategory K] {s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftEndpoints K s t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso
    (vertexFiberPairIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftSource K s t) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismLiftEndpoint K s t)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismFixedEndpoints_isContractibleKan f hf t g)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

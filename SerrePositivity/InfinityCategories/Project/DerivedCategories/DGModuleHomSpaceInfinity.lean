module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeHomComplexInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraDerivedInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentablePresheafValues
/-!
概要：導来加群 ∞ 圏の二変数 Hom 空間の実 ∞ 関手と、同じ全 Hom 複体の pinched 比較。
方針：F1 の twisted arrow の同じ分類図式を使い、実頂点で複体模型へ照合する。
規約：空間値の二変数関手。複体値の二変数化・D(R) 比較・tensor–Hom 随伴は別工程。
使われ方：β5 の実 Hom 空間の全高次関手性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
/-- 直積の普遍射の単体評価を、具体的な二成分へ戻す。 -/
lemma dgHomSpace_lift_app {U V W : SSet.{v}} (f : U ⟶ V) (g : U ⟶ W)
    (n : SimplexCategoryᵒᵖ) (x : U.obj n) :
    (CartesianMonoidalCategory.lift f g).app n x = (f.app n x, g.app n x) := by
  apply Prod.ext
  · exact congrArg (fun h : U ⟶ V ↦ h.app n x)
      (CartesianMonoidalCategory.lift_fst f g)
  · exact congrArg (fun h : U ⟶ W ↦ h.app n x)
      (CartesianMonoidalCategory.lift_snd f g)
/-- 共同評価の実頂点と、第二変数を固定した実表現可能前層の値。 -/
lemma dgHomSpace_joint_vertex {C : SSet.{v}} [Quasicategory C] (x y : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm x), ULift.up y) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm x)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C).app _ _ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C).app _
      ((CartesianMonoidalCategory.lift (𝟙 _) (SSet.const (ULift.up y))).app _ _)
  rw [dgHomSpace_lift_app]
  simp [SSet.const]
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 半自由対象を同じ実導来加群 ∞ 圏の頂点として読む。 -/
abbrev dgSemifreeHomVertex (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P
/-- 実導来加群 ∞ 圏の、両変数の全単体を保持する空間値 Hom 関手。 -/
def dgModuleHomSpaceInfinity :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D).op ⊗
      (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)
/-- 二変数 Hom の同じ実頂点を固定すると、F1 の同じ表現可能前層の値になる。 -/
lemma dgModuleHomSpaceInfinity_vertex (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (dgModuleHomSpaceInfinity R D).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (dgSemifreeHomVertex R D P)),
        ULift.up (dgSemifreeHomVertex R D Q)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity (dgSemifreeHomVertex R D Q)).app
      (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (dgSemifreeHomVertex R D P))) :=
  dgHomSpace_joint_vertex (dgSemifreeHomVertex R D P) (dgSemifreeHomVertex R D Q)
/-- 二変数 Hom 関手の同じ実頂点での値は、同じ全 Hom end の実 pinched 模型と同値。 -/
def dgModuleHomSpaceValueEquivalence (P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((dgModuleHomSpaceInfinity R D).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (dgSemifreeHomVertex R D P)),
        ULift.up (dgSemifreeHomVertex R D Q)))).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (moduleHom R D P.val Q.val)) := by
  rw [dgModuleHomSpaceInfinity_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafValueEquivalence
    (dgSemifreeHomVertex R D P) (dgSemifreeHomVertex R D Q)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomMappingSpaceIso R D P Q))
/-- 非可換 dg 代数の D(A) の二変数空間値 Hom の実 ∞ 関手。 -/
abbrev dgAlgebraHomSpaceInfinity (R : Type u) [CommRing R] (B : Mon (_root_.SerrePositivity.DifferentialGraded.Complex R)) :=
  dgModuleHomSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B)
end SerrePositivity.InfinityCategories.Project.DerivedCategories

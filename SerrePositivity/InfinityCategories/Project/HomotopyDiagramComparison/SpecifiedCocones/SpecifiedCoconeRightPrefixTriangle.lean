module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRootedTetrahedron

/-!
概要：同じ右修正四面体の δ₃ 面を、付加辺と標準右辺を持つ実際の三角形として取り出す。
方針：四面体の既存の二辺・底・始点を、面の単体恒等式で回収する。
規約：新しい三角形を選ばない。使われ方：右終点比較と共通長辺への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- δ₃ 面の第二辺は、同じ四面体の辺 12 を表す。 -/
lemma tetrahedronPrefix_standardEdge_shape :
    (stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) :
      (Δ[1] : SSet.{u}) ⟶ Δ[3]) =
      stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- native な右三角形の右退化を δ₃ 面へ戻すと、元の二単体そのもの。 -/
lemma tetrahedronPrefix_base_shape :
    (stdSimplex.δ (3 : Fin 4) ≫ stdSimplex.σ (2 : Fin 3) :
      (Δ[2] : SSet.{u}) ⟶ Δ[2]) = 𝟙 _ := by
  apply SSet.yonedaEquiv.injective
  decide

variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "T" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "a₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionEdge c hc g (j ≫ p)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightStandardTransportEdge hp p c hc dB dC
local notation "r" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p)
local notation "σ" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC

/-- 右修正四面体の元の付加辺と標準右辺を含む、同じ δ₃ 面。 -/
def specifiedCoconeRightPrefixRootedTriangle :
    (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (f ≫ (i ≫ p)) :=
  stdSimplex.δ (3 : Fin 4) ≫ T

/-- 第一辺は元の実際の右付加比較辺そのもの。 -/
lemma specifiedCoconeRightPrefixRootedTriangle_first :
    stdSimplex.δ (2 : Fin 3) ≫ specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC =
      SSet.yonedaEquiv.symm (a₀).edge :=
  (Category.assoc _ _ _).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron_firstEdge hp p c hc dB dC)

/-- 第二辺は同じ標準右輸送辺を共通部分へ制限したもの。 -/
lemma specifiedCoconeRightPrefixRootedTriangle_second :
    stdSimplex.δ (0 : Fin 3) ≫ specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC =
      SSet.yonedaEquiv.symm (k).edge ≫ r :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ T) tetrahedronPrefix_standardEdge_shape).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron_standardEdge hp p c hc dB dC))

/-- この面の底は元の native な右二単体そのもの。 -/
lemma specifiedCoconeRightPrefixRootedTriangle_projection :
    specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC ≫ q =
      SSet.yonedaEquiv.symm (σ).simplex :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ stdSimplex.δ (3 : Fin 4) ≫ z)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron_base hp p c hc dB dC)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z ↦ z ≫ SSet.yonedaEquiv.symm (σ).simplex)
            tetrahedronPrefix_base_shape).trans (Category.id_comp _))))

/-- 同じ面の始点は元の共通余錐の点に固定される。 -/
lemma specifiedCoconeRightPrefixRootedTriangle_initial :
    (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫
        specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC = SSet.yonedaEquiv.symm c :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ stdSimplex.δ (1 : Fin 2) ≫ z)
      (specifiedCoconeRightPrefixRootedTriangle_first hp p c hc dB dC)).trans
        (a₀).δ_one_yonedaEquiv_symm)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

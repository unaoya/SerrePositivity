module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiniteCellDenominators
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedYonedaExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberEdgesFullyFaithful

/-! # 実 Yoneda に沿う有限 cell 生成条件の保存と反映

概要：共通宇宙の前三角 dg nerve の実安定閉包は、代表加群の有限 cell 条件と一致する。
方針：完全充満忠実な実 Yoneda が実閉包・分母条件を反映することを使う。
規約：対象宇宙の持ち上げを明示。使われ方：有限 cell roof の分母を元の dg 模型へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 共通宇宙に上げた指定対象の実頂点集合。 -/
def dgLiftedGeneratorVertices (P : Set D) :
    Set ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) v} D)) _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) v} A D).obj '' P)

/-- 共通宇宙の全加群への実 Yoneda は充満忠実。 -/
lemma dgPretriangulatedYoneda_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp (dgYoneda A D))) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYonedaNerve_isFullyFaithful A D).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful A (RightModule A D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable A D))
  rwa [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYoneda_inclusion] at h

/-- 指定実頂点の Yoneda 像は、指定代表加群の実頂点の集合そのもの。 -/
lemma dgLiftedGeneratorVertices_yoneda_image (P : Set D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
      (_root_.SerrePositivity.DifferentialGraded.dgYoneda A D))).app (Opposite.op ⦋0⦌) '' dgLiftedGeneratorVertices A D P =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleGeneratorVertices A D P := by
  change _ '' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp A D).obj '' P)) =
    (fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (representable A x)) '' P
  rw [Set.image_image, Set.image_image]
  apply congrArg (fun f : D → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌ => f '' P)
  funext x
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex _ _

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 共通宇宙の元の指定対象の実閉包条件は、代表加群の有限 cell 条件と一致する。 -/
theorem dgLifted_stableVertexClosure_iff_finiteCell (P : Set D) (x : D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (dgLiftedGeneratorVertices A D P)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) v} A D).obj x)) ↔
      _root_.SerrePositivity.DifferentialGraded.homotopyFiniteCellOver A D P ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).obj
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A x))) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftNerve_isStable A D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedYoneda_isExactFunctor A D
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableVertexClosure_image_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown A D).comp (dgYoneda A D)))
    (dgPretriangulatedYoneda_isFullyFaithful A D) (dgLiftedGeneratorVertices A D P)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp A D).obj x))
  rw [dgLiftedGeneratorVertices_yoneda_image, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at h
  exact h.symm.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModule_stableVertexClosure_iff_finiteCell A D P _)

/-- 実 Yoneda は、指定対象で生成した実 cofiber 分母条件を反映する。 -/
theorem dgPretriangulatedYoneda_cofiberEdges_iff (P : Set D)
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) v} D)) _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) v} D))) x y) :
    (f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown A D).comp (dgYoneda A D))))).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleGeneratorVertices A D P) z} ↔
      f.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
        {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (dgLiftedGeneratorVertices A D P) z} := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftNerve_isStable A D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedYoneda_isExactFunctor A D
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_map_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown A D).comp (dgYoneda A D)))
    (dgPretriangulatedYoneda_isFullyFaithful A D) (dgLiftedGeneratorVertices A D P) f
  rwa [dgLiftedGeneratorVertices_yoneda_image] at h

end SerrePositivity.InfinityCategories.Project.DerivedCategories

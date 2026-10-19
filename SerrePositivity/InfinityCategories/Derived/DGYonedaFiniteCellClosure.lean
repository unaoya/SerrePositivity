module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiniteCellDenominators
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedYonedaExact
public import SerrePositivity.InfinityCategories.Derived.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.Stable.CofiberEdgesFullyFaithful

/-! # 実 Yoneda に沿う有限 cell 生成条件の保存と反映

概要：共通宇宙の前三角 dg nerve の実安定閉包は、代表加群の有限 cell 条件と一致する。
方針：完全充満忠実な実 Yoneda が実閉包・分母条件を反映することを使う。
規約：対象宇宙の持ち上げを明示。使われ方：有限 cell roof の分母を元の dg 模型へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 共通宇宙に上げた指定対象の実頂点集合。 -/
def dgLiftedGeneratorVertices (P : Set D) :
    Set ((dgNerve A (DGUniverseLift.{v, max (u + 1) v} D)) _⦋0⦌) :=
  Simplex.vertex '' ((dgUniverseLiftUp.{u, v, max (u + 1) v} A D).obj '' P)

/-- 共通宇宙の全加群への実 Yoneda は充満忠実。 -/
lemma dgPretriangulatedYoneda_isFullyFaithful :
    IsFullyFaithful (dgNerve.map
      ((dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp (dgYoneda A D))) := by
  have h := (dgRepleteYonedaNerve_isFullyFaithful A D).comp
    (dgFullSubcategoryInclusionNerve_isFullyFaithful A (RightModule A D)
      (dgHomotopyRepresentable A D))
  rwa [← dgNerve.map_comp, dgRepleteYoneda_inclusion] at h

/-- 指定実頂点の Yoneda 像は、指定代表加群の実頂点の集合そのもの。 -/
lemma dgLiftedGeneratorVertices_yoneda_image (P : Set D) :
    (dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
      (dgYoneda A D))).app (Opposite.op ⦋0⦌) '' dgLiftedGeneratorVertices A D P =
      dgModuleGeneratorVertices A D P := by
  change _ '' (Simplex.vertex '' ((dgUniverseLiftUp A D).obj '' P)) =
    (fun x => Simplex.vertex (representable A x)) '' P
  rw [Set.image_image, Set.image_image]
  apply congrArg (fun f : D → (dgModuleNerve A D) _⦋0⦌ => f '' P)
  funext x
  exact dgFunctorNerve_vertex _ _

variable [IsDGPretriangulated A D]

/-- 共通宇宙の元の指定対象の実閉包条件は、代表加群の有限 cell 条件と一致する。 -/
theorem dgLifted_stableVertexClosure_iff_finiteCell (P : Set D) (x : D) :
    StableVertexClosure (dgLiftedGeneratorVertices A D P)
      (Simplex.vertex ((dgUniverseLiftUp.{u, v, max (u + 1) v} A D).obj x)) ↔
      homotopyFiniteCellOver A D P ((moduleToHomotopy A D).obj
        (ForgetEnrichment.of (Complex A) (representable A x))) := by
  let := dgUniverseLiftNerve_isStable A D
  let := dgPretriangulatedYoneda_isExactFunctor A D
  have h := stableVertexClosure_image_iff
    (dgNerve.map ((dgUniverseLiftDown A D).comp (dgYoneda A D)))
    (dgPretriangulatedYoneda_isFullyFaithful A D) (dgLiftedGeneratorVertices A D P)
    (Simplex.vertex ((dgUniverseLiftUp A D).obj x))
  rw [dgLiftedGeneratorVertices_yoneda_image, dgFunctorNerve_vertex] at h
  exact h.symm.trans (dgModule_stableVertexClosure_iff_finiteCell A D P _)

/-- 実 Yoneda は、指定対象で生成した実 cofiber 分母条件を反映する。 -/
theorem dgPretriangulatedYoneda_cofiberEdges_iff (P : Set D)
    {x y : (dgNerve A (DGUniverseLift.{v, max (u + 1) v} D)) _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj
      (dgNerve A (DGUniverseLift.{v, max (u + 1) v} D))) x y) :
    (f.map ((truncation 2).map (dgNerve.map
      ((dgUniverseLiftDown A D).comp (dgYoneda A D))))).edge ∈ cofiberLocalizingEdges
      {z | StableVertexClosure (dgModuleGeneratorVertices A D P) z} ↔
      f.edge ∈ cofiberLocalizingEdges
        {z | StableVertexClosure (dgLiftedGeneratorVertices A D P) z} := by
  let := dgUniverseLiftNerve_isStable A D
  let := dgPretriangulatedYoneda_isExactFunctor A D
  have h := cofiberStableEdges_map_iff
    (dgNerve.map ((dgUniverseLiftDown A D).comp (dgYoneda A D)))
    (dgPretriangulatedYoneda_isFullyFaithful A D) (dgLiftedGeneratorVertices A D P) f
  rwa [dgLiftedGeneratorVertices_yoneda_image] at h

end SerrePositivity.InfinityCategories

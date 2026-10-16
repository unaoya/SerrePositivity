module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftBaseChange
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftEdges

/-! # The four families in mixed source/target comparison

Exact interchange and tuple associativity put both orders of comparison
over the same actual base map and fixed strict-lift vertex data.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftMixedComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (X Y W V : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) (h : W ⟶ V)
  (φ : ResolutionLiftPrecomposition.FrameMap f)

abbrev castMap := ResolutionLiftSpace.baseChange (Category.assoc f.base g h.base)
abbrev preTail := ResolutionLiftPrecomposition.map X Y V f (g ≫ h.base) φ
abbrev postTail := ResolutionLiftPostcomposition.map X W V (f.base ≫ g) h ≫ castMap X Y W V f g h
abbrev boundary := postBoundary Y W V g h ≫ preTail X Y W V f g h φ
abbrev space := RelativeChoiceSpace.obj (vertexInclusion Y W g) (boundary X Y W V f g h φ)

abbrev familyA := postLeft hcof Y W V g h ≫ preTail X Y W V f g h φ
abbrev familyB := preRight hcof X Y W f g ≫ postTail X Y W V f g h
abbrev familyC := postRight hcof Y W V g h ≫ preTail X Y W V f g h φ
abbrev tuplePost := VertexTuples.map (postStrict Y W V g h)
abbrev vertexPost := VertexTuples.verticesMap (postStrict Y W V g h)
abbrev familyD := tuplePost Y W V g h ≫ preRight hcof X Y V f (g ≫ h.base)

lemma familyA_vertices : vertexInclusion Y W g ≫ familyA hcof X Y W V f g h φ =
    boundary X Y W V f g h φ :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ preTail X Y W V f g h φ) (postLeft_vertices hcof Y W V g h))

lemma familyC_vertices : vertexInclusion Y W g ≫ familyC hcof X Y W V f g h φ =
    boundary X Y W V f g h φ :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ preTail X Y W V f g h φ) (postRight_vertices hcof Y W V g h))

lemma initial_interchange : preLeft hcof X Y W f g φ ≫ postTail X Y W V f g h =
    familyA hcof X Y W V f g h φ :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => CoherentLiftTuples.interpolation hcof Y W g ≫ k)
      (ResolutionLiftFunctorLaws.interchange X Y W V f g h φ)).trans
        (Category.assoc _ _ _).symm)

include hcof in
lemma pre_boundary_transport : preBoundary X Y W f g ≫ postTail X Y W V f g h =
    boundary X Y W V f g h φ := by
  calc
    _ = (vertexInclusion Y W g ≫ preLeft hcof X Y W f g φ) ≫ postTail X Y W V f g h :=
      congrArg (fun k => k ≫ postTail X Y W V f g h) (preLeft_vertices hcof X Y W f g φ).symm
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun k => vertexInclusion Y W g ≫ k)
        (initial_interchange hcof X Y W V f g h φ)).trans
        (familyA_vertices hcof X Y W V f g h φ))

include φ in
lemma familyB_vertices : vertexInclusion Y W g ≫ familyB hcof X Y W V f g h =
    boundary X Y W V f g h φ :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ postTail X Y W V f g h) (preRight_vertices hcof X Y W f g)).trans
      (pre_boundary_transport hcof X Y W V f g h φ))

omit [ModelCategory SSet.{v}] in
lemma post_vertex_square : vertexInclusion Y W g ≫ tuplePost Y W V g h =
    vertexPost Y W V g h ≫ vertexInclusion Y V (g ≫ h.base) := VertexTuples.inclusion_map _

lemma familyC_as_pre : tuplePost Y W V g h ≫ preLeft hcof X Y V f (g ≫ h.base) φ =
    familyC hcof X Y W V f g h φ := by
  simp only [familyC, postRight, preLeft, preTail, Category.assoc]

include hcof in
lemma post_boundary_transport : vertexPost Y W V g h ≫ preBoundary X Y V f (g ≫ h.base) =
    boundary X Y W V f g h φ := by
  calc
    _ = vertexPost Y W V g h ≫ (vertexInclusion Y V (g ≫ h.base) ≫
        preLeft hcof X Y V f (g ≫ h.base) φ) :=
      congrArg (fun k => vertexPost Y W V g h ≫ k)
        (preLeft_vertices hcof X Y V f (g ≫ h.base) φ).symm
    _ = vertexInclusion Y W g ≫ tuplePost Y W V g h ≫
        preLeft hcof X Y V f (g ≫ h.base) φ := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ preLeft hcof X Y V f (g ≫ h.base) φ) (post_vertex_square Y W V g h).symm
    _ = _ := (congrArg (fun k => vertexInclusion Y W g ≫ k)
      (familyC_as_pre hcof X Y W V f g h φ)).trans (familyC_vertices hcof X Y W V f g h φ)

include φ in
lemma familyD_vertices : vertexInclusion Y W g ≫ familyD hcof X Y W V f g h =
    boundary X Y W V f g h φ := by
  calc
    _ = (vertexInclusion Y W g ≫ tuplePost Y W V g h) ≫
        preRight hcof X Y V f (g ≫ h.base) := (Category.assoc _ _ _).symm
    _ = _ := (congrArg (fun k => k ≫ preRight hcof X Y V f (g ≫ h.base))
      (post_vertex_square Y W V g h)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => vertexPost Y W V g h ≫ k)
            (preRight_vertices hcof X Y V f (g ≫ h.base))).trans
              (post_boundary_transport hcof X Y W V f g h φ)))

abbrev tuplePre := VertexTuples.map (preStrict X Y W f g)
abbrev vertexPre := VertexTuples.verticesMap (preStrict X Y W f g)

omit [ModelCategory SSet.{v}] in
lemma pre_vertex_square : vertexInclusion Y W g ≫ tuplePre X Y W f g =
    vertexPre X Y W f g ≫ vertexInclusion X W (f.base ≫ g) := VertexTuples.inclusion_map _

lemma familyB_as_post : tuplePre X Y W f g ≫ postLeft hcof X W V (f.base ≫ g) h ≫
    castMap X Y W V f g h = familyB hcof X Y W V f g h := by
  simp only [familyB, preRight, postLeft, postTail, Category.assoc]

include hcof in
lemma mixed_boundary_transport : vertexPre X Y W f g ≫
    (postBoundary X W V (f.base ≫ g) h ≫ castMap X Y W V f g h) =
      boundary X Y W V f g h φ := by
  calc
    _ = vertexPre X Y W f g ≫ (vertexInclusion X W (f.base ≫ g) ≫
        postLeft hcof X W V (f.base ≫ g) h) ≫ castMap X Y W V f g h :=
      congrArg (fun k => vertexPre X Y W f g ≫ k ≫ castMap X Y W V f g h)
        (postLeft_vertices hcof X W V (f.base ≫ g) h).symm
    _ = vertexInclusion Y W g ≫ tuplePre X Y W f g ≫
        postLeft hcof X W V (f.base ≫ g) h ≫ castMap X Y W V f g h := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ postLeft hcof X W V (f.base ≫ g) h ≫ castMap X Y W V f g h)
          (pre_vertex_square X Y W f g).symm
    _ = _ := (congrArg (fun k => vertexInclusion Y W g ≫ k)
      (familyB_as_post hcof X Y W V f g h)).trans (familyB_vertices hcof X Y W V f g h φ)

omit [ModelCategory SSet.{v}] in
lemma tuple_interchange : tuplePre X Y W f g ≫
    VertexTuples.map (postStrict X W V (f.base ≫ g) h) ≫
      CoherentLiftBaseChange.tuples (Category.assoc f.base g h.base) =
        tuplePost Y W V g h ≫ VertexTuples.map (preStrict X Y V f (g ≫ h.base)) := by
  ext n a
  funext i
  apply Subtype.ext
  exact Category.assoc _ _ _

lemma final_interchange : tuplePre X Y W f g ≫ postRight hcof X W V (f.base ≫ g) h ≫
    castMap X Y W V f g h = familyD hcof X Y W V f g h := by
  have hi := congrArg (fun k => tuplePre X Y W f g ≫
    VertexTuples.map (postStrict X W V (f.base ≫ g) h) ≫ k)
      (CoherentLiftBaseChange.interpolation hcof (Category.assoc f.base g h.base))
  have ht := congrArg (fun k => k ≫ CoherentLiftTuples.interpolation hcof X V (f.base ≫ g ≫ h.base))
    (tuple_interchange X Y W V f g h)
  calc
    _ = tuplePre X Y W f g ≫ VertexTuples.map (postStrict X W V (f.base ≫ g) h) ≫
        CoherentLiftBaseChange.tuples (Category.assoc f.base g h.base) ≫
          CoherentLiftTuples.interpolation hcof X V (f.base ≫ g ≫ h.base) := by
      simpa only [postRight, Category.assoc] using hi
    _ = _ := by simpa only [familyD, preRight, Category.assoc] using ht

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftMixedComparison

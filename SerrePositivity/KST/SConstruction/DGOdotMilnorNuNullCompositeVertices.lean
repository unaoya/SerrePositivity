module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuUpperTriangleEdges
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuStandardZeroNullHom
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullTriangleEdges
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuProjectionNullHom
public import SerrePositivity.KST.SConstruction.CoherentTriangleMappingEdge

/-!
概要：元下三角形の合成端を指定商比較の同じ二つの実合成へ照合する。
方針：元二短辺を復号し、元最大 path の全 Hom 頂点を端点輸送する。
規約：元二胞体・元共有辺を保持。使われ方：混合零 Hom の指定境界の貼り合わせ。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma nullMaximumCompositePath :
    coherentEndpointPathComposite
      (show (ULift.up (0 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 1 by decide)
      (show (ULift.up (1 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 2 by decide) =
      dgOdotMilnorNuNullUpperMaximalPath.{u} := by
  apply SimplicialThickening.Path.ext
  ext ⟨x⟩
  fin_cases x <;> simp [coherentEndpointPathComposite, coherentEndpointPath,
    dgOdotMilnorNuNullUpperMaximalPath, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPath]

private lemma nullMaximalVertexOfEdges (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} _⦋2⦌)
    (X Y Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h₂ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (2 : Fin 3) s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (h₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}.δ (0 : Fin 3) s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge)
    (hs : s.obj ⟨ULift.up (0 : Fin 3)⟩ = X)
    (ht : s.obj ⟨ULift.up (2 : Fin 3)⟩ = Z) :
    (s.map ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up (2 : Fin 3)⟩ ≫
      eqToHom (congrArg₂ (fun A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1} => SimplicialCategory.sHom A B)
        hs ht)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) X Z (f ≫ g) := by
  have hx : s.obj ⟨ULift.up (0 : Fin 3)⟩ = X :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).1) h₂
  have hy : s.obj ⟨ULift.up (1 : Fin 3)⟩ = Y :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).2.1) h₂
  have hz : s.obj ⟨ULift.up (2 : Fin 3)⟩ = Z :=
    congrArg (fun e => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e).2.1) h₀
  subst X Y Z
  have hf : coherentSimplexArrow s 0 1 (by decide) = f :=
    coherentSimplexArrow_of_edge_face s (SimplexCategory.δ (2 : Fin 3)) f h₂
  have hg : coherentSimplexArrow s 1 2 (by decide) = g :=
    coherentSimplexArrow_of_edge_face s (SimplexCategory.δ (0 : Fin 3)) g h₀
  let e := coherentSimplexCompositionEdge s 0 1 2 (by decide) (by decide)
  let b := (nerve.edgeMk (coherentEndpointPathToComposite
    (show (ULift.up (0 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 1 by decide)
    (show (ULift.up (1 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 2 by decide))).map
      (s.map ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up (2 : Fin 3)⟩)
  have hv := b.tgt_eq.symm.trans e.tgt_eq
  have hp : nerveEquiv.symm dgOdotMilnorNuNullUpperMaximalPath.{u} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u} := ComposableArrows.ext₀ rfl
  simpa only [nullMaximumCompositePath, hp, hf, hg, eqToHom_refl, Category.comp_id] using hv

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "A" => dgKInputStableValue R (dgOdotMilnorCellInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：元実下三角形の最大 path は元包含・元商の同じ実合成。
方針：元の二短辺と同じ固定 ν 端点を使う。
規約：全 Hom の元頂点の等号。使われ方：指定商混合面の零端点。 -/
lemma dgOdotMilnorNuNullLowerHom_maximal :
    (dgOdotMilnorNuNullTriangleHom R d 1).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B)
        (dgOdotMilnorNuNullComposite R d) :=
  nullMaximalVertexOfEdges (dgOdotMilnorNuNullTriangle R d 1) (K) (A) (B)
    (dgOdotMilnorFlatKernelExactMap R d) (dgOdotMilnorCellProjectionExactMap R d)
    (dgOdotMilnorNuNullLowerTriangle_inclusion R d)
    (dgOdotMilnorNuNullLowerTriangle_projection R d)
    (dgOdotMilnorNuNullTriangle_source R d 1) (dgOdotMilnorNuNullTriangle_target R d 1)

/-- 概要：同じ絶対下三角形の最大 path は元完備化後射影との同じ実合成。
方針：元絶対面の二短辺と同じ固定 ν 端点を使う。
規約：元提示の最大 path を保持。使われ方：指定商混合面の一端点。 -/
lemma dgOdotMilnorNuAbsoluteLowerHom_maximal (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    (dgOdotMilnorNuAbsoluteTriangleHom R d h 1).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B)
        (dgOdotMilnorNuProjectionNullTargetComposite R d h) :=
  nullMaximalVertexOfEdges (dgOdotMilnorNuAbsoluteNullTriangle R d h 1) (K) (A) (B)
    (dgOdotMilnorFlatKernelExactMap R d) (dgOdotMilnorNuPerfectSequence R d h).projection
    (dgOdotMilnorNuAbsoluteLowerTriangle_inclusion R d h)
    (dgOdotMilnorNuAbsoluteLowerTriangle_projection R d h)
    (dgOdotMilnorNuAbsoluteTriangle_source R d h 1)
    (dgOdotMilnorNuAbsoluteTriangle_target R d h 1)

/-- 概要：元実上三角形の最大 path は元実零角経由の同じ合成。
方針：元の零角への二短辺と同じ固定 ν 端点を使う。
規約：元全 Hom 頂点の等号。使われ方：指定零角比較の実面側の端点。 -/
lemma dgOdotMilnorNuNullUpperHom_maximal :
    (dgOdotMilnorNuNullTriangleHom R d 0).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B)
        (dgOdotMilnorNuNullTopComposite R d) :=
  nullMaximalVertexOfEdges (dgOdotMilnorNuNullTriangle R d 0) (K)
    (dgKInputStableValue R (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d))) (B)
    (dgOdotMilnorNuZeroActualLeft R d) (dgOdotMilnorNuZeroActualTop R d)
    (dgOdotMilnorNuNullUpperTriangle_left R d) (dgOdotMilnorNuNullUpperTriangle_top R d)
    (dgOdotMilnorNuNullTriangle_source R d 0) (dgOdotMilnorNuNullTriangle_target R d 0)

/-- 概要：同じ絶対上三角形の最大 path は元標準零角経由の同じ合成。
方針：元標準零角への二短辺と同じ固定 ν 端点を使う。
規約：元絶対二胞体を保持。使われ方：指定零角比較の絶対面側の端点。 -/
lemma dgOdotMilnorNuAbsoluteUpperHom_maximal (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    (dgOdotMilnorNuAbsoluteTriangleHom R d h 0).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B)
        (dgOdotMilnorNuStandardZeroComposite R d (fromZeroCategory (B))) :=
  nullMaximalVertexOfEdges (dgOdotMilnorNuAbsoluteNullTriangle R d h 0) (K)
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} (B) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (K)) (fromZeroCategory (B))
    (dgOdotMilnorNuAbsoluteUpperTriangle_left R d h)
    (dgOdotMilnorNuAbsoluteUpperTriangle_top R d h)
    (dgOdotMilnorNuAbsoluteTriangle_source R d h 0)
    (dgOdotMilnorNuAbsoluteTriangle_target R d h 0)

end SerrePositivity.KST.SConstruction

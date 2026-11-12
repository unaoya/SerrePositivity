module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullDiagonal

/-!
概要：元下三角形の全 Hom 像も同じ零合成の終成分へ置く。
方針：元共有対角の終対象性を上三角形から戻し、全 path への元包含辺で移す。
規約：元二単体の全 Hom 作用を保持。使われ方：固定 ν 実零化面の全境界充填。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：元上三角形の各 path の通常完全射は終関手。
方針：同じ全 Hom 像の終対象性を通常射の頂点へ回収する。
規約：元 path の像を変更しない。使われ方：共有対角の終対象性。 -/
lemma dgOdotMilnorNuNullUpperPathFunctor_isTerminal (P : DGOdotMilnorNuNullTrianglePath.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv
      (dgOdotMilnorNuNullTriangleStableObject R d 0)
      (dgOdotMilnorNuNullTriangleStableObject R d 2)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (dgOdotMilnorNuNullTriangle R d 0)).map P)) := by
  have h := congrArg (fun x => (dgOdotMilnorNuNullUpperHomInclusion R d).app
    (Opposite.op ⦋0⦌) x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex (dgOdotMilnorNuNullTriangle R d 0) P)
  exact h.symm ▸ dgOdotMilnorNuNullTriangle_path_isTerminal R d P

/-- 概要：元下三角形の共有対角 path の像は終関手。
方針：元共有一単体の依存射データの等号で上三角形の終対象性を移す。
規約：両端点と元通常射を同時に保持。使われ方：下三角形の全 path の零性。 -/
lemma dgOdotMilnorNuNullLowerDiagonal_isTerminal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv
      ((dgOdotMilnorNuNullTriangle R d 1).obj ⟨ULift.up (0 : Fin 3)⟩)
      ((dgOdotMilnorNuNullTriangle R d 1).obj ⟨ULift.up (2 : Fin 3)⟩)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (dgOdotMilnorNuNullTriangle R d 1)).map
        dgOdotMilnorNuNullDiagonalPath.{u})) := by
  let P : (Σ X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}, X ⟶ Y) → Prop :=
    fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv t.1 t.2.1 t.2.2)
  have he := (dgOdotMilnorNuNullTriangle_diagonal_data R d 0).symm.trans
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (dgOdotMilnorNuNullTriangle_diagonal R d)).trans
      (dgOdotMilnorNuNullTriangle_diagonal_data R d 1))
  have ht : P ⟨_, _, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor
      (dgOdotMilnorNuNullTriangle R d 0)).map dgOdotMilnorNuNullDiagonalPath.{u}⟩ :=
    dgOdotMilnorNuNullUpperPathFunctor_isTerminal R d _
  have hn : P ⟨_, _, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor
      (dgOdotMilnorNuNullTriangle R d 1)).map dgOdotMilnorNuNullDiagonalPath.{u}⟩ :=
    Eq.mp (congrArg P he) ht
  exact hn

/-- 概要：元下三角形の全 Hom 作用。
方針：元の同じ二単体の端点間 Hom 写像を使う。
規約：端点輸送前の元写像。使われ方：同じ全零成分への制限。 -/
def dgOdotMilnorNuNullLowerHom : nerve DGOdotMilnorNuNullTrianglePath.{u} ⟶
    SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1})
      ((dgOdotMilnorNuNullTriangle R d 1).obj ⟨ULift.up (0 : Fin 3)⟩)
      ((dgOdotMilnorNuNullTriangle R d 1).obj ⟨ULift.up (2 : Fin 3)⟩) :=
  (dgOdotMilnorNuNullTriangle R d 1).map ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up (2 : Fin 3)⟩

/-- 概要：元下三角形の完全関手圏。
方針：元の両端を同じ完全関手圏へ保持する。
規約：固定 ν への輸送前。使われ方：元全 Hom の終頂点性。 -/
abbrev DGOdotMilnorNuNullLowerExactFunctors : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors ((dgOdotMilnorNuNullTriangle R d 1).obj ⟨ULift.up (0 : Fin 3)⟩)
    ((dgOdotMilnorNuNullTriangle R d 1).obj ⟨ULift.up (2 : Fin 3)⟩)

local instance nuNullLowerExact_quasicategory :
    Quasicategory (DGOdotMilnorNuNullLowerExactFunctors R d) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors_quasicategory _ _

/-- 概要：元の共有対角 path は同じ任意 path に包含される。
方針：元面 δ₁ の両端像だけが共有 path の台をなすことを使う。
規約：元の包含射。使われ方：下三角形の全 Hom の比較辺。 -/
def dgOdotMilnorNuNullDiagonalToPath (P : DGOdotMilnorNuNullTrianglePath.{u}) :
    dgOdotMilnorNuNullDiagonalPath.{u} ⟶ P := by
  refine ⟨homOfLE (show dgOdotMilnorNuNullDiagonalPath.{u}.I ⊆ P.I from ?_)⟩
  rintro x ⟨y, hy, rfl⟩
  have h : y = ULift.up (0 : Fin 2) ∨ y = ULift.up (1 : Fin 2) := by
    have h := y.down.isLt
    rcases y with ⟨y⟩
    fin_cases y <;> simp
  rcases h with rfl | rfl
  · exact P.left
  · exact P.right

/-- 概要：元下三角形の任意 path の全 Hom 頂点は終関手。
方針：同じ共有対角からの元包含辺を Kan Hom に写して終対象性を移す。
規約：元全 Hom 作用を保持。使われ方：同じ実下三角形の零成分因子分解。 -/
lemma dgOdotMilnorNuNullLowerHom_path_isTerminal (P : DGOdotMilnorNuNullTrianglePath.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((dgOdotMilnorNuNullLowerHom R d ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (DGOdotMilnorNuNullLowerExactFunctors R d)).ι).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex P)) := by
  let i := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (DGOdotMilnorNuNullLowerExactFunctors R d)).ι
  let e : (nerve DGOdotMilnorNuNullTrianglePath.{u}).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex P) :=
    SSet.Edge.mk (ComposableArrows.mk₁ (dgOdotMilnorNuNullDiagonalToPath P))
      (ComposableArrows.ext₀ rfl) (ComposableArrows.ext₀ rfl)
  let e' := e.map (dgOdotMilnorNuNullLowerHom R d)
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e'.toTruncated := IsGroupoid.all_isIso
    (C := hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (DGOdotMilnorNuNullLowerExactFunctors R d) : SSet)) _
  have eiso := @asIso _ _ _ _
    (SSet.Truncated.HomotopyCategory.homMk (e'.map i).toTruncated) (hi.map i)
  have hv := congrArg (fun x => i.app (Opposite.op ⦋0⦌) x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex (dgOdotMilnorNuNullTriangle R d 1)
      dgOdotMilnorNuNullDiagonalPath.{u})
  have ht := hv ▸ dgOdotMilnorNuNullLowerDiagonal_isTerminal R d
  exact ht.of_vertexIso eiso

end SerrePositivity.KST.SConstruction

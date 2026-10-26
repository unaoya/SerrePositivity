module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullDiagonalComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingFaceEndpoints

/-!
概要：元共有対角比較を同じ固定端点の実ホモトピーとして保持する。
方針：元 Hom 辺の標準区間比較を fiber のまま uncurry する。
規約：元共有対角比較の同型の類と両端点の全経路を保持。使われ方：上下比較 prism の同じ対角面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma diagonalIdentityParameter {X : SSet.{u}} (x : X _⦋0⦌) :
    SSet.yonedaEquiv.symm (SSet.Edge.id x).edge = (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).edge = PinchedHom.constant x 1
  exact (pinchedConstant_one x).symm

private lemma diagonalIdentityVertexPath (A : StableQCat.{u}) :
    fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (stableVertex A) =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (stableArrow (𝟙 A)).edge := by
  have hi : SSet.yonedaEquiv.symm (stableArrow (𝟙 A)).edge =
      (SSet.const (stableVertex A) : (Δ[1] : SSet.{u + 1}) ⟶ StableInfinity.{u}) := by
    change SSet.yonedaEquiv.symm (coherentNerveEdge (C := StableQCat.{u}) (𝟙 A)).edge = _
    rw [coherentNerveEdge_id]
    exact diagonalIdentityParameter _
  simp only [SSet.yonedaEquiv_symm_zero, hi, SSet.comp_const]

variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : DGGluingMilnorSquare R d)
local notation "A" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "F" => dgOdotMilnorNuNullDiagonalMap R d
local notation "G" => dgOdotMilnorNuAbsoluteDiagonalMap R d h

/-- 概要：元共有対角比較の同じ豊穣 Hom 辺の固定端点区間表示。
方針：元の同じパラメータ辺を標準 coherent 区間比較へ写す。
規約：元辺を選び直さない。使われ方：端点固定の実共有対角比較。 -/
def dgOdotMilnorNuNullDiagonalIntervalEdge :
    (intervalMappingSpace (coherentNerveVertex (C := StableQCat.{u + 1}) (A))
      (coherentNerveVertex (C := StableQCat.{u + 1}) (B))).Edge
        (intervalMappingVertexOfEdge (coherentNerveEdge (C := StableQCat.{u + 1}) (F)))
        (intervalMappingVertexOfEdge (coherentNerveEdge (C := StableQCat.{u + 1}) (G))) :=
  coherentHomIntervalEdgeFromParameter (C := StableQCat.{u + 1}) (F) (G)
    (dgOdotMilnorNuNullDiagonalCoreEdge R d h)

/-- 概要：元共有対角比較を元二辺の関手空間の同じ実辺として保持する。
方針：同じ固定端点 fiber の包含で元区間辺を写す。
規約：既公開商比較と同じ元辺。使われ方：同じ実ホモトピーの読み出し。 -/
def dgOdotMilnorNuNullDiagonalArrowFunctorEdge : SSet.Truncated.Edge
    (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u + 2})).obj StableInfinity.{u + 1}))
      (functorVertex (SSet.yonedaEquiv.symm (stableArrow (F)).edge))
      (functorVertex (SSet.yonedaEquiv.symm (stableArrow (G)).edge)) :=
  ((dgOdotMilnorNuNullDiagonalIntervalEdge R d h).map
    (vertexFiberι ((pre (boundary 1).ι).app StableInfinity.{u + 1})
      (functorVertex (intervalMappingBoundary (coherentNerveVertex (C := StableQCat.{u + 1}) (A))
        (coherentNerveVertex (C := StableQCat.{u + 1}) (B)))))).toTruncated

/-- 概要：元共有対角比較の同じ固定端点の実ホモトピー。
方針：同じ元関手辺を uncurry する。
規約：元二辺と元パラメータを保持。使われ方：上下比較 prism の同じ対角面。 -/
def dgOdotMilnorNuNullDiagonalArrowHomotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm (stableArrow (F)).edge)
    (SSet.yonedaEquiv.symm (stableArrow (G)).edge) :=
  simplicialHomotopyOfFunctorEdge (dgOdotMilnorNuNullDiagonalArrowFunctorEdge R d h)

/-- 概要：元共有対角ホモトピーは同じ固定端点区間の全 uncurry。
方針：元辺写像の Yoneda 自然性を使う。
規約：全パラメータの等号。使われ方：元端点経路の厳密保持。 -/
lemma dgOdotMilnorNuNullDiagonalArrowHomotopy_uncurry :
    (dgOdotMilnorNuNullDiagonalArrowHomotopy R d h).h =
      intervalMappingUncurry (SSet.yonedaEquiv.symm
        (dgOdotMilnorNuNullDiagonalIntervalEdge R d h).edge) :=
  congrArg (fun f => uncurry f)
    (SSet.yonedaEquiv_symm_comp (dgOdotMilnorNuNullDiagonalIntervalEdge R d h).edge
      (vertexFiberι ((pre (boundary 1).ι).app StableInfinity.{u + 1})
        (functorVertex (intervalMappingBoundary (coherentNerveVertex (C := StableQCat.{u + 1}) (A))
          (coherentNerveVertex (C := StableQCat.{u + 1}) (B)))))).symm

/-- 概要：元共有対角ホモトピーの関手辺は同じ元指定比較辺そのもの。
方針：同じ辺の curry／uncurry と Yoneda の順逆式を使う。
規約：元辺の等号。使われ方：既公開商比較との同一性。 -/
lemma dgOdotMilnorNuNullDiagonalArrowHomotopy_functorEdge :
    functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuNullDiagonalArrowHomotopy R d h) =
      dgOdotMilnorNuNullDiagonalArrowFunctorEdge R d h := by
  apply SSet.Truncated.Edge.ext
  exact (congrArg SSet.yonedaEquiv (curry_uncurry (SSet.yonedaEquiv.symm
    (dgOdotMilnorNuNullDiagonalArrowFunctorEdge R d h).edge))).trans (Equiv.apply_symm_apply _ _)

/-- 概要：元実共有対角ホモトピーは既公開の同じ全共有対角比較を回収する。
方針：同じ関手辺の厳密回収をホモトピー圏へ写す。
規約：比較の同型類を変更しない。使われ方：上下の指定共有境界の保持。 -/
lemma dgOdotMilnorNuNullDiagonalArrowHomotopy_comparison :
    SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuNullDiagonalArrowHomotopy R d h)) =
      (dgOdotMilnorNuNullDiagonalArrowComparison R d h).hom :=
  (congrArg SSet.Truncated.HomotopyCategory.homMk
    (dgOdotMilnorNuNullDiagonalArrowHomotopy_functorEdge R d h)).trans rfl

/-- 概要：元指定共有対角ホモトピーの両端点の経路は元核・元商の恒等。
方針：元固定端点 fiber の全境界式と同じ恒等辺表示を使う。
規約：端点成分の全一単体を厳密保持。使われ方：隣接する prism 面の貼り合わせ。 -/
lemma dgOdotMilnorNuNullDiagonalArrowHomotopy_paths :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullDiagonalArrowHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (stableArrow (𝟙 (A : StableQCat.{u + 1}))).edge ∧
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫
        (dgOdotMilnorNuNullDiagonalArrowHomotopy R d h).h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm
        (stableArrow (𝟙 (B : StableQCat.{u + 1}))).edge := by
  constructor
  · exact (congrArg (fun f => (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ f)
      (dgOdotMilnorNuNullDiagonalArrowHomotopy_uncurry R d h)).trans
        ((intervalMappingUncurry_face_source _).trans (diagonalIdentityVertexPath (A)))
  · exact (congrArg (fun f => (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 2})) ≫ f)
      (dgOdotMilnorNuNullDiagonalArrowHomotopy_uncurry R d h)).trans
        ((intervalMappingUncurry_face_target _).trans (diagonalIdentityVertexPath (B)))

end SerrePositivity.KST.SConstruction

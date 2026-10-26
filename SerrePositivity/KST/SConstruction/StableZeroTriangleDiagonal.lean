module
public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps
public import SerrePositivity.InfinityCategories.F1.Coherent.MaximalPathFunctor
public import SerrePositivity.InfinityCategories.F1.Coherent.OrderPostcomposition
public import SerrePositivity.InfinityCategories.Core.TerminalTransport

/-!
概要：零安定圏を中間頂点に持つ元二単体の対角完全射が全零であることを回収する。
方針：元の対角 path を最大 path へ写す辺を Kan Hom で比較し、元零合成を使う。
規約：元二単体・元対角を変更しない。使われ方：実右面の共有対角比較の一意性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 概要：元二単体の両端だけを結ぶ元一次面の path。
方針：元の δ₁ で一次 path を写す。規約：中間頂点を追加しない。
使われ方：元対角の完全射回収。 -/
def stableTriangleDiagonalPath : SimplicialThickening.Path
    (ULift.up.{u} (0 : Fin 3)) (ULift.up.{u} (2 : Fin 3)) :=
  (SimplicialThickening.functorMap
    (SimplexCategory.δ (1 : Fin 3)).toOrderHom.uliftMap
    ⟨ULift.up (0 : Fin 2)⟩ ⟨ULift.up (1 : Fin 2)⟩).obj coherentOnePath

/-- 概要：元安定圏値二単体の対角完全射。
方針：同じ元の通常関手を対角 path に適用する。
規約：元二端点・元対角を保持。使われ方：元共有対角の全零性。 -/
def stableTriangleDiagonalMap (s : StableInfinity.{u} _⦋2⦌) :
    ExactMap (s.obj ⟨ULift.up (0 : Fin 3)⟩) (s.obj ⟨ULift.up (2 : Fin 3)⟩) :=
  (coherentEnrichedUnderlyingFunctor s).map stableTriangleDiagonalPath

/-- 概要：同じ完全射の coherent 辺は元二単体の対角面そのもの。
方針：元全 Hom 頂点を端点付き通常射データへ戻す。
規約：元一単体の厳密等号。使われ方：零対角の元図式への照合。 -/
lemma stableTriangleDiagonalMap_edge (s : StableInfinity.{u} _⦋2⦌) :
    (stableArrow (stableTriangleDiagonalMap s)).edge = StableInfinity.{u}.δ (1 : Fin 3) s := by
  apply (coherentNerveArrowDataEquiv StableQCat.{u}).injective
  have h := coherentEnrichedUnderlyingFunctor_vertex s stableTriangleDiagonalPath.{u}
  let A := s.obj ⟨ULift.up (0 : Fin 3)⟩
  let B := s.obj ⟨ULift.up (2 : Fin 3)⟩
  let E := SimplicialCategory.homEquiv' (C := StableQCat.{u}) A B
  have he : E.symm ((s.map ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up (2 : Fin 3)⟩).app
      (Opposite.op ⦋0⦌) (nerveVertex stableTriangleDiagonalPath)) = stableTriangleDiagonalMap s :=
    (congrArg E.symm h.symm).trans (E.symm_apply_apply (stableTriangleDiagonalMap s))
  exact (coherentNerveArrowData_of_arrow (C := StableQCat.{u}) (stableTriangleDiagonalMap s)).trans
    (congrArg (fun f : A ⟶ B => (⟨A, B, f⟩ : Σ X Y : StableQCat.{u}, X ⟶ Y)) he).symm

/-- 概要：零中間安定圏を通る元二単体の対角は全対象を零対象に送る。
方針：元最大 path の合成を零角で評価し、元 Kan Hom の path で零性を戻す。
規約：元二単体と元対角を保持。使われ方：上下比較の共有零対角の一意性。 -/
lemma stableTriangleDiagonalMap_zero (s : StableInfinity.{u} _⦋2⦌)
    (hz : IsZeroCategory (s.obj ⟨ULift.up (1 : Fin 3)⟩))
    (x : (s.obj ⟨ULift.up (0 : Fin 3)⟩).obj _⦋0⦌) :
    IsZeroVertex ((stableTriangleDiagonalMap s).hom.app (Opposite.op ⦋0⦌) x) := by
  let A := s.obj ⟨ULift.up (0 : Fin 3)⟩
  let B := s.obj ⟨ULift.up (2 : Fin 3)⟩
  letI : Quasicategory B.obj := B.isQuasicategory
  letI : KanComplex (SimplicialCategory.sHom (C := StableQCat.{u}) A B) :=
    stableQCat_sHom_kanComplex A B
  let F := coherentEnrichedUnderlyingFunctor s
  letI : Quasicategory (F.obj ⟨ULift.up (2 : Fin 3)⟩).obj :=
    (s.obj ⟨ULift.up (2 : Fin 3)⟩).isQuasicategory
  let p : (⟨ULift.up (0 : Fin 3)⟩ : SimplicialThickening (ULift.{u} (Fin 3))) ⟶
      ⟨ULift.up (1 : Fin 3)⟩ := coherentMaximalPath (by decide)
  let q : (⟨ULift.up (1 : Fin 3)⟩ : SimplicialThickening (ULift.{u} (Fin 3))) ⟶
      ⟨ULift.up (2 : Fin 3)⟩ := coherentMaximalPath (by decide)
  let P := coherentMaximalPath
    (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2 by decide)
  have hpq : P = p ≫ q := (coherentMaximalPathFunctor (ULift.{u} (Fin 3))).map_comp
    (homOfLE (show (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 1 by decide))
    (homOfLE (show (ULift.up (1 : Fin 3) : ULift.{u} (Fin 3)) ≤ ULift.up 2 by decide))
  have hmax : IsZeroVertex ((F.map P).hom.app (Opposite.op ⦋0⦌) x) := by
    have he := congrArg ExactMap.hom (F.map_comp p q)
    change (F.map (p ≫ q)).hom = (F.map p).hom ≫ (F.map q).hom at he
    rw [hpq, he]
    exact @IsExactFunctor.preservesZero _ _ (F.map q).hom (F.map q).isExact _ (hz _)
  let ι : SimplicialCategory.sHom (C := StableQCat.{u}) A B ⟶ (exactFunctors A B : SSet.{u}) :=
    (quasicategoryCore (exactFunctors A B : SSet.{u})).ι
  let j : SimplicialCategory.sHom (C := StableQCat.{u}) A B ⟶ B.obj :=
    ι ≫ (exactFunctors A B).ι ≫ evaluateFunctorAt x
  let k : stableTriangleDiagonalPath.{u} ⟶ P := ⟨homOfLE (show stableTriangleDiagonalPath.I ⊆ P.I from
    fun i hi => ⟨stableTriangleDiagonalPath.left_le i hi, stableTriangleDiagonalPath.le_right i hi⟩)⟩
  let e : (nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin 3))
      (ULift.up.{u} (2 : Fin 3)))).Edge (nerveVertex stableTriangleDiagonalPath) (nerveVertex P) :=
    SSet.Edge.mk (ComposableArrows.mk₁ k) (ComposableArrows.ext₀ rfl) (ComposableArrows.ext₀ rfl)
  let e' := e.map (s.map ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up (2 : Fin 3)⟩)
  have hi : IsInvertibleEdge e'.toTruncated :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (SimplicialCategory.sHom (C := StableQCat.{u}) A B)) _
  have hs : j.app _ ((s.map ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up (2 : Fin 3)⟩).app _
      (nerveVertex stableTriangleDiagonalPath)) = (stableTriangleDiagonalMap s).hom.app _ x := by
    change j.app _ ((s.map _ _).app _ (nerveVertex stableTriangleDiagonalPath)) = _
    exact (congrArg (fun y : (SimplicialCategory.sHom (C := StableQCat.{u}) A B) _⦋0⦌ =>
      j.app _ y) (coherentEnrichedUnderlyingFunctor_vertex s stableTriangleDiagonalPath).symm).trans
      (by
        change (evaluateFunctorAt x).app _ (functorVertex (stableTriangleDiagonalMap s).hom) = _
        exact evaluateFunctorAt_functorVertex x _)
  have ht : j.app _ ((s.map ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up (2 : Fin 3)⟩).app _ (nerveVertex P)) = (F.map P).hom.app _ x := by
    change j.app _ ((s.map _ _).app _ (nerveVertex P)) = _
    exact (congrArg (fun y : (SimplicialCategory.sHom (C := StableQCat.{u}) A B) _⦋0⦌ =>
      j.app _ y) (coherentEnrichedUnderlyingFunctor_vertex s P).symm).trans (by
        change (evaluateFunctorAt x).app _ (functorVertex (F.map P).hom) = _
        exact evaluateFunctorAt_functorVertex x _)
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk (e'.map j).toTruncated) := hi.map j
  exact hs ▸ (ht.symm ▸ hmax).of_vertexIso
    (asIso (SSet.Truncated.HomotopyCategory.homMk (e'.map j).toTruncated)).symm
end SerrePositivity.KST.SConstruction

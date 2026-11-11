module
public import SerrePositivity.KST.SConstruction.CofiberEvaluations
public import SerrePositivity.KST.SConstruction.CoreGappedFamilies
public import SerrePositivity.KST.SConstruction.GappedCofibers

/-! # S 構成の cofiber 四角形の転置
概要：S_n(cofiber C) の図式を四角形方向へ転置し、S_n C を値とする四角形にする。
方針：内部 Hom の交換と、全ての角の完全な評価による gapped 性を使う。
規約：零角と高次パラメーターを保持する。使われ方：加法性の有限反復。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- S_n の cofiber 値の図式を二重内部 Hom 内で交換する元の射。 -/
def sCofiberRawTranspose (n : ℕ) (C : SSet.{u}) :
    sConstruction n (cofiberDiagrams C) ⟶
      (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj ((ihom (arNerve n)).obj C) :=
  (gappedSubcomplex n (cofiberDiagrams C)).ι ≫
    (ihom (arNerve n)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve n) (Δ[1] ⊗ Δ[1] : SSet.{u}) C).hom

/-- 転置した四角形の頂点は元の cofiber 図式の族の転置。 -/
lemma sCofiberRawTranspose_vertex (n : ℕ) (C : SSet.{u})
    (v : (sConstruction n (cofiberDiagrams C)) _⦋0⦌) :
    (sCofiberRawTranspose n C).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (Δ[1] ⊗ Δ[1] : SSet.{u}) C
        (gappedDiagram v ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι)) := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (cofiberDiagrams C)).apply_symm_apply v.val
  have h := congrArg (fun w : ((ihom (arNerve n)).obj (cofiberDiagrams C)) _⦋0⦌ =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve n) (Δ[1] ⊗ Δ[1] : SSet.{u}) C).hom.app
      (Opposite.op ⦋0⦌)
      (((ihom (arNerve n)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι).app
        (Opposite.op ⦋0⦌) w)) hv.symm
  have hp : ((ihom (arNerve n)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι) := rfl
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_functorVertex (arNerve n)
    (Δ[1] ⊗ Δ[1] : SSet.{u}) C
    (gappedDiagram v ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι)
  exact h.trans ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve n)
    (Δ[1] ⊗ Δ[1] : SSet.{u}) C).hom.app (Opposite.op ⦋0⦌)) hp).trans hs)

/-- 転置した族の全四角形の角は gapped な Ar 図式。 -/
lemma sCofiberRawTranspose_gapped (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (s : ((Δ[1] ⊗ Δ[1] : SSet.{u}) ⊗ sConstruction n (cofiberDiagrams C)) _⦋0⦌) :
    IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm
      ((uncurry (sCofiberRawTranspose n C)).app (Opposite.op ⦋0⦌) s)) := by
  rcases s with ⟨q, v⟩
  change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt q).app (Opposite.op ⦋0⦌)
      ((sCofiberRawTranspose n C).app (Opposite.op ⦋0⦌) v)))
  rw [sCofiberRawTranspose_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, flipFamily_vertex]
  exact (gappedDiagram_isGapped v).postcomp _
    (cofiberEvaluation_preservesSConstructionData C q)

/-- cofiber 値の S_n 図式の転置は S_n C を値とする四角形の族になる。 -/
def sCofiberTransposeSquare (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    sConstruction n (cofiberDiagrams C) ⟶
      (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj (sConstruction n C) :=
  curry (gappedFamilyLift (uncurry (sCofiberRawTranspose n C))
    (sCofiberRawTranspose_gapped n C))

/-- 転置後の S_n C の包含を通すと元の二重内部 Hom の交換を厳密に回収する。 -/
lemma sCofiberTransposeSquare_ι (n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    sCofiberTransposeSquare n C ≫
      (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map (gappedSubcomplex n C).ι =
        sCofiberRawTranspose n C := by
  apply uncurry_injective
  rw [uncurry_natural_right, sCofiberTransposeSquare, uncurry_curry,
    gappedFamilyLift_ι]

end SerrePositivity.KST.SConstruction

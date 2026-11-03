module
public import SerrePositivity.InfinityCategories.Stable.PushoutComparisonInvertible
public import SerrePositivity.InfinityCategories.F1.SuspensionDiagramArrows

/-!
概要：押し出し四角形の比較の可逆性を入力 span の三つの角で検査する。
方針：span の全頂点を標準辺の端点として読み、既存の普遍余錐の反映を使う。
規約：一般安定性は仮定しない。
使われ方：回転した cofiber の最初の二成分からの比較の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：入力 span の頂点は元の四角形の三つの角のいずれかである。
方針：標準二単体の三頂点を二つの辺の端点として列挙する。
規約：余錐頂点は含めない。使われ方：比較の全頂点での可逆性。 -/
lemma spanSquareBoundary_vertex_cases (v : (horn 2 0 : SSet.{u}) _⦋0⦌) :
    spanSquareBoundary.app (Opposite.op ⦋0⦌) v =
        squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 0 0 ∨
      spanSquareBoundary.app (Opposite.op ⦋0⦌) v =
        squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 1 0 ∨
      spanSquareBoundary.app (Opposite.op ⦋0⦌) v =
        squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 0 1 := by
  rcases v with ⟨v, hv⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
  fin_cases i
  · left
    have he : (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 3), hv⟩ :
        (horn 2 0 : SSet.{u}) _⦋0⦌) = horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
      apply Subtype.ext
      apply stdSimplex.ext
      intro a
      fin_cases a
      rfl
    change spanSquareBoundary.app (Opposite.op ⦋0⦌)
      (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 3), hv⟩ : (horn 2 0 : SSet.{u}) _⦋0⦌) = _
    rw [he] -- normalized vertex
    change (horn₂₀.ι₀₁ ≫ spanSquareBoundary).app (Opposite.op ⦋0⦌) _ = _
    rw [spanSquareBoundary_bottomEdge]
    rfl
  · right; left
    have he : (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 3), hv⟩ :
        (horn 2 0 : SSet.{u}) _⦋0⦌) = horn₂₀.ι₀₁.app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
      apply Subtype.ext
      apply stdSimplex.ext
      intro a
      fin_cases a
      rfl
    change spanSquareBoundary.app (Opposite.op ⦋0⦌)
      (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 3), hv⟩ : (horn 2 0 : SSet.{u}) _⦋0⦌) = _
    rw [he] -- normalized vertex
    change (horn₂₀.ι₀₁ ≫ spanSquareBoundary).app (Opposite.op ⦋0⦌) _ = _
    rw [spanSquareBoundary_bottomEdge]
    rfl
  · right; right
    have he : (⟨stdSimplex.obj₀Equiv.symm (2 : Fin 3), hv⟩ :
        (horn 2 0 : SSet.{u}) _⦋0⦌) = horn₂₀.ι₀₂.app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
      apply Subtype.ext
      apply stdSimplex.ext
      intro a
      fin_cases a
      rfl
    change spanSquareBoundary.app (Opposite.op ⦋0⦌)
      (⟨stdSimplex.obj₀Equiv.symm (2 : Fin 3), hv⟩ : (horn 2 0 : SSet.{u}) _⦋0⦌) = _
    rw [he] -- normalized vertex
    change (horn₂₀.ι₀₂ ≫ spanSquareBoundary).app (Opposite.op ⦋0⦌) _ = _
    rw [spanSquareBoundary_leftEdge]
    rfl

/-- 概要：押し出し間の比較辺は入力 span の三角で可逆なら可逆である。
方針：全評価による可逆性判定と普遍余錐の可逆性反映を接続する。
規約：元の比較辺を選び直さない。
使われ方：cofiber 図式の回転後の比較の検出。 -/
lemma pushoutComparison_isInvertible_of_three_corners {X : SSet.{u}} [Quasicategory X]
    {F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (hF : IsPushoutSquare F)
    (hG : IsPushoutSquare G)
    (e : Truncated.Edge (X := (truncation 2).obj
      ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)) (functorVertex F) (functorVertex G))
    (h : ∀ i j : Fin 2, (i = 0 ∨ j = 0) → IsInvertibleEdge (e.map ((truncation 2).map
      (evaluateFunctorAt (squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) i j))))) :
    IsInvertibleEdge e := by
  let a : Truncated.Edge (X := (truncation 2).obj ((ihom (horn 2 0 : SSet.{u})).obj X))
      (functorVertex (pushoutSpan F)) (functorVertex (pushoutSpan G)) :=
    e.map ((truncation 2).map ((pre spanSquareBoundary).app X))
  have ha : IsInvertibleEdge a := by
    apply (isInvertibleEdge_iff_evaluateFunctorAt a).mpr
    intro v
    have he : (a.map ((truncation 2).map (evaluateFunctorAt (Y := X) v))).edge =
        (e.map ((truncation 2).map (evaluateFunctorAt
          (spanSquareBoundary.app (Opposite.op ⦋0⦌) v)))).edge :=
      congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e.edge)
        (stable_pre_evaluateFunctorAt spanSquareBoundary v)
    apply (isInvertibleEdge_congr he).mpr
    rcases spanSquareBoundary_vertex_cases v with hv | hv | hv
    · rw [hv]; exact h 0 0 (Or.inl rfl)
    · rw [hv]; exact h 1 0 (Or.inr rfl)
    · rw [hv]; exact h 0 1 (Or.inl rfl)
  let H := simplicialHomotopyOfFunctorEdge e
  have hspan : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy
      (stableHomotopyPrecomp spanSquareBoundary H)) := by
    have he : (functorEdgeOfSimplicialHomotopy
        (stableHomotopyPrecomp spanSquareBoundary H)).edge = a.edge := by
      change SSet.yonedaEquiv (curry ((spanSquareBoundary ▷ (Δ[1] : SSet.{u})) ≫
        uncurry (SSet.yonedaEquiv.symm e.edge))) = _
      rw [← uncurry_pre_app, curry_uncurry, SSet.yonedaEquiv_comp,
        Equiv.apply_symm_apply]
      rfl
    exact (isInvertibleEdge_congr he).mpr ha
  have hi := pushoutSquareHomotopy_isInvertible_of_span F G hF hG H hspan
  have he : (functorEdgeOfSimplicialHomotopy H).edge = e.edge := by
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e.edge))) = _
    rw [curry_uncurry, Equiv.apply_symm_apply]
  exact (isInvertibleEdge_congr he).mp hi

end SerrePositivity.InfinityCategories

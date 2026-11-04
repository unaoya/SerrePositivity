module
public import SerrePositivity.InfinityCategories.Stable.PushoutCompletion
public import SerrePositivity.InfinityCategories.Stable.ZeroCornerPasting

/-! # 安定性からの任意 span の押し出し
概要：安定な quasicategory では指定された任意の span を厳密に保つ押し出し四角形が存在する。
方針：一方の枝の fiber 四角形の右に他方の枝を置き、零角の押し出しの貼り合わせを使う。
規約：有限余極限の存在を追加仮定にしない。使われ方：McCarthy 法の関手的な pushout の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：指定 span を零角の左四角形の右側として押し出し長方形に配置できる。
方針：第二枝の fiber 四角形に第一枝の合成二単体を貼る。
規約：左と外側の零角が後合成で検出できる表示。使われ方：一般の押し出しの存在と保存。 -/
lemma exists_stable_pushoutPresentation_of_span {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    ∃ F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X,
      pushoutSpan (pastingSquare F 0) = p ∧
      IsZeroVertex (squareVertex (pastingSquare F 2) 0 1) ∧
      IsPushoutSquare (pastingSquare F 2) ∧ IsPushoutSquare (pastingSquare F 0) ∧
      IsPushoutSquare (pastingSquare F 1) := by
  let f := horn₂₀.ι₀₁ ≫ p
  let g := horn₂₀.ι₀₂ ≫ p
  let s := chosenFiberSquare (edgeOfSimplex (SSet.yonedaEquiv g))
  have hg : squareRightEdge ≫ s.square = g :=
    s.right_edge.trans (SSet.yonedaEquiv.symm_apply_apply g)
  have he : stdSimplex.δ (1 : Fin 2) ≫ f = stdSimplex.δ (1 : Fin 2) ≫ g := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ p) horn₂₀.isPushout.w).trans (Category.assoc _ _ _))
  have hv : X.δ 1 (SSet.yonedaEquiv f) = X.δ 1 (SSet.yonedaEquiv g) := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp, he]
  have hs : X.δ 1 (SSet.yonedaEquiv f) = squareVertex s.square 1 0 :=
    hv.trans ((congrArg (fun k => X.δ 1 (SSet.yonedaEquiv k)) hg).symm.trans
      (squareRightEdge_source s.square))
  let b : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (squareVertex s.square 1 0) (X.δ 0 (SSet.yonedaEquiv f)) :=
    ⟨SSet.yonedaEquiv f, hs, rfl⟩
  let c := (squareBottomArrow s.square).compStruct b
  let τ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm c.simplex
  have hτ₂ : stdSimplex.δ (2 : Fin 3) ≫ τ = squareBottomEdge ≫ s.square := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 2 a) (SSet.yonedaEquiv.apply_symm_apply c.simplex)).trans
      (c.d₂.trans (squareBottomArrow_edge s.square))
  have hτ₀ : stdSimplex.δ (0 : Fin 3) ≫ τ = f := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 0 a) (SSet.yonedaEquiv.apply_symm_apply c.simplex)).trans c.d₀
  obtain ⟨F, hleft, hbottom, hright, houter⟩ := exists_pushoutRectangle_of_zeroTriangle
    s.toZeroTriangle (IsStable.pushout_of_pullback s.toZeroTriangle s.isPullback) τ hτ₂.symm
  let R := pastingSquare F 0
  have hRb : squareBottomEdge ≫ R = f := by
    rw [pastingSquare_bottomEdge, hbottom, hτ₀]
  have hRl : squareLeftEdge ≫ R = g :=
    (pastingSquare_sharedEdge F).symm.trans
      ((congrArg (fun L => squareRightEdge ≫ L) hleft).trans hg)
  refine ⟨F, ?_, ?_, ?_, hright, houter⟩
  · apply horn₂₀.isPushout.hom_ext
    · change horn₂₀.ι₀₁ ≫ (spanSquareBoundary ≫ R) = f
      rw [← Category.assoc, spanSquareBoundary_bottomEdge]
      exact hRb
    · change horn₂₀.ι₀₂ ≫ (spanSquareBoundary ≫ R) = g
      rw [← Category.assoc, spanSquareBoundary_leftEdge]
      exact hRl
  · rw [hleft]
    exact s.zero_corner
  · rw [hleft]
    exact IsStable.pushout_of_pullback s.toZeroTriangle s.isPullback

/-- 概要：任意の指定 span は押し出し四角形へ厳密に補完できる。
方針：安定な押し出し表示の右四角形を取る。
規約：追加の有限余極限の存在仮定は不要。使われ方：pushout 射影の零次元充填。 -/
lemma exists_stable_pushoutSquare_of_span {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    ∃ R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X, pushoutSpan R = p ∧ IsPushoutSquare R := by
  obtain ⟨F, hp, _hz, _hl, hr, _ho⟩ := exists_stable_pushoutPresentation_of_span p
  exact ⟨pastingSquare F 0, hp, hr⟩

/-- 概要：安定な quasicategory の全ての span は余極限を持つ。
方針：指定 span の押し出し四角形を余錐に移す。
規約：入力 span の二辺を保持する。使われ方：押し出しの相対族の補完。 -/
lemma stable_hasColimit_span {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) : HasColimit p := by
  obtain ⟨R, hp, hR⟩ := exists_stable_pushoutSquare_of_span p
  rw [← hp]
  exact ⟨pushoutCocone R, hR⟩

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.InfinityCategories.Stable.SpecifiedCofiberSpan
public import SerrePositivity.InfinityCategories.Stable.PastingCornerGluing
public import SerrePositivity.InfinityCategories.Stable.Pasting

/-! # 零角の左押し出しからの長方形の構成

概要：安定 ∞ 圏では、零角の左押し出しと適合する底辺二単体から、右も押し出しの長方形を構成できる。
方針：外側 span の指定零枝で cofiber の存在を使い、外側基底・五頂点図式へ余極限を延長する。
規約：外側余極限の存在を追加仮定しない。使われ方：懸垂と零射からの有限直和の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：外側の標準 span の第二枝は左四角形の左辺である。
方針：長方形への包含後に標準 span と左四角形の包含の式を使う。
規約：五頂点の形状の中での射の等号。使われ方：零角の移送。 -/
lemma pastingOuterStandardSpan_leftEdge :
    horn₂₀.ι₀₂ ≫ (pastingOuterSpanIso.{u}.hom ≫ pastingOuterSpan.ι ≫ pastingOuterBaseToCorner) =
      squareLeftEdge ≫ pastingCornerLeftInclusion := by
  apply (cancel_mono pastingCorner.ι).1
  simp only [Category.assoc]
  have hb : pastingOuterBaseToCorner.{u} ≫ pastingCorner.ι = pastingOuterBase.ι := rfl
  rw [hb, pastingOuterSpanIso_hom_ι]
  have hl : pastingCornerLeftInclusion.{u} ≫ pastingCorner.ι =
      stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u}) := by
    change pastingLeftSquareIso.hom ≫
      (Subcomplex.homOfLE pastingLeftSquare_le_corner ≫ pastingCorner.ι) = _
    exact pastingLeftSquareIso_hom_ι
  rw [hl, ← Category.assoc horn₂₀.ι₀₂, spanSquareBoundary_leftEdge]
  rfl

/-- 概要：左四角形の零角を持つ五頂点図式の外側基底は余極限を持つ。
方針：外側標準 span の零枝で余極限を得て、trivial な coslice 制限に沿って延長する。
規約：安定性を用いるが左四角形の押し出し性は不要。
使われ方：長方形の構成に必要な外側余極限の存在。 -/
lemma hasColimit_pastingOuterBase_of_zeroCorner {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (G : (pastingCorner : SSet.{u}) ⟶ X)
    (hz : IsZeroVertex (squareVertex (pastingCornerLeftDiagram G) 0 1)) :
    HasColimit (pastingOuterBaseToCorner ≫ G) := by
  let p := pastingOuterBaseToCorner ≫ G
  let k := pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι
  have := pastingOuterBaseRestrict_standardSpan_trivialKanFibration p
  apply (hasColimit_iff_of_trivialRestriction p k).2
  apply hasColimit_span_of_zero_second
  have he : horn₂₀.ι₀₂ ≫ (k ≫ p) = squareLeftEdge ≫ pastingCornerLeftDiagram G := by
    change horn₂₀.ι₀₂ ≫ ((pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι) ≫
      (pastingOuterBaseToCorner ≫ G)) = _
    calc
      _ = (horn₂₀.ι₀₂ ≫ (pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι ≫
          pastingOuterBaseToCorner)) ≫ G := by simp only [Category.assoc]
      _ = _ := by rw [pastingOuterStandardSpan_leftEdge, Category.assoc]; rfl
  rw [he]
  exact hz

/-- 概要：零角の左押し出しと適合する底辺二単体は、両側押し出しの長方形へ延長できる。
方針：指定零枝による外側余極限の存在を用い、貼り合わせの厳密な延長を適用する。
規約：外側余極限の存在は安定性から証明し、追加仮定にしない。
使われ方：懸垂の右に対象を付加する有限直和の構成。 -/
lemma exists_pushoutRectangle_of_zeroTriangle {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t : ZeroTriangle X) (ht : IsCofiberSequence t) (τ : (Δ[2] : SSet.{u}) ⟶ X)
    (h : squareBottomEdge ≫ t.square = stdSimplex.δ (2 : Fin 3) ≫ τ) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      pastingSquare F 2 = t.square ∧ pastingBottomTriangle F = τ ∧
        IsPushoutSquare (pastingSquare F 0) ∧ IsPushoutSquare (pastingSquare F 1) := by
  let G := pastingCornerGlue t.square τ h
  have hz : IsZeroVertex (squareVertex (pastingCornerLeftDiagram G) 0 1) := by
    rw [pastingCornerLeftDiagram_glue]
    exact t.zero_corner
  obtain ⟨d, hd⟩ := hasColimit_pastingOuterBase_of_zeroCorner G hz
  obtain ⟨F, hleft, hbottom, hright, _⟩ :=
    exists_pushoutRectangle_of_left_and_bottom t.square τ h ht d hd
  refine ⟨F, hleft, hbottom, hright, ?_⟩
  apply isPushoutSquare_pasting F _ hright
  rw [hleft]
  exact ht

end SerrePositivity.InfinityCategories

module
public import SerrePositivity.InfinityCategories.Stable.ZeroReturnTriangle
public import SerrePositivity.InfinityCategories.Stable.ZeroCornerPasting
public import SerrePositivity.InfinityCategories.Stable.ColumnPushout

/-! # 零頂点への戻りを指定する押し出し長方形

概要：零始点の押し出しを、外側が列四角形となる長方形へ延長する。
方針：底辺の戻り二単体と列四角形の普遍余錐を保持して貼り合わせる。
規約：左四角形と外側四角形を厳密に保持。使われ方：和の包含の cofiber。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：外側 span の第一枝は底辺二単体の長辺となる。
方針：五頂点図式を長方形へ含めて標準辺の式を計算する。
規約：値域なしの形状の等号。使われ方：戻りの長辺の指定。 -/
lemma pastingOuterStandardSpan_bottomEdge :
    horn₂₀.ι₀₁ ≫ (pastingOuterSpanIso.{u}.hom ≫ pastingOuterSpan.ι ≫
      pastingOuterBaseToCorner) =
      stdSimplex.δ (1 : Fin 3) ≫ pastingCornerBottomInclusion := by
  apply (cancel_mono pastingCorner.ι).1
  simp only [Category.assoc]
  have hb : pastingOuterBaseToCorner.{u} ≫ pastingCorner.ι = pastingOuterBase.ι := rfl
  rw [hb, pastingOuterSpanIso_hom_ι,
    ← Category.assoc horn₂₀.ι₀₁, spanSquareBoundary_bottomEdge]
  rfl

/-- 概要：外側 span への余錐の制限は外側四角形の余錐そのもの。
方針：長方形の join 表示の形状の等式を適用する。
規約：値域への追加条件なし。使われ方：外側の列四角形の厳密な保持。 -/
lemma pastingOuterCocone_restrict_standardSpan_val {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    ((pastingOuterCocone F).restrict
      (pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι)).val =
        (pushoutCocone (pastingSquare F 1)).val := by
  dsimp only [JoinCocone.restrict, pastingOuterCocone, pastingCocone,
    pushoutCocone, pastingSquare]
  rw [← Category.assoc, ← Category.assoc, ← joinMap_comp]
  simp only [Category.id_comp]
  rw [Category.assoc pastingOuterSpanIso.hom pastingOuterSpan.ι pastingOuterBaseToCorner,
    pastingCornerCocone_outerSpan, Category.assoc]

/-- 概要：長辺が零始点の恒等辺である戻り二単体から、外側が列四角形の長方形を作る。
方針：外側 span を列四角形の span と同定し、その普遍余錐を二段階で延長する。
規約：左の押し出しと底辺二単体を保持する。使われ方：和の包含の cofiber の構成。 -/
lemma exists_pushoutRectangle_of_returnTriangle {X : SSet.{u}} [Quasicategory X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hL : IsPushoutSquare L)
    (τ : (Δ[2] : SSet.{u}) ⟶ X)
    (h : squareBottomEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ τ)
    (hreturn : stdSimplex.δ (1 : Fin 3) ≫ τ = SSet.const (squareVertex L 0 0)) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      pastingSquare F 2 = L ∧ pastingBottomTriangle F = τ ∧
        IsPushoutSquare (pastingSquare F 0) ∧
          pastingSquare F 1 = squareColumnDiagram (squareLeftEdge ≫ L) := by
  let G := pastingCornerGlue L τ h
  let p := pastingOuterBaseToCorner ≫ G
  let k := pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι
  let C := squareColumnDiagram (squareLeftEdge ≫ L)
  have hp : k ≫ p = pushoutSpan C := by
    apply horn₂₀.isPushout.hom_ext
    · change horn₂₀.ι₀₁ ≫ ((pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι) ≫
        (pastingOuterBaseToCorner ≫ G)) = _
      have he : horn₂₀.ι₀₁ ≫ ((pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι) ≫
          (pastingOuterBaseToCorner ≫ G)) = stdSimplex.δ (1 : Fin 3) ≫ τ := by
        calc
          _ = (horn₂₀.ι₀₁ ≫ (pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι ≫
              pastingOuterBaseToCorner)) ≫ G := by simp only [Category.assoc]
          _ = _ := by
            rw [pastingOuterStandardSpan_bottomEdge, Category.assoc, pastingCornerGlue_bottom]
      rw [he, hreturn]
      change _ = horn₂₀.ι₀₁ ≫ (spanSquareBoundary ≫ (snd Δ[1] Δ[1] ≫ _))
      rw [← Category.assoc, spanSquareBoundary_bottomEdge, ← Category.assoc]
      simp only [squareBottomEdge, lift_snd, SSet.const_comp]
      rfl
    · change horn₂₀.ι₀₂ ≫ ((pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι) ≫
        (pastingOuterBaseToCorner ≫ G)) = _
      have he : horn₂₀.ι₀₂ ≫ ((pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι) ≫
          (pastingOuterBaseToCorner ≫ G)) = squareLeftEdge ≫ L := by
        calc
          _ = (horn₂₀.ι₀₂ ≫ (pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι ≫
              pastingOuterBaseToCorner)) ≫ G := by simp only [Category.assoc]
          _ = _ := by
            rw [pastingOuterStandardSpan_leftEdge, Category.assoc, pastingCornerGlue_left]
      rw [he]
      change _ = horn₂₀.ι₀₂ ≫ (spanSquareBoundary ≫ (snd Δ[1] Δ[1] ≫ _))
      rw [← Category.assoc, spanSquareBoundary_leftEdge, ← Category.assoc]
      simp only [squareLeftEdge, lift_snd, Category.id_comp]
  let c : JoinCocone (k ≫ p) := ⟨(pushoutCocone C).val, (pushoutCocone C).property.trans hp.symm⟩
  have hc : IsColimitCone c :=
    (isColimitCone_iff_of_val_eq c (pushoutCocone C) rfl).2
      (squareColumnDiagram_isPushout (squareLeftEdge ≫ L))
  have := pastingOuterBaseRestrict_standardSpan_trivialKanFibration p
  obtain ⟨d, hd, hdk, _⟩ := exists_colimitCocone_extension_of_trivialRestriction p k c hc
  obtain ⟨F, hleft, hbottom, hright, houter⟩ :=
    exists_pushoutRectangle_of_left_and_bottom L τ h hL d hd
  refine ⟨F, hleft, hbottom, hright, ?_⟩
  apply (cancel_epi spanCoconeSquareIso.hom).1
  change (pushoutCocone (pastingSquare F 1)).val = (pushoutCocone C).val
  rw [← pastingOuterCocone_restrict_standardSpan_val]
  change joinMap k (𝟙 (Δ[0] : SSet.{u})) ≫ (pastingOuterCocone F).val = _
  rw [houter]
  exact congrArg Subtype.val hdk

end SerrePositivity.InfinityCategories

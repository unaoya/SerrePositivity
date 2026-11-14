module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroReturnTriangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCornerPasting
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ColumnPushout

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：外側 span の第一枝は底辺二単体の長辺となる。
方針：五頂点図式を長方形へ含めて標準辺の式を計算する。
規約：値域なしの形状の等号。使われ方：戻りの長辺の指定。 -/
lemma pastingOuterStandardSpan_bottomEdge :
    horn₂₀.ι₀₁ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.{u}.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner) =
      stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerBottomInclusion := by
  apply (cancel_mono _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι).1
  simp only [Category.assoc]
  have hb : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner.{u} ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBase.ι := rfl
  rw [hb, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso_hom_ι,
    ← Category.assoc horn₂₀.ι₀₁, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
  rfl

/-- 概要：外側 span への余錐の制限は外側四角形の余錐そのもの。
方針：長方形の join 表示の形状の等式を適用する。
規約：値域への追加条件なし。使われ方：外側の列四角形の厳密な保持。 -/
lemma pastingOuterCocone_restrict_standardSpan_val {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterCocone F).restrict
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι)).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1)).val := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.restrict, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterCocone, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare]
  rw [← Category.assoc, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  simp only [Category.id_comp]
  rw [Category.assoc _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerCocone_outerSpan, Category.assoc]

/-- 概要：長辺が零始点の恒等辺である戻り二単体から、外側が列四角形の長方形を作る。
方針：外側 span を列四角形の span と同定し、その普遍余錐を二段階で延長する。
規約：左の押し出しと底辺二単体を保持する。使われ方：和の包含の cofiber の構成。 -/
lemma exists_pushoutRectangle_of_returnTriangle {X : SSet.{u}} [Quasicategory X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare L)
    (τ : (Δ[2] : SSet.{u}) ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ τ)
    (hreturn : stdSimplex.δ (1 : Fin 3) ≫ τ = SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex L 0 0)) :
    ∃ F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2 = L ∧ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle F = τ ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) ∧
          _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ L) := by
  let G := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue L τ h
  let p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ G
  let k := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι
  let C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ L)
  have hp : k ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan C := by
    apply horn₂₀.isPushout.hom_ext
    · change horn₂₀.ι₀₁ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ G)) = _
      have he : horn₂₀.ι₀₁ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι) ≫
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ G)) = stdSimplex.δ (1 : Fin 3) ≫ τ := by
        calc
          _ = (horn₂₀.ι₀₁ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι ≫
              _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner)) ≫ G := by simp only [Category.assoc]
          _ = _ := by
            rw [pastingOuterStandardSpan_bottomEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue_bottom]
      rw [he, hreturn]
      change _ = horn₂₀.ι₀₁ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ (snd Δ[1] Δ[1] ≫ _))
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge, ← Category.assoc]
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge, lift_snd, SSet.const_comp]
      rfl
    · change horn₂₀.ι₀₂ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ G)) = _
      have he : horn₂₀.ι₀₂ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι) ≫
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ G)) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ L := by
        calc
          _ = (horn₂₀.ι₀₂ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι ≫
              _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner)) ≫ G := by simp only [Category.assoc]
          _ = _ := by
            rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterStandardSpan_leftEdge, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue_left]
      rw [he]
      change _ = horn₂₀.ι₀₂ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ (snd Δ[1] Δ[1] ≫ _))
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge, ← Category.assoc]
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge, lift_snd, Category.id_comp]
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (k ≫ p) := ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone C).val, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone C).property.trans hp.symm⟩
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c :=
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone C) rfl).2
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram_isPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ L))
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseRestrict_standardSpan_trivialKanFibration p
  obtain ⟨d, hd, hdk, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCocone_extension_of_trivialRestriction p k c hc
  obtain ⟨F, hleft, hbottom, hright, houter⟩ :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pushoutRectangle_of_left_and_bottom L τ h hL d hd
  refine ⟨F, hleft, hbottom, hright, ?_⟩
  apply (cancel_epi _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom).1
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1)).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone C).val
  rw [← pastingOuterCocone_restrict_standardSpan_val]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap k (𝟙 (Δ[0] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterCocone F).val = _
  rw [houter]
  exact congrArg Subtype.val hdk

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

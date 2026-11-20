module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutCompletion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCornerPasting

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
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 概要：指定 span を零角の左四角形の右側として押し出し長方形に配置できる。
方針：第二枝の fiber 四角形に第一枝の合成二単体を貼る。
規約：左と外側の零角が後合成で検出できる表示。使われ方：一般の押し出しの存在と保存。 -/
lemma exists_stable_pushoutPresentation_of_span {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    ∃ F : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) = p ∧
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) 0 1) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) := by
  let f := horn₂₀.ι₀₁ ≫ p
  let g := horn₂₀.ι₀₂ ≫ p
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenFiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv g))
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ s.square = g :=
    s.right_edge.trans (SSet.yonedaEquiv.symm_apply_apply g)
  have he : stdSimplex.δ (1 : Fin 2) ≫ f = stdSimplex.δ (1 : Fin 2) ≫ g := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ p) horn₂₀.isPushout.w).trans (Category.assoc _ _ _))
  have hv : X.δ 1 (SSet.yonedaEquiv f) = X.δ 1 (SSet.yonedaEquiv g) := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp, he]
  have hs : X.δ 1 (SSet.yonedaEquiv f) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s.square 1 0 :=
    hv.trans ((congrArg (fun k => X.δ 1 (SSet.yonedaEquiv k)) hg).symm.trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source s.square))
  let b : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s.square 1 0) (X.δ 0 (SSet.yonedaEquiv f)) :=
    ⟨SSet.yonedaEquiv f, hs, rfl⟩
  let c := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow s.square).compStruct b
  let τ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm c.simplex
  have hτ₂ : stdSimplex.δ (2 : Fin 3) ≫ τ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ s.square := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 2 a) (SSet.yonedaEquiv.apply_symm_apply c.simplex)).trans
      (c.d₂.trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge s.square))
  have hτ₀ : stdSimplex.δ (0 : Fin 3) ≫ τ = f := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 0 a) (SSet.yonedaEquiv.apply_symm_apply c.simplex)).trans c.d₀
  obtain ⟨F, hleft, hbottom, hright, houter⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pushoutRectangle_of_zeroTriangle
    s.toZeroTriangle (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback s.toZeroTriangle s.isPullback) τ hτ₂.symm
  let R := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0
  have hRb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R = f := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_bottomEdge, hbottom, hτ₀]
  have hRl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ R = g :=
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_sharedEdge F).symm.trans
      ((congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ L) hleft).trans hg)
  refine ⟨F, ?_, ?_, ?_, hright, houter⟩
  · apply horn₂₀.isPushout.hom_ext
    · change horn₂₀.ι₀₁ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ R) = f
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
      exact hRb
    · change horn₂₀.ι₀₂ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ R) = g
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
      exact hRl
  · rw [hleft]
    exact s.zero_corner
  · rw [hleft]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback s.toZeroTriangle s.isPullback

/-- 概要：任意の指定 span は押し出し四角形へ厳密に補完できる。
方針：安定な押し出し表示の右四角形を取る。
規約：追加の有限余極限の存在仮定は不要。使われ方：pushout 射影の零次元充填。 -/
lemma exists_stable_pushoutSquare_of_span {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    ∃ R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R = p ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R := by
  obtain ⟨F, hp, _hz, _hl, hr, _ho⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_stable_pushoutPresentation_of_span p
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0, hp, hr⟩

/-- 概要：安定な quasicategory の全ての span は余極限を持つ。
方針：指定 span の押し出し四角形を余錐に移す。
規約：入力 span の二辺を保持する。使われ方：押し出しの相対族の補完。 -/
lemma stable_hasColimit_span {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
  obtain ⟨R, hp, hR⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_stable_pushoutSquare_of_span p
  rw [← hp]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone R, hR⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

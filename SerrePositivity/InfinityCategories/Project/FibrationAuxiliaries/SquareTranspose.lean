module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitReindex
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.PastingRightCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # 四角形の転置と押し出し

概要：四角形の二座標を交換しても押し出し性は変わらない。
方針：標準 span の二枝を交換し、その join と四角形の転置を照合する。
規約：値域への仮定は不要。使われ方：安定性の双対化と二項積。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries

/-- 概要：標準 span の二枝を交換する射。
方針：共通始点での pushout に逆順の二枝を降ろす。
規約：共通始点を保つ。使われ方：転置した四角形の span。 -/
def spanSwap : (horn 2 0 : SSet.{u}) ⟶ horn 2 0 :=
  horn₂₀.isPushout.desc horn₂₀.ι₀₂ horn₂₀.ι₀₁ horn₂₀.isPushout.w.symm

/-- 概要：枝の交換は第一枝を第二枝に送る。
方針：pushout の第一制限の式。規約：厳密な等号。使われ方：join の計算。 -/
lemma spanSwap_left : horn₂₀.ι₀₁ ≫ spanSwap.{u} = horn₂₀.ι₀₂ :=
  horn₂₀.isPushout.inl_desc _ _ _

/-- 概要：枝の交換は第二枝を第一枝に送る。
方針：pushout の第二制限の式。規約：厳密な等号。使われ方：join の計算。 -/
lemma spanSwap_right : horn₂₀.ι₀₂ ≫ spanSwap.{u} = horn₂₀.ι₀₁ :=
  horn₂₀.isPushout.inr_desc _ _ _

/-- 概要：span の枝の交換は二度で恒等になる。
方針：二枝に制限して確認する。規約：値域なし。使われ方：同型性。 -/
lemma spanSwap_comp_self : spanSwap.{u} ≫ spanSwap = 𝟙 _ := by
  apply horn₂₀.isPushout.hom_ext
  · rw [← Category.assoc, spanSwap_left, spanSwap_right, Category.comp_id]
  · rw [← Category.assoc, spanSwap_right, spanSwap_left, Category.comp_id]

/-- 概要：span の二枝を交換する同型。
方針：交換自体を逆射に取る。規約：始点を固定。使われ方：余極限の再添字付け。 -/
def spanSwapIso : (horn 2 0 : SSet.{u}) ≅ horn 2 0 where
  hom := spanSwap
  inv := spanSwap
  hom_inv_id := spanSwap_comp_self
  inv_hom_id := spanSwap_comp_self

/-- 概要：span の枝の交換の join は正方形の二座標の交換と一致する。
方針：余錐の二三角形に制限し、標準単体の有限頂点写像を計算する。
規約：余錐頂点は固定。使われ方：押し出し性の転置不変性。 -/
lemma spanCoconeSquareIso_swap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap spanSwap (𝟙 (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom := by
  have hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap spanSwap (𝟙 (Δ[0] : SSet.{u})) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight
    rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, spanSwap_left, Category.id_comp]
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap spanSwap (𝟙 (Δ[0] : SSet.{u})) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight
    rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, spanSwap_right, Category.id_comp]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCocone_isPushout.hom_ext
  · rw [← Category.assoc, hL, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left]
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  · rw [← Category.assoc, hR, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right]
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide

/-- 概要：四角形を転置しても押し出し性は同値である。
方針：span の交換同型による余錐の制限を、転置の余錐と照合する。
規約：値域に quasicategory 性は不要。使われ方：安定性と二項積の双対化。 -/
lemma isPushoutSquare_iff_transpose {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((β_ Δ[1] Δ[1]).hom ≫ F) := by
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F) spanSwapIso.hom).trans ?_
  apply _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap spanSwap (𝟙 (Δ[0] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ F) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ ((β_ Δ[1] Δ[1]).hom ≫ F)
  rw [← Category.assoc, spanCoconeSquareIso_swap, Category.assoc]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries

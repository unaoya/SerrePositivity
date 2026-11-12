module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.GridOpposite
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareOpposite
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareTranspose

/-! # 四角形の転置を伴う双対化

概要：転置と反転で零角の位置を保ち、押し出しと引き戻しを交換する。
方針：値域の同型不変性、二重反転、span の枝の交換を組み合わせる。
規約：単体集合に追加条件は不要。使われ方：安定性の自己双対性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries

/-- 概要：値域の同型は coslice の後合成でも同型となる。
方針：各単体の錐に逆射を後合成し、各次数の全単射性を示す。
規約：基底図式の形状は任意。使われ方：余極限の値域の表示変更。 -/
instance sliceUnderPostcomp_isIso {K X Y : SSet.{u}} (p : K ⟶ X)
    (q : X ⟶ Y) [IsIso q] : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p q) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro n
  apply (isIso_iff_bijective _).2
  constructor
  · intro σ τ h
    apply Subtype.ext
    apply (cancel_mono q).1
    exact congrArg Subtype.val h
  · intro τ
    refine ⟨⟨τ.val ≫ inv q, ?_⟩, ?_⟩
    · rw [← Category.assoc, τ.property, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    · apply Subtype.ext
      change (τ.val ≫ inv q) ≫ q = τ.val
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- 概要：値域の同型への後合成は押し出し性を保ち反映する。
方針：余錐の coslice の同型で始対象性を輸送する。
規約：値域への仮定は不要。使われ方：二重反転を元の値域へ戻す。 -/
lemma isPushoutSquare_iff_postcomp_isIso {X Y : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (q : X ⟶ Y) [IsIso q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ q) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F) q) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)

/-- 概要：押し出し四角形は反転すると引き戻し四角形となる。
方針：引き戻しの反転判定を二重反転と値域の同型で戻す。
規約：逆向きも同値として含む。使われ方：cofiber 四角形の双対化。 -/
lemma isPushoutSquare_iff_reverseGrid {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F) := by
  have h := isPushoutSquare_iff_postcomp_isIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F))
    (SSet.opFunctorCompOpFunctorIso.app X).hom
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_double] at h
  exact h.symm.trans (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F)).symm

/-- 概要：四角形の反転と転置は可換。
方針：二座標の交換と各座標の順序反転を成分で照合する。
規約：厳密な射の等号。使われ方：引き戻し性の転置不変性。 -/
lemma reverseGrid_transpose {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid ((β_ Δ[1] Δ[1]).hom ≫ F) =
      (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  rfl

/-- 概要：四角形を転置しても引き戻し性は変わらない。
方針：反転して押し出しの転置不変性へ帰着する。
規約：値域に追加条件は不要。使われ方：零角を保つ双対化。 -/
lemma isPullbackSquare_iff_transpose {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((β_ Δ[1] Δ[1]).hom ≫ F) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid,
    reverseGrid_transpose]
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F)

/-- 概要：四角形の二座標を反転・交換し、値域を反対にする。
方針：reverseGrid の後で標準正方形の転置を前合成する。
規約：(0,1) の零角の位置を保つ。使われ方：安定性の反対圏への輸送。 -/
def dualSquare {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X.op :=
  (β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F

/-- 概要：零角を保つ双対化は押し出しと引き戻しを交換する。
方針：反転による双対性と転置不変性を合成する。
規約：任意の四角形。使われ方：反対圏での fiber の存在。 -/
lemma isPushoutSquare_iff_dualSquare {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dualSquare F) :=
  (isPushoutSquare_iff_reverseGrid F).trans (isPullbackSquare_iff_transpose (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F))

/-- 概要：零角を保つ双対化は引き戻しと押し出しを交換する。
方針：反転による双対性と転置不変性を合成する。
規約：任意の四角形。使われ方：反対圏での cofiber の存在。 -/
lemma isPullbackSquare_iff_dualSquare {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dualSquare F) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid F).trans (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F))

/-- 概要：値域の同型への後合成は引き戻し性を保ち反映する。
方針：反転による押し出し判定と、押し出しの値域同型不変性を使う。
規約：値域への仮定は不要。使われ方：双対化を元の値域へ戻す。 -/
lemma isPullbackSquare_iff_postcomp_isIso {X Y : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (q : X ⟶ Y) [IsIso q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (F ≫ q) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_postcomp]
  exact isPushoutSquare_iff_postcomp_isIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F) (SSet.opFunctor.map q)

/-- 概要：双対四角形の頂点は交換・反転した元の頂点。
方針：標準零単体上の二座標を計算する。
規約：値域は opObjEquiv で移す。使われ方：零角の保持。 -/
lemma dualSquare_vertex {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dualSquare F) i j =
      SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F j.rev i.rev) := by
  rfl

/-- 概要：双対四角形の右辺は元の下辺の反転。
方針：区間上の二座標を計算する。
規約：辺の射の等号。使われ方：cofiber から fiber への輸送。 -/
lemma dualSquare_rightEdge {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dualSquare F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F) := by
  apply SSet.yonedaEquiv.injective
  rfl

/-- 概要：双対四角形の下辺は元の右辺の反転。
方針：区間上の二座標を計算する。
規約：辺の射の等号。使われ方：fiber から cofiber への輸送。 -/
lemma dualSquare_bottomEdge {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dualSquare F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F) := by
  apply SSet.yonedaEquiv.injective
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries

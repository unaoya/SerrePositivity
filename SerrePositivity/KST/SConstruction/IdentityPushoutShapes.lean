module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutCompletion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ColumnPushout
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareTranspose

/-! # 恒等な枝を持つ span の標準押し出し
概要：一方の枝が恒等となる span の全ての族に、退化した標準の押し出し四角形を与える。
方針：正方形の二つの座標射影で辺の族を引き戻し、全部分複体へ移す。
規約：二つの向きを Bool で指定する。使われ方：McCarthy 法の pushout 選択の相対正規化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 概要：恒等な枝を持つ標準四角形を作る座標射影。
方針：false は縦座標、true は横座標を使う。
規約：false では下辺、true では左辺が恒等。使われ方：二つの正規化条件。 -/
def identityPushoutShape (b : Bool) : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[1] :=
  if b then fst _ _ else snd _ _

/-- 概要：一本の辺から作る二つの退化四角形はともに押し出し。
方針：横方向に一定な四角形の押し出し性と転置を使う。
規約：値域に安定性は不要。使われ方：標準押し出しの族の構成。 -/
lemma identityPushoutShape_isPushout {C : SSet.{u}} [Quasicategory C] (b : Bool)
    (g : (Δ[1] : SSet.{u}) ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (identityPushoutShape b ≫ g) := by
  cases b with
  | false => exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram_isPushout g
  | true =>
    have h := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram g)).1
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram_isPushout g)
    simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram, identityPushoutShape, Bool.true_eq, ↓reduceIte,
      ← Category.assoc, braiding_hom_snd] using h

/-- 概要：恒等な枝を持つ標準 span を作る形状射。
方針：標準の退化四角形を入力の span に制限する。
規約：false は下辺が恒等、true は左辺が恒等。使われ方：正規化を指定する単射。 -/
def identitySpanShape (b : Bool) : (horn 2 0 : SSet.{u}) ⟶ Δ[1] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ identityPushoutShape b

/-- 概要：恒等でない枝への制限を与える標準の切断。
方針：向きに応じたホーンの辺を取る。
規約：形状射の右逆。使われ方：二つの正規化の共通部分の照合。 -/
def identitySpanSection (b : Bool) : (Δ[1] : SSet.{u}) ⟶ horn 2 0 :=
  if b then horn₂₀.ι₀₁ else horn₂₀.ι₀₂

/-- 概要：標準の切断は元の辺を厳密に回収する。
方針：二つの標準辺で座標射影を計算する。
規約：二つの向きに共通。使われ方：正規化の単射と重なりの計算。 -/
lemma identitySpanSection_shape (b : Bool) :
    identitySpanSection b ≫ identitySpanShape b = 𝟙 (Δ[1] : SSet.{u}) := by
  cases b <;>
    simp only [identitySpanSection, identitySpanShape, identityPushoutShape, Bool.false_eq_true,
      ↓reduceIte, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
  all_goals
    apply SSet.yonedaEquiv.injective
    decide

/-- 概要：一本の辺の族を恒等な枝を持つ span の族に送る単体的射。
方針：形状射による内部 Hom の前合成。
規約：辺の任意の高次の族を保持する。使われ方：切断の相対正規化。 -/
def identitySpanFamily (b : Bool) (C : SSet.{u}) :
    (ihom (Δ[1] : SSet.{u})).obj C ⟶ (ihom (horn 2 0 : SSet.{u})).obj C :=
  (pre (identitySpanShape b)).app C

/-- 概要：恒等な枝を付加する射は単射。
方針：元の辺への制限が左逆を与える。
規約：値域に quasicategory 性は不要。使われ方：相対切断の延長の単射条件。 -/
instance identitySpanFamily_mono (b : Bool) (C : SSet.{u}) : Mono (identitySpanFamily b C) := by
  have h : identitySpanFamily b C ≫ (pre (identitySpanSection b)).app C = 𝟙 _ := by
    dsimp only [identitySpanFamily]
    rw [← NatTrans.comp_app, ← pre_map, identitySpanSection_shape, pre_id]
    rfl
  exact mono_of_mono_fac h

/-- 概要：恒等な枝を持つ span の標準押し出しの単体的な族。
方針：座標射影による辺の族を押し出し図式の全部分複体へ持ち上げる。
規約：個々の対象での選択を使わない。使われ方：指定した正規化の境界データ。 -/
def identityPushoutFamily (b : Bool) (C : SSet.{u}) [Quasicategory C] :
    (ihom (Δ[1] : SSet.{u})).obj C ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutDiagrams C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex ((pre (identityPushoutShape b)).app C) (by
    intro v
    obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) C).surjective v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C (identityPushoutShape b ≫ g)))
    rw [Equiv.symm_apply_apply]
    exact identityPushoutShape_isPushout b g)

/-- 概要：標準押し出しの族の周囲の図式は座標射影である。
方針：全部分複体への持ち上げの包含の式。
規約：全単体での厳密等号。使われ方：正規化した四角形の回収。 -/
lemma identityPushoutFamily_ι (b : Bool) (C : SSet.{u}) [Quasicategory C] :
    identityPushoutFamily b C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex).ι =
      (pre (identityPushoutShape b)).app C := rfl

/-- 概要：標準押し出しの族は恒等な枝を持つ入力 span を回収する。
方針：内部 Hom の前合成の合成則。
規約：全単体での厳密等号。使われ方：相対切断の延長の可換条件。 -/
lemma identityPushoutFamily_projection (b : Bool) (C : SSet.{u}) [Quasicategory C] :
    identityPushoutFamily b C ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutProjection C = identitySpanFamily b C := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutProjection, ← Category.assoc, identityPushoutFamily_ι,
    ← NatTrans.comp_app, ← pre_map]
  rfl

end SerrePositivity.KST.SConstruction

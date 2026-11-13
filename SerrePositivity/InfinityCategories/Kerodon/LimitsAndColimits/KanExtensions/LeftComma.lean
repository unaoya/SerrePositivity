module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibrationComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaSourceOppositeFibration
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaCounit

/-!
概要：任意の関手 δ の矢印 δ(k)→c を保持する oriented fiber product を構成する。
方針：反転した δ の comma を再び反転し、既存の cocartesian 輸送を使う。
規約：データの定義は任意の単体集合、輸送の証明は両側が quasicategory。
使われ方：一般の δ に沿う Kan 拡張の存在を cocartesian な射影の場合へ移す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：δ(k) から c への矢印を保持する comma。
方針：δ の反転の右 comma を反転する。
規約：標的の c は固定しない。
使われ方：任意の δ の cocartesian な置き換え。 -/
def kanLeftComma {K C : SSet.{u}} (δ : K ⟶ C) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma (SSet.opFunctor.map δ)).op

/-- 概要：oriented fiber product から元の添字 k への射影。
方針：反転した comma の標的射影の二重反転を戻す。
規約：値域は K。
使われ方：元の図式を oriented fiber product へ引き戻す。 -/
def kanLeftCommaSource {K C : SSet.{u}} (δ : K ⟶ C) : kanLeftComma δ ⟶ K :=
  SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget (SSet.opFunctor.map δ)) ≫
    (SSet.opFunctorCompOpFunctorIso.app K).hom

/-- 概要：oriented fiber product から矢印の終点 c への射影。
方針：反転した comma の始域射影の二重反転を戻す。
規約：値域は C。
使われ方：Kan 拡張の構成に使う cocartesian な射影。 -/
def kanLeftCommaProjection {K C : SSet.{u}} (δ : K ⟶ C) : kanLeftComma δ ⟶ C :=
  SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (SSet.opFunctor.map δ)) ≫
    (SSet.opFunctorCompOpFunctorIso.app C).hom

/-- 概要：恒等矢印 δ(k)→δ(k) により K を oriented fiber product に入れる。
方針：反転した恒等矢印の族へ二重反転の逆同型を前合成する。
規約：定義に quasicategory 性は不要。
使われ方：構成後の自然変換を元の添字へ制限する。 -/
def kanLeftCommaInclusion {K C : SSet.{u}} (δ : K ⟶ C) : K ⟶ kanLeftComma δ :=
  (SSet.opFunctorCompOpFunctorIso.app K).inv ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily (SSet.opFunctor.map δ))

/-- 概要：恒等矢印の族を元の添字へ射影すると恒等射。
方針：反転と恒等矢印の標的の式を使う。
規約：射の厳密な等式。
使われ方：元の図式を厳密に復元する。 -/
lemma kanLeftCommaInclusion_source {K C : SSet.{u}} (δ : K ⟶ C) :
    kanLeftCommaInclusion δ ≫ kanLeftCommaSource δ = 𝟙 K := by
  change (SSet.opFunctorCompOpFunctorIso.app K).inv ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily (SSet.opFunctor.map δ) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget (SSet.opFunctor.map δ)) ≫
        (SSet.opFunctorCompOpFunctorIso.app K).hom = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily_target, CategoryTheory.Functor.map_id]
  change (SSet.opFunctorCompOpFunctorIso.app K).inv ≫
    (SSet.opFunctorCompOpFunctorIso.app K).hom = _
  exact Iso.inv_hom_id _

/-- 概要：恒等矢印の族を底へ射影すると元の δ。
方針：反転した恒等矢印の始域と二重反転の自然性を使う。
規約：射の厳密な等式。
使われ方：新しい射影に沿う構成を元の関手へ戻す。 -/
lemma kanLeftCommaInclusion_projection {K C : SSet.{u}} (δ : K ⟶ C) :
    kanLeftCommaInclusion δ ≫ kanLeftCommaProjection δ = δ := by
  change (SSet.opFunctorCompOpFunctorIso.app K).inv ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily (SSet.opFunctor.map δ) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (SSet.opFunctor.map δ)) ≫
        (SSet.opFunctorCompOpFunctorIso.app C).hom = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaIdentityFamily_source]
  have hnat := SSet.opFunctorCompOpFunctorIso.hom.naturality δ
  change SSet.opFunctor.map (SSet.opFunctor.map δ) ≫
    (SSet.opFunctorCompOpFunctorIso.app C).hom =
      (SSet.opFunctorCompOpFunctorIso.app K).hom ≫ δ at hnat
  rw [hnat, Iso.inv_hom_id_assoc]

/-- 概要：任意の関手の oriented fiber product の標的射影は cocartesian fibration。
方針：既存の反転した comma の輸送を F1 の型へ移し、二重反転の同型を合成する。
規約：K と C は quasicategory、δ 自体の充填性は不要。
使われ方：点ごとの余極限から構成した相対 join の存在定理への入力。 -/
instance kanLeftCommaProjection_cocartesianFibration {K C : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (δ : K ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (kanLeftCommaProjection δ) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource (SSet.opFunctor.map δ))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianHornFibration_toCocartesianFibration _
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (SSet.opFunctorCompOpFunctorIso.app C).hom :=
    ⟨MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations _⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianFibration_comp _ _

/-- 概要：quasicategory 間の oriented fiber product は quasicategory。
方針：底への cocartesian fibration の inner fibration 性を使う。
規約：δ 自体は任意の関手。
使われ方：一般の δ の置き換えの全空間の充填性。 -/
instance kanLeftComma_quasicategory {K C : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (δ : K ⟶ C) : Quasicategory (kanLeftComma δ) :=
  quasicategory_of_innerFibration (kanLeftCommaProjection δ)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "2.2.4.15" (partial := component) "仮定：準圏の間の任意の関手 δ（Lean が弱い：operad 構造を要求しない）。結論：δ の oriented fiber product の終点射影が余デカルト・ファイブレーション（(1) の D→O⊗ に一致）。余デカルト辺の判定と Env への制限はこの型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection_cocartesianFibration

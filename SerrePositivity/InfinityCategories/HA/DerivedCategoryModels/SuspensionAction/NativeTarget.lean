module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.QuotientNative
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.UnconditionalData
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonNativeComposition

/-!
概要：工程 1 の native 供給先と、D の工程 2 による同じ懸垂への消費射を固定する。
方針：切替済み段提供者の分解・null 集合を ε core に代入し、正本 data の頂点を照合する。
規約：入力 native core からこの供給先への射の存在は、まだ構成していない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory MonoidalCategory DifferentialGraded KST.NonConnective KST.SConstruction
open DGCategoryCellResolution
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)
  (A B : PerfDGInput.{u, max (u + 1) v} R)
local notation "IA" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R A κ hκ
local notation "IB" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R B κ hκ
local notation "CA" => DGKappaCone R A IA
local notation "CB" => DGKappaCone R B IB
local notation "PA" => Source R CA
local notation "PB" => Source R CB
local notation "SA" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R CA (dgKappaConePerfectObjects R A IA)
local notation "SB" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R CB (dgKappaConePerfectObjects R B IB)

/-- 工程 1 が全単体で着地させる、同じ固定 ε 整合関手圏の core。 -/
def dgSuspensionResolvedEpsilonCore : SSet.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.quotientEpsilonNativeCore R PA PB SA SB

/-- 正本 strict data の resolved 関手を、同じ null 保存対象として保持する。 -/
def dgSuspensionResolvedEpsilonObject (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R PA PB SA SB where
  val := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f).resolved
  property := dgKappaSuspensionMap_preservesNullObjects R A B IA IB
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f)

/-- 工程 1 の頂点作用として要求する、同じ resolved 関手の頂点。 -/
def dgSuspensionResolvedEpsilonVertex (f : A ⟶ B) :
    (dgSuspensionResolvedEpsilonCore R κ hκ A B).obj (Opposite.op ⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.quotientEpsilonNativeVertex R PA PB SA SB
    (dgSuspensionResolvedEpsilonObject R κ hκ A B f)

/-- D の商作用を消費し、同じ実懸垂間の native Hom へ送る全単体射。 -/
def dgSuspensionQuotientNativeMap :
    dgSuspensionResolvedEpsilonCore R κ hκ A B ⟶
      dgFunctorNativeMappingSpace R
        (dgKappaSuspensionKInput R A IA) (dgKappaSuspensionKInput R B IB) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.quotientNativeInputMap R PA PB SA SB

/-- 商作用の頂点は、K-B3 が要求する正本 strict data の同じ実入力射。 -/
lemma dgSuspensionQuotientNativeMap_vertex (f : A ⟶ B) :
    (dgSuspensionQuotientNativeMap R κ hκ A B).app (Opposite.op ⦋0⦌)
        (dgSuspensionResolvedEpsilonVertex R κ hκ A B f) =
      dgFunctorNativeMappingVertex R _ _
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ f).down :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.quotientNativeInputMap_vertex R PA PB SA SB
    (dgSuspensionResolvedEpsilonObject R κ hκ A B f)

/-- 工程 1 の厳密な頂点作用は、商消費後も同じ正本入力射に一致する。 -/
lemma dgSuspensionNativeHom_vertex
    (H : dgFunctorNativeMappingSpace R A B ⟶ dgSuspensionResolvedEpsilonCore R κ hκ A B)
    (f : A ⟶ B)
    (hH : H.app (Opposite.op ⦋0⦌) (dgFunctorNativeMappingVertex R A B f.down) =
      dgSuspensionResolvedEpsilonVertex R κ hκ A B f) :
    (H ≫ dgSuspensionQuotientNativeMap R κ hκ A B).app (Opposite.op ⦋0⦌)
        (dgFunctorNativeMappingVertex R A B f.down) =
      dgFunctorNativeMappingVertex R _ _
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ f).down := by
  change (dgSuspensionQuotientNativeMap R κ hκ A B).app _
    (H.app _ (dgFunctorNativeMappingVertex R A B f.down)) = _
  rw [hH]
  exact dgSuspensionQuotientNativeMap_vertex R κ hκ A B f

/-- 工程 1 の頂点を比較で照合する場合も、商への消費は同じ native 比較を保持する。 -/
def dgSuspensionNativeHom_vertexIso
    (H : dgFunctorNativeMappingSpace R A B ⟶ dgSuspensionResolvedEpsilonCore R κ hκ A B)
    (f : A ⟶ B)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := dgSuspensionResolvedEpsilonCore R κ hκ A B)
      (H.app (Opposite.op ⦋0⦌) (dgFunctorNativeMappingVertex R A B f.down))
      (dgSuspensionResolvedEpsilonVertex R κ hκ A B f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := dgFunctorNativeMappingSpace R
      (dgKappaSuspensionKInput R A IA) (dgKappaSuspensionKInput R B IB))
      ((H ≫ dgSuspensionQuotientNativeMap R κ hκ A B).app (Opposite.op ⦋0⦌)
        (dgFunctorNativeMappingVertex R A B f.down))
      (dgFunctorNativeMappingVertex R _ _
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ f).down) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (dgSuspensionQuotientNativeMap R κ hκ A B)
  rw [dgSuspensionQuotientNativeMap_vertex] at h
  exact h

omit B in
/-- 同じ分解・null 集合を持つ ε core の全単体の単位。 -/
def dgSuspensionResolvedEpsilonUnit :
    𝟙_ SSet.{max (u + 1) v} ⟶ dgSuspensionResolvedEpsilonCore R κ hκ A A :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.quotientNativeInputUnit R PA SA

omit B in
/-- 特殊化した商作用は実懸垂の単位を全単体で保つ。 -/
lemma dgSuspensionQuotientNativeMap_unit :
    dgSuspensionResolvedEpsilonUnit R κ hκ A ≫
        dgSuspensionQuotientNativeMap R κ hκ A A =
      dgFunctorNativeIdentity R (dgKappaSuspensionKInput R A IA) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.quotientNativeInputMap_unit R PA SA

variable (C : PerfDGInput.{u, max (u + 1) v} R)
local notation "IC" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R C κ hκ
local notation "CC" => DGKappaCone R C IC
local notation "PC" => Source R CC
local notation "SC" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R CC (dgKappaConePerfectObjects R C IC)

/-- 工程 1 が横合成と照合する、同じ ε core 間の全単体合成。 -/
def dgSuspensionResolvedEpsilonComposition :
    dgSuspensionResolvedEpsilonCore R κ hκ A B ⊗
        dgSuspensionResolvedEpsilonCore R κ hκ B C ⟶
      dgSuspensionResolvedEpsilonCore R κ hκ A C :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonNativeComposition R PA PB PC SA SB SC

/-- 商への消費は、固定模型の native Hom 合成と全単体で厳密に交換する。 -/
lemma dgSuspensionQuotientNativeMap_composition :
    dgSuspensionResolvedEpsilonComposition R κ hκ A B C ≫
        dgSuspensionQuotientNativeMap R κ hκ A C =
      (dgSuspensionQuotientNativeMap R κ hκ A B ⊗ₘ
        dgSuspensionQuotientNativeMap R κ hκ B C) ≫
          dgFunctorNativeComposition R
            (dgKappaSuspensionKInput R A IA) (dgKappaSuspensionKInput R B IB)
            (dgKappaSuspensionKInput R C IC) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonNativeMap_composition R PA PB PC SA SB SC

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction

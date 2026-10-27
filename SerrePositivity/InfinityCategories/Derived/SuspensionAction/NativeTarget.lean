module
public import SerrePositivity.InfinityCategories.Derived.SuspensionAction.QuotientNative
public import SerrePositivity.InfinityCategories.Derived.SuspensionAction.UnconditionalData

/-!
概要：工程 1 の native 供給先と、D の工程 2 による同じ懸垂への消費射を固定する。
方針：切替済み段提供者の分解・null 集合を ε core に代入し、正本 data の頂点を照合する。
規約：入力 native core からこの供給先への射の存在は、まだ構成していない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.NonConnective KST.SConstruction
open DGCategoryCellResolution
open scoped Simplicial
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)
  (A B : PerfDGInput.{u, max (u + 1) v} R)
local notation "IA" => dgKappaConeInput_unconditional' R A κ hκ
local notation "IB" => dgKappaConeInput_unconditional' R B κ hκ
local notation "CA" => DGKappaCone R A IA
local notation "CB" => DGKappaCone R B IB
local notation "PA" => Source R CA
local notation "PB" => Source R CB
local notation "SA" => resolvedDGNullObjects R CA (dgKappaConePerfectObjects R A IA)
local notation "SB" => resolvedDGNullObjects R CB (dgKappaConePerfectObjects R B IB)

/-- 工程 1 が全単体で着地させる、同じ固定 ε 整合関手圏の core。 -/
def dgSuspensionResolvedEpsilonCore : SSet.{max (u + 1) v} :=
  quotientEpsilonNativeCore R PA PB SA SB

/-- 正本 strict data の resolved 関手を、同じ null 保存対象として保持する。 -/
def dgSuspensionResolvedEpsilonObject (f : A ⟶ B) :
    NullPreservingFunctorsε R PA PB SA SB where
  val := (dgSuspensionUnconditionalMapData R κ hκ f).resolved
  property := dgKappaSuspensionMap_preservesNullObjects R A B IA IB
    (dgSuspensionUnconditionalMapData R κ hκ f)

/-- 工程 1 の頂点作用として要求する、同じ resolved 関手の頂点。 -/
def dgSuspensionResolvedEpsilonVertex (f : A ⟶ B) :
    (dgSuspensionResolvedEpsilonCore R κ hκ A B).obj (Opposite.op ⦋0⦌) :=
  quotientEpsilonNativeVertex R PA PB SA SB
    (dgSuspensionResolvedEpsilonObject R κ hκ A B f)

/-- D の商作用を消費し、同じ実懸垂間の native Hom へ送る全単体射。 -/
def dgSuspensionQuotientNativeMap :
    dgSuspensionResolvedEpsilonCore R κ hκ A B ⟶
      dgFunctorNativeMappingSpace R
        (dgKappaSuspensionKInput R A IA) (dgKappaSuspensionKInput R B IB) :=
  quotientNativeInputMap R PA PB SA SB

/-- 商作用の頂点は、K-B3 が要求する正本 strict data の同じ実入力射。 -/
lemma dgSuspensionQuotientNativeMap_vertex (f : A ⟶ B) :
    (dgSuspensionQuotientNativeMap R κ hκ A B).app (Opposite.op ⦋0⦌)
        (dgSuspensionResolvedEpsilonVertex R κ hκ A B f) =
      dgFunctorNativeMappingVertex R _ _
        (dgSuspensionUnconditionalInputMap R κ hκ f).down :=
  quotientNativeInputMap_vertex R PA PB SA SB
    (dgSuspensionResolvedEpsilonObject R κ hκ A B f)

end SerrePositivity.InfinityCategories

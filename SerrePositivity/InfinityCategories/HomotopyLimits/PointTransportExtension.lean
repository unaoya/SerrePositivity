module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTransportPointComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedExtensionVertexEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.ContractibleEdgeEvaluation

/-!
概要：点評価した元の輸送比較円柱を、同じ根辺の固定延長空間へ戻す。
方針：元の始点と底を固定した実際の長辺・標準辺を頂点として保持する。
規約：同じ二単体と同じ比較円柱を使う。使われ方：標準長辺の正準比較の native な同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

private lemma pointTransportInitial_eq :
    (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) = scaffoldFirstVertex 1 := by
  apply SSet.yonedaEquiv.injective
  decide

variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} (g : B.Edge a c)
  (v : (vertexFiber p a) _⦋0⦌)
local notation "β" => SSet.yonedaEquiv.symm g.edge
local notation "i" => stdSimplex.δ (1 : Fin 2)
local notation "w" => SSet.yonedaEquiv.symm v.val
local notation "V" => prismVertexEvaluation (transportEdgePrism p g) v

/-- 同じ標準辺の始点は、元の fiber の指定頂点。 -/
lemma standardTransportPoint_initial : i ≫ V = w := by
  rw [← standardTransportPointEdge_diagram]
  exact (standardTransportPointEdge p g v).δ_one_yonedaEquiv_symm

/-- 点の標準辺も、元の底の辺を厳密に被覆する。 -/
lemma standardTransportPoint_projection : V ≫ p = β :=
  prismVertexEvaluation_projection p _ _ (transportEdgePrism_projection p g) v

/-- 同じ始点を固定するための底の整合性。 -/
lemma pointTransportExtension_initial_base : w ≫ p = i ≫ β :=
  (congrArg (fun z ↦ z ≫ p) (standardTransportPoint_initial p g v).symm).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ i ≫ z) (standardTransportPoint_projection p g v)))

local notation "hv" => pointTransportExtension_initial_base p g v

/-- 元の根辺と同じ点の初期値を固定する、実際の辺の延長空間。 -/
def pointTransportExtensionSpace : SSet.{u} :=
  relativeFunctorExtensionSpace p β i w hv

/-- この延長空間は、全高次の比較を含めて可縮な Kan 複体。 -/
lemma pointTransportExtensionSpace_isContractibleKan :
    IsContractibleKan (pointTransportExtensionSpace p g v) := by
  apply relativeFunctorExtensionSpace_isContractibleKan
  rw [pointTransportInitial_eq]
  exact scaffoldFirstVertex_leftAnodyne 1

/-- 元の標準 prism の同じ点評価を、この空間の頂点にする。 -/
def standardTransportPointExtensionVertex : (pointTransportExtensionSpace p g v) _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv p β i w hv
    ⟨V, standardTransportPoint_projection p g v, standardTransportPoint_initial p g v⟩

/-- 全延長を同じ根辺の終点で評価する射。 -/
def pointTransportExtensionEndpoint : pointTransportExtensionSpace p g v ⟶ vertexFiber p c :=
  fixedExtensionEdgeTarget p β i w hv (𝟙 Δ[1]) g (Category.id_comp β)

variable {g} (σ : SSet.Edge.CompStruct e f g)
local notation "W" => prismVertexEvaluation (coherentTransportTriangleLongPrism p σ) v
local notation "H" => coherentTransportPointComparisonHomotopy p σ v

/-- 元の三角形の長辺の始点も、同じ元の fiber 頂点。 -/
lemma coherentTransportLongPoint_initial : i ≫ W = w := by
  rw [← prismPointEdge_diagram (coherentTransportTriangleLongPrism p σ)
    (vertexFiberι p a) ((edgeTransport p e ≫ edgeTransport p f) ≫ vertexFiberι p c)
    (coherentTransportTriangleLongPrism_zero p σ) (coherentTransportTriangleLongPrism_one p σ)]
  exact (coherentTransportTriangleDiagonalPointEdge p σ v).δ_one_yonedaEquiv_symm

/-- 同じ三角形の長辺も、元の底の根辺を厳密に被覆する。 -/
lemma coherentTransportLongPoint_projection : W ≫ p = β :=
  prismVertexEvaluation_projection p _ _ (coherentTransportTriangleLongPrism_projection p σ) v

/-- 元の三角形の実際の長辺を、同じ根辺空間の頂点として保持する。 -/
def coherentTransportLongPointExtensionVertex : (pointTransportExtensionSpace p g v) _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv p β i w hv
    ⟨W, coherentTransportLongPoint_projection p v σ, coherentTransportLongPoint_initial p v σ⟩

/-- 点評価した元の円柱は、最初の面の初期図式を全時刻で固定する。 -/
lemma coherentTransportPointComparisonHomotopy_initial_face :
    (i ▷ (Δ[1] : SSet.{u})) ≫ (H).h = fst (Δ[0] : SSet.{u}) Δ[1] ≫ w := by
  rw [pointTransportInitial_eq]
  exact coherentTransportPointComparisonHomotopy_initial p σ v

/-- 元の点比較円柱を同じ延長空間の実際の辺として保持する。 -/
def coherentTransportPointComparisonExtensionEdge :
    (pointTransportExtensionSpace p g v).Edge (coherentTransportLongPointExtensionVertex p v σ)
      (standardTransportPointExtensionVertex p g v) :=
  fixedExtensionHomotopyEdge p β i w hv
    (coherentTransportLongPoint_projection p v σ) (standardTransportPoint_projection p g v)
    (coherentTransportLongPoint_initial p v σ) (standardTransportPoint_initial p g v)
    H (coherentTransportPointComparisonHomotopy_projection p σ v)
    (coherentTransportPointComparisonHomotopy_initial_face p v σ)

/-- 同じ点比較辺を展開しても、元の円柱を回収する。 -/
lemma coherentTransportPointComparisonExtensionEdge_uncurry :
    relativeFunctorUncurry (SSet.yonedaEquiv.symm
      (coherentTransportPointComparisonExtensionEdge p v σ).edge ≫
        relativeFunctorExtensionSpaceι p β i w hv) = (H).h :=
  fixedExtensionHomotopyEdge_uncurry _ _ _ _ _ _ _ _ _ _ _ _

end
end SerrePositivity.InfinityCategories.HomotopyLimits

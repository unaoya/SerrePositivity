module
public import SerrePositivity.KST.SConstruction.CoherentDiagramCutDecoding
public import SerrePositivity.KST.SConstruction.KOriginalSuspensionPrisms

/-! # 元の K prism の高次単体からの全 Path 円柱
概要：零段を含む元の K prism の全高次単体を、豊穣 Hom 内の実合成円柱に復号する。
方針：同じ prism の豊穣作用を使い、入力の再添字と各単体内の再添字を照合する。
規約：Kan の充填で三角形を選び直さず、元の Path の合成面を固定する。
使われ方：元の構造射と既存 BF 境界を保つ coherent な厳密化のパラメータを供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kPrismPathDecoding_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の K prism の各高次単体から復号した、全 Path の境界固定の実合成円柱。 -/
def kKanPrismCutHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n m : ℕ} (s : (nerve I) _⦋n⦌)
    (p : ((Δ[n] : SSet.{u + 1}) ⊗ Δ[1]) _⦋m⦌)
    (i j k : Fin (m + 1)) (hij : i ≤ j) (hjk : j ≤ k) :=
  coherentDiagramCutHomotopy (kKanOriginalSuspensionPrism r F s) p i j k hij hjk

/-- 元の入力列の面・退化は、同じ実合成円柱の制限として厳密に整合する。 -/
lemma kKanPrismCutHomotopy_input_naturality {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n m d : ℕ} (s : (nerve I) _⦋n⦌)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (p : ((Δ[m] : SSet.{u + 1}) ⊗ Δ[1]) _⦋d⦌)
    (i j k : Fin (d + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    HEq (kKanPrismCutHomotopy r F ((nerve I).map θ.op s) p i j k hij hjk).h
      (kKanPrismCutHomotopy r F s
        ((SSet.stdSimplex.map θ ▷ (Δ[1] : SSet.{u + 1})).app _ p) i j k hij hjk).h := by
  have hp := ConcreteCategory.congr_hom
    (NatTrans.congr_app (kKanOriginalSuspensionPrism_naturality r F θ s).symm
      (Opposite.op ⦋d⦌)) p
  exact coherentPathMappingCutHomotopy_heq hp hij hjk

/-- 各 prism の全単体作用も、同じ元の豊穣円柱の制限を回収する。 -/
lemma kKanPrismCutHomotopy_naturality {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n m d : ℕ} (s : (nerve I) _⦋n⦌)
    (p : ((Δ[n] : SSet.{u + 1}) ⊗ Δ[1]) _⦋m⦌) (θ : ⦋d⦌ ⟶ ⦋m⦌)
    (i j k : Fin (d + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    HEq (kKanPrismCutHomotopy r F s
      (((Δ[n] : SSet.{u + 1}) ⊗ Δ[1]).map θ.op p) i j k hij hjk).h
      ((nerveMap (SimplicialThickening.functorMap θ.toOrderHom.uliftMap
        (.mk (ULift.up i)) (.mk (ULift.up k))) ▷ (Δ[1] : SSet.{u})) ≫
        (kKanPrismCutHomotopy r F s p (θ.toOrderHom i) (θ.toOrderHom j)
          (θ.toOrderHom k) (θ.toOrderHom.monotone hij) (θ.toOrderHom.monotone hjk)).h) :=
  coherentDiagramCutHomotopy_naturality (kKanOriginalSuspensionPrism r F s) p θ i j k hij hjk

/-- 端点 Path 上の辺は、同じ元の K prism の合成三角形から復号した辺そのもの。 -/
lemma kKanPrismCutHomotopy_endpoint_edge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n m : ℕ} (s : (nerve I) _⦋n⦌)
    (p : ((Δ[n] : SSet.{u + 1}) ⊗ Δ[1]) _⦋m⦌)
    (i j k : Fin (m + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (kKanPrismCutHomotopy r F s p i j k hij hjk)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentEndpointPath
        (show (ULift.up i : ULift.{u} _) ≤ ULift.up k from hij.trans hjk)))).edge =
      (coherentSimplexCompositionEdge
        ((kKanOriginalSuspensionPrism r F s).app _ p) i j k hij hjk).edge :=
  coherentDiagramCutHomotopy_endpoint_edge (kKanOriginalSuspensionPrism r F s) p i j k hij hjk

end SerrePositivity.KST.SConstruction

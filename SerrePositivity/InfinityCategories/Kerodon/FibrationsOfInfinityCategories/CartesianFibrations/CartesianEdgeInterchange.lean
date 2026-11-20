module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-! # 二つの辺の直積と中間交換
概要：二つのパラメーター辺を動かす順序を比較する実際の三角形を構成する。
方針：各因子の退化三角形の直積で同じ対角辺を回収する。
規約：Kan 性を要求せず、指定した辺を変えない。
使われ方：逆射と Kan 延長の自然性の合成の二次比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 二つの指定した辺を同時に辿る直積の辺。 -/
def cartesianEdgePair {K L : SSet.{u}} {x₀ x₁ : K _⦋0⦌} {y₀ y₁ : L _⦋0⦌}
    (e : K.Edge x₀ x₁) (f : L.Edge y₀ y₁) : (K ⊗ L).Edge (x₀, y₀) (x₁, y₁) :=
  SSet.Edge.mk (e.edge, f.edge) (congrArg₂ Prod.mk e.src_eq f.src_eq)
    (congrArg₂ Prod.mk e.tgt_eq f.tgt_eq)

/-- 指定した二つの合成三角形の直積。 -/
def cartesianEdgeCompStruct {K L : SSet.{u}}
    {x₀ x₁ x₂ : K _⦋0⦌} {y₀ y₁ y₂ : L _⦋0⦌}
    {e₀₁ : K.Edge x₀ x₁} {e₁₂ : K.Edge x₁ x₂} {e₀₂ : K.Edge x₀ x₂}
    {f₀₁ : L.Edge y₀ y₁} {f₁₂ : L.Edge y₁ y₂} {f₀₂ : L.Edge y₀ y₂}
    (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) (k : SSet.Edge.CompStruct f₀₁ f₁₂ f₀₂) :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e₀₁ f₀₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e₁₂ f₁₂)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e₀₂ f₀₂) where
  simplex := (h.simplex, k.simplex)
  d₂ := congrArg₂ Prod.mk h.d₂ k.d₂
  d₀ := congrArg₂ Prod.mk h.d₀ k.d₀
  d₁ := congrArg₂ Prod.mk h.d₁ k.d₁

/-- 第一因子の後で第二因子を動かす三角形は同じ直積対角辺を回収する。 -/
def cartesianEdgeLowerTriangle {K L : SSet.{u}} {x₀ x₁ : K _⦋0⦌} {y₀ y₁ : L _⦋0⦌}
    (e : K.Edge x₀ x₁) (f : L.Edge y₀ y₁) :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id y₀))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id x₁) f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeCompStruct (SSet.Edge.CompStruct.compId e) (SSet.Edge.CompStruct.idComp f)

/-- 第二因子の後で第一因子を動かす三角形も同じ直積対角辺を回収する。 -/
def cartesianEdgeUpperTriangle {K L : SSet.{u}} {x₀ x₁ : K _⦋0⦌} {y₀ y₁ : L _⦋0⦌}
    (e : K.Edge x₀ x₁) (f : L.Edge y₀ y₁) :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id x₀) f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id y₁)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeCompStruct (SSet.Edge.CompStruct.idComp e) (SSet.Edge.CompStruct.compId f)

/-- 任意の写像で直積を評価した二つの辿る順序はホモトピー圏で一致する。 -/
lemma cartesianEdgeInterchange {K L M : SSet.{u}} (F : K ⊗ L ⟶ M)
    {x₀ x₁ : K _⦋0⦌} {y₀ y₁ : L _⦋0⦌} (e : K.Edge x₀ x₁) (f : L.Edge y₀ y₁) :
    SSet.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id y₀)).map F) ≫
        SSet.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id x₁) f).map F) =
      SSet.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id x₀) f).map F) ≫
        SSet.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id y₁)).map F) :=
  (SSet.HomotopyCategory.homMk_comp_homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeLowerTriangle e f).map F)).trans
    (SSet.HomotopyCategory.homMk_comp_homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgeUpperTriangle e f).map F)).symm

/-- 左因子を固定した指定辺を、左右のパラメーター包含と二段の評価へ送る。 -/
def cartesianLeftParameterEdge {K A B L M N : SSet.{u}}
    (s : A ⟶ L) (t : B ⟶ L) (F : K ⊗ L ⟶ M) (G : M ⟶ N)
    (v : (K ⊗ A) _⦋0⦌) (w : B _⦋0⦌)
    (e : L.Edge (s.app _ v.2) (t.app _ w)) :
    N.Edge ((((𝟙 K ⊗ₘ s) ≫ F) ≫ G).app _ v)
      (((𝟙 K ⊗ₘ t) ≫ F ≫ G).app _ (v.1, w)) := by
  refine ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id v.1) e).map (F ≫ G)).ofEq ?_ ?_
  · rfl
  · rfl

/-- 右因子を固定した指定辺を、左右のパラメーター包含と二段の評価へ送る。 -/
def cartesianRightParameterEdge {K A B L M N : SSet.{u}}
    (s : A ⟶ L) (t : B ⟶ L) (F : L ⊗ K ⟶ M) (G : M ⟶ N)
    (v : A _⦋0⦌) (w : (B ⊗ K) _⦋0⦌)
    (e : L.Edge (s.app _ v) (t.app _ w.1)) :
    N.Edge (((s ⊗ₘ 𝟙 K) ≫ F ≫ G).app _ (v, w.2))
      ((((t ⊗ₘ 𝟙 K) ≫ F) ≫ G).app _ w) := by
  refine ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id w.2)).map (F ≫ G)).ofEq ?_ ?_
  · rfl
  · rfl

/-- 左の指定辺の評価は、合成された評価族の同じ辺の評価。 -/
lemma cartesianLeftParameterEdge_evaluation {K A B L M N Q : SSet.{u}}
    (s : A ⟶ L) (t : B ⟶ L) (F : K ⊗ L ⟶ M) (G : M ⟶ N)
    (H : N ⟶ Q) (T : K ⊗ L ⟶ Q) (h : F ≫ (G ≫ H) = T)
    (v : (K ⊗ A) _⦋0⦌) (w : B _⦋0⦌)
    (e : L.Edge (s.app _ v.2) (t.app _ w)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianLeftParameterEdge s t F G v w e).map H).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id v.1) e).map T).edge :=
  ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋1⦌))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair (.id v.1) e).edge

/-- 右の指定辺の評価は、合成された評価族の同じ辺の評価。 -/
lemma cartesianRightParameterEdge_evaluation {K A B L M N Q : SSet.{u}}
    (s : A ⟶ L) (t : B ⟶ L) (F : L ⊗ K ⟶ M) (G : M ⟶ N)
    (H : N ⟶ Q) (T : L ⊗ K ⟶ Q) (h : F ≫ (G ≫ H) = T)
    (v : A _⦋0⦌) (w : (B ⊗ K) _⦋0⦌)
    (e : L.Edge (s.app _ v) (t.app _ w.1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianRightParameterEdge s t F G v w e).map H).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id w.2)).map T).edge :=
  ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋1⦌))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianEdgePair e (.id w.2)).edge

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

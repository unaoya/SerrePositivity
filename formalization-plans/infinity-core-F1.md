# F1：fibration・straightening・Yoneda（レーン α2）

作成日：2026-10-18。状態：着手可能。全体の正本は [foundations.md](foundations.md)。
F0 の一般論は [infinity-core.md](infinity-core.md)（レーン α）が担当し、α2 はその成果を読むだけで編集しない。

## 0. 目標と範囲

Kerodon 第 5・6・7.3・8 章の内容を、quasicategory の組み合わせ論だけで形式化する。
到達点は (i) straightening/unstraightening の同値（Kerodon Theorem 5.6.0.2）、(ii) 随伴と局所化、
(iii) Kan 拡張、(iv) twisted arrow ∞ 圏と Hom 関手、前層 ∞ 圏 Fun(C^op, 𝒮) と Yoneda 埋め込み。
𝒮 := N^hc(Kan)（γ1 により quasicategory。Kan 複体の内部 Hom が Kan であることは Mathlib の
pushout-product から）。𝒮 の極限・余極限は F2（γ3）に委ね、本レーンでは 𝒮 を対象としてだけ使う。

既存（読むだけ）：A2d の left/right fibration（`Core/RightFibration.lean`）、A3b の Joyal の定理、
A3c〜A3e の写像空間・同値、`Coherent/` の coherent nerve。

## 1. 工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| F1a | cocartesian/cartesian 辺と fibration の定義、inner fibration との関係、left/right fibration との関係、合成・底変換での閉性、fiber が quasicategory | Kerodon 5.1 / HTT 2.4.1–2.4.2 |
| F1b | covariant transport：cocartesian fibration の辺に沿う fiber 間の関手、その一意性（可縮な選択空間）、ホモトピー圏への降下 | Kerodon 5.2 / HTT 2.4.4 |
| F1c | Cat_∞ := N^hc(QCat)（Kan 複体 core を Hom に取る単体的圏の coherent nerve。core は A3b の可逆辺）と Fun(C, Cat_∞) | Kerodon 5.5 / HTT 3.0 |
| F1d | **straightening**：cocartesian fibration U → N(C)（まず C が通常の圏）と関手 N(C) → Cat_∞ の対応、unstraightening の構成、同値（Theorem 5.6.0.2）。left fibration と 𝒮 値関手の場合を先に | Kerodon 5.6 / HTT 2.2.1.2、3.2 |
| F1e | 随伴（単位・余単位、写像空間での特徴づけ）、随伴関手の合成、Kan 拡張との関係 | Kerodon 6.1–6.2 / HTT 5.2 |
| F1f | 局所化 C → C[W⁻¹] の普遍性（Kerodon 6.3）と反射的部分 ∞ 圏 | Kerodon 6.3 / HTT 5.2.7 |
| F1g | 左右 Kan 拡張（点ごとの公式、存在と一意性）、cofinality の一般形（Quillen A） | Kerodon 7.2–7.3 / HTT 4.1.3、4.3 |
| F1h | twisted arrow ∞ 圏 Tw(C)、Hom 関手 C^op × C → 𝒮（F1d の left fibration 版で straighten）、前層 ∞ 圏 P(C) := Fun(C^op, 𝒮)、Yoneda 埋め込み、充満忠実性、表現可能関手と極限 | Kerodon 8.1–8.3 / HTT 5.1.3 |
| F1i | 検査：通常の圏の nerve で F1d・F1h が古典（Grothendieck 構成、Yoneda）に戻ること | — |

順序は F1a → F1b → F1c → F1d → F1e → F1f → F1g → F1h → F1i。F1d が最大の山で、
Kerodon 5.6 の証明（5.3 の「fibration の ∞ 圏」、5.4 の （∞,2）的道具を避ける経路）を
着手前に照合し、文言と証明方針を `Core/README.md` ではなく `InfinityCategories/F1/README.md` に記録する。

## 2. 設計上の決定

- 配置は `SerrePositivity/InfinityCategories/F1/`、namespace `SerrePositivity.InfinityCategories`。
  集約 `InfinityCategories/F1.lean` をルートに 1 行で追加する。
- fibration は `MorphismProperty.rlp` 流儀で定義し、A2d の left/right fibration と整合させる。
- Cat_∞ と 𝒮 は coherent nerve で定義する（γ1）。両者の極限・余極限は F2 まで主張しない。
- straightening は left fibration・𝒮 値の場合を先に完成させ、cocartesian・Cat_∞ 値へ拡張する。
- モデル構造（covariant/contravariant model structure）は使わない。Cisinski 流の代替は採らない。
- sorry・公理・引用は導入しない。実施記録はコミットメッセージ、宣言名と型の一覧は本文書 §3。

## 3. 現在地と主要宣言

```lean
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

def IsCartesianEdge {X B : SSet.{u}} (p : X ⟶ B) (e : X _⦋1⦌) : Prop

def IsCocartesianEdge {X B : SSet.{u}} (p : X ⟶ B) (e : X _⦋1⦌) : Prop

lemma isCartesianEdge_of_rightFibration {X B : SSet.{u}} (p : X ⟶ B)
    [RightFibration p] (e : X _⦋1⦌) : IsCartesianEdge p e

lemma isCocartesianEdge_of_leftFibration {X B : SSet.{u}} (p : X ⟶ B)
    [LeftFibration p] (e : X _⦋1⦌) : IsCocartesianEdge p e

lemma IsCartesianEdge.comp {X Y B : SSet.{u}} {p : X ⟶ Y} {q : Y ⟶ B}
    {e : X _⦋1⦌} (hp : IsCartesianEdge p e)
    (hq : IsCartesianEdge q (p.app (Opposite.op ⦋1⦌) e)) :
    IsCartesianEdge (p ≫ q) e

lemma IsCocartesianEdge.comp {X Y B : SSet.{u}} {p : X ⟶ Y} {q : Y ⟶ B}
    {e : X _⦋1⦌} (hp : IsCocartesianEdge p e)
    (hq : IsCocartesianEdge q (p.app (Opposite.op ⦋1⦌) e)) :
    IsCocartesianEdge (p ≫ q) e

def cartesianFibrations : MorphismProperty SSet.{u}

def cocartesianFibrations : MorphismProperty SSet.{u}

class CartesianFibration {X B : SSet.{u}} (p : X ⟶ B) : Prop

class CocartesianFibration {X B : SSet.{u}} (p : X ⟶ B) : Prop

instance cartesianFibration_innerFibration {X B : SSet.{u}} (p : X ⟶ B)
    [CartesianFibration p] : InnerFibration p

instance cocartesianFibration_innerFibration {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] : InnerFibration p

instance rightFibration_cartesianFibration {X B : SSet.{u}} (p : X ⟶ B)
    [RightFibration p] : CartesianFibration p

instance leftFibration_cocartesianFibration {X B : SSet.{u}} (p : X ⟶ B)
    [LeftFibration p] : CocartesianFibration p

instance cartesianFibration_comp {X Y B : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ B)
    [CartesianFibration p] [CartesianFibration q] : CartesianFibration (p ≫ q)

instance cocartesianFibration_comp {X Y B : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ B)
    [CocartesianFibration p] [CocartesianFibration q] : CocartesianFibration (p ≫ q)

lemma vertexFiber_quasicategory_of_innerFibration {X B : SSet.{u}} (p : X ⟶ B)
    [InnerFibration p] (b : B _⦋0⦌) : Quasicategory (vertexFiber p b)

lemma isCartesianEdge_pullback {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (e : (pullback p q) _⦋1⦌)
    (he : IsCartesianEdge p ((pullback.fst p q).app (Opposite.op ⦋1⦌) e)) :
    IsCartesianEdge (pullback.snd p q) e

lemma isCocartesianEdge_pullback {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (e : (pullback p q) _⦋1⦌)
    (he : IsCocartesianEdge p ((pullback.fst p q).app (Opposite.op ⦋1⦌) e)) :
    IsCocartesianEdge (pullback.snd p q) e

instance cartesianFibration_pullback_snd {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    [CartesianFibration p] : CartesianFibration (pullback.snd p q)

instance cocartesianFibration_pullback_snd {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    [CocartesianFibration p] : CocartesianFibration (pullback.snd p q)


lemma rightFibration_of_cartesianFibration_of_all_edges {X B : SSet.{u}}
    (p : X ⟶ B) [CartesianFibration p]
    (h : ∀ e : X _⦋1⦌, IsCartesianEdge p e) : RightFibration p

lemma rightFibration_iff_cartesianFibration_all_edges {X B : SSet.{u}} (p : X ⟶ B) :
    RightFibration p ↔ CartesianFibration p ∧ ∀ e : X _⦋1⦌, IsCartesianEdge p e

lemma leftFibration_of_cocartesianFibration_of_all_edges {X B : SSet.{u}}
    (p : X ⟶ B) [CocartesianFibration p]
    (h : ∀ e : X _⦋1⦌, IsCocartesianEdge p e) : LeftFibration p

lemma leftFibration_iff_cocartesianFibration_all_edges {X B : SSet.{u}} (p : X ⟶ B) :
    LeftFibration p ↔ CocartesianFibration p ∧ ∀ e : X _⦋1⦌, IsCocartesianEdge p e


structure CocartesianEdgeLift {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (x : (vertexFiber p (B.δ 1 e)) _⦋0⦌)

lemma nonempty_cocartesianEdgeLift {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (e : B _⦋1⦌)
    (x : (vertexFiber p (B.δ 1 e)) _⦋0⦌) : Nonempty (CocartesianEdgeLift p e x)

noncomputable def chooseCocartesianEdgeLift {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (e : B _⦋1⦌)
    (x : (vertexFiber p (B.δ 1 e)) _⦋0⦌) : CocartesianEdgeLift p e x

noncomputable def cocartesianTransportObject {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (e : B _⦋1⦌) :
    (vertexFiber p (B.δ 1 e)) _⦋0⦌ → (vertexFiber p (B.δ 0 e)) _⦋0⦌

lemma leftFibration_lift_boundary_prism {X B : SSet.{u}} (p : X ⟶ B)
    [LeftFibration p] (n : ℕ)
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ X)
    (F₀ : (Δ[n] : SSet.{u}) ⟶ X) (b : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ B)
    (hF₀ : (boundary n).ι ≫ F₀ = prismEndpoint 0 (boundary n : SSet.{u}) ≫ H)
    (hH : H ≫ p = (Δ[1] ◁ (boundary n).ι) ≫ b)
    (hb : F₀ ≫ p = prismEndpoint 0 Δ[n] ≫ b) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ X,
      (Δ[1] ◁ (boundary n).ι) ≫ F = H ∧
        prismEndpoint 0 Δ[n] ≫ F = F₀ ∧ F ≫ p = b


noncomputable def relativeEdgeSourceTarget {X B : SSet.{u}} (p : X ⟶ B) : SSet.{u}

noncomputable def relativeEdgeSource {X B : SSet.{u}} (p : X ⟶ B) :
    (ihom (Δ[1] : SSet.{u})).obj X ⟶ relativeEdgeSourceTarget p

instance relativeEdgeSource_trivialKanFibration {X B : SSet.{u}} (p : X ⟶ B)
    [LeftFibration p] : TrivialKanFibration (relativeEdgeSource p)

lemma leftFibration_lift_prism {A X B : SSet.{u}} (p : X ⟶ B) [LeftFibration p]
    (F₀ : A ⟶ X) (b : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (hb : F₀ ≫ p = prismEndpoint 0 A ≫ b) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ A ⟶ X,
      prismEndpoint 0 A ≫ F = F₀ ∧ F ≫ p = b

lemma prismEdgeFamily_zero {A B : SSet.{u}} (e : B _⦋1⦌) :
    prismEndpoint 0 A ≫ (fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e) =
      SSet.const (B.δ 1 e)

lemma prismEdgeFamily_one {A B : SSet.{u}} (e : B _⦋1⦌) :
    prismEndpoint 1 A ≫ (fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e) =
      SSet.const (B.δ 0 e)

lemma leftFibration_exists_transport {X B : SSet.{u}} (p : X ⟶ B) [LeftFibration p]
    (e : B _⦋1⦌) :
    ∃ (F : vertexFiber p (B.δ 1 e) ⟶ vertexFiber p (B.δ 0 e))
      (H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p (B.δ 1 e) ⟶ X),
      prismEndpoint 0 _ ≫ H = vertexFiberι p (B.δ 1 e) ∧
      prismEndpoint 1 _ ≫ H = F ≫ vertexFiberι p (B.δ 0 e) ∧
      H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e ∧
      ∀ x : (vertexFiber p (B.δ 1 e)) _⦋0⦌,
        IsCocartesianEdge p (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))

noncomputable def relativeEdgeLiftSpace {A X B : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p) : SSet.{u}

lemma relativeEdgeLiftSpace_isContractibleKan {A X B : SSet.{u}} (p : X ⟶ B)
    [LeftFibration p] (c : A ⟶ relativeEdgeSourceTarget p) :
    IsContractibleKan (relativeEdgeLiftSpace p c)

noncomputable def relativeEdgeLiftSpaceVertexEquiv {A X B : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p) :
    {F : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X // F ≫ relativeEdgeSource p = c} ≃
      (relativeEdgeLiftSpace p c) _⦋0⦌


lemma cocartesian_prism_exists_section {E : SSet.{u}} (n : ℕ)
    (p : E ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[n + 1]) [InnerFibration p]
    (a : (Subcomplex.unionProd (horn 1 0) (boundary (n + 1)) : SSet.{u}) ⟶ E)
    (ha : a ≫ p = (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι)
    (hc : IsCocartesianEdge p (a.app (Opposite.op ⦋1⦌)
      ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩)) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ E,
      (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ F = a ∧
        F ≫ p = 𝟙 _

lemma cocartesian_prism_exists_lift {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p]
    (n : ℕ)
    (a : (Subcomplex.unionProd (horn 1 0) (boundary (n + 1)) : SSet.{u}) ⟶ E)
    (b : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ B)
    (ha : a ≫ p = (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ b)
    (hc : IsCocartesianEdge p (a.app (Opposite.op ⦋1⦌)
      ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩)) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ E,
      (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ F = a ∧ F ≫ p = b


lemma cocartesian_prism_extend_boundary {X B : SSet.{u}} (p : X ⟶ B) [InnerFibration p]
    (n : ℕ) (H : (Δ[1] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u}) ⟶ X)
    (F₀ : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (b : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ B)
    (hF₀ : (boundary (n + 1)).ι ≫ F₀ =
      prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ H)
    (hHp : H ≫ p = (Δ[1] ◁ (boundary (n + 1)).ι) ≫ b)
    (hb : F₀ ≫ p = prismEndpoint 0 Δ[n + 1] ≫ b)
    (hH : IsCocartesianEdge p (H.app (Opposite.op ⦋1⦌)
      (prismBoundaryFirstVerticalEdge n))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ X,
      (Δ[1] ◁ (boundary (n + 1)).ι) ≫ F = H ∧
        prismEndpoint 0 Δ[n + 1] ≫ F = F₀ ∧ F ≫ p = b

def IsCocartesianPathVertex {X B : SSet.{u}} (p : X ⟶ B)
    (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) : Prop

def cocartesianPath {X B : SSet.{u}} (p : X ⟶ B) : SSet.{u}

def cocartesianPathι {X B : SSet.{u}} (p : X ⟶ B) :
    cocartesianPath p ⟶ (ihom (Δ[1] : SSet.{u})).obj X

noncomputable def cocartesianPathSource {X B : SSet.{u}} (p : X ⟶ B) :
    cocartesianPath p ⟶ relativeEdgeSourceTarget p

def cocartesianPathVertex {X B : SSet.{u}} (p : X ⟶ B) (f : (Δ[1] : SSet.{u}) ⟶ X)
    (hf : IsCocartesianEdge p (SSet.yonedaEquiv f)) : (cocartesianPath p) _⦋0⦌

lemma cocartesianPathSource_lift_vertex {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (b : (Δ[0] : SSet.{u}) ⟶ relativeEdgeSourceTarget p) :
    ∃ g : (Δ[0] : SSet.{u}) ⟶ cocartesianPath p, g ≫ cocartesianPathSource p = b

instance cocartesianPathSource_trivialKanFibration {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] : TrivialKanFibration (cocartesianPathSource p)

lemma cocartesianFibration_lift_prism {A X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (F₀ : A ⟶ X) (b : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (hb : F₀ ≫ p = prismEndpoint 0 A ≫ b) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ A ⟶ X,
      prismEndpoint 0 A ≫ F = F₀ ∧ F ≫ p = b ∧
      ∀ x : A _⦋0⦌, IsCocartesianEdge p (F.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))

lemma cocartesianFibration_exists_transport {X B : SSet.{u}} (p : X ⟶ B) [CocartesianFibration p]
    (e : B _⦋1⦌) :
    ∃ (F : vertexFiber p (B.δ 1 e) ⟶ vertexFiber p (B.δ 0 e))
      (H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p (B.δ 1 e) ⟶ X),
      prismEndpoint 0 _ ≫ H = vertexFiberι p (B.δ 1 e) ∧
      prismEndpoint 1 _ ≫ H = F ≫ vertexFiberι p (B.δ 0 e) ∧
      H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e ∧
      ∀ x : (vertexFiber p (B.δ 1 e)) _⦋0⦌,
        IsCocartesianEdge p (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))

noncomputable def cocartesianLiftSpace {A X B : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p) : SSet.{u}

lemma cocartesianLiftSpace_isContractibleKan {A X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (c : A ⟶ relativeEdgeSourceTarget p) :
    IsContractibleKan (cocartesianLiftSpace p c)

noncomputable def cocartesianLiftSpaceVertexEquiv {A X B : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p) :
    {F : A ⟶ cocartesianPath p // F ≫ cocartesianPathSource p = c} ≃
      (cocartesianLiftSpace p c) _⦋0⦌


lemma ihom_map_const {A X B : SSet.{u}} (b : B _⦋0⦌) :
    (ihom A).map (SSet.const b : X ⟶ B) =
      SSet.const (functorVertex (SSet.const b : A ⟶ B))

lemma uncurry_const_functorVertex {A L B : SSet.{u}} (f : A ⟶ B) :
    uncurry (SSet.const (functorVertex f) : L ⟶ (ihom A).obj B) = fst A L ≫ f

instance vertexFiberι_mono {X B : SSet.{u}} (p : X ⟶ B) (b : B _⦋0⦌) :
    Mono (vertexFiberι p b)

def ihomVertexFiberMap (A : SSet.{u}) {X B : SSet.{u}} (p : X ⟶ B) (b : B _⦋0⦌) :
    (ihom A).obj (vertexFiber p b) ⟶
      vertexFiber ((ihom A).map p) (functorVertex (SSet.const b : A ⟶ B))

def ihomVertexFiberInverse (A : SSet.{u}) {X B : SSet.{u}} (p : X ⟶ B) (b : B _⦋0⦌) :
    vertexFiber ((ihom A).map p) (functorVertex (SSet.const b : A ⟶ B)) ⟶
      (ihom A).obj (vertexFiber p b)

lemma ihomVertexFiberInverse_comp (A : SSet.{u}) {X B : SSet.{u}} (p : X ⟶ B)
    (b : B _⦋0⦌) :
    ihomVertexFiberInverse A p b ≫ (ihom A).map (vertexFiberι p b) =
      vertexFiberι ((ihom A).map p) (functorVertex (SSet.const b : A ⟶ B))

def ihomVertexFiberIso (A : SSet.{u}) {X B : SSet.{u}} (p : X ⟶ B) (b : B _⦋0⦌) :
    (ihom A).obj (vertexFiber p b) ≅
      vertexFiber ((ihom A).map p) (functorVertex (SSet.const b : A ⟶ B))

def cocartesianPathEndpoint {X B : SSet.{u}} (p : X ⟶ B) (i : Fin 2) :
    cocartesianPath p ⟶ X

lemma cocartesianPathEndpoint_comp {X B : SSet.{u}} (p : X ⟶ B) :
    cocartesianPathEndpoint p 1 ≫ p = cocartesianPathSource p ≫
      pullback.snd p (evaluateFunctorAt (Y

noncomputable def cocartesianLiftSpaceEndpoint {A X B : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p) :
    cocartesianLiftSpace p c ⟶ vertexFiber ((ihom A).map p)
      (functorVertex (c ≫ pullback.snd p
        (evaluateFunctorAt (Y

noncomputable def IsContractibleKan.vertexIso {K : SSet.{u}} (h : IsContractibleKan K)
    (x y : K _⦋0⦌) : VertexIso x y

noncomputable def cocartesianLiftSpaceEndpointIso {A X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (c : A ⟶ relativeEdgeSourceTarget p)
    (x y : (cocartesianLiftSpace p c) _⦋0⦌) :
    VertexIso ((cocartesianLiftSpaceEndpoint p c).app (Opposite.op ⦋0⦌) x)
      ((cocartesianLiftSpaceEndpoint p c).app (Opposite.op ⦋0⦌) y)

noncomputable def transportSourceDiagram {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌) :
    vertexFiber p (B.δ 1 e) ⟶ relativeEdgeSourceTarget p

lemma transportSourceDiagram_endpoint {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌) :
    transportSourceDiagram p e ≫ pullback.snd p
      (evaluateFunctorAt (Y

noncomputable def transportChoiceSpace {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌) : SSet.{u}

lemma transportChoiceSpace_isContractibleKan {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (e : B _⦋1⦌) : IsContractibleKan (transportChoiceSpace p e)

noncomputable def transportChoiceLift {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (x : (transportChoiceSpace p e) _⦋0⦌) :
    {F : vertexFiber p (B.δ 1 e) ⟶ cocartesianPath p //
      F ≫ cocartesianPathSource p = transportSourceDiagram p e}

noncomputable def transportChoiceEndpoint {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌) :
    transportChoiceSpace p e ⟶ (ihom (vertexFiber p (B.δ 1 e))).obj (vertexFiber p (B.δ 0 e))

lemma transportChoiceEndpoint_comp {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌) :
    transportChoiceEndpoint p e ≫ (ihom (vertexFiber p (B.δ 1 e))).map (vertexFiberι p (B.δ 0 e)) =
      vertexFiberι ((ihom (vertexFiber p (B.δ 1 e))).map (cocartesianPathSource p))
        (functorVertex (transportSourceDiagram p e)) ≫
          (ihom (vertexFiber p (B.δ 1 e))).map (cocartesianPathEndpoint p 1)

noncomputable def transportAtChoice {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (x : (transportChoiceSpace p e) _⦋0⦌) :
    vertexFiber p (B.δ 1 e) ⟶ vertexFiber p (B.δ 0 e)

lemma transportChoiceLift_vertex {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (x : (transportChoiceSpace p e) _⦋0⦌) :
    functorVertex (transportChoiceLift p e x).val = x.val

lemma transportAtChoice_vertex {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (x : (transportChoiceSpace p e) _⦋0⦌) :
    functorVertex (transportAtChoice p e x) =
      (transportChoiceEndpoint p e).app (Opposite.op ⦋0⦌) x

lemma transportAtChoice_witness {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (x : (transportChoiceSpace p e) _⦋0⦌) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p (B.δ 1 e) ⟶ X,
      prismEndpoint 0 _ ≫ H = vertexFiberι p (B.δ 1 e) ∧
      prismEndpoint 1 _ ≫ H = transportAtChoice p e x ≫ vertexFiberι p (B.δ 0 e) ∧
      H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e ∧
      ∀ v : (vertexFiber p (B.δ 1 e)) _⦋0⦌, IsCocartesianEdge p
        (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))

noncomputable def transportAtChoiceIso {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (e : B _⦋1⦌) (x y : (transportChoiceSpace p e) _⦋0⦌) :
    FunctorIso (transportAtChoice p e x) (transportAtChoice p e y)


def IsCocartesianTransport {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (F : vertexFiber p (B.δ 1 e) ⟶ vertexFiber p (B.δ 0 e)) : Prop

noncomputable def transportChoiceOfPrism {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p (B.δ 1 e) ⟶ X)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (B.δ 1 e))
    (hb : H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e)
    (hc : ∀ v : (vertexFiber p (B.δ 1 e)) _⦋0⦌, IsCocartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))) :
    (transportChoiceSpace p e) _⦋0⦌

lemma transportChoiceOfPrism_lift {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p (B.δ 1 e) ⟶ X)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (B.δ 1 e))
    (hb : H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e)
    (hc : ∀ v : (vertexFiber p (B.δ 1 e)) _⦋0⦌, IsCocartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))) :
    (transportChoiceLift p e (transportChoiceOfPrism p e H h₀ hb hc)).val ≫
      cocartesianPathι p = curry H

lemma transportAtChoice_ofPrism {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (F : vertexFiber p (B.δ 1 e) ⟶ vertexFiber p (B.δ 0 e))
    (H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p (B.δ 1 e) ⟶ X)
    (h₀ : prismEndpoint 0 _ ≫ H = vertexFiberι p (B.δ 1 e))
    (h₁ : prismEndpoint 1 _ ≫ H = F ≫ vertexFiberι p (B.δ 0 e))
    (hb : H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e)
    (hc : ∀ v : (vertexFiber p (B.δ 1 e)) _⦋0⦌, IsCocartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))) :
    transportAtChoice p e (transportChoiceOfPrism p e H h₀ hb hc) = F

lemma IsCocartesianTransport.functorIso {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (e : B _⦋1⦌)
    {F G : vertexFiber p (B.δ 1 e) ⟶ vertexFiber p (B.δ 0 e)}
    (hF : IsCocartesianTransport p e F) (hG : IsCocartesianTransport p e G) :
    Nonempty (FunctorIso F G)

noncomputable def cocartesianTransport {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (e : B _⦋1⦌) :
    vertexFiber p (B.δ 1 e) ⟶ vertexFiber p (B.δ 0 e)

lemma cocartesianTransport_isTransport {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (e : B _⦋1⦌) :
    IsCocartesianTransport p e (cocartesianTransport p e)

noncomputable def cocartesianTransportHo {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (e : B _⦋1⦌) :
    hoFunctor.obj (vertexFiber p (B.δ 1 e)) ⥤ hoFunctor.obj (vertexFiber p (B.δ 0 e))

lemma IsCocartesianTransport.toHoIso {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (e : B _⦋1⦌)
    {F : vertexFiber p (B.δ 1 e) ⟶ vertexFiber p (B.δ 0 e)}
    (hF : IsCocartesianTransport p e F) :
    Nonempty ((hoFunctor.map F).toFunctor ≅ cocartesianTransportHo p e)


lemma isCartesianEdge_of_isInvertibleEdge {X B : SSet.{u}} [Quasicategory X]
    [Quasicategory B] (p : X ⟶ B) [InnerFibration p] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X

lemma isCocartesianEdge_of_isInvertibleEdge {X B : SSet.{u}} [Quasicategory X]
    [Quasicategory B] (p : X ⟶ B) [InnerFibration p] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X

lemma isCocartesianEdge_constant {X B : SSet.{u}} [Quasicategory X] [Quasicategory B]
    (p : X ⟶ B) [InnerFibration p] (x : X _⦋0⦌) :
    IsCocartesianEdge p (PinchedHom.constant x 1)

lemma isInvertibleEdge_of_isCartesianEdge {X B : SSet.{u}} [Quasicategory B]
    (p : X ⟶ B) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X

lemma isInvertibleEdge_iff_isCartesianEdge {X B : SSet.{u}} [Quasicategory X]
    [Quasicategory B] (p : X ⟶ B) [InnerFibration p] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X

lemma isInvertibleEdge_of_isCocartesianEdge {X B : SSet.{u}} [Quasicategory X]
    [Quasicategory B]
    (p : X ⟶ B) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X

lemma isInvertibleEdge_iff_isCocartesianEdge {X B : SSet.{u}} [Quasicategory X]
    [Quasicategory B] (p : X ⟶ B) [InnerFibration p] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X

def IsEdgeTransport {X B : SSet.{u}} (p : X ⟶ B) {a b : B _⦋0⦌}
    (e : SSet.Truncated.Edge (X

noncomputable def edgeTransport {X B : SSet.{u}} (p : X ⟶ B) [CocartesianFibration p]
    {a b : B _⦋0⦌} (e : SSet.Truncated.Edge (X

lemma edgeTransport_isTransport {X B : SSet.{u}} (p : X ⟶ B) [CocartesianFibration p]
    {a b : B _⦋0⦌} (e : SSet.Truncated.Edge (X

lemma IsEdgeTransport.functorIso {X B : SSet.{u}} (p : X ⟶ B) [CocartesianFibration p]
    {a b : B _⦋0⦌} (e : SSet.Truncated.Edge (X

lemma isEdgeTransport_identity {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [CocartesianFibration p] (b : B _⦋0⦌) :
    IsEdgeTransport p (SSet.Truncated.Edge.id (X

lemma edgeTransport_identity_iso {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [CocartesianFibration p] (b : B _⦋0⦌) :
    Nonempty (FunctorIso
      (edgeTransport p (SSet.Truncated.Edge.id (X


def initialEdgeJoinIso (n : ℕ) : join (Δ[1] : SSet.{u}) Δ[n] ≅ Δ[n + 2]

lemma initialHorn_preimage_eqToIso {A : SSet.{u}} {m n : ℕ} (h : m = n)
    (e : A ≅ (Δ[m] : SSet.{u})) :
    (horn n 0).preimage
      (e ≪≫ eqToIso (congrArg (fun d : ℕ ↦ (Δ[d] : SSet.{u})) h)).hom =
        (horn m 0).preimage e.hom

lemma initialHornJoin_preimage (n : ℕ) :
    (horn (n + 2) 0).preimage (initialEdgeJoinIso.{u} n).hom =
      joinUnion (horn 1 0) (boundary n)

def initialHornJoinIso (n : ℕ) :
    (joinUnion (horn 1 0) (boundary n) : SSet.{u}) ≅ horn (n + 2) 0

lemma initialHornJoinIso_hom_ι (n : ℕ) :
    (initialHornJoinIso.{u} n).hom ≫ (horn (n + 2) 0).ι =
      (joinUnion (horn 1 0) (boundary n)).ι ≫ (initialEdgeJoinIso n).hom

lemma initialEdge_eqToIso {m n : ℕ} (h : m = n) :
    (eqToIso (congrArg (fun d : ℕ ↦ (Δ[d] : SSet.{u})) h)).hom.app (Opposite.op ⦋1⦌)
      (stdSimplex.edge m 0 1 (Fin.zero_le _)) = stdSimplex.edge n 0 1 (Fin.zero_le _)

lemma initialEdgeJoinIso_inl_edge (n : ℕ) :
    SSet.yonedaEquiv (joinInl (Δ[1] : SSet.{u}) Δ[n] ≫ (initialEdgeJoinIso n).hom) =
      stdSimplex.edge (n + 2) 0 1 (Fin.zero_le _)

lemma initialHornJoinIso_edge (n : ℕ) :
    SSet.yonedaEquiv (joinInl (Δ[1] : SSet.{u}) (boundary n : SSet.{u}) ≫
      joinUnionRight (horn 1 0) (boundary n) ≫ (initialHornJoinIso n).hom) =
        initialHornEdge n

lemma initialHornJoinIso_inv_ι (n : ℕ) :
    (initialHornJoinIso.{u} n).inv ≫ (joinUnion (horn 1 0) (boundary n)).ι =
      (horn (n + 2) 0).ι ≫ (initialEdgeJoinIso n).inv

lemma relativeCosliceMap_boundary_of_isCocartesianEdge {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y)
    (he : IsCocartesianEdge q (SSet.yonedaEquiv e)) (n : ℕ) :
    HasLiftingProperty (boundary n).ι (relativeCosliceMap e q (horn 1 0))

lemma relativeCosliceMap_trivialKanFibration_of_isCocartesianEdge {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y)
    (he : IsCocartesianEdge q (SSet.yonedaEquiv e)) :
    TrivialKanFibration (relativeCosliceMap e q (horn 1 0))

lemma isCocartesianEdge_of_relativeCosliceMap_trivialKanFibration {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y)
    (hq : TrivialKanFibration (relativeCosliceMap e q (horn 1 0))) :
    IsCocartesianEdge q (SSet.yonedaEquiv e)

lemma isCocartesianEdge_iff_relativeCosliceMap_trivialKanFibration {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y) :
    IsCocartesianEdge q (SSet.yonedaEquiv e) ↔
      TrivialKanFibration (relativeCosliceMap e q (horn 1 0))


lemma relativeCosliceMap_lift_of_rightAnodyne {A K X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (A₀ : A.Subcomplex) (K₀ : K.Subcomplex) (hK : rightAnodyneExtensions K₀.ι) :
    HasLiftingProperty A₀.ι (relativeCosliceMap p q K₀)

lemma relativeCosliceMap_trivialKanFibration_of_rightAnodyne {K X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (K₀ : K.Subcomplex) (hK : rightAnodyneExtensions K₀.ι) :
    TrivialKanFibration (relativeCosliceMap p q K₀)

lemma endpointInclusion_rightAnodyne :
    rightAnodyneExtensions (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])

lemma triangleLongEdge_rightAnodyne :
    rightAnodyneExtensions (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2])

lemma triangleLongFace_rightAnodyne :
    rightAnodyneExtensions (stdSimplex.face (n := 2) {(1 : Fin 3)}ᶜ :
      (Δ[2] : SSet.{u}).Subcomplex).ι

noncomputable def squareComparison {E F B C : SSet.{u}} {f : E ⟶ F} {p : E ⟶ B}
    {q : F ⟶ C} {g : B ⟶ C} (sq : CommSq f p q g) : E ⟶ pullback q g

lemma squareComparison_exists_lift {E F B C A D : SSet.{u}} {f : E ⟶ F} {p : E ⟶ B}
    {q : F ⟶ C} {g : B ⟶ C} (sq : CommSq f p q g)
    [TrivialKanFibration (squareComparison sq)] (i : A ⟶ D) [Mono i]
    (a : A ⟶ E) (b : D ⟶ F) (c : D ⟶ B)
    (hab : a ≫ f = i ≫ b) (hac : a ≫ p = i ≫ c) (hbc : b ≫ q = c ≫ g) :
    ∃ l : D ⟶ E, i ≫ l = a ∧ l ≫ f = b ∧ l ≫ p = c

lemma squareComparison_trivialKanFibration_horiz_comp
    {E₂ E₁ E₀ B₂ B₁ B₀ : SSet.{u}}
    {f : E₂ ⟶ E₁} {g : E₁ ⟶ E₀} {p₂ : E₂ ⟶ B₂} {p₁ : E₁ ⟶ B₁}
    {p₀ : E₀ ⟶ B₀} {b : B₂ ⟶ B₁} {c : B₁ ⟶ B₀}
    (sq₂ : CommSq f p₂ p₁ b) (sq₁ : CommSq g p₁ p₀ c)
    [TrivialKanFibration (squareComparison sq₂)]
    [TrivialKanFibration (squareComparison sq₁)] :
    TrivialKanFibration (squareComparison (sq₂.horiz_comp sq₁))

lemma squareComparison_trivialKanFibration_cancel_left
    {E₂ E₁ E₀ B₂ B₁ B₀ : SSet.{u}}
    {f : E₂ ⟶ E₁} {g : E₁ ⟶ E₀} {p₂ : E₂ ⟶ B₂} {p₁ : E₁ ⟶ B₁}
    {p₀ : E₀ ⟶ B₀} {b : B₂ ⟶ B₁} {c : B₁ ⟶ B₀}
    (sq₂ : CommSq f p₂ p₁ b) (sq₁ : CommSq g p₁ p₀ c)
    [TrivialKanFibration b] [TrivialKanFibration (squareComparison sq₂)]
    [TrivialKanFibration (squareComparison (sq₂.horiz_comp sq₁))] :
    TrivialKanFibration (squareComparison sq₁)

def joinLeftFunctor (B : SSet.{u}) : SSet.{u} ⥤ SSet.{u}

lemma joinSubcomplexLeft_inf (B : SSet.{u}) {A : SSet.{u}} (A₀ A₁ : A.Subcomplex) :
    joinSubcomplexLeft (A₀ ⊓ A₁) B = joinSubcomplexLeft A₀ B ⊓ joinSubcomplexLeft A₁ B

lemma joinSubcomplexLeft_sup (B : SSet.{u}) {A : SSet.{u}} (A₀ A₁ : A.Subcomplex) :
    joinSubcomplexLeft (A₀ ⊔ A₁) B = joinSubcomplexLeft A₀ B ⊔ joinSubcomplexLeft A₁ B

lemma joinSubcomplexLeft_bicartSq (B : SSet.{u}) {A : SSet.{u}}
    {A₀ A₁ A₂ A₃ : A.Subcomplex} (h : Subcomplex.BicartSq A₀ A₁ A₂ A₃) :
    Subcomplex.BicartSq (joinSubcomplexLeft A₀ B) (joinSubcomplexLeft A₁ B)
      (joinSubcomplexLeft A₂ B) (joinSubcomplexLeft A₃ B)

noncomputable def joinLeftSubcomplexIso (B : SSet.{u}) {A C : SSet.{u}}
    (A₀ : A.Subcomplex) (e : C ≅ (A₀ : SSet.{u})) :
    join C B ≅ (joinSubcomplexLeft A₀ B : SSet.{u})

lemma joinLeftSubcomplexIso_hom_ι (B : SSet.{u}) {A C : SSet.{u}}
    (A₀ : A.Subcomplex) (e : C ≅ (A₀ : SSet.{u})) :
    (joinLeftSubcomplexIso B A₀ e).hom ≫ (joinSubcomplexLeft A₀ B).ι =
      joinMap (e.hom ≫ A₀.ι) (𝟙 B)

lemma joinLeft_horn₂₁_isPushout (A : SSet.{u}) :
    IsPushout (joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 A))
      (joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 A))
      (joinMap horn₂₁.ι₀₁ (𝟙 A)) (joinMap horn₂₁.ι₁₂ (𝟙 A))

lemma sliceUnderRestrict_comp {K L M X : SSet.{u}} (p : K ⟶ X)
    (f : L ⟶ K) (g : M ⟶ L) :
    sliceUnderRestrict p f ≫ sliceUnderRestrict (f ≫ p) g =
      sliceUnderRestrict p (g ≫ f)

lemma cosliceRestrictionSquare {K L X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y)
    (f : L ⟶ K) :
    CommSq (sliceUnderRestrict p f) (sliceUnderPostcomp p q)
      (sliceUnderPostcomp (f ≫ p) q) (sliceUnderRestrict (p ≫ q) f)

noncomputable def relativeCosliceRestriction {K L X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (f : L ⟶ K) :
    sliceUnder p ⟶ pullback (sliceUnderPostcomp (f ≫ p) q)
      (sliceUnderRestrict (p ≫ q) f)

lemma relativeCosliceRestriction_subcomplex {K X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (K₀ : K.Subcomplex) :
    relativeCosliceRestriction p q K₀.ι = relativeCosliceMap p q K₀

lemma relativeCosliceRestriction_trivialKanFibration_comp {K L M X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (f : L ⟶ K) (g : M ⟶ L)
    [TrivialKanFibration (relativeCosliceRestriction p q f)]
    [TrivialKanFibration (relativeCosliceRestriction (f ≫ p) q g)] :
    TrivialKanFibration (relativeCosliceRestriction p q (g ≫ f))

lemma relativeCosliceRestriction_trivialKanFibration_cancel {K L M X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (f : L ⟶ K) (g : M ⟶ L)
    [TrivialKanFibration (sliceUnderRestrict (p ≫ q) f)]
    [TrivialKanFibration (relativeCosliceRestriction p q f)]
    [TrivialKanFibration (relativeCosliceRestriction p q (g ≫ f))] :
    TrivialKanFibration (relativeCosliceRestriction (f ≫ p) q g)

lemma squareComparison_trivialKanFibration_congr {E F B C : SSet.{u}}
    {f f' : E ⟶ F} {p : E ⟶ B} {q : F ⟶ C} {g g' : B ⟶ C}
    (sq : CommSq f p q g) (sq' : CommSq f' p q g') (hf : f = f') (hg : g = g') :
    TrivialKanFibration (squareComparison sq) ↔
      TrivialKanFibration (squareComparison sq')

instance sliceUnderRestrict_isIso {K L X : SSet.{u}} (p : K ⟶ X)
    (f : L ⟶ K) [IsIso f] : IsIso (sliceUnderRestrict p f)

instance squareComparison_isIso {E F B C : SSet.{u}} {f : E ⟶ F} {p : E ⟶ B}
    {q : F ⟶ C} {g : B ⟶ C} (sq : CommSq f p q g) [IsIso f] [IsIso g] :
    IsIso (squareComparison sq)

instance relativeCosliceRestriction_isIso {K L X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (f : L ⟶ K) [IsIso f] :
    IsIso (relativeCosliceRestriction p q f)

lemma relativeCosliceRestriction_trivialKanFibration_subcomplexIso {K L X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (K₀ : K.Subcomplex) (e : L ≅ (K₀ : SSet.{u}))
    [TrivialKanFibration (relativeCosliceMap p q K₀)] :
    TrivialKanFibration (relativeCosliceRestriction p q (e.hom ≫ K₀.ι))

lemma relativeCosliceRestriction_triangleLongEdge {X Y : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q] :
    TrivialKanFibration (relativeCosliceRestriction t q (stdSimplex.δ (1 : Fin 3)))

lemma sliceUnderRestrict_lift_of_rightAnodyne {A K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A₀ : A.Subcomplex) (K₀ : K.Subcomplex)
    (hK : rightAnodyneExtensions K₀.ι) : HasLiftingProperty A₀.ι (sliceUnderRestrict p K₀.ι)

lemma sliceUnderRestrict_trivialKanFibration_of_rightAnodyne {K X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (K₀ : K.Subcomplex)
    (hK : rightAnodyneExtensions K₀.ι) : TrivialKanFibration (sliceUnderRestrict p K₀.ι)

lemma sliceUnderRestrict_trivialKanFibration_subcomplexIso {K L X : SSet.{u}}
    (p : K ⟶ X) (K₀ : K.Subcomplex) (e : L ≅ (K₀ : SSet.{u}))
    [TrivialKanFibration (sliceUnderRestrict p K₀.ι)] :
    TrivialKanFibration (sliceUnderRestrict p (e.hom ≫ K₀.ι))

lemma sliceUnderRestrict_triangleLongEdge {X : SSet.{u}} [Quasicategory X]
    (t : (Δ[2] : SSet.{u}) ⟶ X) :
    TrivialKanFibration (sliceUnderRestrict t (stdSimplex.δ (1 : Fin 3)))

lemma initialHorn_eq_sourceFace :
    horn.{u} 1 0 = stdSimplex.face {(1 : Fin 2)}ᶜ

lemma relativeCosliceRestriction_source_of_isCocartesianEdge {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y)
    (he : IsCocartesianEdge q (SSet.yonedaEquiv e)) :
    TrivialKanFibration (relativeCosliceRestriction e q (stdSimplex.δ (1 : Fin 2)))

lemma isCocartesianEdge_of_relativeCosliceRestriction_source {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y)
    [TrivialKanFibration (relativeCosliceRestriction e q (stdSimplex.δ (1 : Fin 2)))] :
    IsCocartesianEdge q (SSet.yonedaEquiv e)

lemma relativeCosliceRestriction_extendCone {K L X Y A : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (f : L ⟶ K)
    [TrivialKanFibration (relativeCosliceRestriction p q f)] (A₀ : A.Subcomplex)
    (G : join K (A₀ : SSet.{u}) ⟶ X) (H : join L A ⟶ X) (B : join K A ⟶ Y)
    (hG : joinInl K (A₀ : SSet.{u}) ≫ G = p)
    (hH : joinInl L A ≫ H = f ≫ p) (hB : joinInl K A ≫ B = p ≫ q)
    (hGH : joinMap f (𝟙 (A₀ : SSet.{u})) ≫ G = joinMap (𝟙 L) A₀.ι ≫ H)
    (hGq : G ≫ q = joinMap (𝟙 K) A₀.ι ≫ B)
    (hHq : H ≫ q = joinMap f (𝟙 A) ≫ B) :
    ∃ T : join K A ⟶ X, joinInl K A ≫ T = p ∧
      joinMap (𝟙 K) A₀.ι ≫ T = G ∧ joinMap f (𝟙 A) ≫ T = H ∧ T ≫ q = B

lemma cocartesianTriangle_extendCone {X Y A : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (he : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t)))
    (A₀ : A.Subcomplex) (G : join (Δ[2] : SSet.{u}) (A₀ : SSet.{u}) ⟶ X)
    (H : join (Δ[1] : SSet.{u}) A ⟶ X) (B : join (Δ[2] : SSet.{u}) A ⟶ Y)
    (hG : joinInl _ _ ≫ G = t)
    (hH : joinInl _ _ ≫ H = stdSimplex.δ (2 : Fin 3) ≫ t)
    (hB : joinInl _ _ ≫ B = t ≫ q)
    (hGH : joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 _) A₀.ι ≫ H)
    (hGq : G ≫ q = joinMap (𝟙 _) A₀.ι ≫ B)
    (hHq : H ≫ q = joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 A) ≫ B) :
    ∃ T : join (Δ[2] : SSet.{u}) A ⟶ X, joinInl _ _ ≫ T = t ∧
      joinMap (𝟙 _) A₀.ι ≫ T = G ∧
      joinMap (stdSimplex.δ (2 : Fin 3)) (𝟙 A) ≫ T = H ∧ T ≫ q = B

lemma relativeCosliceRestriction_triangleFirstEdge_lift {X Y A : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (he : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t)))
    (A₀ : A.Subcomplex) :
    HasLiftingProperty A₀.ι (relativeCosliceRestriction t q (stdSimplex.δ (2 : Fin 3)))

lemma relativeCosliceRestriction_triangleFirstEdge {X Y : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (he : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t))) :
    TrivialKanFibration (relativeCosliceRestriction t q (stdSimplex.δ (2 : Fin 3)))

lemma isCocartesianEdge_triangle_longEdge {X Y : SSet.{u}} [Quasicategory Y]
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (hfirst : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t)))
    (hsecond : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t))) :
    IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ t))

lemma trianglePrism_endpoint_one (A : SSet.{u}) :
    ((stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ▷ A) =
      snd (Δ[0] : SSet.{u}) A ≫ prismEndpoint 1 A

lemma trianglePrism_endpoint_zero (A : SSet.{u}) :
    ((stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ▷ A) =
      snd (Δ[0] : SSet.{u}) A ≫ prismEndpoint 0 A

lemma innerFibration_fillTrianglePrism {X B A : SSet.{u}} (p : X ⟶ B)
    [InnerFibration p] (H₀₁ H₁₂ : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (b : (Δ[2] : SSet.{u}) ⊗ A ⟶ B)
    (hw : prismEndpoint 1 A ≫ H₀₁ = prismEndpoint 0 A ≫ H₁₂)
    (h₀₁ : H₀₁ ≫ p = (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ b)
    (h₁₂ : H₁₂ ≫ p = (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ b) :
    ∃ T : (Δ[2] : SSet.{u}) ⊗ A ⟶ X,
      (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ T = H₀₁ ∧
      (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ T = H₁₂ ∧ T ≫ p = b

lemma cocartesianTrianglePrism_longEdge {X B A : SSet.{u}} [Quasicategory B]
    (p : X ⟶ B) [InnerFibration p] (T : (Δ[2] : SSet.{u}) ⊗ A ⟶ X)
    (hfirst : ∀ v : A _⦋0⦌, IsCocartesianEdge p
      (((stdSimplex.δ (2 : Fin 3) ▷ A) ≫ T).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1)))
    (hsecond : ∀ v : A _⦋0⦌, IsCocartesianEdge p
      (((stdSimplex.δ (0 : Fin 3) ▷ A) ≫ T).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))) :
    ∀ v : A _⦋0⦌, IsCocartesianEdge p
      (((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ T).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))

lemma IsEdgeTransport.comp {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [InnerFibration p] {a b c : B _⦋0⦌}
    {e : SSet.Edge (X := B) a b} {f : SSet.Edge (X := B) b c}
    {g : SSet.Edge (X := B) a c} (σ : SSet.Edge.CompStruct e f g)
    {F : vertexFiber p a ⟶ vertexFiber p b} {G : vertexFiber p b ⟶ vertexFiber p c}
    (hF : IsEdgeTransport p e F) (hG : IsEdgeTransport p f G) :
    IsEdgeTransport p g (F ≫ G)

lemma edgeTransport_composition_iso {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [CocartesianFibration p] {a b c : B _⦋0⦌}
    {e : SSet.Edge (X := B) a b} {f : SSet.Edge (X := B) b c}
    {g : SSet.Edge (X := B) a c} (σ : SSet.Edge.CompStruct e f g) :
    Nonempty (FunctorIso (edgeTransport p g) (edgeTransport p e ≫ edgeTransport p f))

def homotopyQCatHomSetoid (X Y : SSet.{u}) : Setoid (X ⟶ Y)

structure HomotopyQCat where
  obj : SSet.{u}
  isQuasicategory : Quasicategory obj

instance homotopyQCat_category : Category HomotopyQCat.{u}

def homotopyQCatHomMk {X Y : HomotopyQCat.{u}} (f : X.obj ⟶ Y.obj) : X ⟶ Y

lemma homotopyQCatHomMk_eq_of_functorIso {X Y : HomotopyQCat.{u}}
    {f g : X.obj ⟶ Y.obj} (h : Nonempty (FunctorIso f g)) :
    homotopyQCatHomMk f = homotopyQCatHomMk g

lemma homotopyQCatHomMk_comp {X Y Z : HomotopyQCat.{u}}
    (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) :
    homotopyQCatHomMk (f ≫ g) = homotopyQCatHomMk f ≫ homotopyQCatHomMk g

def homotopyTransportFiber {X B : SSet.{u}} (p : X ⟶ B) [CocartesianFibration p]
    (b : B _⦋0⦌) : HomotopyQCat.{u}

noncomputable def homotopyTransport {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [CocartesianFibration p] : hoFunctor.obj B ⥤ HomotopyQCat.{u}

lemma homotopyTransport_obj {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [CocartesianFibration p] (b : B _⦋0⦌) :
    (homotopyTransport p).obj (SSet.HomotopyCategory.mk b) = homotopyTransportFiber p b

lemma homotopyTransport_map_edge {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [CocartesianFibration p] {a b : B _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b) :
    (homotopyTransport p).map (SSet.HomotopyCategory.homMk e) =
      homotopyQCatHomMk (X := homotopyTransportFiber p a)
        (Y := homotopyTransportFiber p b) (edgeTransport p e)

lemma homotopyTransport_map_isTransport {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [CocartesianFibration p] {a b : B _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b)
    {F : vertexFiber p a ⟶ vertexFiber p b} (hF : IsEdgeTransport p e F) :
    (homotopyTransport p).map (SSet.HomotopyCategory.homMk e) =
      homotopyQCatHomMk (X := homotopyTransportFiber p a)
        (Y := homotopyTransportFiber p b) F

lemma homotopyTransport_unique {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [CocartesianFibration p] (T : hoFunctor.obj B ⥤ HomotopyQCat.{u})
    (hobj : ∀ b : B _⦋0⦌, T.obj (SSet.HomotopyCategory.mk b) = homotopyTransportFiber p b)
    (hmap : ∀ {a b : B _⦋0⦌}
      (e : SSet.Truncated.Edge (X := (truncation 2).obj B) a b),
      T.map (SSet.HomotopyCategory.homMk e) = eqToHom (hobj a) ≫
        homotopyQCatHomMk (X := homotopyTransportFiber p a)
          (Y := homotopyTransportFiber p b) (edgeTransport p e) ≫ eqToHom (hobj b).symm) :
    T = homotopyTransport p

lemma IsCartesianEdge.op {X B : SSet.{u}} {p : X ⟶ B} {e : X _⦋1⦌}
    (he : IsCartesianEdge p e) :
    IsCocartesianEdge (SSet.opFunctor.map p) (SSet.opObjEquiv.symm e)

lemma isCartesianEdge_of_isCocartesianEdge_op {X B : SSet.{u}} (p : X ⟶ B)
    (e : X _⦋1⦌)
    (he : IsCocartesianEdge (SSet.opFunctor.map p) (SSet.opObjEquiv.symm e)) :
    IsCartesianEdge p e

lemma isCartesianEdge_iff_isCocartesianEdge_op {X B : SSet.{u}} (p : X ⟶ B)
    (e : X _⦋1⦌) : IsCartesianEdge p e ↔
      IsCocartesianEdge (SSet.opFunctor.map p) (SSet.opObjEquiv.symm e)

lemma isCartesianEdge_triangle_longEdge {X B : SSet.{u}} [Quasicategory B]
    (t : (Δ[2] : SSet.{u}) ⟶ X) (p : X ⟶ B) [InnerFibration p]
    (hfirst : IsCartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t)))
    (hsecond : IsCartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t))) :
    IsCartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ t))

def quasicategoryCore (X : SSet.{u}) : X.Subcomplex

lemma quasicategoryCore_edge {X : SSet.{u}} (s : (quasicategoryCore X : SSet.{u}) _⦋1⦌) :
    IsInvertibleEdge (edgeOfSimplex s.val)

def quasicategoryCoreLift {A X : SSet.{u}} (f : A ⟶ X)
    (hf : ∀ s : A _⦋1⦌, IsInvertibleEdge (edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s))) :
    A ⟶ (quasicategoryCore X : SSet.{u})

lemma quasicategoryCoreLift_ι {A X : SSet.{u}} (f : A ⟶ X)
    (hf : ∀ s : A _⦋1⦌, IsInvertibleEdge (edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s))) :
    quasicategoryCoreLift f hf ≫ (quasicategoryCore X).ι = f

def quasicategoryCoreMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    (quasicategoryCore X : SSet.{u}) ⟶ (quasicategoryCore Y : SSet.{u})

lemma quasicategoryCoreMap_ι {X Y : SSet.{u}} (f : X ⟶ Y) :
    quasicategoryCoreMap f ≫ (quasicategoryCore Y).ι = (quasicategoryCore X).ι ≫ f

def quasicategoryCoreFunctor : SSet.{u} ⥤ SSet.{u}

lemma isInvertibleEdge_degenerate {X : SSet.{u}} (v : X _⦋0⦌) :
    IsInvertibleEdge (edgeOfSimplex (X.σ 0 v))

lemma quasicategoryCore_vertex {X : SSet.{u}} (v : X _⦋0⦌) :
    v ∈ (quasicategoryCore X).obj (Opposite.op ⦋0⦌)

lemma intervalEndomorphism_cases (f : ⦋1⦌ ⟶ ⦋1⦌) :
    f = SimplexCategory.const _ _ 0 ∨ f = 𝟙 _ ∨ f = SimplexCategory.const _ _ 1

lemma quasicategoryCore_mem_edge_iff {X : SSet.{u}} (s : X _⦋1⦌) :
    s ∈ (quasicategoryCore X).obj (Opposite.op ⦋1⦌) ↔ IsInvertibleEdge (edgeOfSimplex s)

lemma isInvertibleEdge_map_const {X : SSet.{u}} {n : SimplexCategory}
    (s : X.obj (Opposite.op n)) (v : Fin (n.len + 1)) :
    IsInvertibleEdge (edgeOfSimplex (X.map (SimplexCategory.const ⦋1⦌ n v).op s))

lemma triangleEdge_cases (f : ⦋1⦌ ⟶ ⦋2⦌) :
    (∃ i : Fin 3, f = SimplexCategory.δ i) ∨
      ∃ v : Fin 3, f = SimplexCategory.const _ _ v

lemma quasicategoryCore_mem_triangle_iff {X : SSet.{u}} (s : X _⦋2⦌) :
    s ∈ (quasicategoryCore X).obj (Opposite.op ⦋2⦌) ↔
      ∀ i : Fin 3, IsInvertibleEdge (edgeOfSimplex (X.δ i s))

lemma edge_mem_horn_of_three_le (n : ℕ) (i : Fin (n + 4))
    (e : (Δ[n + 3] : SSet.{u}) _⦋1⦌) :
    e ∈ (horn (n + 3) i).obj (Opposite.op ⦋1⦌)

lemma isInvertibleEdge_triangle_missing {X : SSet.{u}} (s : X _⦋2⦌) (k : Fin 3)
    (h : ∀ i : Fin 3, i ≠ k → IsInvertibleEdge (edgeOfSimplex (X.δ i s))) :
    IsInvertibleEdge (edgeOfSimplex (X.δ k s))

lemma quasicategoryCore_horn_filler_mem {X : SSet.{u}} (n : ℕ) (i : Fin (n + 3))
    (a : (horn (n + 2) i : SSet.{u}) ⟶ (quasicategoryCore X : SSet.{u}))
    (F : (Δ[n + 2] : SSet.{u}) ⟶ X)
    (hF : (horn (n + 2) i).ι ≫ F = a ≫ (quasicategoryCore X).ι) :
    SSet.yonedaEquiv F ∈ (quasicategoryCore X).obj (Opposite.op ⦋n + 2⦌)

instance quasicategoryCore_kanComplex (X : SSet.{u}) [Quasicategory X] :
    KanComplex (quasicategoryCore X : SSet.{u})

lemma isInvertibleEdge_pair {X Y : SSet.{u}} (e : X _⦋1⦌) (f : Y _⦋1⦌)
    (he : IsInvertibleEdge (edgeOfSimplex e)) (hf : IsInvertibleEdge (edgeOfSimplex f)) :
    IsInvertibleEdge (edgeOfSimplex (X := X ⊗ Y) (e, f))

def quasicategoryCoreProduct (X Y : SSet.{u}) :
    (quasicategoryCore X : SSet.{u}) ⊗ (quasicategoryCore Y : SSet.{u}) ⟶
      (quasicategoryCore (X ⊗ Y) : SSet.{u})

def quasicategoryCoreUnit : (𝟙_ SSet.{u}) ⟶ (quasicategoryCore (𝟙_ SSet.{u}) : SSet.{u})

instance quasicategoryCoreFunctor_laxMonoidal : quasicategoryCoreFunctor.{u}.LaxMonoidal

def quasicategoryCoreUnitHomEquiv (X : SSet.{u}) :
    ((𝟙_ SSet.{u}) ⟶ X) ≃ ((𝟙_ SSet.{u}) ⟶ (quasicategoryCore X : SSet.{u}))

lemma quasicategoryCoreUnitHomEquiv_eq (X : SSet.{u}) (f : (𝟙_ SSet.{u}) ⟶ X) :
    quasicategoryCoreUnitHomEquiv X f = quasicategoryCoreUnit ≫ quasicategoryCoreMap f

structure QuasicategoryObject where
  obj : SSet.{u}
  isQuasicategory : Quasicategory obj

instance quasicategoryObject_category : Category.{u} QuasicategoryObject.{u}

instance quasicategoryObject_enrichedCategory : EnrichedCategory SSet.{u} QuasicategoryObject.{u}

instance quasicategoryObject_simplicialCategory : SimplicialCategory.{u} QuasicategoryObject.{u}

def QCat : Type (u + 1)

instance qCat_category : Category.{u} QCat.{u}

noncomputable instance qCat_simplicialCategory : SimplicialCategory QCat.{u}

lemma qCat_sHom (X Y : QCat.{u}) :
    SimplicialCategory.sHom X Y =
      (quasicategoryCore ((ihom X.obj).obj Y.obj) : SSet.{u})

instance qCat_sHom_kanComplex (X Y : QCat.{u}) :
    KanComplex (SimplicialCategory.sHom X Y)

noncomputable def CatInfinity : SSet.{u + 1}

instance catInfinity_quasicategory : Quasicategory CatInfinity.{u}

noncomputable def CatInfinityFunctor (C : SSet.{u + 1}) : SSet.{u + 1}

instance catInfinityFunctor_quasicategory (C : SSet.{u + 1}) :
    Quasicategory (CatInfinityFunctor C)

structure KanObject where
  obj : SSet.{u}
  isKanComplex : KanComplex obj

instance kanObject_category : Category.{u} KanObject.{u}

instance kanObject_enrichedCategory : EnrichedCategory SSet.{u} KanObject.{u}

instance kanObject_simplicialCategory : SimplicialCategory KanObject.{u}

instance kanObject_sHom_kanComplex (X Y : KanObject.{u}) :
    KanComplex (SimplicialCategory.sHom X Y)

def SpaceInfinity : SSet.{u + 1}

instance spaceInfinity_quasicategory : Quasicategory SpaceInfinity.{u}

def SpaceInfinityFunctor (C : SSet.{u + 1}) : SSet.{u + 1}

instance spaceInfinityFunctor_quasicategory (C : SSet.{u + 1}) :
    Quasicategory (SpaceInfinityFunctor C)

noncomputable def spaceInfinityVertex (K : KanObject.{u}) : SpaceInfinity.{u} _⦋0⦌

def pointKanObject : KanObject.{u}

noncomputable def pointSpaceVertex : SpaceInfinity.{u} _⦋0⦌

noncomputable def PointedSpaceInfinity : SSet.{u + 1}

noncomputable def pointedSpaceProjection : PointedSpaceInfinity.{u} ⟶ SpaceInfinity.{u}

instance pointedSpaceProjection_leftFibration : LeftFibration pointedSpaceProjection.{u}

instance pointedSpaceInfinity_quasicategory : Quasicategory PointedSpaceInfinity.{u}

noncomputable def leftUnstraightening {C : SSet.{u + 1}} (F : C ⟶ SpaceInfinity.{u}) :
    SSet.{u + 1}

noncomputable def leftUnstraighteningProjection {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) : leftUnstraightening F ⟶ C

instance leftUnstraighteningProjection_leftFibration {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) : LeftFibration (leftUnstraighteningProjection F)

instance leftUnstraightening_quasicategory {C : SSet.{u + 1}} [Quasicategory C]
    (F : C ⟶ SpaceInfinity.{u}) : Quasicategory (leftUnstraightening F)

noncomputable def leftUnstraighteningMap {C D : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (G : D ⟶ SpaceInfinity.{u})
    (α : C ⟶ D) (h : α ≫ G = F) : leftUnstraightening F ⟶ leftUnstraightening G

lemma leftUnstraighteningMap_pointed {C D : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (G : D ⟶ SpaceInfinity.{u})
    (α : C ⟶ D) (h : α ≫ G = F) :
    leftUnstraighteningMap F G α h ≫ pullback.fst pointedSpaceProjection G =
      pullback.fst pointedSpaceProjection F

lemma leftUnstraighteningMap_projection {C D : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (G : D ⟶ SpaceInfinity.{u})
    (α : C ⟶ D) (h : α ≫ G = F) :
    leftUnstraighteningMap F G α h ≫ leftUnstraighteningProjection G =
      leftUnstraighteningProjection F ≫ α

lemma leftUnstraighteningMap_id {C : SSet.{u + 1}} (F : C ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningMap F F (𝟙 C) (Category.id_comp F) = 𝟙 (leftUnstraightening F)

lemma leftUnstraighteningMap_comp {C D E : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (G : D ⟶ SpaceInfinity.{u})
    (H : E ⟶ SpaceInfinity.{u}) (α : C ⟶ D) (β : D ⟶ E)
    (hα : α ≫ G = F) (hβ : β ≫ H = G) :
    leftUnstraighteningMap F H (α ≫ β) (by rw [Category.assoc, hβ, hα]) =
      leftUnstraighteningMap F G α hα ≫ leftUnstraighteningMap G H β hβ

lemma leftUnstraighteningMap_isPullback {C D : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (G : D ⟶ SpaceInfinity.{u})
    (α : C ⟶ D) (h : α ≫ G = F) :
    IsPullback (leftUnstraighteningMap F G α h) (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection G) α

noncomputable def vertexFiberPullbackIso {E B C : SSet.{u}} (p : E ⟶ B) (f : C ⟶ B)
    (b : C _⦋0⦌) : vertexFiber (pullback.snd p f) b ≅
      vertexFiber p (f.app (Opposite.op ⦋0⦌) b)

lemma vertexFiberPullbackIso_hom_ι {E B C : SSet.{u}} (p : E ⟶ B) (f : C ⟶ B)
    (b : C _⦋0⦌) : (vertexFiberPullbackIso p f b).hom ≫
      vertexFiberι p (f.app (Opposite.op ⦋0⦌) b) =
        vertexFiberι (pullback.snd p f) b ≫ pullback.fst p f

noncomputable def leftUnstraighteningFiberIso {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (c : C _⦋0⦌) :
    vertexFiber (leftUnstraighteningProjection F) c ≅
      vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) c)

noncomputable def coherentNerveVertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (K : C) : (SimplicialNerve C) _⦋0⦌

lemma thickeningZero_eId_epi (o : SimplicialThickening (ULift.{u} (Fin 1))) :
    Epi (eId SSet o)

def coherentNerveObject {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋0⦌) : C

lemma coherentNerveObject_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (K : C) : coherentNerveObject (coherentNerveVertex K) = K

lemma coherentNerveVertex_object {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋0⦌) : coherentNerveVertex (coherentNerveObject s) = s

noncomputable def coherentNerveVertexEquiv (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    C ≃ (SimplicialNerve C) _⦋0⦌

lemma spaceInfinityVertex_eq_coherent (K : KanObject.{u}) :
    spaceInfinityVertex K = coherentNerveVertex K

def spaceInfinityObject (s : SpaceInfinity.{u} _⦋0⦌) : KanObject.{u}

noncomputable def spaceInfinityVertexEquiv : KanObject.{u} ≃ SpaceInfinity.{u} _⦋0⦌

lemma unitHom_app_constant {X : SSet.{u}} (f : (𝟙_ SSet.{u}) ⟶ X) (n : ℕ) :
    f.app (Opposite.op ⦋n⦌) PUnit.unit = PinchedHom.constant (SSet.unitHomEquiv X f) n

lemma simplicialHom_vertex_comp {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
    SimplicialCategory.homEquiv' A D (f ≫ g) =
      (SimplicialCategory.sHomComp A B D).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' A B f, SimplicialCategory.homEquiv' B D g)

lemma simplicialHom_constant_comp {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (n : ℕ) :
    (SimplicialCategory.sHomComp A B D).app (Opposite.op ⦋n⦌)
      (PinchedHom.constant (SimplicialCategory.homEquiv' A B f) n,
        PinchedHom.constant (SimplicialCategory.homEquiv' B D g) n) =
      PinchedHom.constant (SimplicialCategory.homEquiv' A D (f ≫ g)) n

noncomputable def orderDiagramEnrichedHom {J : Type u} [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (F : J ⥤ C)
    (i j : SimplicialThickening J) :
    SimplicialCategory.sHom i j ⟶ SimplicialCategory.sHom (F.obj i.as) (F.obj j.as)

noncomputable def enrichedFunctorOfOrderDiagram {J : Type u} [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (F : J ⥤ C) :
    EnrichedFunctor SSet (SimplicialThickening J) C

lemma enrichedFunctorOfOrderDiagram_precomp {J K : Type u} [LinearOrder J] [LinearOrder K]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (α : J →o K) (F : K ⥤ C) :
    (SimplicialThickening.functor α).comp SSet (enrichedFunctorOfOrderDiagram F) =
      enrichedFunctorOfOrderDiagram (α.toFunctor ⋙ F)

noncomputable def nerveToCoherent (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    nerve C ⟶ SimplicialNerve C

lemma nerveToCoherent_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C] (X : C) :
    (nerveToCoherent C).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X) =
      coherentNerveVertex X

noncomputable def coherentNerveEdge {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (f : X ⟶ Y) :
    (SimplicialNerve C).Edge (coherentNerveVertex X) (coherentNerveVertex Y)

lemma coherentNerveEdge_edge {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (f : X ⟶ Y) :
    (coherentNerveEdge f).edge =
      (nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)

lemma coherentNerveEdge_id {C : Type v} [Category.{u} C] [SimplicialCategory C] (X : C) :
    coherentNerveEdge (𝟙 X) = SSet.Edge.id (coherentNerveVertex X)

noncomputable def coherentNerveCompStruct {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SSet.Edge.CompStruct (coherentNerveEdge f) (coherentNerveEdge g)
      (coherentNerveEdge (f ≫ g))

lemma joinPoints_inl_face :
    joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 0 0).hom =
      stdSimplex.δ 1

lemma joinPoints_inr_face :
    joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 0 0).hom =
      stdSimplex.δ 0

lemma joinPoints_face_inl :
    stdSimplex.δ 1 ≫ (joinStdSimplexIso.{u} 0 0).inv = joinInl Δ[0] Δ[0]

lemma joinPoints_face_inr :
    stdSimplex.δ 0 ≫ (joinStdSimplexIso.{u} 0 0).inv = joinInr Δ[0] Δ[0]

def cosliceFiberVertexToEdge {X : SSet.{u}} {x y : X _⦋0⦌}
    (s : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋0⦌) :
    X.Edge x y

def edgeToCosliceFiberVertex {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋0⦌

def cosliceFiberVertexEquiv {X : SSet.{u}} (x y : X _⦋0⦌) :
    (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋0⦌ ≃
      X.Edge x y

def coherentOnePath : SimplicialThickening.Path
    (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) (ULift.up (1 : Fin 2))

noncomputable def coherentNerveArrowData {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (s : (SimplicialNerve C) _⦋1⦌) : Σ X Y : C, X ⟶ Y

lemma coherentNerveArrowData_of_arrow {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} (f : X ⟶ Y) :
    coherentNerveArrowData
      ((nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)) = ⟨X, Y, f⟩

instance coherentOnePath_subsingleton (i j : ULift.{u} (Fin 2)) :
    Subsingleton (SimplicialThickening.Path i j)

lemma coherentOneHom_simplex_constant (i j : ULift.{u} (Fin 2)) (n : ℕ)
    (P : (nerve (SimplicialThickening.Path i j)) _⦋n⦌) :
    P = PinchedHom.constant (ComposableArrows.mk₀ (P.obj 0)) n

lemma coherentOne_eId_epi (o : SimplicialThickening (ULift.{u} (Fin 2))) :
    Epi (eId SSet o)

lemma coherentOneHom_map_constant {X : SSet.{u}} (i j : ULift.{u} (Fin 2))
    (f : nerve (SimplicialThickening.Path i j) ⟶ X) (n : ℕ)
    (P : (nerve (SimplicialThickening.Path i j)) _⦋n⦌) :
    f.app (Opposite.op ⦋n⦌) P =
      PinchedHom.constant (f.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (P.obj 0))) n

lemma coherentNerveArrowData_reconstruct {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (s : (SimplicialNerve C) _⦋1⦌) :
    (nerveToCoherent C).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ (coherentNerveArrowData s).2.2) = s

noncomputable def coherentNerveArrowDataEquiv (C : Type v) [Category.{u} C]
    [SimplicialCategory C] : (SimplicialNerve C) _⦋1⦌ ≃ (Σ X Y : C, X ⟶ Y)

lemma coherentNerveEdge_source {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (e : (SimplicialNerve C).Edge (coherentNerveVertex X)
      (coherentNerveVertex Y)) : (coherentNerveArrowData e.edge).1 = X

lemma coherentNerveEdge_target {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (e : (SimplicialNerve C).Edge (coherentNerveVertex X)
      (coherentNerveVertex Y)) : (coherentNerveArrowData e.edge).2.1 = Y

noncomputable def coherentNerveEdgeToHom {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C}
    (e : (SimplicialNerve C).Edge (coherentNerveVertex X) (coherentNerveVertex Y)) : X ⟶ Y

lemma coherentNerveEdgeToHom_edge {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (f : X ⟶ Y) : coherentNerveEdgeToHom (coherentNerveEdge f) = f

lemma arrowData_transport {C : Type v} [Category.{u} C] {X Y : C}
    (a : Σ A B : C, A ⟶ B) (hX : a.1 = X) (hY : a.2.1 = Y) :
    (⟨X, Y, eqToHom hX.symm ≫ a.2.2 ≫ eqToHom hY⟩ : Σ A B : C, A ⟶ B) = a

lemma coherentNerveEdge_hom {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (e : (SimplicialNerve C).Edge (coherentNerveVertex X)
      (coherentNerveVertex Y)) : coherentNerveEdge (coherentNerveEdgeToHom e) = e

noncomputable def coherentNerveEdgeEquiv {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) :
    (SimplicialNerve C).Edge (coherentNerveVertex X) (coherentNerveVertex Y) ≃ (X ⟶ Y)

noncomputable def pointedSpaceFiberVertexEquiv (K : KanObject.{u}) :
    (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌ ≃ K.obj _⦋0⦌

noncomputable def pointedSpaceFiberVertexEquivAt (s : SpaceInfinity.{u} _⦋0⦌) :
    (vertexFiber pointedSpaceProjection s) _⦋0⦌ ≃ (spaceInfinityObject s).obj _⦋0⦌

noncomputable def leftUnstraighteningFiberVertexEquiv {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (c : C _⦋0⦌) :
    (vertexFiber (leftUnstraighteningProjection F) c) _⦋0⦌ ≃
      (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) c)).obj _⦋0⦌

lemma kanComplex_of_leftHornFillers (X : SSet.{u})
    (hf : ∀ (n : ℕ) (i : Fin (n + 2)), i < n + 1 →
      ∀ σ : (horn (n + 1) i : SSet.{u}) ⟶ X,
        ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (horn (n + 1) i).ι ≫ F = σ) : KanComplex X

lemma vertexFiber_kanComplex_of_leftFibration {E B : SSet.{u}} (p : E ⟶ B)
    [LeftFibration p] (b : B _⦋0⦌) : KanComplex (vertexFiber p b)

instance pointedSpaceFiber_kanComplex (s : SpaceInfinity.{u} _⦋0⦌) :
    KanComplex (vertexFiber pointedSpaceProjection s)

instance leftUnstraighteningFiber_kanComplex {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (c : C _⦋0⦌) :
    KanComplex (vertexFiber (leftUnstraighteningProjection F) c)

def leftPointStdSimplexIso (n : ℕ) :
    join (Δ[0] : SSet.{u}) Δ[n] ≅ Δ[n + 1]

lemma joinStdSimplexIso_leftPoint_inl (n : ℕ) :
    joinInl (Δ[0] : SSet.{u}) Δ[n] ≫ (leftPointStdSimplexIso n).hom =
      stdSimplex.map (SimplexCategory.const _ _ 0)

lemma joinStdSimplexIso_leftPoint_inr (n : ℕ) :
    joinInr (Δ[0] : SSet.{u}) Δ[n] ≫ (leftPointStdSimplexIso n).hom =
      stdSimplex.δ 0

def cosliceFiberSimplex {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (s : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌) :
    X _⦋n + 1⦌

lemma leftPointStdSimplexIso_first_inv (n : ℕ) :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
      (leftPointStdSimplexIso.{u} n).inv = joinInl Δ[0] Δ[n]

lemma leftPointStdSimplexIso_face_inv (n : ℕ) :
    stdSimplex.δ 0 ≫ (leftPointStdSimplexIso.{u} n).inv = joinInr Δ[0] Δ[n]

lemma cosliceFiberSimplex_source {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (s : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (cosliceFiberSimplex n s) = x

lemma cosliceFiberSimplex_target {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (s : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌) :
    X.δ 0 (cosliceFiberSimplex n s) = PinchedHom.constant y n

def cosliceFiberSimplexInverse {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (t : {s : X _⦋n + 1⦌ //
      X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s = x ∧
        X.δ 0 s = PinchedHom.constant y n}) :
    (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌

def cosliceFiberSimplexEquiv {X : SSet.{u}} (x y : X _⦋0⦌) (n : ℕ) :
    (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌ ≃
      {s : X _⦋n + 1⦌ // X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s = x ∧
        X.δ 0 s = PinchedHom.constant y n}

lemma leftPointStdSimplexIso_inv_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    stdSimplex.map (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)) ≫
      (leftPointStdSimplexIso.{u} n).inv = (leftPointStdSimplexIso m).inv ≫
        joinMap (𝟙 Δ[0]) (stdSimplex.map α)

lemma cosliceFiberSimplex_naturality {X : SSet.{u}} {x y : X _⦋0⦌}
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌) :
    cosliceFiberSimplex m
      ((vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y).map α.op s) =
        X.map (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)).op
          (cosliceFiberSimplex n s)

lemma pinchedFront_rev (n : ℕ) :
    SimplexCategory.rev.map (PinchedHom.front n) = SimplexCategory.δ 0

lemma pinchedLastVertex_rev (n : ℕ) :
    SimplexCategory.rev.map (PinchedHom.lastVertex n) =
      SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0

lemma pinchedExtend_rev {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    SimplexCategory.rev.map (PinchedHom.extend (SimplexCategory.rev.map α)) =
      SimplexCategory.mkHom (prependOrderHom α.toOrderHom)

lemma pinchedConstant_opObjEquiv {X : SSet.{u}} (x : X _⦋0⦌) (n : ℕ) :
    SSet.opObjEquiv (PinchedHom.constant (X := X.op) (SSet.opObjEquiv.symm x) n) =
      PinchedHom.constant x n

def pinchedLeftSimplexVal {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (s : (pinchedHomLeft x y) _⦋n⦌) : X _⦋n + 1⦌

lemma pinchedLeftSimplexVal_source {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (s : (pinchedHomLeft x y) _⦋n⦌) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (pinchedLeftSimplexVal n s) = x

lemma pinchedLeftSimplexVal_target {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (s : (pinchedHomLeft x y) _⦋n⦌) :
    X.δ 0 (pinchedLeftSimplexVal n s) = PinchedHom.constant y n

def pinchedLeftSimplexInverse {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (t : {s : X _⦋n + 1⦌ //
      X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s = x ∧
        X.δ 0 s = PinchedHom.constant y n}) : (pinchedHomLeft x y) _⦋n⦌

lemma pinchedLeftSimplexVal_injective {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ) :
    Function.Injective (pinchedLeftSimplexVal (x := x) (y := y) n)

def pinchedLeftSimplexEquiv {X : SSet.{u}} (x y : X _⦋0⦌) (n : ℕ) :
    (pinchedHomLeft x y) _⦋n⦌ ≃
      {s : X _⦋n + 1⦌ // X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s = x ∧
        X.δ 0 s = PinchedHom.constant y n}

lemma pinchedLeftSimplexVal_naturality {X : SSet.{u}} {x y : X _⦋0⦌}
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (s : (pinchedHomLeft x y) _⦋n⦌) :
    pinchedLeftSimplexVal m ((pinchedHomLeft x y).map α.op s) =
      X.map (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)).op
        (pinchedLeftSimplexVal n s)

lemma cosliceFiberSimplex_equiv_symm {X : SSet.{u}} {x y : X _⦋0⦌} (n : ℕ)
    (t : {s : X _⦋n + 1⦌ //
      X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s = x ∧
        X.δ 0 s = PinchedHom.constant y n}) :
    cosliceFiberSimplex n ((cosliceFiberSimplexEquiv x y n).symm t) = t.val

def pinchedLeftCosliceFiberIso {X : SSet.{u}} (x y : X _⦋0⦌) :
    pinchedHomLeft x y ≅ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y

noncomputable def pointedSpaceFiberPinchedIso (s : SpaceInfinity.{u} _⦋0⦌) :
    vertexFiber pointedSpaceProjection s ≅ pinchedHomLeft pointSpaceVertex s

noncomputable def leftUnstraighteningFiberPinchedIso {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (c : C _⦋0⦌) :
    vertexFiber (leftUnstraighteningProjection F) c ≅
      pinchedHomLeft pointSpaceVertex (F.app (Opposite.op ⦋0⦌) c)

noncomputable def pathBeforeLast {n : ℕ} {i : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : Finset (Fin (n + 1))

lemma pathBeforeLast_nonempty {n : ℕ} {i : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : (pathBeforeLast P).Nonempty

noncomputable def pathLastMaximum {n : ℕ} {i : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : Fin (n + 1)

lemma pathLastMaximum_mem {n : ℕ} {i : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : ULift.up (pathLastMaximum P).castSucc ∈ P.I

lemma le_pathLastMaximum {n : ℕ} {i : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) (j : Fin (n + 1))
    (hj : ULift.up j.castSucc ∈ P.I) : j ≤ pathLastMaximum P

lemma pathLastMaximum_mono {n : ℕ} {i : Fin (n + 1)}
    {P Q : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))} (h : P.I ⊆ Q.I) :
    pathLastMaximum P ≤ pathLastMaximum Q

lemma pathLastMaximum_comp {n : ℕ} {i j : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc))
    (Q : Path (ULift.up j.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :
    pathLastMaximum (@CategoryStruct.comp (SimplicialThickening (ULift.{u} (Fin (n + 2))))
      _ ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ P Q) =
        pathLastMaximum Q

noncomputable def pathLastMaximumFunctor {n : ℕ} (i : Fin (n + 1)) :
    Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) ⥤ ULift.{u} (Fin (n + 1))

noncomputable def pathLastMaximumMap {n : ℕ} (i : Fin (n + 1)) :
    nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) ⟶ (Δ[n] : SSet.{u})

def pathLastReindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) {i : Fin (m + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (m + 2)))
      (ULift.up (Fin.last (m + 1)))) :
    Path (ULift.up (α.toOrderHom i).castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))

lemma pathLastMaximum_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) {i : Fin (m + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (m + 2)))
      (ULift.up (Fin.last (m + 1)))) :
    pathLastMaximum (pathLastReindex α P) = α.toOrderHom (pathLastMaximum P)

lemma pathLastMaximumMap_apply {n : ℕ} (i : Fin (n + 1))
    {d : SimplexCategoryᵒᵖ}
    (F : (nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))).obj d) (k : Fin (d.unop.len + 1)) :
    ((pathLastMaximumMap i).app d F).down.toOrderHom k = pathLastMaximum (F.obj k)

lemma simplicialHom_id_comp_app {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) (d : SimplexCategoryᵒᵖ) (a : (SimplicialCategory.sHom X Y).obj d) :
    (eComp SSet X X Y).app d ((eId SSet X).app d PUnit.unit, a) = a

lemma simplicialHom_comp_id_app {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) (d : SimplexCategoryᵒᵖ) (a : (SimplicialCategory.sHom X Y).obj d) :
    (eComp SSet X Y Y).app d (a, (eId SSet Y).app d PUnit.unit) = a

lemma thickeningPath_end_eq_id {J : Type u} [LinearOrder J] (a : J) (P : Path a a) :
    P = 𝟙 (⟨a⟩ : SimplicialThickening J)

lemma thickeningHom_comp_end_right {J : Type u} [LinearOrder J]
    (i j : SimplicialThickening J) (d : SimplexCategoryᵒᵖ)
    (P : (SimplicialCategory.sHom i j).obj d) (Q : (SimplicialCategory.sHom j j).obj d) :
    (eComp SSet i j j).app d (P, Q) = P

lemma pathLastMaximumMap_comp {n : ℕ} (i j : Fin (n + 1)) (d : SimplexCategoryᵒᵖ)
    (P : (nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up j.castSucc))).obj d)
    (Q : (nerve (Path (ULift.up j.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))).obj d) :
    (pathLastMaximumMap i).app d
      ((eComp SSet (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩).app d (P, Q)) =
          (pathLastMaximumMap j).app d Q

def coherentHomComparisonObj {C : Type v} (X Y : C) {n : ℕ} (i : Fin (n + 2)) : C

lemma coherentHomComparisonObj_last {C : Type v} (X Y : C) (n : ℕ) :
    coherentHomComparisonObj X Y (Fin.last (n + 1)) = Y

lemma coherentHomComparisonObj_cast {C : Type v} (X Y : C) {n : ℕ} (i : Fin (n + 1)) :
    coherentHomComparisonObj X Y i.castSucc = X

def coherentHomEmptyMap {n : ℕ} (j : Fin (n + 1)) (Z : SSet.{u}) :
    nerve (Path (ULift.up (Fin.last (n + 1)) : ULift.{u} (Fin (n + 2)))
      (ULift.up j.castSucc)) ⟶ Z

noncomputable def coherentHomComparisonHom {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) (i j : Fin (n + 2)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ⟶
      SimplicialCategory.sHom (coherentHomComparisonObj X Y i)
        (coherentHomComparisonObj X Y j)

lemma simplicialHom_id_transport {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {A X : C} (h : A = X) (d : SimplexCategoryᵒᵖ) :
    (eId SSet A).app d PUnit.unit =
      (eqToHom (congrArg₂ SimplicialCategory.sHom h h).symm).app d
        ((eId SSet X).app d PUnit.unit)

lemma simplicialHom_comp_transport {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {A B D X Y Z : C} (hA : A = X) (hB : B = Y) (hD : D = Z)
    (d : SimplexCategoryᵒᵖ) (a : (SimplicialCategory.sHom X Y).obj d)
    (b : (SimplicialCategory.sHom Y Z).obj d) :
    (eComp SSet A B D).app d
      ((eqToHom (congrArg₂ SimplicialCategory.sHom hA hB).symm).app d a,
       (eqToHom (congrArg₂ SimplicialCategory.sHom hB hD).symm).app d b) =
      (eqToHom (congrArg₂ SimplicialCategory.sHom hA hD).symm).app d
        ((eComp SSet X Y Z).app d (a, b))

noncomputable def coherentHomComparisonSimplex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) : (SimplicialNerve C) _⦋n + 1⦌

lemma coherentHomComparisonHom_cast_cast {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) (i j : Fin (n + 1)) :
    coherentHomComparisonHom σ i.castSucc j.castSucc ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_cast X Y j)) =
      toUnit _ ≫ eId SSet X

lemma coherentNerveConstant_obj {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X : C) (n : ℕ) (i : SimplicialThickening (ULift.{u} (Fin (n + 1)))) :
    (PinchedHom.constant (coherentNerveVertex X) n).obj i = X

lemma coherentNerveConstant_map {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X : C) (n : ℕ) (i j : SimplicialThickening (ULift.{u} (Fin (n + 1)))) :
    (PinchedHom.constant (coherentNerveVertex X) n).map i j = toUnit _ ≫ eId SSet X

lemma coherentHomComparisonSimplex_source {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    (SimplicialNerve C).map (PinchedHom.front n).op (coherentHomComparisonSimplex σ) =
      PinchedHom.constant (coherentNerveVertex X) n

lemma coherentHomComparisonSimplex_target {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    (SimplicialNerve C).map (PinchedHom.lastVertex n).op (coherentHomComparisonSimplex σ) =
      coherentNerveVertex Y

noncomputable def coherentHomComparisonPinchedSimplex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n

def pathLastReindexFunctor {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    Path (ULift.up i.castSucc : ULift.{u} (Fin (m + 2)))
      (ULift.up (Fin.last (m + 1))) ⥤
      Path (ULift.up (α.toOrderHom i).castSucc : ULift.{u} (Fin (n + 2)))
        (ULift.up (Fin.last (n + 1)))

lemma pathLastMaximumMap_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 1)) :
    nerveMap (pathLastReindexFunctor.{u} α i) ≫ pathLastMaximumMap (α.toOrderHom i) =
      pathLastMaximumMap i ≫ stdSimplex.map α

lemma coherentHomComparisonHom_cast_last {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) (i : Fin (n + 1)) :
    coherentHomComparisonHom σ i.castSucc (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_last X Y n)) =
      pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm σ

lemma coherentHomComparisonHom_last_last {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    coherentHomComparisonHom σ (Fin.last (n + 1)) (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentHomComparisonObj_last X Y n) (coherentHomComparisonObj_last X Y n)) =
      toUnit _ ≫ eId SSet Y

lemma coherentHomComparisonObj_extend {C : Type v} (X Y : C) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 2)) :
    coherentHomComparisonObj X Y (PinchedHom.extendOrderHom α.toOrderHom i) =
      coherentHomComparisonObj X Y i

lemma coherentHomComparisonHom_transport {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y A B : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) {i j i' j' : Fin (n + 2)}
    (hi : i = i') (hj : j = j')
    (hA : coherentHomComparisonObj X Y i' = A)
    (hB : coherentHomComparisonObj X Y j' = B) :
    coherentHomComparisonHom σ i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg (coherentHomComparisonObj X Y) hi).trans hA)
      ((congrArg (coherentHomComparisonObj X Y) hj).trans hB)) =
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩) hi hj) ≫
        coherentHomComparisonHom σ i' j' ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom hA hB)

lemma thickeningHom_transport_I {J : Type u} [LinearOrder J]
    {i j i' j' : SimplicialThickening J} (hi : i = i') (hj : j = j')
    {d : SimplexCategoryᵒᵖ} (P : (SimplicialCategory.sHom i j).obj d)
    (k : Fin (d.unop.len + 1)) :
    (((eqToHom (congrArg₂ SimplicialCategory.sHom hi hj)).app d P).obj k).I =
      (P.obj k).I

lemma thickeningExtend_map_cast_last {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (SimplicialThickening.functor (PinchedHom.extend α).toOrderHom.uliftMap).map
      (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (m + 2))))
      ⟨ULift.up (Fin.last (m + 1))⟩ ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
        (PinchedHom.extendOrderHom_castSucc α.toOrderHom i)
        (PinchedHom.extendOrderHom_last α.toOrderHom)) =
      nerveMap (pathLastReindexFunctor α i)

def thickeningExtendHom {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (i j : Fin (m + 2)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (m + 2)))) ⟨ULift.up j⟩ ⟶
      SimplicialCategory.sHom
        (⟨ULift.up (PinchedHom.extendOrderHom α.toOrderHom i)⟩ :
          SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up (PinchedHom.extendOrderHom α.toOrderHom j)⟩

lemma coherentHomComparisonHom_naturality_of_normalized
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y A B : C} {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) (i j : Fin (m + 2))
    (hA : coherentHomComparisonObj X Y i = A) (hB : coherentHomComparisonObj X Y j = B)
    (hA' : coherentHomComparisonObj X Y (PinchedHom.extendOrderHom α.toOrderHom i) = A)
    (hB' : coherentHomComparisonObj X Y (PinchedHom.extendOrderHom α.toOrderHom j) = B)
    (h : thickeningExtendHom α i j ≫ coherentHomComparisonHom σ
      (PinchedHom.extendOrderHom α.toOrderHom i)
      (PinchedHom.extendOrderHom α.toOrderHom j) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom hA' hB') =
          coherentHomComparisonHom ((SimplicialCategory.sHom X Y).map α.op σ) i j ≫
            eqToHom (congrArg₂ SimplicialCategory.sHom hA hB)) :
    (thickeningExtendHom α i j ≫ coherentHomComparisonHom σ
      (PinchedHom.extendOrderHom α.toOrderHom i)
      (PinchedHom.extendOrderHom α.toOrderHom j)) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (coherentHomComparisonObj_extend X Y α i)
          (coherentHomComparisonObj_extend X Y α j)) =
            coherentHomComparisonHom ((SimplicialCategory.sHom X Y).map α.op σ) i j

lemma coherentHomComparisonSimplex_naturality {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    (SimplicialNerve C).map (PinchedHom.extend α).op (coherentHomComparisonSimplex σ) =
      coherentHomComparisonSimplex ((SimplicialCategory.sHom X Y).map α.op σ)

noncomputable def coherentHomComparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⟶
      pinchedHom (coherentNerveVertex X) (coherentNerveVertex Y)

lemma coherentHomComparison_app_val {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    ((coherentHomComparison X Y).app (Opposite.op ⦋n⦌) (ULift.up σ)).val =
      coherentHomComparisonSimplex σ

def maximumFlagPath {n : ℕ} (j : Fin (n + 1)) :
    Path (ULift.up (0 : Fin (n + 1)).castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))

lemma pathLastMaximum_maximumFlagPath {n : ℕ} (j : Fin (n + 1)) :
    pathLastMaximum (maximumFlagPath.{u} j) = j

def maximumFlagFunctor (n : ℕ) :
    ULift.{u} (Fin (n + 1)) ⥤
      Path (ULift.up (0 : Fin (n + 1)).castSucc : ULift.{u} (Fin (n + 2)))
        (ULift.up (Fin.last (n + 1)))

def maximumFlagMap (n : ℕ) : (Δ[n] : SSet.{u}) ⟶
    nerve (Path (ULift.up (0 : Fin (n + 1)).castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))

lemma maximumFlagMap_comp_pathLastMaximumMap (n : ℕ) :
    maximumFlagMap.{u} n ≫ pathLastMaximumMap (0 : Fin (n + 1)) = 𝟙 Δ[n]

lemma enrichedFunctor_map_heq {A : Type w} {C : Type v}
    [EnrichedCategory SSet.{u} A] [EnrichedCategory SSet.{u} C]
    {F G : EnrichedFunctor SSet.{u} A C} (h : F = G) (i j : A) :
    HEq (F.map i j) (G.map i j)

lemma coherentHomComparisonSimplex_injective {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} (n : ℕ) :
    Function.Injective (coherentHomComparisonSimplex (X := X) (Y := Y) (n := n))

instance coherentHomComparison_mono {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) : Mono (coherentHomComparison X Y)

def uliftSimplexHomDown {X : SSet.{u}} {n : ℕ}
    (f : (Δ[n] : SSet.{max u v}) ⟶ SSet.uliftFunctor.{v, u}.obj X) :
    (Δ[n] : SSet.{u}) ⟶ X

lemma uliftSimplexHomDown_face {X : SSet.{u}} {n : ℕ}
    (f : (Δ[n + 1] : SSet.{max u v}) ⟶ SSet.uliftFunctor.{v, u}.obj X)
    (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ uliftSimplexHomDown f =
      uliftSimplexHomDown (stdSimplex.δ j ≫ f)

instance kanComplex_uliftFunctor_obj (X : SSet.{u}) [KanComplex X] :
    KanComplex (SSet.uliftFunctor.{v, u}.obj X)

structure CoherentResolutionFlag (n d : ℕ) where
  start : Fin (n + 1)
  sets : Fin (d + 1) → Finset (Fin (n + 1))
  monotone_sets : Monotone sets
  first : sets 0 = {start}
  lower : ∀ i k, k ∈ sets i → start ≤ k

lemma CoherentResolutionFlag.ext {n d : ℕ} {F G : CoherentResolutionFlag n d}
    (hstart : F.start = G.start) (hsets : F.sets = G.sets) : F = G

lemma CoherentResolutionFlag.start_mem {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) : F.start ∈ F.sets i

lemma CoherentResolutionFlag.sets_nonempty {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) : (F.sets i).Nonempty

def CoherentResolutionFlag.maxAt {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) : Fin (n + 1)

lemma CoherentResolutionFlag.maxAt_mem {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) : F.maxAt i ∈ F.sets i

lemma CoherentResolutionFlag.le_maxAt {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) (k : Fin (n + 1)) (hk : k ∈ F.sets i) : k ≤ F.maxAt i

lemma CoherentResolutionFlag.maxAt_monotone {n d : ℕ} (F : CoherentResolutionFlag n d) :
    Monotone F.maxAt

lemma CoherentResolutionFlag.maxAt_zero {n d : ℕ} (F : CoherentResolutionFlag n d) :
    F.maxAt 0 = F.start

def CoherentResolutionFlag.pullback {n d e : ℕ} (F : CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) : CoherentResolutionFlag n e

lemma CoherentResolutionFlag.maxAt_pullback {n d e : ℕ} (F : CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (i : Fin (e + 1)) :
    (F.pullback α).maxAt i = F.maxAt (α i)

lemma CoherentResolutionFlag.pullback_id {n d : ℕ} (F : CoherentResolutionFlag n d) :
    F.pullback (OrderHom.id (α := Fin (d + 1))) = F

lemma CoherentResolutionFlag.pullback_comp {n d e f : ℕ} (F : CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (β : Fin (f + 1) →o Fin (e + 1)) :
    (F.pullback α).pullback β = F.pullback (α.comp β)

def coherentResolutionSimplex (n : ℕ) : SSet.{u}

def coherentResolutionProjection (n : ℕ) : coherentResolutionSimplex.{u} n ⟶ Δ[n]

def CoherentResolutionFlag.interval {n d : ℕ}
    (f : Fin (d + 1) →o Fin (n + 1)) : CoherentResolutionFlag n d

lemma CoherentResolutionFlag.maxAt_interval {n d : ℕ}
    (f : Fin (d + 1) →o Fin (n + 1)) (i : Fin (d + 1)) :
    (CoherentResolutionFlag.interval f).maxAt i = f i

lemma CoherentResolutionFlag.interval_pullback {n d e : ℕ}
    (f : Fin (d + 1) →o Fin (n + 1)) (α : Fin (e + 1) →o Fin (d + 1)) :
    (CoherentResolutionFlag.interval f).pullback α =
      CoherentResolutionFlag.interval (f.comp α)

def coherentResolutionSection (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ coherentResolutionSimplex n

lemma coherentResolutionSection_projection (n : ℕ) :
    coherentResolutionSection.{u} n ≫ coherentResolutionProjection n = 𝟙 Δ[n]

def CoherentResolutionFlag.intervalHull {n d : ℕ} (F : CoherentResolutionFlag n d) :
    CoherentResolutionFlag n d

lemma CoherentResolutionFlag.intervalHull_start {n d : ℕ} (F : CoherentResolutionFlag n d) :
    F.intervalHull.start = F.start

lemma CoherentResolutionFlag.sets_subset_intervalHull {n d : ℕ}
    (F : CoherentResolutionFlag n d) (i : Fin (d + 1)) :
    F.sets i ⊆ F.intervalHull.sets i

lemma CoherentResolutionFlag.maxAt_intervalHull {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) : F.intervalHull.maxAt i = F.maxAt i

lemma CoherentResolutionFlag.intervalHull_pullback {n d e : ℕ}
    (F : CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    F.intervalHull.pullback α = (F.pullback α).intervalHull

lemma CoherentResolutionFlag.intervalHull_idempotent {n d : ℕ}
    (F : CoherentResolutionFlag n d) : F.intervalHull.intervalHull = F.intervalHull

def CoherentResolutionFlag.deform {n d : ℕ} (F : CoherentResolutionFlag n d)
    (t : Fin (d + 1) →o Fin 2) : CoherentResolutionFlag n d

lemma CoherentResolutionFlag.maxAt_deform {n d : ℕ} (F : CoherentResolutionFlag n d)
    (t : Fin (d + 1) →o Fin 2) (i : Fin (d + 1)) :
    (F.deform t).maxAt i = F.maxAt i

lemma CoherentResolutionFlag.deform_pullback {n d e : ℕ} (F : CoherentResolutionFlag n d)
    (t : Fin (d + 1) →o Fin 2) (α : Fin (e + 1) →o Fin (d + 1)) :
    (F.deform t).pullback α = (F.pullback α).deform (t.comp α)

lemma CoherentResolutionFlag.deform_zero {n d : ℕ} (F : CoherentResolutionFlag n d) :
    F.deform (OrderHom.const _ 0) = F

lemma CoherentResolutionFlag.deform_one {n d : ℕ} (F : CoherentResolutionFlag n d) :
    F.deform (OrderHom.const _ 1) = F.intervalHull

lemma CoherentResolutionFlag.deform_intervalHull {n d : ℕ} (F : CoherentResolutionFlag n d)
    (t : Fin (d + 1) →o Fin 2) : F.intervalHull.deform t = F.intervalHull

lemma CoherentResolutionFlag.deform_vertex {n : ℕ} (F : CoherentResolutionFlag n 0)
    (t : Fin 1 →o Fin 2) : F.deform t = F

def coherentResolutionDeformation (n : ℕ) :
    coherentResolutionSimplex.{u} n ⊗ Δ[1] ⟶ coherentResolutionSimplex n

lemma coherentResolutionDeformation_projection (n : ℕ) :
    coherentResolutionDeformation.{u} n ≫ coherentResolutionProjection n =
      fst _ _ ≫ coherentResolutionProjection n

lemma coherentResolutionDeformation_vertex (n : ℕ)
    (x : (coherentResolutionSimplex.{u} n ⊗ Δ[1]) _⦋0⦌) :
    (coherentResolutionDeformation n).app _ x = x.1

def coherentResolutionHomotopy (n : ℕ) :
    SSet.Homotopy (𝟙 (coherentResolutionSimplex.{u} n))
      (coherentResolutionProjection n ≫ coherentResolutionSection n)

lemma CoherentResolutionFlag.intervalHull_interval {n d : ℕ}
    (f : Fin (d + 1) →o Fin (n + 1)) :
    (CoherentResolutionFlag.interval f).intervalHull = CoherentResolutionFlag.interval f

lemma CoherentResolutionFlag.deform_interval {n d : ℕ}
    (f : Fin (d + 1) →o Fin (n + 1)) (t : Fin (d + 1) →o Fin 2) :
    (CoherentResolutionFlag.interval f).deform t = CoherentResolutionFlag.interval f

lemma CoherentResolutionFlag.intervalHull_vertex {n : ℕ} (F : CoherentResolutionFlag n 0) :
    F.intervalHull = F

lemma coherentResolutionSection_vertex_surjective (n : ℕ) :
    Function.Surjective ((coherentResolutionSection.{u} n).app (Opposite.op ⦋0⦌))

lemma coherentResolutionDeformation_section (n : ℕ) :
    (coherentResolutionSection.{u} n ▷ Δ[1]) ≫ coherentResolutionDeformation n =
      fst _ _ ≫ coherentResolutionSection n

lemma coherentResolutionHomotopy_vertex_isInvertible (n : ℕ)
    (F : coherentResolutionSimplex.{u} n _⦋0⦌) :
    IsInvertibleEdge
      (simplicialHomotopyVertexEdge (coherentResolutionHomotopy n) F).toTruncated

lemma coherentResolutionProjection_isPrecompositionEquivalence (n : ℕ) :
    IsPrecompositionEquivalence (coherentResolutionProjection.{u} n)

lemma coherentResolutionSection_isPrecompositionEquivalence (n : ℕ) :
    IsPrecompositionEquivalence (coherentResolutionSection.{u} n)

def CoherentResolutionFlag.pushforward {n m d : ℕ} (F : CoherentResolutionFlag n d)
    (β : Fin (n + 1) →o Fin (m + 1)) : CoherentResolutionFlag m d

lemma CoherentResolutionFlag.maxAt_pushforward {n m d : ℕ}
    (F : CoherentResolutionFlag n d) (β : Fin (n + 1) →o Fin (m + 1))
    (i : Fin (d + 1)) : (F.pushforward β).maxAt i = β (F.maxAt i)

lemma CoherentResolutionFlag.pushforward_pullback {n m d e : ℕ}
    (F : CoherentResolutionFlag n d) (β : Fin (n + 1) →o Fin (m + 1))
    (α : Fin (e + 1) →o Fin (d + 1)) :
    (F.pushforward β).pullback α = (F.pullback α).pushforward β

lemma CoherentResolutionFlag.pushforward_id {n d : ℕ} (F : CoherentResolutionFlag n d) :
    F.pushforward (OrderHom.id (α := Fin (n + 1))) = F

lemma CoherentResolutionFlag.pushforward_comp {n m l d : ℕ}
    (F : CoherentResolutionFlag n d) (β : Fin (n + 1) →o Fin (m + 1))
    (γ : Fin (m + 1) →o Fin (l + 1)) :
    (F.pushforward β).pushforward γ = F.pushforward (γ.comp β)

def coherentResolutionMap {n m : ℕ} (β : Fin (n + 1) →o Fin (m + 1)) :
    coherentResolutionSimplex.{u} n ⟶ coherentResolutionSimplex m

lemma coherentResolutionMap_id (n : ℕ) :
    coherentResolutionMap.{u} (OrderHom.id (α := Fin (n + 1))) =
      𝟙 (coherentResolutionSimplex n)

lemma coherentResolutionMap_comp {n m l : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (γ : Fin (m + 1) →o Fin (l + 1)) :
    coherentResolutionMap.{u} β ≫ coherentResolutionMap γ =
      coherentResolutionMap (γ.comp β)

def coherentResolutionDiagram : SimplexCategory ⥤ SSet.{u}

def coherentResolutionProjectionNat : coherentResolutionDiagram.{u} ⟶ SSet.stdSimplex

noncomputable def coherentResolution : SSet.{u} ⥤ SSet.{u}

noncomputable def coherentResolutionRightAdjoint : SSet.{u} ⥤ SSet.{u}

noncomputable def coherentResolutionAdjunction :
    coherentResolution.{u} ⊣ coherentResolutionRightAdjoint

noncomputable def coherentResolutionStdIso :
    SSet.stdSimplex.{u} ⋙ coherentResolution ≅ coherentResolutionDiagram

instance coherentResolution_isLeftKanExtension :
    coherentResolution.{u}.IsLeftKanExtension
      (SSet.stdSimplex.{u}.leftKanExtensionUnit coherentResolutionDiagram.{u})

noncomputable def coherentResolutionProjectionAll : coherentResolution.{u} ⟶ 𝟭 SSet

lemma coherentResolutionProjectionAll_std (n : ℕ) :
    coherentResolutionStdIso.{u}.inv.app ⦋n⦌ ≫
      coherentResolutionProjectionAll.app Δ[n] = coherentResolutionProjection n

noncomputable def coherentResolutionHomEquiv (X Y : SSet.{u}) :
    (coherentResolution.obj X ⟶ Y) ≃ (X ⟶ coherentResolutionRightAdjoint.obj Y)

lemma coherentResolutionProjectionAll_std_isPrecompositionEquivalence (n : ℕ) :
    IsPrecompositionEquivalence (coherentResolutionProjectionAll.{u}.app Δ[n])

lemma coherentResolutionHomEquiv_app {X Y : SSet.{u}}
    (f : coherentResolution.obj X ⟶ Y) {d : SimplexCategoryᵒᵖ} (x : X.obj d) :
    (coherentResolutionHomEquiv X Y f).app d x =
      ULift.up (coherentResolutionStdIso.inv.app d.unop ≫
        coherentResolution.map (SSet.yonedaEquiv.symm x) ≫ f)

def CoherentResolutionFlag.toPath {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) :
    Path (ULift.up F.start.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))

lemma CoherentResolutionFlag.mem_toPath {n d : ℕ} (F : CoherentResolutionFlag n d)
    (i : Fin (d + 1)) (j : Fin (n + 1)) :
    ULift.up j.castSucc ∈ (F.toPath.{u} i).I ↔ j ∈ F.sets i

lemma CoherentResolutionFlag.pathLastMaximum_toPath {n d : ℕ}
    (F : CoherentResolutionFlag n d) (i : Fin (d + 1)) :
    pathLastMaximum (F.toPath.{u} i) = F.maxAt i

def CoherentResolutionFlag.pathFlag {n d : ℕ} (F : CoherentResolutionFlag n d) :
    Fin (d + 1) ⥤ Path (ULift.up F.start.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))

def CoherentResolutionFlag.prefixPath {n d e : ℕ} (F : CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (i : Fin (e + 1)) :
    Path (ULift.up F.start.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (F.maxAt (α 0)).castSucc)

def CoherentResolutionFlag.prefixFlag {n d e : ℕ} (F : CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) :
    Fin (e + 1) ⥤ Path (ULift.up F.start.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (F.maxAt (α 0)).castSucc)

lemma CoherentResolutionFlag.prefixPath_comp_pullback {n d e : ℕ}
    (F : CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1))
    (i : Fin (e + 1)) :
    @CategoryStruct.comp (SimplicialThickening (ULift.{u} (Fin (n + 2)))) _
      ⟨ULift.up F.start.castSucc⟩ ⟨ULift.up (F.maxAt (α 0)).castSucc⟩
      ⟨ULift.up (Fin.last (n + 1))⟩
      (F.prefixPath α i) ((F.pullback α).toPath i) = F.toPath (α i)

lemma CoherentResolutionFlag.prefixFlag_comp_pullback {n d e : ℕ}
    (F : CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    (F.prefixFlag.{u} α).prod' ((F.pullback α).pathFlag) ⋙
      compFunctor (⟨ULift.up F.start.castSucc⟩ :
        SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up (F.maxAt (α 0)).castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ =
      α.toFunctor ⋙ F.pathFlag

lemma coherentPinched_sourceObj {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (i : Fin (n + 1)) :
    τ.val.obj (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) = X

lemma coherentPinched_targetObj {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n) :
    τ.val.obj (⟨ULift.up (Fin.last (n + 1))⟩ :
      SimplicialThickening (ULift.{u} (Fin (n + 2)))) = Y

noncomputable def coherentPinchedHom {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (i : Fin (n + 1)) :
    nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) ⟶ SimplicialCategory.sHom X Y

noncomputable def coherentPinchedEvaluate {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n d : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (F : CoherentResolutionFlag n d) : (SimplicialCategory.sHom X Y) _⦋d⦌

lemma coherentPinchedHom_comparison {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (i : Fin (n + 1)) :
    coherentPinchedHom (coherentHomComparisonPinchedSimplex σ) i =
      pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm σ

lemma coherentPinchedEvaluate_comparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n d : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) (F : CoherentResolutionFlag n d) :
    coherentPinchedEvaluate (coherentHomComparisonPinchedSimplex σ) F =
      (SimplicialCategory.sHom X Y).map
        (SimplexCategory.mkHom ⟨F.maxAt, F.maxAt_monotone⟩).op σ

lemma enrichedFunctor_map_eqToHom_of_eq {A : Type w} {C : Type v}
    [EnrichedCategory SSet.{u} A] [EnrichedCategory SSet.{u} C]
    {F G : EnrichedFunctor SSet.{u} A C} (h : F = G) (i j : A) :
    F.map i j ≫ eqToHom (congrArg₂ (fun a b : C ↦ (a ⟶[SSet.{u}] b))
      (congrArg (fun H ↦ H.obj i) h) (congrArg (fun H ↦ H.obj j) h)) = G.map i j

lemma coherentPinched_sourceMap {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (i j : Fin (n + 1)) :
    (SimplicialThickening.functor (PinchedHom.front n).toOrderHom.uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
      τ.val.map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentPinched_sourceObj τ i) (coherentPinched_sourceObj τ j)) =
      toUnit _ ≫ eId SSet X

def CoherentResolutionFlag.prefixSmallPath {n d e : ℕ} (F : CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (i : Fin (e + 1)) :
    Path (ULift.up F.start : ULift.{u} (Fin (n + 1))) (ULift.up (F.maxAt (α 0)))

def CoherentResolutionFlag.prefixSmallFlag {n d e : ℕ} (F : CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) :
    Fin (e + 1) ⥤ Path (ULift.up F.start : ULift.{u} (Fin (n + 1)))
      (ULift.up (F.maxAt (α 0)))

lemma CoherentResolutionFlag.front_prefixSmallPath {n d e : ℕ}
    (F : CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1))
    (i : Fin (e + 1)) :
    (SimplicialThickening.functorMap (PinchedHom.front n).toOrderHom.uliftMap
      (⟨ULift.up F.start⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
      ⟨ULift.up (F.maxAt (α 0))⟩).obj (F.prefixSmallPath α i) = F.prefixPath α i

lemma CoherentResolutionFlag.front_prefixSmallFlag {n d e : ℕ}
    (F : CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    ((SimplicialThickening.functor (PinchedHom.front n).toOrderHom.uliftMap).map
      (⟨ULift.up F.start⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
      ⟨ULift.up (F.maxAt (α 0))⟩).app (Opposite.op ⦋e⦌) (F.prefixSmallFlag α) =
        F.prefixFlag α

lemma coherentPinched_prefixFlag {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n d e : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (F : CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    (τ.val.map ⟨ULift.up F.start.castSucc⟩ ⟨ULift.up (F.maxAt (α 0)).castSucc⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentPinched_sourceObj τ F.start)
        (coherentPinched_sourceObj τ (F.maxAt (α 0))))).app (Opposite.op ⦋e⦌)
      (F.prefixFlag α) = (eId SSet X).app (Opposite.op ⦋e⦌) PUnit.unit

lemma enrichedFunctor_map_comp_normalized {A : Type w} {C : Type v}
    [EnrichedCategory SSet.{u} A] [Category.{u} C] [SimplicialCategory C]
    (T : EnrichedFunctor SSet.{u} A C) (i j k : A) {X Y Z : C}
    (hi : T.obj i = X) (hj : T.obj j = Y) (hk : T.obj k = Z)
    (d : SimplexCategoryᵒᵖ) (P : (i ⟶[SSet] j).obj d) (Q : (j ⟶[SSet] k).obj d) :
    (T.map i k ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hi hk)).app d
      ((eComp SSet i j k).app d (P, Q)) =
      (eComp SSet X Y Z).app d
        ((T.map i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hi hj)).app d P,
         (T.map j k ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hj hk)).app d Q)

lemma coherentPinchedEvaluate_pullback {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n d e : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (F : CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    coherentPinchedEvaluate τ (F.pullback α) =
      (SimplicialCategory.sHom X Y).map (SimplexCategory.mkHom α).op
        (coherentPinchedEvaluate τ F)

noncomputable def coherentPinchedFlagMap {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n) :
    coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y

lemma coherentPinchedFlagMap_comparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    coherentPinchedFlagMap (coherentHomComparisonPinchedSimplex σ) =
      coherentResolutionProjection n ≫ SSet.yonedaEquiv.symm σ

lemma pathBeforeLast_mono {n : ℕ} {i : Fin (n + 1)}
    {P Q : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))} (h : P.I ⊆ Q.I) :
    pathBeforeLast P ⊆ pathBeforeLast Q

noncomputable def pathFlagResolution {n d : ℕ} {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : CoherentResolutionFlag n d

lemma pathFlagResolution_maxAt {n d : ℕ} {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) (k : Fin (d + 1)) :
    (pathFlagResolution P).maxAt k = pathLastMaximum (P.obj k)

lemma pathFlagResolution_pullback {n d e : ℕ} {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) (α : Fin (e + 1) →o Fin (d + 1)) :
    (pathFlagResolution P).pullback α = pathFlagResolution (α.toFunctor ⋙ P)

noncomputable def pathResolutionMap {n : ℕ} (i : Fin (n + 1)) :
    nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) ⟶ coherentResolutionSimplex n

lemma CoherentResolutionFlag.pathBeforeLast_toPath {n d : ℕ}
    (F : CoherentResolutionFlag n d) (k : Fin (d + 1)) :
    pathBeforeLast (F.toPath.{u} k) = F.sets k

lemma CoherentResolutionFlag.pathFlagResolution_pathFlag {n d : ℕ}
    (F : CoherentResolutionFlag n d) : pathFlagResolution F.pathFlag.{u} = F

lemma pathResolutionMap_projection {n : ℕ} (i : Fin (n + 1)) :
    pathResolutionMap.{u} i ≫ coherentResolutionProjection n = pathLastMaximumMap i

lemma pathFlagResolution_comp {n d : ℕ} {i j : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up j.castSucc))
    (Q : Fin (d + 1) ⥤ Path (ULift.up j.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :
    pathFlagResolution (P.prod' Q ⋙ compFunctor
      (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩) = pathFlagResolution Q

lemma pathResolutionMap_comp {n : ℕ} (i j : Fin (n + 1)) (d : SimplexCategoryᵒᵖ)
    (P : (nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up j.castSucc))).obj d)
    (Q : (nerve (Path (ULift.up j.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))).obj d) :
    (pathResolutionMap i).app d
      ((eComp SSet (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩).app d (P, Q)) =
          (pathResolutionMap j).app d Q

noncomputable def coherentFlagHom {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) (i j : Fin (n + 2)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ⟶
      SimplicialCategory.sHom (coherentHomComparisonObj X Y i)
        (coherentHomComparisonObj X Y j)

noncomputable def coherentFlagSimplex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) : (SimplicialNerve C) _⦋n + 1⦌

lemma coherentFlagHom_cast_cast {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) (i j : Fin (n + 1)) :
    coherentFlagHom φ i.castSucc j.castSucc ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_cast X Y j)) =
      toUnit _ ≫ eId SSet X

lemma coherentFlagSimplex_source {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) :
    (SimplicialNerve C).map (PinchedHom.front n).op (coherentFlagSimplex φ) =
      PinchedHom.constant (coherentNerveVertex X) n

lemma coherentFlagSimplex_target {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) :
    (SimplicialNerve C).map (PinchedHom.lastVertex n).op (coherentFlagSimplex φ) =
      coherentNerveVertex Y

noncomputable def coherentFlagPinchedSimplex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) :
    PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n

lemma coherentFlagHom_cast_last {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (φ : coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) (i : Fin (n + 1)) :
    coherentFlagHom φ i.castSucc (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_last X Y n)) =
      pathResolutionMap i ≫ φ

lemma coherentPinchedHom_flag {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (φ : coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y)
    (i : Fin (n + 1)) :
    coherentPinchedHom (coherentFlagPinchedSimplex φ) i = pathResolutionMap i ≫ φ

lemma coherentPinchedFlagMap_flag {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (φ : coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) :
    coherentPinchedFlagMap (coherentFlagPinchedSimplex φ) = φ

noncomputable def pathFlagPrepend {n d : ℕ} {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : CoherentResolutionFlag n (d + 1)

lemma pathFlagPrepend_pullback {n d : ℕ} {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :
    (pathFlagPrepend P).pullback (Fin.succOrderEmb (d + 1)).toOrderHom =
      pathFlagResolution P

lemma pathFlagPrepend_pathFlag {n d : ℕ} {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :
    (Fin.succOrderEmb (d + 1)).toOrderHom.toFunctor ⋙ (pathFlagPrepend P).pathFlag = P

lemma coherentPinchedEvaluate_pathFlagResolution {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n d : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :
    coherentPinchedEvaluate τ (pathFlagResolution P) =
      (coherentPinchedHom τ i).app (Opposite.op ⦋d⦌) P

lemma pathResolutionMap_coherentPinchedFlagMap {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (i : Fin (n + 1)) :
    pathResolutionMap i ≫ coherentPinchedFlagMap τ = coherentPinchedHom τ i

def pathFrontInverse {n : ℕ} {i j : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc)) :
    Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)

def pathFrontInverseFunctor {n : ℕ} (i j : Fin (n + 1)) :
    Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc) ⥤
      Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)

lemma pathFrontInverseFunctor_comp {n : ℕ} (i j : Fin (n + 1)) :
    pathFrontInverseFunctor.{u} i j ⋙ SimplicialThickening.functorMap
      (PinchedHom.front n).toOrderHom.uliftMap
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ =
      𝟭 (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc))

instance thickeningFront_map_epi {n : ℕ} (i j : Fin (n + 1)) :
    Epi ((SimplicialThickening.functor (PinchedHom.front n).toOrderHom.uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩)

lemma coherentPinched_sourceMap_full {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (i j : Fin (n + 1)) :
    τ.val.map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentPinched_sourceObj τ i) (coherentPinched_sourceObj τ j)) =
      toUnit _ ≫ eId SSet X

lemma simplicialHom_normalized_ext {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {D : SSet.{u}} {A B A' B' X Y : C} (hA : A = A') (hB : B = B')
    (ha : A' = X) (hb : B' = Y) (f : D ⟶ SimplicialCategory.sHom A B)
    (g : D ⟶ SimplicialCategory.sHom A' B')
    (h : f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom (hA.trans ha) (hB.trans hb)) =
      g ≫ eqToHom (congrArg₂ SimplicialCategory.sHom ha hb)) :
    f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) = g

lemma enrichedFunctor_thickening_self_map {J : Type u} [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening J) C) (a : J)
    {X : C} (ha : T.obj ⟨a⟩ = X) :
    T.map ⟨a⟩ ⟨a⟩ ≫ eqToHom (congrArg₂ SimplicialCategory.sHom ha ha) =
      toUnit _ ≫ eId SSet X

lemma coherentFlagHom_last_last {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (φ : coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) :
    coherentFlagHom φ (Fin.last (n + 1)) (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentHomComparisonObj_last X Y n) (coherentHomComparisonObj_last X Y n)) =
      toUnit _ ≫ eId SSet Y

lemma coherentFlagPinchedSimplex_flagMap {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n) :
    coherentFlagPinchedSimplex (coherentPinchedFlagMap τ) = τ

noncomputable def coherentPinchedFlagEquiv {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) (n : ℕ) :
    PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n ≃
      (coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y)

lemma enrichedFunctor_map_transport {A : Type w} {C : Type v}
    [EnrichedCategory SSet.{u} A] [Category.{u} C] [SimplicialCategory C]
    (T : EnrichedFunctor SSet.{u} A C) {i j i' j' : A} (hi : i = i') (hj : j = j')
    {X Y : C} (hX : T.obj i' = X) (hY : T.obj j' = Y) :
    T.map i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg T.obj hi).trans hX) ((congrArg T.obj hj).trans hY)) =
      eqToHom (congrArg₂ (fun a b : A ↦ (a ⟶[SSet.{u}] b)) hi hj) ≫
        T.map i' j' ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hX hY)

lemma coherentPinchedHom_pullback {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {m n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    coherentPinchedHom (τ.pullback α) i =
      nerveMap (pathLastReindexFunctor α i) ≫ coherentPinchedHom τ (α.toOrderHom i)

lemma CoherentResolutionFlag.toPath_reindex {m n d : ℕ}
    (F : CoherentResolutionFlag m d) (α : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (d + 1)) :
    pathLastReindex α (F.toPath.{u} k) = (F.pushforward α.toOrderHom).toPath k

lemma CoherentResolutionFlag.pathFlag_reindex {m n d : ℕ}
    (F : CoherentResolutionFlag m d) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    F.pathFlag.{u} ⋙ pathLastReindexFunctor α F.start =
      (F.pushforward α.toOrderHom).pathFlag

lemma coherentPinchedEvaluate_reindex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {m n d : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (α : ⦋m⦌ ⟶ ⦋n⦌) (F : CoherentResolutionFlag m d) :
    coherentPinchedEvaluate (τ.pullback α) F =
      coherentPinchedEvaluate τ (F.pushforward α.toOrderHom)

lemma coherentPinchedFlagMap_reindex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {m n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (α : ⦋m⦌ ⟶ ⦋n⦌) :
    coherentPinchedFlagMap (τ.pullback α) =
      coherentResolutionMap α.toOrderHom ≫ coherentPinchedFlagMap τ

noncomputable def coherentPinchedFlagIso {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) :
    pinchedHom (coherentNerveVertex X) (coherentNerveVertex Y) ≅
      (SSet.uliftFunctor.{v, u}).obj
        (coherentResolutionRightAdjoint.obj (SimplicialCategory.sHom X Y))

noncomputable def coherentResolutionComparison (X : SSet.{u}) :
    X ⟶ coherentResolutionRightAdjoint.obj X

lemma coherentResolutionComparison_app {X : SSet.{u}} {n : ℕ} (σ : X _⦋n⦌) :
    (coherentResolutionComparison X).app (Opposite.op ⦋n⦌) σ =
      ULift.up (coherentResolutionProjection n ≫ SSet.yonedaEquiv.symm σ)

lemma coherentHomComparison_flagIso {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    coherentHomComparison X Y ≫ (coherentPinchedFlagIso X Y).hom =
      (SSet.uliftFunctor.{v, u}).map
        (coherentResolutionComparison (SimplicialCategory.sHom X Y))

noncomputable def coherentResolutionComparisonNat : 𝟭 SSet.{u} ⟶ coherentResolutionRightAdjoint

instance coherentResolutionComparison_mono (X : SSet.{u}) :
    Mono (coherentResolutionComparison X)

def CoherentResolutionFlag.support {n d : ℕ} (F : CoherentResolutionFlag n d) :
    Finset (Fin (n + 1))

lemma CoherentResolutionFlag.sets_subset_support {n d : ℕ}
    (F : CoherentResolutionFlag n d) (k : Fin (d + 1)) : F.sets k ⊆ F.support

lemma CoherentResolutionFlag.support_pullback_subset {n d e : ℕ}
    (F : CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    (F.pullback α).support ⊆ F.support

lemma CoherentResolutionFlag.support_pushforward {n m d : ℕ}
    (F : CoherentResolutionFlag n d) (β : Fin (n + 1) →o Fin (m + 1)) :
    (F.pushforward β).support = F.support.image β

lemma CoherentResolutionFlag.pushforward_injective {n m d : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    Function.Injective (fun F : CoherentResolutionFlag n d ↦ F.pushforward β)

lemma coherentResolutionMap_mono {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    Mono (coherentResolutionMap.{u} β)

noncomputable def CoherentResolutionFlag.preimage {n m d : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β)
    (F : CoherentResolutionFlag m d)
    (hs : ∀ k ∈ F.support, k ∈ Set.range β) : CoherentResolutionFlag n d

lemma CoherentResolutionFlag.preimage_pushforward {n m d : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β)
    (F : CoherentResolutionFlag m d) (hs : ∀ k ∈ F.support, k ∈ Set.range β) :
    (CoherentResolutionFlag.preimage β hβ F hs).pushforward β = F

lemma CoherentResolutionFlag.mem_range_pushforward_iff {n m d : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β)
    (F : CoherentResolutionFlag m d) :
    F ∈ Set.range (fun G : CoherentResolutionFlag n d ↦ G.pushforward β) ↔
      ∀ k ∈ F.support, k ∈ Set.range β

def coherentResolutionBoundary (n : ℕ) : (coherentResolutionSimplex.{u} n).Subcomplex

lemma coherentResolutionBoundary_zero : coherentResolutionBoundary.{u} 0 = ⊥

lemma CoherentResolutionFlag.mem_range_face_iff {n d : ℕ}
    (j : Fin (n + 2)) (F : CoherentResolutionFlag (n + 1) d) :
    F ∈ Set.range (fun G : CoherentResolutionFlag n d ↦
      G.pushforward (SimplexCategory.δ j).toOrderHom) ↔ j ∉ F.support

lemma mem_range_coherentResolutionFace_iff {n d : ℕ} (j : Fin (n + 2))
    (F : (coherentResolutionSimplex.{u} (n + 1)) _⦋d⦌) :
    F ∈ (Subcomplex.range (coherentResolutionMap (SimplexCategory.δ j).toOrderHom)).obj
      (Opposite.op ⦋d⦌) ↔ j ∉ F.down.support

lemma coherentResolutionBoundary_eq_iSup_faces (n : ℕ) :
    coherentResolutionBoundary.{u} (n + 1) =
      ⨆ j : Fin (n + 2),
        Subcomplex.range (coherentResolutionMap (SimplexCategory.δ j).toOrderHom)

lemma stdSimplex_map_mono_of_injective {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    Mono (SSet.stdSimplex.{u}.map (SimplexCategory.mkHom β))

noncomputable def coherentResolutionImageProjection {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    (Subcomplex.range (coherentResolutionMap.{u} β)).toSSet ⟶
      (Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.mkHom β))).toSSet

lemma coherentResolutionImageProjection_toRange {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    Subcomplex.toRange (coherentResolutionMap.{u} β) ≫ coherentResolutionImageProjection β hβ =
      coherentResolutionProjection n ≫
        Subcomplex.toRange (SSet.stdSimplex.map (SimplexCategory.mkHom β))

lemma coherentResolutionImageProjection_ι {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    coherentResolutionImageProjection.{u} β hβ ≫
      (Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.mkHom β))).ι =
      (Subcomplex.range (coherentResolutionMap β)).ι ≫ coherentResolutionProjection m

lemma coherentResolutionImageProjection_isPrecompositionEquivalence {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    IsPrecompositionEquivalence (coherentResolutionImageProjection.{u} β hβ)

def coherentResolutionFace {n : ℕ} (T : Finset (Fin (n + 1))) :
    (coherentResolutionSimplex.{u} n).Subcomplex

lemma coherentResolutionFace_mono {n : ℕ} {T U : Finset (Fin (n + 1))} (h : T ⊆ U) :
    coherentResolutionFace.{u} T ≤ coherentResolutionFace U

lemma coherentResolutionFace_inter {n : ℕ} (T U : Finset (Fin (n + 1))) :
    coherentResolutionFace.{u} (T ∩ U) = coherentResolutionFace T ⊓ coherentResolutionFace U

lemma coherentResolutionFace_empty (n : ℕ) :
    coherentResolutionFace.{u} (∅ : Finset (Fin (n + 1))) = ⊥

lemma coherentResolutionFace_univ (n : ℕ) :
    coherentResolutionFace.{u} (Finset.univ : Finset (Fin (n + 1))) = ⊤

lemma range_coherentResolutionMap {n m : ℕ}
    (β : Fin (n + 1) →o Fin (m + 1)) (hβ : Function.Injective β) :
    Subcomplex.range (coherentResolutionMap.{u} β) =
      coherentResolutionFace (Finset.univ.image β)

lemma range_coherentResolutionMap_of_orderIso {n m : ℕ} (T : Finset (Fin (n + 1)))
    (e : Fin (m + 1) ≃o T) :
    Subcomplex.range (coherentResolutionMap.{u}
      ((OrderHom.Subtype.val (· ∈ T)).comp e.toOrderEmbedding.toOrderHom)) =
        coherentResolutionFace T

noncomputable def coherentResolutionFaceIso {n m : ℕ} (T : Finset (Fin (n + 1)))
    (e : Fin (m + 1) ≃o T) :
    coherentResolutionSimplex.{u} m ≅ (coherentResolutionFace T).toSSet

lemma subcomplex_eqToHom_ι {X : SSet.{u}} {A B : X.Subcomplex} (h : A = B) :
    eqToHom (congrArg (fun K : X.Subcomplex ↦ K.toSSet) h) ≫ B.ι = A.ι

lemma coherentResolutionFaceIso_hom_ι {n m : ℕ} (T : Finset (Fin (n + 1)))
    (e : Fin (m + 1) ≃o T) :
    (coherentResolutionFaceIso.{u} T e).hom ≫ (coherentResolutionFace T).ι =
      coherentResolutionMap ((OrderHom.Subtype.val (· ∈ T)).comp e.toOrderEmbedding.toOrderHom)

def coherentResolutionFaceProjection {n : ℕ} (T : Finset (Fin (n + 1))) :
    (coherentResolutionFace.{u} T).toSSet ⟶ (stdSimplex.face T).toSSet

lemma coherentResolutionFaceProjection_ι {n : ℕ} (T : Finset (Fin (n + 1))) :
    coherentResolutionFaceProjection.{u} T ≫ (stdSimplex.face T).ι =
      (coherentResolutionFace T).ι ≫ coherentResolutionProjection n

lemma coherentResolutionFaceProjection_faceIso {n m : ℕ} (T : Finset (Fin (n + 1)))
    (e : Fin (m + 1) ≃o T) :
    (coherentResolutionFaceIso.{u} T e).hom ≫ coherentResolutionFaceProjection T =
      coherentResolutionProjection m ≫
        (stdSimplex.isoOfRepresentableBy (stdSimplex.faceRepresentableBy T m e)).hom

lemma coherentResolutionFaceProjection_isPrecompositionEquivalence_of_orderIso {n m : ℕ}
    (T : Finset (Fin (n + 1))) (e : Fin (m + 1) ≃o T) :
    IsPrecompositionEquivalence (coherentResolutionFaceProjection.{u} T)

lemma coherentResolutionFaceProjection_isPrecompositionEquivalence_of_nonempty {n : ℕ}
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty) :
    IsPrecompositionEquivalence (coherentResolutionFaceProjection.{u} T)

lemma coherentResolutionFaceProjection_isPrecompositionEquivalence {n : ℕ}
    (T : Finset (Fin (n + 1))) :
    IsPrecompositionEquivalence (coherentResolutionFaceProjection.{u} T)

lemma coherentResolutionFaceProjection_naturality {n : ℕ}
    {T U : Finset (Fin (n + 1))} (h : T ⊆ U) :
    Subcomplex.homOfLE (coherentResolutionFace_mono.{u} h) ≫ coherentResolutionFaceProjection U =
      coherentResolutionFaceProjection T ≫
        Subcomplex.homOfLE ((stdSimplex.face_le_face_iff T U).mpr h)

def subcomplexRestriction {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : X.Subcomplex) (B : Y.Subcomplex) (h : A ≤ B.preimage f) : A.toSSet ⟶ B.toSSet

lemma subcomplexRestriction_ι {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : X.Subcomplex) (B : Y.Subcomplex) (h : A ≤ B.preimage f) :
    subcomplexRestriction f A B h ≫ B.ι = A.ι ≫ f

lemma subcomplexRestriction_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    {A A' : X.Subcomplex} {B B' : Y.Subcomplex}
    (h : A ≤ B.preimage f) (h' : A' ≤ B'.preimage f) (hA : A ≤ A') (hB : B ≤ B') :
    Subcomplex.homOfLE hA ≫ subcomplexRestriction f A' B' h' =
      subcomplexRestriction f A B h ≫ Subcomplex.homOfLE hB

lemma subcomplexRestriction_isPrecompositionEquivalence_congr {X Y : SSet.{u}} (f : X ⟶ Y)
    {A A' : X.Subcomplex} {B B' : Y.Subcomplex}
    (h : A ≤ B.preimage f) (h' : A' ≤ B'.preimage f) (hA : A = A') (hB : B = B') :
    IsPrecompositionEquivalence (subcomplexRestriction f A B h) ↔
      IsPrecompositionEquivalence (subcomplexRestriction f A' B' h')

lemma subcomplexRestriction_isPrecompositionEquivalence_sup {X Y : SSet.{u}} (f : X ⟶ Y)
    (A₁ A₂ : X.Subcomplex) (B₁ B₂ : Y.Subcomplex)
    (h₁ : A₁ ≤ B₁.preimage f) (h₂ : A₂ ≤ B₂.preimage f)
    (hI : A₁ ⊓ A₂ ≤ (B₁ ⊓ B₂).preimage f)
    (hU : A₁ ⊔ A₂ ≤ (B₁ ⊔ B₂).preimage f)
    (eI : IsPrecompositionEquivalence (subcomplexRestriction f _ _ hI))
    (e₁ : IsPrecompositionEquivalence (subcomplexRestriction f _ _ h₁))
    (e₂ : IsPrecompositionEquivalence (subcomplexRestriction f _ _ h₂)) :
    IsPrecompositionEquivalence (subcomplexRestriction f _ _ hU)

def coherentResolutionFaceUnion {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) :
    (coherentResolutionSimplex.{u} n).Subcomplex

def stdSimplexFaceUnion {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) :
    (Δ[n] : SSet.{u}).Subcomplex

lemma mem_coherentResolutionFaceUnion_iff {n : ℕ} (S : Finset (Finset (Fin (n + 1))))
    {d : SimplexCategoryᵒᵖ} (F : (coherentResolutionSimplex.{u} n).obj d) :
    F ∈ (coherentResolutionFaceUnion S).obj d ↔ ∃ T ∈ S, F.down.support ⊆ T

lemma coherentResolutionFaceUnion_empty (n : ℕ) :
    coherentResolutionFaceUnion.{u} (∅ : Finset (Finset (Fin (n + 1)))) = ⊥

lemma stdSimplexFaceUnion_empty (n : ℕ) :
    stdSimplexFaceUnion.{u} (∅ : Finset (Finset (Fin (n + 1)))) = ⊥

lemma coherentResolutionFaceUnion_insert {n : ℕ} (T : Finset (Fin (n + 1)))
    (S : Finset (Finset (Fin (n + 1)))) :
    coherentResolutionFaceUnion.{u} (insert T S) =
      coherentResolutionFace T ⊔ coherentResolutionFaceUnion S

lemma stdSimplexFaceUnion_insert {n : ℕ} (T : Finset (Fin (n + 1)))
    (S : Finset (Finset (Fin (n + 1)))) :
    stdSimplexFaceUnion.{u} (insert T S) = stdSimplex.face T ⊔ stdSimplexFaceUnion S

lemma subcomplex_finsetSup_inf {X : SSet.{u}} {ι : Type*} (S : Finset ι)
    (F : ι → X.Subcomplex) (A : X.Subcomplex) :
    S.sup F ⊓ A = S.sup (fun i ↦ F i ⊓ A)

lemma coherentResolutionFaceUnion_inf_face {n : ℕ} (S : Finset (Finset (Fin (n + 1))))
    (T : Finset (Fin (n + 1))) :
    coherentResolutionFaceUnion.{u} S ⊓ coherentResolutionFace T =
      coherentResolutionFaceUnion (S.image (fun U ↦ U ∩ T))

lemma stdSimplexFaceUnion_inf_face {n : ℕ} (S : Finset (Finset (Fin (n + 1))))
    (T : Finset (Fin (n + 1))) :
    stdSimplexFaceUnion.{u} S ⊓ stdSimplex.face T =
      stdSimplexFaceUnion (S.image (fun U ↦ U ∩ T))

lemma coherentResolutionFaceUnion_mapsTo {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) :
    coherentResolutionFaceUnion.{u} S ≤ (stdSimplexFaceUnion S).preimage
      (coherentResolutionProjection n)

def coherentResolutionFaceUnionProjection {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) :
    (coherentResolutionFaceUnion.{u} S).toSSet ⟶ (stdSimplexFaceUnion S).toSSet

lemma coherentResolutionFace_mapsTo {n : ℕ} (T : Finset (Fin (n + 1))) :
    coherentResolutionFace.{u} T ≤ (stdSimplex.face T).preimage (coherentResolutionProjection n)

lemma coherentResolutionFaceUnionProjection_empty_isPrecompositionEquivalence (n : ℕ) :
    IsPrecompositionEquivalence (coherentResolutionFaceUnionProjection.{u}
      (∅ : Finset (Finset (Fin (n + 1)))))

lemma coherentResolutionFaceUnionProjection_insert_isPrecompositionEquivalence {n : ℕ}
    (S : Finset (Finset (Fin (n + 1)))) (T : Finset (Fin (n + 1)))
    (eS : IsPrecompositionEquivalence (coherentResolutionFaceUnionProjection.{u} S))
    (eI : IsPrecompositionEquivalence
      (coherentResolutionFaceUnionProjection.{u} (S.image (fun U ↦ U ∩ T)))) :
    IsPrecompositionEquivalence (coherentResolutionFaceUnionProjection.{u} (insert T S))

lemma coherentResolutionFaceUnionProjection_isPrecompositionEquivalence {n : ℕ}
    (S : Finset (Finset (Fin (n + 1)))) :
    IsPrecompositionEquivalence (coherentResolutionFaceUnionProjection.{u} S)

def coherentResolutionBoundaryFaces (n : ℕ) : Finset (Finset (Fin (n + 1)))

lemma coherentResolutionFaceUnion_boundaryFaces (n : ℕ) :
    coherentResolutionFaceUnion.{u} (coherentResolutionBoundaryFaces n) =
      coherentResolutionBoundary n

lemma stdSimplexFaceUnion_boundaryFaces (n : ℕ) :
    stdSimplexFaceUnion.{u} (coherentResolutionBoundaryFaces n) = SSet.boundary n

lemma coherentResolutionBoundary_mapsTo (n : ℕ) :
    coherentResolutionBoundary.{u} n ≤ (SSet.boundary n).preimage
      (coherentResolutionProjection n)

def coherentResolutionBoundaryProjection (n : ℕ) :
    (coherentResolutionBoundary.{u} n).toSSet ⟶ (SSet.boundary n).toSSet

lemma coherentResolutionBoundaryProjection_ι (n : ℕ) :
    coherentResolutionBoundaryProjection.{u} n ≫ (SSet.boundary n).ι =
      (coherentResolutionBoundary n).ι ≫ coherentResolutionProjection n

lemma coherentResolutionBoundaryProjection_isPrecompositionEquivalence (n : ℕ) :
    IsPrecompositionEquivalence (coherentResolutionBoundaryProjection.{u} n)

instance coherentResolution_isLeftAdjoint : coherentResolution.{u}.IsLeftAdjoint

instance coherentResolution_preservesColimitsOfSize :
    PreservesColimitsOfSize.{v, w} coherentResolution.{u}

noncomputable def coherentResolutionFaceExtensionIso {n m : ℕ}
    (T : Finset (Fin (n + 1))) (e : Fin (m + 1) ≃o T) :
    coherentResolution.{u}.obj (stdSimplex.face T).toSSet ≅ (coherentResolutionFace T).toSSet

lemma coherentResolutionFaceExtensionIso_hom_ι {n m : ℕ}
    (T : Finset (Fin (n + 1))) (e : Fin (m + 1) ≃o T) :
    (coherentResolutionFaceExtensionIso.{u} T e).hom ≫ (coherentResolutionFace T).ι =
      coherentResolution.map (stdSimplex.face T).ι ≫ coherentResolutionStdIso.hom.app ⦋n⦌

lemma coherentResolutionStdIso_hom_projection (n : ℕ) :
    coherentResolutionStdIso.{u}.hom.app ⦋n⦌ ≫ coherentResolutionProjection n =
      coherentResolutionProjectionAll.app Δ[n]

lemma coherentResolutionFaceExtensionIso_projection {n m : ℕ}
    (T : Finset (Fin (n + 1))) (e : Fin (m + 1) ≃o T) :
    (coherentResolutionFaceExtensionIso.{u} T e).hom ≫ coherentResolutionFaceProjection T =
      coherentResolutionProjectionAll.app (stdSimplex.face T).toSSet

lemma coherentResolution_map_face_ι_mono {n m : ℕ}
    (T : Finset (Fin (n + 1))) (e : Fin (m + 1) ≃o T) :
    Mono (coherentResolution.{u}.map (stdSimplex.face T).ι)

lemma exists_coherentResolutionFaceExtensionIso {n : ℕ} (T : Finset (Fin (n + 1))) :
    ∃ e : coherentResolution.{u}.obj (stdSimplex.face T).toSSet ≅
      (coherentResolutionFace T).toSSet,
      e.hom ≫ (coherentResolutionFace T).ι =
        coherentResolution.map (stdSimplex.face T).ι ≫ coherentResolutionStdIso.hom.app ⦋n⦌

noncomputable def coherentResolutionFaceExtensionIsoAll {n : ℕ} (T : Finset (Fin (n + 1))) :
    coherentResolution.{u}.obj (stdSimplex.face T).toSSet ≅ (coherentResolutionFace T).toSSet

lemma coherentResolutionFaceExtensionIsoAll_hom_ι {n : ℕ} (T : Finset (Fin (n + 1))) :
    (coherentResolutionFaceExtensionIsoAll.{u} T).hom ≫ (coherentResolutionFace T).ι =
      coherentResolution.map (stdSimplex.face T).ι ≫ coherentResolutionStdIso.hom.app ⦋n⦌

lemma coherentResolutionFaceExtensionIsoAll_naturality {n : ℕ}
    {T U : Finset (Fin (n + 1))} (h : T ⊆ U) :
    coherentResolution.{u}.map (Subcomplex.homOfLE ((stdSimplex.face_le_face_iff T U).mpr h)) ≫
      (coherentResolutionFaceExtensionIsoAll U).hom =
      (coherentResolutionFaceExtensionIsoAll T).hom ≫
        Subcomplex.homOfLE (coherentResolutionFace_mono h)

lemma coherentResolutionFaceExtensionIsoAll_projection {n : ℕ} (T : Finset (Fin (n + 1))) :
    (coherentResolutionFaceExtensionIsoAll.{u} T).hom ≫ coherentResolutionFaceProjection T =
      coherentResolutionProjectionAll.app (stdSimplex.face T).toSSet

lemma coherentResolution_map_face_ι_mono_all {n : ℕ} (T : Finset (Fin (n + 1))) :
    Mono (coherentResolution.{u}.map (stdSimplex.face T).ι)

lemma exists_pushoutIsoOfCompatibleIsos
    {Z X Y P Z' X' Y' P' : SSet.{u}}
    {f : Z ⟶ X} {g : Z ⟶ Y} {i : X ⟶ P} {j : Y ⟶ P}
    {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {i' : X' ⟶ P'} {j' : Y' ⟶ P'}
    (h : IsPushout f g i j) (h' : IsPushout f' g' i' j')
    (eZ : Z ≅ Z') (eX : X ≅ X') (eY : Y ≅ Y')
    (hf : f ≫ eX.hom = eZ.hom ≫ f') (hg : g ≫ eY.hom = eZ.hom ≫ g') :
    ∃ e : P ≅ P', i ≫ e.hom = eX.hom ≫ i' ∧ j ≫ e.hom = eY.hom ≫ j'

def HasCoherentResolutionExtension {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex)
    (B : (coherentResolutionSimplex.{u} n).Subcomplex) : Prop

lemma hasCoherentResolutionExtension_face {n : ℕ} (T : Finset (Fin (n + 1))) :
    HasCoherentResolutionExtension (stdSimplex.face.{u} T) (coherentResolutionFace T)

lemma hasCoherentResolutionExtension_congr {n : ℕ}
    {A A' : (Δ[n] : SSet.{u}).Subcomplex}
    {B B' : (coherentResolutionSimplex.{u} n).Subcomplex} (hA : A = A') (hB : B = B') :
    HasCoherentResolutionExtension A B ↔ HasCoherentResolutionExtension A' B'

lemma coherentResolutionExtension_naturality {n : ℕ}
    {A A' : (Δ[n] : SSet.{u}).Subcomplex}
    {B B' : (coherentResolutionSimplex.{u} n).Subcomplex}
    (e : coherentResolution.obj A.toSSet ≅ B.toSSet)
    (e' : coherentResolution.obj A'.toSSet ≅ B'.toSSet)
    (he : e.hom ≫ B.ι = coherentResolution.map A.ι ≫ coherentResolutionStdIso.hom.app ⦋n⦌)
    (he' : e'.hom ≫ B'.ι = coherentResolution.map A'.ι ≫ coherentResolutionStdIso.hom.app ⦋n⦌)
    (hA : A ≤ A') (hB : B ≤ B') :
    coherentResolution.map (Subcomplex.homOfLE hA) ≫ e'.hom = e.hom ≫ Subcomplex.homOfLE hB

lemma hasCoherentResolutionExtension_sup {n : ℕ}
    (A₁ A₂ : (Δ[n] : SSet.{u}).Subcomplex)
    (B₁ B₂ : (coherentResolutionSimplex.{u} n).Subcomplex)
    (hI : HasCoherentResolutionExtension (A₁ ⊓ A₂) (B₁ ⊓ B₂))
    (h₁ : HasCoherentResolutionExtension A₁ B₁)
    (h₂ : HasCoherentResolutionExtension A₂ B₂) :
    HasCoherentResolutionExtension (A₁ ⊔ A₂) (B₁ ⊔ B₂)

lemma hasCoherentResolutionExtension_faceUnion_empty (n : ℕ) :
    HasCoherentResolutionExtension
      (stdSimplexFaceUnion.{u} (∅ : Finset (Finset (Fin (n + 1)))))
      (coherentResolutionFaceUnion (∅ : Finset (Finset (Fin (n + 1)))))

lemma hasCoherentResolutionExtension_faceUnion_insert {n : ℕ}
    (S : Finset (Finset (Fin (n + 1)))) (T : Finset (Fin (n + 1)))
    (eS : HasCoherentResolutionExtension (stdSimplexFaceUnion.{u} S) (coherentResolutionFaceUnion S))
    (eI : HasCoherentResolutionExtension (stdSimplexFaceUnion.{u} (S.image (fun U ↦ U ∩ T)))
      (coherentResolutionFaceUnion (S.image (fun U ↦ U ∩ T)))) :
    HasCoherentResolutionExtension (stdSimplexFaceUnion.{u} (insert T S))
      (coherentResolutionFaceUnion (insert T S))

lemma hasCoherentResolutionExtension_faceUnion {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) :
    HasCoherentResolutionExtension (stdSimplexFaceUnion.{u} S) (coherentResolutionFaceUnion S)

lemma hasCoherentResolutionExtension_boundary (n : ℕ) :
    HasCoherentResolutionExtension (SSet.boundary.{u} n) (coherentResolutionBoundary n)

noncomputable def coherentResolutionBoundaryExtensionIso (n : ℕ) :
    coherentResolution.{u}.obj (SSet.boundary n).toSSet ≅ (coherentResolutionBoundary n).toSSet

lemma coherentResolutionBoundaryExtensionIso_hom_ι (n : ℕ) :
    (coherentResolutionBoundaryExtensionIso.{u} n).hom ≫ (coherentResolutionBoundary n).ι =
      coherentResolution.map (SSet.boundary n).ι ≫ coherentResolutionStdIso.hom.app ⦋n⦌

lemma coherentResolutionBoundaryExtensionIso_projection (n : ℕ) :
    (coherentResolutionBoundaryExtensionIso.{u} n).hom ≫ coherentResolutionBoundaryProjection n =
      coherentResolutionProjectionAll.app (SSet.boundary n).toSSet

lemma coherentResolutionProjectionAll_boundary_isPrecompositionEquivalence (n : ℕ) :
    IsPrecompositionEquivalence
      (coherentResolutionProjectionAll.{u}.app (SSet.boundary n).toSSet)

lemma coherentResolution_map_boundary_ι_mono (n : ℕ) :
    Mono (coherentResolution.{u}.map (SSet.boundary n).ι)

lemma coherentResolution_map_mono_of_attachCells {α : Type v} {A B : α → SSet.{u}}
    (g : (i : α) → A i ⟶ B i) {X Y : SSet.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} g f) (hg : ∀ i, Mono (coherentResolution.map (g i))) :
    Mono (coherentResolution.map f)

lemma coherentResolution_map_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (coherentResolution.map f)

instance coherentResolution_preservesMonomorphisms :
    coherentResolution.{u}.PreservesMonomorphisms

lemma coherentResolutionProjectionAll_initial_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (coherentResolutionProjectionAll.{u}.app (⊥_ SSet.{u}))

lemma coherentResolutionProjectionAll_isPrecompositionEquivalence (X : SSet.{u}) :
    IsPrecompositionEquivalence (coherentResolutionProjectionAll.app X)

lemma coherentResolution_map_isPrecompositionEquivalence {A B : SSet.{u}} (f : A ⟶ B)
    (hf : IsPrecompositionEquivalence f) : IsPrecompositionEquivalence (coherentResolution.map f)

lemma exists_extension_of_precompositionEquivalence {A B Z : SSet.{u}} [Quasicategory Z]
    (i : A ⟶ B) [Mono i] (hi : IsPrecompositionEquivalence i) (a : A ⟶ Z) :
    ∃ b : B ⟶ Z, i ≫ b = a

instance coherentResolutionRightAdjoint_quasicategory (Z : SSet.{u}) [Quasicategory Z] :
    Quasicategory (coherentResolutionRightAdjoint.obj Z)

lemma trivialKanFibration_pre_horn (Z : SSet.{u}) [KanComplex Z]
    (n : ℕ) (i : Fin (n + 2)) : TrivialKanFibration ((pre (horn (n + 1) i).ι).app Z)

lemma coherentResolution_pre_horn_isQCatEquivalence (Z : SSet.{u}) [KanComplex Z]
    (n : ℕ) (i : Fin (n + 2)) :
    IsQCatEquivalence ((pre (coherentResolution.map (horn (n + 1) i).ι)).app Z)

lemma coherentResolutionRightAdjoint_horn_extension (Z : SSet.{u}) [KanComplex Z]
    (n : ℕ) (i : Fin (n + 2))
    (σ : (horn (n + 1) i).toSSet ⟶ coherentResolutionRightAdjoint.obj Z) :
    ∃ F : Δ[n + 1] ⟶ coherentResolutionRightAdjoint.obj Z, (horn (n + 1) i).ι ≫ F = σ

instance coherentResolutionRightAdjoint_kanComplex (Z : SSet.{u}) [KanComplex Z] :
    KanComplex (coherentResolutionRightAdjoint.obj Z)

noncomputable def coherentResolutionCylinderComparison (K : SSet.{u}) :
    coherentResolution.obj (K ⊗ Δ[1]) ⟶ coherentResolution.obj K ⊗ Δ[1]

lemma coherentResolutionCylinderComparison_zero (K : SSet.{u}) :
    coherentResolution.map (SSet.ι₀ : K ⟶ K ⊗ Δ[1]) ≫ coherentResolutionCylinderComparison K =
      SSet.ι₀

lemma coherentResolutionCylinderComparison_one (K : SSet.{u}) :
    coherentResolution.map (SSet.ι₁ : K ⟶ K ⊗ Δ[1]) ≫ coherentResolutionCylinderComparison K =
      SSet.ι₁

noncomputable def coherentResolutionTransposeHomotopy {K Z : SSet.{u}}
    {a b : coherentResolution.obj K ⟶ Z} (H : SSet.Homotopy a b) :
    SSet.Homotopy (coherentResolutionAdjunction.homEquiv K Z a)
      (coherentResolutionAdjunction.homEquiv K Z b)

lemma coherentResolutionHomEquiv_projection_comp {K Z : SSet.{u}} (b : K ⟶ Z) :
    coherentResolutionAdjunction.homEquiv K Z (coherentResolutionProjectionAll.app K ≫ b) =
      b ≫ coherentResolutionComparison Z

lemma coherentResolutionComparison_postcomp_essentiallySurjective {K Z : SSet.{u}} [KanComplex Z]
    (a : K ⟶ coherentResolutionRightAdjoint.obj Z) :
    ∃ b : K ⟶ Z, Nonempty (FunctorIso (b ≫ coherentResolutionComparison Z) a)

end SerrePositivity.InfinityCategories
```

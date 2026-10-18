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
universe u
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

end SerrePositivity.InfinityCategories
```

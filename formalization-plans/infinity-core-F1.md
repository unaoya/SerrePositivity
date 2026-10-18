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

**分割（2026-10-18 15:40）：** F1e・F1f・F1g は straightening に依存しないので、レーン α2b（Π2 チャット、
計画は [infinity-core-F1b.md](infinity-core-F1b.md)、配置 `InfinityCategories/F1B/`）へ切り出した。
α2 の順序は F1a → F1b → F1c → F1d → F1h → F1i。F1h は α2b の Kan 拡張を使ってよい。F1d が最大の山で、
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

lemma coherentResolutionComparison_counit (Z : SSet.{u}) :
    coherentResolution.map (coherentResolutionComparison Z) ≫
        coherentResolutionAdjunction.counit.app Z = coherentResolutionProjectionAll.app Z

lemma coherentResolutionComparison_exists_retraction (Z : SSet.{u}) [KanComplex Z] :
    ∃ c : coherentResolutionRightAdjoint.obj Z ⟶ Z,
      coherentResolutionComparison Z ≫ c = 𝟙 Z

lemma coherentResolutionComparison_isQCatEquivalence (Z : SSet.{u}) [KanComplex Z] :
    IsQCatEquivalence (coherentResolutionComparison Z)

lemma coherentResolutionComparison_isSimplicialHomotopyEquivalence
    (Z : SSet.{u}) [KanComplex Z] :
    IsSimplicialHomotopyEquivalence (coherentResolutionComparison Z)

def uliftSimplicialHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g)

lemma IsSimplicialHomotopyEquivalence.ulift {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : IsSimplicialHomotopyEquivalence f) :
    IsSimplicialHomotopyEquivalence ((SSet.uliftFunctor.{v, u}).map f)

lemma IsQCatEquivalence.ulift_of_kan {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f : X ⟶ Y} (hf : IsQCatEquivalence f) :
    IsQCatEquivalence ((SSet.uliftFunctor.{v, u}).map f)

lemma coherentHomComparison_isQCatEquivalence {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] (X Y : C) :
    IsQCatEquivalence (coherentHomComparison X Y)

lemma coherentHomComparison_isSimplicialHomotopyEquivalence {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] (X Y : C) :
    IsSimplicialHomotopyEquivalence (coherentHomComparison X Y)

noncomputable def coherentHomEquivalence {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] (X Y : C) :
    QCatEquivalence ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
      (pinchedHom (coherentNerveVertex X) (coherentNerveVertex Y))

lemma rev_lastVertex (n : ℕ) :
    SimplexCategory.rev.map (PinchedHom.lastVertex n) =
      SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0

lemma rev_front (n : ℕ) :
    SimplexCategory.rev.map (PinchedHom.front n) = SimplexCategory.δ 0

lemma constant_opObjEquiv {X : SSet.{u}} (x : X _⦋0⦌) (n : ℕ) :
    SSet.opObjEquiv (PinchedHom.constant (X := X.op) (SSet.opObjEquiv.symm x) n) =
      PinchedHom.constant x n

lemma rev_extend_rev {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    SimplexCategory.rev.map (PinchedHom.extend (SimplexCategory.rev.map α)) =
      SimplexCategory.mkHom (prependOrderHom α.toOrderHom)

def leftPinchedSimplexEquiv {X : SSet.{u}} (x y : X _⦋0⦌) (n : ℕ) :
    (pinchedHomLeft x y) _⦋n⦌ ≃
      {s : X _⦋n + 1⦌ // X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s = x ∧
        X.δ 0 s = PinchedHom.constant y n}

noncomputable def cosliceFiberPinchedLeftIso {X : SSet.{u}} (x y : X _⦋0⦌) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ≅ pinchedHomLeft x y

noncomputable def pointedSpaceFiberPinchedLeftIso (s : SpaceInfinity.{u} _⦋0⦌) :
    vertexFiber pointedSpaceProjection s ≅ pinchedHomLeft pointSpaceVertex s

noncomputable def leftUnstraighteningFiberPinchedLeftIso {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (c : C _⦋0⦌) :
    vertexFiber (leftUnstraighteningProjection F) c ≅
      pinchedHomLeft pointSpaceVertex (F.app (Opposite.op ⦋0⦌) c)

noncomputable def pointKanObjectHomIso (K : KanObject.{u}) :
    SimplicialCategory.sHom pointKanObject K ≅ K.obj

noncomputable def pointSpaceRightMappingEquivalence (K : KanObject.{u}) :
    QCatEquivalence (pinchedHom pointSpaceVertex (spaceInfinityVertex K))
      ((SSet.uliftFunctor.{u + 1, u}).obj K.obj)

noncomputable def pointSpaceRightMappingEquivalenceAt (s : SpaceInfinity.{u} _⦋0⦌) :
    QCatEquivalence (pinchedHom pointSpaceVertex s)
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject s).obj)

def cosliceFiberUncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    join (Δ[0] : SSet.{u}) A ⟶ X

lemma cosliceFiberUncurry_inl {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    joinInl Δ[0] A ≫ cosliceFiberUncurry f = SSet.yonedaEquiv.symm x

lemma cosliceFiberUncurry_inr {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    joinInr Δ[0] A ≫ cosliceFiberUncurry f = SSet.const y

def cosliceFiberCurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (F : join (Δ[0] : SSet.{u}) A ⟶ X)
    (hx : joinInl Δ[0] A ≫ F = SSet.yonedaEquiv.symm x)
    (hy : joinInr Δ[0] A ≫ F = SSet.const y) :
    A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y

lemma cosliceFiberUncurry_curry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (F : join (Δ[0] : SSet.{u}) A ⟶ X)
    (hx : joinInl Δ[0] A ≫ F = SSet.yonedaEquiv.symm x)
    (hy : joinInr Δ[0] A ≫ F = SSet.const y) :
    cosliceFiberUncurry (cosliceFiberCurry F hx hy) = F

lemma cosliceFiberUncurry_injective {A X : SSet.{u}} (x y : X _⦋0⦌) :
    Function.Injective (cosliceFiberUncurry (A := A) (x := x) (y := y))

lemma cosliceFiberCurry_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    cosliceFiberCurry (cosliceFiberUncurry f)
      (cosliceFiberUncurry_inl f) (cosliceFiberUncurry_inr f) = f

lemma cosliceFiberUncurry_precomp {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (i : A ⟶ B)
    (f : B ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    cosliceFiberUncurry (i ≫ f) = joinMap (𝟙 Δ[0]) i ≫ cosliceFiberUncurry f

def cosliceFiberHomEquiv (A X : SSet.{u}) (x y : X _⦋0⦌) :
    (A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) ≃
      {F : join (Δ[0] : SSet.{u}) A ⟶ X //
        joinInl Δ[0] A ≫ F = SSet.yonedaEquiv.symm x ∧
        joinInr Δ[0] A ≫ F = SSet.const y}

def intervalMappingBoundary {X : SSet.{u}} (x y : X _⦋0⦌) :
    (boundary 1 : SSet.{u}) ⟶ X

def intervalMappingSpace {X : SSet.{u}} (x y : X _⦋0⦌) : SSet.{u}

def intervalMappingUncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) : (Δ[1] : SSet.{u}) ⊗ A ⟶ X

lemma intervalMappingUncurry_boundary {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    ((boundary 1).ι ▷ A) ≫ intervalMappingUncurry f =
      fst (boundary 1 : SSet.{u}) A ≫ intervalMappingBoundary x y

def intervalMappingCurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h : ((boundary 1).ι ▷ A) ≫ H =
      fst (boundary 1 : SSet.{u}) A ≫ intervalMappingBoundary x y) :
    A ⟶ intervalMappingSpace x y

lemma intervalMappingUncurry_curry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h : ((boundary 1).ι ▷ A) ≫ H =
      fst (boundary 1 : SSet.{u}) A ≫ intervalMappingBoundary x y) :
    intervalMappingUncurry (intervalMappingCurry H h) = H

lemma intervalMappingUncurry_injective {A X : SSet.{u}} (x y : X _⦋0⦌) :
    Function.Injective (intervalMappingUncurry (A := A) (x := x) (y := y))

lemma intervalMappingCurry_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    intervalMappingCurry (intervalMappingUncurry f) (intervalMappingUncurry_boundary f) = f

lemma intervalMappingUncurry_precomp {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (i : A ⟶ B) (f : B ⟶ intervalMappingSpace x y) :
    intervalMappingUncurry (i ≫ f) = (Δ[1] ◁ i) ≫ intervalMappingUncurry f

noncomputable def rightMappingSpacePrism (A : SSet.{u}) : Δ[1] ⊗ A ⟶ join A (Δ[0] : SSet.{u})

lemma rightMappingSpacePrism_zero (A : SSet.{u}) :
    prismEndpoint 0 A ≫ rightMappingSpacePrism A = joinInl A Δ[0]

lemma rightMappingSpacePrism_one (A : SSet.{u}) :
    prismEndpoint 1 A ≫ rightMappingSpacePrism A =
      SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫ joinInr A Δ[0]

noncomputable def leftMappingSpacePrism (A : SSet.{u}) : Δ[1] ⊗ A ⟶ join (Δ[0] : SSet.{u}) A

lemma leftMappingSpacePrism_zero (A : SSet.{u}) :
    prismEndpoint 0 A ≫ leftMappingSpacePrism A =
      SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫ joinInl Δ[0] A

lemma leftMappingSpacePrism_one (A : SSet.{u}) :
    prismEndpoint 1 A ≫ leftMappingSpacePrism A = joinInr Δ[0] A

lemma rightMappingSpacePrism_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    (Δ[1] ◁ f) ≫ rightMappingSpacePrism B =
      rightMappingSpacePrism A ≫ joinMap f (𝟙 Δ[0])

lemma leftMappingSpacePrism_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    (Δ[1] ◁ f) ≫ leftMappingSpacePrism B =
      leftMappingSpacePrism A ≫ joinMap (𝟙 Δ[0]) f

lemma intervalMappingBoundary_diagram {A X : SSet.{u}} (x y : X _⦋0⦌) :
    intervalBoundaryDiagram (SSet.const x : A ⟶ X) (SSet.const y) =
      fst (boundary 1 : SSet.{u}) A ≫ intervalMappingBoundary x y

noncomputable def intervalMappingCurryOfEndpoints {A X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : prismEndpoint 0 A ≫ H = SSet.const x)
    (h₁ : prismEndpoint 1 A ≫ H = SSet.const y) : A ⟶ intervalMappingSpace x y

lemma intervalMappingUncurry_curryOfEndpoints {A X : SSet.{u}} {x y : X _⦋0⦌}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : prismEndpoint 0 A ≫ H = SSet.const x)
    (h₁ : prismEndpoint 1 A ≫ H = SSet.const y) :
    intervalMappingUncurry (intervalMappingCurryOfEndpoints H h₀ h₁) = H

lemma const_point_comp_yoneda {A X : SSet.{u}} (x : X _⦋0⦌) :
    (SSet.const (stdSimplex.obj₀Equiv.symm 0) : A ⟶ Δ[0]) ≫ SSet.yonedaEquiv.symm x =
      SSet.const x

noncomputable def pinchedHomToIntervalMappingSpace {X : SSet.{u}} (x y : X _⦋0⦌) :
    pinchedHom x y ⟶ intervalMappingSpace x y

noncomputable def cosliceFiberToIntervalMappingSpace {X : SSet.{u}} (x y : X _⦋0⦌) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ⟶ intervalMappingSpace x y

noncomputable def pinchedHomLeftToIntervalMappingSpace {X : SSet.{u}} (x y : X _⦋0⦌) :
    pinchedHomLeft x y ⟶ intervalMappingSpace x y

lemma pinchedHomToIntervalMappingSpace_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ pinchedHom x y) :
    intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace x y) =
      rightMappingSpacePrism A ≫ pinchedHomUncurry f

lemma cosliceFiberToIntervalMappingSpace_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    intervalMappingUncurry (f ≫ cosliceFiberToIntervalMappingSpace x y) =
      leftMappingSpacePrism A ≫ cosliceFiberUncurry f

def joinEndpointDiagram (A B : SSet.{u}) : SSet.{u}

def joinEndpointInclusion (A B : SSet.{u}) : joinEndpointDiagram A B ⟶ join A B

noncomputable def fatJoinEndpointInclusion (A B : SSet.{u}) :
    joinEndpointDiagram A B ⟶ fatJoin A B

instance joinEndpointInclusion_mono (A B : SSet.{u}) : Mono (joinEndpointInclusion A B)

lemma fatJoinEndpointInclusion_comparison (A B : SSet.{u}) :
    fatJoinEndpointInclusion A B ≫ fatJoinComparison A B = joinEndpointInclusion A B

instance fatJoinEndpointInclusion_mono (A B : SSet.{u}) :
    Mono (fatJoinEndpointInclusion A B)

lemma isQCatEquivalence_fatJoinComparison_fixedEndpoints
    (A B X : SSet.{u}) [Quasicategory X] (p : joinEndpointDiagram A B ⟶ X) :
    IsQCatEquivalence (vertexFiberMap
      ((pre (joinEndpointInclusion A B)).app X)
      ((pre (fatJoinEndpointInclusion A B)).app X)
      ((pre (fatJoinComparison A B)).app X)
      (by rw [← NatTrans.comp_app, ← pre_map, fatJoinEndpointInclusion_comparison])
      (functorVertex p))

lemma evaluateFunctorAt_pre {A B X : SSet.{u}} (j : A ⟶ B) (a : A _⦋0⦌) :
    (pre j).app X ≫ evaluateFunctorAt (Y := X) a =
      evaluateFunctorAt (Y := X) (j.app (Opposite.op ⦋0⦌) a)

lemma isInvertibleEdge_preFiber_of_vertexSurjective {A B X : SSet.{u}}
    [Quasicategory X] (j : A ⟶ B) [Mono j]
    (hj : Function.Surjective (j.app (Opposite.op ⦋0⦌)))
    (p : ((ihom A).obj X) _⦋0⦌)
    {s t : (vertexFiber ((pre j).app X) p) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (vertexFiber ((pre j).app X) p)) s t) :
    IsInvertibleEdge e

lemma kanComplex_preFiber_of_vertexSurjective {A B X : SSet.{u}} [Quasicategory X]
    (j : A ⟶ B) [Mono j] (hj : Function.Surjective (j.app (Opposite.op ⦋0⦌)))
    (p : ((ihom A).obj X) _⦋0⦌) : KanComplex (vertexFiber ((pre j).app X) p)

instance intervalMappingSpace_kanComplex {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌) :
    KanComplex (intervalMappingSpace x y)

lemma rightMappingSpacePrism_hom_ext {A X : SSet.{u}} {f g : join A (Δ[0] : SSet.{u}) ⟶ X}
    (h : rightMappingSpacePrism A ≫ f = rightMappingSpacePrism A ≫ g)
    (hy : joinInr A Δ[0] ≫ f = joinInr A Δ[0] ≫ g) : f = g

lemma leftMappingSpacePrism_hom_ext {A X : SSet.{u}} {f g : join (Δ[0] : SSet.{u}) A ⟶ X}
    (h : leftMappingSpacePrism A ≫ f = leftMappingSpacePrism A ≫ g)
    (hx : joinInl Δ[0] A ≫ f = joinInl Δ[0] A ≫ g) : f = g

instance pinchedHomToIntervalMappingSpace_mono {X : SSet.{u}} (x y : X _⦋0⦌) :
    Mono (pinchedHomToIntervalMappingSpace x y)

instance cosliceFiberToIntervalMappingSpace_mono {X : SSet.{u}} (x y : X _⦋0⦌) :
    Mono (cosliceFiberToIntervalMappingSpace x y)

instance pinchedHomLeftToIntervalMappingSpace_mono {X : SSet.{u}} (x y : X _⦋0⦌) :
    Mono (pinchedHomLeftToIntervalMappingSpace x y)

lemma intervalMappingUncurry_zero {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    prismEndpoint 0 A ≫ intervalMappingUncurry f = SSet.const x

lemma intervalMappingUncurry_one {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    prismEndpoint 1 A ≫ intervalMappingUncurry f = SSet.const y

def rightIntervalCylinderProjection (A : SSet.{u}) :
    (A ⊗ Δ[1]) ⊗ (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ A

def rightIntervalCylinderSection (A : SSet.{u}) :
    Δ[1] ⊗ A ⟶ (A ⊗ Δ[1]) ⊗ (Δ[0] : SSet.{u})

lemma rightIntervalCylinderSection_projection (A : SSet.{u}) :
    rightIntervalCylinderSection A ≫ rightIntervalCylinderProjection A = 𝟙 _

lemma rightIntervalCylinderProjection_section (A : SSet.{u}) :
    rightIntervalCylinderProjection A ≫ rightIntervalCylinderSection A = 𝟙 _

lemma rightIntervalCylinderProjection_zero (A : SSet.{u}) :
    (SSet.ι₀ (X := A) ▷ (Δ[0] : SSet.{u})) ≫ rightIntervalCylinderProjection A =
      fst A Δ[0] ≫ prismEndpoint 0 A

lemma rightIntervalCylinderProjection_one (A : SSet.{u}) :
    (SSet.ι₁ (X := A) ▷ (Δ[0] : SSet.{u})) ≫ rightIntervalCylinderProjection A =
      fst A Δ[0] ≫ prismEndpoint 1 A

noncomputable def rightIntervalFatDiagram {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) : fatJoin A (Δ[0] : SSet.{u}) ⟶ X

lemma rightIntervalFatDiagram_inl {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    fatJoinInl A Δ[0] ≫ rightIntervalFatDiagram f = SSet.const x

lemma rightIntervalFatDiagram_inr {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    fatJoinInr A Δ[0] ≫ rightIntervalFatDiagram f = SSet.yonedaEquiv.symm y

lemma rightIntervalFatDiagram_recover {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    rightIntervalCylinderSection A ≫ fatJoinCylinder A Δ[0] ≫ rightIntervalFatDiagram f =
      intervalMappingUncurry f

lemma exists_joinDiagram_of_fatJoinDiagram {A B X : SSet.{u}} [Quasicategory X]
    (p : joinEndpointDiagram A B ⟶ X) (F : fatJoin A B ⟶ X)
    (hF : fatJoinEndpointInclusion A B ≫ F = p) :
    ∃ G : join A B ⟶ X, ∃ _hG : joinEndpointInclusion A B ≫ G = p,
      ∃ H : SSet.Homotopy (fatJoinComparison A B ≫ G) F,
        (fatJoinEndpointInclusion A B ▷ (Δ[1] : SSet.{u})) ≫ H.h =
          fst (joinEndpointDiagram A B) Δ[1] ≫ p ∧
        ∀ v, IsInvertibleEdge (simplicialHomotopyVertexEdge H v).toTruncated

noncomputable def intervalMappingHomotopyOfSquare {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f g : A ⟶ intervalMappingSpace x y) (K : Δ[1] ⊗ (A ⊗ Δ[1]) ⟶ X)
    (hx : prismEndpoint 0 (A ⊗ Δ[1]) ≫ K = SSet.const x)
    (hy : prismEndpoint 1 (A ⊗ Δ[1]) ≫ K = SSet.const y)
    (h₀ : (Δ[1] ◁ (SSet.ι₀ : A ⟶ A ⊗ Δ[1])) ≫ K = intervalMappingUncurry f)
    (h₁ : (Δ[1] ◁ (SSet.ι₁ : A ⟶ A ⊗ Δ[1])) ≫ K = intervalMappingUncurry g) :
    SSet.Homotopy f g

noncomputable def intervalMappingHomotopyOfFatJoin {A X : SSet.{u}} {x y : X _⦋0⦌}
    {F G : fatJoin A (Δ[0] : SSet.{u}) ⟶ X} (H : SSet.Homotopy F G)
    (f g : A ⟶ intervalMappingSpace x y)
    (hF : rightIntervalCylinderSection A ≫ fatJoinCylinder A Δ[0] ≫ F = intervalMappingUncurry f)
    (hG : rightIntervalCylinderSection A ≫ fatJoinCylinder A Δ[0] ≫ G = intervalMappingUncurry g)
    (hx : (fatJoinInl A Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst A Δ[1] ≫ SSet.const x)
    (hy : (fatJoinInr A Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm y) : SSet.Homotopy f g

lemma pinchedHomToIntervalMappingSpace_exists_homotopy {A X : SSet.{u}}
    [Quasicategory X] {x y : X _⦋0⦌} (a : A ⟶ intervalMappingSpace x y) :
    ∃ b : A ⟶ pinchedHom x y,
      Nonempty (SSet.Homotopy (b ≫ pinchedHomToIntervalMappingSpace x y) a)

lemma pinchedHomToIntervalMappingSpace_postcomp_essentiallySurjective {A X : SSet.{u}}
    [Quasicategory X] {x y : X _⦋0⦌} (a : A ⟶ intervalMappingSpace x y) :
    ∃ b : A ⟶ pinchedHom x y, Nonempty (FunctorIso (b ≫ pinchedHomToIntervalMappingSpace x y) a)

lemma pinchedHomToIntervalMappingSpace_exists_homotopy_section {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    ∃ r : intervalMappingSpace x y ⟶ pinchedHom x y,
      Nonempty (SSet.Homotopy (r ≫ pinchedHomToIntervalMappingSpace x y) (𝟙 _))

lemma joinSimplex_exists_inl_of_cut {A K : SSet.{u}} {n : ℕ}
    (s : (join A K) _⦋n⦌) (h : s.1.val = n + 1) :
    ∃ a : A _⦋n⦌, (joinInl A K).app (Opposite.op ⦋n⦌) a = s

noncomputable def joinLeftBoundaryObject {A B : SSet.{u}} (i : A ⟶ B) (K : SSet.{u}) :
    SSet.{u}

noncomputable def joinLeftBoundaryMap {A B : SSet.{u}} (i : A ⟶ B) (K : SSet.{u}) :
    joinLeftBoundaryObject i K ⟶ join B K

lemma joinLeftBoundaryMap_join {A B : SSet.{u}} (i : A ⟶ B) (K : SSet.{u}) :
    pushout.inl (joinInl A K) i ≫ joinLeftBoundaryMap i K = joinMap i (𝟙 K)

lemma joinLeftBoundaryMap_left {A B : SSet.{u}} (i : A ⟶ B) (K : SSet.{u}) :
    pushout.inr (joinInl A K) i ≫ joinLeftBoundaryMap i K = joinInl B K

instance joinLeftBoundaryMap_mono {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (K : SSet.{u}) :
    Mono (joinLeftBoundaryMap i K)

lemma exists_joinDiagramFamily_extension_of_leftBoundary
    {E F A B X : SSet.{u}} [Quasicategory X]
    (e : E ⟶ F) [Mono e] (he : IsPrecompositionEquivalence e)
    (i : A ⟶ B) [Mono i] (K : SSet.{u})
    (u : E ⟶ (ihom (join B K)).obj X)
    (v : F ⟶ (ihom (join A K)).obj X) (w : F ⟶ (ihom B).obj X)
    (hv : e ≫ v = u ≫ (pre (joinMap i (𝟙 K))).app X)
    (hw : e ≫ w = u ≫ (pre (joinInl B K)).app X)
    (hvw : v ≫ (pre (joinInl A K)).app X = w ≫ (pre i).app X) :
    ∃ U : F ⟶ (ihom (join B K)).obj X,
      e ≫ U = u ∧ U ≫ (pre (joinMap i (𝟙 K))).app X = v ∧
        U ≫ (pre (joinInl B K)).app X = w

lemma exists_joinDiagramFamily_extension_of_leftBoundary_of_hasLiftingProperty
    {E F A B X : SSet.{u}} (e : E ⟶ F) (i : A ⟶ B) (K : SSet.{u})
    [HasLiftingProperty e ((pre (joinLeftBoundaryMap i K)).app X)]
    (u : E ⟶ (ihom (join B K)).obj X)
    (v : F ⟶ (ihom (join A K)).obj X) (w : F ⟶ (ihom B).obj X)
    (hv : e ≫ v = u ≫ (pre (joinMap i (𝟙 K))).app X)
    (hw : e ≫ w = u ≫ (pre (joinInl B K)).app X)
    (hvw : v ≫ (pre (joinInl A K)).app X = w ≫ (pre i).app X) :
    ∃ U : F ⟶ (ihom (join B K)).obj X,
      e ≫ U = u ∧ U ≫ (pre (joinMap i (𝟙 K))).app X = v ∧
        U ≫ (pre (joinInl B K)).app X = w

lemma IsQCatEquivalence.exists_strict_retraction {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] {f : A ⟶ B} [Mono f]
    (hf : IsQCatEquivalence f) : ∃ r : B ⟶ A, f ≫ r = 𝟙 A

lemma isQCatEquivalence_of_retraction_of_rightInverseIso {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (f : A ⟶ B) (r b : B ⟶ A)
    (hr : f ≫ r = 𝟙 A) (hb : FunctorIso (b ≫ f) (𝟙 B)) :
    IsQCatEquivalence f

lemma fixedDiagramι_pre_factor {J K T X : SSet.{u}}
    (j : J ⟶ T) (p : J ⟶ X) (t : K ⟶ J) :
    vertexFiberι ((pre j).app X) (functorVertex p) ≫ (pre (t ≫ j)).app X =
      SSet.const (functorVertex (t ≫ p))

def fixedDiagramRestriction {J K T U X : SSet.{u}}
    (j : J ⟶ T) (k : K ⟶ U) (q : U ⟶ T) (t : K ⟶ J)
    (h : k ≫ q = t ≫ j) (p : J ⟶ X) :
    vertexFiber ((pre j).app X) (functorVertex p) ⟶
      vertexFiber ((pre k).app X) (functorVertex (t ≫ p))

lemma fixedDiagramRestriction_ι {J K T U X : SSet.{u}}
    (j : J ⟶ T) (k : K ⟶ U) (q : U ⟶ T) (t : K ⟶ J)
    (h : k ≫ q = t ≫ j) (p : J ⟶ X) :
    fixedDiagramRestriction j k q t h p ≫
        vertexFiberι ((pre k).app X) (functorVertex (t ≫ p)) =
      vertexFiberι ((pre j).app X) (functorVertex p) ≫ (pre q).app X

lemma fixedDiagramRestriction_pre_naturality {J K T U T' U' X : SSet.{u}}
    (j : J ⟶ T) (k : J ⟶ U) (q : U ⟶ T) (h : k ≫ q = j)
    (j' : K ⟶ T') (k' : K ⟶ U') (q' : U' ⟶ T') (h' : k' ≫ q' = j')
    (a : T' ⟶ T) (b : U' ⟶ U) (t : K ⟶ J)
    (hj : j' ≫ a = t ≫ j) (hk : k' ≫ b = t ≫ k)
    (hab : b ≫ q = q' ≫ a) (p : J ⟶ X) :
    fixedDiagramPre j k q h p ≫ fixedDiagramRestriction k k' b t hk p =
      fixedDiagramRestriction j j' a t hj p ≫
        fixedDiagramPre j' k' q' h' (t ≫ p)

def joinEndpointInl (A B : SSet.{u}) : A ⟶ joinEndpointDiagram A B

def joinEndpointInr (A B : SSet.{u}) : B ⟶ joinEndpointDiagram A B

lemma joinEndpointInl_inclusion (A B : SSet.{u}) :
    joinEndpointInl A B ≫ joinEndpointInclusion A B = joinInl A B

lemma joinEndpointInr_inclusion (A B : SSet.{u}) :
    joinEndpointInr A B ≫ joinEndpointInclusion A B = joinInr A B

lemma joinEndpointInl_fatInclusion (A B : SSet.{u}) :
    joinEndpointInl A B ≫ fatJoinEndpointInclusion A B = fatJoinInl A B

lemma joinEndpointInr_fatInclusion (A B : SSet.{u}) :
    joinEndpointInr A B ≫ fatJoinEndpointInclusion A B = fatJoinInr A B

def joinEndpointMap {A B C D : SSet.{u}} (f : A ⟶ C) (g : B ⟶ D) :
    joinEndpointDiagram A B ⟶ joinEndpointDiagram C D

def joinEndpointDesc {A B X : SSet.{u}} (f : A ⟶ X) (g : B ⟶ X) :
    joinEndpointDiagram A B ⟶ X

lemma joinEndpointInclusion_map {A B C D : SSet.{u}} (f : A ⟶ C) (g : B ⟶ D) :
    joinEndpointInclusion A B ≫ joinMap f g =
      joinEndpointMap f g ≫ joinEndpointInclusion C D

lemma fatJoinEndpointInclusion_map {A B C D : SSet.{u}} (f : A ⟶ C) (g : B ⟶ D) :
    fatJoinEndpointInclusion A B ≫ fatJoinMap f g =
      joinEndpointMap f g ≫ fatJoinEndpointInclusion C D

lemma joinEndpointMap_desc {A B C D X : SSet.{u}}
    (f : A ⟶ C) (g : B ⟶ D) (p : C ⟶ X) (q : D ⟶ X) :
    joinEndpointMap f g ≫ joinEndpointDesc p q = joinEndpointDesc (f ≫ p) (g ≫ q)

lemma exists_pre_fatJoinComparison_retraction (A K X : SSet.{u}) [Quasicategory X] :
    ∃ r : (ihom (fatJoin A K)).obj X ⟶ (ihom (join A K)).obj X,
      (pre (fatJoinComparison A K)).app X ≫ r = 𝟙 _ ∧
      r ≫ (pre (joinInl A K)).app X = (pre (fatJoinInl A K)).app X ∧
      r ≫ (pre (joinInr A K)).app X = (pre (fatJoinInr A K)).app X

lemma exists_pre_fatJoinComparison_relative_retraction
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (K X : SSet.{u}) [Quasicategory X] :
    ∃ rA : (ihom (fatJoin A K)).obj X ⟶ (ihom (join A K)).obj X,
    ∃ rB : (ihom (fatJoin B K)).obj X ⟶ (ihom (join B K)).obj X,
      (pre (fatJoinComparison A K)).app X ≫ rA = 𝟙 _ ∧
      (pre (fatJoinComparison B K)).app X ≫ rB = 𝟙 _ ∧
      rB ≫ (pre (joinMap i (𝟙 K))).app X = (pre (fatJoinMap i (𝟙 K))).app X ≫ rA ∧
      rB ≫ (pre (joinInl B K)).app X = (pre (fatJoinInl B K)).app X ∧
      rB ≫ (pre (joinInr B K)).app X = (pre (fatJoinInr B K)).app X

lemma exists_joinDiagram_relative_extension {A B K X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (F : fatJoin B K ⟶ X) (G : join A K ⟶ X)
    (hFG : fatJoinMap i (𝟙 K) ≫ F = fatJoinComparison A K ≫ G) :
    ∃ H : join B K ⟶ X,
      joinMap i (𝟙 K) ≫ H = G ∧
      joinInl B K ≫ H = fatJoinInl B K ≫ F ∧
      joinInr B K ≫ H = fatJoinInr B K ≫ F

lemma rightIntervalFatDiagram_cylinder {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    fatJoinCylinder A Δ[0] ≫ rightIntervalFatDiagram f =
      rightIntervalCylinderProjection A ≫ intervalMappingUncurry f

lemma rightIntervalCylinderProjection_naturality {A B : SSet.{u}} (i : A ⟶ B) :
    fatJoinCylinderMap i (𝟙 (Δ[0] : SSet.{u})) ≫ rightIntervalCylinderProjection B =
      rightIntervalCylinderProjection A ≫ (Δ[1] ◁ i)

lemma rightIntervalFatDiagram_precomp {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (i : A ⟶ B) (f : B ⟶ intervalMappingSpace x y) :
    fatJoinMap i (𝟙 (Δ[0] : SSet.{u})) ≫ rightIntervalFatDiagram f =
      rightIntervalFatDiagram (i ≫ f)

lemma rightIntervalFatDiagram_comparison {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ pinchedHom x y) :
    rightIntervalFatDiagram (f ≫ pinchedHomToIntervalMappingSpace x y) =
      fatJoinComparison A Δ[0] ≫ pinchedHomUncurry f

lemma pinchedHomToIntervalMappingSpace_exists_retraction {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    ∃ r : intervalMappingSpace x y ⟶ pinchedHom x y,
      pinchedHomToIntervalMappingSpace x y ≫ r = 𝟙 _

lemma pinchedHomToIntervalMappingSpace_isQCatEquivalence {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    IsQCatEquivalence (pinchedHomToIntervalMappingSpace x y)

lemma joinSimplex_exists_inr_of_cut {A K : SSet.{u}} {n : ℕ}
    (s : (join K A) _⦋n⦌) (h : s.1.val = 0) :
    ∃ a : A _⦋n⦌, (joinInr K A).app (Opposite.op ⦋n⦌) a = s

noncomputable def joinRightBoundaryObject {A B : SSet.{u}} (i : A ⟶ B) (K : SSet.{u}) :
    SSet.{u}

noncomputable def joinRightBoundaryMap {A B : SSet.{u}} (i : A ⟶ B) (K : SSet.{u}) :
    joinRightBoundaryObject i K ⟶ join K B

lemma joinRightBoundaryMap_join {A B : SSet.{u}} (i : A ⟶ B) (K : SSet.{u}) :
    pushout.inl (joinInr K A) i ≫ joinRightBoundaryMap i K = joinMap (𝟙 K) i

lemma joinRightBoundaryMap_right {A B : SSet.{u}} (i : A ⟶ B) (K : SSet.{u}) :
    pushout.inr (joinInr K A) i ≫ joinRightBoundaryMap i K = joinInr K B

instance joinRightBoundaryMap_mono {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (K : SSet.{u}) :
    Mono (joinRightBoundaryMap i K)

lemma exists_joinDiagramFamily_extension_of_rightBoundary_of_hasLiftingProperty
    {E F A B X : SSet.{u}} (e : E ⟶ F) (i : A ⟶ B) (K : SSet.{u})
    [HasLiftingProperty e ((pre (joinRightBoundaryMap i K)).app X)]
    (u : E ⟶ (ihom (join K B)).obj X)
    (v : F ⟶ (ihom (join K A)).obj X) (w : F ⟶ (ihom B).obj X)
    (hv : e ≫ v = u ≫ (pre (joinMap (𝟙 K) i)).app X)
    (hw : e ≫ w = u ≫ (pre (joinInr K B)).app X)
    (hvw : v ≫ (pre (joinInr K A)).app X = w ≫ (pre i).app X) :
    ∃ U : F ⟶ (ihom (join K B)).obj X,
      e ≫ U = u ∧ U ≫ (pre (joinMap (𝟙 K) i)).app X = v ∧
        U ≫ (pre (joinInr K B)).app X = w

lemma exists_joinDiagramFamily_extension_of_rightBoundary
    {E F A B X : SSet.{u}} [Quasicategory X]
    (e : E ⟶ F) [Mono e] (he : IsPrecompositionEquivalence e)
    (i : A ⟶ B) [Mono i] (K : SSet.{u})
    (u : E ⟶ (ihom (join K B)).obj X)
    (v : F ⟶ (ihom (join K A)).obj X) (w : F ⟶ (ihom B).obj X)
    (hv : e ≫ v = u ≫ (pre (joinMap (𝟙 K) i)).app X)
    (hw : e ≫ w = u ≫ (pre (joinInr K B)).app X)
    (hvw : v ≫ (pre (joinInr K A)).app X = w ≫ (pre i).app X) :
    ∃ U : F ⟶ (ihom (join K B)).obj X,
      e ≫ U = u ∧ U ≫ (pre (joinMap (𝟙 K) i)).app X = v ∧
        U ≫ (pre (joinInr K B)).app X = w

lemma exists_pre_fatJoinComparison_right_relative_retraction
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (K X : SSet.{u}) [Quasicategory X] :
    ∃ rA : (ihom (fatJoin K A)).obj X ⟶ (ihom (join K A)).obj X,
    ∃ rB : (ihom (fatJoin K B)).obj X ⟶ (ihom (join K B)).obj X,
      (pre (fatJoinComparison K A)).app X ≫ rA = 𝟙 _ ∧
      (pre (fatJoinComparison K B)).app X ≫ rB = 𝟙 _ ∧
      rB ≫ (pre (joinMap (𝟙 K) i)).app X = (pre (fatJoinMap (𝟙 K) i)).app X ≫ rA ∧
      rB ≫ (pre (joinInr K B)).app X = (pre (fatJoinInr K B)).app X ∧
      rB ≫ (pre (joinInl K B)).app X = (pre (fatJoinInl K B)).app X

lemma exists_joinDiagram_right_relative_extension {A B K X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (F : fatJoin K B ⟶ X) (G : join K A ⟶ X)
    (hFG : fatJoinMap (𝟙 K) i ≫ F = fatJoinComparison K A ≫ G) :
    ∃ H : join K B ⟶ X,
      joinMap (𝟙 K) i ≫ H = G ∧
      joinInr K B ≫ H = fatJoinInr K B ≫ F ∧
      joinInl K B ≫ H = fatJoinInl K B ≫ F

def leftIntervalCylinderProjection (A : SSet.{u}) :
    ((Δ[0] : SSet.{u}) ⊗ Δ[1]) ⊗ A ⟶ Δ[1] ⊗ A

def leftIntervalCylinderSection (A : SSet.{u}) :
    Δ[1] ⊗ A ⟶ ((Δ[0] : SSet.{u}) ⊗ Δ[1]) ⊗ A

lemma leftIntervalCylinderSection_projection (A : SSet.{u}) :
    leftIntervalCylinderSection A ≫ leftIntervalCylinderProjection A = 𝟙 _

lemma leftIntervalCylinderProjection_section (A : SSet.{u}) :
    leftIntervalCylinderProjection A ≫ leftIntervalCylinderSection A = 𝟙 _

lemma leftIntervalCylinderProjection_zero (A : SSet.{u}) :
    (SSet.ι₀ (X := (Δ[0] : SSet.{u})) ▷ A) ≫ leftIntervalCylinderProjection A =
      snd (Δ[0] : SSet.{u}) A ≫ prismEndpoint 0 A

lemma leftIntervalCylinderProjection_one (A : SSet.{u}) :
    (SSet.ι₁ (X := (Δ[0] : SSet.{u})) ▷ A) ≫ leftIntervalCylinderProjection A =
      snd (Δ[0] : SSet.{u}) A ≫ prismEndpoint 1 A

noncomputable def leftIntervalFatDiagram {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) : fatJoin (Δ[0] : SSet.{u}) A ⟶ X

lemma leftIntervalFatDiagram_inl {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    fatJoinInl Δ[0] A ≫ leftIntervalFatDiagram f = SSet.yonedaEquiv.symm x

lemma leftIntervalFatDiagram_inr {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    fatJoinInr Δ[0] A ≫ leftIntervalFatDiagram f = SSet.const y

lemma leftIntervalFatDiagram_cylinder {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    fatJoinCylinder Δ[0] A ≫ leftIntervalFatDiagram f =
      leftIntervalCylinderProjection A ≫ intervalMappingUncurry f

lemma leftIntervalFatDiagram_recover {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    leftIntervalCylinderSection A ≫ fatJoinCylinder Δ[0] A ≫ leftIntervalFatDiagram f =
      intervalMappingUncurry f

lemma leftIntervalCylinderProjection_naturality {A B : SSet.{u}} (i : A ⟶ B) :
    fatJoinCylinderMap (𝟙 (Δ[0] : SSet.{u})) i ≫ leftIntervalCylinderProjection B =
      leftIntervalCylinderProjection A ≫ (Δ[1] ◁ i)

lemma leftIntervalFatDiagram_precomp {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (i : A ⟶ B) (f : B ⟶ intervalMappingSpace x y) :
    fatJoinMap (𝟙 (Δ[0] : SSet.{u})) i ≫ leftIntervalFatDiagram f =
      leftIntervalFatDiagram (i ≫ f)

lemma leftIntervalFatDiagram_comparison {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    leftIntervalFatDiagram (f ≫ cosliceFiberToIntervalMappingSpace x y) =
      fatJoinComparison Δ[0] A ≫ cosliceFiberUncurry f

noncomputable def intervalMappingHomotopyOfPrism {A D X : SSet.{u}} {x y : X _⦋0⦌}
    {F G : D ⟶ X} (H : SSet.Homotopy F G) (P : Δ[1] ⊗ A ⟶ D)
    (f g : A ⟶ intervalMappingSpace x y)
    (hF : P ≫ F = intervalMappingUncurry f) (hG : P ≫ G = intervalMappingUncurry g)
    (hx : ((prismEndpoint 0 A ≫ P) ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const x)
    (hy : ((prismEndpoint 1 A ≫ P) ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const y) :
    SSet.Homotopy f g

noncomputable def leftIntervalFatPrism (A : SSet.{u}) :
    Δ[1] ⊗ A ⟶ fatJoin (Δ[0] : SSet.{u}) A

lemma leftIntervalFatPrism_zero (A : SSet.{u}) :
    prismEndpoint 0 A ≫ leftIntervalFatPrism A =
      SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫ fatJoinInl Δ[0] A

lemma leftIntervalFatPrism_one (A : SSet.{u}) :
    prismEndpoint 1 A ≫ leftIntervalFatPrism A = fatJoinInr Δ[0] A

lemma leftIntervalFatPrism_comparison (A : SSet.{u}) :
    leftIntervalFatPrism A ≫ fatJoinComparison Δ[0] A = leftMappingSpacePrism A

noncomputable def intervalMappingHomotopyOfLeftFatJoin {A X : SSet.{u}} {x y : X _⦋0⦌}
    {F G : fatJoin (Δ[0] : SSet.{u}) A ⟶ X} (H : SSet.Homotopy F G)
    (f g : A ⟶ intervalMappingSpace x y)
    (hF : leftIntervalFatPrism A ≫ F = intervalMappingUncurry f)
    (hG : leftIntervalFatPrism A ≫ G = intervalMappingUncurry g)
    (hx : (fatJoinInl Δ[0] A ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm x)
    (hy : (fatJoinInr Δ[0] A ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst A Δ[1] ≫ SSet.const y) : SSet.Homotopy f g

lemma cosliceFiberToIntervalMappingSpace_exists_homotopy {A X : SSet.{u}}
    [Quasicategory X] {x y : X _⦋0⦌} (a : A ⟶ intervalMappingSpace x y) :
    ∃ b : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y,
      Nonempty (SSet.Homotopy (b ≫ cosliceFiberToIntervalMappingSpace x y) a)

lemma cosliceFiberToIntervalMappingSpace_postcomp_essentiallySurjective {A X : SSet.{u}}
    [Quasicategory X] {x y : X _⦋0⦌} (a : A ⟶ intervalMappingSpace x y) :
    ∃ b : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y, Nonempty (FunctorIso (b ≫ cosliceFiberToIntervalMappingSpace x y) a)

lemma cosliceFiberToIntervalMappingSpace_exists_homotopy_section {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    ∃ r : intervalMappingSpace x y ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y,
      Nonempty (SSet.Homotopy (r ≫ cosliceFiberToIntervalMappingSpace x y) (𝟙 _))

lemma cosliceFiberToIntervalMappingSpace_exists_retraction {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    ∃ r : intervalMappingSpace x y ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y,
      cosliceFiberToIntervalMappingSpace x y ≫ r = 𝟙 _

lemma cosliceFiberToIntervalMappingSpace_isQCatEquivalence {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    IsQCatEquivalence (cosliceFiberToIntervalMappingSpace x y)

lemma pinchedHomLeftToIntervalMappingSpace_isQCatEquivalence {X : SSet.{u}}
    [Quasicategory X] (x y : X _⦋0⦌) :
    IsQCatEquivalence (pinchedHomLeftToIntervalMappingSpace x y)

noncomputable def pinchedHomLeftRightEquivalence {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : QCatEquivalence (pinchedHomLeft x y) (pinchedHom x y)

noncomputable def cosliceFiberRightMappingEquivalence {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) :
    QCatEquivalence (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y)
      (pinchedHom x y)

noncomputable def pointedSpaceFiberValueEquivalence (s : SpaceInfinity.{u} _⦋0⦌) :
    QCatEquivalence (vertexFiber pointedSpaceProjection s)
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject s).obj)

noncomputable def leftUnstraighteningFiberValueEquivalence {C : SSet.{u + 1}}
    (F : C ⟶ SpaceInfinity.{u}) (c : C _⦋0⦌) :
    QCatEquivalence (vertexFiber (leftUnstraighteningProjection F) c)
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) c)).obj)

lemma leftAnodyneExtensions_pushoutObjObj_horn {m : ℕ} (k : Fin (m + 1))
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (sq : (curriedTensor SSet.{u}).PushoutObjObj (horn (m + 1) k.castSucc).ι i) :
    leftAnodyneExtensions sq.ι

lemma leftAnodyneExtensions_horn_whiskerRight {m : ℕ} (k : Fin (m + 1))
    (A : SSet.{u}) : leftAnodyneExtensions ((horn (m + 1) k.castSucc).ι ▷ A)

instance ihom_map_leftFibration {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    (A : SSet.{u}) : LeftFibration ((ihom A).map p)

def relativeFunctorSpace {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) : SSet.{u}

def relativeFunctorUncurry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (f : T ⟶ relativeFunctorSpace p a) : A ⊗ T ⟶ E

lemma relativeFunctorUncurry_projection {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (f : T ⟶ relativeFunctorSpace p a) :
    relativeFunctorUncurry f ≫ p = fst A T ≫ a

def relativeFunctorCurry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (H : A ⊗ T ⟶ E) (hH : H ≫ p = fst A T ≫ a) :
    T ⟶ relativeFunctorSpace p a

lemma relativeFunctorUncurry_curry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (H : A ⊗ T ⟶ E) (hH : H ≫ p = fst A T ≫ a) :
    relativeFunctorUncurry (relativeFunctorCurry H hH) = H

lemma relativeFunctorUncurry_injective {A T E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    Function.Injective (relativeFunctorUncurry (T := T) (p := p) (a := a))

instance relativeFunctorSpace_kanComplex {A E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    (a : A ⟶ B) : KanComplex (relativeFunctorSpace p a)

def relativeFunctorPre {A D E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) :
    relativeFunctorSpace p a ⟶ relativeFunctorSpace p (i ≫ a)

lemma relativeFunctorPre_ι {A D E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) :
    relativeFunctorPre p a i ≫ vertexFiberι ((ihom D).map p) (functorVertex (i ≫ a)) =
      vertexFiberι ((ihom A).map p) (functorVertex a) ≫ (pre i).app E

lemma relativeFunctorPre_id {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    relativeFunctorPre p a (𝟙 A) = 𝟙 (relativeFunctorSpace p a)

lemma relativeFunctorPre_comp {A D T E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (j : T ⟶ D) :
    relativeFunctorPre p a i ≫ relativeFunctorPre p (i ≫ a) j =
      relativeFunctorPre p a (j ≫ i)

def relativeFunctorEvaluate {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (v : A _⦋0⦌) :
    relativeFunctorSpace p a ⟶ vertexFiber p (a.app (Opposite.op ⦋0⦌) v)

lemma relativeFunctorEvaluate_ι {A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (v : A _⦋0⦌) :
    relativeFunctorEvaluate p a v ≫ vertexFiberι p (a.app (Opposite.op ⦋0⦌) v) =
      vertexFiberι ((ihom A).map p) (functorVertex a) ≫ evaluateFunctorAt v

def nerveUnderMap {C : Type u} [Category.{u} C] {c d : C} (f : c ⟶ d) :
    nerve (Under d) ⟶ nerve (Under c)

lemma nerveUnderMap_projection {C : Type u} [Category.{u} C] {c d : C} (f : c ⟶ d) :
    nerveUnderMap f ≫ nerveMap (Under.forget c) = nerveMap (Under.forget d)

lemma nerveUnderMap_id {C : Type u} [Category.{u} C] (c : C) :
    nerveUnderMap (𝟙 c) = 𝟙 (nerve (Under c))

lemma nerveUnderMap_comp {C : Type u} [Category.{u} C] {c d e : C}
    (f : c ⟶ d) (g : d ⟶ e) : nerveUnderMap (f ≫ g) = nerveUnderMap g ≫ nerveUnderMap f

def leftStrictTransport {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) : SSet.{u}

def leftStrictTransportMap {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {c d : C} (f : c ⟶ d) :
    leftStrictTransport p c ⟶ leftStrictTransport p d

lemma leftStrictTransportMap_id {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) : leftStrictTransportMap p (𝟙 c) = 𝟙 _

lemma leftStrictTransportMap_comp {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {c d e : C} (f : c ⟶ d) (g : d ⟶ e) :
    leftStrictTransportMap p (f ≫ g) = leftStrictTransportMap p f ≫ leftStrictTransportMap p g

instance leftStrictTransport_kanComplex {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) : KanComplex (leftStrictTransport p c)

def leftStrictTransportFunctor {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] : C ⥤ KanObject.{u}

def strictTransportUnderIdentityVertex {C : Type u} [Category.{u} C] (c : C) :
    (nerve (Under c)) _⦋0⦌

lemma strictTransportUnderIdentityVertex_projection {C : Type u} [Category.{u} C] (c : C) :
    (nerveMap (Under.forget c)).app (Opposite.op ⦋0⦌) (strictTransportUnderIdentityVertex c) =
      (nerveEquiv (C := C)).symm c

def leftStrictTransportEvaluate {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) :
    leftStrictTransport p c ⟶ vertexFiber p ((nerveEquiv (C := C)).symm c)

lemma leftStrictTransportEvaluate_ι {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) :
    leftStrictTransportEvaluate p c ≫ vertexFiberι p ((nerveEquiv (C := C)).symm c) =
      vertexFiberι ((ihom (nerve (Under c))).map p)
        (functorVertex (nerveMap (Under.forget c))) ≫
          evaluateFunctorAt (strictTransportUnderIdentityVertex c)

lemma leftFibration_pullbackObjObjπ {A D E B : SSet.{u}}
    (i : D ⟶ A) [Mono i] (p : E ⟶ B) [LeftFibration p]
    (sq' : internalHom.PullbackObjObj i p) : LeftFibration sq'.π

lemma leftAnodyneExtensions_pushoutObjObj_right {A D K L : SSet.{u}}
    (i : D ⟶ A) [Mono i] (j : K ⟶ L) (hj : leftAnodyneExtensions j)
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) :
    leftAnodyneExtensions sq.ι

lemma leftAnodyneExtensions_pushoutObjObj_left {A D K L : SSet.{u}}
    (i : D ⟶ A) (hi : leftAnodyneExtensions i) (j : K ⟶ L) [Mono j]
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) :
    leftAnodyneExtensions sq.ι

lemma trivialKanFibration_relativeHom_of_leftAnodyne {A D E B : SSet.{u}}
    (i : D ⟶ A) (hi : leftAnodyneExtensions i) (p : E ⟶ B) [LeftFibration p]
    (sq' : internalHom.PullbackObjObj i p) : TrivialKanFibration sq'.π

lemma relativeFunctorPre_trivialKanFibration {A D E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) : TrivialKanFibration (relativeFunctorPre p a i)

lemma curry_evaluateFunctorAt_vertex {A T E : SSet.{u}} (H : A ⊗ T ⟶ E) (v : A _⦋0⦌) :
    curry H ≫ evaluateFunctorAt v = lift (SSet.const v) (𝟙 T) ≫ H

lemma stdSimplex_zero_eq_constant {n : ℕ} (b : (Δ[0] : SSet.{u}) _⦋n⦌) :
    b = PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n

def pointFunctorEvaluationIso (E : SSet.{u}) : (ihom (Δ[0] : SSet.{u})).obj E ≅ E

lemma pointDiagram_eq_const {B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ B) :
    a = SSet.const (a.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))

def relativePointFunctorInverse {E B : SSet.{u}} (p : E ⟶ B)
    (a : (Δ[0] : SSet.{u}) ⟶ B) :
    vertexFiber p (a.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) ⟶
      relativeFunctorSpace p a

lemma relativePointFunctorInverse_evaluate {E B : SSet.{u}} (p : E ⟶ B)
    (a : (Δ[0] : SSet.{u}) ⟶ B) :
    relativePointFunctorInverse p a ≫
        relativeFunctorEvaluate p a (stdSimplex.obj₀Equiv.symm 0) = 𝟙 _

def relativePointFunctorIso {E B : SSet.{u}} (p : E ⟶ B)
    (a : (Δ[0] : SSet.{u}) ⟶ B) :
    relativeFunctorSpace p a ≅
      vertexFiber p (a.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))

lemma relativeFunctorPre_point_evaluate {A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : (Δ[0] : SSet.{u}) ⟶ A) :
    relativeFunctorPre p a i ≫ (relativePointFunctorIso p (i ≫ a)).hom =
      relativeFunctorEvaluate p a (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))

lemma relativeFunctorEvaluate_trivialKanFibration_of_pointMap {A E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B)
    (i : (Δ[0] : SSet.{u}) ⟶ A) (hi : leftAnodyneExtensions i) :
    TrivialKanFibration (relativeFunctorEvaluate p a
      (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)))

lemma relativeFunctorEvaluate_trivialKanFibration_of_identification {A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (v : A _⦋0⦌) (b : B _⦋0⦌)
    (hb : a.app (Opposite.op ⦋0⦌) v = b)
    (f : relativeFunctorSpace p a ⟶ vertexFiber p b)
    (hf : f ≫ vertexFiberι p b =
      vertexFiberι ((ihom A).map p) (functorVertex a) ≫ evaluateFunctorAt v)
    (he : TrivialKanFibration (relativeFunctorEvaluate p a v)) : TrivialKanFibration f

instance leftStrictTransportEvaluate_trivialKanFibration
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    TrivialKanFibration (leftStrictTransportEvaluate p c)

lemma leftStrictTransportEvaluate_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    IsQCatEquivalence (leftStrictTransportEvaluate p c)

noncomputable def leftStrictTransportFiberEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    QCatEquivalence (leftStrictTransport p c)
      (vertexFiber p ((nerveEquiv (C := C)).symm c))

lemma leftStrictTransportEvaluate_fiber_isContractibleKan
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C)
    (e : (vertexFiber p ((nerveEquiv (C := C)).symm c)) _⦋0⦌) :
    IsContractibleKan (vertexFiber (leftStrictTransportEvaluate p c) e)

def simplexPrefixInclusion (m n : ℕ) (h : m ≤ n) : ⦋m⦌ ⟶ ⦋n⦌

lemma simplexPrefixInclusion_id (n : ℕ) : simplexPrefixInclusion n n le_rfl = 𝟙 ⦋n⦌

lemma simplexPrefixInclusion_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    simplexPrefixInclusion l m h ≫ simplexPrefixInclusion m n k =
      simplexPrefixInclusion l n (h.trans k)

def simplexPrefixVertex {n : ℕ} (i : Fin (n + 1)) (k : Fin (i.val + 1)) : Fin (n + 1)

def simplexPrefixRestriction {m n : SimplexCategory} (α : m ⟶ n) (i : Fin (m.len + 1)) :
    ⦋i.val⦌ ⟶ ⦋(α.toOrderHom i).val⦌

lemma simplexPrefixRestriction_id (m : SimplexCategory) (i : Fin (m.len + 1)) :
    simplexPrefixRestriction (𝟙 m) i = 𝟙 ⦋i.val⦌

lemma simplexPrefixRestriction_comp {l m n : SimplexCategory}
    (α : l ⟶ m) (β : m ⟶ n) (i : Fin (l.len + 1)) :
    simplexPrefixRestriction (α ≫ β) i =
      simplexPrefixRestriction α i ≫ simplexPrefixRestriction β (α.toOrderHom i)

lemma simplexPrefixRestriction_naturality {m n : SimplexCategory} (α : m ⟶ n)
    {i j : Fin (m.len + 1)} (h : i ≤ j) :
    simplexPrefixInclusion i.val j.val h ≫ simplexPrefixRestriction α j =
      simplexPrefixRestriction α i ≫ simplexPrefixInclusion
        (α.toOrderHom i).val (α.toOrderHom j).val (α.toOrderHom.monotone h)

lemma simplexPrefixRestriction_factor {m n : SimplexCategory} (α : m ⟶ n)
    (i : Fin (m.len + 1)) :
    simplexPrefixInclusion i.val m.len (Nat.le_of_lt_succ i.isLt) ≫ α =
      simplexPrefixRestriction α i ≫ simplexPrefixInclusion
        (α.toOrderHom i).val n.len (Nat.le_of_lt_succ (α.toOrderHom i).isLt)

def simplexPrefixWeight (n : ℕ) : Fin (n + 1) ⥤ SSet.{u}

def simplexPrefixWeightRestriction {m n : SimplexCategory} (α : m ⟶ n) :
    simplexPrefixWeight.{u} m.len ⟶
      (SimplexCategory.toCat.map α).toFunctor ⋙ simplexPrefixWeight n.len

def weightedNerveSimplex {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) (n : ℕ) : Type u

def weightedNerveSimplexMap {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {m n : SimplexCategory} (α : m ⟶ n) (s : weightedNerveSimplex F n.len) :
    weightedNerveSimplex F m.len

def weightedNerve {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) : SSet.{u}

def weightedNerveProjection {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    weightedNerve F ⟶ nerve C

def weightedNerveMap {C : Type u} [Category.{u} C] {F G : C ⥤ SSet.{u}} (η : F ⟶ G) :
    weightedNerve F ⟶ weightedNerve G

lemma weightedNerveMap_projection {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) :
    weightedNerveMap η ≫ weightedNerveProjection G = weightedNerveProjection F

lemma weightedNerveMap_id {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    weightedNerveMap (𝟙 F) = 𝟙 (weightedNerve F)

lemma weightedNerveMap_comp {C : Type u} [Category.{u} C]
    {F G H : C ⥤ SSet.{u}} (η : F ⟶ G) (θ : G ⟶ H) :
    weightedNerveMap (η ≫ θ) = weightedNerveMap η ≫ weightedNerveMap θ

def weightedNerveFunctor (C : Type u) [Category.{u} C] :
    (C ⥤ SSet.{u}) ⥤ Over (nerve C)

def weightedNerveConstantDiagram {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) {n : ℕ} (s : (F.obj c) _⦋n⦌) :
    simplexPrefixWeight n ⟶ (CategoryTheory.Functor.const (Fin (n + 1))).obj c ⋙ F

def weightedNerveConstantLift {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) (c : C) :
    F.obj c ⟶ weightedNerve F

lemma weightedNerveConstantLift_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    weightedNerveConstantLift F c ≫ weightedNerveProjection F = SSet.const (nerveVertex c)

def weightedNerveFiberMap {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) (c : C) :
    F.obj c ⟶ vertexFiber (weightedNerveProjection F) (nerveVertex c)

instance weightedNerveFiberMap_isIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : IsIso (weightedNerveFiberMap F c)

noncomputable def weightedNerveFiberIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : F.obj c ≅
      vertexFiber (weightedNerveProjection F) (nerveVertex c)

instance weightedNerveFiber_kanComplex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) [KanComplex (F.obj c)] :
    KanComplex (vertexFiber (weightedNerveProjection F) (nerveVertex c))

def leftStrictTransportDiagram {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) : C ⥤ SSet.{u}

def leftStrictTransportWeightedNerve {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) : SSet.{u}

def leftStrictTransportWeightedProjection {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) : leftStrictTransportWeightedNerve p ⟶ nerve C

instance leftStrictTransportWeightedFiber_kanComplex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    KanComplex (vertexFiber (leftStrictTransportWeightedProjection p) (nerveVertex c))

noncomputable def leftStrictTransportWeightedFiberEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    QCatEquivalence
      (vertexFiber (leftStrictTransportWeightedProjection p) (nerveVertex c))
      (vertexFiber p (nerveVertex c))

def weightedNervePrefixFunctor (n : ℕ) : Fin (n + 1) ⥤ Fin (n + 2)

def weightedNerveDiagramSnoc {n : ℕ} (G : Fin (n + 2) ⥤ SSet.{u})
    (τ : simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (hH : ∀ i : Fin (n + 1),
      stdSimplex.map (simplexPrefixInclusion i.val (n + 1) (by omega)) ≫ H =
        τ.app i ≫ G.map (homOfLE (Fin.le_last i.castSucc))) :
    simplexPrefixWeight (n + 1) ⟶ G

lemma weightedNerveDiagramSnoc_castSucc {n : ℕ} (G : Fin (n + 2) ⥤ SSet.{u})
    (τ : simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (hH : ∀ i : Fin (n + 1),
      stdSimplex.map (simplexPrefixInclusion i.val (n + 1) (by omega)) ≫ H =
        τ.app i ≫ G.map (homOfLE (Fin.le_last i.castSucc))) (i : Fin (n + 1)) :
    (weightedNerveDiagramSnoc G τ H hH).app i.castSucc = τ.app i

lemma weightedNerveDiagramSnoc_last {n : ℕ} (G : Fin (n + 2) ⥤ SSet.{u})
    (τ : simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (hH : ∀ i : Fin (n + 1),
      stdSimplex.map (simplexPrefixInclusion i.val (n + 1) (by omega)) ≫ H =
        τ.app i ≫ G.map (homOfLE (Fin.le_last i.castSucc))) :
    (weightedNerveDiagramSnoc G τ H hH).app (Fin.last (n + 1)) = H

lemma weightedNerveDiagram_lastFace_compatible {n : ℕ} (G : Fin (n + 2) ⥤ SSet.{u})
    (τ : simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (h : stdSimplex.map (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫ H =
      τ.app (Fin.last n) ≫ G.map (homOfLE (Fin.le_last (Fin.last n).castSucc)))
    (i : Fin (n + 1)) :
    stdSimplex.map (simplexPrefixInclusion i.val (n + 1) (by omega)) ≫ H =
      τ.app i ≫ G.map (homOfLE (Fin.le_last i.castSucc))

def weightedNerveDiagramSnocOfLastFace {n : ℕ} (G : Fin (n + 2) ⥤ SSet.{u})
    (τ : simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (h : stdSimplex.map (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫ H =
      τ.app (Fin.last n) ≫ G.map (homOfLE (Fin.le_last (Fin.last n).castSucc))) :
    simplexPrefixWeight (n + 1) ⟶ G

lemma weightedNerveDiagram_ext {n : ℕ} {G : Fin (n + 2) ⥤ SSet.{u}}
    {τ ψ : simplexPrefixWeight (n + 1) ⟶ G}
    (hpre : ∀ i : Fin (n + 1), τ.app i.castSucc = ψ.app i.castSucc)
    (hlast : τ.app (Fin.last (n + 1)) = ψ.app (Fin.last (n + 1))) : τ = ψ

lemma simplexPrefixInclusion_eq_lastFace (n : ℕ) :
    simplexPrefixInclusion n (n + 1) (Nat.le_succ n) = SimplexCategory.δ (Fin.last (n + 1))

lemma simplexPrefixRestriction_inclusion {m n : ℕ} (h : m ≤ n) (i : Fin (m + 1)) :
    simplexPrefixRestriction (simplexPrefixInclusion m n h) i = 𝟙 ⦋i.val⦌

lemma weightedNerveDiagramSnoc_restrict {n : ℕ} (G : Fin (n + 2) ⥤ SSet.{u})
    (τ : simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (hH : ∀ i : Fin (n + 1),
      stdSimplex.map (simplexPrefixInclusion i.val (n + 1) (by omega)) ≫ H =
        τ.app i ≫ G.map (homOfLE (Fin.le_last i.castSucc))) :
    simplexPrefixWeightRestriction (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫
        CategoryTheory.Functor.whiskerLeft (weightedNervePrefixFunctor n)
          (weightedNerveDiagramSnoc G τ H hH) = τ

def weightedNerveSimplexSnoc {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1))
    (τ : simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ σ ⋙ F)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))))
    (h : stdSimplex.map (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫ H =
      τ.app (Fin.last n) ≫ F.map (σ.map (homOfLE (Fin.le_last (Fin.last n).castSucc)))) :
    weightedNerveSimplex F (n + 1)

lemma weightedNerveSimplexSnoc_lastFace {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1))
    (τ : simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ σ ⋙ F)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))))
    (h : stdSimplex.map (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫ H =
      τ.app (Fin.last n) ≫ F.map (σ.map (homOfLE (Fin.le_last (Fin.last n).castSucc)))) :
    weightedNerveSimplexMap F (simplexPrefixInclusion n (n + 1) (Nat.le_succ n))
        (weightedNerveSimplexSnoc F σ τ H h) = ⟨weightedNervePrefixFunctor n ⋙ σ, τ⟩

lemma exists_weightedNerveDiagram_extension_of_lastHorn {n : ℕ}
    (G : Fin (n + 2) ⥤ SSet.{u}) [KanComplex (G.obj (Fin.last (n + 1)))]
    (τ : simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ G)
    (k : Fin (n + 2)) (hk : k ≠ Fin.last (n + 1))
    (f : ∀ (j : Fin (n + 2)) (_hj : j ≠ k), (Δ[n] : SSet.{u}) ⟶ G.obj (Fin.last (n + 1)))
    (hf : horn.IsCompatible f)
    (hlast : f (Fin.last (n + 1)) hk.symm =
      τ.app (Fin.last n) ≫ G.map (homOfLE (Fin.le_last (Fin.last n).castSucc))) :
    ∃ ψ : simplexPrefixWeight (n + 1) ⟶ G,
      (∀ i : Fin (n + 1), ψ.app i.castSucc = τ.app i) ∧
      ∀ j (hj : j ≠ k), stdSimplex.δ j ≫ ψ.app (Fin.last (n + 1)) = f j hj

def weightedNerveSimplexDiagram {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C n) (s : weightedNerveSimplex F n) (h : s.1 = σ) :
    simplexPrefixWeight n ⟶ σ ⋙ F

lemma weightedNerveSimplexDiagram_mk {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C n) (τ : simplexPrefixWeight n ⟶ σ ⋙ F) :
    weightedNerveSimplexDiagram F σ ⟨σ, τ⟩ rfl = τ

lemma weightedNerveSimplexDiagram_eta {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C n) (s : weightedNerveSimplex F n) (h : s.1 = σ) :
    (⟨σ, weightedNerveSimplexDiagram F σ s h⟩ : weightedNerveSimplex F n) = s

lemma weightedNerveSimplexDiagram_map {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {m n : SimplexCategory} (α : m ⟶ n) (σ : ComposableArrows C n.len)
    (s : weightedNerveSimplex F n.len) (h : s.1 = σ) :
    weightedNerveSimplexDiagram F ((SimplexCategory.toCat.map α).toFunctor ⋙ σ)
        (weightedNerveSimplexMap F α s)
        (congrArg (fun q ↦ (SimplexCategory.toCat.map α).toFunctor ⋙ q) h) =
      simplexPrefixWeightRestriction α ≫
        CategoryTheory.Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor
          (weightedNerveSimplexDiagram F σ s h)

lemma weightedNerveHornFace_base {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) :
    (SSet.yonedaEquiv (horn.ι k j hj ≫ a)).1 =
      (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ

def weightedNerveHornFaceDiagram {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) :
    simplexPrefixWeight n ⟶
      (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ ⋙ F

lemma weightedNerveHornFaceDiagram_eta {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) :
    (⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
      weightedNerveHornFaceDiagram F σ k a ha j hj⟩ : weightedNerveSimplex F n) =
      SSet.yonedaEquiv (horn.ι k j hj ≫ a)

lemma weightedNerveHornFaceDiagram_overlap {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n m : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j l : Fin (n + 2)) (hj : j ≠ k) (hl : l ≠ k)
    (β γ : ⦋m⦌ ⟶ ⦋n⦌)
    (h : (stdSimplex.map β : (Δ[m] : SSet.{u}) ⟶ Δ[n]) ≫ horn.ι k j hj =
      stdSimplex.map γ ≫ horn.ι k l hl) :
    weightedNerveSimplexMap F β
        ⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
          weightedNerveHornFaceDiagram F σ k a ha j hj⟩ =
      weightedNerveSimplexMap F γ
        ⟨(SimplexCategory.toCat.map (SimplexCategory.δ l)).toFunctor ⋙ σ,
          weightedNerveHornFaceDiagram F σ k a ha l hl⟩

lemma simplexPrefixRestriction_last_factor {m n : SimplexCategory} (α : m ⟶ n) :
    simplexPrefixRestriction α (Fin.last m.len) ≫ simplexPrefixInclusion
        (α.toOrderHom (Fin.last m.len)).val n.len
        (Nat.le_of_lt_succ (α.toOrderHom (Fin.last m.len)).isLt) = α

def weightedNerveConstantEvaluation (C : Type u) [Category.{u} C] (K : SSet.{u}) :
    weightedNerve ((CategoryTheory.Functor.const C).obj K) ⟶ K

def weightedNerveTerminalCoefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsTerminal t) :
    F ⟶ (CategoryTheory.Functor.const C).obj (F.obj t)

def weightedNerveTerminalEvaluation {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsTerminal t) : weightedNerve F ⟶ F.obj t

def weightedNerveBaseMap {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) : weightedNerve (H ⋙ F) ⟶ weightedNerve F

lemma weightedNerveBaseMap_projection {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    weightedNerveBaseMap H F ≫ weightedNerveProjection F =
      weightedNerveProjection (H ⋙ F) ≫ nerveMap H

lemma weightedNerveBaseMap_isPullback {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    IsPullback (weightedNerveBaseMap H F) (weightedNerveProjection (H ⋙ F))
      (weightedNerveProjection F) (nerveMap H)

noncomputable def weightedNerveBaseChangeLift {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) {T : SSet.{u}}
    (a : T ⟶ weightedNerve F) (b : T ⟶ nerve D)
    (h : a ≫ weightedNerveProjection F = b ≫ nerveMap H) :
    T ⟶ weightedNerve (H ⋙ F)

lemma weightedNerveBaseChangeLift_base {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) {T : SSet.{u}}
    (a : T ⟶ weightedNerve F) (b : T ⟶ nerve D)
    (h : a ≫ weightedNerveProjection F = b ≫ nerveMap H) :
    weightedNerveBaseChangeLift H F a b h ≫ weightedNerveBaseMap H F = a

lemma weightedNerveBaseChangeLift_projection {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) {T : SSet.{u}}
    (a : T ⟶ weightedNerve F) (b : T ⟶ nerve D)
    (h : a ≫ weightedNerveProjection F = b ≫ nerveMap H) :
    weightedNerveBaseChangeLift H F a b h ≫ weightedNerveProjection (H ⋙ F) = b

def weightedNerveSimplexIndexFunctor {C : Type u} [Category.{u} C]
    {n : ℕ} (σ : ComposableArrows C n) : ULift.{u} (Fin (n + 1)) ⥤ C

lemma weightedNerveSimplexIndexFunctor_projection {C : Type u} [Category.{u} C]
    {n : ℕ} (σ : ComposableArrows C n) :
    (stdSimplex.isoNerve.{u} n).hom ≫ nerveMap (weightedNerveSimplexIndexFunctor σ) =
      SSet.yonedaEquiv.symm σ

def weightedNerveSimplexIndexTerminal (n : ℕ) :
    IsTerminal (ULift.up (Fin.last n) : ULift.{u} (Fin (n + 1)))

noncomputable def weightedNerveSimplexCoefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C n) {T : SSet.{u}}
    (a : T ⟶ weightedNerve F) (b : T ⟶ (Δ[n] : SSet.{u}))
    (ha : a ≫ weightedNerveProjection F = b ≫ SSet.yonedaEquiv.symm σ) :
    T ⟶ F.obj (σ.obj (Fin.last n))

noncomputable def weightedNerveHornLastCoefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    (horn (n + 1) k : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1)))

lemma exists_weightedNerveHornLastCoefficient_filler {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    [KanComplex (F.obj (σ.obj (Fin.last (n + 1))))] (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    ∃ H : (Δ[n + 1] : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))),
      (horn (n + 1) k).ι ≫ H = weightedNerveHornLastCoefficient F σ k a ha

lemma weightedNerveSimplexCoefficient_congr {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C n) {T : SSet.{u}}
    (a a' : T ⟶ weightedNerve F) (b b' : T ⟶ (Δ[n] : SSet.{u}))
    (h : a ≫ weightedNerveProjection F = b ≫ SSet.yonedaEquiv.symm σ)
    (h' : a' ≫ weightedNerveProjection F = b' ≫ SSet.yonedaEquiv.symm σ)
    (ha : a = a') (hb : b = b') :
    weightedNerveSimplexCoefficient F σ a b h = weightedNerveSimplexCoefficient F σ a' b' h'

lemma weightedNerveBaseChangeLift_precomp {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) {T U : SSet.{u}}
    (a : T ⟶ weightedNerve F) (b : T ⟶ nerve D)
    (h : a ≫ weightedNerveProjection F = b ≫ nerveMap H) (r : U ⟶ T)
    (hr : (r ≫ a) ≫ weightedNerveProjection F = (r ≫ b) ≫ nerveMap H) :
    weightedNerveBaseChangeLift H F (r ≫ a) (r ≫ b) hr =
      r ≫ weightedNerveBaseChangeLift H F a b h

lemma weightedNerveSimplexCoefficient_precomp {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C n) {T U : SSet.{u}}
    (a : T ⟶ weightedNerve F) (b : T ⟶ (Δ[n] : SSet.{u}))
    (h : a ≫ weightedNerveProjection F = b ≫ SSet.yonedaEquiv.symm σ) (r : U ⟶ T)
    (hr : (r ≫ a) ≫ weightedNerveProjection F = (r ≫ b) ≫ SSet.yonedaEquiv.symm σ) :
    weightedNerveSimplexCoefficient F σ (r ≫ a) (r ≫ b) hr =
      r ≫ weightedNerveSimplexCoefficient F σ a b h

lemma weightedNerveTerminalEvaluation_yoneda {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsTerminal t) {n : ℕ}
    (s : weightedNerveSimplex F n) :
    SSet.yonedaEquiv.symm s ≫ weightedNerveTerminalEvaluation F ht =
      s.2.app (Fin.last n) ≫ F.map (ht.from (s.1.obj (Fin.last n)))

def weightedNerveSimplexIndexChain {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    Fin (m + 1) ⥤ ULift.{u} (Fin (n + 1))

lemma weightedNerveSimplexIndexChain_projection {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (stdSimplex.map α : (Δ[m] : SSet.{u}) ⟶ Δ[n]) ≫ (stdSimplex.isoNerve.{u} n).hom =
      SSet.yonedaEquiv.symm (weightedNerveSimplexIndexChain.{u} α)

lemma weightedNerveSimplexCoefficient_diagram {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {m n : ℕ} (σ : ComposableArrows C n) (α : ⦋m⦌ ⟶ ⦋n⦌)
    (τ : simplexPrefixWeight m ⟶ (SimplexCategory.toCat.map α).toFunctor ⋙ σ ⋙ F)
    (h : SSet.yonedaEquiv.symm
        (⟨(SimplexCategory.toCat.map α).toFunctor ⋙ σ, τ⟩ : weightedNerveSimplex F m) ≫
        weightedNerveProjection F = stdSimplex.map α ≫ SSet.yonedaEquiv.symm σ) :
    weightedNerveSimplexCoefficient F σ
        (SSet.yonedaEquiv.symm
          (⟨(SimplexCategory.toCat.map α).toFunctor ⋙ σ, τ⟩ : weightedNerveSimplex F m))
        (stdSimplex.map α) h =
      τ.app (Fin.last m) ≫ F.map (σ.map
        (homOfLE (Fin.le_last (α.toOrderHom (Fin.last m)))))

lemma weightedNerveDiagram_terminal_transport {m n : ℕ}
    (G : Fin (n + 1) ⥤ SSet.{u}) (τ : simplexPrefixWeight n ⟶ G)
    (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (simplexPrefixWeightRestriction α ≫
        CategoryTheory.Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor τ).app
        (Fin.last m) ≫ G.map (homOfLE (Fin.le_last (α.toOrderHom (Fin.last m)))) =
      stdSimplex.map α ≫ τ.app (Fin.last n)

lemma weightedNerveDiagram_terminal_transport_isIso {m n : ℕ}
    (G : Fin (n + 1) ⥤ SSet.{u}) (α : ⦋m⦌ ⟶ ⦋n⦌)
    (h : α.toOrderHom (Fin.last m) = Fin.last n) :
    IsIso (G.map (homOfLE (Fin.le_last (α.toOrderHom (Fin.last m)))))

lemma weightedNerveSimplex_last_heq {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} {s t : weightedNerveSimplex F n} (h : s = t) :
    HEq (s.2.app (Fin.last n)) (t.2.app (Fin.last n))

lemma weightedNerveHornLastCoefficient_face {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) :
    horn.ι k j hj ≫ weightedNerveHornLastCoefficient F σ k a ha =
      (weightedNerveHornFaceDiagram F σ k a ha j hj).app (Fin.last n) ≫
        F.map (σ.map (homOfLE (Fin.le_last ((SimplexCategory.δ j).toOrderHom (Fin.last n)))))

lemma weightedNerveSimplexCoefficient_restriction {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n m : ℕ} (σ : ComposableArrows C n) {T : SSet.{u}}
    (a : T ⟶ weightedNerve F) (b : T ⟶ (Δ[n] : SSet.{u}))
    (h : a ≫ weightedNerveProjection F = b ≫ SSet.yonedaEquiv.symm σ)
    (r : (Δ[m] : SSet.{u}) ⟶ T) (α : ⦋m⦌ ⟶ ⦋n⦌)
    (hr : r ≫ b = stdSimplex.map α)
    (τ : simplexPrefixWeight m ⟶ (SimplexCategory.toCat.map α).toFunctor ⋙ σ ⋙ F)
    (hτ : SSet.yonedaEquiv.symm
      (⟨(SimplexCategory.toCat.map α).toFunctor ⋙ σ, τ⟩ : weightedNerveSimplex F m) = r ≫ a) :
    r ≫ weightedNerveSimplexCoefficient F σ a b h =
      τ.app (Fin.last m) ≫ F.map (σ.map
        (homOfLE (Fin.le_last (α.toOrderHom (Fin.last m)))))

lemma weightedNerveHornPrefix_base {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    (SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a)).1 =
      weightedNervePrefixFunctor n ⋙ σ

def weightedNerveHornPrefixDiagram {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    simplexPrefixWeight n ⟶ weightedNervePrefixFunctor n ⋙ σ ⋙ F

lemma weightedNerveHornPrefixDiagram_yoneda {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    SSet.yonedaEquiv.symm
      (⟨weightedNervePrefixFunctor n ⋙ σ, weightedNerveHornPrefixDiagram F σ k hk a ha⟩ :
        weightedNerveSimplex F n) = horn.ι k (Fin.last (n + 1)) hk.symm ≫ a

lemma exists_weightedNerveHorn_candidate {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    [KanComplex (F.obj (σ.obj (Fin.last (n + 1))))] (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    ∃ ψ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F,
      weightedNerveSimplexMap F (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩ =
        SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a) ∧
      (horn (n + 1) k).ι ≫ ψ.app (Fin.last (n + 1)) =
        weightedNerveHornLastCoefficient F σ k a ha

lemma weightedNerveSimplexMap_comp {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {l m n : ℕ} (α : ⦋l⦌ ⟶ ⦋m⦌) (β : ⦋m⦌ ⟶ ⦋n⦌) (s : weightedNerveSimplex F n) :
    weightedNerveSimplexMap F α (weightedNerveSimplexMap F β s) =
      weightedNerveSimplexMap F (α ≫ β) s

def simplexPrefixThroughLast {n : ℕ} (α : ⦋n⦌ ⟶ ⦋n + 1⦌) (i : Fin (n + 1))
    (hi : (α.toOrderHom i).val ≤ n) : ⦋i.val⦌ ⟶ ⦋n⦌

lemma simplexPrefixThroughLast_factor {n : ℕ} (α : ⦋n⦌ ⟶ ⦋n + 1⦌) (i : Fin (n + 1))
    (hi : (α.toOrderHom i).val ≤ n) :
    simplexPrefixThroughLast α i hi ≫ simplexPrefixInclusion n (n + 1) (Nat.le_succ n) =
      simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt) ≫ α

lemma simplexPrefixThroughLast_restriction {n : ℕ} (α : ⦋n⦌ ⟶ ⦋n + 1⦌) (i : Fin (n + 1))
    (hi : (α.toOrderHom i).val ≤ n) :
    simplexPrefixRestriction (simplexPrefixThroughLast α i hi) (Fin.last i.val) =
      simplexPrefixRestriction α i

lemma simplexFace_last_of_ne_last {n : ℕ} (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)) :
    (SimplexCategory.δ j).toOrderHom (Fin.last n) = Fin.last (n + 1)

lemma simplexFace_eq_last_of_image_last {n : ℕ} (j : Fin (n + 2)) (i : Fin (n + 1))
    (h : (SimplexCategory.δ j).toOrderHom i = Fin.last (n + 1)) : i = Fin.last n

lemma horn_face_prefix_through_last {n : ℕ} (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1)) (j : Fin (n + 2)) (hj : j ≠ k)
    (i : Fin (n + 1)) (hi : ((SimplexCategory.δ j).toOrderHom i).val ≤ n) :
    (stdSimplex.map (simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) :
        (Δ[i.val] : SSet.{u}) ⟶ Δ[n]) ≫ horn.ι k j hj =
      stdSimplex.map (simplexPrefixThroughLast (SimplexCategory.δ j) i hi) ≫
        horn.ι k (Fin.last (n + 1)) hk.symm

lemma weightedNerveHorn_candidate_prefix_agreement {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (ψ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hψ : weightedNerveSimplexMap F (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a))
    (j : Fin (n + 2)) (hj : j ≠ k) (i : Fin (n + 1))
    (hi : ((SimplexCategory.δ j).toOrderHom i).val ≤ n) :
    (weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩).2.app i =
      (weightedNerveHornFaceDiagram F σ k a ha j hj).app i

lemma weightedNerveHorn_candidate_terminal_agreement {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (ψ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hψ : (horn (n + 1) k).ι ≫ ψ.app (Fin.last (n + 1)) =
      weightedNerveHornLastCoefficient F σ k a ha)
    (j : Fin (n + 2)) (hj : j ≠ k) (hjl : j ≠ Fin.last (n + 1)) :
    (weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩).2.app (Fin.last n) =
      (weightedNerveHornFaceDiagram F σ k a ha j hj).app (Fin.last n)

lemma weightedNerveHorn_candidate_face_agreement {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (ψ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hp : weightedNerveSimplexMap F (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (horn.ι k (Fin.last (n + 1)) hk.symm ≫ a))
    (ht : (horn (n + 1) k).ι ≫ ψ.app (Fin.last (n + 1)) =
      weightedNerveHornLastCoefficient F σ k a ha)
    (j : Fin (n + 2)) (hj : j ≠ k) :
    weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (horn.ι k j hj ≫ a)

lemma exists_weightedNerve_leftHorn_lift {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    [KanComplex (F.obj (σ.obj (Fin.last (n + 1))))] (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    ∃ H : (Δ[n + 1] : SSet.{u}) ⟶ weightedNerve F,
      (horn (n + 1) k).ι ≫ H = a ∧ H ≫ weightedNerveProjection F = SSet.yonedaEquiv.symm σ

instance weightedNerveProjection_leftFibration {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] : LeftFibration (weightedNerveProjection F)

instance leftStrictTransportWeightedProjection_leftFibration
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] : LeftFibration (leftStrictTransportWeightedProjection p)

instance weightedNerve_quasicategory {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] : Quasicategory (weightedNerve F)

instance leftStrictTransportWeightedNerve_quasicategory
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] : Quasicategory (leftStrictTransportWeightedNerve p)

def simplicialReplacementSimplex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (n : ℕ) : Type u

def simplicialReplacementSimplexMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {m n : SimplexCategory} (α : m ⟶ n)
    (s : simplicialReplacementSimplex F n.len) : simplicialReplacementSimplex F m.len

def simplicialReplacement {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) : SSet.{u}

def simplicialReplacementProjection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) : simplicialReplacement F ⟶ nerve C

def tautScaffoldDiagram {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (s : simplicialReplacementSimplex F n) :
    simplexPrefixWeight n ⟶ s.1 ⋙ F

def tautScaffold {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    simplicialReplacement F ⟶ weightedNerve F

lemma tautScaffold_projection {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    tautScaffold F ≫ weightedNerveProjection F = simplicialReplacementProjection F

def simplicialReplacementConstantLift {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : F.obj c ⟶ simplicialReplacement F

lemma simplicialReplacementConstantLift_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    simplicialReplacementConstantLift F c ≫ simplicialReplacementProjection F =
      SSet.const (nerveVertex c)

def simplicialReplacementFiberMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    F.obj c ⟶ vertexFiber (simplicialReplacementProjection F) (nerveVertex c)

instance simplicialReplacementFiberMap_isIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : IsIso (simplicialReplacementFiberMap F c)

lemma simplicialReplacementConstantLift_tautScaffold {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    simplicialReplacementConstantLift F c ≫ tautScaffold F = weightedNerveConstantLift F c

def tautScaffoldFiberMap {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) (c : C) :
    vertexFiber (simplicialReplacementProjection F) (nerveVertex c) ⟶
      vertexFiber (weightedNerveProjection F) (nerveVertex c)

lemma simplicialReplacementFiberMap_tautScaffoldFiberMap
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) (c : C) :
    simplicialReplacementFiberMap F c ≫ tautScaffoldFiberMap F c = weightedNerveFiberMap F c

instance tautScaffoldFiberMap_isIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : IsIso (tautScaffoldFiberMap F c)

def scaffoldInitialTransformation {C : Type u} [Category.{u} C]
    {n : ℕ} (σ : ComposableArrows C n) :
    (CategoryTheory.Functor.const (Fin (n + 1))).obj (σ.obj 0) ⟶ σ

def scaffoldUnderChain {C : Type u} [Category.{u} C]
    {n : ℕ} (σ : ComposableArrows C n) : ComposableArrows (Under (σ.obj 0)) n

lemma scaffoldUnderChain_projection {C : Type u} [Category.{u} C]
    {n : ℕ} (σ : ComposableArrows C n) :
    scaffoldUnderChain σ ⋙ Under.forget (σ.obj 0) = σ

lemma scaffoldUnderChain_yoneda_projection {C : Type u} [Category.{u} C]
    {n : ℕ} (σ : ComposableArrows C n) :
    SSet.yonedaEquiv.symm (scaffoldUnderChain σ) ≫ nerveMap (Under.forget (σ.obj 0)) =
      SSet.yonedaEquiv.symm σ

lemma scaffoldUnderChain_restriction {C : Type u} [Category.{u} C]
    {m n : SimplexCategory} (α : m ⟶ n) (σ : ComposableArrows C n.len) :
    (SimplexCategory.toCat.map α).toFunctor ⋙ scaffoldUnderChain σ =
      scaffoldUnderChain ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) ⋙
        Under.map (σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0))))

lemma scaffoldUnderChain_yoneda_restriction {C : Type u} [Category.{u} C]
    {m n : SimplexCategory} (α : m ⟶ n) (σ : ComposableArrows C n.len) :
    stdSimplex.map α ≫ SSet.yonedaEquiv.symm (scaffoldUnderChain σ) =
      SSet.yonedaEquiv.symm
        (scaffoldUnderChain ((SimplexCategory.toCat.map α).toFunctor ⋙ σ)) ≫
          nerveUnderMap (σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0))))

lemma relativeFunctorUncurry_parameter {A T U E B : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (f : T ⟶ relativeFunctorSpace p a) (r : U ⟶ T) :
    relativeFunctorUncurry (r ≫ f) = A ◁ r ≫ relativeFunctorUncurry f

lemma relativeFunctorUncurry_pre {A D T E B : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (f : T ⟶ relativeFunctorSpace p a) (i : D ⟶ A) :
    relativeFunctorUncurry (f ≫ relativeFunctorPre p a i) =
      i ▷ T ≫ relativeFunctorUncurry f

def universalScaffoldSimplex {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {n : ℕ}
    (s : simplicialReplacementSimplex (leftStrictTransportDiagram p) n) :
    (Δ[n] : SSet.{u}) ⟶ E

lemma universalScaffoldSimplex_projection {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {n : ℕ}
    (s : simplicialReplacementSimplex (leftStrictTransportDiagram p) n) :
    universalScaffoldSimplex p s ≫ p = SSet.yonedaEquiv.symm s.1

lemma universalScaffoldSimplex_naturality {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {m n : SimplexCategory} (α : m ⟶ n)
    (s : simplicialReplacementSimplex (leftStrictTransportDiagram p) n.len) :
    universalScaffoldSimplex p
        (simplicialReplacementSimplexMap (leftStrictTransportDiagram p) α s) =
      stdSimplex.map α ≫ universalScaffoldSimplex p s

def universalScaffold {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) : simplicialReplacement (leftStrictTransportDiagram p) ⟶ E

lemma universalScaffold_projection {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) :
    universalScaffold p ≫ p = simplicialReplacementProjection (leftStrictTransportDiagram p)

instance simplicialReplacementFiber_kanComplex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) [KanComplex (F.obj c)] :
    KanComplex (vertexFiber (simplicialReplacementProjection F) (nerveVertex c))

lemma scaffoldUnderChain_constant {C : Type u} [Category.{u} C] (c : C) (n : ℕ) :
    scaffoldUnderChain ((CategoryTheory.Functor.const (Fin (n + 1))).obj c) =
      (CategoryTheory.Functor.const (Fin (n + 1))).obj (Under.mk (𝟙 c))

lemma simplicialReplacementConstantLift_universalScaffold
    {C : Type u} [Category.{u} C] {E : SSet.{u}} (p : E ⟶ nerve C) (c : C) :
    simplicialReplacementConstantLift (leftStrictTransportDiagram p) c ≫ universalScaffold p =
      leftStrictTransportEvaluate p c ≫ vertexFiberι p (nerveVertex c)

def universalScaffoldFiberMap {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (c : C) :
    vertexFiber (simplicialReplacementProjection (leftStrictTransportDiagram p)) (nerveVertex c) ⟶
      vertexFiber p (nerveVertex c)

lemma simplicialReplacementFiberMap_universalScaffoldFiberMap
    {C : Type u} [Category.{u} C] {E : SSet.{u}} (p : E ⟶ nerve C) (c : C) :
    simplicialReplacementFiberMap (leftStrictTransportDiagram p) c ≫
      universalScaffoldFiberMap p c = leftStrictTransportEvaluate p c

instance universalScaffoldFiberMap_trivialKanFibration
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    TrivialKanFibration (universalScaffoldFiberMap p c)

instance leftStrictTransportReplacementFiber_kanComplex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    KanComplex (vertexFiber
      (simplicialReplacementProjection (leftStrictTransportDiagram p)) (nerveVertex c))

lemma universalScaffoldFiberMap_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    IsQCatEquivalence (universalScaffoldFiberMap p c)

def simplicialReplacementBaseMap {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    simplicialReplacement (H ⋙ F) ⟶ simplicialReplacement F

lemma simplicialReplacementBaseMap_projection
    {C D : Type u} [Category.{u} C] [Category.{u} D] (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    simplicialReplacementBaseMap H F ≫ simplicialReplacementProjection F =
      simplicialReplacementProjection (H ⋙ F) ≫ nerveMap H

lemma simplicialReplacementBaseMap_isPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D] (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    IsPullback (simplicialReplacementBaseMap H F) (simplicialReplacementProjection (H ⋙ F))
      (simplicialReplacementProjection F) (nerveMap H)

lemma tautScaffold_baseMap {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    tautScaffold (H ⋙ F) ≫ weightedNerveBaseMap H F =
      simplicialReplacementBaseMap H F ≫ tautScaffold F

lemma tautScaffold_baseMap_isPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D] (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    IsPullback (tautScaffold (H ⋙ F)) (simplicialReplacementBaseMap H F)
      (weightedNerveBaseMap H F) (tautScaffold F)

def simplicialReplacementMap {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) : simplicialReplacement F ⟶ simplicialReplacement G

lemma simplicialReplacementMap_projection {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) :
    simplicialReplacementMap η ≫ simplicialReplacementProjection G =
      simplicialReplacementProjection F

lemma simplicialReplacementMap_id {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    simplicialReplacementMap (𝟙 F) = 𝟙 (simplicialReplacement F)

lemma simplicialReplacementMap_comp {C : Type u} [Category.{u} C]
    {F G H : C ⥤ SSet.{u}} (η : F ⟶ G) (θ : G ⟶ H) :
    simplicialReplacementMap (η ≫ θ) = simplicialReplacementMap η ≫ simplicialReplacementMap θ

def simplicialReplacementFunctor (C : Type u) [Category.{u} C] :
    (C ⥤ SSet.{u}) ⥤ Over (nerve C)

lemma tautScaffold_map {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) :
    simplicialReplacementMap η ≫ tautScaffold G = tautScaffold F ≫ weightedNerveMap η

def simplicialReplacementConstantIso (C : Type u) [Category.{u} C] (K : SSet.{u}) :
    simplicialReplacement ((CategoryTheory.Functor.const C).obj K) ≅ nerve C ⊗ K

lemma simplicialReplacementConstantIso_projection (C : Type u) [Category.{u} C]
    (K : SSet.{u}) :
    (simplicialReplacementConstantIso C K).hom ≫ fst (nerve C) K =
      simplicialReplacementProjection ((CategoryTheory.Functor.const C).obj K)

def simplicialReplacementInitialCoefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsInitial t) :
    (CategoryTheory.Functor.const C).obj (F.obj t) ⟶ F

def simplicialReplacementInitialAssembly {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsInitial t) :
    nerve C ⊗ F.obj t ⟶ simplicialReplacement F

lemma simplicialReplacementInitialAssembly_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsInitial t) :
    simplicialReplacementInitialAssembly F ht ≫ simplicialReplacementProjection F =
      fst (nerve C) (F.obj t)

def simplicialReplacementAssembly {C : Type u} [Category.{u} C]
    {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F) :
    nerve C ⊗ K ⟶ simplicialReplacement F

lemma simplicialReplacementAssembly_baseMap
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F) :
    simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft H η) ≫
        simplicialReplacementBaseMap H F =
      (nerveMap H ▷ K) ≫ simplicialReplacementAssembly η

lemma simplicialReplacementAssembly_baseMap_isPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F) :
    IsPullback (simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft H η))
      (nerveMap H ▷ K) (simplicialReplacementBaseMap H F)
      (simplicialReplacementAssembly η)

def scaffoldFiniteTail (n : ℕ) :
    ULift.{u} (Fin (n + 1)) ⥤ ULift.{u} (Fin (n + 2))

def scaffoldFiniteInitial (n : ℕ) : IsInitial (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)

def scaffoldFiniteTailFactor {n m : ℕ}
    (σ : ComposableArrows (ULift.{u} (Fin (n + 2))) m) :
    ComposableArrows (ULift.{u} (Fin (n + 1))) m

lemma scaffoldFiniteChain_positive {n m : ℕ}
    (σ : ComposableArrows (ULift.{u} (Fin (n + 2))) m)
    (h : (σ.obj 0).down ≠ 0) (i : Fin (m + 1)) : 0 < (σ.obj i).down.val

lemma scaffoldFiniteTailFactor_comp {n m : ℕ}
    (σ : ComposableArrows (ULift.{u} (Fin (n + 2))) m)
    (h : (σ.obj 0).down ≠ 0) :
    scaffoldFiniteTailFactor σ ⋙ scaffoldFiniteTail n = σ

instance scaffoldFiniteTail_nerveMap_mono (n : ℕ) : Mono (nerveMap (scaffoldFiniteTail.{u} n))

lemma scaffoldFiniteReplacement_cover (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    Set.range ((simplicialReplacementBaseMap (scaffoldFiniteTail n) F).app d) ⊔
      Set.range ((simplicialReplacementInitialAssembly F (scaffoldFiniteInitial (n + 1))).app d) =
        Set.univ

lemma scaffoldFiniteTail_complement_zero (n : ℕ) (K : SSet.{u})
    (d : SimplexCategoryᵒᵖ) (s : (nerve (ULift.{u} (Fin (n + 2))) ⊗ K).obj d)
    (hs : s ∉ Set.range ((nerveMap (scaffoldFiniteTail n) ▷ K).app d)) :
    (s.1.obj 0).down = 0

lemma scaffoldFiniteReplacement_isPushout (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    IsPushout
      (simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft (scaffoldFiniteTail n)
        (simplicialReplacementInitialCoefficient F (scaffoldFiniteInitial (n + 1)))))
      (nerveMap (scaffoldFiniteTail n) ▷ F.obj (ULift.up 0))
      (simplicialReplacementBaseMap (scaffoldFiniteTail n) F)
      (simplicialReplacementInitialAssembly F (scaffoldFiniteInitial (n + 1)))

lemma simplexChain_eq_constant {C : Type u} [Category.{u} C] [Subsingleton C]
    [Quiver.IsThin C] (c : C) {n : ℕ} (σ : ComposableArrows C n) :
    σ = (CategoryTheory.Functor.const (Fin (n + 1))).obj c

instance simplicialReplacementConstantLift_isIso
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    (F : C ⥤ SSet.{u}) (c : C) : IsIso (simplicialReplacementConstantLift F c)

lemma nervePoint_snd_isIso {C : Type u} [Category.{u} C] [Subsingleton C]
    [Quiver.IsThin C] (c : C) (K : SSet.{u}) : IsIso (snd (nerve C) K)

lemma simplicialReplacementAssembly_point
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    (c : C) {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F) :
    simplicialReplacementAssembly η = snd (nerve C) K ≫ η.app c ≫
      simplicialReplacementConstantLift F c

def scaffoldIntervalMap (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    F.obj (ULift.up 0) ⟶ F.obj (ULift.up 1)

noncomputable def scaffoldIntervalPrism (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ F.obj (ULift.up 0) ⟶ simplicialReplacement F

lemma scaffoldIntervalTail_constantLift (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    simplicialReplacementConstantLift (scaffoldFiniteTail 0 ⋙ F) (ULift.up 0) ≫
      simplicialReplacementBaseMap (scaffoldFiniteTail 0) F =
        simplicialReplacementConstantLift F (ULift.up 1)

lemma scaffoldIntervalTail_assembly (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft (scaffoldFiniteTail 0)
      (simplicialReplacementInitialCoefficient F (scaffoldFiniteInitial 1))) =
    snd (nerve (ULift.{u} (Fin 1))) (F.obj (ULift.up 0)) ≫ scaffoldIntervalMap F ≫
      simplicialReplacementConstantLift (scaffoldFiniteTail 0 ⋙ F) (ULift.up 0)

lemma scaffoldIntervalTail_endpoint (K : SSet.{u}) :
    (nerveMap (scaffoldFiniteTail 0) ▷ K) ≫ (stdSimplex.isoNerve.{u} 1).inv ▷ K =
      snd (nerve (ULift.{u} (Fin 1))) K ≫ prismEndpoint 1 K

lemma scaffoldInterval_isPushout (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    IsPushout (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldIntervalMap F)
      (scaffoldIntervalPrism F) (simplicialReplacementConstantLift F (ULift.up 1))

noncomputable def simplicialReplacementIntervalIso (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    simplicialReplacement F ≅
      pushout (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldIntervalMap F)

def leftScaffoldFiberMap {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (c : C) :
    F.obj c ⟶ vertexFiber p (nerveVertex c)

def IsLeftScaffold {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    (l : simplicialReplacement F ⟶ E) : Prop

lemma tautScaffold_isLeftScaffold {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] :
    IsLeftScaffold (weightedNerveProjection F) F (tautScaffold F)

instance leftStrictTransportDiagram_kanComplex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    KanComplex ((leftStrictTransportDiagram p).obj c)

lemma universalScaffold_isLeftScaffold
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    IsLeftScaffold p (leftStrictTransportDiagram p) (universalScaffold p)

lemma vertexFiberTransport_ι {E B : SSet.{u}} (p : E ⟶ B)
    {b b' : B _⦋0⦌} (h : b = b') :
    eqToHom (congrArg (vertexFiber p) h) ≫ vertexFiberι p b' = vertexFiberι p b

noncomputable def vertexFiberNervePullbackIso
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (H : D ⥤ C) (d : D) :
    vertexFiber (pullback.snd p (nerveMap H)) (nerveVertex d) ≅
      vertexFiber p (nerveVertex (H.obj d))

lemma vertexFiberNervePullbackIso_hom_ι
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (H : D ⥤ C) (d : D) :
    (vertexFiberNervePullbackIso p H d).hom ≫ vertexFiberι p (nerveVertex (H.obj d)) =
      vertexFiberι (pullback.snd p (nerveMap H)) (nerveVertex d) ≫ pullback.fst p (nerveMap H)

instance leftFibration_nervePullback
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (H : D ⥤ C) :
    LeftFibration (pullback.snd p (nerveMap H))

lemma simplicialReplacementConstantLift_baseMap
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) (d : D) :
    simplicialReplacementConstantLift (H ⋙ F) d ≫ simplicialReplacementBaseMap H F =
      simplicialReplacementConstantLift F (H.obj d)

noncomputable def leftScaffoldBaseChange
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (H : D ⥤ C) :
    simplicialReplacement (H ⋙ F) ⟶ pullback p (nerveMap H)

lemma leftScaffoldBaseChange_projection
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (H : D ⥤ C) :
    leftScaffoldBaseChange p F l h H ≫ pullback.snd p (nerveMap H) =
      simplicialReplacementProjection (H ⋙ F)

lemma leftScaffoldBaseChange_fiber
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (H : D ⥤ C) (d : D) :
    leftScaffoldFiberMap (pullback.snd p (nerveMap H)) (H ⋙ F) (leftScaffoldBaseChange p F l h H)
        (leftScaffoldBaseChange_projection p F l h H) d ≫ (vertexFiberNervePullbackIso p H d).hom =
      leftScaffoldFiberMap p F l h (H.obj d)

lemma IsLeftScaffold.baseChange
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    {p : E ⟶ nerve C} [LeftFibration p] {F : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)]
    {l : simplicialReplacement F ⟶ E} (hs : IsLeftScaffold p F l) (H : D ⥤ C) :
    ∃ h : l ≫ p = simplicialReplacementProjection F,
      @IsLeftScaffold D _ _ (pullback.snd p (nerveMap H)) inferInstance (H ⋙ F)
        (fun d ↦ inferInstanceAs (KanComplex (F.obj (H.obj d))))
        (leftScaffoldBaseChange p F l h H)

lemma vertexFiberι_isIso_of_nervePoint
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    {E : SSet.{u}} (p : E ⟶ nerve C) (c : C) : IsIso (vertexFiberι p (nerveVertex c))

lemma simplicialReplacementPoint_kanComplex
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    (F : C ⥤ SSet.{u}) (c : C) [KanComplex (F.obj c)] :
    KanComplex (simplicialReplacement F)

lemma IsLeftScaffold.isPrecompositionEquivalence_of_point
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    {E : SSet.{u}} {p : E ⟶ nerve C} [LeftFibration p]
    {F : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)]
    {l : simplicialReplacement F ⟶ E} (hs : IsLeftScaffold p F l) (c : C) :
    IsPrecompositionEquivalence l

lemma leftFibration_hasLiftingProperty_horn_of_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (q : X ⟶ Y) [LeftFibration q]
    (n : ℕ) (i : Fin (n + 2)) : HasLiftingProperty (horn (n + 1) i).ι q

lemma leftFibration_fibration_of_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (q : X ⟶ Y) [LeftFibration q] : Fibration q

lemma hasLiftingProperty_relativeFunctorPre {A D E B T U : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A)
    (r : internalHom.PullbackObjObj i p) (j : T ⟶ U) [HasLiftingProperty j r.π] :
    HasLiftingProperty j (relativeFunctorPre p a i)

instance relativeFunctorPre_leftFibration {A D E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A) [Mono i] :
    LeftFibration (relativeFunctorPre p a i)

lemma relativeFunctorPre_fibration {A D E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A) [Mono i] :
    Fibration (relativeFunctorPre p a i)

instance under_isThin_of_thin
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] (c : C) : Quiver.IsThin (Under c)

lemma underMap_obj_injective_of_thin
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] {c d : C} (f : c ⟶ d) :
    Function.Injective (Under.map f).obj

instance nerveUnderMap_mono_of_thin
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] {c d : C} (f : c ⟶ d) :
    Mono (nerveUnderMap f)

lemma leftStrictTransportMap_fibration_of_thin
    {C : Type u} [Category.{u} C] [Quiver.IsThin C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] {c d : C} (f : c ⟶ d) :
    Fibration (leftStrictTransportMap p f)

def simplicialReplacementSourceCoefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (s : simplicialReplacementSimplex F n)
    (c : C) (h : s.1.obj 0 = c) : (Δ[n] : SSet.{u}) ⟶ F.obj c

lemma simplicialReplacementSourceCoefficient_congr {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} {s t : simplicialReplacementSimplex F n}
    (hst : s = t) (c : C) (h : s.1.obj 0 = c) (h' : t.1.obj 0 = c) :
    simplicialReplacementSourceCoefficient F s c h =
      simplicialReplacementSourceCoefficient F t c h'

lemma simplicialReplacementSimplex_eq_of_sourceCoefficient
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (s t : simplicialReplacementSimplex F n) (hb : s.1 = t.1)
    (c : C) (h : s.1.obj 0 = c) (h' : t.1.obj 0 = c)
    (he : simplicialReplacementSourceCoefficient F s c h =
      simplicialReplacementSourceCoefficient F t c h') : s = t

lemma simplicialReplacementSourceCoefficient_naturality
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {m n : SimplexCategory} (α : m ⟶ n) (hα : α.toOrderHom 0 = 0)
    (s : simplicialReplacementSimplex F n.len) (c : C)
    (h : s.1.obj 0 = c)
    (h' : (simplicialReplacementSimplexMap F α s).1.obj 0 = c) :
    simplicialReplacementSourceCoefficient F (simplicialReplacementSimplexMap F α s) c h' =
      stdSimplex.map α ≫ simplicialReplacementSourceCoefficient F s c h

lemma simplicialReplacementSourceCoefficient_overlap
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {m n r : SimplexCategory} (α : m ⟶ n) (β : m ⟶ r)
    (hα : α.toOrderHom 0 = 0) (hβ : β.toOrderHom 0 = 0)
    (s : simplicialReplacementSimplex F n.len) (t : simplicialReplacementSimplex F r.len)
    (c : C) (hs : s.1.obj 0 = c) (ht : t.1.obj 0 = c)
    (he : simplicialReplacementSimplexMap F α s = simplicialReplacementSimplexMap F β t) :
    stdSimplex.map α ≫ simplicialReplacementSourceCoefficient F s c hs =
      stdSimplex.map β ≫ simplicialReplacementSourceCoefficient F t c ht

lemma simplexFace_zero_of_ne_zero {n : ℕ} (j : Fin (n + 2)) (hj : j ≠ 0) :
    (SimplexCategory.δ j).toOrderHom 0 = 0

lemma simplicialReplacementHornFace_base
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ simplicialReplacement F)
    (ha : a ≫ simplicialReplacementProjection F =
      (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) :
    (SSet.yonedaEquiv (horn.ι k j hj ≫ a)).1 =
      (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ

lemma simplicialReplacementHornFace_start
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ simplicialReplacement F)
    (ha : a ≫ simplicialReplacementProjection F =
      (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) (hj0 : j ≠ 0) :
    (SSet.yonedaEquiv (horn.ι k j hj ≫ a)).1.obj 0 = σ.obj 0

def simplicialReplacementHornSourceFace
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ simplicialReplacement F)
    (ha : a ≫ simplicialReplacementProjection F =
      (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) (hj0 : j ≠ 0) :
    (Δ[n] : SSet.{u}) ⟶ F.obj (σ.obj 0)

lemma simplicialReplacementHornSourceFace_overlap
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {n m : ℕ}
    (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ simplicialReplacement F)
    (ha : a ≫ simplicialReplacementProjection F =
      (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j l : Fin (n + 2)) (hj : j ≠ k) (hl : l ≠ k) (hj0 : j ≠ 0) (hl0 : l ≠ 0)
    (β γ : ⦋m⦌ ⟶ ⦋n⦌) (hβ : β.toOrderHom 0 = 0) (hγ : γ.toOrderHom 0 = 0)
    (he : (stdSimplex.map β : (Δ[m] : SSet.{u}) ⟶ Δ[n]) ≫ (horn.ι k j hj ≫ a) =
      stdSimplex.map γ ≫ (horn.ι k l hl ≫ a)) :
    stdSimplex.map β ≫ simplicialReplacementHornSourceFace F σ k a ha j hj hj0 =
      stdSimplex.map γ ≫ simplicialReplacementHornSourceFace F σ k a ha l hl hl0

lemma simplicialReplacementHornSourceFace_zero_isCompatible
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1))
    (a : (horn (n + 1) 0 : SSet.{u}) ⟶ simplicialReplacement F)
    (ha : a ≫ simplicialReplacementProjection F =
      (horn (n + 1) 0).ι ≫ SSet.yonedaEquiv.symm σ) :
    horn.IsCompatible (fun j hj ↦ simplicialReplacementHornSourceFace F σ 0 a ha j hj hj)

lemma exists_simplicialReplacement_zeroHorn_lift
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) [KanComplex (F.obj (σ.obj 0))]
    (a : (horn (n + 1) 0 : SSet.{u}) ⟶ simplicialReplacement F)
    (ha : a ≫ simplicialReplacementProjection F =
      (horn (n + 1) 0).ι ≫ SSet.yonedaEquiv.symm σ) :
    ∃ H : (Δ[n + 1] : SSet.{u}) ⟶ simplicialReplacement F,
      (horn (n + 1) 0).ι ≫ H = a ∧
        H ≫ simplicialReplacementProjection F = SSet.yonedaEquiv.symm σ

lemma hasLiftingProperty_simplicialReplacementProjection_zeroHorn
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] (n : ℕ) :
    HasLiftingProperty (horn (n + 1) 0).ι (simplicialReplacementProjection F)

noncomputable def joinDiagonalCylinder (K : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ K ⟶ (K ⊗ (Δ[1] : SSet.{u})) ⊗ K

noncomputable def joinDiagonal (K : SSet.{u}) : (Δ[1] : SSet.{u}) ⊗ K ⟶ join K K

lemma prismEndpoint_zero_joinDiagonal (K : SSet.{u}) :
    prismEndpoint 0 K ≫ joinDiagonal K = joinInl K K

lemma prismEndpoint_one_joinDiagonal (K : SSet.{u}) :
    prismEndpoint 1 K ≫ joinDiagonal K = joinInr K K

lemma joinDiagonal_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    ((Δ[1] : SSet.{u}) ◁ f) ≫ joinDiagonal Y = joinDiagonal X ≫ joinMap f f

noncomputable def relativeJoin {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) : SSet.{u}

noncomputable def relativeJoinProjection {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoin f g ⟶ (Δ[1] : SSet.{u})

noncomputable def relativeJoinInl {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    X ⟶ relativeJoin f g

noncomputable def relativeJoinInr {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Y ⟶ relativeJoin f g

lemma relativeJoinInl_fst {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoinInl f g ≫ pullback.fst (joinMap f g) (joinDiagonal S) = joinInl X Y

lemma relativeJoinInr_fst {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoinInr f g ≫ pullback.fst (joinMap f g) (joinDiagonal S) = joinInr X Y

lemma relativeJoinInl_projection {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoinInl f g ≫ relativeJoinProjection f g =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

lemma relativeJoinInr_projection {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoinInr f g ≫ relativeJoinProjection f g =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

noncomputable def relativeJoinPrism {X Y : SSet.{u}} (f : X ⟶ Y) :
    (Δ[1] : SSet.{u}) ⊗ X ⟶ relativeJoin f (𝟙 Y)

lemma relativeJoinPrism_zero {X Y : SSet.{u}} (f : X ⟶ Y) :
    prismEndpoint 0 X ≫ relativeJoinPrism f = relativeJoinInl f (𝟙 Y)

lemma relativeJoinPrism_one {X Y : SSet.{u}} (f : X ⟶ Y) :
    prismEndpoint 1 X ≫ relativeJoinPrism f = f ≫ relativeJoinInr f (𝟙 Y)

lemma relativeJoinPrism_projection {X Y : SSet.{u}} (f : X ⟶ Y) :
    relativeJoinPrism f ≫ relativeJoinProjection f (𝟙 Y) = fst (Δ[1] : SSet.{u}) X

noncomputable def relativeJoinCylinderComparison {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout (prismEndpoint 1 X) f ⟶ relativeJoin f (𝟙 Y)

lemma relativeJoinCylinderComparison_inl {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inl (prismEndpoint 1 X) f ≫ relativeJoinCylinderComparison f = relativeJoinPrism f

lemma relativeJoinCylinderComparison_inr {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inr (prismEndpoint 1 X) f ≫ relativeJoinCylinderComparison f =
      relativeJoinInr f (𝟙 Y)

instance relativeJoinSelf_snd_isIso (S : SSet.{u}) :
    IsIso (pullback.snd (joinMap (𝟙 S) (𝟙 S)) (joinDiagonal S))

noncomputable def relativeJoinSelfIso (S : SSet.{u}) :
    relativeJoin (𝟙 S) (𝟙 S) ≅ (Δ[1] : SSet.{u}) ⊗ S

instance relativeJoinPrism_id_isIso (S : SSet.{u}) : IsIso (relativeJoinPrism (𝟙 S))

instance relativeJoinCylinderComparison_id_isIso (S : SSet.{u}) :
    IsIso (relativeJoinCylinderComparison (𝟙 S))

lemma fatJoinPoint_isPushout (X : SSet.{u}) :
    IsPushout (SSet.ι₁ (X := X) ▷ (Δ[0] : SSet.{u}))
      (snd X (Δ[0] : SSet.{u})) (fatJoinCylinder X Δ[0]) (fatJoinInr X Δ[0])

noncomputable def fatJoinPointCylinderIso (X : SSet.{u}) :
    (X ⊗ (Δ[1] : SSet.{u})) ⊗ (Δ[0] : SSet.{u}) ≅ (Δ[1] : SSet.{u}) ⊗ X

noncomputable def fatJoinPointPrism (X : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ X ⟶ fatJoin X (Δ[0] : SSet.{u})

lemma fatJoinPointPrism_isPushout {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    IsPushout (prismEndpoint 1 X) f (fatJoinPointPrism X) (fatJoinInr X Δ[0])

noncomputable def mappingCylinderFatJoinPointIso {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    pushout (prismEndpoint 1 X) f ≅ fatJoin X (Δ[0] : SSet.{u})

instance joinDiagonalCylinder_point_isIso : IsIso (joinDiagonalCylinder (Δ[0] : SSet.{u}))

instance joinDiagonal_point_isIso : IsIso (joinDiagonal (Δ[0] : SSet.{u}))

instance relativeJoin_point_fst_isIso {X Y : SSet.{u}}
    (f : X ⟶ (Δ[0] : SSet.{u})) (g : Y ⟶ (Δ[0] : SSet.{u})) :
    IsIso (pullback.fst (joinMap f g) (joinDiagonal (Δ[0] : SSet.{u})))

lemma fatJoinPointPrism_comparison {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    fatJoinPointPrism X ≫ fatJoinComparison X (Δ[0] : SSet.{u}) =
      joinDiagonal X ≫ joinMap (𝟙 X) f

lemma relativeJoinCylinderComparison_point_fst {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    relativeJoinCylinderComparison f ≫ pullback.fst (joinMap f (𝟙 (Δ[0] : SSet.{u})))
        (joinDiagonal (Δ[0] : SSet.{u})) =
      (mappingCylinderFatJoinPointIso f).hom ≫ fatJoinComparison X (Δ[0] : SSet.{u})

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_point
    {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison f)

noncomputable def relativeJoinLeftMap {X X' Y S : SSet.{u}} (g : Y ⟶ S)
    {f : X ⟶ S} {f' : X' ⟶ S} (u : X ⟶ X') (h : u ≫ f' = f) :
    relativeJoin f g ⟶ relativeJoin f' g

lemma relativeJoinLeftMap_fst {X X' Y S : SSet.{u}} (g : Y ⟶ S)
    {f : X ⟶ S} {f' : X' ⟶ S} (u : X ⟶ X') (h : u ≫ f' = f) :
    relativeJoinLeftMap g u h ≫ pullback.fst (joinMap f' g) (joinDiagonal S) =
      pullback.fst (joinMap f g) (joinDiagonal S) ≫ joinMap u (𝟙 Y)

lemma relativeJoinLeftMap_snd {X X' Y S : SSet.{u}} (g : Y ⟶ S)
    {f : X ⟶ S} {f' : X' ⟶ S} (u : X ⟶ X') (h : u ≫ f' = f) :
    relativeJoinLeftMap g u h ≫ pullback.snd (joinMap f' g) (joinDiagonal S) =
      pullback.snd (joinMap f g) (joinDiagonal S)

lemma relativeJoinLeftMap_id {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : 𝟙 X ≫ f = f) : relativeJoinLeftMap g (𝟙 X) h = 𝟙 (relativeJoin f g)

lemma relativeJoinLeftMap_comp {X X' X'' Y S : SSet.{u}} (g : Y ⟶ S)
    {f : X ⟶ S} {f' : X' ⟶ S} {f'' : X'' ⟶ S}
    (u : X ⟶ X') (v : X' ⟶ X'') (hu : u ≫ f' = f) (hv : v ≫ f'' = f')
    (h' : (u ≫ v) ≫ f'' = f) :
    relativeJoinLeftMap g (u ≫ v) h' = relativeJoinLeftMap g u hu ≫ relativeJoinLeftMap g v hv

noncomputable def relativeJoinLeftFunctor {Y S : SSet.{u}} (g : Y ⟶ S) :
    Over S ⥤ SSet.{u}

lemma relativeJoinLeftMap_isPullback {X X' Y S : SSet.{u}} (g : Y ⟶ S)
    {f : X ⟶ S} {f' : X' ⟶ S} (u : X ⟶ X') (h : u ≫ f' = f) :
    IsPullback (relativeJoinLeftMap g u h)
      (pullback.fst (joinMap f g) (joinDiagonal S))
      (pullback.fst (joinMap f' g) (joinDiagonal S)) (joinMap u (𝟙 Y))

instance relativeJoinLeftMap_mono {X X' Y S : SSet.{u}} (g : Y ⟶ S)
    {f : X ⟶ S} {f' : X' ⟶ S} (u : X ⟶ X') [Mono u] (h : u ≫ f' = f) :
    Mono (relativeJoinLeftMap g u h)

instance relativeJoinLeftFunctor_preservesMonomorphisms {Y S : SSet.{u}} (g : Y ⟶ S) :
    (relativeJoinLeftFunctor g).PreservesMonomorphisms

lemma relativeJoin_left_isPushout {Y S : SSet.{u}} (g : Y ⟶ S)
    {A B C D : Over S} {u : A ⟶ B} {v : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    [Mono u.left] (hp : IsPushout u.left v.left r.left s.left) :
    IsPushout ((relativeJoinLeftFunctor g).map u) ((relativeJoinLeftFunctor g).map v)
      ((relativeJoinLeftFunctor g).map r) ((relativeJoinLeftFunctor g).map s)

noncomputable def mappingCylinderOverMap {S : SSet.{u}} {A B : Over S} (u : A ⟶ B) :
    pushout (prismEndpoint 1 A.left) A.hom ⟶ pushout (prismEndpoint 1 B.left) B.hom

lemma mappingCylinderOverMap_inl {S : SSet.{u}} {A B : Over S} (u : A ⟶ B) :
    pushout.inl (prismEndpoint 1 A.left) A.hom ≫ mappingCylinderOverMap u =
      ((Δ[1] : SSet.{u}) ◁ u.left) ≫ pushout.inl (prismEndpoint 1 B.left) B.hom

lemma mappingCylinderOverMap_inr {S : SSet.{u}} {A B : Over S} (u : A ⟶ B) :
    pushout.inr (prismEndpoint 1 A.left) A.hom ≫ mappingCylinderOverMap u =
      pushout.inr (prismEndpoint 1 B.left) B.hom

lemma mappingCylinderOverMap_id {S : SSet.{u}} (A : Over S) :
    mappingCylinderOverMap (𝟙 A) = 𝟙 (pushout (prismEndpoint 1 A.left) A.hom)

lemma mappingCylinderOverMap_comp {S : SSet.{u}} {A B C : Over S}
    (u : A ⟶ B) (v : B ⟶ C) :
    mappingCylinderOverMap (u ≫ v) = mappingCylinderOverMap u ≫ mappingCylinderOverMap v

noncomputable def mappingCylinderOverFunctor (S : SSet.{u}) : Over S ⥤ SSet.{u}

noncomputable def mappingCylinderEndpointNat (S : SSet.{u}) :
    Over.forget S ⟶ Over.forget S ⋙ tensorLeft (Δ[1] : SSet.{u})

def mappingCylinderStructureNat (S : SSet.{u}) :
    Over.forget S ⟶ (CategoryTheory.Functor.const (Over S)).obj S

noncomputable def mappingCylinderInlNat (S : SSet.{u}) :
    Over.forget S ⋙ tensorLeft (Δ[1] : SSet.{u}) ⟶ mappingCylinderOverFunctor S

noncomputable def mappingCylinderInrNat (S : SSet.{u}) :
    (CategoryTheory.Functor.const (Over S)).obj S ⟶ mappingCylinderOverFunctor S

instance mappingCylinderOverFunctor_preservesColimitsOfShape (S : SSet.{u})
    (J : Type*) [Category* J] [IsConnected J] [HasColimitsOfShape J SSet.{u}] :
    PreservesColimitsOfShape J (mappingCylinderOverFunctor S)

lemma relativeJoinInr_leftMap {S : SSet.{u}} {A B : Over S} (u : A ⟶ B) :
    relativeJoinInr A.hom (𝟙 S) ≫ relativeJoinLeftMap (𝟙 S) u.left u.w =
      relativeJoinInr B.hom (𝟙 S)

lemma relativeJoinPrism_naturality {S : SSet.{u}} {A B : Over S} (u : A ⟶ B) :
    relativeJoinPrism A.hom ≫ relativeJoinLeftMap (𝟙 S) u.left u.w =
      ((Δ[1] : SSet.{u}) ◁ u.left) ≫ relativeJoinPrism B.hom

lemma relativeJoinCylinderComparison_naturality {S : SSet.{u}} {A B : Over S}
    (u : A ⟶ B) :
    mappingCylinderOverMap u ≫ relativeJoinCylinderComparison B.hom =
      relativeJoinCylinderComparison A.hom ≫ relativeJoinLeftMap (𝟙 S) u.left u.w

noncomputable def relativeJoinCylinderComparisonNat (S : SSet.{u}) :
    mappingCylinderOverFunctor S ⟶ relativeJoinLeftFunctor (𝟙 S)

lemma prismEndpoint_snd (i : Fin 2) (A : SSet.{u}) :
    prismEndpoint i A ≫ snd (Δ[1] : SSet.{u}) A = 𝟙 A

instance prismEndpoint_mono (i : Fin 2) (A : SSet.{u}) : Mono (prismEndpoint i A)

lemma isPullback_prismEndpoint_naturality (i : Fin 2) {A B : SSet.{u}} (f : A ⟶ B) :
    IsPullback (prismEndpoint i A) f ((Δ[1] : SSet.{u}) ◁ f) (prismEndpoint i B)

instance mappingCylinderOverMap_mono {S : SSet.{u}} {A B : Over S}
    (u : A ⟶ B) [Mono u.left] : Mono (mappingCylinderOverMap u)

instance mappingCylinderOverFunctor_preservesMonomorphisms (S : SSet.{u}) :
    (mappingCylinderOverFunctor S).PreservesMonomorphisms

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_of_pushout
    {S : SSet.{u}} {A B C D : Over S} {i : A ⟶ B} {g : A ⟶ C}
    {r : B ⟶ D} {s : C ⟶ D} [Mono i.left] (hp : IsPushout i g r s)
    (hA : IsPrecompositionEquivalence (relativeJoinCylinderComparison A.hom))
    (hB : IsPrecompositionEquivalence (relativeJoinCylinderComparison B.hom))
    (hC : IsPrecompositionEquivalence (relativeJoinCylinderComparison C.hom)) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison D.hom)

lemma joinDiagonal_app_cut (Y : SSet.{u}) (n : ℕ)
    (t : (Δ[1] : SSet.{u}) _⦋n⦌) (a : Y _⦋n⦌) :
    ((joinDiagonal Y).app (Opposite.op ⦋n⦌) (t, a)).1.val =
      Join.pullCut (stdSimplex.objEquiv t).toOrderHom 1

lemma joinDiagonal_eq_inr_iff (Y : SSet.{u}) (n : ℕ)
    (z : ((Δ[1] : SSet.{u}) ⊗ Y) _⦋n⦌) (b : Y _⦋n⦌) :
    (joinDiagonal Y).app (Opposite.op ⦋n⦌) z =
        (joinInr Y Y).app (Opposite.op ⦋n⦌) b ↔
      z = (prismEndpoint 1 Y).app (Opposite.op ⦋n⦌) b

lemma isPullback_joinDiagonal_inr (Y : SSet.{u}) :
    IsPullback (prismEndpoint 1 Y) (𝟙 Y) (joinDiagonal Y) (joinInr Y Y)

instance relativeJoin_joinInr_emptySource_isIso (X Y : SSet.{u})
    [∀ n, IsEmpty (X.obj n)] : IsIso (joinInr X Y)

instance relativeJoinInr_emptySource_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    [∀ n, IsEmpty (X.obj n)] : IsIso (relativeJoinInr f (𝟙 Y))

instance relativeJoin_prismEndpoint_empty_isIso (i : Fin 2) (X : SSet.{u})
    [∀ n, IsEmpty (X.obj n)] : IsIso (prismEndpoint i X)

instance relativeJoinCylinderComparison_emptySource_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    [∀ n, IsEmpty (X.obj n)] : IsIso (relativeJoinCylinderComparison f)

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_emptySource
    {X Y : SSet.{u}} (f : X ⟶ Y) [∀ n, IsEmpty (X.obj n)] :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison f)

lemma joinDiagonal_stdSimplex_val (n d : ℕ)
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) (a : (Δ[n] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    ((joinStdSimplexIso n n).hom.app (Opposite.op ⦋d⦌)
      ((joinDiagonal Δ[n]).app (Opposite.op ⦋d⦌) (t, a)) i).val =
        if (t i).val = 0 then (a i).val else n + 1 + (a i).val

instance joinDiagonal_stdSimplex_mono (n : ℕ) : Mono (joinDiagonal (Δ[n] : SSet.{u}))

instance relativeJoin_fst_stdSimplex_mono {X Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ (Δ[n] : SSet.{u})) (g : Y ⟶ (Δ[n] : SSet.{u})) :
    Mono (pullback.fst (joinMap f g) (joinDiagonal Δ[n]))

lemma join_prefix_mem_boundary {Y : SSet.{u}} {m d : ℕ} (c : Fin (d + 2))
    (a : (Δ[m] : SSet.{u}) _⦋d⦌) (b : Y _⦋d⦌)
    (h : ∀ i : Fin (d + 1), i.val < c.val → a i ≠ Fin.last m) :
    (⟨c, Join.augMap Δ[m] (Join.prefixIncl (d + 1) c.val
          (Nat.le_of_lt_succ c.isLt)) a,
        Join.augMap Y (Join.suffixIncl (d + 1) c.val
          (Nat.le_of_lt_succ c.isLt)) b⟩ : Join.Simplex Δ[m] Y d) ∈
      (joinSubcomplexLeft (boundary m) Y).obj (Opposite.op ⦋d⦌)

lemma relativeJoinPrism_fst_app {X Y : SSet.{u}} (f : X ⟶ Y) (d : ℕ)
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) (a : X _⦋d⦌) :
    (pullback.fst (joinMap f (𝟙 Y)) (joinDiagonal Y)).app (Opposite.op ⦋d⦌)
        ((relativeJoinPrism f).app (Opposite.op ⦋d⦌) (t, a)) =
      (joinCylinderMap X Y).app (Opposite.op ⦋d⦌) ((a, t), f.app _ a)

lemma relativeJoinPrism_mem_boundary_of_no_last_zero {Y : SSet.{u}} {m d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) (t : (Δ[1] : SSet.{u}) _⦋d⦌)
    (a : (Δ[m] : SSet.{u}) _⦋d⦌)
    (h : ∀ i : Fin (d + 1), (t i).val = 0 → a i ≠ Fin.last m) :
    (relativeJoinPrism f).app (Opposite.op ⦋d⦌) (t, a) ∈ Set.range
      ((relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl).app
          (Opposite.op ⦋d⦌))

noncomputable def relativeJoinPrismShuffle (m : ℕ) (k : Fin (m + 1)) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]) _⦋m + 1⦌

lemma relativeJoinPrismShuffle_no_last_zero (m : ℕ) (k : Fin (m + 1))
    (hk : k < Fin.last m) (i : Fin (m + 2))
    (hi : ((relativeJoinPrismShuffle.{u} m k).1 i).val = 0) :
    (relativeJoinPrismShuffle.{u} m k).2 i ≠ Fin.last m

lemma relativeJoinPrismShuffle_mem_boundary {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) (k : Fin (m + 1)) (hk : k < Fin.last m) :
    (relativeJoinPrism f).app (Opposite.op ⦋m + 1⦌) (relativeJoinPrismShuffle.{u} m k) ∈
      Set.range ((relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl).app (Opposite.op ⦋m + 1⦌))

noncomputable def relativeJoinPrismShuffleBoundaryLift {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) (k : Fin (m + 1)) (hk : k < Fin.last m) :
    (Δ[m + 1] : SSet.{u}) ⟶ relativeJoin ((boundary m).ι ≫ f) (𝟙 Y)

lemma relativeJoinPrismShuffleBoundaryLift_comp {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) (k : Fin (m + 1)) (hk : k < Fin.last m) :
    relativeJoinPrismShuffleBoundaryLift f k hk ≫
        relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl =
      SSet.yonedaEquiv.symm (relativeJoinPrismShuffle.{u} m k) ≫ relativeJoinPrism f

noncomputable def relativeJoinPrismInitial (m : ℕ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).Subcomplex

noncomputable def relativeJoinPrismPenultimate (m : ℕ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).Subcomplex

lemma relativeJoinPrismInitial_le_penultimate (m : ℕ) :
    relativeJoinPrismInitial.{u} m ≤ relativeJoinPrismPenultimate m

lemma relativeJoinPrismPenultimate_le_boundary_preimage {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    relativeJoinPrismPenultimate m ≤
      (Subcomplex.range (relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl)).preimage (relativeJoinPrism f)

lemma relativeJoinPrismPenultimate_range_le {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    Subcomplex.range ((relativeJoinPrismPenultimate m).ι ≫ relativeJoinPrism f) ≤
      Subcomplex.range (relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl)

noncomputable def relativeJoinPrismPenultimateBoundaryLift {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    (relativeJoinPrismPenultimate m : SSet.{u}) ⟶
      relativeJoin ((boundary m).ι ≫ f) (𝟙 Y)

lemma relativeJoinPrismPenultimateBoundaryLift_comp {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    relativeJoinPrismPenultimateBoundaryLift f ≫
        relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl =
      (relativeJoinPrismPenultimate m).ι ≫ relativeJoinPrism f

lemma relativeJoinPrismShuffle_time_zero_iff (m : ℕ) (k : Fin (m + 1))
    (i : Fin (m + 2)) :
    ((relativeJoinPrismShuffle.{u} m k).1 i).val = 0 ↔ i ≤ k.castSucc

lemma relativeJoinPrismShuffle_coefficient_val (m : ℕ) (k : Fin (m + 1))
    (i : Fin (m + 2)) :
    ((relativeJoinPrismShuffle.{u} m k).2 i).val =
      if i ≤ k.castSucc then i.val else i.val - 1

lemma relativeJoinPrismShuffle_vertex_sum (m : ℕ) (k : Fin (m + 1))
    (i : Fin (m + 2)) :
    ((relativeJoinPrismShuffle.{u} m k).1 i).val +
      ((relativeJoinPrismShuffle.{u} m k).2 i).val = i.val

lemma relativeJoinPrismShuffle_vertex_injective (m : ℕ) (k : Fin (m + 1)) :
    Function.Injective (fun i : Fin (m + 2) ↦
      ((relativeJoinPrismShuffle.{u} m k).1 i, (relativeJoinPrismShuffle.{u} m k).2 i))

instance relativeJoinPrismShuffle_mono (m : ℕ) (k : Fin (m + 1)) :
    Mono (SSet.yonedaEquiv.symm (relativeJoinPrismShuffle.{u} m k))

noncomputable def relativeJoinPrismStage (m r : ℕ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).Subcomplex

lemma relativeJoinPrismStage_zero (m : ℕ) :
    relativeJoinPrismStage.{u} m 0 = relativeJoinPrismInitial m

lemma relativeJoinPrismStage_penultimate (m : ℕ) :
    relativeJoinPrismStage.{u} m m = relativeJoinPrismPenultimate m

lemma relativeJoinPrismStage_monotone (m : ℕ) :
    Monotone (relativeJoinPrismStage.{u} m)

lemma relativeJoinPrismStage_succ (m : ℕ) (k : Fin (m + 1)) :
    relativeJoinPrismStage.{u} m (k.val + 1) =
      relativeJoinPrismStage m k.val ⊔ Subcomplex.ofSimplex (relativeJoinPrismShuffle m k)

lemma relativeJoinPrismInitial_preimage_shuffle_le_horn (m : ℕ) (k : Fin (m + 1)) :
    (relativeJoinPrismInitial m).preimage
        (SSet.yonedaEquiv.symm (relativeJoinPrismShuffle.{u} m k)) ≤ horn (m + 1) k.succ

lemma relativeJoinPrismShuffle_preimage_previous_le_face (m : ℕ) (j k : Fin (m + 1))
    (hjk : j < k) :
    (Subcomplex.ofSimplex (relativeJoinPrismShuffle.{u} m j)).preimage
        (SSet.yonedaEquiv.symm (relativeJoinPrismShuffle m k)) ≤
      stdSimplex.face {k.castSucc}ᶜ

lemma relativeJoinPrismStage_preimage_shuffle_le_horn (m : ℕ) (k : Fin (m + 1)) :
    (relativeJoinPrismStage m k.val).preimage
        (SSet.yonedaEquiv.symm (relativeJoinPrismShuffle.{u} m k)) ≤ horn (m + 1) k.succ

lemma relativeJoinPrismShuffle_coefficient_fiber_singleton (m : ℕ) (k : Fin (m + 1))
    (i j : Fin (m + 2)) (hi₀ : i ≠ k.castSucc) (hi₁ : i ≠ k.succ)
    (h : (relativeJoinPrismShuffle.{u} m k).2 j =
      (relativeJoinPrismShuffle.{u} m k).2 i) : j = i

lemma relativeJoinPrismShuffle_face_coefficient_mem_boundary (m : ℕ) (k : Fin (m + 1))
    (i : Fin (m + 2)) (hi₀ : i ≠ k.castSucc) (hi₁ : i ≠ k.succ) :
    (((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ i (relativeJoinPrismShuffle.{u} m k)).2 ∈
      (boundary m).obj (Opposite.op ⦋m⦌)

lemma relativeJoinPrismShuffle_face_mem_initial (m : ℕ) (k : Fin (m + 1))
    (i : Fin (m + 2)) (hi₀ : i ≠ k.castSucc) (hi₁ : i ≠ k.succ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ i (relativeJoinPrismShuffle.{u} m k) ∈
      (relativeJoinPrismInitial m).obj (Opposite.op ⦋m⦌)

lemma relativeJoinPrismShuffle_shared_face (m : ℕ) (j : Fin m) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ j.succ.castSucc
        (relativeJoinPrismShuffle m j.succ) =
      ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ j.castSucc.succ
        (relativeJoinPrismShuffle m j.castSucc)

lemma relativeJoinPrismShuffle_zero_face_mem_initial (m : ℕ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ 0 (relativeJoinPrismShuffle m 0) ∈
      (relativeJoinPrismInitial m).obj (Opposite.op ⦋m⦌)

lemma relativeJoinPrismShuffle_switch_face_mem_stage (m : ℕ) (k : Fin (m + 1)) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ k.castSucc (relativeJoinPrismShuffle m k) ∈
      (relativeJoinPrismStage m k.val).obj (Opposite.op ⦋m⦌)

lemma relativeJoinPrismShuffle_face_mem_stage (m : ℕ) (k : Fin (m + 1))
    (i : Fin (m + 2)) (hi : i ≠ k.succ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).δ i (relativeJoinPrismShuffle m k) ∈
      (relativeJoinPrismStage m k.val).obj (Opposite.op ⦋m⦌)

lemma relativeJoinPrismStage_preimage_shuffle_eq_horn (m : ℕ) (k : Fin (m + 1)) :
    (relativeJoinPrismStage m k.val).preimage
        (SSet.yonedaEquiv.symm (relativeJoinPrismShuffle.{u} m k)) = horn (m + 1) k.succ

lemma isPushout_prism_mono_cell {X V : SSet.{u}} (A B : X.Subcomplex)
    (P : V.Subcomplex) (σ : V ⟶ X) [Mono σ]
    (hB : A ⊔ Subcomplex.range σ = B) (hP : P = A.preimage σ)
    (a : (P : SSet.{u}) ⟶ A) (b : V ⟶ B)
    (ha : a ≫ A.ι = P.ι ≫ σ) (hb : b ≫ B.ι = σ) :
    IsPushout P.ι a b (Subcomplex.homOfLE (hB ▸ le_sup_left))

lemma relativeJoinPrismShuffle_range (m : ℕ) (k : Fin (m + 1)) :
    Subcomplex.range (SSet.yonedaEquiv.symm (relativeJoinPrismShuffle.{u} m k)) =
      Subcomplex.ofSimplex (relativeJoinPrismShuffle m k)

noncomputable def relativeJoinPrismCellHorn (m : ℕ) (k : Fin (m + 1)) :
    (horn (m + 1) k.succ : SSet.{u}) ⟶ relativeJoinPrismStage m k.val

noncomputable def relativeJoinPrismCellSimplex (m : ℕ) (k : Fin (m + 1)) :
    (Δ[m + 1] : SSet.{u}) ⟶ relativeJoinPrismStage m (k.val + 1)

lemma relativeJoinPrismCell_isPushout (m : ℕ) (k : Fin (m + 1)) :
    IsPushout (horn (m + 1) k.succ).ι (relativeJoinPrismCellHorn m k)
      (relativeJoinPrismCellSimplex m k)
      (Subcomplex.homOfLE (relativeJoinPrismStage_monotone m (Nat.le_succ k.val)))

lemma innerAnodyneExtensions_relativeJoinPrismStage_step (m : ℕ) (k : Fin (m + 1))
    (hk : k < Fin.last m) :
    innerAnodyneExtensions (Subcomplex.homOfLE
      (relativeJoinPrismStage_monotone.{u} m (Nat.le_succ k.val)))

lemma innerAnodyneExtensions_relativeJoinPrismStage (m r : ℕ) (hr : r ≤ m) :
    innerAnodyneExtensions (Subcomplex.homOfLE
      (relativeJoinPrismStage_monotone.{u} m (Nat.zero_le r)))

lemma innerAnodyneExtensions_relativeJoinPrismInitial_penultimate (m : ℕ) :
    innerAnodyneExtensions (Subcomplex.homOfLE
      (relativeJoinPrismInitial_le_penultimate.{u} m))

lemma isPrecompositionEquivalence_relativeJoinPrismInitial_penultimate (m : ℕ) :
    IsPrecompositionEquivalence (Subcomplex.homOfLE
      (relativeJoinPrismInitial_le_penultimate.{u} m))

lemma relativeJoinPrismStage_top (m : ℕ) :
    relativeJoinPrismStage.{u} m (m + 1) = ⊤

lemma relativeJoinPrismPenultimate_sup_last (m : ℕ) :
    relativeJoinPrismPenultimate.{u} m ⊔
        Subcomplex.ofSimplex (relativeJoinPrismShuffle m (Fin.last m)) = ⊤

lemma relativeJoinPrismPenultimate_or_last (m d : ℕ)
    (z : ((Δ[1] : SSet.{u}) ⊗ Δ[m]) _⦋d⦌) :
    z ∈ (relativeJoinPrismPenultimate m).obj (Opposite.op ⦋d⦌) ∨
      ∃ a : (Δ[m + 1] : SSet.{u}) _⦋d⦌,
        (SSet.yonedaEquiv.symm (relativeJoinPrismShuffle m (Fin.last m))).app
          (Opposite.op ⦋d⦌) a = z

lemma join_left_boundary_exists_missing_vertex {Y : SSet.{u}} {m d : ℕ}
    (s : Join.Simplex (Δ[m] : SSet.{u}) Y d)
    (hs : s ∈ (joinSubcomplexLeft (boundary m) Y).obj (Opposite.op ⦋d⦌)) :
    ∃ v : Fin (m + 1), ∀ i : Fin s.1.val, (Join.stdAugEquiv m _ s.2.1) i ≠ v

lemma joinCylinderMap_left_boundary_exists_missing_vertex {Y : SSet.{u}} {m d : ℕ}
    (a : (Δ[m] : SSet.{u}) _⦋d⦌) (t : (Δ[1] : SSet.{u}) _⦋d⦌) (b : Y _⦋d⦌)
    (hs : (joinCylinderMap Δ[m] Y).app (Opposite.op ⦋d⦌) ((a, t), b) ∈
      (joinSubcomplexLeft (boundary m) Y).obj (Opposite.op ⦋d⦌)) :
    ∃ v : Fin (m + 1), ∀ i : Fin (d + 1), (t i).val = 0 → a i ≠ v

lemma relativeJoinPrism_boundary_exists_missing_vertex {Y : SSet.{u}} {m d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) (t : (Δ[1] : SSet.{u}) _⦋d⦌)
    (a : (Δ[m] : SSet.{u}) _⦋d⦌)
    (h : (relativeJoinPrism f).app (Opposite.op ⦋d⦌) (t, a) ∈ Set.range
      ((relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl).app (Opposite.op ⦋d⦌))) :
    ∃ v : Fin (m + 1), ∀ i : Fin (d + 1), (t i).val = 0 → a i ≠ v

lemma relativeJoinPrismShuffle_last_left_vertex (m : ℕ) (v : Fin (m + 1)) :
    ((relativeJoinPrismShuffle.{u} m (Fin.last m)).1 v.castSucc,
      (relativeJoinPrismShuffle.{u} m (Fin.last m)).2 v.castSucc) = (0, v)

lemma relativeJoinPrism_last_boundary_mem_horn {Y : SSet.{u}} {m d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) (a : (Δ[m + 1] : SSet.{u}) _⦋d⦌)
    (h : (relativeJoinPrism f).app (Opposite.op ⦋d⦌)
        ((SSet.yonedaEquiv.symm (relativeJoinPrismShuffle m (Fin.last m))).app
          (Opposite.op ⦋d⦌) a) ∈ Set.range
      ((relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl).app (Opposite.op ⦋d⦌))) :
    a ∈ (horn (m + 1) (Fin.last m).succ).obj (Opposite.op ⦋d⦌)

lemma relativeJoinPrism_boundary_preimage_eq_penultimate {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    (Subcomplex.range (relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl)).preimage (relativeJoinPrism f) =
      relativeJoinPrismPenultimate m

lemma relativeJoinPrismPenultimateBoundaryLift_isPullback {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    IsPullback (relativeJoinPrismPenultimateBoundaryLift f) (relativeJoinPrismPenultimate m).ι
      (relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl)
      (relativeJoinPrism f)

instance relativeJoinPrism_lastCell_mono {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    Mono (SSet.yonedaEquiv.symm (relativeJoinPrismShuffle m (Fin.last m)) ≫
      relativeJoinPrism f)

lemma relativeJoinPrism_injective_outside_penultimate {m n d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (x y : ((Δ[1] : SSet.{u}) ⊗ Δ[m]) _⦋d⦌)
    (hx : x ∉ (relativeJoinPrismPenultimate m).obj (Opposite.op ⦋d⦌))
    (hy : y ∉ (relativeJoinPrismPenultimate m).obj (Opposite.op ⦋d⦌))
    (h : (relativeJoinPrism f).app (Opposite.op ⦋d⦌) x =
      (relativeJoinPrism f).app (Opposite.op ⦋d⦌) y) : x = y

lemma relativeJoin_stdSimplex_hom_apply {m n d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) (a : (Δ[m] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    f.app (Opposite.op ⦋d⦌) a i = (SSet.yonedaEquiv f) (a i)

lemma relativeJoin_stdAugHom_apply {m n r : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) (a : Join.augObj (Δ[m] : SSet.{u}) r) (i : Fin r) :
    Join.stdAugEquiv n r (Join.augHom f r a) i =
      (SSet.yonedaEquiv f) (Join.stdAugEquiv m r a i)

lemma relativeJoin_stdSimplex_join_prefix_val {m n d : ℕ}
    (s : Join.Simplex (Δ[m] : SSet.{u}) Δ[n] d) (i : Fin s.1.val) :
    ((joinStdSimplexIso m n).hom.app (Opposite.op ⦋d⦌) s
      (Join.prefixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i)).val =
      (Join.stdAugEquiv m _ s.2.1 i).val

lemma relativeJoin_stdSimplex_join_suffix_val {m n d : ℕ}
    (s : Join.Simplex (Δ[m] : SSet.{u}) Δ[n] d) (i : Fin (d + 1 - s.1.val)) :
    ((joinStdSimplexIso m n).hom.app (Opposite.op ⦋d⦌) s
      (Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i)).val =
      m + 1 + (Join.stdAugEquiv n _ s.2.2 i).val

lemma relativeJoin_not_left_boundary_surjective {Y : SSet.{u}} {m d : ℕ}
    (s : Join.Simplex (Δ[m] : SSet.{u}) Y d)
    (hs : s ∉ (joinSubcomplexLeft (boundary m) Y).obj (Opposite.op ⦋d⦌)) :
    Function.Surjective (Join.stdAugEquiv m _ s.2.1)

lemma relativeJoin_stdSimplex_right_tail_last {m n d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last n)
    (s : Join.Simplex (Δ[m] : SSet.{u}) Δ[n] d)
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) (c : (Δ[n] : SSet.{u}) _⦋d⦌)
    (h : (joinMap f (𝟙 Δ[n])).app (Opposite.op ⦋d⦌) s =
      (joinDiagonal Δ[n]).app (Opposite.op ⦋d⦌) (t, c))
    (hs : s ∉ (joinSubcomplexLeft (boundary m) Δ[n]).obj (Opposite.op ⦋d⦌)) :
    ∀ j : Fin (d + 1 - s.1.val), Join.stdAugEquiv n _ s.2.2 j = Fin.last n

lemma relativeJoinPrism_lastCell_stdSimplex_val {m n d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last n)
    (a : (Δ[m + 1] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    ((joinStdSimplexIso m n).hom.app (Opposite.op ⦋d⦌)
      ((pullback.fst (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n])).app (Opposite.op ⦋d⦌)
        ((relativeJoinPrism f).app (Opposite.op ⦋d⦌)
          ((SSet.yonedaEquiv.symm (relativeJoinPrismShuffle m (Fin.last m))).app
            (Opposite.op ⦋d⦌) a))) i).val =
      if (a i).val ≤ m then (a i).val else m + 1 + n

noncomputable def relativeJoinLastCellLiftSimplex {m n d : ℕ}
    (s : Join.Simplex (Δ[m] : SSet.{u}) Δ[n] d) : (Δ[m + 1] : SSet.{u}) _⦋d⦌

lemma relativeJoinLastCellLiftSimplex_fst {m n d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last n)
    (s : Join.Simplex (Δ[m] : SSet.{u}) Δ[n] d)
    (hs : ∀ j : Fin (d + 1 - s.1.val), Join.stdAugEquiv n _ s.2.2 j = Fin.last n) :
    (pullback.fst (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n])).app (Opposite.op ⦋d⦌)
      ((relativeJoinPrism f).app (Opposite.op ⦋d⦌)
        ((SSet.yonedaEquiv.symm (relativeJoinPrismShuffle m (Fin.last m))).app
          (Opposite.op ⦋d⦌) (relativeJoinLastCellLiftSimplex s))) = s

lemma relativeJoin_stdSimplex_boundary_or_prism {m n d : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last n)
    (z : (relativeJoin f (𝟙 Δ[n])) _⦋d⦌) :
    z ∈ Set.range ((relativeJoinLeftMap (𝟙 Δ[n]) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl).app (Opposite.op ⦋d⦌)) ∨
      z ∈ Set.range ((relativeJoinPrism f).app (Opposite.op ⦋d⦌))

lemma relativeJoin_stdSimplex_prism_isPushout {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last n) :
    IsPushout (relativeJoinPrismPenultimateBoundaryLift f) (relativeJoinPrismPenultimate m).ι
      (relativeJoinLeftMap (𝟙 Δ[n]) (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl)
      (relativeJoinPrism f)

noncomputable def relativeJoinPrismInitialBoundary (m : ℕ) :
    (Δ[1] : SSet.{u}) ⊗ (boundary m : SSet.{u}) ⟶ relativeJoinPrismInitial m

noncomputable def relativeJoinPrismInitialEndpoint (m : ℕ) :
    (Δ[m] : SSet.{u}) ⟶ relativeJoinPrismInitial m

lemma relativeJoinPrismInitial_isPushout (m : ℕ) :
    IsPushout (prismEndpoint 1 (boundary m : SSet.{u})) (boundary m).ι
      (relativeJoinPrismInitialBoundary m) (relativeJoinPrismInitialEndpoint m)

noncomputable def relativeJoinBoundaryCylinderMap {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    pushout (prismEndpoint 1 (boundary m : SSet.{u})) ((boundary m).ι ≫ f) ⟶
      pushout (prismEndpoint 1 (Δ[m] : SSet.{u})) f

lemma relativeJoinBoundaryCylinderMap_inl {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    pushout.inl (prismEndpoint 1 (boundary m : SSet.{u})) ((boundary m).ι ≫ f) ≫
        relativeJoinBoundaryCylinderMap f =
      ((Δ[1] : SSet.{u}) ◁ (boundary m).ι) ≫ pushout.inl (prismEndpoint 1 Δ[m]) f

lemma relativeJoinBoundaryCylinderMap_inr {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    pushout.inr (prismEndpoint 1 (boundary m : SSet.{u})) ((boundary m).ι ≫ f) ≫
        relativeJoinBoundaryCylinderMap f = pushout.inr (prismEndpoint 1 Δ[m]) f

noncomputable def relativeJoinPrismInitialCylinderMap {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    (relativeJoinPrismInitial m : SSet.{u}) ⟶
      pushout (prismEndpoint 1 (boundary m : SSet.{u})) ((boundary m).ι ≫ f)

lemma relativeJoinPrismInitialCylinderMap_boundary {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    relativeJoinPrismInitialBoundary m ≫ relativeJoinPrismInitialCylinderMap f =
      pushout.inl (prismEndpoint 1 (boundary m : SSet.{u})) ((boundary m).ι ≫ f)

lemma relativeJoinPrismInitialCylinderMap_endpoint {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    relativeJoinPrismInitialEndpoint m ≫ relativeJoinPrismInitialCylinderMap f =
      f ≫ pushout.inr (prismEndpoint 1 (boundary m : SSet.{u})) ((boundary m).ι ≫ f)

lemma relativeJoinPrismInitialCylinderMap_square {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    relativeJoinPrismInitialCylinderMap f ≫ relativeJoinBoundaryCylinderMap f =
      (relativeJoinPrismInitial m).ι ≫ pushout.inl (prismEndpoint 1 Δ[m]) f

lemma relativeJoinCylinder_front_isPushout {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    IsPushout (relativeJoinPrismInitialCylinderMap f) (relativeJoinPrismInitial m).ι
      (relativeJoinBoundaryCylinderMap f)
      (pushout.inl (prismEndpoint 1 Δ[m]) f)

lemma relativeJoinBoundaryCylinderComparison_naturality {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    relativeJoinCylinderComparison ((boundary m).ι ≫ f) ≫
        relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl =
      relativeJoinBoundaryCylinderMap f ≫ relativeJoinCylinderComparison f

lemma relativeJoinCylinder_boundary_cube {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    relativeJoinPrismInitialCylinderMap f ≫ relativeJoinCylinderComparison ((boundary m).ι ≫ f) =
      Subcomplex.homOfLE (relativeJoinPrismInitial_le_penultimate m) ≫
        relativeJoinPrismPenultimateBoundaryLift f

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_lastVertex_of_boundary
    {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) = Fin.last n)
    (hboundary : IsPrecompositionEquivalence
      (relativeJoinCylinderComparison ((boundary m).ι ≫ f))) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison f)

noncomputable def stdSimplexLastFaceOrderHom {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) < Fin.last (n + 1)) :
    Fin (m + 1) →o Fin (n + 1)

noncomputable def stdSimplexLastFaceFactor {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) < Fin.last (n + 1)) :
    (Δ[m] : SSet.{u}) ⟶ Δ[n]

lemma stdSimplexLastFaceFactor_comp {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) < Fin.last (n + 1)) :
    stdSimplexLastFaceFactor f hf ≫ stdSimplex.δ (Fin.last (n + 1)) = f

noncomputable def relativeJoinBaseMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    relativeJoin f (𝟙 Y) ⟶ relativeJoin (f ≫ h) (𝟙 Z)

lemma relativeJoinBaseMap_fst {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    relativeJoinBaseMap f h ≫ pullback.fst (joinMap (f ≫ h) (𝟙 Z)) (joinDiagonal Z) =
      pullback.fst (joinMap f (𝟙 Y)) (joinDiagonal Y) ≫ joinMap (𝟙 X) h

lemma relativeJoinBaseMap_snd {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    relativeJoinBaseMap f h ≫ pullback.snd (joinMap (f ≫ h) (𝟙 Z)) (joinDiagonal Z) =
      pullback.snd (joinMap f (𝟙 Y)) (joinDiagonal Y) ≫ ((Δ[1] : SSet.{u}) ◁ h)

instance relativeJoinBaseMap_stdSimplex_mono {X Z : SSet.{u}} {n : ℕ}
    (f : X ⟶ (Δ[n] : SSet.{u})) (h : (Δ[n] : SSet.{u}) ⟶ Z) [Mono h] :
    Mono (relativeJoinBaseMap f h)

lemma relativeJoinCone_hom_ext_stdSimplex {A B : SSet.{u}} {n : ℕ}
    {f g : join A B ⟶ (Δ[n] : SSet.{u})}
    (hA : joinInl A B ≫ f = joinInl A B ≫ g)
    (hB : joinInr A B ≫ f = joinInr A B ≫ g) : f = g

lemma relativeJoinCone_stdSimplex_inl (n : ℕ) :
    joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso n 0).hom =
      stdSimplex.δ (Fin.last (n + 1))

lemma relativeJoinCone_stdSimplex_inr (n : ℕ) :
    joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso n 0).hom =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)))

noncomputable def relativeJoinConeTime : join (Δ[1] : SSet.{u}) Δ[0] ⟶ Δ[1]

lemma relativeJoinConeTime_inl :
    joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ relativeJoinConeTime = 𝟙 Δ[1]

lemma relativeJoinConeTime_inr :
    joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ relativeJoinConeTime =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

noncomputable def relativeJoinConeFirst {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    join (relativeJoin f (𝟙 Δ[n])) Δ[0] ⟶ join (Δ[m] : SSet.{u}) Δ[n + 1]

lemma relativeJoinConeFirst_inl {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    joinInl (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫ relativeJoinConeFirst f =
      pullback.fst (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n]) ≫
        joinMap (𝟙 Δ[m]) (stdSimplex.δ (Fin.last (n + 1)))

lemma relativeJoinConeFirst_inr {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    joinInr (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫ relativeJoinConeFirst f =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫
        joinInr (Δ[m] : SSet.{u}) Δ[n + 1]

instance relativeJoinConeFirst_mono {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    Mono (relativeJoinConeFirst f)

noncomputable def relativeJoinConeSecond {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    join (relativeJoin f (𝟙 Δ[n])) Δ[0] ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[n + 1]

lemma relativeJoinConeSecond_inl {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    joinInl (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫ relativeJoinConeSecond f =
      pullback.snd (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n]) ≫
        ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (Fin.last (n + 1)))

lemma relativeJoinConeSecond_inr {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    joinInr (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫ relativeJoinConeSecond f =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫
        prismEndpoint 1 (Δ[n + 1] : SSet.{u})

lemma relativeJoinCone_condition {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinConeFirst f ≫ joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]) =
      relativeJoinConeSecond f ≫ joinDiagonal Δ[n + 1]

noncomputable def relativeJoinConeMap {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    join (relativeJoin f (𝟙 Δ[n])) Δ[0] ⟶
      relativeJoin (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])

lemma relativeJoinConeMap_fst {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinConeMap f ≫
        pullback.fst (joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]))
          (joinDiagonal Δ[n + 1]) = relativeJoinConeFirst f

lemma relativeJoinConeMap_snd {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinConeMap f ≫
        pullback.snd (joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]))
          (joinDiagonal Δ[n + 1]) = relativeJoinConeSecond f

instance relativeJoinConeMap_mono {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    Mono (relativeJoinConeMap f)

lemma join_augHom_isPullback {P A B C : SSet.{u}}
    {a : P ⟶ A} {b : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsPullback a b f g) (r : ℕ) :
    IsPullback (↾(Join.augHom a r)) (↾(Join.augHom b r))
      (↾(Join.augHom f r)) (↾(Join.augHom g r))

lemma join_left_isPullback {P A B C : SSet.{u}}
    {a : P ⟶ A} {b : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsPullback a b f g) (K : SSet.{u}) :
    IsPullback (joinMap a (𝟙 K)) (joinMap b (𝟙 K))
      (joinMap f (𝟙 K)) (joinMap g (𝟙 K))

noncomputable def prismRightConeMap (n : ℕ) :
    join ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[n + 1]

lemma relativeJoinConeSecond_factor {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinConeSecond f =
      joinMap (pullback.snd (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n])) (𝟙 Δ[0]) ≫
        prismRightConeMap n

instance relativeJoinConeSecond_id_mono (n : ℕ) :
    Mono (relativeJoinConeSecond (𝟙 (Δ[n] : SSet.{u})))

instance prismRightConeMap_mono (n : ℕ) : Mono (prismRightConeMap.{u} n)

lemma prismRightConeMap_time_prefix {n d : ℕ}
    (s : Join.Simplex ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] d) (i : Fin s.1.val) :
    ((prismRightConeMap n).app (Opposite.op ⦋d⦌) s).1
        (Join.prefixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i) =
      Join.stdAugEquiv 1 _ (Join.augHom (fst (Δ[1] : SSet.{u}) Δ[n]) _ s.2.1) i

lemma prismRightConeMap_time_suffix {n d : ℕ}
    (s : Join.Simplex ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] d)
    (i : Fin (d + 1 - s.1.val)) :
    ((prismRightConeMap n).app (Opposite.op ⦋d⦌) s).1
        (Join.suffixIncl (d + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) i) = 1

lemma prismRightConeMap_mem_range {n d : ℕ}
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) (c : (Δ[n + 1] : SSet.{u}) _⦋d⦌)
    (h : ∀ i : Fin (d + 1), c i = Fin.last (n + 1) → t i = 1) :
    (t, c) ∈ Set.range ((prismRightConeMap n).app (Opposite.op ⦋d⦌))

lemma prismRightConeMap_last_time_one {n d : ℕ}
    (s : Join.Simplex ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] d) (i : Fin (d + 1))
    (h : ((prismRightConeMap n).app (Opposite.op ⦋d⦌) s).2 i = Fin.last (n + 1)) :
    ((prismRightConeMap n).app (Opposite.op ⦋d⦌) s).1 i = 1

lemma prismRightConeMap_mem_range_iff {n d : ℕ}
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) (c : (Δ[n + 1] : SSet.{u}) _⦋d⦌) :
    (t, c) ∈ Set.range ((prismRightConeMap n).app (Opposite.op ⦋d⦌)) ↔
      ∀ i : Fin (d + 1), c i = Fin.last (n + 1) → t i = 1

noncomputable def rightConeJoinIso (K : SSet.{u}) (n : ℕ) :
    join (join K Δ[n]) Δ[0] ≅ join K Δ[n + 1]

lemma rightConeJoinIso_naturality {K L : SSet.{u}} (f : K ⟶ L) (n : ℕ) :
    joinMap (joinMap f (𝟙 Δ[n])) (𝟙 Δ[0]) ≫ (rightConeJoinIso L n).hom =
      (rightConeJoinIso K n).hom ≫ joinMap f (𝟙 Δ[n + 1])

lemma rightConeJoinIso_inl (K : SSet.{u}) (n : ℕ) :
    joinInl (join K Δ[n]) Δ[0] ≫ (rightConeJoinIso K n).hom =
      joinMap (𝟙 K) (stdSimplex.δ (Fin.last (n + 1)))

lemma rightConeJoinIso_inr (K : SSet.{u}) (n : ℕ) :
    joinInr (join K Δ[n]) Δ[0] ≫ (rightConeJoinIso K n).hom =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫ joinInr K Δ[n + 1]

lemma relativeJoinConeFirst_factor {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinConeFirst f =
      joinMap (pullback.fst (joinMap f (𝟙 Δ[n])) (joinDiagonal Δ[n])) (𝟙 Δ[0]) ≫
        (rightConeJoinIso Δ[m] n).hom

noncomputable def prismRightConeDiagonal (n : ℕ) :
    join ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ⟶ join (Δ[n] : SSet.{u}) Δ[n + 1]

lemma prismRightConeMap_inl (n : ℕ) :
    joinInl ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ prismRightConeMap n =
      ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (Fin.last (n + 1)))

lemma prismRightConeMap_inr (n : ℕ) :
    joinInr ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ prismRightConeMap n =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫
        prismEndpoint 1 (Δ[n + 1] : SSet.{u})

lemma prismRightConeDiagonal_inl (n : ℕ) :
    joinInl ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ prismRightConeDiagonal n =
      joinDiagonal Δ[n] ≫ joinMap (𝟙 Δ[n]) (stdSimplex.δ (Fin.last (n + 1)))

lemma prismRightConeDiagonal_inr (n : ℕ) :
    joinInr ((Δ[1] : SSet.{u}) ⊗ Δ[n]) Δ[0] ≫ prismRightConeDiagonal n =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫
        joinInr (Δ[n] : SSet.{u}) Δ[n + 1]

lemma prismRightCone_square (n : ℕ) :
    prismRightConeDiagonal.{u} n ≫ joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]) =
      prismRightConeMap n ≫ joinDiagonal Δ[n + 1]

lemma prismRightCone_lastFace_aug_val {n r : ℕ}
    (a : Join.augObj (Δ[n] : SSet.{u}) r) (i : Fin r) :
    (Join.stdAugEquiv (n + 1) r
      (Join.augHom (stdSimplex.δ (Fin.last (n + 1))) r a) i).val =
      (Join.stdAugEquiv n r a i).val

lemma prismRightCone_joinFace_avoids_left_last {n d : ℕ}
    (s : Join.Simplex (Δ[n] : SSet.{u}) Δ[n + 1] d) (i : Fin (d + 1)) :
    ((joinStdSimplexIso (n + 1) (n + 1)).hom.app (Opposite.op ⦋d⦌)
      ((joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])).app
        (Opposite.op ⦋d⦌) s) i).val ≠ n + 1

lemma prismRightCone_isPullback (n : ℕ) :
    IsPullback (prismRightConeDiagonal.{u} n) (prismRightConeMap n)
      (joinMap (stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])) (joinDiagonal Δ[n + 1])

lemma relativeJoinCone_isPullback {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    IsPullback (relativeJoinConeFirst f) (relativeJoinConeSecond f)
      (joinMap (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1]))
      (joinDiagonal Δ[n + 1])

instance relativeJoinConeMap_isIso {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    IsIso (relativeJoinConeMap f)

noncomputable def relativeJoinConeIso {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    join (relativeJoin f (𝟙 Δ[n])) Δ[0] ≅
      relativeJoin (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])

lemma relativeJoinConeMap_inl {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    joinInl (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫ relativeJoinConeMap f =
      relativeJoinBaseMap f (stdSimplex.δ (Fin.last (n + 1)))

lemma relativeJoinConeMap_inr {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    joinInr (relativeJoin f (𝟙 Δ[n])) Δ[0] ≫ relativeJoinConeMap f =
      SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫
        relativeJoinInr (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])

lemma relativeJoinBaseMap_inr {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    relativeJoinInr f (𝟙 Y) ≫ relativeJoinBaseMap f h =
      h ≫ relativeJoinInr (f ≫ h) (𝟙 Z)

lemma relativeJoinConeMap_right {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    joinMap (relativeJoinInr f (𝟙 Δ[n])) (𝟙 Δ[0]) ≫ relativeJoinConeMap f =
      (joinStdSimplexIso n 0).hom ≫
        relativeJoinInr (f ≫ stdSimplex.δ (Fin.last (n + 1))) (𝟙 Δ[n + 1])

lemma relativeJoinBaseMap_prism {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    relativeJoinPrism f ≫ relativeJoinBaseMap f h = relativeJoinPrism (f ≫ h)

lemma relativeJoinCylinderCone_face_inv (n : ℕ) :
    stdSimplex.δ (Fin.last (n + 1)) ≫ (joinStdSimplexIso.{u} n 0).inv =
      joinInl (Δ[n] : SSet.{u}) Δ[0]

noncomputable def relativeJoinCylinderConeMap {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    pushout (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1))) ⟶
      join (pushout (prismEndpoint 1 Δ[m]) f) Δ[0]

lemma relativeJoinCylinderConeMap_inl {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    pushout.inl (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1))) ≫
      relativeJoinCylinderConeMap f =
        pushout.inl (prismEndpoint 1 Δ[m]) f ≫ joinInl _ Δ[0]

lemma relativeJoinCylinderConeMap_inr {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    pushout.inr (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1))) ≫
      relativeJoinCylinderConeMap f =
        (joinStdSimplexIso n 0).inv ≫
          joinMap (pushout.inr (prismEndpoint 1 Δ[m]) f) (𝟙 Δ[0])

lemma relativeJoinCylinderConeMap_comparison {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinCylinderConeMap f ≫
      joinMap (relativeJoinCylinderComparison f) (𝟙 Δ[0]) ≫ relativeJoinConeMap f =
        relativeJoinCylinderComparison (f ≫ stdSimplex.δ (Fin.last (n + 1)))

lemma joinLeftBoundary_subcomplex_isPushout {B : SSet.{u}} (A : B.Subcomplex) (K : SSet.{u}) :
    IsPushout (joinInl (A : SSet.{u}) K) A.ι
      (joinUnionLeft A (⊥ : K.Subcomplex))
      ((joinEmptyIso B K).inv ≫ joinUnionRight A (⊥ : K.Subcomplex))

lemma joinLeftBoundaryMap_innerAnodyne_of_rightAnodyne {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (K : SSet.{u}) (hi : rightAnodyneExtensions i) :
    innerAnodyneExtensions (joinLeftBoundaryMap i K)

noncomputable def hornOneLastSectionIso (A : SSet.{u}) :
    A ≅ (horn 1 1 : SSet.{u}) ⊗ A

lemma prismEndpoint_one_rightAnodyne (A : SSet.{u}) :
    rightAnodyneExtensions (prismEndpoint 1 A)

noncomputable def relativeJoinCylinderLastFaceMap {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    pushout (prismEndpoint 1 Δ[m]) f ⟶
      pushout (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1)))

lemma relativeJoinCylinderLastFaceMap_cone {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinCylinderLastFaceMap f ≫ relativeJoinCylinderConeMap f =
      joinInl (pushout (prismEndpoint 1 Δ[m]) f) Δ[0]

lemma relativeJoinCylinderCone_isPushout {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    IsPushout (joinInl (Δ[n] : SSet.{u}) Δ[0]) (pushout.inr (prismEndpoint 1 Δ[m]) f)
      ((joinStdSimplexIso n 0).hom ≫
        pushout.inr (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1))))
      (relativeJoinCylinderLastFaceMap f)

lemma relativeJoinCylinderCone_boundary_factor {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    joinLeftBoundaryMap (pushout.inr (prismEndpoint 1 Δ[m]) f) Δ[0] =
      (relativeJoinCylinderCone_isPushout f).isoPushout.inv ≫ relativeJoinCylinderConeMap f

lemma relativeJoinCylinderConeMap_innerAnodyne {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    innerAnodyneExtensions (relativeJoinCylinderConeMap f)

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_lastFace {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (hf : IsPrecompositionEquivalence (relativeJoinCylinderComparison f)) :
    IsPrecompositionEquivalence
      (relativeJoinCylinderComparison (f ≫ stdSimplex.δ (Fin.last (n + 1))))

lemma relativeJoin_exists_lastFaceFactor {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) ≠ Fin.last (n + 1)) :
    ∃ g : (Δ[m] : SSet.{u}) ⟶ Δ[n],
      g ≫ stdSimplex.δ (Fin.last (n + 1)) = f

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_of_not_last
    {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) ≠ Fin.last (n + 1))
    (hsmall : ∀ g : (Δ[m] : SSet.{u}) ⟶ Δ[n],
      IsPrecompositionEquivalence (relativeJoinCylinderComparison g)) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison f)

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_stdSimplex_step
    {m n : ℕ} (f : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1])
    (hsmall : ∀ g : (Δ[m] : SSet.{u}) ⟶ Δ[n],
      IsPrecompositionEquivalence (relativeJoinCylinderComparison g))
    (hboundary : IsPrecompositionEquivalence
      (relativeJoinCylinderComparison ((boundary m).ι ≫ f))) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison f)

lemma types_exists_dependentDesc {J : Type v} [Category.{w} J] {D : J ⥤ Type u}
    (c : Cocone D) (hc : IsColimit c) (P : c.pt → Type u)
    (a : ∀ j (x : D.obj j), P (c.ι.app j x))
    (ha : ∀ {j k} (f : j ⟶ k) (x : D.obj j), HEq (a k (D.map f x)) (a j x)) :
    ∃ b : ∀ z, P z, ∀ j (x : D.obj j), b (c.ι.app j x) = a j x

noncomputable def types_isColimit_of_pullback {J : Type v} [Category.{w} J]
    {D E : J ⥤ Type u} (c : Cocone D) (hc : IsColimit c) (d : Cocone E)
    (α : E ⟶ D) (f : d.pt ⟶ c.pt)
    (hp : ∀ j, IsPullback (d.ι.app j) (α.app j) f (c.ι.app j)) : IsColimit d

noncomputable def sset_isColimit_of_pullback {J : Type v} [Category.{w} J] [Small.{u} J]
    {D E : J ⥤ SSet.{u}} (c : Cocone D) (hc : IsColimit c) (d : Cocone E)
    (α : E ⟶ D) (f : d.pt ⟶ c.pt)
    (hp : ∀ j, IsPullback (d.ι.app j) (α.app j) f (c.ι.app j)) : IsColimit d

noncomputable def relativeJoinLeftProjection {Y S : SSet.{u}} (g : Y ⟶ S) :
    relativeJoinLeftFunctor g ⟶ Over.forget S ⋙ joinLeftFunctor Y

noncomputable def relativeJoin_left_isColimit {Y S : SSet.{u}} (g : Y ⟶ S)
    {J : Type v} [Category.{w} J] [Small.{u} J] [IsConnected J] {D : J ⥤ Over S}
    (c : Cocone D) (hc : IsColimit c) :
    IsColimit ((relativeJoinLeftFunctor g).mapCocone c)

instance relativeJoinLeftFunctor_preservesConnectedColimits {Y S : SSet.{u}} (g : Y ⟶ S)
    (J : Type v) [Category.{w} J] [Small.{u} J] [IsConnected J] :
    PreservesColimitsOfShape J (relativeJoinLeftFunctor g)

lemma isPrecompositionEquivalence_over_of_sequential_colimit {S : SSet.{u}}
    {F G : Over S ⥤ SSet.{u}} (t : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape ℕ F] [PreservesColimitsOfShape ℕ G]
    (D : ℕ ⥤ Over S) [∀ n, Mono (D.map (homOfLE (Nat.le_succ n)))]
    (c : Cocone D) (hc : IsColimit c)
    (ht : ∀ n, IsPrecompositionEquivalence (t.app (D.obj n))) :
    IsPrecompositionEquivalence (t.app c.pt)

lemma isPrecompositionEquivalence_over_of_widePushout_colimit {S : SSet.{u}}
    (J : Type u) {F G : Over S ⥤ SSet.{u}} (t : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape (WidePushoutShape J) F] [PreservesColimitsOfShape (WidePushoutShape J) G]
    (D : WidePushoutShape J ⥤ Over S) [∀ j, Mono (D.map (.init j))]
    (c : Cocone D) (hc : IsColimit c)
    (ht : ∀ n, IsPrecompositionEquivalence (t.app (D.obj n))) :
    IsPrecompositionEquivalence (t.app c.pt)

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_of_sequential_colimit
    {S : SSet.{u}} (D : ℕ ⥤ Over S)
    [∀ n, Mono (D.map (homOfLE (Nat.le_succ n)))]
    (c : Cocone D) (hc : IsColimit c)
    (h : ∀ n, IsPrecompositionEquivalence (relativeJoinCylinderComparison (D.obj n).hom)) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison c.pt.hom)

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_of_widePushout_colimit
    (J : Type u) {S : SSet.{u}} (D : WidePushoutShape J ⥤ Over S)
    [∀ j, Mono (D.map (.init j))] (c : Cocone D) (hc : IsColimit c)
    (h : ∀ j, IsPrecompositionEquivalence (relativeJoinCylinderComparison (D.obj j).hom)) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison c.pt.hom)

noncomputable def overCoproductWideCocone {J : Type u} {S : SSet.{u}}
    (objs : J → Over S) (c : Cofan objs) :
    Cocone (WidePushoutShape.wideSpan (⊥_ (Over S)) objs (fun j ↦ initial.to (objs j)))

noncomputable def overCoproductWideCocone_isColimit {J : Type u} {S : SSet.{u}}
    (objs : J → Over S) (c : Cofan objs) (hc : IsColimit c) :
    IsColimit (overCoproductWideCocone objs c)

lemma isPrecompositionEquivalence_over_of_coproduct_cocone
    (J : Type u) {S : SSet.{u}} {F G : Over S ⥤ SSet.{u}} (t : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape (WidePushoutShape J) F]
    [PreservesColimitsOfShape (WidePushoutShape J) G]
    (objs : J → Over S) (c : Cofan objs) (hc : IsColimit c)
    (h0 : IsPrecompositionEquivalence (t.app (⊥_ (Over S))))
    (h : ∀ j, IsPrecompositionEquivalence (t.app (objs j))) :
    IsPrecompositionEquivalence (t.app c.pt)

noncomputable def relativeJoinOverSigmaCofan {J : Type u} {S : SSet.{u}}
    (X : J → SSet.{u}) (f : ∀ j, X j ⟶ S) : Cofan (fun j ↦ Over.mk (f j))

noncomputable def relativeJoinOverSigmaCofan_isColimit {J : Type u} {S : SSet.{u}}
    (X : J → SSet.{u}) (f : ∀ j, X j ⟶ S) :
    IsColimit (relativeJoinOverSigmaCofan X f)

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_initialOver (S : SSet.{u}) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison (⊥_ (Over S)).hom)

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_sigma
    {J : Type u} {S : SSet.{u}} (X : J → SSet.{u}) (f : ∀ j, X j ⟶ S)
    (h : ∀ j, IsPrecompositionEquivalence (relativeJoinCylinderComparison (f j))) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison (Sigma.desc f))

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_skeleton_succ
    {A X S : SSet.{u}} (i : A ⟶ X) [Mono i] (f : X ⟶ S) (d : ℕ)
    (hprev : IsPrecompositionEquivalence
      (relativeJoinCylinderComparison ((skeletonOfMono i d).ι ≫ f)))
    (hboundary : ∀ c : Cell i d, IsPrecompositionEquivalence
      (relativeJoinCylinderComparison ((boundary d).ι ≫ c.map ≫ f)))
    (hcell : ∀ c : Cell i d, IsPrecompositionEquivalence
      (relativeJoinCylinderComparison (c.map ≫ f))) :
    IsPrecompositionEquivalence
      (relativeJoinCylinderComparison ((skeletonOfMono i (d + 1)).ι ≫ f))

lemma isPrecompositionEquivalence_over_natComponent_of_iso
    {S : SSet.{u}} {F G : Over S ⥤ SSet.{u}} (t : F ⟶ G) {A B : Over S} (e : A ≅ B)
    (hB : IsPrecompositionEquivalence (t.app B)) : IsPrecompositionEquivalence (t.app A)

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_sourceIso_iff
    {X Y S : SSet.{u}} (e : X ≅ Y) (f : Y ⟶ S) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison (e.hom ≫ f)) ↔
      IsPrecompositionEquivalence (relativeJoinCylinderComparison f)

instance relativeJoin_initialSkeleton_ι_isIso (X : SSet.{u}) (d : ℕ) [X.HasDimensionLT d] :
    IsIso (skeletonOfMono (initial.to X) d).ι

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_isInitialSource
    {X S : SSet.{u}} (f : X ⟶ S) (hX : IsInitial X) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison f)

noncomputable def relativeJoinSkeletonDiagram {A X S : SSet.{u}}
    (i : A ⟶ X) [Mono i] (f : X ⟶ S) : ℕ ⥤ Over S

noncomputable def relativeJoinSkeletonCocone {A X S : SSet.{u}}
    (i : A ⟶ X) [Mono i] (f : X ⟶ S) : Cocone (relativeJoinSkeletonDiagram i f)

noncomputable def relativeJoinSkeletonCocone_isColimit {A X S : SSet.{u}}
    (i : A ⟶ X) [Mono i] (f : X ⟶ S) : IsColimit (relativeJoinSkeletonCocone i f)

instance relativeJoinSkeletonDiagram_map_mono {A X S : SSet.{u}}
    (i : A ⟶ X) [Mono i] (f : X ⟶ S) (n : ℕ) :
    Mono ((relativeJoinSkeletonDiagram i f).map (homOfLE (Nat.le_succ n)))

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_of_skeletons
    {A X S : SSet.{u}} (i : A ⟶ X) [Mono i] (f : X ⟶ S)
    (h : ∀ n, IsPrecompositionEquivalence
      (relativeJoinCylinderComparison ((skeletonOfMono i n).ι ≫ f))) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison f)

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_standardTarget (n : ℕ) :
    ∀ {X : SSet.{u}} (f : X ⟶ Δ[n]),
      IsPrecompositionEquivalence (relativeJoinCylinderComparison f)

lemma isPrecompositionEquivalence_over_natComponent_of_pushout
    {S : SSet.{u}} {F G : Over S ⥤ SSet.{u}} (τ : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape WalkingSpan F] [PreservesColimitsOfShape WalkingSpan G]
    {A B C D : Over S} {i : A ⟶ B} [Mono i] {g : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hp : IsPushout i g r s) (hA : IsPrecompositionEquivalence (τ.app A))
    (hB : IsPrecompositionEquivalence (τ.app B)) (hC : IsPrecompositionEquivalence (τ.app C)) :
    IsPrecompositionEquivalence (τ.app D)

lemma isPrecompositionEquivalence_over_natComponent_skeleton_succ
    {S : SSet.{u}} {F G : Over S ⥤ SSet.{u}} (τ : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape WalkingSpan F] [PreservesColimitsOfShape WalkingSpan G]
    [∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J) F]
    [∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J) G]
    (h0 : IsPrecompositionEquivalence (τ.app (⊥_ (Over S))))
    {A X : SSet.{u}} (i : A ⟶ X) [Mono i] (f : X ⟶ S) (d : ℕ)
    (hprev : IsPrecompositionEquivalence
      (τ.app (Over.mk ((skeletonOfMono i d).ι ≫ f))))
    (hboundary : ∀ c : Cell i d, IsPrecompositionEquivalence
      (τ.app (Over.mk ((boundary d).ι ≫ c.map ≫ f))))
    (hcell : ∀ c : Cell i d, IsPrecompositionEquivalence (τ.app (Over.mk (c.map ≫ f)))) :
    IsPrecompositionEquivalence (τ.app (Over.mk ((skeletonOfMono i (d + 1)).ι ≫ f)))

lemma isPrecompositionEquivalence_over_natComponent_of_stdSimplex
    {S : SSet.{u}} {F G : Over S ⥤ SSet.{u}} (τ : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape WalkingSpan F] [PreservesColimitsOfShape WalkingSpan G]
    [PreservesColimitsOfShape ℕ F] [PreservesColimitsOfShape ℕ G]
    [∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J) F]
    [∀ J : Type u, PreservesColimitsOfShape (WidePushoutShape J) G]
    (h0 : IsPrecompositionEquivalence (τ.app (⊥_ (Over S))))
    (hstd : ∀ (d : ℕ) (p : (Δ[d] : SSet.{u}) ⟶ S),
      IsPrecompositionEquivalence (τ.app (Over.mk p)))
    (X : SSet.{u}) (f : X ⟶ S) : IsPrecompositionEquivalence (τ.app (Over.mk f))

noncomputable def overPullbackUnderlying {M S : SSet.{u}} (p : M ⟶ S) : Over S ⥤ SSet.{u}

lemma overPullbackUnderlying_map_fst {M S : SSet.{u}} (p : M ⟶ S)
    {a b : Over S} (u : a ⟶ b) :
    (overPullbackUnderlying p).map u ≫ pullback.fst b.hom p = pullback.fst a.hom p ≫ u.left

lemma overPullbackUnderlying_map_snd {M S : SSet.{u}} (p : M ⟶ S)
    {a b : Over S} (u : a ⟶ b) :
    (overPullbackUnderlying p).map u ≫ pullback.snd b.hom p = pullback.snd a.hom p

noncomputable def overPullbackProjection {M S : SSet.{u}} (p : M ⟶ S) :
    overPullbackUnderlying p ⟶ Over.forget S

lemma overPullbackProjection_isPullback {M S : SSet.{u}} (p : M ⟶ S)
    {a b : Over S} (u : a ⟶ b) :
    IsPullback ((overPullbackUnderlying p).map u) (pullback.fst a.hom p)
      (pullback.fst b.hom p) u.left

instance overPullbackUnderlying_preservesMonomorphisms {M S : SSet.{u}} (p : M ⟶ S) :
    (overPullbackUnderlying p).PreservesMonomorphisms

noncomputable def overPullbackUnderlying_isColimit {M S : SSet.{u}} (p : M ⟶ S)
    {J : Type v} [Category.{w} J] [Small.{u} J] {D : J ⥤ Over S}
    (c : Cocone D) (hc : IsColimit c) : IsColimit ((overPullbackUnderlying p).mapCocone c)

instance overPullbackUnderlying_preservesColimitsOfShape {M S : SSet.{u}} (p : M ⟶ S)
    (J : Type v) [Category.{w} J] [Small.{u} J] :
    PreservesColimitsOfShape J (overPullbackUnderlying p)

noncomputable def overPullbackMap {S : SSet.{u}} {a b : Over S} (u : a ⟶ b) (z : Over S) :
    (overPullbackUnderlying a.hom).obj z ⟶ (overPullbackUnderlying b.hom).obj z

lemma overPullbackMap_fst {S : SSet.{u}} {a b : Over S} (u : a ⟶ b) (z : Over S) :
    overPullbackMap u z ≫ pullback.fst z.hom b.hom = pullback.fst z.hom a.hom

lemma overPullbackMap_snd {S : SSet.{u}} {a b : Over S} (u : a ⟶ b) (z : Over S) :
    overPullbackMap u z ≫ pullback.snd z.hom b.hom = pullback.snd z.hom a.hom ≫ u.left

lemma overPullbackMap_naturality {S : SSet.{u}} {a b z w : Over S}
    (u : a ⟶ b) (v : z ⟶ w) :
    (overPullbackUnderlying a.hom).map v ≫ overPullbackMap u w =
      overPullbackMap u z ≫ (overPullbackUnderlying b.hom).map v

noncomputable def overPullbackMapNat {S : SSet.{u}} {a b : Over S} (u : a ⟶ b) :
    overPullbackUnderlying a.hom ⟶ overPullbackUnderlying b.hom

lemma isPrecompositionEquivalence_overPullbackMap_initial
    {S : SSet.{u}} {a b : Over S} (u : a ⟶ b) :
    IsPrecompositionEquivalence (overPullbackMap u (⊥_ (Over S)))

lemma isPrecompositionEquivalence_of_pullback_stdSimplex
    {S : SSet.{u}} {a b : Over S} (u : a ⟶ b)
    (hstd : ∀ (n : ℕ) (p : (Δ[n] : SSet.{u}) ⟶ S),
      IsPrecompositionEquivalence (overPullbackMap u (Over.mk p))) :
    IsPrecompositionEquivalence u.left

noncomputable def relativeJoinBaseProjection {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoin f g ⟶ S

lemma relativeJoinInr_baseProjection {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoinInr f g ≫ relativeJoinBaseProjection f g = g

lemma relativeJoinPrism_baseProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    relativeJoinPrism f ≫ relativeJoinBaseProjection f (𝟙 Y) =
      snd (Δ[1] : SSet.{u}) X ≫ f

noncomputable def mappingCylinderBaseProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout (prismEndpoint 1 X) f ⟶ Y

lemma mappingCylinderBaseProjection_inl {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inl (prismEndpoint 1 X) f ≫ mappingCylinderBaseProjection f =
      snd (Δ[1] : SSet.{u}) X ≫ f

lemma mappingCylinderBaseProjection_inr {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inr (prismEndpoint 1 X) f ≫ mappingCylinderBaseProjection f = 𝟙 Y

lemma relativeJoinCylinderComparison_baseProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    relativeJoinCylinderComparison f ≫ relativeJoinBaseProjection f (𝟙 Y) =
      mappingCylinderBaseProjection f

noncomputable def relativeJoinCylinderComparisonOver {X Y : SSet.{u}} (f : X ⟶ Y) :
    Over.mk (mappingCylinderBaseProjection f) ⟶ Over.mk (relativeJoinBaseProjection f (𝟙 Y))

noncomputable def relativeJoinPullbackMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoin (pullback.snd f h) (𝟙 Z) ⟶ relativeJoin f (𝟙 Y)

lemma relativeJoinPullbackMap_fst {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinPullbackMap f h ≫ pullback.fst (joinMap f (𝟙 Y)) (joinDiagonal Y) =
      pullback.fst (joinMap (pullback.snd f h) (𝟙 Z)) (joinDiagonal Z) ≫
        joinMap (pullback.fst f h) h

lemma relativeJoinPullbackMap_snd {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinPullbackMap f h ≫ pullback.snd (joinMap f (𝟙 Y)) (joinDiagonal Y) =
      pullback.snd (joinMap (pullback.snd f h) (𝟙 Z)) (joinDiagonal Z) ≫
        ((Δ[1] : SSet.{u}) ◁ h)

lemma relativeJoinPullbackMap_baseProjection {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinPullbackMap f h ≫ relativeJoinBaseProjection f (𝟙 Y) =
      relativeJoinBaseProjection (pullback.snd f h) (𝟙 Z) ≫ h

lemma relativeJoinPrism_pullbackMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinPrism (pullback.snd f h) ≫ relativeJoinPullbackMap f h =
      ((Δ[1] : SSet.{u}) ◁ pullback.fst f h) ≫ relativeJoinPrism f

lemma relativeJoinInr_pullbackMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinInr (pullback.snd f h) (𝟙 Z) ≫ relativeJoinPullbackMap f h =
      h ≫ relativeJoinInr f (𝟙 Y)

noncomputable def mappingCylinderPullbackMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    pushout (prismEndpoint 1 (pullback f h)) (pullback.snd f h) ⟶
      pushout (prismEndpoint 1 X) f

lemma mappingCylinderPullbackMap_inl {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    pushout.inl (prismEndpoint 1 (pullback f h)) (pullback.snd f h) ≫
      mappingCylinderPullbackMap f h =
        ((Δ[1] : SSet.{u}) ◁ pullback.fst f h) ≫ pushout.inl (prismEndpoint 1 X) f

lemma mappingCylinderPullbackMap_inr {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    pushout.inr (prismEndpoint 1 (pullback f h)) (pullback.snd f h) ≫
      mappingCylinderPullbackMap f h = h ≫ pushout.inr (prismEndpoint 1 X) f

lemma mappingCylinderPullbackMap_baseProjection {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    mappingCylinderPullbackMap f h ≫ mappingCylinderBaseProjection f =
      mappingCylinderBaseProjection (pullback.snd f h) ≫ h

lemma relativeJoinCylinderComparison_pullbackMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    mappingCylinderPullbackMap f h ≫ relativeJoinCylinderComparison f =
      relativeJoinCylinderComparison (pullback.snd f h) ≫ relativeJoinPullbackMap f h

noncomputable def mappingCylinderPullbackLift {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    pushout (prismEndpoint 1 (pullback f h)) (pullback.snd f h) ⟶
      pullback h (mappingCylinderBaseProjection f)

lemma mappingCylinderPullbackLift_fst {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    mappingCylinderPullbackLift f h ≫ pullback.fst h (mappingCylinderBaseProjection f) =
      mappingCylinderBaseProjection (pullback.snd f h)

lemma mappingCylinderPullbackLift_snd {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    mappingCylinderPullbackLift f h ≫ pullback.snd h (mappingCylinderBaseProjection f) =
      mappingCylinderPullbackMap f h

noncomputable def relativeJoinPullbackLift {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoin (pullback.snd f h) (𝟙 Z) ⟶ pullback h (relativeJoinBaseProjection f (𝟙 Y))

lemma relativeJoinPullbackLift_fst {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinPullbackLift f h ≫ pullback.fst h (relativeJoinBaseProjection f (𝟙 Y)) =
      relativeJoinBaseProjection (pullback.snd f h) (𝟙 Z)

lemma relativeJoinPullbackLift_snd {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinPullbackLift f h ≫ pullback.snd h (relativeJoinBaseProjection f (𝟙 Y)) =
      relativeJoinPullbackMap f h

lemma relativeJoinCylinderComparison_pullbackLift {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinCylinderComparison (pullback.snd f h) ≫ relativeJoinPullbackLift f h =
      mappingCylinderPullbackLift f h ≫
        overPullbackMap (relativeJoinCylinderComparisonOver f) (Over.mk h)

lemma sset_isPullback_of_colimits {J : Type v} [Category.{w} J] [Small.{u} J]
    {D E : J ⥤ SSet.{u}} (c : Cocone D) (hc : IsColimit c)
    (d : Cocone E) (hd : IsColimit d) (α : E ⟶ D) (a : d.pt ⟶ c.pt)
    {S T : SSet.{u}} (p : c.pt ⟶ S) (q : d.pt ⟶ T) (h : T ⟶ S)
    (hw : a ≫ p = q ≫ h) (ha : ∀ j, d.ι.app j ≫ a = α.app j ≫ c.ι.app j)
    (hp : ∀ j, IsPullback (α.app j) (d.ι.app j ≫ q) (c.ι.app j ≫ p) h) :
    IsPullback a q p h

lemma mappingCylinder_prism_isPullback {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsPullback ((Δ[1] : SSet.{u}) ◁ pullback.fst f h)
      (snd (Δ[1] : SSet.{u}) (pullback f h) ≫ pullback.snd f h)
      (snd (Δ[1] : SSet.{u}) X ≫ f) h

lemma mappingCylinderPullbackMap_isPullback {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsPullback (mappingCylinderPullbackMap f h) (mappingCylinderBaseProjection (pullback.snd f h))
      (mappingCylinderBaseProjection f) h

instance mappingCylinderPullbackLift_isIso {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsIso (mappingCylinderPullbackLift f h)

lemma join_isPullback {P A B C Q D E F : SSet.{u}}
    {a : P ⟶ A} {b : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    {c : Q ⟶ D} {d : Q ⟶ E} {h : D ⟶ F} {k : E ⟶ F}
    (hP : IsPullback a b f g) (hQ : IsPullback c d h k) :
    IsPullback (joinMap a c) (joinMap b d) (joinMap f h) (joinMap g k)

lemma prismBaseChange_isPullback {Y Z : SSet.{u}} (h : Z ⟶ Y) :
    IsPullback ((Δ[1] : SSet.{u}) ◁ h) (snd (Δ[1] : SSet.{u}) Z)
      (snd (Δ[1] : SSet.{u}) Y) h

lemma relativeJoinPullbackMap_prism_isPullback {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsPullback (relativeJoinPullbackMap f h)
      (pullback.snd (joinMap (pullback.snd f h) (𝟙 Z)) (joinDiagonal Z))
      (pullback.snd (joinMap f (𝟙 Y)) (joinDiagonal Y)) ((Δ[1] : SSet.{u}) ◁ h)

lemma relativeJoinPullbackMap_isPullback {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsPullback (relativeJoinPullbackMap f h) (relativeJoinBaseProjection (pullback.snd f h) (𝟙 Z))
      (relativeJoinBaseProjection f (𝟙 Y)) h

instance relativeJoinPullbackLift_isIso {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsIso (relativeJoinPullbackLift f h)

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_pullback_iff
    {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsPrecompositionEquivalence
      (overPullbackMap (relativeJoinCylinderComparisonOver f) (Over.mk h)) ↔
        IsPrecompositionEquivalence (relativeJoinCylinderComparison (pullback.snd f h))

lemma isPrecompositionEquivalence_relativeJoinCylinderComparison
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison f)

lemma emptyJoinIso_naturality {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u}) :
    joinMap (𝟙 ((⊥ : K.Subcomplex) : SSet.{u})) f ≫ (emptyJoinIso K B).hom =
      (emptyJoinIso K A).hom ≫ f

lemma joinRightBoundary_subcomplex_isPushout {B : SSet.{u}} (A : B.Subcomplex) (K : SSet.{u}) :
    IsPushout (joinInr K (A : SSet.{u})) A.ι
      (joinUnionRight (⊥ : K.Subcomplex) A)
      ((emptyJoinIso K B).inv ≫ joinUnionLeft (⊥ : K.Subcomplex) A)

lemma joinRightBoundaryMap_innerAnodyne_of_leftAnodyne {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (K : SSet.{u}) (hi : leftAnodyneExtensions i) :
    innerAnodyneExtensions (joinRightBoundaryMap i K)

lemma joinPoint_inl_leftAnodyne (K : SSet.{u}) :
    leftAnodyneExtensions (joinInl (Δ[0] : SSet.{u}) K)

def scaffoldFirstVertex (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n]

instance scaffoldFirstVertex_mono (n : ℕ) : Mono (scaffoldFirstVertex.{u} n)

lemma scaffoldFirstVertex_leftAnodyne (n : ℕ) :
    leftAnodyneExtensions (scaffoldFirstVertex.{u} n)

lemma scaffoldIntervalCone_inr :
    joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 0 0).hom =
      stdSimplex.δ (0 : Fin 2)

lemma scaffoldIntervalCone_endpoint :
    stdSimplex.δ (0 : Fin 2) ≫ (joinStdSimplexIso.{u} 0 0).inv =
      joinInr (Δ[0] : SSet.{u}) Δ[0]

noncomputable def scaffoldConeBridge (n : ℕ) :
    pushout (stdSimplex.δ (0 : Fin 2)) (scaffoldFirstVertex.{u} n) ⟶
      join (Δ[0] : SSet.{u}) Δ[n]

lemma scaffoldConeBridge_inl (n : ℕ) :
    pushout.inl (stdSimplex.δ (0 : Fin 2)) (scaffoldFirstVertex.{u} n) ≫ scaffoldConeBridge n =
      (joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) (scaffoldFirstVertex n)

lemma scaffoldConeBridge_inr (n : ℕ) :
    pushout.inr (stdSimplex.δ (0 : Fin 2)) (scaffoldFirstVertex.{u} n) ≫ scaffoldConeBridge n =
      joinInr Δ[0] Δ[n]

lemma scaffoldConeBridge_innerAnodyne (n : ℕ) :
    innerAnodyneExtensions (scaffoldConeBridge.{u} n)

noncomputable def scaffoldSimplexBridge (n : ℕ) :
    pushout (stdSimplex.δ (0 : Fin 2)) (scaffoldFirstVertex.{u} n) ⟶ Δ[0 + n + 1]

lemma scaffoldSimplexBridge_innerAnodyne (n : ℕ) :
    innerAnodyneExtensions (scaffoldSimplexBridge.{u} n)

lemma scaffoldSimplexBridge_whiskerRight_innerAnodyne (n : ℕ) (K : SSet.{u}) :
    innerAnodyneExtensions (scaffoldSimplexBridge n ▷ K)

noncomputable def scaffoldFiniteNerveConeIso (n : ℕ) :
    join (Δ[0] : SSet.{u}) (nerve (ULift.{u} (Fin (n + 1)))) ≅
      nerve (ULift.{u} (Fin (n + 2)))

lemma scaffoldFiniteTail_isoNerve (n : ℕ) :
    stdSimplex.δ (0 : Fin (n + 2)) ≫ (stdSimplex.isoNerve.{u} (n + 1)).hom =
      (stdSimplex.isoNerve n).hom ≫ nerveMap (scaffoldFiniteTail n)

lemma scaffoldFiniteNerveConeIso_inr (n : ℕ) :
    joinInr (Δ[0] : SSet.{u}) (nerve (ULift.{u} (Fin (n + 1)))) ≫
        (scaffoldFiniteNerveConeIso n).hom = nerveMap (scaffoldFiniteTail n)

lemma scaffoldFiniteNervePoint_leftAnodyne (n : ℕ) :
    leftAnodyneExtensions (nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _))

noncomputable def scaffoldNerveConeBridge (n : ℕ) :
    pushout (stdSimplex.δ (0 : Fin 2))
        (nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ⟶
      join (Δ[0] : SSet.{u}) (nerve (ULift.{u} (Fin (n + 1))))

lemma scaffoldNerveConeBridge_innerAnodyne (n : ℕ) :
    innerAnodyneExtensions (scaffoldNerveConeBridge.{u} n)

noncomputable def scaffoldFiniteNerveBridge (n : ℕ) :
    pushout (stdSimplex.δ (0 : Fin 2))
        (nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ⟶
      nerve (ULift.{u} (Fin (n + 2)))

lemma scaffoldFiniteNerveBridge_innerAnodyne (n : ℕ) :
    innerAnodyneExtensions (scaffoldFiniteNerveBridge.{u} n)

lemma scaffoldFiniteNerveBridge_whiskerRight_innerAnodyne (n : ℕ) (K : SSet.{u}) :
    innerAnodyneExtensions (scaffoldFiniteNerveBridge n ▷ K)

lemma scaffoldFiniteNerveBridge_inr (n : ℕ) :
    pushout.inr (stdSimplex.δ (0 : Fin 2))
        (nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ≫
      scaffoldFiniteNerveBridge n = nerveMap (scaffoldFiniteTail n)

def scaffoldFiniteFirstEdge (n : ℕ) :
    ULift.{u} (Fin 2) ⥤ ULift.{u} (Fin (n + 2))

lemma scaffoldFiniteNervePoint_isoNerve (n : ℕ) :
    nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _) ≫
      (stdSimplex.isoNerve n).inv =
        stdSimplex.map (SimplexCategory.mkHom (OrderHom.const _ (0 : Fin (n + 1))))

lemma scaffoldFiniteFirstEdge_isoNerve (n : ℕ) :
    stdSimplex.map (SimplexCategory.mkHom
        (prependOrderHom (OrderHom.const _ (0 : Fin (n + 1))))) ≫
      (stdSimplex.isoNerve.{u} (n + 1)).hom =
        (stdSimplex.isoNerve 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n)

lemma scaffoldFiniteNerveBridge_inl (n : ℕ) :
    pushout.inl (stdSimplex.δ (0 : Fin 2))
        (nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ≫
      scaffoldFiniteNerveBridge n =
        (stdSimplex.isoNerve 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n)

noncomputable def scaffoldFiniteExtension (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) : SSet.{u}

noncomputable def scaffoldFiniteExtensionMap (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    scaffoldFiniteExtension n F ⟶ simplicialReplacement F

lemma scaffoldFiniteExtensionMap_isPushout (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    IsPushout (scaffoldFiniteNerveBridge n ▷ F.obj (ULift.up 0))
      (pushout.inl
        (pushout.inr (stdSimplex.δ (0 : Fin 2))
          (nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ▷ F.obj (ULift.up 0))
        (simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft (scaffoldFiniteTail n)
          (simplicialReplacementInitialCoefficient F (scaffoldFiniteInitial (n + 1))))))
      (simplicialReplacementInitialAssembly F (scaffoldFiniteInitial (n + 1)))
      (scaffoldFiniteExtensionMap n F)

lemma scaffoldFiniteExtensionMap_innerAnodyne (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    innerAnodyneExtensions (scaffoldFiniteExtensionMap n F)

lemma simplicialReplacementAssembly_nervePoint
    {C : Type u} [Category.{u} C] {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F) (c : C) :
    (nervePoint c ▷ K) ≫ simplicialReplacementAssembly η =
      snd (Δ[0] : SSet.{u}) K ≫ η.app c ≫ simplicialReplacementConstantLift F c

noncomputable def scaffoldFiniteCylinderAttachingMap (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    F.obj (ULift.up 0) ⟶ simplicialReplacement (scaffoldFiniteTail n ⋙ F)

noncomputable def scaffoldFiniteCylinderPrism (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ F.obj (ULift.up 0) ⟶ scaffoldFiniteExtension n F

noncomputable def scaffoldFiniteCylinderTail (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    simplicialReplacement (scaffoldFiniteTail n ⋙ F) ⟶ scaffoldFiniteExtension n F

lemma scaffoldFiniteCylinder_isPushout (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    IsPushout (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F)
      (scaffoldFiniteCylinderPrism n F) (scaffoldFiniteCylinderTail n F)

noncomputable def scaffoldFiniteCylinderIso (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    scaffoldFiniteExtension n F ≅
      pushout (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F)

noncomputable def scaffoldFiniteCylinderComparison (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    pushout (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ⟶
      simplicialReplacement F

lemma scaffoldFiniteCylinderComparison_innerAnodyne (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    innerAnodyneExtensions (scaffoldFiniteCylinderComparison n F)

lemma scaffoldFiniteCylinderComparison_inl (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    pushout.inl (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
      scaffoldFiniteCylinderComparison n F =
        (((stdSimplex.isoNerve 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n)) ▷ F.obj (ULift.up 0)) ≫
          simplicialReplacementInitialAssembly F (scaffoldFiniteInitial (n + 1))

lemma scaffoldFiniteCylinderComparison_inr (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    pushout.inr (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
      scaffoldFiniteCylinderComparison n F = simplicialReplacementBaseMap (scaffoldFiniteTail n) F

lemma isPrecompositionEquivalence_scaffoldFiniteCylinderComparison (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    IsPrecompositionEquivalence (scaffoldFiniteCylinderComparison n F)

def scaffoldFiniteCollapseFunctor (n : ℕ) :
    ULift.{u} (Fin (n + 2)) ⥤ ULift.{u} (Fin 2)

lemma scaffoldFiniteFirstEdge_collapse (n : ℕ) :
    scaffoldFiniteFirstEdge.{u} n ⋙ scaffoldFiniteCollapseFunctor n = 𝟭 _

lemma scaffoldFiniteTail_collapse (n : ℕ) :
    scaffoldFiniteTail.{u} n ⋙ scaffoldFiniteCollapseFunctor n =
      (CategoryTheory.Functor.const _).obj (ULift.up (1 : Fin 2))

def scaffoldFiniteCollapse (n : ℕ) :
    nerve (ULift.{u} (Fin (n + 2))) ⟶ (Δ[1] : SSet.{u})

lemma scaffoldFiniteCollapse_firstEdge (n : ℕ) :
    (stdSimplex.isoNerve.{u} 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n) ≫
      scaffoldFiniteCollapse n = 𝟙 Δ[1]

lemma scaffoldFiniteCollapse_app (n d : ℕ)
    (σ : (nerve (ULift.{u} (Fin (n + 2)))) _⦋d⦌) (i : Fin (d + 1)) :
    (scaffoldFiniteCollapse n).app (Opposite.op ⦋d⦌) σ i =
      if (σ.obj i).down = 0 then 0 else 1

lemma scaffoldFiniteCollapse_tail (n : ℕ) :
    nerveMap (scaffoldFiniteTail.{u} n) ≫ scaffoldFiniteCollapse n =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

lemma scaffoldFiniteCollapse_zero (n : ℕ) :
    nervePoint (ULift.up (0 : Fin (n + 2)) : ULift.{u} _) ≫ scaffoldFiniteCollapse n =
      stdSimplex.δ (1 : Fin 2)

lemma scaffoldFiniteCollapse_zero_obj (n d : ℕ)
    (σ : (nerve (ULift.{u} (Fin (n + 2)))) _⦋d⦌) (x : (Δ[0] : SSet.{u}) _⦋d⦌)
    (h : (scaffoldFiniteCollapse n).app _ σ = (stdSimplex.δ (1 : Fin 2)).app _ x)
    (i : Fin (d + 1)) : (σ.obj i).down = 0

lemma scaffoldFiniteCollapse_one_obj (n d : ℕ)
    (σ : (nerve (ULift.{u} (Fin (n + 2)))) _⦋d⦌) (x : (Δ[0] : SSet.{u}) _⦋d⦌)
    (h : (scaffoldFiniteCollapse n).app _ σ = (stdSimplex.δ (0 : Fin 2)).app _ x)
    (i : Fin (d + 1)) : (σ.obj i).down ≠ 0

lemma scaffoldFiniteCollapse_zero_isPullback (n : ℕ) :
    IsPullback (nervePoint (ULift.up (0 : Fin (n + 2)) : ULift.{u} _))
      (𝟙 (Δ[0] : SSet.{u})) (scaffoldFiniteCollapse n) (stdSimplex.δ (1 : Fin 2))

lemma scaffoldFiniteCollapse_one_isPullback (n : ℕ) :
    IsPullback (nerveMap (scaffoldFiniteTail.{u} n))
      (stdSimplex.isTerminalObj₀.from (nerve (ULift.{u} (Fin (n + 1)))))
      (scaffoldFiniteCollapse n) (stdSimplex.δ (0 : Fin 2))

lemma vertexFiber_isPullback {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    IsPullback (vertexFiberι p b) (stdSimplex.isTerminalObj₀.from (vertexFiber p b)) p
      (SSet.const b : (Δ[0] : SSet.{u}) ⟶ B)

lemma scaffoldFiniteTotal_zero_isPullback (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) :
    IsPullback (vertexFiberι p (nerveVertex (ULift.up (0 : Fin (n + 2)))))
      (stdSimplex.isTerminalObj₀.from _) (p ≫ scaffoldFiniteCollapse n)
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))

noncomputable def scaffoldFiniteTotalZeroFiberIso (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) :
    vertexFiber p (nerveVertex (ULift.up (0 : Fin (n + 2)))) ≅
      vertexFiber (p ≫ scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

lemma scaffoldFiniteTotalZeroFiberIso_hom_ι (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) :
    (scaffoldFiniteTotalZeroFiberIso n p).hom ≫
      vertexFiberι (p ≫ scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        vertexFiberι p (nerveVertex (ULift.up (0 : Fin (n + 2))))

lemma scaffoldFiniteTotal_one_isPullback (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) :
    IsPullback (pullback.fst p (nerveMap (scaffoldFiniteTail n)))
      (stdSimplex.isTerminalObj₀.from _) (p ≫ scaffoldFiniteCollapse n)
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))

noncomputable def scaffoldFiniteTotalOneFiberIso (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) :
    pullback p (nerveMap (scaffoldFiniteTail n)) ≅
      vertexFiber (p ≫ scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

lemma scaffoldFiniteTotalOneFiberIso_hom_ι (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) :
    (scaffoldFiniteTotalOneFiberIso n p).hom ≫
      vertexFiberι (p ≫ scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        pullback.fst p (nerveMap (scaffoldFiniteTail n))

lemma simplicialReplacementAssembly_const
    {C : Type u} [Category.{u} C] {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F) (c : C) :
    lift (SSet.const (nerveVertex c)) (𝟙 K) ≫ simplicialReplacementAssembly η =
      η.app c ≫ simplicialReplacementConstantLift F c

lemma scaffoldFiniteFirstEdge_prism_zero (n : ℕ) (K : SSet.{u}) :
    prismEndpoint 0 K ≫
      (((stdSimplex.isoNerve 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n)) ▷ K) =
        lift (SSet.const (nerveVertex (ULift.up (0 : Fin (n + 2))))) (𝟙 K)

lemma scaffoldFiniteCylinderComparison_endpoint_zero (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    prismEndpoint 0 (F.obj (ULift.up 0)) ≫
      pushout.inl (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
      scaffoldFiniteCylinderComparison n F = simplicialReplacementConstantLift F (ULift.up 0)

lemma scaffoldFiniteCylinderAttachingMap_baseMap (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    scaffoldFiniteCylinderAttachingMap n F ≫ simplicialReplacementBaseMap (scaffoldFiniteTail n) F =
      (simplicialReplacementInitialCoefficient F (scaffoldFiniteInitial (n + 1))).app
        ((scaffoldFiniteTail n).obj (ULift.up 0)) ≫
          simplicialReplacementConstantLift F ((scaffoldFiniteTail n).obj (ULift.up 0))

lemma scaffoldFiniteCylinderComparison_endpoint_one (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) :
    prismEndpoint 1 (F.obj (ULift.up 0)) ≫
      pushout.inl (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
      scaffoldFiniteCylinderComparison n F =
        scaffoldFiniteCylinderAttachingMap n F ≫ simplicialReplacementBaseMap (scaffoldFiniteTail n) F

noncomputable def scaffoldFiniteZeroFiberComparison (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    F.obj (ULift.up 0) ⟶
      vertexFiber (p ≫ scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

lemma scaffoldFiniteZeroFiberComparison_ι (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    scaffoldFiniteZeroFiberComparison n p F l h ≫
        vertexFiberι (p ≫ scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      prismEndpoint 0 (F.obj (ULift.up 0)) ≫
        pushout.inl (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
          scaffoldFiniteCylinderComparison n F ≫ l

noncomputable def scaffoldFiniteOneFiberComparison (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    simplicialReplacement (scaffoldFiniteTail n ⋙ F) ⟶
      vertexFiber (p ≫ scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

lemma scaffoldFiniteOneFiberComparison_ι (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    scaffoldFiniteOneFiberComparison n p F l h ≫
        vertexFiberι (p ≫ scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      pushout.inr (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldFiniteCylinderAttachingMap n F) ≫
        scaffoldFiniteCylinderComparison n F ≫ l

lemma IsLeftScaffold.finiteZeroFiber_isPrecompositionEquivalence
    (n : ℕ) {E : SSet.{u}} {p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))} [LeftFibration p]
    {F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)]
    {l : simplicialReplacement F ⟶ E} (hs : IsLeftScaffold p F l)
    (h : l ≫ p = simplicialReplacementProjection F) :
    IsPrecompositionEquivalence (scaffoldFiniteZeroFiberComparison n p F l h)

lemma scaffoldFiniteOneFiberComparison_isPrecompositionEquivalence_iff
    (n : ℕ) {E : SSet.{u}} (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    IsPrecompositionEquivalence (scaffoldFiniteOneFiberComparison n p F l h) ↔
      IsPrecompositionEquivalence (leftScaffoldBaseChange p F l h (scaffoldFiniteTail n))

lemma thinNerve_hom_ext_vertices {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    {X : SSet.{u}} {f g : X ⟶ nerve C}
    (h : f.app (Opposite.op ⦋0⦌) = g.app (Opposite.op ⦋0⦌)) : f = g

lemma thinNerve_hom_ext_horn {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    (n : ℕ) (i : Fin (n + 3)) {f g : (Δ[n + 2] : SSet.{u}) ⟶ nerve C}
    (h : (horn (n + 2) i).ι ≫ f = (horn (n + 2) i).ι ≫ g) : f = g

instance thinNerve_innerFibration {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    {X : SSet.{u}} [Quasicategory X] (p : X ⟶ nerve C) : InnerFibration p

instance stdSimplexTarget_innerFibration {X : SSet.{u}} [Quasicategory X]
    (n : ℕ) (p : X ⟶ (Δ[n] : SSet.{u})) : InnerFibration p

def preorderNerveHornVertex {C : Type u} [Preorder C] {n : ℕ} {i : Fin (n + 3)}
    (a : (horn (n + 2) i : SSet.{u}) ⟶ nerve C) (j : Fin (n + 3)) : C

lemma preorderNerveHornVertex_apply {C : Type u} [Preorder C] {n : ℕ} {i : Fin (n + 3)}
    (a : (horn (n + 2) i : SSet.{u}) ⟶ nerve C)
    (v : (horn (n + 2) i : SSet.{u}) _⦋0⦌) :
    preorderNerveHornVertex a (v.val 0) = (a.app _ v).obj 0

lemma preorderNerveHorn_extend {C : Type u} [Preorder C] {n : ℕ} {i : Fin (n + 3)}
    (a : (horn (n + 2) i : SSet.{u}) ⟶ nerve C)
    (ha : Monotone (preorderNerveHornVertex a)) :
    ∃ l : (Δ[n + 2] : SSet.{u}) ⟶ nerve C, (horn (n + 2) i).ι ≫ l = a

lemma preorderNerveHornVertex_edge_objs {C : Type u} [Preorder C] {n : ℕ} {i : Fin (n + 3)}
    (a : (horn (n + 2) i : SSet.{u}) ⟶ nerve C)
    (j k : Fin (n + 3)) (hjk : j ≤ k) (hc : Finset.card {i, j, k} ≤ n + 2) :
    (a.app (Opposite.op ⦋1⦌) (horn.edge (n + 2) i j k hjk hc)).obj 0 =
        preorderNerveHornVertex a j ∧
      (a.app (Opposite.op ⦋1⦌) (horn.edge (n + 2) i j k hjk hc)).obj 1 =
        preorderNerveHornVertex a k

lemma preorderNerveHornVertex_le {C : Type u} [Preorder C] {n : ℕ} {i : Fin (n + 3)}
    (a : (horn (n + 2) i : SSet.{u}) ⟶ nerve C)
    (j k : Fin (n + 3)) (hjk : j ≤ k) (hc : Finset.card {i, j, k} ≤ n + 2) :
    preorderNerveHornVertex a j ≤ preorderNerveHornVertex a k

lemma stdSimplex_hom_ext_horn (n r : ℕ) (i : Fin (n + 3))
    {f g : (Δ[n + 2] : SSet.{u}) ⟶ Δ[r]}
    (h : (horn (n + 2) i).ι ≫ f = (horn (n + 2) i).ι ≫ g) : f = g

def scaffoldFiniteInitialEdge (n : ℕ) : (nerve (ULift.{u} (Fin (n + 2)))) _⦋1⦌

lemma scaffoldFiniteCollapse_horn_vertex (n m : ℕ) (i : Fin (m + 3))
    (a : (horn (m + 2) i : SSet.{u}) ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (b : (Δ[m + 2] : SSet.{u}) ⟶ Δ[1])
    (sq : CommSq a (horn (m + 2) i).ι (scaffoldFiniteCollapse n) b) (j : Fin (m + 3)) :
    (if (preorderNerveHornVertex a j).down = 0 then (0 : Fin 2) else 1) =
      (SSet.yonedaEquiv b) j

lemma scaffoldFiniteInitialHorn_monotone (n m : ℕ)
    (a : (horn (m + 2) 0 : SSet.{u}) ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (b : (Δ[m + 2] : SSet.{u}) ⟶ Δ[1])
    (he : a.app (Opposite.op ⦋1⦌) (initialHornEdge m) = scaffoldFiniteInitialEdge n)
    (sq : CommSq a (horn (m + 2) 0).ι (scaffoldFiniteCollapse n) b) :
    Monotone (preorderNerveHornVertex a)

lemma scaffoldFiniteInitialEdge_isCocartesian (n : ℕ) :
    IsCocartesianEdge (scaffoldFiniteCollapse.{u} n) (scaffoldFiniteInitialEdge n)

lemma scaffoldFiniteInitialEdge_yoneda (n : ℕ) :
    SSet.yonedaEquiv ((stdSimplex.isoNerve.{u} 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n)) =
      scaffoldFiniteInitialEdge n

lemma scaffoldFiniteInitialEdge_comp_isCocartesian (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) [LeftFibration p]
    (e : E _⦋1⦌) (he : p.app (Opposite.op ⦋1⦌) e = scaffoldFiniteInitialEdge n) :
    IsCocartesianEdge (p ≫ scaffoldFiniteCollapse n) e

noncomputable def scaffoldFiniteScaffoldPrism (n : ℕ) {E : SSet.{u}}
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E) :
    (Δ[1] : SSet.{u}) ⊗ F.obj (ULift.up 0) ⟶ E

lemma scaffoldFiniteScaffoldPrism_projection (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    scaffoldFiniteScaffoldPrism n F l ≫ p =
      fst Δ[1] (F.obj (ULift.up 0)) ≫
        (stdSimplex.isoNerve 1).hom ≫ nerveMap (scaffoldFiniteFirstEdge n)

lemma scaffoldFiniteScaffoldPrism_interval_projection (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    scaffoldFiniteScaffoldPrism n F l ≫ (p ≫ scaffoldFiniteCollapse n) =
      fst Δ[1] (F.obj (ULift.up 0))

def prismVerticalSimplex {K E : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ E)
    (x : K _⦋0⦌) : E _⦋1⦌

lemma scaffoldFiniteScaffoldPrism_vertical_isCocartesian (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) [LeftFibration p]
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (x : (F.obj (ULift.up 0)) _⦋0⦌) :
    IsCocartesianEdge (p ≫ scaffoldFiniteCollapse n)
      (prismVerticalSimplex (scaffoldFiniteScaffoldPrism n F l) x)

noncomputable def mappingCylinderPrismMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout (prismEndpoint 1 X) f ⟶ (Δ[1] : SSet.{u}) ⊗ Y

instance mappingCylinderPrismMap_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (mappingCylinderPrismMap f)

lemma relativeJoinCylinderComparison_prismMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    relativeJoinCylinderComparison f ≫ pullback.snd (joinMap f (𝟙 Y)) (joinDiagonal Y) =
      mappingCylinderPrismMap f

instance relativeJoinCylinderComparison_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (relativeJoinCylinderComparison f)

instance relativeJoinCylinderComparison_pre_trivialKanFibration
    {X Y E : SSet.{u}} (f : X ⟶ Y) [Mono f] [Quasicategory E] :
    TrivialKanFibration ((pre (relativeJoinCylinderComparison f)).app E)

noncomputable def relativeJoinCylinderExtensionSpace {X Y E : SSet.{u}} (f : X ⟶ Y)
    (u : pushout (prismEndpoint 1 X) f ⟶ E) : SSet.{u}

lemma relativeJoinCylinderExtensionSpace_isContractibleKan
    {X Y E : SSet.{u}} (f : X ⟶ Y) [Mono f] [Quasicategory E]
    (u : pushout (prismEndpoint 1 X) f ⟶ E) :
    IsContractibleKan (relativeJoinCylinderExtensionSpace f u)

lemma relativeJoinCylinder_extension_exists {X Y E : SSet.{u}}
    (f : X ⟶ Y) [Mono f] [Quasicategory E]
    (u : pushout (prismEndpoint 1 X) f ⟶ E) :
    ∃ G : relativeJoin f (𝟙 Y) ⟶ E, relativeJoinCylinderComparison f ≫ G = u

lemma relativeJoin_extension_of_prism {X Y E : SSet.{u}}
    (f : X ⟶ Y) [Mono f] [Quasicategory E]
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (g : Y ⟶ E)
    (w : prismEndpoint 1 X ≫ H = f ≫ g) :
    ∃ G : relativeJoin f (𝟙 Y) ⟶ E,
      relativeJoinPrism f ≫ G = H ∧ relativeJoinInr f (𝟙 Y) ≫ G = g

lemma stdSimplex_homotopy_vertex_le {A : SSet.{u}} {n : ℕ}
    {f g : A ⟶ (Δ[n] : SSet.{u})} (H : SSet.Homotopy f g) (x : A _⦋0⦌) :
    (f.app (Opposite.op ⦋0⦌) x) 0 ≤ (g.app (Opposite.op ⦋0⦌) x) 0

lemma stdSimplex_eq_of_functorIso {A : SSet.{u}} {n : ℕ}
    {f g : A ⟶ (Δ[n] : SSet.{u})} (e : FunctorIso f g) : f = g

lemma IsPrecompositionEquivalence.stdSimplex_hom_ext {A B : SSet.{u}} {i : A ⟶ B}
    (hi : IsPrecompositionEquivalence i) {n : ℕ} {f g : B ⟶ (Δ[n] : SSet.{u})}
    (h : i ≫ f = i ≫ g) : f = g

noncomputable def mappingCylinderIntervalProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout (prismEndpoint 1 X) f ⟶ (Δ[1] : SSet.{u})

lemma mappingCylinderIntervalProjection_inl {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inl (prismEndpoint 1 X) f ≫ mappingCylinderIntervalProjection f = fst Δ[1] X

lemma mappingCylinderIntervalProjection_inr {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inr (prismEndpoint 1 X) f ≫ mappingCylinderIntervalProjection f =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

lemma relativeJoinCylinderComparison_intervalProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    relativeJoinCylinderComparison f ≫ relativeJoinProjection f (𝟙 Y) =
      mappingCylinderIntervalProjection f

lemma relativeJoinCylinder_extension_intervalProjection {X Y E : SSet.{u}}
    (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u}))
    (u : pushout (prismEndpoint 1 X) f ⟶ E) (hu : u ≫ p = mappingCylinderIntervalProjection f)
    (G : relativeJoin f (𝟙 Y) ⟶ E) (hG : relativeJoinCylinderComparison f ≫ G = u) :
    G ≫ p = relativeJoinProjection f (𝟙 Y)

lemma relativeJoinCylinder_extension_over_interval_exists {X Y E : SSet.{u}}
    (f : X ⟶ Y) [Mono f] [Quasicategory E] (p : E ⟶ (Δ[1] : SSet.{u}))
    (u : pushout (prismEndpoint 1 X) f ⟶ E) (hu : u ≫ p = mappingCylinderIntervalProjection f) :
    ∃ G : relativeJoin f (𝟙 Y) ⟶ E,
      relativeJoinCylinderComparison f ≫ G = u ∧ G ≫ p = relativeJoinProjection f (𝟙 Y)

lemma relativeJoin_extension_of_prism_over_interval {X Y E : SSet.{u}}
    (f : X ⟶ Y) [Mono f] [Quasicategory E] (p : E ⟶ (Δ[1] : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (g : Y ⟶ E)
    (w : prismEndpoint 1 X ≫ H = f ≫ g) (hH : H ≫ p = fst Δ[1] X)
    (hg : g ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
    ∃ G : relativeJoin f (𝟙 Y) ⟶ E,
      relativeJoinPrism f ≫ G = H ∧ relativeJoinInr f (𝟙 Y) ≫ G = g ∧
        G ≫ p = relativeJoinProjection f (𝟙 Y)

lemma isPullback_joinInl_naturality {A B K L : SSet.{u}} (f : A ⟶ B) (g : K ⟶ L) :
    IsPullback (joinInl A K) f (joinMap f g) (joinInl B L)

lemma isPullback_joinInr_naturality {A B K L : SSet.{u}} (f : A ⟶ B) (g : K ⟶ L) :
    IsPullback (joinInr A K) g (joinMap f g) (joinInr B L)

lemma isPullback_prismEndpoint_fst (i : Fin 2) (S : SSet.{u}) :
    IsPullback (prismEndpoint i S) (stdSimplex.isTerminalObj₀.from S) (fst Δ[1] S)
      (SSet.const (stdSimplex.obj₀Equiv.symm i) : (Δ[0] : SSet.{u}) ⟶ Δ[1])

lemma relativeJoinInl_prism_isPullback {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (relativeJoinInl f g) f
      (pullback.snd (joinMap f g) (joinDiagonal S)) (prismEndpoint 0 S)

lemma relativeJoinInr_prism_isPullback {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (relativeJoinInr f g) g
      (pullback.snd (joinMap f g) (joinDiagonal S)) (prismEndpoint 1 S)

lemma relativeJoinInl_endpoint_isPullback {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (relativeJoinInl f g) (stdSimplex.isTerminalObj₀.from X)
      (relativeJoinProjection f g) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))

lemma relativeJoinInr_endpoint_isPullback {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (relativeJoinInr f g) (stdSimplex.isTerminalObj₀.from Y)
      (relativeJoinProjection f g) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))

noncomputable def relativeJoinZeroFiberIso {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    X ≅ vertexFiber (relativeJoinProjection f g) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

lemma relativeJoinZeroFiberIso_hom_ι {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    (relativeJoinZeroFiberIso f g).hom ≫
      vertexFiberι (relativeJoinProjection f g) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        relativeJoinInl f g

noncomputable def relativeJoinOneFiberIso {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Y ≅ vertexFiber (relativeJoinProjection f g) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

lemma relativeJoinOneFiberIso_hom_ι {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    (relativeJoinOneFiberIso f g).hom ≫
      vertexFiberι (relativeJoinProjection f g) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        relativeJoinInr f g

lemma relativeJoinZeroFiberIso_vertexFiberMap_ι {X Y S E : SSet.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (p : E ⟶ (Δ[1] : SSet.{u}))
    (G : relativeJoin f g ⟶ E) (hG : G ≫ p = relativeJoinProjection f g) :
    (relativeJoinZeroFiberIso f g).hom ≫
      vertexFiberMap (relativeJoinProjection f g) p G hG (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
        vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = relativeJoinInl f g ≫ G

lemma relativeJoinOneFiberIso_vertexFiberMap_ι {X Y S E : SSet.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (p : E ⟶ (Δ[1] : SSet.{u}))
    (G : relativeJoin f g ⟶ E) (hG : G ≫ p = relativeJoinProjection f g) :
    (relativeJoinOneFiberIso f g).hom ≫
      vertexFiberMap (relativeJoinProjection f g) p G hG (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
        vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = relativeJoinInr f g ≫ G

lemma relativeJoin_extension_zeroFiber_eq {X Y E : SSet.{u}} (f : X ⟶ Y)
    (p : E ⟶ (Δ[1] : SSet.{u})) (G : relativeJoin f (𝟙 Y) ⟶ E)
    (hG : G ≫ p = relativeJoinProjection f (𝟙 Y))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (hH : relativeJoinPrism f ≫ G = H)
    (z : X ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz : z ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = prismEndpoint 0 X ≫ H) :
    (relativeJoinZeroFiberIso f (𝟙 Y)).hom ≫
      vertexFiberMap (relativeJoinProjection f (𝟙 Y)) p G hG (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        z

lemma relativeJoin_extension_oneFiber_eq {X Y E : SSet.{u}} (f : X ⟶ Y)
    (p : E ⟶ (Δ[1] : SSet.{u})) (G : relativeJoin f (𝟙 Y) ⟶ E)
    (hG : G ≫ p = relativeJoinProjection f (𝟙 Y))
    (g : Y ⟶ E) (hg : relativeJoinInr f (𝟙 Y) ≫ G = g)
    (z : Y ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz : z ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g) :
    (relativeJoinOneFiberIso f (𝟙 Y)).hom ≫
      vertexFiberMap (relativeJoinProjection f (𝟙 Y)) p G hG (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        z

lemma relativeJoin_extension_zeroFiber_isPrecompositionEquivalence_iff
    {X Y E : SSet.{u}} (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u}))
    (G : relativeJoin f (𝟙 Y) ⟶ E) (hG : G ≫ p = relativeJoinProjection f (𝟙 Y))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (hH : relativeJoinPrism f ≫ G = H)
    (z : X ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz : z ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = prismEndpoint 0 X ≫ H) :
    IsPrecompositionEquivalence
      (vertexFiberMap (relativeJoinProjection f (𝟙 Y)) p G hG (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ↔
        IsPrecompositionEquivalence z

lemma relativeJoin_extension_oneFiber_isPrecompositionEquivalence_iff
    {X Y E : SSet.{u}} (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u}))
    (G : relativeJoin f (𝟙 Y) ⟶ E) (hG : G ≫ p = relativeJoinProjection f (𝟙 Y))
    (g : Y ⟶ E) (hg : relativeJoinInr f (𝟙 Y) ≫ G = g)
    (z : Y ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz : z ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g) :
    IsPrecompositionEquivalence
      (vertexFiberMap (relativeJoinProjection f (𝟙 Y)) p G hG (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ↔
        IsPrecompositionEquivalence z

def joinIntervalProjection (X Y : SSet.{u}) : join X Y ⟶ (Δ[1] : SSet.{u})

lemma joinIntervalProjection_intervalJoin (X Y : SSet.{u}) :
    joinIntervalProjection X Y ≫ (joinStdSimplexIso 0 0).inv =
      joinMap (stdSimplex.isTerminalObj₀.from X) (stdSimplex.isTerminalObj₀.from Y)

lemma joinIntervalProjection_app_cut (X Y : SSet.{u}) (n : ℕ) (s : (join X Y) _⦋n⦌) :
    Join.pullCut (stdSimplex.objEquiv
      ((joinIntervalProjection X Y).app (Opposite.op ⦋n⦌) s)).toOrderHom 1 = s.1.val

lemma joinIntervalProjection_app_eq_zero_iff (X Y : SSet.{u}) (n : ℕ)
    (s : (join X Y) _⦋n⦌) (j : Fin (n + 1)) :
    (joinIntervalProjection X Y).app (Opposite.op ⦋n⦌) s j = 0 ↔ j.val < s.1.val

lemma joinIntervalProjection_naturality {X Y X' Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    joinMap f g ≫ joinIntervalProjection X' Y' = joinIntervalProjection X Y

lemma joinDiagonal_joinIntervalProjection (K : SSet.{u}) :
    joinDiagonal K ≫ joinIntervalProjection K K = fst (Δ[1] : SSet.{u}) K

lemma Join.pullCut_delta_zero (n l : ℕ) (hl : 0 < l) (hn : l ≤ n + 2) :
    Join.pullCut (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom l = l - 1

lemma Join.pullCut_delta_last (n l : ℕ) (hl : l ≤ n + 1) :
    Join.pullCut (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom l = l

lemma Join.simplexMap_delta_zero_right_heq {X Y : SSet.{u}} {n : ℕ}
    (s : Join.Simplex X Y (n + 1)) (hs : 0 < s.1.val) :
    HEq (Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom s).2.2 s.2.2

lemma Join.simplexMap_delta_last_left_heq {X Y : SSet.{u}} {n : ℕ}
    (s : Join.Simplex X Y (n + 1)) (hs : s.1.val ≤ n + 1) :
    HEq (Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom s).2.1 s.2.1

lemma Join.Simplex.ext_of_extreme_faces {X Y : SSet.{u}} {n : ℕ}
    (s t : Join.Simplex X Y (n + 1)) (hc : s.1 = t.1)
    (hs0 : 0 < s.1.val) (hs1 : s.1.val ≤ n + 1)
    (h0 : Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom s =
      Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom t)
    (h1 : Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom s =
      Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom t) : s = t

lemma join_hom_ext_innerHorn_of_cut {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 3))
    (hi0 : 0 < i) (hi1 : i < Fin.last (n + 2))
    {f g : (Δ[n + 2] : SSet.{u}) ⟶ join X Y}
    (hc : (SSet.yonedaEquiv f).1 = (SSet.yonedaEquiv g).1)
    (hs0 : 0 < (SSet.yonedaEquiv f).1.val) (hs1 : (SSet.yonedaEquiv f).1.val ≤ n + 2)
    (h : (horn (n + 2) i).ι ≫ f = (horn (n + 2) i).ι ≫ g) : f = g

lemma join_hom_ext_innerHorn_of_interval {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 3))
    (hi0 : 0 < i) (hi1 : i < Fin.last (n + 2))
    {f g : (Δ[n + 2] : SSet.{u}) ⟶ join X Y}
    (ht : f ≫ joinIntervalProjection X Y = g ≫ joinIntervalProjection X Y)
    (hs0 : 0 < (SSet.yonedaEquiv f).1.val) (hs1 : (SSet.yonedaEquiv f).1.val ≤ n + 2)
    (h : (horn (n + 2) i).ι ≫ f = (horn (n + 2) i).ι ≫ g) : f = g

lemma joinIntervalProjection_inl_isPullback (X Y : SSet.{u}) :
    IsPullback (joinInl X Y) (stdSimplex.isTerminalObj₀.from X) (joinIntervalProjection X Y)
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))

lemma joinIntervalProjection_inr_isPullback (X Y : SSet.{u}) :
    IsPullback (joinInr X Y) (stdSimplex.isTerminalObj₀.from Y) (joinIntervalProjection X Y)
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))

lemma join_exists_factor_inl_of_interval_zero {K X Y : SSet.{u}} (b : K ⟶ join X Y)
    (hb : b ≫ joinIntervalProjection X Y = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :
    ∃ c : K ⟶ X, c ≫ joinInl X Y = b

lemma join_exists_factor_inr_of_interval_one {K X Y : SSet.{u}} (b : K ⟶ join X Y)
    (hb : b ≫ joinIntervalProjection X Y = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
    ∃ c : K ⟶ Y, c ≫ joinInr X Y = b

lemma joinIntervalProjection_inl (X Y : SSet.{u}) :
    joinInl X Y ≫ joinIntervalProjection X Y =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

lemma joinIntervalProjection_inr (X Y : SSet.{u}) :
    joinInr X Y ≫ joinIntervalProjection X Y =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

lemma join_hom_exists_factor_inl_of_cut {X Y : SSet.{u}} {n : ℕ}
    (b : (Δ[n] : SSet.{u}) ⟶ join X Y) (hb : (SSet.yonedaEquiv b).1.val = n + 1) :
    ∃ c : (Δ[n] : SSet.{u}) ⟶ X, c ≫ joinInl X Y = b

lemma join_hom_exists_factor_inr_of_cut {X Y : SSet.{u}} {n : ℕ}
    (b : (Δ[n] : SSet.{u}) ⟶ join X Y) (hb : (SSet.yonedaEquiv b).1.val = 0) :
    ∃ c : (Δ[n] : SSet.{u}) ⟶ Y, c ≫ joinInr X Y = b

lemma prism_eq_comp_endpoint_of_fst {A Y : SSet.{u}} (i : Fin 2)
    (a : A ⟶ (Δ[1] : SSet.{u}) ⊗ Y)
    (ha : a ≫ fst Δ[1] Y = SSet.const (stdSimplex.obj₀Equiv.symm i)) :
    (a ≫ snd Δ[1] Y) ≫ prismEndpoint i Y = a

lemma joinDiagonal_hasLift_of_inl {A B Y : SSet.{u}} (j : A ⟶ B)
    (a : A ⟶ (Δ[1] : SSet.{u}) ⊗ Y) (b : B ⟶ join Y Y) (c : B ⟶ Y)
    (hb : c ≫ joinInl Y Y = b) (sq : CommSq a j (joinDiagonal Y) b) : sq.HasLift

lemma joinDiagonal_hasLift_of_inr {A B Y : SSet.{u}} (j : A ⟶ B)
    (a : A ⟶ (Δ[1] : SSet.{u}) ⊗ Y) (b : B ⟶ join Y Y) (c : B ⟶ Y)
    (hb : c ≫ joinInr Y Y = b) (sq : CommSq a j (joinDiagonal Y) b) : sq.HasLift

instance joinDiagonal_innerFibration (Y : SSet.{u}) [Quasicategory Y] :
    InnerFibration (joinDiagonal Y)

instance relativeJoin_fst_innerFibration {X Y S : SSet.{u}} [Quasicategory S]
    (f : X ⟶ S) (g : Y ⟶ S) :
    InnerFibration (pullback.fst (joinMap f g) (joinDiagonal S))

lemma Join.delta_zero_left_heq_of_left_heq {X Y : SSet.{u}} {n : ℕ}
    (s : Join.Simplex X Y (n + 2)) (t : Join.Simplex X Y (n + 1))
    (hc : s.1.val = t.1.val) (hs : 0 < s.1.val) (hx : HEq s.2.1 t.2.1) :
    HEq (Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 3))).toOrderHom s).2.1
      (Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom t).2.1

lemma Join.delta_last_right_heq_of_right_heq {X Y : SSet.{u}} {n : ℕ}
    (s : Join.Simplex X Y (n + 2)) (t : Join.Simplex X Y (n + 1))
    (hc : n + 3 - s.1.val = n + 2 - t.1.val)
    (hs : s.1.val ≤ n + 2) (ht : t.1.val ≤ n + 1) (hy : HEq s.2.2 t.2.2) :
    HEq (Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom s).2.2
      (Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom t).2.2

lemma Join.Simplex.exists_extreme_faces {X Y : SSet.{u}} {n : ℕ}
    (a b : Join.Simplex X Y (n + 1)) (hc : b.1.val = a.1.val + 1)
    (hab : Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom a =
      Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom b) :
    ∃ s : Join.Simplex X Y (n + 2), s.1.val = b.1.val ∧
      Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 3))).toOrderHom s = a ∧
      Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom s = b

lemma Join.pullCut_delta_inner_mixed (n l : ℕ) (hl0 : 0 < l) (hl1 : l ≤ n + 2)
    (j : Fin (n + 3)) (hj0 : 0 < j) (hj1 : j < Fin.last (n + 2)) :
    0 < Join.pullCut (SimplexCategory.δ j).toOrderHom l ∧
      Join.pullCut (SimplexCategory.δ j).toOrderHom l ≤ n + 1

lemma join_horn_face_cut {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 3))
    (a : (horn (n + 2) i : SSet.{u}) ⟶ join X Y) (t : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (ht : (horn (n + 2) i).ι ≫ t = a ≫ joinIntervalProjection X Y)
    (j : Fin (n + 3)) (hj : j ≠ i) :
    (a.app (Opposite.op ⦋n + 1⦌) (horn.face i j hj)).1.val =
      Join.pullCut (SimplexCategory.δ j).toOrderHom
        (Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1)

lemma horn_inner_face_zero_comp (n : ℕ) (i j : Fin (n + 3)) (hi0 : 0 < i) (hj0 : 0 < j)
    (hji : j ≠ i) :
    stdSimplex.δ (0 : Fin (n + 2)) ≫ horn.ι i j hji =
      stdSimplex.δ (j.pred (ne_of_gt hj0)) ≫ horn.ι i 0 (ne_of_gt hi0).symm

lemma horn_inner_face_last_comp (n : ℕ) (i j : Fin (n + 3))
    (hi1 : i < Fin.last (n + 2)) (hj1 : j < Fin.last (n + 2)) (hji : j ≠ i) :
    stdSimplex.δ (Fin.last (n + 1)) ≫ horn.ι i j hji =
      stdSimplex.δ (j.castPred (ne_of_lt hj1)) ≫ horn.ι i (Fin.last (n + 2)) (ne_of_gt hi1)

lemma intervalSimplex_eq_of_pullCut_eq {n : ℕ} (s t : (Δ[1] : SSet.{u}) _⦋n⦌)
    (hc : Join.pullCut (stdSimplex.objEquiv s).toOrderHom 1 =
      Join.pullCut (stdSimplex.objEquiv t).toOrderHom 1) : s = t

lemma intervalHom_eq_const_one_of_cut_zero {n : ℕ} (t : (Δ[n] : SSet.{u}) ⟶ Δ[1])
    (hc : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = 0) :
    t = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

lemma intervalHom_eq_const_zero_of_cut_all {n : ℕ} (t : (Δ[n] : SSet.{u}) ⟶ Δ[1])
    (hc : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = n + 1) :
    t = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

lemma join_hom_ext_extreme_faces_of_interval {X Y : SSet.{u}} (n : ℕ)
    {f g : (Δ[n + 1] : SSet.{u}) ⟶ join X Y}
    (ht : f ≫ joinIntervalProjection X Y = g ≫ joinIntervalProjection X Y)
    (hs0 : 0 < (SSet.yonedaEquiv f).1.val) (hs1 : (SSet.yonedaEquiv f).1.val ≤ n + 1)
    (h0 : stdSimplex.δ (0 : Fin (n + 2)) ≫ f = stdSimplex.δ (0 : Fin (n + 2)) ≫ g)
    (h1 : stdSimplex.δ (Fin.last (n + 1)) ≫ f = stdSimplex.δ (Fin.last (n + 1)) ≫ g) : f = g

lemma join_horn_hom_ext_extreme_faces {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 3))
    (hi0 : 0 < i) (hi1 : i < Fin.last (n + 2))
    (f g : (horn (n + 2) i : SSet.{u}) ⟶ join X Y)
    (t : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (hft : (horn (n + 2) i).ι ≫ t = f ≫ joinIntervalProjection X Y)
    (hgt : (horn (n + 2) i).ι ≫ t = g ≫ joinIntervalProjection X Y)
    (ht0 : 0 < Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1)
    (ht1 : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 2)
    (h0 : horn.ι i 0 (ne_of_gt hi0).symm ≫ f = horn.ι i 0 (ne_of_gt hi0).symm ≫ g)
    (h1 : horn.ι i (Fin.last (n + 2)) (ne_of_gt hi1) ≫ f =
      horn.ι i (Fin.last (n + 2)) (ne_of_gt hi1) ≫ g) : f = g

lemma join_mixed_innerHorn_filling {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 3))
    (hi0 : 0 < i) (hi1 : i < Fin.last (n + 2))
    (a : (horn (n + 2) i : SSet.{u}) ⟶ join X Y) (t : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (ht : (horn (n + 2) i).ι ≫ t = a ≫ joinIntervalProjection X Y)
    (ht0 : 0 < Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1)
    (ht1 : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 2) :
    ∃ l : (Δ[n + 2] : SSet.{u}) ⟶ join X Y,
      (horn (n + 2) i).ι ≫ l = a ∧ l ≫ joinIntervalProjection X Y = t

instance join_quasicategory (X Y : SSet.{u}) [Quasicategory X] [Quasicategory Y] :
    Quasicategory (join X Y)

instance relativeJoin_quasicategory {X Y S : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory S] (f : X ⟶ S) (g : Y ⟶ S) :
    Quasicategory (relativeJoin f g)

instance relativeJoinProjection_innerFibration {X Y S : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory S] (f : X ⟶ S) (g : Y ⟶ S) :
    InnerFibration (relativeJoinProjection f g)

lemma Join.Simplex.ext_of_joinMap_right_id {X X' Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ X') (s t : Join.Simplex X Y n) (hx : HEq s.2.1 t.2.1)
    (hf : (joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) s =
      (joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) t) : s = t

lemma Join.simplexMap_initial_left_heq {X Y : SSet.{u}} {n : ℕ}
    (s : Join.Simplex X Y n) (hs : s.1.val = 1) :
    HEq (Join.simplexMap X Y (OrderHom.const (Fin 1) (0 : Fin (n + 1))) s).2.1
      s.2.1

lemma Join.Simplex.ext_of_initial_vertex_joinMap {X X' Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ X') (s t : Join.Simplex X Y n)
    (hs : s.1.val = 1) (ht : t.1.val = 1)
    (h0 : Join.simplexMap X Y (OrderHom.const (Fin 1) (0 : Fin (n + 1))) s =
      Join.simplexMap X Y (OrderHom.const (Fin 1) (0 : Fin (n + 1))) t)
    (hf : (joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) s =
      (joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) t) : s = t

lemma Join.Simplex.exists_preimage_cut_one {X X' Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ X') (t : Join.Simplex X' Y n) (ht : t.1.val = 1)
    (x : X _⦋0⦌) (hx : HEq (f.app (Opposite.op ⦋0⦌) x) t.2.1) :
    ∃ s : Join.Simplex X Y n, s.1.val = 1 ∧ HEq s.2.1 x ∧
      (joinMap f (𝟙 Y)).app (Opposite.op ⦋n⦌) s = t

lemma join_hom_ext_of_initial_vertex_joinMap {X X' Y : SSet.{u}} (n : ℕ)
    (f : X ⟶ X') {a b : (Δ[n] : SSet.{u}) ⟶ join X Y}
    (ha : (SSet.yonedaEquiv a).1.val = 1) (hb : (SSet.yonedaEquiv b).1.val = 1)
    (h0 : stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫ a =
      stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫ b)
    (hf : a ≫ joinMap f (𝟙 Y) = b ≫ joinMap f (𝟙 Y)) : a = b

lemma Join.pullCut_delta_one_of_ne_zero (n : ℕ) (j : Fin (n + 3)) (hj : j ≠ 0) :
    Join.pullCut (SimplexCategory.δ j).toOrderHom 1 = 1

lemma initialHorn_face_initial_vertex (n : ℕ) (j : Fin (n + 3)) (hj : j ≠ 0) :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫ horn.ι 0 j hj =
      stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
        horn.ι (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp)

lemma join_initialHorn_hom_ext_of_initial_vertex_joinMap {X X' Y : SSet.{u}} (n : ℕ)
    (f : X ⟶ X') (a b : (horn (n + 2) 0 : SSet.{u}) ⟶ join X Y)
    (t : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (hat : (horn (n + 2) 0).ι ≫ t = a ≫ joinIntervalProjection X Y)
    (hbt : (horn (n + 2) 0).ι ≫ t = b ≫ joinIntervalProjection X Y)
    (ht : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = 1)
    (h0 : (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
      horn.ι (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp)) ≫ a =
      (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0) ≫
        horn.ι (0 : Fin (n + 3)) (Fin.last (n + 2)) (by simp)) ≫ b)
    (hf : a ≫ joinMap f (𝟙 Y) = b ≫ joinMap f (𝟙 Y)) : a = b

lemma joinMap_right_id_initialHorn_hasLift_of_cut_one {X X' Y : SSet.{u}} (n : ℕ)
    (f : X ⟶ X') (a : (horn (n + 2) 0 : SSet.{u}) ⟶ join X Y)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ join X' Y)
    (hsq : (horn (n + 2) 0).ι ≫ b = a ≫ joinMap f (𝟙 Y))
    (hb : (SSet.yonedaEquiv b).1.val = 1) :
    ∃ l : (Δ[n + 2] : SSet.{u}) ⟶ join X Y,
      (horn (n + 2) 0).ι ≫ l = a ∧ l ≫ joinMap f (𝟙 Y) = b

lemma relativeJoin_initialHorn_hasLift_of_coefficient {X Y : SSet.{u}} (n : ℕ)
    (f : X ⟶ Y) (a : (horn (n + 2) 0 : SSet.{u}) ⟶ relativeJoin f (𝟙 Y))
    (b : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (sq : CommSq a (horn (n + 2) 0).ι (relativeJoinProjection f (𝟙 Y)) b)
    (hb : Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv b)).toOrderHom 1 = 1)
    (c : (Δ[n + 2] : SSet.{u}) ⟶ Y)
    (hc : (horn (n + 2) 0).ι ≫ c = a ≫ relativeJoinBaseProjection f (𝟙 Y)) :
    sq.HasLift

lemma intervalHom_cut_one_of_initial_edge (n : ℕ)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (hb : b.app (Opposite.op ⦋1⦌) (initialHornEdge n).val =
      stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) :
    Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv b)).toOrderHom 1 = 1

lemma relativeJoin_crossing_isCocartesian {X Y : SSet.{u}} [Quasicategory Y]
    (f : X ⟶ Y) (e : (relativeJoin f (𝟙 Y)) _⦋1⦌)
    (ht : (relativeJoinProjection f (𝟙 Y)).app (Opposite.op ⦋1⦌) e =
      stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))
    (he : IsInvertibleEdge (edgeOfSimplex
      ((relativeJoinBaseProjection f (𝟙 Y)).app (Opposite.op ⦋1⦌) e))) :
    IsCocartesianEdge (relativeJoinProjection f (𝟙 Y)) e

lemma relativeJoinPrism_vertical_isCocartesian {X Y : SSet.{u}} [Quasicategory Y]
    (f : X ⟶ Y) (x : X _⦋0⦌) :
    IsCocartesianEdge (relativeJoinProjection f (𝟙 Y))
      (prismVerticalSimplex (relativeJoinPrism f) x)

lemma interval_hom_eq_id_or_const (e : (Δ[1] : SSet.{u}) ⟶ Δ[1]) :
    e = 𝟙 Δ[1] ∨ ∃ i : Fin 2, e = SSet.const (stdSimplex.obj₀Equiv.symm i)

lemma cocartesianFibration_interval_of_lift {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) [Quasicategory E] [InnerFibration p]
    (h : ∀ x : E _⦋0⦌, p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm (0 : Fin 2) →
      ∃ l : (Δ[1] : SSet.{u}) ⟶ E,
        stdSimplex.δ 1 ≫ l = SSet.yonedaEquiv.symm x ∧ l ≫ p = 𝟙 Δ[1] ∧
          IsCocartesianEdge p (SSet.yonedaEquiv l)) : CocartesianFibration p

lemma relativeJoin_vertex_inl_of_projection_zero {X Y S : SSet.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (x : (relativeJoin f g) _⦋0⦌)
    (hx : (relativeJoinProjection f g).app (Opposite.op ⦋0⦌) x =
      stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
    ∃ y : X _⦋0⦌, (relativeJoinInl f g).app (Opposite.op ⦋0⦌) y = x

instance relativeJoinProjection_cocartesianFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
    CocartesianFibration (relativeJoinProjection f (𝟙 Y))

lemma isEssentiallySurjective_of_vertexFiberMap {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, IsEssentiallySurjective (vertexFiberMap p q f hf b)) :
    IsEssentiallySurjective f

lemma isEssentiallySurjective_of_vertexFiberMap_equivalence {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [InnerFibration p] [InnerFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b)) :
    IsEssentiallySurjective f

lemma isEssentiallySurjective_over_interval_of_endpoint_fibers {E F : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) (q : F ⟶ Δ[1]) (f : E ⟶ F) (hf : f ≫ q = p)
    (h0 : IsEssentiallySurjective (vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (h1 : IsEssentiallySurjective (vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) :
    IsEssentiallySurjective f

lemma relativeJoin_extension_isEssentiallySurjective {X Y E : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y)
    (p : E ⟶ (Δ[1] : SSet.{u})) [InnerFibration p]
    (G : relativeJoin f (𝟙 Y) ⟶ E) (hG : G ≫ p = relativeJoinProjection f (𝟙 Y))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (hH : relativeJoinPrism f ≫ G = H)
    (g : Y ⟶ E) (hg : relativeJoinInr f (𝟙 Y) ≫ G = g)
    (z0 : X ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz0 : z0 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = prismEndpoint 0 X ≫ H)
    (z1 : Y ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz1 : z1 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g)
    (he0 : IsPrecompositionEquivalence z0) (he1 : IsPrecompositionEquivalence z1) :
    IsEssentiallySurjective G

lemma stdSimplex_vertex_isFullyFaithful {n : ℕ} (b : (Δ[n] : SSet.{u}) _⦋0⦌) :
    IsFullyFaithful (SSet.const b : (Δ[0] : SSet.{u}) ⟶ Δ[n])

lemma vertexFiberι_stdSimplex_isFullyFaithful {E : SSet.{u}} [Quasicategory E]
    {n : ℕ} (p : E ⟶ (Δ[n] : SSet.{u})) (b : (Δ[n] : SSet.{u}) _⦋0⦌) :
    IsFullyFaithful (vertexFiberι p b)

lemma pinchedHomMap_equivalence_of_vertexFiberMap_fullyFaithful
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F] {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u})) (q : F ⟶ Δ[n]) (f : E ⟶ F) (hf : f ≫ q = p)
    (b : (Δ[n] : SSet.{u}) _⦋0⦌)
    (hb : IsFullyFaithful (vertexFiberMap p q f hf b))
    (x y : (vertexFiber p b) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap f x.val y.val)

lemma pinchedHom_isEmpty_of_stdSimplex_reverse {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u})) (x y : E _⦋0⦌)
    (h : (p.app (Opposite.op ⦋0⦌) y) 0 < (p.app (Opposite.op ⦋0⦌) x) 0) (m : ℕ) :
    IsEmpty ((pinchedHom x y) _⦋m⦌)

lemma pinchedHomMap_equivalence_of_stdSimplex_reverse
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F] {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u})) (q : F ⟶ Δ[n]) (f : E ⟶ F) (hf : f ≫ q = p)
    (x y : E _⦋0⦌)
    (h : (p.app (Opposite.op ⦋0⦌) y) 0 < (p.app (Opposite.op ⦋0⦌) x) 0) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap f x y)

lemma isFullyFaithful_over_interval_of_endpoint_fibers_of_crossing
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (p : E ⟶ (Δ[1] : SSet.{u})) (q : F ⟶ Δ[1]) (f : E ⟶ F) (hf : f ≫ q = p)
    (h0 : IsFullyFaithful (vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (h1 : IsFullyFaithful (vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hc : ∀ x y : E _⦋0⦌,
      p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm (0 : Fin 2) →
      p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2) →
        IsSimplicialHomotopyEquivalence (pinchedHomMap f x y)) : IsFullyFaithful f

lemma sliceUnderRestrict_projection {K L X : SSet.{u}} (e : K ⟶ X) (i : L ⟶ K) :
    sliceUnderRestrict e i ≫ sliceUnderProjection (i ≫ e) = sliceUnderProjection e

def cosliceRestrictionFiberMap {K L X : SSet.{u}} (e : K ⟶ X) (i : L ⟶ K)
    (y : X _⦋0⦌) : vertexFiber (sliceUnderProjection e) y ⟶
      vertexFiber (sliceUnderProjection (i ≫ e)) y

lemma cosliceRestrictionFiberMap_trivialKanFibration {K L X : SSet.{u}}
    (e : K ⟶ X) (i : L ⟶ K) [TrivialKanFibration (sliceUnderRestrict e i)]
    (y : X _⦋0⦌) : TrivialKanFibration (cosliceRestrictionFiberMap e i y)

lemma sliceUnderRestrict_target_trivialKanFibration {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    TrivialKanFibration (sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)))

lemma cosliceTriangleTarget_trivialKanFibration {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) (y : X _⦋0⦌) :
    TrivialKanFibration (cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y)

lemma join_hom_ext_stdSimplex_factors {K L : SSet.{u}} {n : ℕ}
    {f g : join K L ⟶ (Δ[n] : SSet.{u})}
    (hl : joinInl K L ≫ f = joinInl K L ≫ g)
    (hr : joinInr K L ≫ f = joinInr K L ≫ g) : f = g

lemma interval_hom_eq_const_one_of_source_one (e : (Δ[1] : SSet.{u}) ⟶ Δ[1])
    (he : stdSimplex.δ (1 : Fin 2) ≫ e = stdSimplex.δ (0 : Fin 2)) :
    e = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

lemma join_interval_cone_inr_eq_const_one {A : SSet.{u}}
    (f : join (Δ[1] : SSet.{u}) A ⟶ Δ[1])
    (hf : joinInl Δ[1] A ≫ f = 𝟙 Δ[1]) :
    joinInr Δ[1] A ≫ f = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

instance intervalIdentityCoslice_subsingleton (m : ℕ) :
    Subsingleton ((sliceUnder (𝟙 (Δ[1] : SSet.{u}))) _⦋m⦌)

lemma intervalIdentityCoslice_projection : sliceUnderProjection (𝟙 (Δ[1] : SSet.{u})) =
    SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

def intervalIdentityCosliceVertex : (sliceUnder (𝟙 (Δ[1] : SSet.{u}))) _⦋0⦌

instance intervalIdentityCoslice_nonempty (m : ℕ) :
    Nonempty ((sliceUnder (𝟙 (Δ[1] : SSet.{u}))) _⦋m⦌)

instance stdSimplexCosliceFiber_subsingleton {K : SSet.{u}} {n : ℕ}
    (e : K ⟶ (Δ[n] : SSet.{u})) (y : (Δ[n] : SSet.{u}) _⦋0⦌) (m : ℕ) :
    Subsingleton ((vertexFiber (sliceUnderProjection e) y) _⦋m⦌)

instance sliceUnderProjection_stdSimplex_mono {K : SSet.{u}} {n : ℕ}
    (e : K ⟶ (Δ[n] : SSet.{u})) : Mono (sliceUnderProjection e)

lemma sliceUnderPostcomp_projection {K X Y : SSet.{u}} (e : K ⟶ X) (p : X ⟶ Y) :
    sliceUnderPostcomp e p ≫ sliceUnderProjection (e ≫ p) = sliceUnderProjection e ≫ p

lemma cosliceTriangleSource_trivialKanFibration {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) (e : (Δ[1] : SSet.{u}) ⟶ E)
    (hp : e ≫ p = 𝟙 Δ[1]) (he : IsCocartesianEdge p (SSet.yonedaEquiv e))
    (y : E _⦋0⦌) (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :
    TrivialKanFibration (cosliceRestrictionFiberMap e (stdSimplex.δ (1 : Fin 2)) y)

def coslicePostcompFiberMap {K E F : SSet.{u}} (e : K ⟶ E) (f : E ⟶ F) (y : E _⦋0⦌) :
    vertexFiber (sliceUnderProjection e) y ⟶
      vertexFiber (sliceUnderProjection (e ≫ f)) (f.app (Opposite.op ⦋0⦌) y)

lemma coslicePostcompFiberMap_ι {K E F : SSet.{u}} (e : K ⟶ E) (f : E ⟶ F) (y : E _⦋0⦌) :
    coslicePostcompFiberMap e f y ≫
      vertexFiberι (sliceUnderProjection (e ≫ f)) (f.app (Opposite.op ⦋0⦌) y) =
        vertexFiberι (sliceUnderProjection e) y ≫ sliceUnderPostcomp e f

lemma coslicePostcompFiberMap_restrict {K L E F : SSet.{u}}
    (e : K ⟶ E) (i : L ⟶ K) (f : E ⟶ F) (y : E _⦋0⦌) :
    cosliceRestrictionFiberMap e i y ≫ coslicePostcompFiberMap (i ≫ e) f y =
      coslicePostcompFiberMap e f y ≫
        cosliceRestrictionFiberMap (e ≫ f) i (f.app (Opposite.op ⦋0⦌) y)

lemma coslicePostcompFiberMap_source_equivalence_of_target
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (p : E ⟶ (Δ[1] : SSet.{u})) (q : F ⟶ Δ[1]) (f : E ⟶ F) (hf : f ≫ q = p)
    (e : (Δ[1] : SSet.{u}) ⟶ E) (hp : e ≫ p = 𝟙 Δ[1])
    (he : IsCocartesianEdge p (SSet.yonedaEquiv e))
    (hef : IsCocartesianEdge q (SSet.yonedaEquiv (e ≫ f)))
    (y : E _⦋0⦌) (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2))
    (ht : IsQCatEquivalence (coslicePostcompFiberMap (stdSimplex.δ (0 : Fin 2) ≫ e) f y)) :
    IsQCatEquivalence (coslicePostcompFiberMap (stdSimplex.δ (1 : Fin 2) ≫ e) f y)

def pointCosliceFiberMap {E F : SSet.{u}} (f : E ⟶ F) (x y : E _⦋0⦌) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ⟶
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm
        (f.app (Opposite.op ⦋0⦌) x))) (f.app (Opposite.op ⦋0⦌) y)

lemma pointCosliceFiberMap_uncurry {A E F : SSet.{u}} {x y : E _⦋0⦌}
    (a : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) (f : E ⟶ F) :
    cosliceFiberUncurry (a ≫ pointCosliceFiberMap f x y) = cosliceFiberUncurry a ≫ f

lemma cosliceIntervalComparison_naturality {E F : SSet.{u}} (f : E ⟶ F) (x y : E _⦋0⦌) :
    pointCosliceFiberMap f x y ≫ cosliceFiberToIntervalMappingSpace
        (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) =
      cosliceFiberToIntervalMappingSpace x y ≫ intervalFunctorMap f x y

lemma pinchedInterval_comparison_eq {E : SSet.{u}} (x y : E _⦋0⦌) :
    PinchedInterval.comparison x y = pinchedHomToIntervalMappingSpace x y

lemma pinchedHomToIntervalMappingSpace_naturality {E F : SSet.{u}}
    (f : E ⟶ F) (x y : E _⦋0⦌) :
    pinchedHomMap f x y ≫ pinchedHomToIntervalMappingSpace
        (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) =
      pinchedHomToIntervalMappingSpace x y ≫ intervalFunctorMap f x y

lemma pointCosliceFiberMap_equivalence_iff_pinchedHomMap
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (f : E ⟶ F) (x y : E _⦋0⦌) :
    IsQCatEquivalence (pointCosliceFiberMap f x y) ↔
      IsSimplicialHomotopyEquivalence (pinchedHomMap f x y)

def cosliceFiberDiagramIso {K E : SSet.{u}} {a b : K ⟶ E} (h : a = b) (y : E _⦋0⦌) :
    vertexFiber (sliceUnderProjection a) y ≅ vertexFiber (sliceUnderProjection b) y

lemma cosliceFiberDiagramIso_uncurry {A K E : SSet.{u}} {a b : K ⟶ E}
    (h : a = b) (y : E _⦋0⦌) (g : A ⟶ vertexFiber (sliceUnderProjection a) y) :
    sliceUnderUncurry ((g ≫ (cosliceFiberDiagramIso h y).hom) ≫
      vertexFiberι (sliceUnderProjection b) y) =
        sliceUnderUncurry (g ≫ vertexFiberι (sliceUnderProjection a) y)

lemma pointCosliceFiberMap_eq_postcomp {E F : SSet.{u}}
    (f : E ⟶ F) (x y : E _⦋0⦌) :
    pointCosliceFiberMap f x y = coslicePostcompFiberMap (SSet.yonedaEquiv.symm x) f y ≫
      (cosliceFiberDiagramIso (SSet.yonedaEquiv_symm_comp x f)
        (f.app (Opposite.op ⦋0⦌) y)).hom

lemma coslicePostcompFiberMap_equivalence_iff_pinchedHomMap
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (a : (Δ[0] : SSet.{u}) ⟶ E) (f : E ⟶ F) (y : E _⦋0⦌) :
    IsQCatEquivalence (coslicePostcompFiberMap a f y) ↔
      IsSimplicialHomotopyEquivalence (pinchedHomMap f (SSet.yonedaEquiv a) y)

lemma cocartesian_crossing_mapping_equivalence_of_target
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (p : E ⟶ (Δ[1] : SSet.{u})) (q : F ⟶ Δ[1]) (f : E ⟶ F) (hf : f ≫ q = p)
    (e : (Δ[1] : SSet.{u}) ⟶ E) (hp : e ≫ p = 𝟙 Δ[1])
    (he : IsCocartesianEdge p (SSet.yonedaEquiv e))
    (hef : IsCocartesianEdge q (SSet.yonedaEquiv (e ≫ f)))
    (y : E _⦋0⦌) (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2))
    (ht : IsSimplicialHomotopyEquivalence
      (pinchedHomMap f (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e)) y)) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap f (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ e)) y)

lemma isFullyFaithful_over_interval_of_endpoint_fibers_of_cocartesian_lifts
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (p : E ⟶ (Δ[1] : SSet.{u})) (q : F ⟶ Δ[1]) (f : E ⟶ F) (hf : f ≫ q = p)
    (h0 : IsFullyFaithful (vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (h1 : IsFullyFaithful (vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hl : ∀ x : E _⦋0⦌,
      p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm (0 : Fin 2) →
      ∃ e : (Δ[1] : SSet.{u}) ⟶ E,
        stdSimplex.δ 1 ≫ e = SSet.yonedaEquiv.symm x ∧ e ≫ p = 𝟙 Δ[1] ∧
          IsCocartesianEdge p (SSet.yonedaEquiv e) ∧
          IsCocartesianEdge q (SSet.yonedaEquiv (e ≫ f))) : IsFullyFaithful f

lemma isQCatEquivalence_over_interval_of_endpoint_fibers_of_cocartesian_lifts
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (p : E ⟶ (Δ[1] : SSet.{u})) (q : F ⟶ Δ[1]) (f : E ⟶ F) (hf : f ≫ q = p)
    (h0 : IsQCatEquivalence (vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (h1 : IsQCatEquivalence (vertexFiberMap p q f hf (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hl : ∀ x : E _⦋0⦌,
      p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm (0 : Fin 2) →
      ∃ e : (Δ[1] : SSet.{u}) ⟶ E,
        stdSimplex.δ 1 ≫ e = SSet.yonedaEquiv.symm x ∧ e ≫ p = 𝟙 Δ[1] ∧
          IsCocartesianEdge p (SSet.yonedaEquiv e) ∧
          IsCocartesianEdge q (SSet.yonedaEquiv (e ≫ f))) : IsQCatEquivalence f

lemma relativeJoin_extension_preserved_lift {X Y E : SSet.{u}} [Quasicategory Y]
    (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u})) (G : relativeJoin f (𝟙 Y) ⟶ E)
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (hH : relativeJoinPrism f ≫ G = H)
    (hc : ∀ x : X _⦋0⦌, IsCocartesianEdge p (prismVerticalSimplex H x))
    (x : (relativeJoin f (𝟙 Y)) _⦋0⦌)
    (hx : (relativeJoinProjection f (𝟙 Y)).app (Opposite.op ⦋0⦌) x =
      stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
    ∃ e : (Δ[1] : SSet.{u}) ⟶ relativeJoin f (𝟙 Y),
      stdSimplex.δ 1 ≫ e = SSet.yonedaEquiv.symm x ∧
      e ≫ relativeJoinProjection f (𝟙 Y) = 𝟙 Δ[1] ∧
      IsCocartesianEdge (relativeJoinProjection f (𝟙 Y)) (SSet.yonedaEquiv e) ∧
      IsCocartesianEdge p (SSet.yonedaEquiv (e ≫ G))

lemma relativeJoin_extension_isQCatEquivalence {X Y E : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory E] (f : X ⟶ Y)
    (p : E ⟶ (Δ[1] : SSet.{u}))
    (G : relativeJoin f (𝟙 Y) ⟶ E) (hG : G ≫ p = relativeJoinProjection f (𝟙 Y))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (hH : relativeJoinPrism f ≫ G = H)
    (g : Y ⟶ E) (hg : relativeJoinInr f (𝟙 Y) ≫ G = g)
    (z0 : X ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz0 : z0 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = prismEndpoint 0 X ≫ H)
    (z1 : Y ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz1 : z1 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g)
    (he0 : IsPrecompositionEquivalence z0) (he1 : IsPrecompositionEquivalence z1)
    (hc : ∀ x : X _⦋0⦌, IsCocartesianEdge p (prismVerticalSimplex H x)) :
    IsQCatEquivalence G

lemma mappingCylinder_isPrecompositionEquivalence_of_quasicategories
    {X Y E : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory E]
    (f : X ⟶ Y) [Mono f] (p : E ⟶ (Δ[1] : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (g : Y ⟶ E)
    (w : prismEndpoint 1 X ≫ H = f ≫ g) (hH : H ≫ p = fst Δ[1] X)
    (hg : g ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (z0 : X ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz0 : z0 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = prismEndpoint 0 X ≫ H)
    (z1 : Y ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz1 : z1 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g)
    (he0 : IsPrecompositionEquivalence z0) (he1 : IsPrecompositionEquivalence z1)
    (hc : ∀ x : X _⦋0⦌, IsCocartesianEdge p (prismVerticalSimplex H x)) :
    IsPrecompositionEquivalence (pushout.desc H g w)

def boundaryInclusions : MorphismProperty SSet.{u}

instance boundaryInclusions_isSmall : MorphismProperty.IsSmall.{u} boundaryInclusions.{u}

instance boundaryInclusions_isCardinalForSmallObjectArgument :
    IsCardinalForSmallObjectArgument boundaryInclusions.{u} Cardinal.aleph0.{u}

instance boundaryInclusions_hasSmallObjectArgument : HasSmallObjectArgument.{u} boundaryInclusions.{u}

lemma boundaryInclusions_rlp_eq : boundaryInclusions.{u}.rlp = trivialKanFibrations

lemma boundaryInclusions_llp_rlp_le_monomorphisms :
    boundaryInclusions.{u}.rlp.llp ≤ monomorphisms SSet

lemma exists_mono_trivialKan_factorization {X Y : SSet.{u}} (f : X ⟶ Y) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y), Mono i ∧ TrivialKanFibration p ∧ i ≫ p = f

noncomputable def mappingCylinderTargetMap {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (q : Z ⟶ Y) (h : g ≫ q = f) :
    pushout (prismEndpoint 1 X) g ⟶ pushout (prismEndpoint 1 X) f

lemma mappingCylinderTargetMap_isPrecompositionEquivalence {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (q : Z ⟶ Y) (h : g ≫ q = f)
    (hq : IsPrecompositionEquivalence q) :
    IsPrecompositionEquivalence (mappingCylinderTargetMap f g q h)

lemma mappingCylinderTargetMap_desc {X Y Z E : SSet.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (q : Z ⟶ Y) (h : g ≫ q = f)
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (k : Y ⟶ E)
    (w : prismEndpoint 1 X ≫ H = f ≫ k)
    (v : prismEndpoint 1 X ≫ H = g ≫ (q ≫ k)) :
    mappingCylinderTargetMap f g q h ≫ pushout.desc H k w = pushout.desc H (q ≫ k) v

lemma mappingCylinder_isPrecompositionEquivalence_of_quasicategory_factors
    {X Y E : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory E]
    (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (g : Y ⟶ E)
    (w : prismEndpoint 1 X ≫ H = f ≫ g) (hH : H ≫ p = fst Δ[1] X)
    (hg : g ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (z0 : X ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz0 : z0 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = prismEndpoint 0 X ≫ H)
    (z1 : Y ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz1 : z1 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g)
    (he0 : IsPrecompositionEquivalence z0) (he1 : IsPrecompositionEquivalence z1)
    (hc : ∀ x : X _⦋0⦌, IsCocartesianEdge p (prismVerticalSimplex H x)) :
    IsPrecompositionEquivalence (pushout.desc H g w)

lemma mono_of_innerAnodyne {X Y : SSet.{u}} (i : X ⟶ Y)
    (hi : innerAnodyneExtensions i) : Mono i

lemma exists_innerAnodyne_innerFibration_factorization {X Y : SSet.{u}} (f : X ⟶ Y) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      innerAnodyneExtensions i ∧ InnerFibration p ∧ i ≫ p = f

lemma exists_quasicategory_resolution_over {X Y : SSet.{u}} [Quasicategory Y] (f : X ⟶ Y) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      innerAnodyneExtensions i ∧ Quasicategory Z ∧ InnerFibration p ∧ i ≫ p = f

lemma innerAnodyne_vertex_bijective {A B : SSet.{u}} (i : A ⟶ B)
    (hi : innerAnodyneExtensions i) : Function.Bijective (i.app (Opposite.op ⦋0⦌))

lemma intervalBoundaryDiagram_postcomp {A E F : SSet.{u}} (a b : A ⟶ E) (f : E ⟶ F) :
    intervalBoundaryDiagram a b ≫ f = intervalBoundaryDiagram (a ≫ f) (b ≫ f)

lemma innerAnodyne_extend_prism_over_interval {A B E : SSet.{u}}
    (i : A ⟶ B) (hi : innerAnodyneExtensions i)
    (p : E ⟶ (Δ[1] : SSet.{u})) [InnerFibration p]
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (hH : H ≫ p = fst Δ[1] A)
    (F0 F1 : B ⟶ E)
    (h0 : i ≫ F0 = prismEndpoint 0 A ≫ H) (h1 : i ≫ F1 = prismEndpoint 1 A ≫ H)
    (h0p : F0 ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (h1p : F1 ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
    ∃ L : (Δ[1] : SSet.{u}) ⊗ B ⟶ E,
      (Δ[1] ◁ i) ≫ L = H ∧ prismEndpoint 0 B ≫ L = F0 ∧
      prismEndpoint 1 B ≫ L = F1 ∧ L ≫ p = fst Δ[1] B

lemma prismVerticalSimplex_naturality {A B E : SSet.{u}} (i : A ⟶ B)
    (H : (Δ[1] : SSet.{u}) ⊗ B ⟶ E) (x : A _⦋0⦌) :
    prismVerticalSimplex ((Δ[1] ◁ i) ≫ H) x =
      prismVerticalSimplex H (i.app (Opposite.op ⦋0⦌) x)

lemma innerAnodyne_prism_vertical_isCocartesian {A B E S : SSet.{u}}
    (i : A ⟶ B) (hi : innerAnodyneExtensions i) (p : E ⟶ S)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (L : (Δ[1] : SSet.{u}) ⊗ B ⟶ E)
    (hL : (Δ[1] ◁ i) ≫ L = H)
    (hc : ∀ x : A _⦋0⦌, IsCocartesianEdge p (prismVerticalSimplex H x)) :
    ∀ y : B _⦋0⦌, IsCocartesianEdge p (prismVerticalSimplex L y)

noncomputable def mappingCylinderMap {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f') :
    pushout (prismEndpoint 1 X) f ⟶ pushout (prismEndpoint 1 X') f'

lemma mappingCylinderMap_isPrecompositionEquivalence {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f')
    (ha : IsPrecompositionEquivalence a) (hb : IsPrecompositionEquivalence b) :
    IsPrecompositionEquivalence (mappingCylinderMap f f' a b h)

lemma mappingCylinderMap_desc {X Y X' Y' E : SSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f')
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (g : Y ⟶ E)
    (H' : (Δ[1] : SSet.{u}) ⊗ X' ⟶ E) (g' : Y' ⟶ E)
    (w : prismEndpoint 1 X ≫ H = f ≫ g) (w' : prismEndpoint 1 X' ≫ H' = f' ≫ g')
    (hH : (Δ[1] ◁ a) ≫ H' = H) (hg : b ≫ g' = g) :
    mappingCylinderMap f f' a b h ≫ pushout.desc H' g' w' = pushout.desc H g w

lemma mappingCylinder_isPrecompositionEquivalence
    {X Y E : SSet.{u}} [Quasicategory E]
    (f : X ⟶ Y) (p : E ⟶ (Δ[1] : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (g : Y ⟶ E)
    (w : prismEndpoint 1 X ≫ H = f ≫ g) (hH : H ≫ p = fst Δ[1] X)
    (_hg : g ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (z0 : X ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz0 : z0 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = prismEndpoint 0 X ≫ H)
    (z1 : Y ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz1 : z1 ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g)
    (he0 : IsPrecompositionEquivalence z0) (he1 : IsPrecompositionEquivalence z1)
    (hc : ∀ x : X _⦋0⦌, IsCocartesianEdge p (prismVerticalSimplex H x)) :
    IsPrecompositionEquivalence (pushout.desc H g w)

lemma IsLeftScaffold.finiteComparison_step (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) [LeftFibration p]
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    (l : simplicialReplacement F ⟶ E) (hs : IsLeftScaffold p F l)
    (h : l ≫ p = simplicialReplacementProjection F)
    (ht : IsPrecompositionEquivalence (leftScaffoldBaseChange p F l h (scaffoldFiniteTail n))) :
    IsPrecompositionEquivalence l

lemma IsLeftScaffold.finiteComparison (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 1)))) [LeftFibration p]
    (F : ULift.{u} (Fin (n + 1)) ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    (l : simplicialReplacement F ⟶ E) (hs : IsLeftScaffold p F l) :
    IsPrecompositionEquivalence l

lemma isPrecompositionEquivalence_of_pullback_finiteNerve
    {C : Type u} [Category.{u} C] {a b : Over (nerve C)} (f : a ⟶ b)
    (hfin : ∀ (n : ℕ) (H : ULift.{u} (Fin (n + 1)) ⥤ C),
      IsPrecompositionEquivalence (overPullbackMap f (Over.mk (nerveMap H)))) :
    IsPrecompositionEquivalence f.left

lemma leftScaffoldBaseChange_overPullbackMap
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (H : D ⥤ C) :
    (simplicialReplacementBaseMap_isPullback H F).flip.isoPullback.hom ≫
        overPullbackMap
          (Over.homMk (U := Over.mk (simplicialReplacementProjection F)) (V := Over.mk p) l h)
          (Over.mk (nerveMap H)) ≫
          (pullbackSymmetry (nerveMap H) p).hom = leftScaffoldBaseChange p F l h H

lemma IsLeftScaffold.overPullback_finiteComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    (l : simplicialReplacement F ⟶ E) (hs : IsLeftScaffold p F l)
    (h : l ≫ p = simplicialReplacementProjection F)
    (n : ℕ) (H : ULift.{u} (Fin (n + 1)) ⥤ C) :
    IsPrecompositionEquivalence
      (overPullbackMap
          (Over.homMk (U := Over.mk (simplicialReplacementProjection F)) (V := Over.mk p) l h)
          (Over.mk (nerveMap H)))

lemma IsLeftScaffold.isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    {p : E ⟶ nerve C} [LeftFibration p]
    {F : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)]
    {l : simplicialReplacement F ⟶ E} (hs : IsLeftScaffold p F l) :
    IsPrecompositionEquivalence l

lemma tautScaffold_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] :
    IsPrecompositionEquivalence (tautScaffold F)

lemma universalScaffold_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    IsPrecompositionEquivalence (universalScaffold p)

lemma exists_innerFibration_comparison_span
    {A X Y S : SSet.{u}} (r : A ⟶ S) (p : X ⟶ S) (q : Y ⟶ S)
    [InnerFibration p] [InnerFibration q]
    (f : A ⟶ X) (g : A ⟶ Y) (hf : f ≫ p = r) (hg : g ≫ q = r)
    (ef : IsPrecompositionEquivalence f) (eg : IsPrecompositionEquivalence g) :
    ∃ (Z : SSet.{u}) (i : A ⟶ Z) (t : Z ⟶ S) (a : Z ⟶ X) (b : Z ⟶ Y),
      innerAnodyneExtensions i ∧ InnerFibration t ∧ i ≫ t = r ∧
      i ≫ a = f ∧ i ≫ b = g ∧ a ≫ p = t ∧ b ≫ q = t ∧
      IsPrecompositionEquivalence a ∧ IsPrecompositionEquivalence b

lemma exists_leftStrictTransport_reconstruction_span
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    ∃ (Z : SSet.{u}) (t : Z ⟶ nerve C) (a : Z ⟶ E)
      (b : Z ⟶ leftStrictTransportWeightedNerve p),
      InnerFibration t ∧ a ≫ p = t ∧ b ≫ leftStrictTransportWeightedProjection p = t ∧
      IsPrecompositionEquivalence a ∧ IsPrecompositionEquivalence b

lemma nonempty_leftStrictTransportTotalEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ nerve C) [LeftFibration p] :
    Nonempty (QCatEquivalence E (leftStrictTransportWeightedNerve p))

noncomputable def leftStrictTransportTotalEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ nerve C) [LeftFibration p] :
    QCatEquivalence E (leftStrictTransportWeightedNerve p)

noncomputable def kanDiagramCoherentNerve
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ SpaceInfinity.{u}

lemma kanDiagramCoherentNerve_vertex
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    (kanDiagramCoherentNerve F).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex c)) =
      spaceInfinityVertex (F.obj c)

lemma kanDiagramCoherentNerve_precomp
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap H) ≫ kanDiagramCoherentNerve F =
      kanDiagramCoherentNerve (H ⋙ F)

noncomputable def leftStraighteningCandidate
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ SpaceInfinity.{u}

lemma leftStraighteningCandidate_vertex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    (leftStraighteningCandidate p).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex c)) =
      spaceInfinityVertex ((leftStrictTransportFunctor p).obj c)

noncomputable def leftStraighteningCandidateFiberEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    QCatEquivalence
      (vertexFiber (leftUnstraighteningProjection (leftStraighteningCandidate p))
        (ULift.up (nerveVertex c)))
      ((SSet.uliftFunctor.{u + 1, u}).obj (vertexFiber p (nerveVertex c)))

lemma leftScaffoldFiberMap_postcomp
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) (f : E ⟶ E') (hf : f ≫ q = p)
    (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F)
    (h' : (l ≫ f) ≫ q = simplicialReplacementProjection F) (c : C) :
    leftScaffoldFiberMap q F (l ≫ f) h' c =
      leftScaffoldFiberMap p F l h c ≫ vertexFiberMap p q f hf (nerveVertex c)

lemma isPrecompositionEquivalence_of_leftFibration_nerve_fibers
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ c : C, IsQCatEquivalence (vertexFiberMap p q f hf (nerveVertex c))) :
    IsPrecompositionEquivalence f

noncomputable def fiberComparisonBaseChange {E E' B K : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p) (g : K ⟶ B) :
    pullback p g ⟶ pullback q g

lemma fiberComparisonBaseChange_projection {E E' B K : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p) (g : K ⟶ B) :
    fiberComparisonBaseChange p q f hf g ≫ pullback.snd q g = pullback.snd p g

lemma fiberComparisonBaseChange_fiber {E E' B K : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p)
    (g : K ⟶ B) (k : K _⦋0⦌) :
    vertexFiberMap (pullback.snd p g) (pullback.snd q g)
        (fiberComparisonBaseChange p q f hf g)
        (fiberComparisonBaseChange_projection p q f hf g) k ≫
      (vertexFiberPullbackIso q g k).hom =
    (vertexFiberPullbackIso p g k).hom ≫
      vertexFiberMap p q f hf (g.app (Opposite.op ⦋0⦌) k)

lemma fiberComparisonBaseChange_overPullbackMap {E E' B K : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p) (g : K ⟶ B) :
    (pullbackSymmetry g p).hom ≫ fiberComparisonBaseChange p q f hf g =
      overPullbackMap (Over.homMk (U := Over.mk p) (V := Over.mk q) f hf) (Over.mk g) ≫
        (pullbackSymmetry g q).hom

lemma isPrecompositionEquivalence_leftFibration_nerveBaseChange
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [LeftFibration p] [LeftFibration q] (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b))
    {C : Type u} [Category.{u} C] (g : nerve C ⟶ B) :
    IsPrecompositionEquivalence (fiberComparisonBaseChange p q f hf g)

lemma isPrecompositionEquivalence_of_leftFibration_fibers
    {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    [LeftFibration p] [LeftFibration q] (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b)) :
    IsPrecompositionEquivalence f

lemma isQCatEquivalence_of_leftFibration_fibers
    {E E' B : SSet.{u}} [Quasicategory E] [Quasicategory E']
    (p : E ⟶ B) (q : E' ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b : B _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b)) :
    IsQCatEquivalence f

lemma kanDiagramCoherentNerve_eq_strictCoherentDiagram
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    kanDiagramCoherentNerve F = HomotopyLimits.strictCoherentDiagram F

lemma weightedPointedKanComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    IsPrecompositionEquivalence
      (HomotopyLimits.weightedCoherentConeComparison F pointKanObject)

lemma coherentConeTotal_transport_projection {K X : SSet.{u}} {F G : K ⟶ X}
    {x y : X _⦋0⦌} (hF : F = G) (hx : x = y)
    (h : HomotopyLimits.coherentConeTotal F x = HomotopyLimits.coherentConeTotal G y) :
    eqToHom h ≫ HomotopyLimits.coherentConeProjection G y =
      HomotopyLimits.coherentConeProjection F x

noncomputable def strictKanUnstraighteningIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    HomotopyLimits.coherentConeTotal (HomotopyLimits.strictCoherentDiagram F)
      (coherentNerveVertex pointKanObject) ≅ leftUnstraightening (kanDiagramCoherentNerve F)

lemma strictKanUnstraighteningIso_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (strictKanUnstraighteningIso F).hom ≫
      leftUnstraighteningProjection (kanDiagramCoherentNerve F) =
    HomotopyLimits.coherentConeProjection (HomotopyLimits.strictCoherentDiagram F)
      (coherentNerveVertex pointKanObject)

noncomputable def strictKanUnstraighteningComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (weightedNerve
        (HomotopyLimits.simplicialHomDiagram F pointKanObject ⋙ SSet.opFunctor)) ⟶
      leftUnstraightening (kanDiagramCoherentNerve F)

lemma strictKanUnstraighteningComparison_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    strictKanUnstraighteningComparison F ≫
      leftUnstraighteningProjection (kanDiagramCoherentNerve F) =
    (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection
        (HomotopyLimits.simplicialHomDiagram F pointKanObject ⋙ SSet.opFunctor))

lemma strictKanUnstraighteningComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    IsPrecompositionEquivalence (strictKanUnstraighteningComparison F)

def kanObjectForget : KanObject.{u} ⥤ SSet.{u}

lemma kanObject_sHomWhiskerLeft (K : KanObject.{u}) {L M : KanObject.{u}} (f : L ⟶ M) :
    (((SimplicialCategory.sHomFunctor KanObject).obj (Opposite.op K)).map f) =
      (ihom K.obj).map f

noncomputable def pointKanObjectHomNatIso :
    (SimplicialCategory.sHomFunctor KanObject.{u}).obj (Opposite.op pointKanObject) ≅
      kanObjectForget

def kanObjectOpFunctor : KanObject.{u} ⥤ KanObject.{u}

noncomputable def oppositePointHomDiagramIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (HomotopyLimits.simplicialHomDiagram (F ⋙ kanObjectOpFunctor) pointKanObject ⋙
      SSet.opFunctor) ≅ F ⋙ kanObjectForget

noncomputable def oppositePointHomWeightedIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    weightedNerve (HomotopyLimits.simplicialHomDiagram
      (F ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor) ≅
      weightedNerve (F ⋙ kanObjectForget)

lemma oppositePointHomWeightedIso_inv_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (oppositePointHomWeightedIso F).inv ≫
      weightedNerveProjection (HomotopyLimits.simplicialHomDiagram
        (F ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor) =
      weightedNerveProjection (F ⋙ kanObjectForget)

noncomputable def oppositeKanUnstraighteningComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve (F ⋙ kanObjectForget)) ⟶
      leftUnstraightening (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor))

lemma oppositeKanUnstraighteningComparison_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    oppositeKanUnstraighteningComparison F ≫
      leftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)) =
      (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (F ⋙ kanObjectForget))

lemma oppositeKanUnstraighteningComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    IsPrecompositionEquivalence (oppositeKanUnstraighteningComparison F)

instance innerFibration_uliftFunctor_map {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p] :
    InnerFibration ((SSet.uliftFunctor.{v, u}).map p)

instance quasicategory_uliftFunctor_obj (E : SSet.{u}) [Quasicategory E] :
    Quasicategory ((SSet.uliftFunctor.{v, u}).obj E)

def uliftTruncatedEdge {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X))
      (ULift.up x) (ULift.up y)

def uliftTruncatedCompStruct {X : SSet.{u}} {x y z : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) y z}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj X) x z}
    (t : SSet.Truncated.Edge.CompStruct e f g) :
    SSet.Truncated.Edge.CompStruct (uliftTruncatedEdge.{u, v} e)
      (uliftTruncatedEdge f) (uliftTruncatedEdge g)

lemma uliftTruncatedEdge_id {X : SSet.{u}} (x : X _⦋0⦌) :
    uliftTruncatedEdge.{u, v} (SSet.Truncated.Edge.id x) =
      SSet.Truncated.Edge.id
        (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X)) (ULift.up x)

lemma IsInvertibleEdge.ulift {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y} (he : IsInvertibleEdge e) :
    IsInvertibleEdge (X := (SSet.uliftFunctor.{v, u}).obj X)
      (uliftTruncatedEdge.{u, v} e)

lemma uliftSimplicialHomotopy_vertexEdge {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (x : X _⦋0⦌) :
    (simplicialHomotopyVertexEdge (uliftSimplicialHomotopy.{u, v} H) (ULift.up x)).toTruncated =
      uliftTruncatedEdge (simplicialHomotopyVertexEdge H x).toTruncated

noncomputable def FunctorIso.ulift {X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) :
    FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g)

lemma IsQCatEquivalence.ulift {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : IsQCatEquivalence f) :
    IsQCatEquivalence ((SSet.uliftFunctor.{v, u}).map f)

noncomputable def leftCoherentTransport
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ SpaceInfinity.{u}

noncomputable def leftCoherentTransportComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj (leftStrictTransportWeightedNerve p) ⟶
      leftUnstraightening (leftCoherentTransport p)

lemma leftCoherentTransportComparison_projection
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    leftCoherentTransportComparison p ≫ leftUnstraighteningProjection (leftCoherentTransport p) =
      (SSet.uliftFunctor.{u + 1, u}).map (leftStrictTransportWeightedProjection p)

lemma leftCoherentTransportComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    IsPrecompositionEquivalence (leftCoherentTransportComparison p)

lemma exists_leftCoherentTransport_reconstruction_span
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    ∃ (Z : SSet.{u + 1})
      (t : Z ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve C))
      (a : Z ⟶ (SSet.uliftFunctor.{u + 1, u}).obj E)
      (b : Z ⟶ leftUnstraightening (leftCoherentTransport p)),
      InnerFibration t ∧ a ≫ (SSet.uliftFunctor.{u + 1, u}).map p = t ∧
      b ≫ leftUnstraighteningProjection (leftCoherentTransport p) = t ∧
      IsPrecompositionEquivalence a ∧ IsPrecompositionEquivalence b

lemma nonempty_leftCoherentTransportEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ nerve C) [LeftFibration p] :
    Nonempty (QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj E)
      (leftUnstraightening (leftCoherentTransport p)))

lemma leftFibration_vertex_surjective_of_essentiallySurjective
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (hp : IsEssentiallySurjective p) : Function.Surjective (p.app (Opposite.op ⦋0⦌))

lemma trivialKanFibration_of_leftFibration_of_isQCatEquivalence
    {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (hp : IsQCatEquivalence p) : TrivialKanFibration p

lemma trivialKanFibration_relativeHom_of_precompositionEquivalence
    {A D E B : SSet.{u}} [Quasicategory B] (i : D ⟶ A) [Mono i]
    (hi : IsPrecompositionEquivalence i) (p : E ⟶ B) [LeftFibration p]
    (r : internalHom.PullbackObjObj i p) : TrivialKanFibration r.π

lemma relativeFunctorPre_trivialKanFibration_of_precompositionEquivalence
    {A D E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (a : A ⟶ B) (i : D ⟶ A) [Mono i] (hi : IsPrecompositionEquivalence i) :
    TrivialKanFibration (relativeFunctorPre p a i)

def relativeFunctorOverPre {E B : SSet.{u}} (p : E ⟶ B) {a b : Over B} (f : a ⟶ b) :
    relativeFunctorSpace p b.hom ⟶ relativeFunctorSpace p a.hom

lemma relativeFunctorOverPre_ι {E B : SSet.{u}} (p : E ⟶ B) {a b : Over B} (f : a ⟶ b) :
    relativeFunctorOverPre p f ≫ vertexFiberι ((ihom a.left).map p) (functorVertex a.hom) =
      vertexFiberι ((ihom b.left).map p) (functorVertex b.hom) ≫ (pre f.left).app E

lemma relativeFunctorOverPre_id {E B : SSet.{u}} (p : E ⟶ B) (a : Over B) :
    relativeFunctorOverPre p (𝟙 a) = 𝟙 (relativeFunctorSpace p a.hom)

lemma relativeFunctorOverPre_comp {E B : SSet.{u}} (p : E ⟶ B) {a b c : Over B}
    (f : a ⟶ b) (g : b ⟶ c) :
    relativeFunctorOverPre p (f ≫ g) = relativeFunctorOverPre p g ≫ relativeFunctorOverPre p f

def relativeFunctorOverFunctor {E B : SSet.{u}} (p : E ⟶ B) : (Over B)ᵒᵖ ⥤ SSet.{u}

lemma relativeFunctorOverPre_isPrecompositionEquivalence_of_mono
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    {a b : Over B} (f : a ⟶ b) [Mono f.left] (hf : IsPrecompositionEquivalence f.left) :
    IsPrecompositionEquivalence (relativeFunctorOverPre p f)

lemma relativeFunctorOverPre_isPrecompositionEquivalence
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    {a b : Over B} (f : a ⟶ b) (hf : IsPrecompositionEquivalence f.left) :
    IsPrecompositionEquivalence (relativeFunctorOverPre p f)

lemma relativeFunctorOverPre_isQCatEquivalence
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    {a b : Over B} (f : a ⟶ b) (hf : IsPrecompositionEquivalence f.left) :
    IsQCatEquivalence (relativeFunctorOverPre p f)

lemma relativeFunctorPre_isQCatEquivalence_of_precompositionEquivalence
    {A D E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (a : A ⟶ B) (i : D ⟶ A) (hi : IsPrecompositionEquivalence i) :
    IsQCatEquivalence (relativeFunctorPre p a i)

noncomputable def relativeFunctorEquivalenceOfSpan
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    {a b c : Over B} (f : c ⟶ a) (g : c ⟶ b)
    (hf : IsPrecompositionEquivalence f.left) (hg : IsPrecompositionEquivalence g.left) :
    QCatEquivalence (relativeFunctorSpace p a.hom) (relativeFunctorSpace p b.hom)

lemma nonempty_leftCoherentTransportRelativeEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] {Y : SSet.{u + 1}}
    (q : Y ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) [LeftFibration q] :
    Nonempty (QCatEquivalence
      (relativeFunctorSpace q ((SSet.uliftFunctor.{u + 1, u}).map p))
      (relativeFunctorSpace q (leftUnstraighteningProjection (leftCoherentTransport p))))

def relativeFunctorVertex {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (f : A ⟶ E) (hf : f ≫ p = a) : (relativeFunctorSpace p a) _⦋0⦌

lemma exists_relativeFunctorVertex {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (v : (relativeFunctorSpace p a) _⦋0⦌) :
    ∃ (f : A ⟶ E) (hf : f ≫ p = a), relativeFunctorVertex p a f hf = v

lemma relativeFunctorOverPre_vertex {E B : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (f : a ⟶ b) (g : b.left ⟶ E) (hg : g ≫ p = b.hom) :
    (relativeFunctorOverPre p f).app (Opposite.op ⦋0⦌) (relativeFunctorVertex p b.hom g hg) =
      relativeFunctorVertex p a.hom (f.left ≫ g)
        (by rw [Category.assoc, hg, f.w])

lemma exists_leftFibration_comparison_of_span
    {E F Z B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration q] (r : Z ⟶ B)
    (a : Z ⟶ E) (b : Z ⟶ F) (ha : a ≫ p = r) (hb : b ≫ q = r)
    (ea : IsPrecompositionEquivalence a) (eb : IsPrecompositionEquivalence b) :
    ∃ f : E ⟶ F, f ≫ q = p ∧ IsPrecompositionEquivalence f

lemma exists_leftCoherentTransport_directComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    ∃ f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶
        leftUnstraightening (leftCoherentTransport p),
      f ≫ leftUnstraighteningProjection (leftCoherentTransport p) =
        (SSet.uliftFunctor.{u + 1, u}).map p ∧ IsPrecompositionEquivalence f

noncomputable def leftCoherentTransportDirectComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening (leftCoherentTransport p)

lemma leftCoherentTransportDirectComparison_projection
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    leftCoherentTransportDirectComparison p ≫
      leftUnstraighteningProjection (leftCoherentTransport p) =
      (SSet.uliftFunctor.{u + 1, u}).map p

lemma leftCoherentTransportDirectComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    IsPrecompositionEquivalence (leftCoherentTransportDirectComparison p)

lemma leftCoherentTransportDirectComparison_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ nerve C) [LeftFibration p] :
    IsQCatEquivalence (leftCoherentTransportDirectComparison p)

def relativeFunctorEvaluation {B : SSet.{u}} (a b : Over B) :
    a.left ⊗ relativeFunctorSpace b.hom a.hom ⟶ b.left

lemma relativeFunctorEvaluation_projection {B : SSet.{u}} (a b : Over B) :
    relativeFunctorEvaluation a b ≫ b.hom =
      fst a.left (relativeFunctorSpace b.hom a.hom) ≫ a.hom

def relativeFunctorComposition {B : SSet.{u}} (a b c : Over B) :
    relativeFunctorSpace b.hom a.hom ⊗ relativeFunctorSpace c.hom b.hom ⟶
      relativeFunctorSpace c.hom a.hom

lemma relativeFunctorComposition_ι {B : SSet.{u}} (a b c : Over B) :
    relativeFunctorComposition a b c ≫
      vertexFiberι ((ihom a.left).map c.hom) (functorVertex a.hom) =
    (vertexFiberι ((ihom a.left).map b.hom) (functorVertex a.hom) ⊗ₘ
      vertexFiberι ((ihom b.left).map c.hom) (functorVertex b.hom)) ≫
      MonoidalClosed.comp a.left b.left c.left

def relativeFunctorIdentity {B : SSet.{u}} (a : Over B) :
    𝟙_ SSet.{u} ⟶ relativeFunctorSpace a.hom a.hom

lemma relativeFunctorIdentity_ι {B : SSet.{u}} (a : Over B) :
    relativeFunctorIdentity a ≫
      vertexFiberι ((ihom a.left).map a.hom) (functorVertex a.hom) =
      MonoidalClosed.id a.left

lemma relativeFunctorIdentity_comp {B : SSet.{u}} (a b : Over B) :
    (λ_ (relativeFunctorSpace b.hom a.hom)).inv ≫
      relativeFunctorIdentity a ▷ _ ≫ relativeFunctorComposition a a b = 𝟙 _

lemma relativeFunctorComposition_id {B : SSet.{u}} (a b : Over B) :
    (ρ_ (relativeFunctorSpace b.hom a.hom)).inv ≫
      _ ◁ relativeFunctorIdentity b ≫ relativeFunctorComposition a b b = 𝟙 _

lemma relativeFunctorComposition_assoc {B : SSet.{u}} (a b c d : Over B) :
    (α_ (relativeFunctorSpace b.hom a.hom) (relativeFunctorSpace c.hom b.hom)
      (relativeFunctorSpace d.hom c.hom)).inv ≫
      relativeFunctorComposition a b c ▷ _ ≫ relativeFunctorComposition a c d =
    _ ◁ relativeFunctorComposition b c d ≫ relativeFunctorComposition a b d

noncomputable def relativeFunctorVertexEquiv {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    {f : A ⟶ E // f ≫ p = a} ≃ (relativeFunctorSpace p a) _⦋0⦌

def overHomEquivSubtype {B : SSet.{u}} (a b : Over B) :
    (a ⟶ b) ≃ {f : a.left ⟶ b.left // f ≫ b.hom = a.hom}

noncomputable def relativeFunctorHomEquiv {B : SSet.{u}} (a b : Over B) :
    (a ⟶ b) ≃ (𝟙_ SSet.{u} ⟶ relativeFunctorSpace b.hom a.hom)

lemma relativeFunctorHomEquiv_ι {B : SSet.{u}} {a b : Over B} (f : a ⟶ b) :
    relativeFunctorHomEquiv a b f ≫
      vertexFiberι ((ihom a.left).map b.hom) (functorVertex a.hom) = curry' f.left

lemma relativeFunctorHomEquiv_id {B : SSet.{u}} (a : Over B) :
    relativeFunctorHomEquiv a a (𝟙 a) = relativeFunctorIdentity a

lemma relativeFunctorHomEquiv_comp {B : SSet.{u}} {a b c : Over B}
    (f : a ⟶ b) (g : b ⟶ c) :
    relativeFunctorHomEquiv a c (f ≫ g) =
      (λ_ (𝟙_ SSet.{u})).inv ≫
        (relativeFunctorHomEquiv a b f ⊗ₘ relativeFunctorHomEquiv b c g) ≫
          relativeFunctorComposition a b c

def LeftFibrationObject (B : SSet.{u})

instance leftFibrationObject_category (B : SSet.{u}) : Category.{u} (LeftFibrationObject B)

instance leftFibrationObject_projection {B : SSet.{u}} (p : LeftFibrationObject B) :
    LeftFibration p.val.hom

instance leftFibrationObject_enrichedCategory (B : SSet.{u}) :
    EnrichedCategory SSet.{u} (LeftFibrationObject B)

noncomputable instance leftFibrationObject_simplicialCategory (B : SSet.{u}) :
    SimplicialCategory (LeftFibrationObject B)

instance leftFibrationObject_sHom_kanComplex {B : SSet.{u}} (p q : LeftFibrationObject B) :
    KanComplex (SimplicialCategory.sHom p q)

noncomputable def LeftFibrationInfinity (B : SSet.{u}) : SSet.{u + 1}

instance leftFibrationInfinity_quasicategory (B : SSet.{u}) :
    Quasicategory (LeftFibrationInfinity B)

def leftFibrationObjectOf {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    LeftFibrationObject B

noncomputable def leftFibrationInfinityVertex {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] : (LeftFibrationInfinity B) _⦋0⦌

noncomputable def leftFibrationInfinityEdge {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    (LeftFibrationInfinity B).Edge
      (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q)

noncomputable def leftFibrationInfinityMappingEquivalence {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj (relativeFunctorSpace q p))
      (pinchedHom (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q))

def relativeFunctorPostHom {B : SSet.{u}} (a b c : Over B) :
    relativeFunctorSpace c.hom b.hom ⟶
      (ihom (relativeFunctorSpace b.hom a.hom)).obj (relativeFunctorSpace c.hom a.hom)

lemma relativeFunctorPostHom_id {B : SSet.{u}} (a b : Over B) :
    relativeFunctorIdentity b ≫ relativeFunctorPostHom a b b =
      MonoidalClosed.id (relativeFunctorSpace b.hom a.hom)

lemma relativeFunctorPostHom_comp_uncurry {B : SSet.{u}} (a b c d : Over B) :
    uncurry ((relativeFunctorPostHom a b c ⊗ₘ relativeFunctorPostHom a c d) ≫
      MonoidalClosed.comp (relativeFunctorSpace b.hom a.hom)
        (relativeFunctorSpace c.hom a.hom) (relativeFunctorSpace d.hom a.hom)) =
    (α_ (relativeFunctorSpace b.hom a.hom) (relativeFunctorSpace c.hom b.hom)
      (relativeFunctorSpace d.hom c.hom)).inv ≫
      relativeFunctorComposition a b c ▷ _ ≫ relativeFunctorComposition a c d

lemma relativeFunctorPostHom_comp {B : SSet.{u}} (a b c d : Over B) :
    relativeFunctorComposition b c d ≫ relativeFunctorPostHom a b d =
    (relativeFunctorPostHom a b c ⊗ₘ relativeFunctorPostHom a c d) ≫
      MonoidalClosed.comp (relativeFunctorSpace b.hom a.hom)
        (relativeFunctorSpace c.hom a.hom) (relativeFunctorSpace d.hom a.hom)

def relativeFunctorEnrichedEvaluation {B : SSet.{u}} (a : Over B) :
    EnrichedFunctor SSet.{u} (LeftFibrationObject B) KanObject.{u}

lemma relativeFunctorComposition_overPre {B : SSet.{u}} {a b : Over B}
    (f : a ⟶ b) (p q : Over B) :
    relativeFunctorComposition b p q ≫ relativeFunctorOverPre q.hom f =
      relativeFunctorOverPre p.hom f ▷ _ ≫ relativeFunctorComposition a p q

lemma relativeFunctorPostHom_overPre {B : SSet.{u}} {a b : Over B}
    (f : a ⟶ b) (p q : Over B) :
    relativeFunctorPostHom b p q ≫
      (ihom (relativeFunctorSpace p.hom b.hom)).map (relativeFunctorOverPre q.hom f) =
    relativeFunctorPostHom a p q ≫
      (pre (relativeFunctorOverPre p.hom f)).app (relativeFunctorSpace q.hom a.hom)

def coherentNerveMap {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D] (F : EnrichedFunctor SSet.{u} C D) :
    SimplicialNerve C ⟶ SimplicialNerve D

lemma coherentNerveMap_id (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    coherentNerveMap (EnrichedFunctor.id SSet.{u} C) = 𝟙 (SimplicialNerve C)

lemma coherentNerveMap_comp {C D E : Type v} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    [SimplicialCategory C] [SimplicialCategory D] [SimplicialCategory E]
    (F : EnrichedFunctor SSet.{u} C D) (G : EnrichedFunctor SSet.{u} D E) :
    coherentNerveMap (F.comp SSet G) = coherentNerveMap F ≫ coherentNerveMap G

lemma coherentNerveMap_vertex {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (c : C) :
    (coherentNerveMap F).app (Opposite.op ⦋0⦌) (coherentNerveVertex c) =
      coherentNerveVertex (F.obj c)

noncomputable def leftFibrationCoherentEvaluation {B : SSet.{u}} (a : Over B) :
    LeftFibrationInfinity B ⟶ SpaceInfinity.{u}

lemma leftFibrationCoherentEvaluation_vertex {E B : SSet.{u}} (a : Over B)
    (p : E ⟶ B) [LeftFibration p] :
    (leftFibrationCoherentEvaluation a).app (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p) =
      spaceInfinityVertex
        ((relativeFunctorEnrichedEvaluation a).obj (leftFibrationObjectOf p))

noncomputable def leftStrictTransportCoherentEvaluation {C : Type u} [Category.{u} C] (c : C) :
    LeftFibrationInfinity (nerve C) ⟶ SpaceInfinity.{u}

lemma leftStrictTransportCoherentEvaluation_vertex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (c : C) :
    (leftStrictTransportCoherentEvaluation c).app (Opposite.op ⦋0⦌)
      (leftFibrationInfinityVertex p) =
      spaceInfinityVertex ((leftStrictTransportFunctor p).obj c)

def relativeFunctorMixedHom {B : SSet.{u}} {a b : Over B} (f : a ⟶ b) (p q : Over B) :
    relativeFunctorSpace q.hom p.hom ⟶
      (ihom (relativeFunctorSpace p.hom b.hom)).obj (relativeFunctorSpace q.hom a.hom)

lemma relativeFunctorMixedHom_id {B : SSet.{u}} (a p : Over B) :
    relativeFunctorIdentity p ≫ relativeFunctorMixedHom (𝟙 a) p p =
      MonoidalClosed.id (relativeFunctorSpace p.hom a.hom)

lemma relativeFunctorMixedHom_comp {B : SSet.{u}} {a b c : Over B}
    (f : b ⟶ a) (g : c ⟶ b) (p q r : Over B) :
    relativeFunctorComposition p q r ≫ relativeFunctorMixedHom (g ≫ f) p r =
      (relativeFunctorMixedHom f p q ⊗ₘ relativeFunctorMixedHom g q r) ≫
        MonoidalClosed.comp (relativeFunctorSpace p.hom a.hom)
          (relativeFunctorSpace q.hom b.hom) (relativeFunctorSpace r.hom c.hom)

def diagonalRelativeObject {B : SSet.{u}} {J : Type u} [LinearOrder J]
    (A : Jᵒᵖ ⥤ Over B)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (LeftFibrationObject B))
    (i : SimplicialThickening J) : KanObject.{u}

noncomputable def diagonalRelativeHom {B : SSet.{u}} {J : Type u} [LinearOrder J]
    (A : Jᵒᵖ ⥤ Over B)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (LeftFibrationObject B))
    (i j : SimplicialThickening J) :
    SimplicialCategory.sHom i j ⟶
      SimplicialCategory.sHom (diagonalRelativeObject A F i) (diagonalRelativeObject A F j)

lemma diagonalRelativeHom_of_le {B : SSet.{u}} {J : Type u} [LinearOrder J]
    (A : Jᵒᵖ ⥤ Over B)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (LeftFibrationObject B))
    (i j : SimplicialThickening J) (h : i.as ≤ j.as) :
    diagonalRelativeHom A F i j =
      F.map i j ≫ relativeFunctorMixedHom (A.map (homOfLE h).op) (F.obj i).val (F.obj j).val

noncomputable def diagonalRelativeEvaluation {B : SSet.{u}} {J : Type u} [LinearOrder J]
    (A : Jᵒᵖ ⥤ Over B)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (LeftFibrationObject B)) :
    EnrichedFunctor SSet.{u} (SimplicialThickening J) KanObject.{u}

lemma diagonalRelativeEvaluation_reindex {B : SSet.{u}} {J K : Type u}
    [LinearOrder J] [LinearOrder K] (α : J →o K) (A : Kᵒᵖ ⥤ Over B)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening K) (LeftFibrationObject B)) :
    (SimplicialThickening.functor α).comp SSet (diagonalRelativeEvaluation A F) =
      diagonalRelativeEvaluation (α.toFunctor.op ⋙ A)
        ((SimplicialThickening.functor α).comp SSet F)

def underNerveDiagram (C : Type u) [Category.{u} C] : Cᵒᵖ ⥤ Over (nerve C)

def strictTransportSimplexUnderDiagram {C : Type u} [Category.{u} C] {n : ℕ}
    (σ : (nerve C) _⦋n⦌) : (ULift.{u} (Fin (n + 1)))ᵒᵖ ⥤ Over (nerve C)

lemma strictTransportSimplexUnderDiagram_reindex
    {C : Type u} [Category.{u} C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (nerve C) _⦋n⦌) :
    α.toOrderHom.uliftMap.toFunctor.op ⋙ strictTransportSimplexUnderDiagram σ =
      strictTransportSimplexUnderDiagram ((nerve C).map α.op σ)

noncomputable def strictTransportDiagonalSimplex
    {C : Type u} [Category.{u} C] {n : ℕ} (σ : (nerve C) _⦋n⦌)
    (F : (LeftFibrationInfinity (nerve C)) _⦋n⦌) : SpaceInfinity.{u} _⦋n⦌

lemma strictTransportDiagonalSimplex_naturality
    {C : Type u} [Category.{u} C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (nerve C) _⦋n⦌) (F : (LeftFibrationInfinity (nerve C)) _⦋n⦌) :
    SpaceInfinity.map α.op (strictTransportDiagonalSimplex σ F) =
      strictTransportDiagonalSimplex ((nerve C).map α.op σ)
        ((LeftFibrationInfinity (nerve C)).map α.op F)

noncomputable def strictTransportJointEvaluation (C : Type u) [Category.{u} C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⊗ LeftFibrationInfinity (nerve C) ⟶
      SpaceInfinity.{u}

noncomputable def leftStraighteningCoherentMap (C : Type u) [Category.{u} C] :
    LeftFibrationInfinity (nerve C) ⟶
      SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))

lemma leftStraighteningCoherentMap_uncurry (C : Type u) [Category.{u} C] :
    uncurry (leftStraighteningCoherentMap C) = strictTransportJointEvaluation C

lemma relativeFunctorMixedHom_unit {B : SSet.{u}} {a b : Over B} (f : a ⟶ b) (p : Over B) :
    relativeFunctorIdentity p ≫ relativeFunctorMixedHom f p p =
      curry' (relativeFunctorOverPre p.hom f)

noncomputable def enrichedConstantOrderDiagram (J : Type u) [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (c : C) :
    EnrichedFunctor SSet.{u} (SimplicialThickening J) C

lemma coherentNerveVertex_constant {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (c : C) (n : ℕ) :
    PinchedHom.constant (coherentNerveVertex c) n =
      enrichedConstantOrderDiagram (ULift.{u} (Fin (n + 1))) c

def relativeFunctorKanDiagram {B : SSet.{u}} {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) (p : LeftFibrationObject B) : J ⥤ KanObject.{u}

lemma diagonalRelativeEvaluation_constant {B : SSet.{u}} {J : Type u} [LinearOrder J]
    (A : Jᵒᵖ ⥤ Over B) (p : LeftFibrationObject B) :
    diagonalRelativeEvaluation A (enrichedConstantOrderDiagram J p) =
      enrichedFunctorOfOrderDiagram (relativeFunctorKanDiagram A p)

lemma strictTransportSimplex_relativeFunctorKanDiagram
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] {n : ℕ} (σ : (nerve C) _⦋n⦌) :
    relativeFunctorKanDiagram (strictTransportSimplexUnderDiagram σ) (leftFibrationObjectOf p) =
      (⟨ULift.down, fun _ _ h ↦ h⟩ :
        ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙ σ ⋙ leftStrictTransportFunctor p

lemma strictTransportDiagonalSimplex_constant
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] {n : ℕ} (σ : (nerve C) _⦋n⦌) :
    strictTransportDiagonalSimplex σ (PinchedHom.constant (leftFibrationInfinityVertex p) n) =
      (kanDiagramCoherentNerve (leftStrictTransportFunctor p)).app
        (Opposite.op ⦋n⦌) (ULift.up σ)

lemma leftStraighteningCoherentMap_vertex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    (leftStraighteningCoherentMap C).app (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p) =
      functorVertex (leftStraighteningCandidate p)

lemma relativeFunctorMixedHom_domain_id {B : SSet.{u}} (a p q : Over B) :
    relativeFunctorMixedHom (𝟙 a) p q = relativeFunctorPostHom a p q

lemma diagonalRelativeEvaluation_constant_base
    {B : SSet.{u}} {J : Type u} [LinearOrder J] (a : Over B)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (LeftFibrationObject B)) :
    diagonalRelativeEvaluation ((Functor.const Jᵒᵖ).obj a) F =
      F.comp SSet (relativeFunctorEnrichedEvaluation a)

lemma strictTransportSimplexUnderDiagram_constant
    {C : Type u} [Category.{u} C] (c : C) (n : ℕ) :
    strictTransportSimplexUnderDiagram (PinchedHom.constant (nerveVertex c) n) =
      (Functor.const (ULift.{u} (Fin (n + 1)))ᵒᵖ).obj
        (Over.mk (nerveMap (Under.forget c)))

lemma strictTransportDiagonalSimplex_constant_base
    {C : Type u} [Category.{u} C] (c : C) {n : ℕ}
    (F : (LeftFibrationInfinity (nerve C)) _⦋n⦌) :
    strictTransportDiagonalSimplex (PinchedHom.constant (nerveVertex c) n) F =
      (leftStrictTransportCoherentEvaluation c).app (Opposite.op ⦋n⦌) F

lemma leftStraighteningCoherentMap_evaluate
    {C : Type u} [Category.{u} C] (c : C) :
    leftStraighteningCoherentMap C ≫ evaluateFunctorAt (ULift.up (nerveVertex c)) =
      leftStrictTransportCoherentEvaluation c

lemma relativeFunctorPostHom_ordinary {B : SSet.{u}} (a b c : Over B) (f : b ⟶ c) :
    relativeFunctorHomEquiv b c f ≫ relativeFunctorPostHom a b c =
      curry' (HomotopyLimits.relativeFunctorPost b.hom c.hom f.left f.w a.hom)

def edgewiseWeight : SimplexCategory ⥤ SSet.{u}

def edgewiseSubdivision (X : SSet.{u}) : SSet.{u}

def edgewiseSubdivisionMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    edgewiseSubdivision X ⟶ edgewiseSubdivision Y

def edgewiseSubdivisionFunctor : SSet.{u} ⥤ SSet.{u}

lemma edgewiseStdSimplex_opIso_inv_naturality {a b : SimplexCategory} (α : a ⟶ b) :
    (stdSimplex.opIso.{u} a).inv ≫
        SSet.opFunctor.map (stdSimplex.map (SimplexCategory.rev.map α)) =
      stdSimplex.map α ≫ (stdSimplex.opIso b).inv

def edgewiseRight (X : SSet.{u}) : edgewiseSubdivision X ⟶ X

def edgewiseLeft (X : SSet.{u}) : edgewiseSubdivision X ⟶ X.op

lemma edgewiseRight_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    edgewiseSubdivisionMap f ≫ edgewiseRight Y = edgewiseRight X ≫ f

lemma edgewiseLeft_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    edgewiseSubdivisionMap f ≫ edgewiseLeft Y = edgewiseLeft X ≫ SSet.opFunctor.map f

def edgewiseWeightIso (n : ℕ) :
    edgewiseWeight.{u}.obj ⦋n⦌ ≅ (Δ[n + n + 1] : SSet.{u})

def edgewiseSimplexEquiv (X : SSet.{u}) (n : ℕ) :
    (edgewiseSubdivision X) _⦋n⦌ ≃ X _⦋n + n + 1⦌

lemma edgewiseSimplexEquiv_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (s : (edgewiseSubdivision X) _⦋n⦌) :
    edgewiseSimplexEquiv Y n ((edgewiseSubdivisionMap f).app (Opposite.op ⦋n⦌) s) =
      f.app (Opposite.op ⦋n + n + 1⦌) (edgewiseSimplexEquiv X n s)

lemma edgewiseSubdivision_yoneda_restriction {X : SSet.{u}}
    {m n : SimplexCategory} (α : m ⟶ n) (f : stdSimplex.obj n ⟶ edgewiseSubdivision X) :
    SSet.yonedaEquiv (stdSimplex.map α ≫ f) =
      edgewiseWeight.map α ≫ SSet.yonedaEquiv f

lemma edgewiseSubdivision_boundary_extension {X : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ edgewiseSubdivision X)
    (F : edgewiseWeight.obj ⦋n + 1⦌ ⟶ X)
    (hF : ∀ i : Fin (n + 2), edgewiseWeight.map (SimplexCategory.δ i) ≫ F =
      SSet.yonedaEquiv (boundary.ι i ≫ a)) :
    (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm F = a

lemma edgewiseRight_boundary_hasLift_iff {X : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ edgewiseSubdivision X)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (sq : CommSq a (boundary (n + 1)).ι (edgewiseRight X) b) :
    sq.HasLift ↔ ∃ F : edgewiseWeight.obj ⦋n + 1⦌ ⟶ X,
      (∀ i : Fin (n + 2), edgewiseWeight.map (SimplexCategory.δ i) ≫ F =
        SSet.yonedaEquiv (boundary.ι i ≫ a)) ∧
      joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1] ≫ F = b

lemma edgewiseRight_boundary_zero_lifting (X : SSet.{u}) :
    HasLiftingProperty (boundary.{u} 0).ι (edgewiseRight X)

lemma edgewiseRight_trivialKanFibration_of_extensions (X : SSet.{u})
    (h : ∀ (n : ℕ) (a : (boundary (n + 1) : SSet.{u}) ⟶ edgewiseSubdivision X)
      (b : (Δ[n + 1] : SSet.{u}) ⟶ X)
      (_ : CommSq a (boundary (n + 1)).ι (edgewiseRight X) b),
      ∃ F : edgewiseWeight.obj ⦋n + 1⦌ ⟶ X,
        (∀ i : Fin (n + 2), edgewiseWeight.map (SimplexCategory.δ i) ≫ F =
          SSet.yonedaEquiv (boundary.ι i ≫ a)) ∧
        joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1] ≫ F = b) :
    TrivialKanFibration (edgewiseRight X)

def edgewiseLeftVertex (n : ℕ) (i : Fin (n + 1)) : Fin (n + n + 1 + 1)

def edgewiseRightVertex (n : ℕ) (i : Fin (n + 1)) : Fin (n + n + 1 + 1)

def edgewiseRightVertices (n : ℕ) : Finset (Fin (n + n + 1 + 1))

def edgewiseRightExtensionDomain (n : ℕ) : (Δ[n + n + 1] : SSet.{u}).Subcomplex

lemma mem_edgewiseRightExtensionDomain_iff {n d : ℕ}
    (s : (Δ[n + n + 1] : SSet.{u}) _⦋d⦌) :
    s ∈ (edgewiseRightExtensionDomain n).obj (Opposite.op ⦋d⦌) ↔
      (∀ j : Fin (d + 1), n < (s j).val) ∨
        ∃ i : Fin (n + 1), ∀ j : Fin (d + 1),
          s j ≠ edgewiseLeftVertex n i ∧ s j ≠ edgewiseRightVertex n i

lemma edgewiseLeftVertex_ne_right (n : ℕ) (i j : Fin (n + 1)) :
    edgewiseLeftVertex n i ≠ edgewiseRightVertex n j

def EdgewiseSupportInDomain (n : ℕ) (S : Finset (Fin (n + n + 1 + 1))) : Prop

lemma mem_edgewiseRightExtensionDomain_iff_support {n d : ℕ}
    (s : (Δ[n + n + 1] : SSet.{u}) _⦋d⦌) :
    s ∈ (edgewiseRightExtensionDomain n).obj (Opposite.op ⦋d⦌) ↔
      EdgewiseSupportInDomain n (Finset.univ.image s)

lemma edgewiseRightVertex_injective (n : ℕ) : Function.Injective (edgewiseRightVertex n)

lemma edgewiseSupportInDomain_insert_right_iff {n : ℕ}
    (S : Finset (Fin (n + n + 1 + 1))) (i : Fin (n + 1))
    (hi : edgewiseLeftVertex n i ∈ S) :
    EdgewiseSupportInDomain n (insert (edgewiseRightVertex n i) S) ↔
      EdgewiseSupportInDomain n S

lemma edgewiseSupportInDomain_erase_right_iff {n : ℕ}
    (S : Finset (Fin (n + n + 1 + 1))) (i : Fin (n + 1))
    (hi : edgewiseLeftVertex n i ∈ S) :
    EdgewiseSupportInDomain n (S.erase (edgewiseRightVertex n i)) ↔
      EdgewiseSupportInDomain n S

def edgewiseLeftSupport (n : ℕ) (S : Finset (Fin (n + n + 1 + 1))) : Finset (Fin (n + 1))

lemma edgewiseLeftSupport_nonempty {n : ℕ}
    (S : Finset (Fin (n + n + 1 + 1))) (h : ¬ EdgewiseSupportInDomain n S) :
    (edgewiseLeftSupport n S).Nonempty

def edgewiseSupportPivot {n : ℕ} (S : Finset (Fin (n + n + 1 + 1)))
    (h : ¬ EdgewiseSupportInDomain n S) : Fin (n + 1)

lemma edgewiseSupportPivot_mem {n : ℕ} (S : Finset (Fin (n + n + 1 + 1)))
    (h : ¬ EdgewiseSupportInDomain n S) :
    edgewiseLeftVertex n (edgewiseSupportPivot S h) ∈ S

lemma edgewiseSupportPivot_le {n : ℕ} (S : Finset (Fin (n + n + 1 + 1)))
    (h : ¬ EdgewiseSupportInDomain n S) (i : Fin (n + 1))
    (hi : edgewiseLeftVertex n i ∈ S) : edgewiseSupportPivot S h ≤ i

lemma edgewiseSupportPivot_le_of_subset_pair {n : ℕ}
    (S T : Finset (Fin (n + n + 1 + 1)))
    (hS : ¬ EdgewiseSupportInDomain n S) (hT : ¬ EdgewiseSupportInDomain n T)
    (hST : S ⊆ insert (edgewiseRightVertex n (edgewiseSupportPivot T hT)) T) :
    edgewiseSupportPivot T hT ≤ edgewiseSupportPivot S hS

lemma edgewiseSupport_card_lt_of_pivot_eq {n : ℕ}
    (S T : Finset (Fin (n + n + 1 + 1)))
    (hS : ¬ EdgewiseSupportInDomain n S) (hT : ¬ EdgewiseSupportInDomain n T)
    (hST : S ⊆ insert (edgewiseRightVertex n (edgewiseSupportPivot T hT)) T)
    (hR : edgewiseRightVertex n (edgewiseSupportPivot S hS) ∉ S)
    (hP : edgewiseSupportPivot S hS = edgewiseSupportPivot T hT) (hne : S ≠ T) :
    S.card < T.card

lemma edgewiseSupport_rank_lt {n : ℕ}
    (S T : Finset (Fin (n + n + 1 + 1)))
    (hS : ¬ EdgewiseSupportInDomain n S) (hT : ¬ EdgewiseSupportInDomain n T)
    (hST : S ⊆ insert (edgewiseRightVertex n (edgewiseSupportPivot T hT)) T)
    (hR : edgewiseRightVertex n (edgewiseSupportPivot S hS) ∉ S) (hne : S ≠ T) :
    Prod.Lex (· < ·) (· < ·)
      (n - (edgewiseSupportPivot S hS).val, S.card)
      (n - (edgewiseSupportPivot T hT).val, T.card)

lemma edgewiseLeftSupport_insert_right {n : ℕ}
    (S : Finset (Fin (n + n + 1 + 1))) (i : Fin (n + 1)) :
    edgewiseLeftSupport n (insert (edgewiseRightVertex n i) S) = edgewiseLeftSupport n S

lemma edgewiseLeftSupport_erase_right {n : ℕ}
    (S : Finset (Fin (n + n + 1 + 1))) (i : Fin (n + 1)) :
    edgewiseLeftSupport n (S.erase (edgewiseRightVertex n i)) = edgewiseLeftSupport n S

lemma edgewiseSupportPivot_eq_of_leftSupport_eq {n : ℕ}
    (S T : Finset (Fin (n + n + 1 + 1)))
    (hS : ¬ EdgewiseSupportInDomain n S) (hT : ¬ EdgewiseSupportInDomain n T)
    (hST : edgewiseLeftSupport n S = edgewiseLeftSupport n T) :
    edgewiseSupportPivot S hS = edgewiseSupportPivot T hT

def EdgewiseOutsideSupport (n : ℕ)

def EdgewiseLowerSupport (n : ℕ)

def EdgewiseUpperSupport (n : ℕ)

def edgewiseSupportRaise {n : ℕ} (S : EdgewiseLowerSupport n) : EdgewiseUpperSupport n

def edgewiseSupportLower {n : ℕ} (S : EdgewiseUpperSupport n) : EdgewiseLowerSupport n

lemma edgewiseSupportRaise_pivot {n : ℕ} (S : EdgewiseLowerSupport n) :
    edgewiseSupportPivot (edgewiseSupportRaise S).val.val (edgewiseSupportRaise S).val.property =
      edgewiseSupportPivot S.val.val S.val.property

lemma edgewiseSupportLower_pivot {n : ℕ} (S : EdgewiseUpperSupport n) :
    edgewiseSupportPivot (edgewiseSupportLower S).val.val (edgewiseSupportLower S).val.property =
      edgewiseSupportPivot S.val.val S.val.property

def edgewiseSupportPairEquiv (n : ℕ) : EdgewiseLowerSupport n ≃ EdgewiseUpperSupport n

lemma edgewiseWeightIso_inl (n : ℕ) :
    joinInl (Δ[n] : SSet.{u}).op Δ[n] ≫ (edgewiseWeightIso n).hom =
      (stdSimplex.opIso ⦋n⦌).hom ≫ stdSimplex.map
        (SimplexCategory.mkHom (DGNerve.joinLeftOrderHom n n))

lemma edgewiseWeightIso_inr (n : ℕ) :
    joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ (edgewiseWeightIso n).hom =
      stdSimplex.map (SimplexCategory.mkHom (DGNerve.joinRightOrderHom n n))

def edgewiseRightVerticesOrderIso (n : ℕ) : Fin (n + 1) ≃o edgewiseRightVertices n

lemma edgewiseWeightIso_inr_range (n : ℕ) :
    Subcomplex.range (joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ (edgewiseWeightIso n).hom) =
      stdSimplex.face (edgewiseRightVertices n)

noncomputable def stdSimplexNondegenerateSupport {n : ℕ} (s : (Δ[n] : SSet.{u}).N) :
    Finset (Fin (n + 1))

lemma stdSimplexNondegenerateSupport_card {n : ℕ} (s : (Δ[n] : SSet.{u}).N) :
    (stdSimplexNondegenerateSupport s).card = s.dim + 1

lemma stdSimplexNondegenerateSupport_nonempty {n : ℕ} (s : (Δ[n] : SSet.{u}).N) :
    (stdSimplexNondegenerateSupport s).Nonempty

lemma stdSimplexNondegenerateSupport_injective (n : ℕ) :
    Function.Injective (stdSimplexNondegenerateSupport.{u} (n := n))

noncomputable def stdSimplexNondegenerateSupportEquiv (n : ℕ) :
    (Δ[n] : SSet.{u}).N ≃ {S : Finset (Fin (n + 1)) // S.Nonempty}

lemma stdSimplexNondegenerateSupport_subset_iff {n : ℕ} (s t : (Δ[n] : SSet.{u}).N) :
    stdSimplexNondegenerateSupport s ⊆ stdSimplexNondegenerateSupport t ↔ s ≤ t

lemma stdSimplexNondegenerateSupport_eq_image {n : ℕ} (s : (Δ[n] : SSet.{u}).N) :
    stdSimplexNondegenerateSupport s = Finset.univ.image s.simplex

lemma edgewiseNondegenerate_mem_iff_support {n : ℕ}
    (s : (Δ[n + n + 1] : SSet.{u}).N) :
    s.simplex ∈ (edgewiseRightExtensionDomain n).obj (Opposite.op ⦋s.dim⦌) ↔
      EdgewiseSupportInDomain n (stdSimplexNondegenerateSupport s)

noncomputable def edgewiseOutsideSimplexSupport {n : ℕ}
    (s : (edgewiseRightExtensionDomain.{u} n).N) : EdgewiseOutsideSupport n

lemma edgewiseOutsideSimplexSupport_bijective (n : ℕ) :
    Function.Bijective (edgewiseOutsideSimplexSupport.{u} (n := n))

noncomputable def edgewiseOutsideSimplexEquiv (n : ℕ) :
    (edgewiseRightExtensionDomain.{u} n).N ≃ EdgewiseOutsideSupport n

lemma edgewiseOutsideSimplexEquiv_symm_support (n : ℕ) (S : EdgewiseOutsideSupport n) :
    stdSimplexNondegenerateSupport ((edgewiseOutsideSimplexEquiv.{u} n).symm S).toN = S.val

noncomputable def edgewiseUpperSimplices (n : ℕ) : Set (edgewiseRightExtensionDomain.{u} n).N

noncomputable def edgewiseLowerSimplices (n : ℕ) : Set (edgewiseRightExtensionDomain.{u} n).N

noncomputable def edgewiseUpperSimplexEquiv (n : ℕ) :
    {s // s ∈ edgewiseUpperSimplices.{u} n} ≃ EdgewiseUpperSupport n

noncomputable def edgewiseLowerSimplexEquiv (n : ℕ) :
    {s // s ∈ edgewiseLowerSimplices.{u} n} ≃ EdgewiseLowerSupport n

noncomputable def edgewiseExtensionPairing (n : ℕ) : (edgewiseRightExtensionDomain.{u} n).Pairing

lemma edgewiseExtensionPairing_support (n : ℕ) (s : (edgewiseExtensionPairing.{u} n).II) :
    stdSimplexNondegenerateSupport ((edgewiseExtensionPairing n).p s).val.toN =
      insert (edgewiseRightVertex n (edgewiseSupportPivot
        (stdSimplexNondegenerateSupport s.val.toN)
        (edgewiseOutsideSimplexEquiv n s.val).property))
        (stdSimplexNondegenerateSupport s.val.toN)

lemma uniquelyCodimOneFace_of_nonsingular_le {X : SSet.{u}} [X.Nonsingular]
    (x y : X.N) (hxy : x ≤ y) (hd : y.dim = x.dim + 1) :
    x.toS.IsUniquelyCodimOneFace y.toS

lemma edgewiseExtensionPairing_le (n : ℕ) (s : (edgewiseExtensionPairing.{u} n).II) :
    s.val ≤ ((edgewiseExtensionPairing n).p s).val

lemma edgewiseExtensionPairing_dim (n : ℕ) (s : (edgewiseExtensionPairing.{u} n).II) :
    ((edgewiseExtensionPairing n).p s).val.dim = s.val.dim + 1

instance edgewiseExtensionPairing_isProper (n : ℕ) : (edgewiseExtensionPairing.{u} n).IsProper

lemma edgewiseExtensionPairing_ancestral_rank_lt (n : ℕ)
    (s t : (edgewiseExtensionPairing.{u} n).II)
    (hst : (edgewiseExtensionPairing n).AncestralRel s t) :
    Prod.Lex (· < ·) (· < ·)
      (n - (edgewiseSupportPivot (stdSimplexNondegenerateSupport s.val.toN)
        (edgewiseOutsideSimplexEquiv n s.val).property).val,
        (stdSimplexNondegenerateSupport s.val.toN).card)
      (n - (edgewiseSupportPivot (stdSimplexNondegenerateSupport t.val.toN)
        (edgewiseOutsideSimplexEquiv n t.val).property).val,
        (stdSimplexNondegenerateSupport t.val.toN).card)

instance edgewiseExtensionPairing_isRegular (n : ℕ) : (edgewiseExtensionPairing.{u} n).IsRegular

lemma regularPairing_hasLiftingProperty {X E B : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] (p : E ⟶ B)
    (h : ∀ (n : ℕ) (i : Fin (n + 2)), HasLiftingProperty (horn (n + 1) i).ι p) :
    HasLiftingProperty A.ι p

lemma exists_extension_of_regularPairing {X K : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] [KanComplex K] (f : (A : SSet.{u}) ⟶ K) :
    ∃ F : X ⟶ K, A.ι ≫ F = f

lemma exists_edgewiseRightExtensionDomain_extension {K : SSet.{u}} [KanComplex K] (n : ℕ)
    (f : (edgewiseRightExtensionDomain n : SSet.{u}) ⟶ K) :
    ∃ F : (Δ[n + n + 1] : SSet.{u}) ⟶ K, (edgewiseRightExtensionDomain n).ι ≫ F = f

def edgewiseRightWeightDomain (n : ℕ) : (edgewiseWeight.{u}.obj ⦋n⦌).Subcomplex

lemma exists_edgewiseRightWeightDomain_extension {K : SSet.{u}} [KanComplex K] (n : ℕ)
    (f : (edgewiseRightWeightDomain n : SSet.{u}) ⟶ K) :
    ∃ F : edgewiseWeight.obj ⦋n⦌ ⟶ K, (edgewiseRightWeightDomain n).ι ≫ F = f

lemma Join.augMem_range_iff {X Y : SSet.{u}} (f : X ⟶ Y) (r : ℕ) (a : Join.augObj Y r) :
    Join.augMem (Subcomplex.range f) r a ↔ ∃ b : Join.augObj X r, Join.augHom f r b = a

lemma joinMap_range {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    Subcomplex.range (joinMap f g) =
      joinSubcomplexLeft (Subcomplex.range f) Y' ⊓ joinSubcomplexRight X' (Subcomplex.range g)

lemma subcomplex_range_opFunctor_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    Subcomplex.range (SSet.opFunctor.map f) = (Subcomplex.range f).op

lemma edgewiseWeight_face_range (n : ℕ) (i : Fin (n + 2)) :
    Subcomplex.range (edgewiseWeight.{u}.map (SimplexCategory.δ i)) =
      joinSubcomplexLeft (stdSimplex.face ({i}ᶜ)).op Δ[n + 1] ⊓
        joinSubcomplexRight (Δ[n + 1] : SSet.{u}).op (stdSimplex.face ({i}ᶜ))

instance edgewiseWeight_face_mono (n : ℕ) (i : Fin (n + 2)) :
    Mono (edgewiseWeight.{u}.map (SimplexCategory.δ i))

lemma edgewiseWeight_face_range_inf (n : ℕ) (i j : Fin (n + 2)) :
    Subcomplex.range (edgewiseWeight.{u}.map (SimplexCategory.δ i)) ⊓
      Subcomplex.range (edgewiseWeight.map (SimplexCategory.δ j)) =
    joinSubcomplexLeft ((stdSimplex.face ({i}ᶜ) ⊓ stdSimplex.face ({j}ᶜ)).op) Δ[n + 1] ⊓
      joinSubcomplexRight (Δ[n + 1] : SSet.{u}).op
        (stdSimplex.face ({i}ᶜ) ⊓ stdSimplex.face ({j}ᶜ))

lemma stdSimplex_faces_isPullback {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j) :
    IsPullback (stdSimplex.{u}.δ j) (stdSimplex.δ i)
      (stdSimplex.δ i.castSucc) (stdSimplex.δ j.succ)

lemma edgewiseWeight_faces_isPullback {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j) :
    IsPullback (edgewiseWeight.{u}.map (SimplexCategory.δ j))
      (edgewiseWeight.map (SimplexCategory.δ i))
      (edgewiseWeight.map (SimplexCategory.δ i.castSucc))
      (edgewiseWeight.map (SimplexCategory.δ j.succ))

lemma boundary_faces_overlap {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j) :
    (stdSimplex.{u}.δ j) ≫ boundary.ι i.castSucc =
      stdSimplex.δ i ≫ boundary.ι j.succ

lemma edgewiseBoundaryFace_overlap {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ edgewiseSubdivision K)
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    edgewiseWeight.map (SimplexCategory.δ j) ≫ SSet.yonedaEquiv (boundary.ι i.castSucc ≫ a) =
      edgewiseWeight.map (SimplexCategory.δ i) ≫ SSet.yonedaEquiv (boundary.ι j.succ ≫ a)

lemma edgewiseBoundaryFace_eq_of_same_image {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ edgewiseSubdivision K)
    (i j : Fin (n + 2)) (hij : i ≤ j) (d : SimplexCategoryᵒᵖ)
    (x y : (edgewiseWeight.obj ⦋n + 1⦌).obj d)
    (hxy : (edgewiseWeight.map (SimplexCategory.δ i.castSucc)).app d x =
      (edgewiseWeight.map (SimplexCategory.δ j.succ)).app d y) :
    (SSet.yonedaEquiv (boundary.ι i.castSucc ≫ a)).app d x =
      (SSet.yonedaEquiv (boundary.ι j.succ ≫ a)).app d y

lemma edgewiseBoundaryFace_eq_of_lt {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ edgewiseSubdivision K)
    (i j : Fin (n + 3)) (hij : i < j) (d : SimplexCategoryᵒᵖ)
    (x y : (edgewiseWeight.obj ⦋n + 1⦌).obj d)
    (hxy : (edgewiseWeight.map (SimplexCategory.δ i)).app d x =
      (edgewiseWeight.map (SimplexCategory.δ j)).app d y) :
    (SSet.yonedaEquiv (boundary.ι i ≫ a)).app d x =
      (SSet.yonedaEquiv (boundary.ι j ≫ a)).app d y

lemma edgewiseBoundaryFaces_compatible {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ edgewiseSubdivision K)
    (i j : Fin (n + 3)) (d : SimplexCategoryᵒᵖ)
    (x y : (edgewiseWeight.obj ⦋n + 1⦌).obj d)
    (hxy : (edgewiseWeight.map (SimplexCategory.δ i)).app d x =
      (edgewiseWeight.map (SimplexCategory.δ j)).app d y) :
    (SSet.yonedaEquiv (boundary.ι i ≫ a)).app d x =
      (SSet.yonedaEquiv (boundary.ι j ≫ a)).app d y

lemma exists_map_of_compatible_range_cover {I : Type v} {Y K : SSet.{u}}
    (X : I → SSet.{u}) (ι : ∀ i, X i ⟶ Y) (f : ∀ i, X i ⟶ K)
    (hc : ∀ (i j : I) (d : SimplexCategoryᵒᵖ) (x : (X i).obj d) (y : (X j).obj d),
      (ι i).app d x = (ι j).app d y → (f i).app d x = (f j).app d y) :
    ∃ F : ((⨆ i, Subcomplex.range (ι i) : Y.Subcomplex) : SSet.{u}) ⟶ K,
      ∀ i, Subcomplex.lift (ι i) (le_iSup (fun j ↦ Subcomplex.range (ι j)) i) ≫ F = f i

lemma edgewiseRight_yoneda {K : SSet.{u}} {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ edgewiseSubdivision K) :
    joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ SSet.yonedaEquiv f = f ≫ edgewiseRight K

lemma edgewiseBoundaryFace_right_restriction {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ edgewiseSubdivision K)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ K)
    (sq : CommSq a (boundary (n + 1)).ι (edgewiseRight K) b) (i : Fin (n + 2)) :
    joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ SSet.yonedaEquiv (boundary.ι i ≫ a) =
      stdSimplex.δ i ≫ b

lemma edgewiseBoundaryFace_right_compatible {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ edgewiseSubdivision K)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ K)
    (sq : CommSq a (boundary (n + 1)).ι (edgewiseRight K) b)
    (i : Fin (n + 2)) (d : SimplexCategoryᵒᵖ)
    (x : (edgewiseWeight.obj ⦋n⦌).obj d) (y : (Δ[n + 1] : SSet.{u}).obj d)
    (hxy : (edgewiseWeight.map (SimplexCategory.δ i)).app d x =
      (joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]).app d y) :
    (SSet.yonedaEquiv (boundary.ι i ≫ a)).app d x = b.app d y

def edgewiseBoundaryCoverSource (n : ℕ) : Option (Fin (n + 3)) → SSet.{u}

def edgewiseBoundaryCoverMap (n : ℕ) : ∀ i, edgewiseBoundaryCoverSource.{u} n i ⟶
    edgewiseWeight.obj ⦋n + 2⦌

def edgewiseBoundaryCoverDiagram {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ edgewiseSubdivision K)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ K) : ∀ i, edgewiseBoundaryCoverSource n i ⟶ K

lemma edgewiseBoundaryCover_compatible {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ edgewiseSubdivision K)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ K)
    (sq : CommSq a (boundary (n + 2)).ι (edgewiseRight K) b)
    (i j : Option (Fin (n + 3))) (d : SimplexCategoryᵒᵖ)
    (x : (edgewiseBoundaryCoverSource n i).obj d) (y : (edgewiseBoundaryCoverSource n j).obj d)
    (hxy : (edgewiseBoundaryCoverMap n i).app d x = (edgewiseBoundaryCoverMap n j).app d y) :
    (edgewiseBoundaryCoverDiagram a b i).app d x = (edgewiseBoundaryCoverDiagram a b j).app d y

lemma exists_edgewiseBoundaryCover_gluing {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 2) : SSet.{u}) ⟶ edgewiseSubdivision K)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ K)
    (sq : CommSq a (boundary (n + 2)).ι (edgewiseRight K) b) :
    ∃ F : ((⨆ i, Subcomplex.range (edgewiseBoundaryCoverMap n i) :
      (edgewiseWeight.obj ⦋n + 2⦌).Subcomplex) : SSet.{u}) ⟶ K,
      ∀ i, Subcomplex.lift (edgewiseBoundaryCoverMap n i)
        (le_iSup (fun j ↦ Subcomplex.range (edgewiseBoundaryCoverMap n j)) i) ≫ F =
          edgewiseBoundaryCoverDiagram a b i

lemma Join.mem_range_cast_iff {p q r : ℕ} (h : p = q) (f : Fin r → Fin p) (v : Fin p) :
    Fin.cast h v ∈ Set.range (fun j ↦ Fin.cast h (f j)) ↔ v ∈ Set.range f

lemma joinStdSimplexIso_mem_range_left {p q d : ℕ}
    (s : Join.Simplex (Δ[p] : SSet.{u}) Δ[q] d) (v : Fin (p + 1)) :
    Fin.cast (by omega : (p + 1) + (q + 1) = p + q + 1 + 1) (v.castAdd (q + 1)) ∈
      Set.range ((joinStdSimplexIso p q).hom.app (Opposite.op ⦋d⦌) s) ↔
      v ∈ Set.range (Join.stdAugEquiv p s.1.val s.2.1)

lemma joinStdSimplexIso_mem_range_right {p q d : ℕ}
    (s : Join.Simplex (Δ[p] : SSet.{u}) Δ[q] d) (v : Fin (q + 1)) :
    Fin.cast (by omega : (p + 1) + (q + 1) = p + q + 1 + 1) (v.natAdd (p + 1)) ∈
      Set.range ((joinStdSimplexIso p q).hom.app (Opposite.op ⦋d⦌) s) ↔
      v ∈ Set.range (Join.stdAugEquiv q (d + 1 - s.1.val) s.2.2)

lemma Join.augMem_face_compl_iff {p : ℕ} (i : Fin (p + 1)) (r : ℕ)
    (a : Join.augObj (Δ[p] : SSet.{u}) r) :
    Join.augMem (stdSimplex.face ({i}ᶜ)) r a ↔ i ∉ Set.range (Join.stdAugEquiv p r a)

lemma Join.augMem_op_face_compl_iff {p : ℕ} (i : Fin (p + 1)) (r : ℕ)
    (a : Join.augObj (Δ[p] : SSet.{u}).op r) :
    Join.augMem (stdSimplex.face ({i}ᶜ)).op r a ↔
      i.rev ∉ Set.range (Join.stdAugEquiv p r (Join.augHom (stdSimplex.opIso ⦋p⦌).hom r a))

lemma edgewiseWeightIso_missing_left {n d : ℕ}
    (s : (edgewiseWeight.{u}.obj ⦋n⦌).obj (Opposite.op ⦋d⦌)) (i : Fin (n + 1)) :
    edgewiseLeftVertex n i ∉ Set.range ((edgewiseWeightIso n).hom.app (Opposite.op ⦋d⦌) s) ↔
      Join.augMem (stdSimplex.face ({i}ᶜ)).op s.1.val s.2.1

lemma edgewiseWeightIso_missing_right {n d : ℕ}
    (s : (edgewiseWeight.{u}.obj ⦋n⦌).obj (Opposite.op ⦋d⦌)) (i : Fin (n + 1)) :
    edgewiseRightVertex n i ∉ Set.range ((edgewiseWeightIso n).hom.app (Opposite.op ⦋d⦌) s) ↔
      Join.augMem (stdSimplex.face ({i}ᶜ)) (d + 1 - s.1.val) s.2.2

lemma edgewiseWeightIso_pair_face_preimage (n : ℕ) (i : Fin (n + 2)) :
    (stdSimplex.face ({edgewiseLeftVertex (n + 1) i, edgewiseRightVertex (n + 1) i}ᶜ)).preimage
      (edgewiseWeightIso.{u} (n + 1)).hom =
    Subcomplex.range (edgewiseWeight.map (SimplexCategory.δ i))

lemma edgewiseWeightIso_right_face_preimage (n : ℕ) :
    (stdSimplex.face (edgewiseRightVertices n)).preimage (edgewiseWeightIso.{u} n).hom =
      Subcomplex.range (joinInr (Δ[n] : SSet.{u}).op Δ[n])

lemma edgewiseRightWeightDomain_eq_face_cover (n : ℕ) :
    edgewiseRightWeightDomain.{u} (n + 1) =
      Subcomplex.range (joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]) ⊔
        ⨆ i : Fin (n + 2), Subcomplex.range (edgewiseWeight.map (SimplexCategory.δ i))

lemma edgewiseRightWeightDomain_eq_boundary_cover (n : ℕ) :
    edgewiseRightWeightDomain.{u} (n + 2) =
      ⨆ i, Subcomplex.range (edgewiseBoundaryCoverMap.{u} n i)

lemma edgewiseWeight_one_faces_inf :
    Subcomplex.range (edgewiseWeight.{u}.map (SimplexCategory.δ (0 : Fin 2))) ⊓
      Subcomplex.range (edgewiseWeight.map (SimplexCategory.δ (1 : Fin 2))) = ⊥

lemma edgewiseBoundaryOneFaces_compatible {K : SSet.{u}}
    (a : (boundary 1 : SSet.{u}) ⟶ edgewiseSubdivision K)
    (i j : Fin 2) (d : SimplexCategoryᵒᵖ)
    (x y : (edgewiseWeight.obj ⦋0⦌).obj d)
    (hxy : (edgewiseWeight.map (SimplexCategory.δ i)).app d x =
      (edgewiseWeight.map (SimplexCategory.δ j)).app d y) :
    (SSet.yonedaEquiv (boundary.ι i ≫ a)).app d x =
      (SSet.yonedaEquiv (boundary.ι j ≫ a)).app d y

lemma edgewiseBoundaryFaces_compatible_all {K : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ edgewiseSubdivision K)
    (i j : Fin (n + 2)) (d : SimplexCategoryᵒᵖ)
    (x y : (edgewiseWeight.obj ⦋n⦌).obj d)
    (hxy : (edgewiseWeight.map (SimplexCategory.δ i)).app d x =
      (edgewiseWeight.map (SimplexCategory.δ j)).app d y) :
    (SSet.yonedaEquiv (boundary.ι i ≫ a)).app d x =
      (SSet.yonedaEquiv (boundary.ι j ≫ a)).app d y

lemma exists_edgewiseRight_weight_extension {K : SSet.{u}} [KanComplex K] {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ edgewiseSubdivision K)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ K)
    (sq : CommSq a (boundary (n + 1)).ι (edgewiseRight K) b) :
    ∃ F : edgewiseWeight.obj ⦋n + 1⦌ ⟶ K,
      (∀ i : Fin (n + 2), edgewiseWeight.map (SimplexCategory.δ i) ≫ F =
        SSet.yonedaEquiv (boundary.ι i ≫ a)) ∧
      joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1] ≫ F = b

instance edgewiseRight_trivialKanFibration (K : SSet.{u}) [KanComplex K] :
    TrivialKanFibration (edgewiseRight K)

instance edgewiseSubdivision_kanComplex (K : SSet.{u}) [KanComplex K] :
    KanComplex (edgewiseSubdivision K)

noncomputable def joinSelfOppositeIso (A : SSet.{u}) : (join A.op A).op ≅ join A.op A

lemma joinSelfOpposite_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    SSet.opFunctor.map (joinMap (SSet.opFunctor.map f) f) ≫ (joinSelfOppositeIso B).hom =
      (joinSelfOppositeIso A).hom ≫ joinMap (SSet.opFunctor.map f) f

lemma joinSelfOpposite_inv_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    joinMap (SSet.opFunctor.map f) f ≫ (joinSelfOppositeIso B).inv =
      (joinSelfOppositeIso A).inv ≫ SSet.opFunctor.map (joinMap (SSet.opFunctor.map f) f)

lemma joinSelfOpposite_inv_inr (A : SSet.{u}) :
    joinInr A.op A ≫ (joinSelfOppositeIso A).inv =
      (SSet.opFunctorCompOpFunctorIso.app A).inv ≫ SSet.opFunctor.map (joinInl A.op A)

noncomputable def edgewiseWeightReverseIso (n : SimplexCategory) :
    (edgewiseWeight.{u}.obj n).op ≅ edgewiseWeight.obj n

lemma edgewiseWeightReverse_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    SSet.opFunctor.map (edgewiseWeight.{u}.map α) ≫ (edgewiseWeightReverseIso n).hom =
      (edgewiseWeightReverseIso m).hom ≫ edgewiseWeight.map α

lemma edgewiseWeightReverse_inv_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    edgewiseWeight.{u}.map α ≫ (edgewiseWeightReverseIso n).inv =
      (edgewiseWeightReverseIso m).inv ≫ SSet.opFunctor.map (edgewiseWeight.map α)

lemma edgewiseWeightReverse_inv_inr (n : SimplexCategory) :
    joinInr (stdSimplex.obj n).op (stdSimplex.obj n) ≫ (edgewiseWeightReverseIso.{u} n).inv =
      (SSet.opFunctorCompOpFunctorIso.app (stdSimplex.obj n)).inv ≫
        SSet.opFunctor.map (joinInl (stdSimplex.obj n).op (stdSimplex.obj n))

noncomputable def edgewiseDuality (X : SSet.{u}) : edgewiseSubdivision X ⟶ edgewiseSubdivision X.op

instance edgewiseDuality_isIso (X : SSet.{u}) : IsIso (edgewiseDuality X)

noncomputable def edgewiseDualityIso (X : SSet.{u}) : edgewiseSubdivision X ≅ edgewiseSubdivision X.op

lemma edgewiseDuality_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    edgewiseSubdivisionMap f ≫ edgewiseDuality Y =
      edgewiseDuality X ≫ edgewiseSubdivisionMap (SSet.opFunctor.map f)

lemma oppositeSimplex_yoneda {K : SSet.{u}} (n : SimplexCategory)
    (g : (stdSimplex.obj n).op ⟶ K) :
    SSet.yonedaEquiv ((SSet.opFunctorCompOpFunctorIso.app (stdSimplex.obj n)).inv ≫
      SSet.opFunctor.map g) =
      SSet.opObjEquiv.symm (SSet.yonedaEquiv ((stdSimplex.opIso n).inv ≫ g))

lemma edgewiseDuality_right (X : SSet.{u}) :
    edgewiseDuality X ≫ edgewiseRight X.op = edgewiseLeft X

instance edgewiseLeft_trivialKanFibration (X : SSet.{u}) [KanComplex X] :
    TrivialKanFibration (edgewiseLeft X)

def kanEdgewiseFunctor : KanObject.{u} ⥤ KanObject.{u}

def kanEdgewiseRight : kanEdgewiseFunctor.{u} ⟶ 𝟭 KanObject.{u}

def kanEdgewiseLeft : kanEdgewiseFunctor.{u} ⟶ kanObjectOpFunctor

lemma kanEdgewiseRight_trivialKanFibration (K : KanObject.{u}) :
    TrivialKanFibration (kanEdgewiseRight.app K)

lemma kanEdgewiseLeft_trivialKanFibration (K : KanObject.{u}) :
    TrivialKanFibration (kanEdgewiseLeft.app K)

lemma weightedNerveMap_fiber_naturality {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) (c : C) :
    weightedNerveFiberMap F c ≫ vertexFiberMap (weightedNerveProjection F)
      (weightedNerveProjection G) (weightedNerveMap η) (weightedNerveMap_projection η) (nerveVertex c) =
      η.app c ≫ weightedNerveFiberMap G c

lemma weightedNerveMap_isPrecompositionEquivalence {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) (h : ∀ c, IsQCatEquivalence (η.app c)) :
    IsPrecompositionEquivalence (weightedNerveMap η)

def weightedKanEdgewiseRight {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    weightedNerve (F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget) ⟶ weightedNerve (F ⋙ kanObjectForget)

def weightedKanEdgewiseLeft {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    weightedNerve (F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget) ⟶
      weightedNerve (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget)

lemma weightedKanEdgewiseRight_projection {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    weightedKanEdgewiseRight F ≫ weightedNerveProjection (F ⋙ kanObjectForget) =
      weightedNerveProjection (F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget)

lemma weightedKanEdgewiseLeft_projection {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    weightedKanEdgewiseLeft F ≫ weightedNerveProjection (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) =
      weightedNerveProjection (F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget)

lemma weightedKanEdgewiseRight_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    IsPrecompositionEquivalence (weightedKanEdgewiseRight F)

lemma weightedKanEdgewiseLeft_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    IsPrecompositionEquivalence (weightedKanEdgewiseLeft F)

noncomputable def directPointHomDiagramIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (HomotopyLimits.simplicialHomDiagram F pointKanObject ⋙ SSet.opFunctor) ≅
      F ⋙ kanObjectOpFunctor ⋙ kanObjectForget

noncomputable def directPointHomWeightedIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    weightedNerve (HomotopyLimits.simplicialHomDiagram
      F pointKanObject ⋙ SSet.opFunctor) ≅
      weightedNerve (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget)

lemma directPointHomWeightedIso_inv_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (directPointHomWeightedIso F).inv ≫
      weightedNerveProjection (HomotopyLimits.simplicialHomDiagram
        F pointKanObject ⋙ SSet.opFunctor) =
      weightedNerveProjection (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget)

noncomputable def reversedWeightedKanUnstraighteningComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget)) ⟶
      leftUnstraightening (kanDiagramCoherentNerve F)

lemma reversedWeightedKanUnstraighteningComparison_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    reversedWeightedKanUnstraighteningComparison F ≫
      leftUnstraighteningProjection (kanDiagramCoherentNerve F) =
      (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget))

lemma reversedWeightedKanUnstraighteningComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    IsPrecompositionEquivalence (reversedWeightedKanUnstraighteningComparison F)

lemma exists_directKanUnstraighteningComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    ∃ f : (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve (F ⋙ kanObjectForget)) ⟶
        leftUnstraightening (kanDiagramCoherentNerve F),
      f ≫ leftUnstraighteningProjection (kanDiagramCoherentNerve F) =
        (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (F ⋙ kanObjectForget)) ∧
      IsPrecompositionEquivalence f

noncomputable def directKanUnstraighteningComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve (F ⋙ kanObjectForget)) ⟶
      leftUnstraightening (kanDiagramCoherentNerve F)

lemma directKanUnstraighteningComparison_projection
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    directKanUnstraighteningComparison F ≫
      leftUnstraighteningProjection (kanDiagramCoherentNerve F) =
      (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (F ⋙ kanObjectForget))

lemma directKanUnstraighteningComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    IsPrecompositionEquivalence (directKanUnstraighteningComparison F)

lemma exists_leftStraighteningCandidateComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    ∃ f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶
        leftUnstraightening (leftStraighteningCandidate p),
      f ≫ leftUnstraighteningProjection (leftStraighteningCandidate p) =
        (SSet.uliftFunctor.{u + 1, u}).map p ∧ IsPrecompositionEquivalence f

noncomputable def leftStraighteningCandidateComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening (leftStraighteningCandidate p)

lemma leftStraighteningCandidateComparison_projection
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    leftStraighteningCandidateComparison p ≫
      leftUnstraighteningProjection (leftStraighteningCandidate p) =
      (SSet.uliftFunctor.{u + 1, u}).map p

lemma leftStraighteningCandidateComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    IsPrecompositionEquivalence (leftStraighteningCandidateComparison p)

lemma leftStraighteningCandidateComparison_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ nerve C) [LeftFibration p] :
    IsQCatEquivalence (leftStraighteningCandidateComparison p)

noncomputable def leftUnstraighteningTransformationSource
    {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) :
    leftUnstraightening F ⟶ relativeEdgeSourceTarget pointedSpaceProjection

noncomputable def leftUnstraighteningTransformationChoiceSpace
    {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) : SSet.{u + 1}

lemma leftUnstraighteningTransformationChoiceSpace_isContractibleKan
    {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) :
    IsContractibleKan (leftUnstraighteningTransformationChoiceSpace F H h₀)

lemma exists_leftUnstraighteningTransformation
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G) :
    ∃ (f : leftUnstraightening F ⟶ leftUnstraightening G)
      (W : (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u}),
      f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F ∧
      prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F ∧
      prismEndpoint 1 _ ≫ W = f ≫ pullback.fst pointedSpaceProjection G ∧
      W ≫ pointedSpaceProjection = (Δ[1] ◁ leftUnstraighteningProjection F) ≫ H

lemma relativeFunctorUncurry_naturality {A T U E B : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (f : U ⟶ relativeFunctorSpace p a) (k : T ⟶ U) :
    relativeFunctorUncurry (k ≫ f) = (A ◁ k) ≫ relativeFunctorUncurry f

noncomputable def relativeFunctorBaseChangeForward {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D) :
    relativeFunctorSpace (pullback.snd p f) a ⟶ relativeFunctorSpace p (a ≫ f)

noncomputable def relativeFunctorBaseChangeBackward {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D) :
    relativeFunctorSpace p (a ≫ f) ⟶ relativeFunctorSpace (pullback.snd p f) a

lemma relativeFunctorBaseChangeForward_uncurry {A E B D T : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D)
    (k : T ⟶ relativeFunctorSpace (pullback.snd p f) a) :
    relativeFunctorUncurry (k ≫ relativeFunctorBaseChangeForward p f a) =
      relativeFunctorUncurry k ≫ pullback.fst p f

lemma relativeFunctorBaseChangeBackward_uncurry {A E B D T : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D)
    (k : T ⟶ relativeFunctorSpace p (a ≫ f)) :
    relativeFunctorUncurry (k ≫ relativeFunctorBaseChangeBackward p f a) =
      pullback.lift (relativeFunctorUncurry k) (fst A T ≫ a) (by
        rw [relativeFunctorUncurry_projection, Category.assoc])

noncomputable def relativeFunctorBaseChangeIso {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D) :
    relativeFunctorSpace (pullback.snd p f) a ≅ relativeFunctorSpace p (a ≫ f)

lemma relativeEdgeEndpoint_comp {X B : SSet.{u}} (p : X ⟶ B) :
    evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫ p =
      relativeEdgeSource p ≫ pullback.snd p
        (evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
          evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

noncomputable def relativeEdgeLiftSpaceEndpoint {A X B : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p) :
    relativeEdgeLiftSpace p c ⟶ relativeFunctorSpace p
      (c ≫ pullback.snd p
        (evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
          evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))

lemma leftUnstraighteningTransformationSource_endpoint
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G) :
    leftUnstraighteningTransformationSource F H h₀ ≫
      pullback.snd pointedSpaceProjection
        (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
          evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      leftUnstraighteningProjection F ≫ G

noncomputable def leftUnstraighteningTransformationEndpoint
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G) :
    leftUnstraighteningTransformationChoiceSpace F H h₀ ⟶
      relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)

noncomputable def leftUnstraighteningTransformationEndpointIso
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G)
    (x y : (leftUnstraighteningTransformationChoiceSpace F H h₀) _⦋0⦌) :
    VertexIso ((leftUnstraighteningTransformationEndpoint F G H h₀ h₁).app _ x)
      ((leftUnstraighteningTransformationEndpoint F G H h₀ h₁).app _ y)

noncomputable def leftUnstraighteningTransformationChoice
    {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) :
    (leftUnstraighteningTransformationChoiceSpace F H h₀) _⦋0⦌

noncomputable def leftUnstraighteningTransformationMap
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G) :
    {f : leftUnstraightening F ⟶ leftUnstraightening G //
      f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F}

lemma leftUnstraighteningTransformationMap_vertex
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G) :
    relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
      (leftUnstraighteningTransformationMap F G H h₀ h₁).val
      (leftUnstraighteningTransformationMap F G H h₀ h₁).property =
    (leftUnstraighteningTransformationEndpoint F G H h₀ h₁).app _
      (leftUnstraighteningTransformationChoice F H h₀)

noncomputable def leftUnstraighteningTransformationMapChoiceIso
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G)
    (x : (leftUnstraighteningTransformationChoiceSpace F H h₀) _⦋0⦌) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection G)
      (leftUnstraighteningProjection F) (leftUnstraighteningTransformationMap F G H h₀ h₁).val
        (leftUnstraighteningTransformationMap F G H h₀ h₁).property)
      ((leftUnstraighteningTransformationEndpoint F G H h₀ h₁).app _ x)

lemma relativeFunctorVertex_transport {A E B : SSet.{u}} (p : E ⟶ B)
    {a b : A ⟶ B} (h : a = b) (f : A ⟶ E) (hf : f ≫ p = a) :
    (eqToHom (congrArg (relativeFunctorSpace p) h)).app _ (relativeFunctorVertex p a f hf) =
      relativeFunctorVertex p b f (hf.trans h)

lemma relativeFunctorBaseChangeForward_vertex {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D)
    (g : A ⟶ pullback p f) (hg : g ≫ pullback.snd p f = a) :
    (relativeFunctorBaseChangeForward p f a).app _
      (relativeFunctorVertex (pullback.snd p f) a g hg) =
    relativeFunctorVertex p (a ≫ f) (g ≫ pullback.fst p f) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hg])

lemma relativeFunctorBaseChangeBackward_vertex {A E B D : SSet.{u}}
    (p : E ⟶ B) (f : D ⟶ B) (a : A ⟶ D)
    (g : A ⟶ E) (hg : g ≫ p = a ≫ f) :
    (relativeFunctorBaseChangeBackward p f a).app _ (relativeFunctorVertex p (a ≫ f) g hg) =
      relativeFunctorVertex (pullback.snd p f) a (pullback.lift g a hg)
        (pullback.lift_snd _ _ _)

lemma relativeEdgeLiftSpaceEndpoint_vertex {A X B : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p)
    (Q : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (hQ : Q ≫ relativeEdgeSource p = c) :
    (relativeEdgeLiftSpaceEndpoint p c).app _
      (relativeEdgeLiftSpaceVertexEquiv p c ⟨Q, hQ⟩) =
    relativeFunctorVertex p (c ≫ pullback.snd p
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (by
        rw [Category.assoc, relativeEdgeEndpoint_comp, ← Category.assoc, hQ])

lemma relativeEdgeLiftSpaceEndpoint_baseChange_vertex {A X B D : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p)
    (Q : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (hQ : Q ≫ relativeEdgeSource p = c)
    (G : D ⟶ B) (a : A ⟶ D)
    (he : c ≫ pullback.snd p
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = a ≫ G)
    (g : A ⟶ pullback p G) (hg : g ≫ pullback.snd p G = a)
    (hQg : Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      g ≫ pullback.fst p G) :
    (relativeEdgeLiftSpaceEndpoint p c ≫ eqToHom (congrArg (relativeFunctorSpace p) he) ≫
      (relativeFunctorBaseChangeIso p G a).inv).app _
        (relativeEdgeLiftSpaceVertexEquiv p c ⟨Q, hQ⟩) =
      relativeFunctorVertex (pullback.snd p G) a g hg

noncomputable def leftUnstraighteningTransformationWitness
    {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F)
    (W : (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u})
    (hW₀ : prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F)
    (hWp : W ≫ pointedSpaceProjection = (Δ[1] ◁ leftUnstraighteningProjection F) ≫ H) :
    (leftUnstraighteningTransformationChoiceSpace F H h₀) _⦋0⦌

lemma leftUnstraighteningTransformationWitness_endpoint
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G)
    (W : (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u})
    (hW₀ : prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F)
    (hWp : W ≫ pointedSpaceProjection = (Δ[1] ◁ leftUnstraighteningProjection F) ≫ H)
    (g : leftUnstraightening F ⟶ leftUnstraightening G)
    (hg : g ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (hW₁ : prismEndpoint 1 _ ≫ W = g ≫ pullback.fst pointedSpaceProjection G) :
    (leftUnstraighteningTransformationEndpoint F G H h₀ h₁).app _
      (leftUnstraighteningTransformationWitness F H h₀ W hW₀ hWp) =
      relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
        g hg

def leftUnstraighteningIdentityTransformation {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u}

lemma leftUnstraighteningIdentityTransformation_endpoint {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : Fin 2) :
    prismEndpoint i B ≫ leftUnstraighteningIdentityTransformation F = F

noncomputable def leftUnstraighteningIdentityLift {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u}

lemma leftUnstraighteningIdentityLift_endpoint {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (i : Fin 2) :
    prismEndpoint i _ ≫ leftUnstraighteningIdentityLift F =
      pullback.fst pointedSpaceProjection F

lemma leftUnstraighteningIdentityLift_projection {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningIdentityLift F ≫ pointedSpaceProjection =
      (Δ[1] ◁ leftUnstraighteningProjection F) ≫ leftUnstraighteningIdentityTransformation F

noncomputable def leftUnstraighteningTransformationMap_identityIso
    {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection F)
        (leftUnstraighteningTransformationMap F F (leftUnstraighteningIdentityTransformation F)
          (leftUnstraighteningIdentityTransformation_endpoint F 0)
          (leftUnstraighteningIdentityTransformation_endpoint F 1)).val
        (leftUnstraighteningTransformationMap F F (leftUnstraighteningIdentityTransformation F)
          (leftUnstraighteningIdentityTransformation_endpoint F 0)
          (leftUnstraighteningIdentityTransformation_endpoint F 1)).property)
      (relativeFunctorVertex (leftUnstraighteningProjection F) (leftUnstraighteningProjection F)
        (𝟙 _) (Category.id_comp _))

lemma exists_leftUnstraighteningTransformationWitness
    {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F)
    (x : (leftUnstraighteningTransformationChoiceSpace F H h₀) _⦋0⦌) :
    ∃ (W : (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u})
      (hW₀ : prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F)
      (hWp : W ≫ pointedSpaceProjection = (Δ[1] ◁ leftUnstraighteningProjection F) ≫ H),
      leftUnstraighteningTransformationWitness F H h₀ W hW₀ hWp = x

lemma exists_leftUnstraighteningTransformationMap_lift
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G) :
    ∃ W : (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u},
      prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F ∧
      prismEndpoint 1 _ ≫ W = (leftUnstraighteningTransformationMap F G H h₀ h₁).val ≫
        pullback.fst pointedSpaceProjection G ∧
      W ≫ pointedSpaceProjection = (Δ[1] ◁ leftUnstraighteningProjection F) ≫ H

lemma trianglePrism_restrict_baseChange {A B X : SSet.{u}}
    (p : A ⟶ B) (T : (Δ[2] : SSet.{u}) ⊗ B ⟶ X) (i : Fin 3) :
    (stdSimplex.δ i ▷ A) ≫ ((Δ[2] ◁ p) ≫ T) =
      (Δ[1] ◁ p) ≫ ((stdSimplex.δ i ▷ B) ≫ T)

lemma exists_leftUnstraighteningTransformationComposite_lift
    {B : SSet.{u + 1}} (F G J : B ⟶ SpaceInfinity.{u})
    (α β γ : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (hα₀ : prismEndpoint 0 B ≫ α = F) (hα₁ : prismEndpoint 1 B ≫ α = G)
    (hβ₀ : prismEndpoint 0 B ≫ β = G) (hβ₁ : prismEndpoint 1 B ≫ β = J)
    (T : (Δ[2] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (hTα : (stdSimplex.δ (2 : Fin 3) ▷ B) ≫ T = α)
    (hTβ : (stdSimplex.δ (0 : Fin 3) ▷ B) ≫ T = β)
    (hTγ : (stdSimplex.δ (1 : Fin 3) ▷ B) ≫ T = γ) :
    ∃ W : (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u},
      prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F ∧
      prismEndpoint 1 _ ≫ W =
        ((leftUnstraighteningTransformationMap F G α hα₀ hα₁).val ≫
          (leftUnstraighteningTransformationMap G J β hβ₀ hβ₁).val) ≫
            pullback.fst pointedSpaceProjection J ∧
      W ≫ pointedSpaceProjection = (Δ[1] ◁ leftUnstraighteningProjection F) ≫ γ

noncomputable def leftUnstraighteningTransformationMap_witnessIso
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G)
    (W : (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u})
    (hW₀ : prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F)
    (hWp : W ≫ pointedSpaceProjection = (Δ[1] ◁ leftUnstraighteningProjection F) ≫ H)
    (g : leftUnstraightening F ⟶ leftUnstraightening G)
    (hg : g ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (hW₁ : prismEndpoint 1 _ ≫ W = g ≫ pullback.fst pointedSpaceProjection G) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection G)
      (leftUnstraighteningProjection F) (leftUnstraighteningTransformationMap F G H h₀ h₁).val
        (leftUnstraighteningTransformationMap F G H h₀ h₁).property)
      (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
        g hg)

noncomputable def leftUnstraighteningTransformationMap_compositionIso
    {B : SSet.{u + 1}} (F G J : B ⟶ SpaceInfinity.{u})
    (α β γ : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (hα₀ : prismEndpoint 0 B ≫ α = F) (hα₁ : prismEndpoint 1 B ≫ α = G)
    (hβ₀ : prismEndpoint 0 B ≫ β = G) (hβ₁ : prismEndpoint 1 B ≫ β = J)
    (hγ₀ : prismEndpoint 0 B ≫ γ = F) (hγ₁ : prismEndpoint 1 B ≫ γ = J)
    (T : (Δ[2] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (hTα : (stdSimplex.δ (2 : Fin 3) ▷ B) ≫ T = α)
    (hTβ : (stdSimplex.δ (0 : Fin 3) ▷ B) ≫ T = β)
    (hTγ : (stdSimplex.δ (1 : Fin 3) ▷ B) ≫ T = γ) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection J)
      (leftUnstraighteningProjection F) (leftUnstraighteningTransformationMap F J γ hγ₀ hγ₁).val
        (leftUnstraighteningTransformationMap F J γ hγ₀ hγ₁).property)
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        ((leftUnstraighteningTransformationMap F G α hα₀ hα₁).val ≫
          (leftUnstraighteningTransformationMap G J β hβ₀ hβ₁).val) (by
            rw [Category.assoc, (leftUnstraighteningTransformationMap G J β hβ₀ hβ₁).property,
              (leftUnstraighteningTransformationMap F G α hα₀ hα₁).property]))

def functorFamilyPrism {K B X : SSet.{u}} (q : K ⟶ (ihom B).obj X) : K ⊗ B ⟶ X

lemma functorFamilyPrism_restrict {K L B X : SSet.{u}}
    (q : K ⟶ (ihom B).obj X) (i : L ⟶ K) :
    (i ▷ B) ≫ functorFamilyPrism q = functorFamilyPrism (i ≫ q)

def functorEdgePrism {B X : SSet.{u}} {F G : B ⟶ X}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex F) (functorVertex G)) : (Δ[1] : SSet.{u}) ⊗ B ⟶ X

lemma functorEdgePrism_zero {B X : SSet.{u}} {F G : B ⟶ X}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex F) (functorVertex G)) : prismEndpoint 0 B ≫ functorEdgePrism e = F

lemma functorEdgePrism_one {B X : SSet.{u}} {F G : B ⟶ X}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex F) (functorVertex G)) : prismEndpoint 1 B ≫ functorEdgePrism e = G

lemma functorCompStructPrism_two {B X : SSet.{u}} {F G J : B ⟶ X}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex F) (functorVertex G)}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex G) (functorVertex J)}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex F) (functorVertex J)} (σ : SSet.Truncated.Edge.CompStruct e f g) :
    (stdSimplex.δ (2 : Fin 3) ▷ B) ≫ functorFamilyPrism (SSet.yonedaEquiv.symm σ.simplex) =
      functorEdgePrism e

lemma functorCompStructPrism_zero {B X : SSet.{u}} {F G J : B ⟶ X}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex F) (functorVertex G)}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex G) (functorVertex J)}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex F) (functorVertex J)} (σ : SSet.Truncated.Edge.CompStruct e f g) :
    (stdSimplex.δ (0 : Fin 3) ▷ B) ≫ functorFamilyPrism (SSet.yonedaEquiv.symm σ.simplex) =
      functorEdgePrism f

lemma functorCompStructPrism_one {B X : SSet.{u}} {F G J : B ⟶ X}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex F) (functorVertex G)}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex G) (functorVertex J)}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex F) (functorVertex J)} (σ : SSet.Truncated.Edge.CompStruct e f g) :
    (stdSimplex.δ (1 : Fin 3) ▷ B) ≫ functorFamilyPrism (SSet.yonedaEquiv.symm σ.simplex) =
      functorEdgePrism g

lemma functorEdgePrism_id {B X : SSet.{u}} (F : B ⟶ X) :
    functorEdgePrism (F := F) (G := F)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom B).obj X)) (functorVertex F)) = snd (Δ[1] : SSet.{u}) B ≫ F

noncomputable def leftUnstraighteningEdgeMap {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G)) :
    {f : leftUnstraightening F ⟶ leftUnstraightening G //
      f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F}

noncomputable def leftUnstraighteningEdgeMap_identityIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection F)
      (leftUnstraighteningEdgeMap F F (SSet.Edge.id (functorVertex F))).val
      (leftUnstraighteningEdgeMap F F (SSet.Edge.id (functorVertex F))).property)
      (relativeFunctorVertex (leftUnstraighteningProjection F) (leftUnstraighteningProjection F)
        (𝟙 _) (Category.id_comp _))

noncomputable def leftUnstraighteningEdgeMap_compositionIso {B : SSet.{u + 1}}
    {F G J : B ⟶ SpaceInfinity.{u}}
    {e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G)}
    {f : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex G) (functorVertex J)}
    {g : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex J)}
    (σ : SSet.Edge.CompStruct e f g) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection J)
      (leftUnstraighteningProjection F) (leftUnstraighteningEdgeMap F J g).val
        (leftUnstraighteningEdgeMap F J g).property)
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        ((leftUnstraighteningEdgeMap F G e).val ≫ (leftUnstraighteningEdgeMap G J f).val) (by
          rw [Category.assoc, (leftUnstraighteningEdgeMap G J f).property,
            (leftUnstraighteningEdgeMap F G e).property]))

lemma leftUnstraighteningEdgeMap_isQCatEquivalence_of_isInvertibleEdge
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G))
    (he : IsInvertibleEdge e) : IsQCatEquivalence (leftUnstraighteningEdgeMap F G e).val

lemma leftUnstraighteningEdgeMap_isPrecompositionEquivalence_of_isInvertibleEdge
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G))
    (he : IsInvertibleEdge e) : IsPrecompositionEquivalence (leftUnstraighteningEdgeMap F G e).val

lemma exists_leftUnstraighteningComparison_of_functorIso
    {B : SSet.{u + 1}} [Quasicategory B] {F G : B ⟶ SpaceInfinity.{u}}
    (η : FunctorIso F G) :
    ∃ f : leftUnstraightening F ⟶ leftUnstraightening G,
      f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F ∧
      IsPrecompositionEquivalence f

def relativeFunctorExtensionSpace {A D E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b) : SSet.{u}

def relativeFunctorExtensionSpaceι {A D E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b) :
    relativeFunctorExtensionSpace p b i v hv ⟶ relativeFunctorSpace p b

lemma relativeFunctorExtensionSpaceι_pre {A D E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b) :
    relativeFunctorExtensionSpaceι p b i v hv ≫ relativeFunctorPre p b i =
      SSet.const (relativeFunctorVertex p (i ≫ b) v hv)

lemma relativeFunctorExtensionSpace_isContractibleKan {A D E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ b) :
    IsContractibleKan (relativeFunctorExtensionSpace p b i v hv)

noncomputable def relativeFunctorExtensionSpaceVertexEquiv {A D E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b) :
    {W : A ⟶ E // W ≫ p = b ∧ i ≫ W = v} ≃
      (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌

lemma exists_relativeFunctorExtension_of_leftAnodyne {A D E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ b) :
    ∃ W : A ⟶ E, W ≫ p = b ∧ i ≫ W = v

lemma leftAnodyneExtensions_whiskerRight {K L : SSet.{u}}
    (i : K ⟶ L) (hi : leftAnodyneExtensions i) (A : SSet.{u}) :
    leftAnodyneExtensions (i ▷ A)

lemma simplexPrismFirstVertex_leftAnodyne (n : ℕ) (A : SSet.{u}) :
    leftAnodyneExtensions (scaffoldFirstVertex.{u} n ▷ A)

def simplexPrismVertex (n : ℕ) (i : Fin (n + 1)) (A : SSet.{u}) :
    A ⟶ (Δ[n] : SSet.{u}) ⊗ A

lemma simplexPrismVertex_snd (n : ℕ) (i : Fin (n + 1)) (A : SSet.{u}) :
    simplexPrismVertex n i A ≫ snd (Δ[n] : SSet.{u}) A = 𝟙 A

lemma simplexPrismVertex_naturality (n : ℕ) (i : Fin (n + 1))
    {A B : SSet.{u}} (f : A ⟶ B) :
    simplexPrismVertex n i A ≫ (Δ[n] ◁ f) = f ≫ simplexPrismVertex n i B

lemma scaffoldFirstVertex_whiskerRight (n : ℕ) (A : SSet.{u}) :
    (scaffoldFirstVertex.{u} n ▷ A) =
      snd (Δ[0] : SSet.{u}) A ≫ simplexPrismVertex n 0 A

noncomputable def leftUnstraighteningSimplexStart {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    (Δ[0] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u}

lemma leftUnstraighteningSimplexStart_projection {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : simplexPrismVertex n 0 B ≫ T = F) :
    leftUnstraighteningSimplexStart F ≫ pointedSpaceProjection =
      (scaffoldFirstVertex n ▷ leftUnstraightening F) ≫
        ((Δ[n] ◁ leftUnstraighteningProjection F) ≫ T)

noncomputable def leftUnstraighteningSimplexChoiceSpace {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : simplexPrismVertex n 0 B ≫ T = F) : SSet.{u + 1}

lemma leftUnstraighteningSimplexChoiceSpace_isContractibleKan {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : simplexPrismVertex n 0 B ≫ T = F) :
    IsContractibleKan (leftUnstraighteningSimplexChoiceSpace F n T h₀)

lemma exists_leftUnstraighteningSimplexLift {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : simplexPrismVertex n 0 B ≫ T = F) :
    ∃ W : (Δ[n] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u},
      W ≫ pointedSpaceProjection = (Δ[n] ◁ leftUnstraighteningProjection F) ≫ T ∧
      simplexPrismVertex n 0 (leftUnstraightening F) ≫ W = pullback.fst pointedSpaceProjection F

lemma leftUnstraighteningSimplexEndpoint_projection {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u}) (i : Fin (n + 1))
    (hi : simplexPrismVertex n i B ≫ T = G) :
    simplexPrismVertex n i (leftUnstraightening F) ≫
      ((Δ[n] ◁ leftUnstraighteningProjection F) ≫ T) = leftUnstraighteningProjection F ≫ G

noncomputable def leftUnstraighteningSimplexEndpoint {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : simplexPrismVertex n 0 B ≫ T = F) (i : Fin (n + 1))
    (hi : simplexPrismVertex n i B ≫ T = G) :
    leftUnstraighteningSimplexChoiceSpace F n T h₀ ⟶
      relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)

noncomputable def leftUnstraighteningSimplexEndpointIso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : (Δ[n] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : simplexPrismVertex n 0 B ≫ T = F) (i : Fin (n + 1))
    (hi : simplexPrismVertex n i B ≫ T = G)
    (x y : (leftUnstraighteningSimplexChoiceSpace F n T h₀) _⦋0⦌) :
    VertexIso ((leftUnstraighteningSimplexEndpoint F G n T h₀ i hi).app _ x)
      ((leftUnstraighteningSimplexEndpoint F G n T h₀ i hi).app _ y)

lemma leftFibration_lift_relative_parameters {D A K L X Y : SSet.{u}}
    (p : X ⟶ Y) [LeftFibration p] (i : D ⟶ A) (hi : leftAnodyneExtensions i)
    (j : K ⟶ L) [Mono j]
    (u : A ⊗ K ⟶ X) (v : D ⊗ L ⟶ X) (b : A ⊗ L ⟶ Y)
    (hw : (i ▷ K) ≫ u = (D ◁ j) ≫ v)
    (hu : u ≫ p = (A ◁ j) ≫ b) (hv : v ≫ p = (i ▷ L) ≫ b) :
    ∃ W : A ⊗ L ⟶ X,
      (A ◁ j) ≫ W = u ∧ (i ▷ L) ≫ W = v ∧ W ≫ p = b

lemma leftFibration_extend_simplexLift_parameters {A K L X Y : SSet.{u}}
    (p : X ⟶ Y) [LeftFibration p] (n : ℕ) (j : K ⟶ L) [Mono j]
    (u : ((Δ[n] : SSet.{u}) ⊗ A) ⊗ K ⟶ X)
    (v : ((Δ[0] : SSet.{u}) ⊗ A) ⊗ L ⟶ X)
    (b : ((Δ[n] : SSet.{u}) ⊗ A) ⊗ L ⟶ Y)
    (hw : ((scaffoldFirstVertex n ▷ A) ▷ K) ≫ u = ((Δ[0] ⊗ A) ◁ j) ≫ v)
    (hu : u ≫ p = ((Δ[n] ⊗ A) ◁ j) ≫ b)
    (hv : v ≫ p = ((scaffoldFirstVertex n ▷ A) ▷ L) ≫ b) :
    ∃ W : ((Δ[n] : SSet.{u}) ⊗ A) ⊗ L ⟶ X,
      ((Δ[n] ⊗ A) ◁ j) ≫ W = u ∧
      ((scaffoldFirstVertex n ▷ A) ▷ L) ≫ W = v ∧ W ≫ p = b

lemma simplexPrism_parameterizedStart {A B L X : SSet.{u}}
    (p : A ⟶ B) (F : B ⟶ X) (n : ℕ)
    (T : ((Δ[n] : SSet.{u}) ⊗ B) ⊗ L ⟶ X)
    (h₀ : (simplexPrismVertex n 0 B ▷ L) ≫ T = fst B L ≫ F) :
    (((scaffoldFirstVertex n ▷ A) ▷ L) ≫ ((Δ[n] ◁ p) ▷ L)) ≫ T =
      fst (Δ[0] ⊗ A) L ≫ snd (Δ[0] : SSet.{u}) A ≫ p ≫ F

noncomputable def leftUnstraighteningParameterizedSimplexStart {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (L : SSet.{u + 1}) :
    ((Δ[0] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗ L ⟶ PointedSpaceInfinity.{u}

lemma leftUnstraighteningParameterizedSimplexStart_projection {B L : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : ((Δ[n] : SSet.{u + 1}) ⊗ B) ⊗ L ⟶ SpaceInfinity.{u})
    (h₀ : (simplexPrismVertex n 0 B ▷ L) ≫ T = fst B L ≫ F) :
    leftUnstraighteningParameterizedSimplexStart F L ≫ pointedSpaceProjection =
      ((scaffoldFirstVertex n ▷ leftUnstraightening F) ▷ L) ≫
        (((Δ[n] ◁ leftUnstraighteningProjection F) ▷ L) ≫ T)

lemma exists_leftUnstraighteningSimplexLift_relative_parameters
    {B K L : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (j : K ⟶ L) [Mono j]
    (T : ((Δ[n] : SSet.{u + 1}) ⊗ B) ⊗ L ⟶ SpaceInfinity.{u})
    (h₀ : (simplexPrismVertex n 0 B ▷ L) ≫ T = fst B L ≫ F)
    (u : ((Δ[n] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hu₀ : ((scaffoldFirstVertex n ▷ leftUnstraightening F) ▷ K) ≫ u =
      ((Δ[0] ⊗ leftUnstraightening F) ◁ j) ≫ leftUnstraighteningParameterizedSimplexStart F L)
    (hup : u ≫ pointedSpaceProjection = ((Δ[n] ⊗ leftUnstraightening F) ◁ j) ≫
      (((Δ[n] ◁ leftUnstraighteningProjection F) ▷ L) ≫ T)) :
    ∃ W : ((Δ[n] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗ L ⟶ PointedSpaceInfinity.{u},
      ((Δ[n] ⊗ leftUnstraightening F) ◁ j) ≫ W = u ∧
      ((scaffoldFirstVertex n ▷ leftUnstraightening F) ▷ L) ≫ W =
        leftUnstraighteningParameterizedSimplexStart F L ∧
      W ≫ pointedSpaceProjection = ((Δ[n] ◁ leftUnstraighteningProjection F) ▷ L) ≫ T

lemma relativeFunctorPost_id {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    HomotopyLimits.relativeFunctorPost p p (𝟙 E) (Category.id_comp p) a =
      𝟙 (relativeFunctorSpace p a)

lemma relativeFunctorPost_comp {A E F G B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (r : G ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) (g : F ⟶ G) (hg : g ≫ r = q) (a : A ⟶ B) :
    HomotopyLimits.relativeFunctorPost p q f hf a ≫ HomotopyLimits.relativeFunctorPost q r g hg a =
      HomotopyLimits.relativeFunctorPost p r (f ≫ g)
        (by rw [Category.assoc, hg, hf]) a

lemma relativeFunctorPost_vertex {A E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (a : A ⟶ B) (g : A ⟶ E) (hg : g ≫ p = a) :
    (HomotopyLimits.relativeFunctorPost p q f hf a).app _ (relativeFunctorVertex p a g hg) =
      relativeFunctorVertex q a (g ≫ f) (by rw [Category.assoc, hf, hg])

lemma relativeFunctorPostHom_vertex {B : SSet.{u}} (a b c : Over B) (f : b ⟶ c) :
    (relativeFunctorPostHom a b c).app _ (relativeFunctorVertex c.hom b.hom f.left f.w) =
      functorVertex (HomotopyLimits.relativeFunctorPost b.hom c.hom f.left f.w a.hom)

lemma exists_relativeFunctorInverse_of_precompositionEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    ∃ (g : F ⟶ E) (hg : g ≫ p = q),
      Nonempty (VertexIso
        (relativeFunctorVertex p p (f ≫ g) (by rw [Category.assoc, hg, hf]))
        (relativeFunctorVertex p p (𝟙 E) (Category.id_comp p))) ∧
      Nonempty (VertexIso
        (relativeFunctorVertex q q (g ≫ f) (by rw [Category.assoc, hf, hg]))
        (relativeFunctorVertex q q (𝟙 F) (Category.id_comp q)))

noncomputable def relativeFunctorPostIso {B : SSet.{u}} (a b c : Over B) (f g : b ⟶ c)
    (η : VertexIso (relativeFunctorVertex c.hom b.hom f.left f.w)
      (relativeFunctorVertex c.hom b.hom g.left g.w)) :
    FunctorIso (HomotopyLimits.relativeFunctorPost b.hom c.hom f.left f.w a.hom)
      (HomotopyLimits.relativeFunctorPost b.hom c.hom g.left g.w a.hom)

lemma relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    {A E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) (a : A ⟶ B) :
    IsQCatEquivalence (HomotopyLimits.relativeFunctorPost p q f hf a)

lemma relativeFunctorPost_isPrecompositionEquivalence_of_precompositionEquivalence
    {A E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) (a : A ⟶ B) :
    IsPrecompositionEquivalence (HomotopyLimits.relativeFunctorPost p q f hf a)

noncomputable def relativeFunctorEquivalenceOfComparisons
    {B : SSet.{u}} [Quasicategory B] (a b p q : Over B)
    [LeftFibration p.hom] [LeftFibration q.hom]
    (f : a ⟶ b) (g : p ⟶ q)
    (ef : IsPrecompositionEquivalence f.left) (eg : IsPrecompositionEquivalence g.left) :
    QCatEquivalence (relativeFunctorSpace p.hom a.hom) (relativeFunctorSpace q.hom b.hom)

noncomputable def leftStraighteningCandidateRelativeEquivalence
    {C : Type u} [Category.{u} C] {E F : SSet.{u}}
    (p : E ⟶ nerve C) (q : F ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence
      (relativeFunctorSpace ((SSet.uliftFunctor.{u + 1, u}).map q)
        ((SSet.uliftFunctor.{u + 1, u}).map p))
      (relativeFunctorSpace (leftUnstraighteningProjection (leftStraighteningCandidate q))
        (leftUnstraighteningProjection (leftStraighteningCandidate p)))

def uliftFunctorHomUp {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (f : ((ihom A).obj E).obj n) :
    ((ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj ((SSet.uliftFunctor.{v, u}).obj E)).obj n

def uliftFunctorHomDown {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (f : ((ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj
      ((SSet.uliftFunctor.{v, u}).obj E)).obj n) : ((ihom A).obj E).obj n

lemma uliftFunctorHomDown_up {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (f : ((ihom A).obj E).obj n) :
    uliftFunctorHomDown (uliftFunctorHomUp.{u, v} f) = f

lemma uliftFunctorHomUp_down {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (f : ((ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj
      ((SSet.uliftFunctor.{v, u}).obj E)).obj n) :
    uliftFunctorHomUp (uliftFunctorHomDown f) = f

lemma uliftFunctorHomUp_injective {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ} :
    Function.Injective (uliftFunctorHomUp.{u, v} (A := A) (E := E) (n := n))

lemma uliftFunctorHomUp_post {A E B : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (p : E ⟶ B) (f : ((ihom A).obj E).obj n) :
    uliftFunctorHomUp.{u, v} (((ihom A).map p).app n f) =
      ((ihom ((SSet.uliftFunctor.{v, u}).obj A)).map ((SSet.uliftFunctor.{v, u}).map p)).app n
        (uliftFunctorHomUp.{u, v} f)

lemma uliftFunctorHomUp_constant {A E : SSet.{u}} (a : A ⟶ E) (n : ℕ) :
    uliftFunctorHomUp.{u, v} (PinchedHom.constant (functorVertex a) n) =
      PinchedHom.constant (functorVertex ((SSet.uliftFunctor.{v, u}).map a)) n

def uliftFunctorSpaceMap (A E : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj ((ihom A).obj E) ⟶
      (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj ((SSet.uliftFunctor.{v, u}).obj E)

def uliftFunctorSpaceDown (A E : SSet.{u}) :
    (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj ((SSet.uliftFunctor.{v, u}).obj E) ⟶
      (SSet.uliftFunctor.{v, u}).obj ((ihom A).obj E)

def uliftFunctorSpaceIso (A E : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj ((ihom A).obj E) ≅
      (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj ((SSet.uliftFunctor.{v, u}).obj E)

def uliftRelativeFunctorMap {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    (SSet.uliftFunctor.{v, u}).obj (relativeFunctorSpace p a) ⟶
      relativeFunctorSpace ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map a)

def uliftRelativeFunctorDown {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    relativeFunctorSpace ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map a) ⟶
      (SSet.uliftFunctor.{v, u}).obj (relativeFunctorSpace p a)

def uliftRelativeFunctorIso {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    (SSet.uliftFunctor.{v, u}).obj (relativeFunctorSpace p a) ≅
      relativeFunctorSpace ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map a)

lemma uliftRelativeFunctorMap_vertex {A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (f : A ⟶ E) (hf : f ≫ p = a) :
    (uliftRelativeFunctorMap.{u, v} p a).app _ (ULift.up (relativeFunctorVertex p a f hf)) =
      relativeFunctorVertex ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map a)
        ((SSet.uliftFunctor.{v, u}).map f) (by rw [← Functor.map_comp, hf])

lemma uliftRelativeFunctorMap_post {A E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) (a : A ⟶ B) :
    (SSet.uliftFunctor.{v, u}).map (HomotopyLimits.relativeFunctorPost p q f hf a) ≫
      uliftRelativeFunctorMap q a =
    uliftRelativeFunctorMap p a ≫ HomotopyLimits.relativeFunctorPost
      ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map q)
      ((SSet.uliftFunctor.{v, u}).map f) (by rw [← Functor.map_comp, hf])
      ((SSet.uliftFunctor.{v, u}).map a)

lemma uliftRelativeFunctorMap_pre {D A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) :
    (SSet.uliftFunctor.{v, u}).map (relativeFunctorPre p a i) ≫
      uliftRelativeFunctorMap p (i ≫ a) =
    uliftRelativeFunctorMap p a ≫ relativeFunctorPre
      ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map a)
      ((SSet.uliftFunctor.{v, u}).map i)

noncomputable def leftStraighteningCandidateMappingEquivalence
    {C : Type u} [Category.{u} C] {E F : SSet.{u}}
    (p : E ⟶ nerve C) (q : F ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj (relativeFunctorSpace q p))
      (relativeFunctorSpace (leftUnstraighteningProjection (leftStraighteningCandidate q))
        (leftUnstraighteningProjection (leftStraighteningCandidate p)))

def functorParameterizedPrism {K B L X : SSet.{u}}
    (H : K ⊗ L ⟶ (ihom B).obj X) : (K ⊗ B) ⊗ L ⟶ X

lemma simplexPrismVertex_exchange (n : ℕ) (i : Fin (n + 1)) (B L : SSet.{u}) :
    ((simplexPrismVertex n i B ▷ L) ≫ ((β_ (Δ[n] : SSet.{u}) B).hom ▷ L)) ≫
      (α_ B (Δ[n] : SSet.{u}) L).hom = B ◁ simplexPrismVertex n i L

lemma functorParameterizedPrism_vertex {B L X : SSet.{u}} (n : ℕ)
    (H : (Δ[n] : SSet.{u}) ⊗ L ⟶ (ihom B).obj X) (i : Fin (n + 1)) :
    (simplexPrismVertex n i B ▷ L) ≫ functorParameterizedPrism H =
      uncurry (simplexPrismVertex n i L ≫ H)

lemma functorParameterizedPrism_vertex_of_const {B L X : SSet.{u}} (n : ℕ)
    (H : (Δ[n] : SSet.{u}) ⊗ L ⟶ (ihom B).obj X) (i : Fin (n + 1))
    (F : B ⟶ X) (hi : simplexPrismVertex n i L ≫ H = SSet.const (functorVertex F)) :
    (simplexPrismVertex n i B ▷ L) ≫ functorParameterizedPrism H = fst B L ≫ F

lemma simplexPrismVertex_parameterizedBaseChange {A B L X : SSet.{u}}
    (n : ℕ) (i : Fin (n + 1)) (p : A ⟶ B) (T : ((Δ[n] : SSet.{u}) ⊗ B) ⊗ L ⟶ X) :
    ((simplexPrismVertex n i A ▷ L) ≫ ((Δ[n] ◁ p) ▷ L)) ≫ T =
      (p ▷ L) ≫ ((simplexPrismVertex n i B ▷ L) ≫ T)

lemma simplexPrism_initialRestriction {A L X : SSet.{u}} (n : ℕ)
    (W : ((Δ[n] : SSet.{u}) ⊗ A) ⊗ L ⟶ X) (f : A ⟶ X)
    (h : ((scaffoldFirstVertex n ▷ A) ▷ L) ≫ W =
      fst (Δ[0] ⊗ A) L ≫ snd (Δ[0] : SSet.{u}) A ≫ f) :
    (simplexPrismVertex n 0 A ▷ L) ≫ W = fst A L ≫ f

def leftUnstraighteningTransformationSpace {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) :
    SSet.{u + 1}

instance leftUnstraighteningTransformationSpace_kanComplex {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) : KanComplex (leftUnstraighteningTransformationSpace F G)

def leftUnstraighteningTransformationFamily {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    ((Δ[1] : SSet.{u + 1}) ⊗ B) ⊗ leftUnstraighteningTransformationSpace F G ⟶ SpaceInfinity.{u}

lemma leftUnstraighteningTransformationFamily_zero {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    (simplexPrismVertex 1 0 B ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamily F G =
        fst B (leftUnstraighteningTransformationSpace F G) ≫ F

lemma leftUnstraighteningTransformationFamily_one {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    (simplexPrismVertex 1 1 B ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamily F G =
        fst B (leftUnstraighteningTransformationSpace F G) ≫ G

lemma exists_leftUnstraighteningParameterizedSimplexLift {B L : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (n : ℕ)
    (T : ((Δ[n] : SSet.{u + 1}) ⊗ B) ⊗ L ⟶ SpaceInfinity.{u})
    (h₀ : (simplexPrismVertex n 0 B ▷ L) ≫ T = fst B L ≫ F) :
    ∃ W : ((Δ[n] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗ L ⟶ PointedSpaceInfinity.{u},
      W ≫ pointedSpaceProjection = ((Δ[n] ◁ leftUnstraighteningProjection F) ▷ L) ≫ T ∧
      ((scaffoldFirstVertex n ▷ leftUnstraightening F) ▷ L) ≫ W =
        leftUnstraighteningParameterizedSimplexStart F L

noncomputable def leftUnstraighteningTransformationFamilyLift {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u}

lemma leftUnstraighteningTransformationFamilyLift_projection {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningTransformationFamilyLift F G ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G

lemma leftUnstraighteningTransformationFamilyLift_zero {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    ((scaffoldFirstVertex 1 ▷ leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamilyLift F G =
        leftUnstraighteningParameterizedSimplexStart F (leftUnstraighteningTransformationSpace F G)

lemma leftUnstraighteningTransformationFamilyLift_start {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    (simplexPrismVertex 1 0 (leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamilyLift F G =
        fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
          pullback.fst pointedSpaceProjection F

lemma leftUnstraighteningTransformationFamilyLift_one_projection {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    ((simplexPrismVertex 1 1 (leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamilyLift F G) ≫ pointedSpaceProjection =
      (fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningProjection F) ≫ G

noncomputable def leftUnstraighteningMappingFamily {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraightening F ⊗ leftUnstraighteningTransformationSpace F G ⟶ leftUnstraightening G

noncomputable def leftUnstraighteningMappingSpaceMap {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningTransformationSpace F G ⟶
      relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)

lemma leftUnstraighteningMappingSpaceMap_uncurry {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G) =
      leftUnstraighteningMappingFamily F G

lemma leftUnstraighteningMappingSpaceMap_pointed {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G) ≫
      pullback.fst pointedSpaceProjection G =
      (simplexPrismVertex 1 1 (leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamilyLift F G

noncomputable def leftUnstraighteningPinchedMappingSpaceMap {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    pinchedHom (functorVertex F) (functorVertex G) ⟶
      relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)

lemma leftUnstraighteningPinchedMappingSpaceMap_isQCatEquivalence_iff {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (leftUnstraighteningPinchedMappingSpaceMap F G) ↔
      IsQCatEquivalence (leftUnstraighteningMappingSpaceMap F G)

def relativeFunctorCurryHom {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (L : SSet.{u}) :
    relativeFunctorSpace p (fst A L ≫ a) ⟶ (ihom L).obj (relativeFunctorSpace p a)

lemma relativeFunctorCurryHom_vertex {A E B L : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (H : A ⊗ L ⟶ E) (hH : H ≫ p = fst A L ≫ a) :
    (relativeFunctorCurryHom p a L).app _ (relativeFunctorVertex p (fst A L ≫ a) H hH) =
      functorVertex (relativeFunctorCurry H hH)

noncomputable def relativeFunctorCurryIso {A E B L : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (H H' : A ⊗ L ⟶ E)
    (hH : H ≫ p = fst A L ≫ a) (hH' : H' ≫ p = fst A L ≫ a)
    (η : VertexIso (relativeFunctorVertex p (fst A L ≫ a) H hH)
      (relativeFunctorVertex p (fst A L ≫ a) H' hH')) :
    FunctorIso (relativeFunctorCurry H hH) (relativeFunctorCurry H' hH')

lemma relativeFunctorPre_vertex {A C E B : SSet.{u}} (p : E ⟶ B) (b : A ⟶ B)
    (j : C ⟶ A) (W : A ⟶ E) (hW : W ≫ p = b) :
    (relativeFunctorPre p b j).app _ (relativeFunctorVertex p b W hW) =
      relativeFunctorVertex p (j ≫ b) (j ≫ W) (by rw [Category.assoc, hW])

noncomputable def relativeFunctorExtensionEndpoint {A D C E F B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F) (hj : j ≫ b = a ≫ q) :
    relativeFunctorExtensionSpace p b i v hv ⟶ relativeFunctorSpace (pullback.snd p q) a

lemma relativeFunctorExtensionEndpoint_vertex {A D C E F B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F) (hj : j ≫ b = a ≫ q)
    (W : A ⟶ E) (hW : W ≫ p = b) (hWi : i ≫ W = v)
    (g : C ⟶ pullback p q) (hg : g ≫ pullback.snd p q = a)
    (hWj : j ≫ W = g ≫ pullback.fst p q) :
    (relativeFunctorExtensionEndpoint p b i v hv j q a hj).app _
      (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩) =
      relativeFunctorVertex (pullback.snd p q) a g hg

noncomputable def relativeFunctorExtensionEndpoint_witnessIso {A D C E F B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : A ⟶ B) (i : D ⟶ A) (hi : leftAnodyneExtensions i)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F) (hj : j ≫ b = a ≫ q)
    (W W' : A ⟶ E) (hW : W ≫ p = b) (hW' : W' ≫ p = b)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (g g' : C ⟶ pullback p q) (hg : g ≫ pullback.snd p q = a) (hg' : g' ≫ pullback.snd p q = a)
    (hWj : j ≫ W = g ≫ pullback.fst p q) (hWj' : j ≫ W' = g' ≫ pullback.fst p q) :
    VertexIso (relativeFunctorVertex (pullback.snd p q) a g hg)
      (relativeFunctorVertex (pullback.snd p q) a g' hg')

lemma leftUnstraighteningMappingChoice_endpoint_base {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    (simplexPrismVertex 1 1 (leftUnstraightening F) ▷ leftUnstraighteningTransformationSpace F G) ≫
      (((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G) =
      (fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningProjection F) ≫ G

noncomputable def leftUnstraighteningMappingFamilyOfLift {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (W : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u})
    (hWp : W ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G) :
    {g : leftUnstraightening F ⊗ leftUnstraighteningTransformationSpace F G ⟶ leftUnstraightening G //
      g ≫ leftUnstraighteningProjection G =
        fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
          leftUnstraighteningProjection F}

noncomputable def leftUnstraighteningMappingSpaceMapOfLift {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (W : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u})
    (hWp : W ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G) :
    leftUnstraighteningTransformationSpace F G ⟶
      relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)

noncomputable def leftUnstraighteningMappingSpaceMapOfLift_iso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (W W' : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u})
    (hWp : W ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G)
    (hWp' : W' ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G)
    (hW₀ : ((scaffoldFirstVertex 1 ▷ leftUnstraightening F) ▷
      leftUnstraighteningTransformationSpace F G) ≫ W =
        leftUnstraighteningParameterizedSimplexStart F (leftUnstraighteningTransformationSpace F G))
    (hW₀' : ((scaffoldFirstVertex 1 ▷ leftUnstraightening F) ▷
      leftUnstraighteningTransformationSpace F G) ≫ W' =
        leftUnstraighteningParameterizedSimplexStart F (leftUnstraighteningTransformationSpace F G)) :
    FunctorIso (leftUnstraighteningMappingSpaceMapOfLift F G W hWp)
      (leftUnstraighteningMappingSpaceMapOfLift F G W' hWp')

lemma leftUnstraighteningMappingSpaceMap_eq_ofLift {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningMappingSpaceMap F G =
      leftUnstraighteningMappingSpaceMapOfLift F G (leftUnstraighteningTransformationFamilyLift F G)
        (leftUnstraighteningTransformationFamilyLift_projection F G)

noncomputable def leftUnstraighteningMappingSpaceMap_iso_ofLift {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (W : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u})
    (hWp : W ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamily F G)
    (hW₀ : ((scaffoldFirstVertex 1 ▷ leftUnstraightening F) ▷
      leftUnstraighteningTransformationSpace F G) ≫ W =
        leftUnstraighteningParameterizedSimplexStart F (leftUnstraighteningTransformationSpace F G)) :
    FunctorIso (leftUnstraighteningMappingSpaceMap F G)
      (leftUnstraighteningMappingSpaceMapOfLift F G W hWp)

lemma intervalMappingBoundary_of_edge {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (boundary 1).ι ≫ SSet.yonedaEquiv.symm e.edge = intervalMappingBoundary x y

def intervalMappingVertexOfEdge {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (intervalMappingSpace x y) _⦋0⦌

lemma uncurry_at_vertex {A L E : SSet.{u}} (f : L ⟶ (ihom A).obj E) (x : L _⦋0⦌) :
    lift (𝟙 A) (SSet.const x) ≫ uncurry f =
      (functorVertexEquiv A E).symm (f.app (Opposite.op ⦋0⦌) x)

lemma relativeFunctorCurry_vertex {A L E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (H : A ⊗ L ⟶ E) (hH : H ≫ p = fst A L ≫ a) (x : L _⦋0⦌) :
    (relativeFunctorCurry H hH).app _ x =
      relativeFunctorVertex p a (lift (𝟙 A) (SSet.const x) ≫ H) (by
        rw [Category.assoc, hH, ← Category.assoc, lift_fst, Category.id_comp])

lemma functorParameterizedPrism_at_parameter {K B L E : SSet.{u}}
    (H : K ⊗ L ⟶ (ihom B).obj E) (x : L _⦋0⦌) :
    lift (𝟙 (K ⊗ B)) (SSet.const x) ≫ functorParameterizedPrism H =
      functorFamilyPrism (lift (𝟙 K) (SSet.const x) ≫ H)

lemma parameterVertex_naturality {A B L : SSet.{u}} (f : A ⟶ B) (x : L _⦋0⦌) :
    lift (𝟙 A) (SSet.const x) ≫ (f ▷ L) = f ≫ lift (𝟙 B) (SSet.const x)

lemma intervalMappingUniversal_at_edge {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (intervalMappingVertexOfEdge e)) ≫
      intervalMappingUncurry (𝟙 (intervalMappingSpace x y)) = SSet.yonedaEquiv.symm e.edge

lemma leftUnstraighteningTransformationFamily_at_edge {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G)) :
    lift (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ B)) (SSet.const (intervalMappingVertexOfEdge e)) ≫
      leftUnstraighteningTransformationFamily F G = functorEdgePrism e

lemma leftUnstraighteningMappingSpaceMap_vertex {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    (leftUnstraighteningMappingSpaceMap F G).app _ x =
      relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
        (lift (𝟙 (leftUnstraightening F)) (SSet.const x) ≫ leftUnstraighteningMappingFamily F G) (by
          have hp : leftUnstraighteningMappingFamily F G ≫ leftUnstraighteningProjection G =
              fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
                leftUnstraighteningProjection F := pullback.lift_snd _ _ _
          rw [Category.assoc, hp, ← Category.assoc, lift_fst, Category.id_comp])

noncomputable def leftUnstraighteningMappingSpaceMap_edgeVertexIso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G)) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
      (leftUnstraighteningEdgeMap F G e).val (leftUnstraighteningEdgeMap F G e).property)
      ((leftUnstraighteningMappingSpaceMap F G).app _ (intervalMappingVertexOfEdge e))

noncomputable def leftUnstraighteningMappingVertexMap {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    {f : leftUnstraightening F ⟶ leftUnstraightening G //
      f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F}

lemma leftUnstraighteningMappingVertexMap_vertex {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
      (leftUnstraighteningMappingVertexMap F G x).val (leftUnstraighteningMappingVertexMap F G x).property =
      (leftUnstraighteningMappingSpaceMap F G).app _ x

lemma leftUnstraighteningMappingVertexMap_isPrecompositionEquivalence_of_isInvertibleEdge
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G))
    (he : IsInvertibleEdge e) :
    IsPrecompositionEquivalence
      (leftUnstraighteningMappingVertexMap F G (intervalMappingVertexOfEdge e)).val

lemma leftUnstraighteningMappingVertexMap_isQCatEquivalence_of_isInvertibleEdge
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G))
    (he : IsInvertibleEdge e) :
    IsQCatEquivalence (leftUnstraighteningMappingVertexMap F G (intervalMappingVertexOfEdge e)).val

lemma intervalMappingBoundary_face_one {X : SSet.{u}} (x y : X _⦋0⦌) :
    boundary.ι (1 : Fin 2) ≫ intervalMappingBoundary x y = SSet.yonedaEquiv.symm x

lemma intervalMappingBoundary_face_zero {X : SSet.{u}} (x y : X _⦋0⦌) :
    boundary.ι (0 : Fin 2) ≫ intervalMappingBoundary x y = SSet.yonedaEquiv.symm y

noncomputable def intervalMappingEdgeOfVertex {X : SSet.{u}} {x y : X _⦋0⦌}
    (v : (intervalMappingSpace x y) _⦋0⦌) : SSet.Edge x y

noncomputable def intervalMappingEdgeVertexEquiv {X : SSet.{u}} (x y : X _⦋0⦌) :
    SSet.Edge x y ≃ (intervalMappingSpace x y) _⦋0⦌

lemma leftUnstraighteningMappingVertexMap_eq_family {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    (leftUnstraighteningMappingVertexMap F G x).val =
      lift (𝟙 (leftUnstraightening F)) (SSet.const x) ≫ leftUnstraighteningMappingFamily F G

noncomputable def leftUnstraighteningMappingSpaceMap_vertexIso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
      (leftUnstraighteningEdgeMap F G (intervalMappingEdgeOfVertex x)).val
      (leftUnstraighteningEdgeMap F G (intervalMappingEdgeOfVertex x)).property)
      ((leftUnstraighteningMappingSpaceMap F G).app _ x)

lemma leftUnstraighteningMappingVertexMap_isPrecompositionEquivalence_of_recoveredEdge
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (hx : IsInvertibleEdge (intervalMappingEdgeOfVertex x)) :
    IsPrecompositionEquivalence (leftUnstraighteningMappingVertexMap F G x).val

noncomputable def relativeFunctorPullback {E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B) :
    relativeFunctorSpace q p ⟶
      relativeFunctorSpace (pullback.snd q k) (pullback.snd p k)

lemma relativeFunctorPullback_uncurry_fst {E F B D T : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B)
    (f : T ⟶ relativeFunctorSpace q p) :
    relativeFunctorUncurry (f ≫ relativeFunctorPullback p q k) ≫ pullback.fst q k =
      (pullback.fst p k ▷ T) ≫ relativeFunctorUncurry f

lemma relativeFunctorPullback_uncurry_snd {E F B D T : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B)
    (f : T ⟶ relativeFunctorSpace q p) :
    relativeFunctorUncurry (f ≫ relativeFunctorPullback p q k) ≫ pullback.snd q k =
      fst (pullback p k) T ≫ pullback.snd p k

lemma relativeFunctorPullback_identity {B D : SSet.{u}} (a : Over B) (k : D ⟶ B) :
    relativeFunctorIdentity a ≫ relativeFunctorPullback a.hom a.hom k =
      relativeFunctorIdentity (Over.mk (pullback.snd a.hom k))

lemma relativeFunctorPullback_composition {B D : SSet.{u}}
    (a b c : Over B) (k : D ⟶ B) :
    relativeFunctorComposition a b c ≫ relativeFunctorPullback a.hom c.hom k =
      (relativeFunctorPullback a.hom b.hom k ⊗ₘ relativeFunctorPullback b.hom c.hom k) ≫
        relativeFunctorComposition (Over.mk (pullback.snd a.hom k))
          (Over.mk (pullback.snd b.hom k)) (Over.mk (pullback.snd c.hom k))

noncomputable def leftFibrationBaseChangeObject {B D : SSet.{u}}
    (k : D ⟶ B) (p : LeftFibrationObject B) : LeftFibrationObject D

noncomputable def leftFibrationBaseChangeEnriched {B D : SSet.{u}} (k : D ⟶ B) :
    EnrichedFunctor SSet.{u} (LeftFibrationObject B) (LeftFibrationObject D)

noncomputable def leftFibrationInfinityBaseChange {B D : SSet.{u}} (k : D ⟶ B) :
    LeftFibrationInfinity B ⟶ LeftFibrationInfinity D

lemma leftFibrationInfinityBaseChange_vertex {B D : SSet.{u}}
    (k : D ⟶ B) (p : LeftFibrationObject B) :
    (leftFibrationInfinityBaseChange k).app (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      coherentNerveVertex (leftFibrationBaseChangeObject k p)

noncomputable def leftUnstraighteningBaseChangeIso {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    leftUnstraightening (k ≫ F) ≅ pullback (leftUnstraighteningProjection F) k

lemma leftUnstraighteningBaseChangeIso_hom_fst {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    (leftUnstraighteningBaseChangeIso F k).hom ≫
      pullback.fst (leftUnstraighteningProjection F) k =
        leftUnstraighteningMap (k ≫ F) F k rfl

lemma leftUnstraighteningBaseChangeIso_hom_snd {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    (leftUnstraighteningBaseChangeIso F k).hom ≫
      pullback.snd (leftUnstraighteningProjection F) k =
        leftUnstraighteningProjection (k ≫ F)

noncomputable def leftUnstraighteningBaseChangeOverIso {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    Over.mk (leftUnstraighteningProjection (k ≫ F)) ≅
      (leftFibrationBaseChangeObject k
        (leftFibrationObjectOf (leftUnstraighteningProjection F))).val

lemma relativeFunctorPullback_vertex {E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) :
    (relativeFunctorPullback p q k).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex q p f hf) =
    relativeFunctorVertex (pullback.snd q k) (pullback.snd p k)
      (pullback.lift (pullback.fst p k ≫ f) (pullback.snd p k)
        (by rw [Category.assoc, hf, pullback.condition])) (pullback.lift_snd _ _ _)

lemma intervalMappingBoundary_post {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) :
    intervalMappingBoundary x y ≫ f =
      intervalMappingBoundary (f.app _ x) (f.app _ y)

def intervalMappingPost {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) :
    intervalMappingSpace x y ⟶ intervalMappingSpace (f.app _ x) (f.app _ y)

lemma intervalMappingPost_uncurry {T X Y : SSet.{u}}
    (f : X ⟶ Y) (x y : X _⦋0⦌) (g : T ⟶ intervalMappingSpace x y) :
    intervalMappingUncurry (g ≫ intervalMappingPost f x y) =
      intervalMappingUncurry g ≫ f

lemma functorParameterizedPrism_pre {K B D L X : SSet.{u}}
    (H : K ⊗ L ⟶ (ihom B).obj X) (k : D ⟶ B) :
    functorParameterizedPrism (H ≫ (pre k).app X) =
      ((K ◁ k) ▷ L) ≫ functorParameterizedPrism H

lemma functorParameterizedPrism_parameter {K B L M X : SSet.{u}}
    (H : K ⊗ L ⟶ (ihom B).obj X) (i : M ⟶ L) :
    functorParameterizedPrism ((K ◁ i) ≫ H) =
      ((K ⊗ B) ◁ i) ≫ functorParameterizedPrism H

def leftUnstraighteningTransformationRestriction {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    leftUnstraighteningTransformationSpace F G ⟶
      leftUnstraighteningTransformationSpace (k ≫ F) (k ≫ G)

lemma leftUnstraighteningTransformationRestriction_uncurry {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    intervalMappingUncurry (leftUnstraighteningTransformationRestriction F G k) =
      intervalMappingUncurry (𝟙 (leftUnstraighteningTransformationSpace F G)) ≫
        (pre k).app SpaceInfinity

lemma leftUnstraighteningTransformationFamily_restriction {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    ((Δ[1] ⊗ D) ◁ leftUnstraighteningTransformationRestriction F G k) ≫
      leftUnstraighteningTransformationFamily (k ≫ F) (k ≫ G) =
    ((Δ[1] ◁ k) ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamily F G

noncomputable def leftUnstraighteningRestrictedLift {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening (k ≫ F)) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u}

noncomputable def leftUnstraighteningRestrictionLift {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening (k ≫ F)) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u}

lemma leftUnstraighteningRestrictedLift_projection {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    leftUnstraighteningRestrictedLift F G k ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection (k ≫ F)) ▷
        leftUnstraighteningTransformationSpace F G) ≫
      ((Δ[1] ⊗ D) ◁ leftUnstraighteningTransformationRestriction F G k) ≫
        leftUnstraighteningTransformationFamily (k ≫ F) (k ≫ G)

lemma leftUnstraighteningRestrictionLift_projection {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    leftUnstraighteningRestrictionLift F G k ≫ pointedSpaceProjection =
      ((Δ[1] ◁ leftUnstraighteningProjection (k ≫ F)) ▷
        leftUnstraighteningTransformationSpace F G) ≫
      ((Δ[1] ⊗ D) ◁ leftUnstraighteningTransformationRestriction F G k) ≫
        leftUnstraighteningTransformationFamily (k ≫ F) (k ≫ G)

lemma leftUnstraighteningRestrictedLift_start {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    (simplexPrismVertex 1 0 (leftUnstraightening (k ≫ F)) ▷
      leftUnstraighteningTransformationSpace F G) ≫ leftUnstraighteningRestrictedLift F G k =
    fst (leftUnstraightening (k ≫ F)) (leftUnstraighteningTransformationSpace F G) ≫
      pullback.fst pointedSpaceProjection (k ≫ F)

lemma leftUnstraighteningRestrictionLift_start {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    (simplexPrismVertex 1 0 (leftUnstraightening (k ≫ F)) ▷
      leftUnstraighteningTransformationSpace F G) ≫ leftUnstraighteningRestrictionLift F G k =
    fst (leftUnstraightening (k ≫ F)) (leftUnstraighteningTransformationSpace F G) ≫
      pullback.fst pointedSpaceProjection (k ≫ F)

noncomputable def relativeFunctorExtensionEndpoint_curryIso
    {A D C E F B L : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    (b : A ⟶ B) (i : D ⟶ A) (hi : leftAnodyneExtensions i)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⊗ L ⟶ A) (q : F ⟶ B) (a : C ⟶ F)
    (hj : j ≫ b = (fst C L ≫ a) ≫ q)
    (W W' : A ⟶ E) (hW : W ≫ p = b) (hW' : W' ≫ p = b)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (g g' : C ⊗ L ⟶ pullback p q)
    (hg : g ≫ pullback.snd p q = fst C L ≫ a)
    (hg' : g' ≫ pullback.snd p q = fst C L ≫ a)
    (hWj : j ≫ W = g ≫ pullback.fst p q)
    (hWj' : j ≫ W' = g' ≫ pullback.fst p q) :
    FunctorIso (relativeFunctorCurry g hg) (relativeFunctorCurry g' hg')

lemma leftUnstraighteningMappingFamily_projection {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningMappingFamily F G ≫ leftUnstraighteningProjection G =
      fst _ _ ≫ leftUnstraighteningProjection F

lemma leftUnstraighteningMappingFamily_pointed {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningMappingFamily F G ≫ pullback.fst pointedSpaceProjection G =
      (simplexPrismVertex 1 1 (leftUnstraightening F) ▷
        leftUnstraighteningTransformationSpace F G) ≫
          leftUnstraighteningTransformationFamilyLift F G

noncomputable def leftUnstraighteningMappingSourceRestriction {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    {g : leftUnstraightening (k ≫ F) ⊗ leftUnstraighteningTransformationSpace F G ⟶
        leftUnstraightening G //
      g ≫ leftUnstraighteningProjection G =
        fst _ _ ≫ leftUnstraighteningProjection (k ≫ F) ≫ k}

noncomputable def leftUnstraighteningMappingTargetRestriction {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    {g : leftUnstraightening (k ≫ F) ⊗ leftUnstraighteningTransformationSpace F G ⟶
        leftUnstraightening G //
      g ≫ leftUnstraighteningProjection G =
        fst _ _ ≫ leftUnstraighteningProjection (k ≫ F) ≫ k}

noncomputable def leftUnstraighteningMappingRestrictionIso {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    FunctorIso
      (relativeFunctorCurry (leftUnstraighteningMappingSourceRestriction F G k).val
        (leftUnstraighteningMappingSourceRestriction F G k).property)
      (relativeFunctorCurry (leftUnstraighteningMappingTargetRestriction F G k).val
        (leftUnstraighteningMappingTargetRestriction F G k).property)

def relativeFunctorSquarePost {A E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (k : B ⟶ D)
    (f : E ⟶ F) (hf : f ≫ q = p ≫ k) (a : A ⟶ B) :
    relativeFunctorSpace p a ⟶ relativeFunctorSpace q (a ≫ k)

lemma relativeFunctorSquarePost_uncurry {A E F B D T : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (k : B ⟶ D)
    (f : E ⟶ F) (hf : f ≫ q = p ≫ k) (a : A ⟶ B)
    (g : T ⟶ relativeFunctorSpace p a) :
    relativeFunctorUncurry (g ≫ relativeFunctorSquarePost p q k f hf a) =
      relativeFunctorUncurry g ≫ f

lemma relativeFunctorSquarePost_vertex {A E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (k : B ⟶ D)
    (f : E ⟶ F) (hf : f ≫ q = p ≫ k) (a : A ⟶ B)
    (g : A ⟶ E) (hg : g ≫ p = a) :
    (relativeFunctorSquarePost p q k f hf a).app _ (relativeFunctorVertex p a g hg) =
      relativeFunctorVertex q (a ≫ k) (g ≫ f)
        (by rw [Category.assoc, hf, ← Category.assoc, hg])

lemma relativeFunctorOverPre_uncurry {E B T : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (f : a ⟶ b) (g : T ⟶ relativeFunctorSpace p b.hom) :
    relativeFunctorUncurry (g ≫ relativeFunctorOverPre p f) =
      (f.left ▷ T) ≫ relativeFunctorUncurry g

noncomputable def leftUnstraighteningOverBaseMap {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    Over.mk (leftUnstraighteningProjection (k ≫ F) ≫ k) ⟶
      Over.mk (leftUnstraighteningProjection F)

lemma leftUnstraighteningMappingSourceRestriction_curry {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    leftUnstraighteningMappingSpaceMap F G ≫
      relativeFunctorOverPre (leftUnstraighteningProjection G)
        (leftUnstraighteningOverBaseMap F k) =
    relativeFunctorCurry (leftUnstraighteningMappingSourceRestriction F G k).val
      (leftUnstraighteningMappingSourceRestriction F G k).property

lemma leftUnstraighteningMappingTargetRestriction_curry {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    (leftUnstraighteningTransformationRestriction F G k ≫
      leftUnstraighteningMappingSpaceMap (k ≫ F) (k ≫ G)) ≫
        relativeFunctorSquarePost (leftUnstraighteningProjection (k ≫ G))
          (leftUnstraighteningProjection G) k (leftUnstraighteningMap (k ≫ G) G k rfl)
          (leftUnstraighteningMap_projection (k ≫ G) G k rfl)
          (leftUnstraighteningProjection (k ≫ F)) =
    relativeFunctorCurry (leftUnstraighteningMappingTargetRestriction F G k).val
      (leftUnstraighteningMappingTargetRestriction F G k).property

noncomputable def leftUnstraighteningMappingSpaceMap_baseChangeIso
    {B D : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    FunctorIso
      (leftUnstraighteningMappingSpaceMap F G ≫
        relativeFunctorOverPre (leftUnstraighteningProjection G)
          (leftUnstraighteningOverBaseMap F k))
      ((leftUnstraighteningTransformationRestriction F G k ≫
        leftUnstraighteningMappingSpaceMap (k ≫ F) (k ≫ G)) ≫
          relativeFunctorSquarePost (leftUnstraighteningProjection (k ≫ G))
            (leftUnstraighteningProjection G) k (leftUnstraighteningMap (k ≫ G) G k rfl)
            (leftUnstraighteningMap_projection (k ≫ G) G k rfl)
            (leftUnstraighteningProjection (k ≫ F)))

noncomputable def relativeFunctorSquareLift {A E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (k : B ⟶ D) (f : E ⟶ F)
    (h : IsPullback f p q k) (a : A ⟶ B) :
    relativeFunctorSpace q (a ≫ k) ⟶ relativeFunctorSpace p a

lemma relativeFunctorSquareLift_uncurry_fst {A E F B D T : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (k : B ⟶ D) (f : E ⟶ F)
    (h : IsPullback f p q k) (a : A ⟶ B)
    (g : T ⟶ relativeFunctorSpace q (a ≫ k)) :
    relativeFunctorUncurry (g ≫ relativeFunctorSquareLift p q k f h a) ≫ f =
      relativeFunctorUncurry g

noncomputable def relativeFunctorPullbackSquareIso {A E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (k : B ⟶ D) (f : E ⟶ F)
    (h : IsPullback f p q k) (a : A ⟶ B) :
    relativeFunctorSpace p a ≅ relativeFunctorSpace q (a ≫ k)

noncomputable def leftUnstraighteningMappingPullbackIso {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    relativeFunctorSpace (leftUnstraighteningProjection (k ≫ G))
      (leftUnstraighteningProjection (k ≫ F)) ≅
    relativeFunctorSpace (leftUnstraighteningProjection G)
      (leftUnstraighteningProjection (k ≫ F) ≫ k)

noncomputable def leftUnstraighteningRelativeRestriction {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F) ⟶
      relativeFunctorSpace (leftUnstraighteningProjection (k ≫ G))
        (leftUnstraighteningProjection (k ≫ F))

noncomputable def leftUnstraighteningMappingSpaceMap_restrictionIso
    {B D : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    FunctorIso
      (leftUnstraighteningMappingSpaceMap F G ≫ leftUnstraighteningRelativeRestriction F G k)
      (leftUnstraighteningTransformationRestriction F G k ≫
        leftUnstraighteningMappingSpaceMap (k ≫ F) (k ≫ G))

lemma coherentHomComparison_ordinary {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} (f : X ⟶ Y) :
    ((coherentHomComparison X Y).app (Opposite.op ⦋0⦌)
      (ULift.up (SimplicialCategory.homEquiv' X Y f))).val =
        (coherentNerveEdge f).edge

noncomputable def spaceInfinityUnderlyingHomEquivalence (K L : KanObject.{u}) :
    QCatEquivalence (pinchedHom (coherentNerveVertex K) (coherentNerveVertex L))
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj K.obj)).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj L.obj))

lemma spaceInfinityUnderlyingHomEquivalence_inv_vertex (K L : KanObject.{u}) (f : K ⟶ L) :
    ((spaceInfinityUnderlyingHomEquivalence K L).inv.app (Opposite.op ⦋0⦌)
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map f))).val =
        (coherentNerveEdge f).edge

noncomputable def spaceInfinityUnderlyingHomEquivalenceAt
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    QCatEquivalence (pinchedHom s t)
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject s).obj)).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject t).obj))

noncomputable def pointedSpaceFiberHomEquivalence (s t : SpaceInfinity.{u} _⦋0⦌) :
    QCatEquivalence (pinchedHom s t)
      ((ihom (vertexFiber pointedSpaceProjection s)).obj
        (vertexFiber pointedSpaceProjection t))

def functorEdgeAt {B X : SSet.{u}} {F G : B ⟶ X}
    (e : SSet.Edge (X := (ihom B).obj X) (functorVertex F) (functorVertex G))
    (b : B _⦋0⦌) : SSet.Edge (F.app _ b) (G.app _ b)

lemma functorEdgePrism_const {B X A : SSet.{u}} {F G : B ⟶ X}
    (e : SSet.Edge (X := (ihom B).obj X) (functorVertex F) (functorVertex G))
    (b : B _⦋0⦌) :
    (Δ[1] ◁ (SSet.const b : A ⟶ B)) ≫ functorEdgePrism e =
      fst (Δ[1] : SSet.{u}) A ≫
        SSet.yonedaEquiv.symm (e.map (evaluateFunctorAt b)).edge

lemma functorParameterizedPrism_const {K B A L X : SSet.{u}}
    (H : K ⊗ L ⟶ (ihom B).obj X) (b : B _⦋0⦌) :
    ((K ◁ (SSet.const b : A ⟶ B)) ▷ L) ≫ functorParameterizedPrism H =
      (fst K A ▷ L) ≫ H ≫ evaluateFunctorAt b

lemma leftUnstraighteningFiberIso_hom_ι {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (leftUnstraighteningFiberIso F b).hom ≫
      vertexFiberι pointedSpaceProjection (F.app _ b) =
    vertexFiberι (leftUnstraighteningProjection F) b ≫ pullback.fst pointedSpaceProjection F

lemma leftUnstraighteningFiberIso_inv_ι_fst {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (leftUnstraighteningFiberIso F b).inv ≫
      vertexFiberι (leftUnstraighteningProjection F) b ≫ pullback.fst pointedSpaceProjection F =
    vertexFiberι pointedSpaceProjection (F.app _ b)

noncomputable def leftUnstraighteningPointedFiberMap {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (f : leftUnstraightening F ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (b : B _⦋0⦌) :
    vertexFiber pointedSpaceProjection (F.app _ b) ⟶
      vertexFiber pointedSpaceProjection (G.app _ b)

lemma leftUnstraighteningPointedFiberMap_ι {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (f : leftUnstraightening F ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (b : B _⦋0⦌) :
    leftUnstraighteningPointedFiberMap F G f hf b ≫
      vertexFiberι pointedSpaceProjection (G.app _ b) =
    (leftUnstraighteningFiberIso F b).inv ≫
      vertexFiberι (leftUnstraighteningProjection F) b ≫ f ≫
        pullback.fst pointedSpaceProjection G

lemma leftUnstraighteningEdgeMap_pointedFiber_isTransport {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u})
      (functorVertex F) (functorVertex G)) (b : B _⦋0⦌) :
    IsEdgeTransport pointedSpaceProjection (functorEdgeAt e b)
      (leftUnstraighteningPointedFiberMap F G (leftUnstraighteningEdgeMap F G e).val
        (leftUnstraighteningEdgeMap F G e).property b)

noncomputable def leftUnstraighteningEdgeMap_pointedFiberTransportIso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u})
      (functorVertex F) (functorVertex G)) (b : B _⦋0⦌) :
    FunctorIso
      (leftUnstraighteningPointedFiberMap F G (leftUnstraighteningEdgeMap F G e).val
        (leftUnstraighteningEdgeMap F G e).property b)
      (edgeTransport pointedSpaceProjection (functorEdgeAt e b))

def relativeFunctorFiberEvaluation {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌) :
    vertexFiber p b ⊗ relativeFunctorSpace q p ⟶ vertexFiber q b

def relativeFunctorFiberHom {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌) :
    relativeFunctorSpace q p ⟶ (ihom (vertexFiber p b)).obj (vertexFiber q b)

lemma relativeFunctorFiberHom_vertex {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌)
    (f : E ⟶ F) (hf : f ≫ q = p) :
    (relativeFunctorFiberHom p q b).app _ (relativeFunctorVertex q p f hf) =
      functorVertex (vertexFiberMap p q f hf b)

lemma relativeFunctorFiberHom_uncurry {E F B T : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌)
    (f : T ⟶ relativeFunctorSpace q p) :
    uncurry (f ≫ relativeFunctorFiberHom p q b) ≫ vertexFiberι q b =
      (vertexFiberι p b ▷ T) ≫ relativeFunctorUncurry f

noncomputable def leftUnstraighteningMappingVertex_pointedFiberTransportIso
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : B _⦋0⦌) :
    FunctorIso
      (leftUnstraighteningPointedFiberMap F G (leftUnstraighteningMappingVertexMap F G x).val
        (leftUnstraighteningMappingVertexMap F G x).property b)
      (edgeTransport pointedSpaceProjection (functorEdgeAt (intervalMappingEdgeOfVertex x) b))

noncomputable def leftUnstraighteningMappingFiberHom {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    leftUnstraighteningTransformationSpace F G ⟶
      (ihom (vertexFiber pointedSpaceProjection (F.app _ b))).obj
        (vertexFiber pointedSpaceProjection (G.app _ b))

noncomputable def leftUnstraighteningFiberFamilyLift {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    ((Δ[1] : SSet.{u + 1}) ⊗ vertexFiber pointedSpaceProjection (F.app _ b)) ⊗
      leftUnstraighteningTransformationSpace F G ⟶ PointedSpaceInfinity.{u}

lemma leftUnstraighteningFiberFamilyLift_start {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (simplexPrismVertex 1 0 (vertexFiber pointedSpaceProjection (F.app _ b)) ▷
      leftUnstraighteningTransformationSpace F G) ≫ leftUnstraighteningFiberFamilyLift F G b =
    fst _ _ ≫ vertexFiberι pointedSpaceProjection (F.app _ b)

lemma leftUnstraighteningFiberFamilyLift_projection {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    leftUnstraighteningFiberFamilyLift F G b ≫ pointedSpaceProjection =
    (fst (Δ[1] : SSet.{u + 1}) (vertexFiber pointedSpaceProjection (F.app _ b)) ▷
      leftUnstraighteningTransformationSpace F G) ≫
      intervalMappingUncurry (𝟙 (leftUnstraighteningTransformationSpace F G)) ≫
        evaluateFunctorAt b

lemma leftUnstraighteningMappingFiberHom_uncurry {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    uncurry (leftUnstraighteningMappingFiberHom F G b) ≫
      vertexFiberι pointedSpaceProjection (G.app _ b) =
    (((leftUnstraighteningFiberIso F b).inv ≫
      vertexFiberι (leftUnstraighteningProjection F) b) ▷
        leftUnstraighteningTransformationSpace F G) ≫
      relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G) ≫
        pullback.fst pointedSpaceProjection G

lemma leftUnstraighteningFiberFamilyLift_end {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    uncurry (leftUnstraighteningMappingFiberHom F G b) ≫
      vertexFiberι pointedSpaceProjection (G.app _ b) =
    (simplexPrismVertex 1 1 (vertexFiber pointedSpaceProjection (F.app _ b)) ▷
      leftUnstraighteningTransformationSpace F G) ≫ leftUnstraighteningFiberFamilyLift F G b

def weightedNerveConstantProduct (C : Type u) [Category.{u} C] (K : SSet.{u}) :
    nerve C ⊗ K ⟶ weightedNerve ((CategoryTheory.Functor.const C).obj K)

lemma weightedNerveConstantProduct_projection (C : Type u) [Category.{u} C] (K : SSet.{u}) :
    weightedNerveConstantProduct C K ≫
      weightedNerveProjection ((CategoryTheory.Functor.const C).obj K) = fst (nerve C) K

lemma weightedNerveConstantProduct_at {C : Type u} [Category.{u} C] (K : SSet.{u}) (c : C) :
    lift (SSet.const (nerveVertex c)) (𝟙 K) ≫ weightedNerveConstantProduct C K =
      weightedNerveConstantLift ((CategoryTheory.Functor.const C).obj K) c

lemma weightedNerveConstantLift_map {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) (c : C) :
    weightedNerveConstantLift F c ≫ weightedNerveMap η =
      η.app c ≫ weightedNerveConstantLift G c

lemma weightedNerveConstantLift_baseMap
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) (d : D) :
    weightedNerveConstantLift (H ⋙ F) d ≫ weightedNerveBaseMap H F =
      weightedNerveConstantLift F (H.obj d)

def weightedNerveUnderCoefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    (CategoryTheory.Functor.const (Under c)).obj (F.obj c) ⟶ Under.forget c ⋙ F

def weightedNerveUnderEvaluation {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : nerve (Under c) ⊗ F.obj c ⟶ weightedNerve F

lemma weightedNerveUnderEvaluation_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    weightedNerveUnderEvaluation F c ≫ weightedNerveProjection F =
      fst (nerve (Under c)) (F.obj c) ≫ nerveMap (Under.forget c)

lemma weightedNerveUnderEvaluation_at {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) (d : Under c) :
    lift (SSet.const (nerveVertex d)) (𝟙 (F.obj c)) ≫ weightedNerveUnderEvaluation F c =
      F.map d.hom ≫ weightedNerveConstantLift F d.right

lemma prismEndpoint_edge_source {X A : SSet.{u}} {a b : X _⦋0⦌} (e : SSet.Edge a b) :
    prismEndpoint 0 A ≫ (SSet.yonedaEquiv.symm e.edge ▷ A) =
      lift (SSet.const a) (𝟙 A)

lemma prismEndpoint_edge_target {X A : SSet.{u}} {a b : X _⦋0⦌} (e : SSet.Edge a b) :
    prismEndpoint 1 A ≫ (SSet.yonedaEquiv.symm e.edge ▷ A) =
      lift (SSet.const b) (𝟙 A)

noncomputable def weightedNerveTransportPrism {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    (Δ[1] : SSet.{u}) ⊗ F.obj c ⟶ weightedNerve F

lemma weightedNerveTransportPrism_zero {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    prismEndpoint 0 _ ≫ weightedNerveTransportPrism F f = weightedNerveConstantLift F c

lemma weightedNerveTransportPrism_one {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    prismEndpoint 1 _ ≫ weightedNerveTransportPrism F f =
      F.map f ≫ weightedNerveConstantLift F d

lemma weightedNerveTransportPrism_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    weightedNerveTransportPrism F f ≫ weightedNerveProjection F =
      fst (Δ[1] : SSet.{u}) (F.obj c) ≫ SSet.yonedaEquiv.symm (nerve.edgeMk f).edge

lemma weightedNerveFiberIso_hom_ι {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    (weightedNerveFiberIso F c).hom ≫
      vertexFiberι (weightedNerveProjection F) (nerveVertex c) =
        weightedNerveConstantLift F c

lemma weightedNerveFiberIso_inv_constantLift {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    (weightedNerveFiberIso F c).inv ≫ weightedNerveConstantLift F c =
      vertexFiberι (weightedNerveProjection F) (nerveVertex c)

noncomputable def weightedNerveCoefficientTransport {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    vertexFiber (weightedNerveProjection F) (nerveVertex c) ⟶
      vertexFiber (weightedNerveProjection F) (nerveVertex d)

lemma weightedNerveCoefficientTransport_isTransport {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] {c d : C} (f : c ⟶ d) :
    IsEdgeTransport (weightedNerveProjection F) (nerve.edgeMk f)
      (weightedNerveCoefficientTransport F f)

noncomputable def weightedNerveTransport_coefficientIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] {c d : C} (f : c ⟶ d) :
    FunctorIso
      ((weightedNerveFiberIso F c).hom ≫
        edgeTransport (weightedNerveProjection F) (nerve.edgeMk f) ≫
          (weightedNerveFiberIso F d).inv)
      (F.map f)

lemma weightedNerveTransport_isQCatEquivalence_iff {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] {c d : C} (f : c ⟶ d) :
    IsQCatEquivalence (edgeTransport (weightedNerveProjection F) (nerve.edgeMk f)) ↔
      IsQCatEquivalence (F.map f)

def relativeFunctorConstFiberHom {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    relativeFunctorSpace p (SSet.const b : A ⟶ B) ⟶ (ihom A).obj (vertexFiber p b)

lemma relativeFunctorConstFiberHom_vertex {A E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) (g : A ⟶ vertexFiber p b) :
    (relativeFunctorConstFiberHom (A := A) p b).app _
      (relativeFunctorVertex p (SSet.const b) (g ≫ vertexFiberι p b) (by
        rw [Category.assoc, vertexFiberι_comp, SSet.comp_const])) = functorVertex g

def relativeExtensionFiberEndpoint {A D C E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b) :
    relativeFunctorExtensionSpace p a i v hv ⟶
      (ihom C).obj (vertexFiber p b)

lemma relativeExtensionFiberEndpoint_vertex {A D C E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W : A ⟶ E) (hW : W ≫ p = a) (hWi : i ≫ W = v)
    (g : C ⟶ vertexFiber p b) (hWj : j ≫ W = g ≫ vertexFiberι p b) :
    (relativeExtensionFiberEndpoint p a i v hv j b hj).app _
      (relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W, hW, hWi⟩) =
        functorVertex g

noncomputable def relativeExtensionFiberEndpoint_witnessIso {A D C E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W W' : A ⟶ E) (hW : W ≫ p = a) (hW' : W' ≫ p = a)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (g g' : C ⟶ vertexFiber p b)
    (hWj : j ≫ W = g ≫ vertexFiberι p b) (hWj' : j ≫ W' = g' ≫ vertexFiberι p b) :
    FunctorIso g g'

noncomputable def leftFibrationTransportNaturalityIso {E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) [LeftFibration q] (f : E ⟶ E') (hf : f ≫ q = p)
    {a b : B _⦋0⦌} (e : SSet.Edge a b)
    {T : vertexFiber p a ⟶ vertexFiber p b} {T' : vertexFiber q a ⟶ vertexFiber q b}
    (hT : IsEdgeTransport p e T) (hT' : IsEdgeTransport q e T') :
    FunctorIso (T ≫ vertexFiberMap p q f hf b) (vertexFiberMap p q f hf a ≫ T')

noncomputable def leftFibrationMap_transportIso {E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p) {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    FunctorIso
      (edgeTransport p e ≫ vertexFiberMap p q f hf b)
      (vertexFiberMap p q f hf a ≫ edgeTransport q e)

lemma leftFibrationMap_transport_isQCatEquivalence_iff {E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p) {a b : B _⦋0⦌} (e : SSet.Edge a b)
    (ha : IsQCatEquivalence (vertexFiberMap p q f hf a))
    (hb : IsQCatEquivalence (vertexFiberMap p q f hf b)) :
    IsQCatEquivalence (edgeTransport p e) ↔ IsQCatEquivalence (edgeTransport q e)

lemma vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) (b : B _⦋0⦌) :
    IsQCatEquivalence (vertexFiberMap p q f hf b)

lemma leftFibration_precompositionEquivalence_iff_fibers
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    IsPrecompositionEquivalence f ↔
      ∀ b : B _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b)

lemma leftFibration_isQCatEquivalence_iff_fibers
    {E F B : SSet.{u}} [Quasicategory E] [Quasicategory F] [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    IsQCatEquivalence f ↔ ∀ b : B _⦋0⦌, IsQCatEquivalence (vertexFiberMap p q f hf b)

noncomputable def weightedNerveComparisonFiber {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C)
    (h : weightedNerve F ⟶ E) (hh : h ≫ q = weightedNerveProjection F) (c : C) :
    F.obj c ⟶ vertexFiber q (nerveVertex c)

noncomputable def weightedNerveComparisonFiber_transportIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q]
    (h : weightedNerve F ⟶ E) (hh : h ≫ q = weightedNerveProjection F)
    {c d : C} (f : c ⟶ d) :
    FunctorIso
      (F.map f ≫ weightedNerveComparisonFiber F q h hh d)
      (weightedNerveComparisonFiber F q h hh c ≫ edgeTransport q (nerve.edgeMk f))

lemma weightedNerveComparisonFiber_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q]
    (h : weightedNerve F ⟶ E) (hh : h ≫ q = weightedNerveProjection F) (c : C)
    (hc : IsQCatEquivalence
      (vertexFiberMap (weightedNerveProjection F) q h hh (nerveVertex c))) :
    IsQCatEquivalence (weightedNerveComparisonFiber F q h hh c)

lemma weightedNerveComparison_transport_isQCatEquivalence_iff
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q]
    (h : weightedNerve F ⟶ E) (hh : h ≫ q = weightedNerveProjection F)
    {c d : C} (f : c ⟶ d)
    (hc : IsQCatEquivalence (weightedNerveComparisonFiber F q h hh c))
    (hd : IsQCatEquivalence (weightedNerveComparisonFiber F q h hh d)) :
    IsQCatEquivalence (edgeTransport q (nerve.edgeMk f)) ↔ IsQCatEquivalence (F.map f)

lemma weightedNerveComparisonFiber_isQCatEquivalence_of_precompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q]
    (h : weightedNerve F ⟶ E) (hh : h ≫ q = weightedNerveProjection F)
    (eh : IsPrecompositionEquivalence h) (c : C) :
    IsQCatEquivalence (weightedNerveComparisonFiber F q h hh c)

lemma weightedNerveComparison_transport_isQCatEquivalence_iff_of_precompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q]
    (h : weightedNerve F ⟶ E) (hh : h ≫ q = weightedNerveProjection F)
    (eh : IsPrecompositionEquivalence h) {c d : C} (f : c ⟶ d) :
    IsQCatEquivalence (edgeTransport q (nerve.edgeMk f)) ↔ IsQCatEquivalence (F.map f)

def uliftVertexFiberMap {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (vertexFiber p b) ⟶
      vertexFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b)

def uliftVertexFiberInverse {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    vertexFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b) ⟶
      (SSet.uliftFunctor.{v, u}).obj (vertexFiber p b)

def uliftVertexFiberIso {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (vertexFiber p b) ≅
      vertexFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b)

lemma uliftVertexFiberIso_hom_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (uliftVertexFiberIso.{u, v} p b).hom ≫
      vertexFiberι ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b) =
        (SSet.uliftFunctor.{v, u}).map (vertexFiberι p b)

lemma uliftVertexFiberIso_inv_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (uliftVertexFiberIso.{u, v} p b).inv ≫
      (SSet.uliftFunctor.{v, u}).map (vertexFiberι p b) =
        vertexFiberι ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b)

lemma uliftVertexFiberIso_naturality {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).map (vertexFiberMap p q f hf b) ≫
      (uliftVertexFiberIso.{u, v} q b).hom =
    (uliftVertexFiberIso.{u, v} p b).hom ≫
      vertexFiberMap ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map q)
        ((SSet.uliftFunctor.{v, u}).map f) (by
          rw [← Functor.map_comp, hf]) (ULift.up b)

def uliftSimplexPrism {A E : SSet.{u}} {n : ℕ} (H : (Δ[n] : SSet.{u}) ⊗ A ⟶ E) :
    (Δ[n] : SSet.{max u v}) ⊗ (SSet.uliftFunctor.{v, u}).obj A ⟶
      (SSet.uliftFunctor.{v, u}).obj E

lemma uliftSimplexPrism_vertex {A E : SSet.{u}} {n : ℕ}
    (H : (Δ[n] : SSet.{u}) ⊗ A ⟶ E) (i : Fin (n + 1)) :
    simplexPrismVertex n i ((SSet.uliftFunctor.{v, u}).obj A) ≫ uliftSimplexPrism.{u, v} H =
      (SSet.uliftFunctor.{v, u}).map (simplexPrismVertex n i A ≫ H)

lemma uliftSimplexPrism_post {A E B : SSet.{u}} {n : ℕ}
    (H : (Δ[n] : SSet.{u}) ⊗ A ⟶ E) (f : E ⟶ B) :
    uliftSimplexPrism.{u, v} H ≫ (SSet.uliftFunctor.{v, u}).map f =
      uliftSimplexPrism.{u, v} (H ≫ f)

lemma uliftSimplexPrism_edgeFamily {A B : SSet.{u}} {a b : B _⦋0⦌}
    (e : SSet.Edge a b) :
    uliftSimplexPrism.{u, v}
      (fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge) =
    fst (Δ[1] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj A) ≫
      SSet.yonedaEquiv.symm (uliftTruncatedEdge.{u, v} e).edge

def uliftFiberTransport {E B : SSet.{u}} (p : E ⟶ B) {a b : B _⦋0⦌}
    (T : vertexFiber p a ⟶ vertexFiber p b) :
    vertexFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up a) ⟶
      vertexFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b)

lemma IsEdgeTransport.ulift {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b : B _⦋0⦌} (e : SSet.Edge a b) {T : vertexFiber p a ⟶ vertexFiber p b}
    (hT : IsEdgeTransport p e T) :
    IsEdgeTransport ((SSet.uliftFunctor.{v, u}).map p) (uliftTruncatedEdge.{u, v} e)
      (uliftFiberTransport.{u, v} p T)

noncomputable def edgeTransport_uliftIso {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    FunctorIso
      (edgeTransport ((SSet.uliftFunctor.{v, u}).map p) (uliftTruncatedEdge.{u, v} e))
      (uliftFiberTransport.{u, v} p (edgeTransport p e))

noncomputable def uliftWeightedNerveFiberIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    (SSet.uliftFunctor.{v, u}).obj (F.obj c) ≅
      vertexFiber ((SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
        (ULift.up (nerveVertex c))

lemma uliftWeightedNerveCoefficientTransport_isTransport
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {c d : C} (f : c ⟶ d) :
    IsEdgeTransport ((SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
      (uliftTruncatedEdge.{u, v} (nerve.edgeMk f))
      ((uliftWeightedNerveFiberIso.{u, v} F c).inv ≫
        (SSet.uliftFunctor.{v, u}).map (F.map f) ≫ (uliftWeightedNerveFiberIso.{u, v} F d).hom)

noncomputable def uliftWeightedNerveTransport_coefficientIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {c d : C} (f : c ⟶ d) :
    FunctorIso
      ((uliftWeightedNerveFiberIso.{u, v} F c).hom ≫
        edgeTransport ((SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
          (uliftTruncatedEdge.{u, v} (nerve.edgeMk f)) ≫
            (uliftWeightedNerveFiberIso.{u, v} F d).inv)
      ((SSet.uliftFunctor.{v, u}).map (F.map f))

noncomputable def uliftWeightedNerveComparisonFiber {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{max u v}}
    (q : E ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve C))
    (h : (SSet.uliftFunctor.{v, u}).obj (weightedNerve F) ⟶ E)
    (hh : h ≫ q = (SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F)) (c : C) :
    (SSet.uliftFunctor.{v, u}).obj (F.obj c) ⟶ vertexFiber q (ULift.up (nerveVertex c))

noncomputable def uliftWeightedNerveComparisonFiber_transportIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{max u v}} (q : E ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve C)) [LeftFibration q]
    (h : (SSet.uliftFunctor.{v, u}).obj (weightedNerve F) ⟶ E)
    (hh : h ≫ q = (SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
    {c d : C} (f : c ⟶ d) :
    FunctorIso
      ((SSet.uliftFunctor.{v, u}).map (F.map f) ≫ uliftWeightedNerveComparisonFiber F q h hh d)
      (uliftWeightedNerveComparisonFiber F q h hh c ≫
        edgeTransport q (uliftTruncatedEdge.{u, v} (nerve.edgeMk f)))

lemma uliftWeightedNerveComparisonFiber_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{max u v}} (q : E ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve C)) [LeftFibration q]
    (h : (SSet.uliftFunctor.{v, u}).obj (weightedNerve F) ⟶ E)
    (hh : h ≫ q = (SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
    (eh : IsPrecompositionEquivalence h) (c : C) :
    IsQCatEquivalence (uliftWeightedNerveComparisonFiber F q h hh c)

lemma uliftWeightedNerveComparison_transport_isQCatEquivalence_iff
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{max u v}} (q : E ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve C)) [LeftFibration q]
    (h : (SSet.uliftFunctor.{v, u}).obj (weightedNerve F) ⟶ E)
    (hh : h ≫ q = (SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
    (eh : IsPrecompositionEquivalence h) {c d : C} (f : c ⟶ d) :
    IsQCatEquivalence (edgeTransport q (uliftTruncatedEdge.{u, v} (nerve.edgeMk f))) ↔
      IsQCatEquivalence ((SSet.uliftFunctor.{v, u}).map (F.map f))

def uliftMorphismDown {X Y : SSet.{u}}
    (f : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y) : X ⟶ Y

lemma uliftMorphismDown_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    uliftMorphismDown ((SSet.uliftFunctor.{v, u}).map f) = f

lemma uliftMorphismDown_comp {X Y Z : SSet.{u}}
    (f : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y)
    (g : (SSet.uliftFunctor.{v, u}).obj Y ⟶ (SSet.uliftFunctor.{v, u}).obj Z) :
    uliftMorphismDown (f ≫ g) = uliftMorphismDown f ≫ uliftMorphismDown g

lemma uliftMorphismDown_id (X : SSet.{u}) :
    uliftMorphismDown (𝟙 ((SSet.uliftFunctor.{v, u}).obj X)) = 𝟙 X

def unliftSimplicialHomotopy {X Y : SSet.{u}}
    {f g : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y}
    (H : SSet.Homotopy f g) : SSet.Homotopy (uliftMorphismDown f) (uliftMorphismDown g)

lemma IsSimplicialHomotopyEquivalence.of_ulift {X Y : SSet.{u}} {f : X ⟶ Y}
    (h : IsSimplicialHomotopyEquivalence ((SSet.uliftFunctor.{v, u}).map f)) :
    IsSimplicialHomotopyEquivalence f

lemma isQCatEquivalence_ulift_iff_of_kan {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) :
    IsQCatEquivalence ((SSet.uliftFunctor.{v, u}).map f) ↔ IsQCatEquivalence f

noncomputable def directKanUnstraighteningFiberComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    (SSet.uliftFunctor.{u + 1, u}).obj (F.obj c).obj ⟶
      vertexFiber (leftUnstraighteningProjection (kanDiagramCoherentNerve F))
        (ULift.up (nerveVertex c))

lemma directKanUnstraighteningFiberComparison_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    IsQCatEquivalence (directKanUnstraighteningFiberComparison F c)

noncomputable def directKanUnstraighteningFiberComparison_transportIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) {c d : C} (f : c ⟶ d) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (F.map f) ≫
        directKanUnstraighteningFiberComparison F d)
      (directKanUnstraighteningFiberComparison F c ≫
        edgeTransport (leftUnstraighteningProjection (kanDiagramCoherentNerve F))
          (uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f)))

lemma directKanUnstraighteningTransport_isQCatEquivalence_iff
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) {c d : C} (f : c ⟶ d) :
    IsQCatEquivalence
      (edgeTransport (leftUnstraighteningProjection (kanDiagramCoherentNerve F))
        (uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f))) ↔
      IsQCatEquivalence (F.map f)

instance leftFibration_pullback_snd {E B C : SSet.{u}} (p : E ⟶ B) (k : C ⟶ B)
    [LeftFibration p] : LeftFibration (pullback.snd p k)

lemma vertexFiberPullbackIso_inv_ι_fst {E B C : SSet.{u}}
    (p : E ⟶ B) (k : C ⟶ B) (a : C _⦋0⦌) :
    (vertexFiberPullbackIso p k a).inv ≫ vertexFiberι (pullback.snd p k) a ≫
      pullback.fst p k = vertexFiberι p (k.app (Opposite.op ⦋0⦌) a)

lemma IsEdgeTransport.pullback {E B C : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : C ⟶ B)
    {a b : C _⦋0⦌} (e : SSet.Edge a b)
    {T : vertexFiber (pullback.snd p k) a ⟶ vertexFiber (pullback.snd p k) b}
    (hT : IsEdgeTransport (pullback.snd p k) e T) :
    IsEdgeTransport p (e.map k)
      ((vertexFiberPullbackIso p k a).inv ≫ T ≫ (vertexFiberPullbackIso p k b).hom)

noncomputable def edgeTransport_pullbackIso {E B C : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : C ⟶ B)
    {a b : C _⦋0⦌} (e : SSet.Edge a b) :
    FunctorIso
      ((vertexFiberPullbackIso p k a).inv ≫ edgeTransport (pullback.snd p k) e ≫
        (vertexFiberPullbackIso p k b).hom)
      (edgeTransport p (e.map k))

lemma edgeTransport_pullback_isQCatEquivalence_iff {E B C : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : C ⟶ B)
    {a b : C _⦋0⦌} (e : SSet.Edge a b) :
    IsQCatEquivalence (edgeTransport (pullback.snd p k) e) ↔
      IsQCatEquivalence (edgeTransport p (e.map k))

noncomputable def kanDiagramUniversalFiberComparison
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    (SSet.uliftFunctor.{u + 1, u}).obj (F.obj c).obj ⟶
      vertexFiber pointedSpaceProjection
        ((kanDiagramCoherentNerve F).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex c)))

lemma kanDiagramUniversalFiberComparison_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    IsQCatEquivalence (kanDiagramUniversalFiberComparison F c)

noncomputable def kanDiagramUniversalFiberComparison_transportIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) {c d : C} (f : c ⟶ d) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (F.map f) ≫ kanDiagramUniversalFiberComparison F d)
      (kanDiagramUniversalFiberComparison F c ≫ edgeTransport pointedSpaceProjection
        (SSet.Edge.map (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C))
          (uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f)) (kanDiagramCoherentNerve F)))

lemma kanDiagramUniversalTransport_isQCatEquivalence_iff
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) {c d : C} (f : c ⟶ d) :
    IsQCatEquivalence (edgeTransport pointedSpaceProjection
      (SSet.Edge.map (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C))
          (uliftTruncatedEdge.{u, u + 1} (nerve.edgeMk f)) (kanDiagramCoherentNerve F))) ↔
      IsQCatEquivalence (F.map f)

lemma kanDiagramCoherentNerve_edge
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) {c d : C} (f : c ⟶ d) :
    (kanDiagramCoherentNerve F).app (Opposite.op ⦋1⦌) (ULift.up (nerve.edgeMk f).edge) =
      (coherentNerveEdge (F.map f)).edge

lemma edgeTransport_isQCatEquivalence_congr_edge {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b a' b' : B _⦋0⦌}
    (e : SSet.Edge a b) (e' : SSet.Edge a' b') (h : e.edge = e'.edge) :
    IsQCatEquivalence (edgeTransport p e) ↔ IsQCatEquivalence (edgeTransport p e')

lemma pointedSpaceTransport_coherentEdge_isQCatEquivalence_iff
    {K L : KanObject.{u}} (f : K ⟶ L) :
    IsQCatEquivalence (edgeTransport pointedSpaceProjection (coherentNerveEdge f)) ↔
      IsQCatEquivalence f

lemma coherentKanEdge_homMk_eq_of_functorIso {K L : KanObject.{u}}
    {f g : K ⟶ L} (h : FunctorIso f g) :
    SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge g).toTruncated

lemma coherentKanEdge_isInvertible_of_isQCatEquivalence {K L : KanObject.{u}}
    {f : K ⟶ L} (hf : IsQCatEquivalence f) : IsInvertibleEdge (coherentNerveEdge f)

lemma pointedSpaceEdge_isInvertible_of_transport_isQCatEquivalence
    {s t : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge s t)
    (he : IsQCatEquivalence (edgeTransport pointedSpaceProjection e)) : IsInvertibleEdge e

lemma leftUnstraighteningMappingEdge_isQCatEquivalence_iff_isInvertibleEdge
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G)) :
    IsQCatEquivalence (leftUnstraighteningMappingVertexMap F G (intervalMappingVertexOfEdge e)).val ↔
      IsInvertibleEdge e

lemma leftUnstraighteningMappingVertexMap_isQCatEquivalence_iff
    {B : SSet.{u + 1}} [Quasicategory B] (F G : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    IsQCatEquivalence (leftUnstraighteningMappingVertexMap F G x).val ↔
      IsInvertibleEdge (intervalMappingEdgeOfVertex x)

lemma coherentHomComparisonSimplex_postcomp
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) {X Y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    (coherentHomComparisonSimplex σ).comp SSet F =
      coherentHomComparisonSimplex ((F.map X Y).app (Opposite.op ⦋n⦌) σ)

lemma pinchedHom_eqToHom_app_val {Z : SSet.{u}} {x y x' y' : Z _⦋0⦌}
    (hx : x = x') (hy : y = y') {n : ℕ} (s : (pinchedHom x y) _⦋n⦌) :
    (((eqToHom (congrArg₂ (fun a b ↦ pinchedHom a b) hx hy)).app (Opposite.op ⦋n⦌)) s).val =
      s.val

noncomputable def coherentPinchedHomMap {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    pinchedHom (coherentNerveVertex X) (coherentNerveVertex Y) ⟶
      pinchedHom (coherentNerveVertex (F.obj X)) (coherentNerveVertex (F.obj Y))

lemma coherentHomComparison_enriched_naturality
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    coherentHomComparison X Y ≫ coherentPinchedHomMap F X Y =
      (SSet.uliftFunctor.{v, u}).map (F.map X Y) ≫ coherentHomComparison (F.obj X) (F.obj Y)

lemma coherentPinchedHomMap_isQCatEquivalence_iff
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    [∀ X Y : D, KanComplex (SimplicialCategory.sHom X Y)]
    (F : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    IsQCatEquivalence (coherentPinchedHomMap F X Y) ↔ IsQCatEquivalence (F.map X Y)

lemma coherentNerveMap_pinchedHomMap_isQCatEquivalence_iff
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    [∀ X Y : D, KanComplex (SimplicialCategory.sHom X Y)]
    (F : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    IsQCatEquivalence (pinchedHomMap (coherentNerveMap F)
      (coherentNerveVertex X) (coherentNerveVertex Y)) ↔ IsQCatEquivalence (F.map X Y)

lemma coherentNerveMap_isFullyFaithful_iff
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    [∀ X Y : D, KanComplex (SimplicialCategory.sHom X Y)]
    (F : EnrichedFunctor SSet.{u} C D) :
    IsFullyFaithful (coherentNerveMap F) ↔ ∀ X Y : C, IsQCatEquivalence (F.map X Y)

def leftFibrationFiberObject {B : SSet.{u}} (b : B _⦋0⦌) (p : LeftFibrationObject B) :
    KanObject.{u}

noncomputable def leftFibrationFiberEvaluationEnriched {B : SSet.{u}} (b : B _⦋0⦌) :
    EnrichedFunctor SSet.{u} (LeftFibrationObject B) KanObject.{u}

noncomputable def leftFibrationInfinityFiberEvaluation {B : SSet.{u}} (b : B _⦋0⦌) :
    LeftFibrationInfinity B ⟶ SpaceInfinity.{u}

lemma leftFibrationInfinityFiberEvaluation_vertex {B : SSet.{u}} (b : B _⦋0⦌)
    (p : LeftFibrationObject B) :
    (leftFibrationInfinityFiberEvaluation b).app (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      coherentNerveVertex (leftFibrationFiberObject b p)

lemma leftFibrationFiberEvaluation_mapping_naturality {B : SSet.{u}} (b : B _⦋0⦌)
    (p q : LeftFibrationObject B) :
    coherentHomComparison p q ≫ coherentPinchedHomMap (leftFibrationFiberEvaluationEnriched b) p q =
      (SSet.uliftFunctor.{u + 1, u}).map (relativeFunctorFiberHom p.val.hom q.val.hom b) ≫
        coherentHomComparison (leftFibrationFiberObject b p) (leftFibrationFiberObject b q)

def vertexFiberSubterminalBaseIso {E B : SSet.{u}}
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (p : E ⟶ B) (b : B _⦋0⦌) :
    vertexFiber p b ≅ E

instance ihom_subsingleton_of_subterminal {A B : SSet.{u}}
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (n : SimplexCategoryᵒᵖ) :
    Subsingleton (((ihom A).obj B).obj n)

def relativeFunctorSubterminalBaseIso {E F B : SSet.{u}}
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)]
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌) :
    relativeFunctorSpace q p ≅ (ihom (vertexFiber p b)).obj (vertexFiber q b)

lemma relativeFunctorSubterminalBaseIso_hom {E F B : SSet.{u}}
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)]
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌) :
    (relativeFunctorSubterminalBaseIso p q b).hom = relativeFunctorFiberHom p q b

instance relativeFunctorFiberHom_isIso_of_subterminal {E F B : SSet.{u}}
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)]
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌) : IsIso (relativeFunctorFiberHom p q b)

lemma leftFibrationInfinityFiberEvaluation_isFullyFaithful_of_subterminal
    {B : SSet.{u}} [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (b : B _⦋0⦌) :
    IsFullyFaithful (leftFibrationInfinityFiberEvaluation b)

instance leftFibration_to_subterminal_of_kan {E B : SSet.{u}} [KanComplex E]
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (p : E ⟶ B) : LeftFibration p

lemma leftFibrationInfinityFiberEvaluation_isEssentiallySurjective_of_subterminal
    {B : SSet.{u}} [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (b : B _⦋0⦌) :
    IsEssentiallySurjective (leftFibrationInfinityFiberEvaluation b)

lemma leftFibrationInfinityFiberEvaluation_isQCatEquivalence_of_subterminal
    {B : SSet.{u}} [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (b : B _⦋0⦌) :
    IsQCatEquivalence (leftFibrationInfinityFiberEvaluation b)

noncomputable def leftFibrationInfinitySubterminalEquivalence
    {B : SSet.{u}} [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (b : B _⦋0⦌) :
    QCatEquivalence (LeftFibrationInfinity B) SpaceInfinity.{u}

noncomputable def leftFibrationInfinityPointEquivalence :
    QCatEquivalence (LeftFibrationInfinity (Δ[0] : SSet.{u})) SpaceInfinity.{u}

def strictDiagramMappingSimplex {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (n : SimplexCategoryᵒᵖ) : Type u

def strictDiagramMappingSimplexMap {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (η : strictDiagramMappingSimplex F G n) : strictDiagramMappingSimplex F G m

def strictDiagramMappingSpace {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) : SSet.{u}

def strictDiagramMappingComponent {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (c : C) :
    strictDiagramMappingSpace F G ⟶ (ihom (F.obj c)).obj (G.obj c)

def leftStrictTransportMappingSpaceMap {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) :
    relativeFunctorSpace q p ⟶
      strictDiagramMappingSpace (leftStrictTransportDiagram p) (leftStrictTransportDiagram q)

def strictDiagramMappingEvaluation {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    F ⋙ tensorRight (strictDiagramMappingSpace F G) ⟶ G

def simplicialReplacementTensorMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (T : SSet.{u}) :
    simplicialReplacement F ⊗ T ⟶ simplicialReplacement (F ⋙ tensorRight T)

lemma simplicialReplacementTensorMap_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (T : SSet.{u}) :
    simplicialReplacementTensorMap F T ≫ simplicialReplacementProjection (F ⋙ tensorRight T) =
      fst (simplicialReplacement F) T ≫ simplicialReplacementProjection F

def strictDiagramMappingReplacementEvaluation {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    simplicialReplacement F ⊗ strictDiagramMappingSpace F G ⟶ simplicialReplacement G

lemma strictDiagramMappingReplacementEvaluation_projection
    {C : Type u} [Category.{u} C] (F G : C ⥤ SSet.{u}) :
    strictDiagramMappingReplacementEvaluation F G ≫ simplicialReplacementProjection G =
      fst (simplicialReplacement F) (strictDiagramMappingSpace F G) ≫
        simplicialReplacementProjection F

def strictDiagramMappingScaffoldMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    strictDiagramMappingSpace F (leftStrictTransportDiagram q) ⟶
      relativeFunctorSpace q (simplicialReplacementProjection F)

lemma leftStrictTransportMappingSpaceMap_scaffold
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) :
    leftStrictTransportMappingSpaceMap p q ≫
        strictDiagramMappingScaffoldMap (leftStrictTransportDiagram p) q =
      relativeFunctorOverPre q (Over.homMk
        (U := Over.mk (simplicialReplacementProjection (leftStrictTransportDiagram p)))
        (V := Over.mk p) (universalScaffold p) (universalScaffold_projection p))

noncomputable def leftStrictTransportScaffoldRestrictionEquivalence
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence (relativeFunctorSpace q p)
      (relativeFunctorSpace q (simplicialReplacementProjection (leftStrictTransportDiagram p)))

noncomputable def leftStrictTransportMappingRetraction
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    strictDiagramMappingSpace (leftStrictTransportDiagram p) (leftStrictTransportDiagram q) ⟶
      relativeFunctorSpace q p

noncomputable def leftStrictTransportMappingRetraction_unitIso
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    FunctorIso (leftStrictTransportMappingSpaceMap p q ≫ leftStrictTransportMappingRetraction p q)
      (𝟙 (relativeFunctorSpace q p))

def simplicialReplacementUnderEvaluation {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : nerve (Under c) ⊗ F.obj c ⟶ simplicialReplacement F

lemma simplicialReplacementUnderEvaluation_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    simplicialReplacementUnderEvaluation F c ≫ simplicialReplacementProjection F =
      fst (nerve (Under c)) (F.obj c) ≫ nerveMap (Under.forget c)

lemma simplicialReplacementUnderEvaluation_naturality
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    (nerveUnderMap f ▷ F.obj c) ≫ simplicialReplacementUnderEvaluation F c =
      (nerve (Under d) ◁ F.map f) ≫ simplicialReplacementUnderEvaluation F d

lemma simplicialReplacementUnderEvaluation_scaffold {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C n) (x : (F.obj (σ.obj 0)) _⦋n⦌) :
    (simplicialReplacementUnderEvaluation F (σ.obj 0)).app (Opposite.op ⦋n⦌)
      (scaffoldUnderChain σ, x) = ⟨σ, SSet.yonedaEquiv.symm x⟩

lemma scaffoldUnderChain_forget_factorization {C : Type u} [Category.{u} C]
    {c : C} {n : ℕ} (τ : ComposableArrows (Under c) n) :
    scaffoldUnderChain (τ ⋙ Under.forget c) ⋙ Under.map (τ.obj 0).hom = τ

def strictDiagramScaffoldInverseComponent {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) (c : C) :
    relativeFunctorSpace q (simplicialReplacementProjection F) ⟶
      (ihom (F.obj c)).obj (leftStrictTransport q c)

lemma sSetInternalHom_pre_app {A D E : SSet.{u}} (i : D ⟶ A)
    (n k : SimplexCategoryᵒᵖ) (s : ((ihom A).obj E).obj n) (α : n ⟶ k) (d : D.obj k) :
    ((((pre i).app E).app n s).app k α d) = s.app k α (i.app k d)

lemma strictDiagramScaffoldInverseComponent_app {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) (c : C)
    (n k l : SimplexCategoryᵒᵖ)
    (x : (relativeFunctorSpace q (simplicialReplacementProjection F)).obj n)
    (α : n ⟶ k) (y : (F.obj c).obj k) (β : k ⟶ l) (τ : (nerve (Under c)).obj l) :
    ((((strictDiagramScaffoldInverseComponent F q c).app n x).app k α y).val.app l β τ) =
      x.val.app l (α ≫ β) ((simplicialReplacementUnderEvaluation F c).app l
        (τ, (F.obj c).map β y))

def strictDiagramMappingScaffoldInverse {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    relativeFunctorSpace q (simplicialReplacementProjection F) ⟶
      strictDiagramMappingSpace F (leftStrictTransportDiagram q)

lemma strictDiagramMappingScaffoldMap_app {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) {n k : ℕ}
    (η : (strictDiagramMappingSpace F (leftStrictTransportDiagram q)) _⦋n⦌)
    (α : Opposite.op ⦋n⦌ ⟶ Opposite.op ⦋k⦌) (s : simplicialReplacementSimplex F k) :
    (((strictDiagramMappingScaffoldMap F q).app (Opposite.op ⦋n⦌) η).val.app
      (Opposite.op ⦋k⦌) α s) =
      ((η.val (s.1.obj 0)).app (Opposite.op ⦋k⦌) α (SSet.yonedaEquiv s.2)).val.app
        (Opposite.op ⦋k⦌) (𝟙 _) (scaffoldUnderChain s.1)

lemma strictDiagramMappingScaffoldInverse_map {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    strictDiagramMappingScaffoldInverse F q ≫ strictDiagramMappingScaffoldMap F q =
      𝟙 (relativeFunctorSpace q (simplicialReplacementProjection F))

lemma strictDiagramMappingScaffoldMap_inverse {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    strictDiagramMappingScaffoldMap F q ≫ strictDiagramMappingScaffoldInverse F q =
      𝟙 (strictDiagramMappingSpace F (leftStrictTransportDiagram q))

def strictDiagramMappingScaffoldIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    strictDiagramMappingSpace F (leftStrictTransportDiagram q) ≅
      relativeFunctorSpace q (simplicialReplacementProjection F)

instance strictDiagramMappingSpace_leftStrictTransport_kanComplex
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {E : SSet.{u}}
    (q : E ⟶ nerve C) [LeftFibration q] :
    KanComplex (strictDiagramMappingSpace F (leftStrictTransportDiagram q))

lemma strictDiagramMappingScaffoldMap_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {E : SSet.{u}}
    (q : E ⟶ nerve C) [LeftFibration q] :
    IsQCatEquivalence (strictDiagramMappingScaffoldMap F q)

lemma leftStrictTransportMappingSpaceMap_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    IsQCatEquivalence (leftStrictTransportMappingSpaceMap p q)

noncomputable def leftStrictTransportMappingEquivalence
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence (relativeFunctorSpace q p)
      (strictDiagramMappingSpace (leftStrictTransportDiagram p) (leftStrictTransportDiagram q))

def strictDiagramMappingIdentity {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    𝟙_ SSet.{u} ⟶ strictDiagramMappingSpace F F

def strictDiagramMappingComposition {C : Type u} [Category.{u} C]
    (F G H : C ⥤ SSet.{u}) :
    strictDiagramMappingSpace F G ⊗ strictDiagramMappingSpace G H ⟶
      strictDiagramMappingSpace F H

lemma strictDiagramMappingIdentity_comp {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    (λ_ (strictDiagramMappingSpace F G)).inv ≫ strictDiagramMappingIdentity F ▷ _ ≫
      strictDiagramMappingComposition F F G = 𝟙 _

lemma strictDiagramMappingComposition_id {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    (ρ_ (strictDiagramMappingSpace F G)).inv ≫ _ ◁ strictDiagramMappingIdentity G ≫
      strictDiagramMappingComposition F G G = 𝟙 _

lemma strictDiagramMappingComposition_assoc {C : Type u} [Category.{u} C]
    (F G H I : C ⥤ SSet.{u}) :
    (α_ (strictDiagramMappingSpace F G) (strictDiagramMappingSpace G H)
      (strictDiagramMappingSpace H I)).inv ≫ strictDiagramMappingComposition F G H ▷ _ ≫
        strictDiagramMappingComposition F H I =
      _ ◁ strictDiagramMappingComposition G H I ≫ strictDiagramMappingComposition F G I

lemma strictDiagramMappingHom_ext {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} {A : SSet.{u}} {f g : A ⟶ strictDiagramMappingSpace F G}
    (h : ∀ c, f ≫ strictDiagramMappingComponent F G c =
      g ≫ strictDiagramMappingComponent F G c) : f = g

lemma strictDiagramMappingIdentity_component {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    strictDiagramMappingIdentity F ≫ strictDiagramMappingComponent F F c =
      MonoidalClosed.id (F.obj c)

lemma strictDiagramMappingComposition_component {C : Type u} [Category.{u} C]
    (F G H : C ⥤ SSet.{u}) (c : C) :
    strictDiagramMappingComposition F G H ≫ strictDiagramMappingComponent F H c =
      (strictDiagramMappingComponent F G c ⊗ₘ strictDiagramMappingComponent G H c) ≫
        MonoidalClosed.comp (F.obj c) (G.obj c) (H.obj c)

def StrictTransportDiagramObject (C : Type u) [Category.{u} C]

instance strictTransportDiagramObject_enrichedCategory (C : Type u) [Category.{u} C] :
    EnrichedCategory SSet.{u} (StrictTransportDiagramObject C)

instance strictTransportDiagramObject_category (C : Type u) [Category.{u} C] :
    Category.{u} (StrictTransportDiagramObject C)

instance strictTransportDiagramObject_simplicialCategory (C : Type u) [Category.{u} C] :
    SimplicialCategory (StrictTransportDiagramObject C)

instance strictTransportDiagramObject_sHom_kanComplex
    {C : Type u} [Category.{u} C] (F G : StrictTransportDiagramObject C) :
    KanComplex (SimplicialCategory.sHom F G)

noncomputable def StrictTransportDiagramInfinity (C : Type u) [Category.{u} C] : SSet.{u + 1}

instance strictTransportDiagramInfinity_quasicategory (C : Type u) [Category.{u} C] :
    Quasicategory (StrictTransportDiagramInfinity C)

def leftStrictTransportImageObject {C : Type u} [Category.{u} C]
    (p : LeftFibrationObject (nerve C)) : StrictTransportDiagramObject C

lemma leftStrictTransportMappingSpaceMap_component
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) (c : C) :
    leftStrictTransportMappingSpaceMap p q ≫ strictDiagramMappingComponent
      (leftStrictTransportDiagram p) (leftStrictTransportDiagram q) c =
      relativeFunctorPostHom (Over.mk (nerveMap (Under.forget c))) (Over.mk p) (Over.mk q)

def leftStrictTransportEnriched {C : Type u} [Category.{u} C] :
    EnrichedFunctor SSet.{u} (LeftFibrationObject (nerve C)) (StrictTransportDiagramObject C)

noncomputable def leftStrictTransportInfinityMap (C : Type u) [Category.{u} C] :
    LeftFibrationInfinity (nerve C) ⟶ StrictTransportDiagramInfinity C

lemma leftStrictTransportInfinityMap_isFullyFaithful (C : Type u) [Category.{u} C] :
    IsFullyFaithful (leftStrictTransportInfinityMap C)

lemma leftStrictTransportInfinityMap_vertex {C : Type u} [Category.{u} C]
    (p : LeftFibrationObject (nerve C)) :
    (leftStrictTransportInfinityMap C).app (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      coherentNerveVertex (leftStrictTransportImageObject p)

lemma leftStrictTransportInfinityMap_isEssentiallySurjective (C : Type u) [Category.{u} C] :
    IsEssentiallySurjective (leftStrictTransportInfinityMap C)

lemma leftStrictTransportInfinityMap_isQCatEquivalence (C : Type u) [Category.{u} C] :
    IsQCatEquivalence (leftStrictTransportInfinityMap C)

noncomputable def leftStrictTransportInfinityEquivalence (C : Type u) [Category.{u} C] :
    QCatEquivalence (LeftFibrationInfinity (nerve C)) (StrictTransportDiagramInfinity C)

def strictTransportDiagramEvaluationEnriched {C : Type u} [Category.{u} C] (c : C) :
    EnrichedFunctor SSet.{u} (StrictTransportDiagramObject C) KanObject.{u}

noncomputable def strictTransportDiagramInfinityEvaluation {C : Type u} [Category.{u} C] (c : C) :
    StrictTransportDiagramInfinity C ⟶ SpaceInfinity.{u}

lemma leftStrictTransportEnriched_evaluate {C : Type u} [Category.{u} C] (c : C) :
    (leftStrictTransportEnriched (C := C)).comp SSet (strictTransportDiagramEvaluationEnriched c) =
      relativeFunctorEnrichedEvaluation (Over.mk (nerveMap (Under.forget c)))

lemma leftStrictTransportInfinityMap_evaluate {C : Type u} [Category.{u} C] (c : C) :
    leftStrictTransportInfinityMap C ≫ strictTransportDiagramInfinityEvaluation c =
      leftStrictTransportCoherentEvaluation c

lemma leftStrictTransportInfinityMap_evaluate_straightening
    {C : Type u} [Category.{u} C] (c : C) :
    leftStrictTransportInfinityMap C ≫ strictTransportDiagramInfinityEvaluation c =
      leftStraighteningCoherentMap C ≫ evaluateFunctorAt (ULift.up (nerveVertex c))

def strictDiagramMixedHom {C : Type u} [Category.{u} C] {c d : C}
    (f : c ⟶ d) (F G : C ⥤ SSet.{u}) :
    strictDiagramMappingSpace F G ⟶ (ihom (F.obj c)).obj (G.obj d)

lemma strictDiagramMixedHom_id {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    strictDiagramMappingIdentity F ≫ strictDiagramMixedHom (𝟙 c) F F =
      MonoidalClosed.id (F.obj c)

lemma strictDiagramMixedHom_comp {C : Type u} [Category.{u} C] {c d e : C}
    (f : c ⟶ d) (g : d ⟶ e) (F G H : C ⥤ SSet.{u}) :
    strictDiagramMappingComposition F G H ≫ strictDiagramMixedHom (f ≫ g) F H =
      (strictDiagramMixedHom f F G ⊗ₘ strictDiagramMixedHom g G H) ≫
        MonoidalClosed.comp (F.obj c) (G.obj d) (H.obj e)

def diagonalStrictDiagramObject {C : Type u} [Category.{u} C] {J : Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (StrictTransportDiagramObject C))
    (i : SimplicialThickening J) : KanObject.{u}

noncomputable def diagonalStrictDiagramHom {C : Type u} [Category.{u} C] {J : Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (StrictTransportDiagramObject C))
    (i j : SimplicialThickening J) :
    SimplicialCategory.sHom i j ⟶
      SimplicialCategory.sHom (diagonalStrictDiagramObject A F i) (diagonalStrictDiagramObject A F j)

lemma diagonalStrictDiagramHom_of_le {C : Type u} [Category.{u} C] {J : Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (StrictTransportDiagramObject C))
    (i j : SimplicialThickening J) (h : i.as ≤ j.as) :
    diagonalStrictDiagramHom A F i j =
      F.map i j ≫ strictDiagramMixedHom (A.map (homOfLE h))
      ((F.obj i).val ⋙ kanObjectForget) ((F.obj j).val ⋙ kanObjectForget)

noncomputable def diagonalStrictDiagramEvaluation {C : Type u} [Category.{u} C] {J : Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (StrictTransportDiagramObject C)) :
    EnrichedFunctor SSet.{u} (SimplicialThickening J) KanObject.{u}

lemma diagonalStrictDiagramEvaluation_reindex {C : Type u} [Category.{u} C] {J K : Type u}
    [LinearOrder J] [LinearOrder K] (α : J →o K) (A : K ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening K) (StrictTransportDiagramObject C)) :
    (SimplicialThickening.functor α).comp SSet (diagonalStrictDiagramEvaluation A F) =
      diagonalStrictDiagramEvaluation (α.toFunctor ⋙ A)
        ((SimplicialThickening.functor α).comp SSet F)

def strictDiagramSimplexBase {C : Type u} [Category.{u} C] {n : ℕ}
    (σ : (nerve C) _⦋n⦌) : ULift.{u} (Fin (n + 1)) ⥤ C

noncomputable def strictDiagramDiagonalSimplex
    {C : Type u} [Category.{u} C] {n : ℕ} (σ : (nerve C) _⦋n⦌)
    (F : (StrictTransportDiagramInfinity C) _⦋n⦌) : SpaceInfinity.{u} _⦋n⦌

lemma strictDiagramDiagonalSimplex_naturality
    {C : Type u} [Category.{u} C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (nerve C) _⦋n⦌) (F : (StrictTransportDiagramInfinity C) _⦋n⦌) :
    SpaceInfinity.map α.op (strictDiagramDiagonalSimplex σ F) =
      strictDiagramDiagonalSimplex ((nerve C).map α.op σ)
        ((StrictTransportDiagramInfinity C).map α.op F)

noncomputable def strictDiagramJointEvaluation (C : Type u) [Category.{u} C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⊗ StrictTransportDiagramInfinity C ⟶
      SpaceInfinity.{u}

noncomputable def strictTransportDiagramRealization (C : Type u) [Category.{u} C] :
    StrictTransportDiagramInfinity C ⟶
      SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))

lemma diagonalStrictDiagramEvaluation_transport
    {C J : Type u} [Category.{u} C] [LinearOrder J] (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J)
      (LeftFibrationObject (nerve C))) :
    diagonalStrictDiagramEvaluation A (F.comp SSet leftStrictTransportEnriched) =
      diagonalRelativeEvaluation (A.op ⋙ underNerveDiagram C) F

lemma strictDiagramJointEvaluation_transport (C : Type u) [Category.{u} C] :
    (𝟙 _ ⊗ₘ leftStrictTransportInfinityMap C) ≫ strictDiagramJointEvaluation C =
      strictTransportJointEvaluation C

lemma leftStrictTransportInfinityMap_realization (C : Type u) [Category.{u} C] :
    leftStrictTransportInfinityMap C ≫ strictTransportDiagramRealization C =
      leftStraighteningCoherentMap C

lemma strictDiagramMixedHom_base_id {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (c : C) :
    strictDiagramMixedHom (𝟙 c) F G = strictDiagramMappingComponent F G c

lemma diagonalStrictDiagramEvaluation_constant_base
    {C J : Type u} [Category.{u} C] [LinearOrder J] (c : C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J)
      (StrictTransportDiagramObject C)) :
    diagonalStrictDiagramEvaluation ((Functor.const J).obj c) F =
      F.comp SSet (strictTransportDiagramEvaluationEnriched c)

lemma strictTransportDiagramRealization_evaluate
    {C : Type u} [Category.{u} C] (c : C) :
    strictTransportDiagramRealization C ≫ evaluateFunctorAt (ULift.up (nerveVertex c)) =
      strictTransportDiagramInfinityEvaluation c

lemma strictTransportDiagramRealization_vertex
    {C : Type u} [Category.{u} C] (F : StrictTransportDiagramObject C) :
    (strictTransportDiagramRealization C).app (Opposite.op ⦋0⦌) (coherentNerveVertex F) =
      functorVertex (kanDiagramCoherentNerve F.val)

lemma simplicialReplacementMap_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {F G : C ⥤ SSet.{u}}
    [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) (hη : ∀ c, IsQCatEquivalence (η.app c)) :
    IsPrecompositionEquivalence (simplicialReplacementMap η)

def strictDiagramMappingPre {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) (H : C ⥤ SSet.{u}) :
    strictDiagramMappingSpace G H ⟶ strictDiagramMappingSpace F H

lemma strictDiagramMappingPre_scaffold {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) {E : SSet.{u}} (q : E ⟶ nerve C) :
    strictDiagramMappingPre η (leftStrictTransportDiagram q) ≫
      strictDiagramMappingScaffoldMap F q =
    strictDiagramMappingScaffoldMap G q ≫ relativeFunctorOverPre q
      (Over.homMk (U := Over.mk (simplicialReplacementProjection F))
        (V := Over.mk (simplicialReplacementProjection G))
        (simplicialReplacementMap η) (simplicialReplacementMap_projection η))

lemma strictDiagramMappingPre_isQCatEquivalence {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) (hη : ∀ c, IsQCatEquivalence (η.app c))
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q] :
    IsQCatEquivalence (strictDiagramMappingPre η (leftStrictTransportDiagram q))

def strictDiagramMappingVertex {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) : (strictDiagramMappingSpace F G) _⦋0⦌

lemma exists_strictDiagramMappingVertex {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (v : (strictDiagramMappingSpace F G) _⦋0⦌) :
    ∃ η : F ⟶ G, strictDiagramMappingVertex η = v

lemma strictDiagramMappingPre_vertex {C : Type u} [Category.{u} C]
    {F G H : C ⥤ SSet.{u}} (η : F ⟶ G) (θ : G ⟶ H) :
    (strictDiagramMappingPre η H).app _ (strictDiagramMappingVertex θ) =
      strictDiagramMappingVertex (η ≫ θ)

def strictDiagramMappingPost {C : Type u} [Category.{u} C]
    {G H : C ⥤ SSet.{u}} (η : G ⟶ H) (F : C ⥤ SSet.{u}) :
    strictDiagramMappingSpace F G ⟶ strictDiagramMappingSpace F H

lemma strictDiagramMappingPost_vertex {C : Type u} [Category.{u} C]
    {F G H : C ⥤ SSet.{u}} (η : G ⟶ H) (θ : F ⟶ G) :
    (strictDiagramMappingPost η F).app _ (strictDiagramMappingVertex θ) =
      strictDiagramMappingVertex (θ ≫ η)

lemma exists_strictTransportInverse {C : Type u} [Category.{u} C]
    {E E' : SSet.{u}} (p : E ⟶ nerve C) (q : E' ⟶ nerve C)
    [LeftFibration p] [LeftFibration q]
    (η : leftStrictTransportDiagram p ⟶ leftStrictTransportDiagram q)
    (hη : ∀ c, IsQCatEquivalence (η.app c)) :
    ∃ θ : leftStrictTransportDiagram q ⟶ leftStrictTransportDiagram p,
      Nonempty (VertexIso (strictDiagramMappingVertex (η ≫ θ))
        (strictDiagramMappingVertex (𝟙 (leftStrictTransportDiagram p)))) ∧
      Nonempty (VertexIso (strictDiagramMappingVertex (θ ≫ η))
        (strictDiagramMappingVertex (𝟙 (leftStrictTransportDiagram q))))

lemma exists_strictTransportImageInverse {C : Type u} [Category.{u} C]
    (F G : StrictTransportDiagramObject C)
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (hη : ∀ c, IsQCatEquivalence (X := (F.val.obj c).obj)
      (Y := (G.val.obj c).obj) (η.app c)) :
    ∃ θ : G.val ⋙ kanObjectForget ⟶ F.val ⋙ kanObjectForget,
      Nonempty (VertexIso (strictDiagramMappingVertex (η ≫ θ))
        (strictDiagramMappingVertex (𝟙 (F.val ⋙ kanObjectForget)))) ∧
      Nonempty (VertexIso (strictDiagramMappingVertex (θ ≫ η))
        (strictDiagramMappingVertex (𝟙 (G.val ⋙ kanObjectForget))))

lemma coherentNerveEdge_homMk_eq_of_enrichedVertexIso
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    {X Y : C} {f g : X ⟶ Y}
    (h : VertexIso (SimplicialCategory.homEquiv' X Y f)
      (SimplicialCategory.homEquiv' X Y g)) :
    SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge g).toTruncated

lemma coherentNerveEdge_isInvertible_of_enrichedInverse
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
    (hu : VertexIso (SimplicialCategory.homEquiv' X X (f ≫ g))
      (SimplicialCategory.homEquiv' X X (𝟙 X)))
    (hc : VertexIso (SimplicialCategory.homEquiv' Y Y (g ≫ f))
      (SimplicialCategory.homEquiv' Y Y (𝟙 Y))) :
    IsInvertibleEdge (coherentNerveEdge f)

def strictTransportImageHom {C : Type u} [Category.{u} C]
    {F G : StrictTransportDiagramObject C}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) : F ⟶ G

lemma strictTransportImageHom_vertex {C : Type u} [Category.{u} C]
    {F G : StrictTransportDiagramObject C}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    SimplicialCategory.homEquiv' F G (strictTransportImageHom η) =
      strictDiagramMappingVertex η

lemma strictTransportImageHom_comp {C : Type u} [Category.{u} C]
    {F G H : StrictTransportDiagramObject C}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (θ : G.val ⋙ kanObjectForget ⟶ H.val ⋙ kanObjectForget) :
    strictTransportImageHom (η ≫ θ) = strictTransportImageHom η ≫ strictTransportImageHom θ

lemma strictTransportImageHom_id {C : Type u} [Category.{u} C]
    (F : StrictTransportDiagramObject C) :
    strictTransportImageHom (𝟙 (F.val ⋙ kanObjectForget)) = 𝟙 F

lemma strictTransportImageHom_isInvertible_of_pointwise
    {C : Type u} [Category.{u} C] {F G : StrictTransportDiagramObject C}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (hη : ∀ c, IsQCatEquivalence (X := (F.val.obj c).obj)
      (Y := (G.val.obj c).obj) (η.app c)) :
    IsInvertibleEdge (coherentNerveEdge (strictTransportImageHom η))

def enrichedFunctorFixedObjectCode {A : Type v} {D : Type w}
    [EnrichedCategory SSet.{u} A] [EnrichedCategory SSet.{u} D] (obj : A → D)
    (F : {F : EnrichedFunctor SSet.{u} A D // F.obj = obj}) :
    ∀ i j : A, (i ⟶[SSet.{u}] j) ⟶ (obj i ⟶[SSet.{u}] obj j)

lemma enrichedFunctorFixedObjectCode_injective {A : Type v} {D : Type w}
    [EnrichedCategory SSet.{u} A] [EnrichedCategory SSet.{u} D] (obj : A → D) :
    Function.Injective (enrichedFunctorFixedObjectCode obj)

instance enrichedFunctor_fixedObjects_small {A : Type v} {D : Type w}
    [Small.{u} A] [EnrichedCategory SSet.{u} A] [EnrichedCategory SSet.{u} D]
    (obj : A → D) : Small.{u} {F : EnrichedFunctor SSet.{u} A D // F.obj = obj}

lemma coherentMap_simplex_obj {D : Type v} [Category.{u} D] [SimplicialCategory D]
    {X : SSet.{max u v}} (f : X ⟶ SimplicialNerve D)
    {n : SimplexCategoryᵒᵖ} (s : X.obj n)
    (i : SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1)))) :
    (f.app n s).obj i = coherentNerveObject
      (f.app (Opposite.op ⦋0⦌)
        (X.map (SimplexCategory.const ⦋0⦌ n.unop i.as.down).op s))

def coherentMapFixedVertexCode {D : Type v} [Category.{u} D] [SimplicialCategory D]
    {X : SSet.{max u v}} (obj : X _⦋0⦌ → D)
    (f : {f : X ⟶ SimplicialNerve D //
      ∀ x, coherentNerveObject (f.app (Opposite.op ⦋0⦌) x) = obj x}) :
    ∀ (n : SimplexCategoryᵒᵖ) (s : X.obj n),
      {F : EnrichedFunctor SSet.{u}
        (SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1)))) D //
        F.obj = fun i ↦ obj (X.map
          (SimplexCategory.const ⦋0⦌ n.unop i.as.down).op s)}

lemma coherentMapFixedVertexCode_injective
    {D : Type v} [Category.{u} D] [SimplicialCategory D]
    {X : SSet.{max u v}} (obj : X _⦋0⦌ → D) :
    Function.Injective (coherentMapFixedVertexCode obj)

instance coherentMap_fixedVertices_small
    {D : Type v} [Category.{u} D] [SimplicialCategory D]
    {X : SSet.{max u v}} [∀ n, Small.{u} (X.obj n)] (obj : X _⦋0⦌ → D) :
    Small.{u} {f : X ⟶ SimplicialNerve D //
      ∀ x, coherentNerveObject (f.app (Opposite.op ⦋0⦌) x) = obj x}

lemma coherentMap_fixedRestrictions_small
    {D : Type v} [Category.{u} D] [SimplicialCategory D]
    {A B X : SSet.{max u v}} [∀ n, Small.{u} (X.obj n)]
    (j : A ⟶ X) (k : B ⟶ X) (a : A ⟶ SimplicialNerve D) (b : B ⟶ SimplicialNerve D)
    (hcover : ∀ x : X _⦋0⦌,
      (∃ y, j.app (Opposite.op ⦋0⦌) y = x) ∨
        (∃ z, k.app (Opposite.op ⦋0⦌) z = x)) :
    Small.{u} {f : X ⟶ SimplicialNerve D // j ≫ f = a ∧ k ≫ f = b}

instance join_augObj_small (K : SSet.{v}) [∀ n, Small.{u} (K.obj n)] (r : ℕ) :
    Small.{u} (Join.augObj K r)

instance join_obj_small (K L : SSet.{v})
    [∀ n, Small.{u} (K.obj n)] [∀ n, Small.{u} (L.obj n)] (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((join K L).obj n)

lemma join_vertices_covered (K L : SSet.{v}) (x : (join K L) _⦋0⦌) :
    (∃ y, (joinInl K L).app (Opposite.op ⦋0⦌) y = x) ∨
      (∃ z, (joinInr K L).app (Opposite.op ⦋0⦌) z = x)

lemma pointedSpaceProjection_simplexFiber_small (n : SimplexCategoryᵒᵖ)
    (s : SpaceInfinity.{u}.obj n) :
    Small.{u} {t : PointedSpaceInfinity.{u}.obj n // pointedSpaceProjection.app n t = s}

lemma pullback_simplex_small_of_fibers {X Y B : SSet.{v}}
    (p : X ⟶ B) (q : Y ⟶ B) (n : ℕ) [Small.{u} (Y _⦋n⦌)]
    (hf : ∀ y : Y _⦋n⦌,
      Small.{u} {x : X _⦋n⦌ // p.app _ x = q.app _ y}) :
    Small.{u} ((pullback p q) _⦋n⦌)

instance leftUnstraightening_obj_small {B : SSet.{u + 1}}
    [∀ n, Small.{u} (B.obj n)] (F : B ⟶ SpaceInfinity.{u}) (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((leftUnstraightening F).obj n)

noncomputable def smallSimplicialSet (X : SSet.{max u v})
    [∀ n, Small.{u} (X.obj n)] : SSet.{u}

noncomputable def smallSimplicialSetIso (X : SSet.{max u v})
    [∀ n, Small.{u} (X.obj n)] :
    (SSet.uliftFunctor.{v, u}).obj (smallSimplicialSet X) ≅ X

def uliftSimplexHomUp {X : SSet.{u}} {n : ℕ} (f : (Δ[n] : SSet.{u}) ⟶ X) :
    (Δ[n] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X

lemma uliftSimplexHomDown_up {X : SSet.{u}} {n : ℕ} (f : (Δ[n] : SSet.{u}) ⟶ X) :
    uliftSimplexHomDown (uliftSimplexHomUp.{u, v} f) = f

lemma uliftSimplexHomUp_face {X : SSet.{u}} {n : ℕ} (f : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ uliftSimplexHomUp.{u, v} f = uliftSimplexHomUp (stdSimplex.δ j ≫ f)

lemma uliftSimplexHomUp_post {X Y : SSet.{u}} (p : X ⟶ Y) {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ X) :
    uliftSimplexHomUp.{u, v} f ≫ (SSet.uliftFunctor.{v, u}).map p =
      uliftSimplexHomUp (f ≫ p)

lemma hasLiftingProperty_horn_of_ulift {E B : SSet.{u}} (p : E ⟶ B)
    (n : ℕ) (i : Fin (n + 2))
    [HasLiftingProperty (horn.{max u v} (n + 1) i).ι ((SSet.uliftFunctor.{v, u}).map p)] :
    HasLiftingProperty (horn.{u} (n + 1) i).ι p

lemma leftFibration_of_ulift {E B : SSet.{u}} (p : E ⟶ B)
    [LeftFibration ((SSet.uliftFunctor.{v, u}).map p)] : LeftFibration p

noncomputable def smallSimplicialProjection {X : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] {B : SSet.{u}}
    (p : X ⟶ (SSet.uliftFunctor.{v, u}).obj B) : smallSimplicialSet X ⟶ B

lemma smallSimplicialProjection_ulift {X : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] {B : SSet.{u}}
    (p : X ⟶ (SSet.uliftFunctor.{v, u}).obj B) :
    (SSet.uliftFunctor.{v, u}).map (smallSimplicialProjection p) =
      (smallSimplicialSetIso X).hom ≫ p

instance smallSimplicialProjection_leftFibration {X : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] {B : SSet.{u}}
    (p : X ⟶ (SSet.uliftFunctor.{v, u}).obj B) [LeftFibration p] :
    LeftFibration (smallSimplicialProjection p)

instance leftUnstraightening_uliftBase_obj_small {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((leftUnstraightening F).obj n)

noncomputable def smallLeftUnstraightening {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) : SSet.{u}

noncomputable def smallLeftUnstraighteningIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening F) ≅ leftUnstraightening F

noncomputable def smallLeftUnstraighteningProjection {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    smallLeftUnstraightening F ⟶ B

lemma smallLeftUnstraighteningIso_projection {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (smallLeftUnstraighteningIso F).hom ≫ leftUnstraighteningProjection F =
      (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection F)

instance smallLeftUnstraighteningProjection_leftFibration {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    LeftFibration (smallLeftUnstraighteningProjection F)

noncomputable def smallLeftUnstraighteningObject {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) : LeftFibrationObject B

def vertexFiberTotalIso {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (e : E ≅ F) (he : e.hom ≫ q = p) (b : B _⦋0⦌) : vertexFiber p b ≅ vertexFiber q b

lemma uliftMorphismDown_lift {X Y : SSet.{u}}
    (f : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y) :
    (SSet.uliftFunctor.{v, u}).map (uliftMorphismDown f) = f

noncomputable def QCatEquivalence.downOfKan {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (e : QCatEquivalence ((SSet.uliftFunctor.{v, u}).obj X)
      ((SSet.uliftFunctor.{v, u}).obj Y)) : QCatEquivalence X Y

noncomputable def smallLeftUnstraighteningFiberIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : B _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (vertexFiber (smallLeftUnstraighteningProjection F) c) ≅
      vertexFiber (leftUnstraighteningProjection F) (ULift.up c)

noncomputable def smallLeftUnstraighteningLiftedFiberValueEquivalence {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : B _⦋0⦌) :
    QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj
      (vertexFiber (smallLeftUnstraighteningProjection F) c))
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up c))).obj)

noncomputable def smallLeftUnstraighteningFiberValueEquivalence {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : B _⦋0⦌) :
    QCatEquivalence (vertexFiber (smallLeftUnstraighteningProjection F) c)
      (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up c))).obj

noncomputable def smallSimplicialMap {X Y : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] [∀ n, Small.{u} (Y.obj n)] (f : X ⟶ Y) :
    smallSimplicialSet.{u, v} X ⟶ smallSimplicialSet.{u, v} Y

lemma smallSimplicialMap_ulift {X Y : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] [∀ n, Small.{u} (Y.obj n)] (f : X ⟶ Y) :
    (SSet.uliftFunctor.{v, u}).map (smallSimplicialMap f) =
      (smallSimplicialSetIso X).hom ≫ f ≫ (smallSimplicialSetIso Y).inv

lemma smallSimplicialMap_naturality {X Y : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] [∀ n, Small.{u} (Y.obj n)] (f : X ⟶ Y) :
    (SSet.uliftFunctor.{v, u}).map (smallSimplicialMap f) ≫ (smallSimplicialSetIso Y).hom =
      (smallSimplicialSetIso X).hom ≫ f

lemma smallSimplicialMap_id (X : SSet.{max u v}) [∀ n, Small.{u} (X.obj n)] :
    smallSimplicialMap.{u, v} (𝟙 X) = 𝟙 (smallSimplicialSet X)

lemma smallSimplicialMap_comp {X Y Z : SSet.{max u v}}
    [∀ n, Small.{u} (X.obj n)] [∀ n, Small.{u} (Y.obj n)] [∀ n, Small.{u} (Z.obj n)]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallSimplicialMap.{u, v} (f ≫ g) = smallSimplicialMap f ≫ smallSimplicialMap g

noncomputable def smallLeftUnstraighteningMap {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
    (α : B ⟶ D) (h : (SSet.uliftFunctor.{u + 1, u}).map α ≫ G = F) :
    smallLeftUnstraightening F ⟶ smallLeftUnstraightening G

lemma smallLeftUnstraighteningMap_naturality {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
    (α : B ⟶ D) (h : (SSet.uliftFunctor.{u + 1, u}).map α ≫ G = F) :
    (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningMap F G α h) ≫
      (smallLeftUnstraighteningIso G).hom =
    (smallLeftUnstraighteningIso F).hom ≫
      leftUnstraighteningMap F G ((SSet.uliftFunctor.{u + 1, u}).map α) h

lemma smallLeftUnstraighteningMap_projection {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
    (α : B ⟶ D) (h : (SSet.uliftFunctor.{u + 1, u}).map α ≫ G = F) :
    smallLeftUnstraighteningMap F G α h ≫ smallLeftUnstraighteningProjection G =
      smallLeftUnstraighteningProjection F ≫ α

lemma smallLeftUnstraighteningMap_isPullback {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
    (α : B ⟶ D) (h : (SSet.uliftFunctor.{u + 1, u}).map α ≫ G = F) :
    IsPullback (smallLeftUnstraighteningMap F G α h) (smallLeftUnstraighteningProjection F)
      (smallLeftUnstraighteningProjection G) α

noncomputable def smallLeftUnstraighteningBaseChangeIso {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    smallLeftUnstraightening ((SSet.uliftFunctor.{u + 1, u}).map k ≫ F) ≅
      pullback (smallLeftUnstraighteningProjection F) k

lemma smallLeftUnstraighteningMap_id {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    smallLeftUnstraighteningMap F F (𝟙 B) (by simp) = 𝟙 (smallLeftUnstraightening F)

lemma smallLeftUnstraighteningMap_comp {B D E : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
    (H : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ SpaceInfinity.{u})
    (α : B ⟶ D) (β : D ⟶ E)
    (hα : (SSet.uliftFunctor.{u + 1, u}).map α ≫ G = F)
    (hβ : (SSet.uliftFunctor.{u + 1, u}).map β ≫ H = G) :
    smallLeftUnstraighteningMap F H (α ≫ β)
        (by rw [Functor.map_comp, Category.assoc, hβ, hα]) =
      smallLeftUnstraighteningMap F G α hα ≫ smallLeftUnstraighteningMap G H β hβ

noncomputable def coherentResolutionParameterizedMap {X Y T : SSet.{u}} (f : X ⊗ T ⟶ Y) :
    coherentResolutionRightAdjoint.obj X ⊗ T ⟶ coherentResolutionRightAdjoint.obj Y

lemma coherentResolutionParameterizedMap_fst (X T : SSet.{u}) :
    coherentResolutionParameterizedMap (fst X T) =
      fst (coherentResolutionRightAdjoint.obj X) T

noncomputable def coherentResolutionEnrichedMap (X Y : SSet.{u}) :
    (ihom X).obj Y ⟶
      (ihom (coherentResolutionRightAdjoint.obj X)).obj (coherentResolutionRightAdjoint.obj Y)

noncomputable def coherentResolutionKanEnriched : EnrichedFunctor SSet.{u} KanObject.{u} KanObject.{u}

lemma coherentResolutionParameterizedMap_comparison {X Y T : SSet.{u}} (f : X ⊗ T ⟶ Y) :
    (coherentResolutionComparison X ▷ T) ≫ coherentResolutionParameterizedMap f =
      f ≫ coherentResolutionComparison Y

lemma coherentResolutionEnrichedMap_comparison (X Y : SSet.{u}) :
    (coherentResolutionComparison X ▷ (ihom X).obj Y) ≫
        uncurry (coherentResolutionEnrichedMap X Y) =
      uncurry (𝟙 ((ihom X).obj Y)) ≫ coherentResolutionComparison Y

lemma coherentResolutionEnrichedMap_app_comparison (X Y : SSet.{u})
    {n k : SimplexCategoryᵒᵖ} (η : ((ihom X).obj Y).obj n) (α : n ⟶ k) (x : X.obj k) :
    (((coherentResolutionEnrichedMap X Y).app n η).app k α)
        ((coherentResolutionComparison X).app k x) =
      (coherentResolutionComparison Y).app k (η.app k α x)

def KanDiagramObject (C : Type u) [Category.{u} C]

instance kanDiagramObject_enrichedCategory (C : Type u) [Category.{u} C] :
    EnrichedCategory SSet.{u} (KanDiagramObject C)

instance kanDiagramObject_category (C : Type u) [Category.{u} C] :
    Category.{u} (KanDiagramObject C)

instance kanDiagramObject_simplicialCategory (C : Type u) [Category.{u} C] :
    SimplicialCategory (KanDiagramObject C)

noncomputable def KanDiagramNerve (C : Type u) [Category.{u} C] : SSet.{u + 1}

def diagonalKanDiagramObject {C : Type u} [Category.{u} C] {J : Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (KanDiagramObject C))
    (i : SimplicialThickening J) : KanObject.{u}

noncomputable def diagonalKanDiagramHom {C : Type u} [Category.{u} C] {J : Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (KanDiagramObject C))
    (i j : SimplicialThickening J) :
    SimplicialCategory.sHom i j ⟶
      SimplicialCategory.sHom (diagonalKanDiagramObject A F i) (diagonalKanDiagramObject A F j)

lemma diagonalKanDiagramHom_of_le {C : Type u} [Category.{u} C] {J : Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (KanDiagramObject C))
    (i j : SimplicialThickening J) (h : i.as ≤ j.as) :
    diagonalKanDiagramHom A F i j =
      F.map i j ≫ strictDiagramMixedHom (A.map (homOfLE h))
      ((F.obj i).val ⋙ kanObjectForget) ((F.obj j).val ⋙ kanObjectForget)

noncomputable def diagonalKanDiagramEvaluation {C : Type u} [Category.{u} C] {J : Type u} [LinearOrder J]
    (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (KanDiagramObject C)) :
    EnrichedFunctor SSet.{u} (SimplicialThickening J) KanObject.{u}

lemma diagonalKanDiagramEvaluation_reindex {C : Type u} [Category.{u} C] {J K : Type u}
    [LinearOrder J] [LinearOrder K] (α : J →o K) (A : K ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening K) (KanDiagramObject C)) :
    (SimplicialThickening.functor α).comp SSet (diagonalKanDiagramEvaluation A F) =
      diagonalKanDiagramEvaluation (α.toFunctor ⋙ A)
        ((SimplicialThickening.functor α).comp SSet F)

def kanDiagramSimplexBase {C : Type u} [Category.{u} C] {n : ℕ}
    (σ : (nerve C) _⦋n⦌) : ULift.{u} (Fin (n + 1)) ⥤ C

noncomputable def kanDiagramDiagonalSimplex
    {C : Type u} [Category.{u} C] {n : ℕ} (σ : (nerve C) _⦋n⦌)
    (F : (KanDiagramNerve C) _⦋n⦌) : SpaceInfinity.{u} _⦋n⦌

lemma kanDiagramDiagonalSimplex_naturality
    {C : Type u} [Category.{u} C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (nerve C) _⦋n⦌) (F : (KanDiagramNerve C) _⦋n⦌) :
    SpaceInfinity.map α.op (kanDiagramDiagonalSimplex σ F) =
      kanDiagramDiagonalSimplex ((nerve C).map α.op σ)
        ((KanDiagramNerve C).map α.op F)

noncomputable def kanDiagramJointEvaluation (C : Type u) [Category.{u} C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⊗ KanDiagramNerve C ⟶
      SpaceInfinity.{u}

noncomputable def kanDiagramRealization (C : Type u) [Category.{u} C] :
    KanDiagramNerve C ⟶
      SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))

def kanDiagramEvaluationEnriched {C : Type u} [Category.{u} C] (c : C) :
    EnrichedFunctor SSet.{u} (KanDiagramObject C) KanObject.{u}

noncomputable def kanDiagramNerveEvaluation {C : Type u} [Category.{u} C] (c : C) :
    KanDiagramNerve C ⟶ SpaceInfinity.{u}

lemma kanDiagramMixedHom_base_id {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (c : C) :
    strictDiagramMixedHom (𝟙 c) F G = strictDiagramMappingComponent F G c

lemma diagonalKanDiagramEvaluation_constant_base
    {C J : Type u} [Category.{u} C] [LinearOrder J] (c : C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J)
      (KanDiagramObject C)) :
    diagonalKanDiagramEvaluation ((Functor.const J).obj c) F =
      F.comp SSet (kanDiagramEvaluationEnriched c)

lemma kanDiagramRealization_evaluate
    {C : Type u} [Category.{u} C] (c : C) :
    kanDiagramRealization C ≫ evaluateFunctorAt (ULift.up (nerveVertex c)) =
      kanDiagramNerveEvaluation c

noncomputable def coherentResolutionArrowDiagram (X : KanObject.{u}) :
    ULift.{u} (Fin 2) ⥤ KanObject.{u}

noncomputable def coherentResolutionArrowMappingSimplex (X Y : KanObject.{u})
    {n : SimplexCategoryᵒᵖ} (η : ((ihom X.obj).obj Y.obj).obj n) :
    strictDiagramMappingSimplex (coherentResolutionArrowDiagram X ⋙ kanObjectForget)
      (coherentResolutionArrowDiagram Y ⋙ kanObjectForget) n

noncomputable def coherentResolutionArrowMappingSpaceMap (X Y : KanObject.{u}) :
    (ihom X.obj).obj Y.obj ⟶ strictDiagramMappingSpace
      (coherentResolutionArrowDiagram X ⋙ kanObjectForget)
      (coherentResolutionArrowDiagram Y ⋙ kanObjectForget)

noncomputable def coherentResolutionArrowEnriched :
    EnrichedFunctor SSet.{u} KanObject.{u} (KanDiagramObject (ULift.{u} (Fin 2)))

lemma coherentResolutionArrowEnriched_zero :
    coherentResolutionArrowEnriched.comp SSet
      (kanDiagramEvaluationEnriched (ULift.up (0 : Fin 2))) =
        EnrichedFunctor.id SSet.{u} KanObject.{u}

lemma coherentResolutionArrowEnriched_one :
    coherentResolutionArrowEnriched.comp SSet
      (kanDiagramEvaluationEnriched (ULift.up (1 : Fin 2))) =
        coherentResolutionKanEnriched.{u}

noncomputable def coherentResolutionInfinityMap : SpaceInfinity.{u} ⟶ SpaceInfinity.{u}

noncomputable def coherentResolutionComparisonFamily :
    SpaceInfinity.{u} ⟶ SpaceInfinityFunctor
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin 2))))

lemma coherentResolutionComparisonFamily_zero :
    coherentResolutionComparisonFamily.{u} ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (0 : Fin 2)))) =
        𝟙 SpaceInfinity.{u}

lemma coherentResolutionComparisonFamily_one :
    coherentResolutionComparisonFamily.{u} ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (1 : Fin 2)))) =
        coherentResolutionInfinityMap.{u}

lemma strictDiagramMixedHom_identity {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    strictDiagramMappingIdentity F ≫ strictDiagramMixedHom f F F = curry' (F.map f)

lemma diagonalKanDiagramEvaluation_constant
    {C J : Type u} [Category.{u} C] [LinearOrder J] (A : J ⥤ C) (F : KanDiagramObject C) :
    diagonalKanDiagramEvaluation A (enrichedConstantOrderDiagram J F) =
      enrichedFunctorOfOrderDiagram (A ⋙ F.val)

lemma kanDiagramDiagonalSimplex_constant {C : Type u} [Category.{u} C]
    (F : KanDiagramObject C) {n : ℕ} (σ : (nerve C) _⦋n⦌) :
    kanDiagramDiagonalSimplex σ (PinchedHom.constant (coherentNerveVertex F) n) =
      (kanDiagramCoherentNerve F.val).app (Opposite.op ⦋n⦌) (ULift.up σ)

def transposeFunctorFamily {A I X : SSet.{u}} (F : A ⟶ (ihom I).obj X) :
    I ⟶ (ihom A).obj X

lemma transposeFunctorFamily_vertex {A I X : SSet.{u}} (F : A ⟶ (ihom I).obj X)
    (i : I _⦋0⦌) :
    (transposeFunctorFamily F).app (Opposite.op ⦋0⦌) i =
      functorVertex (F ≫ evaluateFunctorAt i)

lemma transposeFunctorFamily_edgeAt {A I X : SSet.{u}} (F : A ⟶ (ihom I).obj X)
    {i j : I _⦋0⦌} (e : SSet.Edge i j) (a : A _⦋0⦌) :
    ((e.map (transposeFunctorFamily F)).map (evaluateFunctorAt a)).edge =
      ((F.app (Opposite.op ⦋1⦌) (PinchedHom.constant a 1)).app (Opposite.op ⦋1⦌)
        (𝟙 (Opposite.op ⦋1⦌))) e.edge

def coherentResolutionComparisonIndexEdge :
    SSet.Edge (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin 2))))
      (ULift.up (nerveVertex (ULift.up (0 : Fin 2))))
      (ULift.up (nerveVertex (ULift.up (1 : Fin 2))))

noncomputable def coherentResolutionComparisonEdge :
    SSet.Edge (X := (ihom SpaceInfinity.{u}).obj SpaceInfinity.{u})
      (functorVertex (𝟙 SpaceInfinity.{u})) (functorVertex coherentResolutionInfinityMap.{u})

lemma coherentResolutionComparisonEdge_at (K : KanObject.{u}) :
    (functorEdgeAt coherentResolutionComparisonEdge (coherentNerveVertex K)).edge =
      (coherentNerveEdge
        (show K ⟶ coherentResolutionKanEnriched.obj K from coherentResolutionComparison K.obj)).edge

lemma coherentResolutionComparisonEdge_isInvertible :
    IsInvertibleEdge coherentResolutionComparisonEdge.{u}

noncomputable def coherentResolutionInfinityComparisonIso :
    FunctorIso (𝟙 SpaceInfinity.{u}) coherentResolutionInfinityMap.{u}

noncomputable def coherentResolutionInfinityEquivalence :
    QCatEquivalence SpaceInfinity.{u} SpaceInfinity.{u}

noncomputable def coherentResolutionDiagramComparisonIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) : FunctorIso F (F ≫ coherentResolutionInfinityMap)

noncomputable def smallLeftUnstraighteningOverMap {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⟶ leftUnstraightening G) :
    smallLeftUnstraightening F ⟶ smallLeftUnstraightening G

lemma smallLeftUnstraighteningOverMap_naturality {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⟶ leftUnstraightening G) :
    (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningOverMap F G f) ≫
      (smallLeftUnstraighteningIso G).hom = (smallLeftUnstraighteningIso F).hom ≫ f

lemma smallLeftUnstraighteningOverMap_projection {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⟶ leftUnstraightening G)
    (h : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F) :
    smallLeftUnstraighteningOverMap F G f ≫ smallLeftUnstraighteningProjection G =
      smallLeftUnstraighteningProjection F

lemma smallLeftUnstraighteningFiberIso_hom_ι {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : B _⦋0⦌) :
    (smallLeftUnstraighteningFiberIso F c).hom ≫
        vertexFiberι (leftUnstraighteningProjection F) (ULift.up c) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberι (smallLeftUnstraighteningProjection F) c) ≫
          (smallLeftUnstraighteningIso F).hom

lemma smallLeftUnstraighteningOverMap_fiber_naturality {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⟶ leftUnstraightening G)
    (h : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F) (c : B _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (vertexFiberMap (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G)
        (smallLeftUnstraighteningOverMap F G f) (smallLeftUnstraighteningOverMap_projection F G f h) c) ≫
        (smallLeftUnstraighteningFiberIso G c).hom =
      (smallLeftUnstraighteningFiberIso F c).hom ≫
        vertexFiberMap (leftUnstraighteningProjection F) (leftUnstraighteningProjection G)
          f h (ULift.up c)

lemma smallLeftUnstraighteningOverMap_isPrecompositionEquivalence
    {B : SSet.{u}} [Quasicategory B]
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⟶ leftUnstraightening G)
    (h : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (ef : IsPrecompositionEquivalence f) :
    IsPrecompositionEquivalence (smallLeftUnstraighteningOverMap F G f)

instance smallLeftUnstraightening_quasicategory {B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    Quasicategory (smallLeftUnstraightening F)

lemma exists_smallLeftUnstraighteningComparison_of_functorIso
    {B : SSet.{u}} [Quasicategory B]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (η : FunctorIso F G) :
    ∃ f : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G,
      f ≫ smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection F ∧
        IsPrecompositionEquivalence f

noncomputable def smallLeftUnstraighteningComparisonOfFunctorIso
    {B : SSet.{u}} [Quasicategory B]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (η : FunctorIso F G) : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G

lemma smallLeftUnstraighteningComparisonOfFunctorIso_projection
    {B : SSet.{u}} [Quasicategory B]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (η : FunctorIso F G) :
    smallLeftUnstraighteningComparisonOfFunctorIso η ≫ smallLeftUnstraighteningProjection G =
      smallLeftUnstraighteningProjection F

lemma smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence
    {B : SSet.{u}} [Quasicategory B]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (η : FunctorIso F G) :
    IsPrecompositionEquivalence (smallLeftUnstraighteningComparisonOfFunctorIso η)

noncomputable def smallLeftUnstraighteningEquivalenceOfFunctorIso
    {B : SSet.{u}} [Quasicategory B]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (η : FunctorIso F G) : QCatEquivalence (smallLeftUnstraightening F) (smallLeftUnstraightening G)

noncomputable def smallLeftUnstraighteningResolutionEquivalence
    {B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    QCatEquivalence (smallLeftUnstraightening F)
      (smallLeftUnstraightening (F ≫ coherentResolutionInfinityMap))

lemma leftFibrationHom_vertex {B : SSet.{u}} (p q : LeftFibrationObject B) (f : p ⟶ q) :
    SimplicialCategory.homEquiv' p q f =
      relativeFunctorVertex q.val.hom p.val.hom f.left f.w

lemma leftFibrationInfinityEdge_isInvertible_of_precompositionEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    IsInvertibleEdge (leftFibrationInfinityEdge p q f hf)

noncomputable def leftFibrationInfinityVertexIsoOfPrecompositionEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    VertexIso (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q)

noncomputable def leftStraighteningCandidateIsoOfPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    FunctorIso (leftStraighteningCandidate p) (leftStraighteningCandidate q)

noncomputable def smallStraighteningCandidateIsoOfFunctorIso
    {C : Type u} [Category.{u} C]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ SpaceInfinity.{u}}
    (η : FunctorIso F G) :
    FunctorIso (leftStraighteningCandidate (smallLeftUnstraighteningProjection F))
      (leftStraighteningCandidate (smallLeftUnstraighteningProjection G))

noncomputable def smallStraighteningCandidateResolutionIso
    {C : Type u} [Category.{u} C]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ SpaceInfinity.{u}) :
    FunctorIso (leftStraighteningCandidate (smallLeftUnstraighteningProjection F))
      (leftStraighteningCandidate
        (smallLeftUnstraighteningProjection (F ≫ coherentResolutionInfinityMap)))

noncomputable def smallLeftUnstraighteningLift {E B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening F) :
    E ⟶ smallLeftUnstraightening F

lemma smallLeftUnstraighteningLift_naturality {E B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening F) :
    (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningLift F f) ≫
      (smallLeftUnstraighteningIso F).hom = f

lemma smallLeftUnstraighteningLift_projection {E B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (p : E ⟶ B)
    (f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening F)
    (h : f ≫ leftUnstraighteningProjection F = (SSet.uliftFunctor.{u + 1, u}).map p) :
    smallLeftUnstraighteningLift F f ≫ smallLeftUnstraighteningProjection F = p

lemma smallLeftUnstraighteningLift_fiber_naturality {E B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (p : E ⟶ B)
    (f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening F)
    (h : f ≫ leftUnstraighteningProjection F = (SSet.uliftFunctor.{u + 1, u}).map p)
    (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberMap p
      (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningLift F f)
        (smallLeftUnstraighteningLift_projection F p f h) b) ≫
      (smallLeftUnstraighteningFiberIso F b).hom =
    (uliftVertexFiberIso p b).hom ≫ vertexFiberMap
      ((SSet.uliftFunctor.{u + 1, u}).map p) (leftUnstraighteningProjection F)
        f h (ULift.up b)

lemma smallLeftUnstraighteningLift_isPrecompositionEquivalence
    {E B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (p : E ⟶ B) [LeftFibration p]
    (f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening F)
    (h : f ≫ leftUnstraighteningProjection F = (SSet.uliftFunctor.{u + 1, u}).map p)
    (ef : IsPrecompositionEquivalence f) :
    IsPrecompositionEquivalence (smallLeftUnstraighteningLift F f)

noncomputable def smallLeftCoherentTransportComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    E ⟶ smallLeftUnstraightening (leftCoherentTransport p)

lemma smallLeftCoherentTransportComparison_projection
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    smallLeftCoherentTransportComparison p ≫
      smallLeftUnstraighteningProjection (leftCoherentTransport p) = p

lemma smallLeftCoherentTransportComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    IsPrecompositionEquivalence (smallLeftCoherentTransportComparison p)

noncomputable def smallLeftCoherentTransportVertexIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    VertexIso (leftFibrationInfinityVertex p)
      (leftFibrationInfinityVertex
        (smallLeftUnstraighteningProjection (leftCoherentTransport p)))

lemma exists_smallLeftUnstraightening_representation
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ SpaceInfinity.{u},
      Nonempty (VertexIso (leftFibrationInfinityVertex p)
        (leftFibrationInfinityVertex (smallLeftUnstraighteningProjection F)))

lemma kanDiagramRealization_vertex {C : Type u} [Category.{u} C] (F : KanDiagramObject C) :
    (kanDiagramRealization C).app (Opposite.op ⦋0⦌) (coherentNerveVertex F) =
      functorVertex (kanDiagramCoherentNerve F.val)

def kanDiagramHom {C : Type u} [Category.{u} C] {F G : KanDiagramObject C}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) : F ⟶ G

noncomputable def kanDiagramNaturalTransformationEdge {C : Type u} [Category.{u} C]
    {F G : KanDiagramObject C}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    Edge (functorVertex (kanDiagramCoherentNerve F.val))
      (functorVertex (kanDiagramCoherentNerve G.val))

lemma kanDiagramNaturalTransformationEdge_at {C : Type u} [Category.{u} C]
    {F G : KanDiagramObject C}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) (c : C) :
    (functorEdgeAt (kanDiagramNaturalTransformationEdge η) (ULift.up (nerveVertex c))).edge =
      (coherentNerveEdge (show F.val.obj c ⟶ G.val.obj c from η.app c)).edge

lemma kanDiagramNaturalTransformationEdge_isInvertible {C : Type u} [Category.{u} C]
    {F G : KanDiagramObject C}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (hη : ∀ c, IsQCatEquivalence (X := (F.val.obj c).obj)
      (Y := (G.val.obj c).obj) (η.app c)) :
    IsInvertibleEdge (kanDiagramNaturalTransformationEdge η)

noncomputable def kanDiagramFunctorIsoOfPointwise {C : Type u} [Category.{u} C]
    {F G : KanDiagramObject C}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (hη : ∀ c, IsQCatEquivalence (X := (F.val.obj c).obj)
      (Y := (G.val.obj c).obj) (η.app c)) :
    FunctorIso (kanDiagramCoherentNerve F.val) (kanDiagramCoherentNerve G.val)

noncomputable def kanDiagramEdgewiseRightIso {C : Type u} [Category.{u} C]
    (F : C ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve (F ⋙ kanEdgewiseFunctor))
      (kanDiagramCoherentNerve F)

noncomputable def kanDiagramEdgewiseLeftIso {C : Type u} [Category.{u} C]
    (F : C ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve (F ⋙ kanEdgewiseFunctor))
      (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor))

noncomputable def kanDiagramOppositeComparisonIso {C : Type u} [Category.{u} C]
    (F : C ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve F)
      (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor))

noncomputable def leftStraighteningCandidateCoherentTransportIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    FunctorIso (leftStraighteningCandidate p) (leftCoherentTransport p)

noncomputable def smallStraighteningReconstruction
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    E ⟶ smallLeftUnstraightening (leftStraighteningCandidate p)

lemma smallStraighteningReconstruction_projection
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    smallStraighteningReconstruction p ≫
      smallLeftUnstraighteningProjection (leftStraighteningCandidate p) = p

lemma smallStraighteningReconstruction_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    IsPrecompositionEquivalence (smallStraighteningReconstruction p)

noncomputable def smallStraighteningReconstructionVertexIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    VertexIso (leftFibrationInfinityVertex p)
      (leftFibrationInfinityVertex
        (smallLeftUnstraighteningProjection (leftStraighteningCandidate p)))

noncomputable def smallStraighteningReconstructionCandidateIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    FunctorIso (leftStraighteningCandidate p)
      (leftStraighteningCandidate
        (smallLeftUnstraighteningProjection (leftStraighteningCandidate p)))

def relativeFunctorOverPostFunctor {A B : SSet.{u}} (a : A ⟶ B) : Over B ⥤ SSet.{u}

noncomputable def relativeFunctorOverIso {B : SSet.{u}}
    {a a' p p' : Over B} (ea : a ≅ a') (ep : p ≅ p') :
    relativeFunctorSpace p.hom a.hom ≅ relativeFunctorSpace p'.hom a'.hom

lemma relativeFunctorOverIso_hom {B : SSet.{u}}
    {a a' p p' : Over B} (ea : a ≅ a') (ep : p ≅ p') :
    (relativeFunctorOverIso ea ep).hom =
      relativeFunctorOverPre p.hom ea.inv ≫
        HomotopyLimits.relativeFunctorPost p.hom p'.hom ep.hom.left ep.hom.w a'.hom

lemma relativeFunctorOverIso_vertex {B : SSet.{u}}
    {a a' p p' : Over B} (ea : a ≅ a') (ep : p ≅ p')
    (f : a.left ⟶ p.left) (hf : f ≫ p.hom = a.hom) :
    (relativeFunctorOverIso ea ep).hom.app _ (relativeFunctorVertex p.hom a.hom f hf) =
      relativeFunctorVertex p'.hom a'.hom ((ea.inv.left ≫ f) ≫ ep.hom.left)
        (by rw [Category.assoc, ep.hom.w, Category.assoc, hf, ea.inv.w])

noncomputable def smallLeftUnstraighteningOverIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection F)) ≅
      Over.mk (leftUnstraighteningProjection F)

noncomputable def smallLeftUnstraighteningRelativeFunctorIso {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (relativeFunctorSpace (smallLeftUnstraighteningProjection G)
          (smallLeftUnstraighteningProjection F)) ≅
      relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)

noncomputable def liftedSmallLeftUnstraighteningMappingSpaceMap {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    leftUnstraighteningTransformationSpace F G ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        (relativeFunctorSpace (smallLeftUnstraighteningProjection G)
          (smallLeftUnstraighteningProjection F))

lemma liftedSmallLeftUnstraighteningMappingSpaceMap_comparison {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    liftedSmallLeftUnstraighteningMappingSpaceMap F G ≫
      (smallLeftUnstraighteningRelativeFunctorIso F G).hom =
      leftUnstraighteningMappingSpaceMap F G

lemma liftedSmallLeftUnstraighteningMappingSpaceMap_isQCatEquivalence_iff {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (liftedSmallLeftUnstraighteningMappingSpaceMap F G) ↔
      IsQCatEquivalence (leftUnstraighteningMappingSpaceMap F G)

lemma functorParameterizedPrism_injective {K B L X : SSet.{u}} :
    Function.Injective (functorParameterizedPrism (K := K) (B := B) (L := L) (X := X))

instance leftUnstraighteningTransformationSpace_obj_small {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((leftUnstraighteningTransformationSpace F G).obj n)

noncomputable def smallLeftUnstraighteningTransformationSpace {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) : SSet.{u}

noncomputable def smallLeftUnstraighteningTransformationSpaceIso {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraighteningTransformationSpace F G) ≅
      leftUnstraighteningTransformationSpace F G

instance smallLeftUnstraighteningTransformationSpace_kanComplex {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    KanComplex (smallLeftUnstraighteningTransformationSpace F G)

noncomputable def smallLeftUnstraighteningMappingSpaceMap {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    smallLeftUnstraighteningTransformationSpace F G ⟶
      relativeFunctorSpace (smallLeftUnstraighteningProjection G)
        (smallLeftUnstraighteningProjection F)

lemma smallLeftUnstraighteningMappingSpaceMap_comparison {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningMappingSpaceMap F G) ≫
      (smallLeftUnstraighteningRelativeFunctorIso F G).hom =
    (smallLeftUnstraighteningTransformationSpaceIso F G).hom ≫
      leftUnstraighteningMappingSpaceMap F G

lemma smallLeftUnstraighteningMappingSpaceMap_isQCatEquivalence_iff {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (smallLeftUnstraighteningMappingSpaceMap F G) ↔
      IsQCatEquivalence (leftUnstraighteningMappingSpaceMap F G)

def coherentPathDeformation {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) {i j : J} (P : Path i j) : Path (A i) (A j)

lemma coherentPathDeformation_mono {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) {i j : J} {P Q : Path i j} (h : P.I ⊆ Q.I) :
    (coherentPathDeformation A t P).I ⊆ (coherentPathDeformation A t Q).I

lemma coherentPathDeformation_id {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) (i : J) :
    coherentPathDeformation A t (𝟙 (⟨i⟩ : SimplicialThickening J)) =
      𝟙 (⟨A i⟩ : SimplicialThickening K)

lemma coherentPathDeformation_comp {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) {i j k : J} (P : Path i j) (Q : Path j k) :
    coherentPathDeformation A t
        (show (⟨i⟩ : SimplicialThickening J) ⟶ ⟨k⟩ from P ≫ Q) =
      (show (⟨A i⟩ : SimplicialThickening K) ⟶ ⟨A k⟩ from
        coherentPathDeformation A t P ≫ coherentPathDeformation A t Q)

lemma coherentPathDeformation_reindex {I J K : Type u}
    [LinearOrder I] [LinearOrder J] [LinearOrder K]
    (g : I →o J) (A : J →o K) (t : J →o Fin 2) {i j : I} (P : Path i j) :
    coherentPathDeformation (A.comp g) (t.comp g) P =
      coherentPathDeformation A t ((SimplicialThickening.functorMap g ⟨i⟩ ⟨j⟩).obj P)

lemma coherentPathDeformation_zero {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) {i j : J} (P : Path i j) :
    coherentPathDeformation A (OrderHom.const J 0) P =
      (SimplicialThickening.functorMap A ⟨i⟩ ⟨j⟩).obj P

lemma coherentPathDeformation_one {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) {i j : J} (P : Path i j) :
    (coherentPathDeformation A (OrderHom.const J 1) P).I = Set.Icc (A i) (A j)

lemma coherentPathDeformation_constant {J K : Type u} [LinearOrder J] [LinearOrder K]
    (a : K) (t : J →o Fin 2) {i j : J} (P : Path i j) :
    coherentPathDeformation (OrderHom.const J a) t P =
      𝟙 (⟨a⟩ : SimplicialThickening K)

def coherentPathDeformationFunctor {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) (i j : J) : Path i j ⥤ Path (A i) (A j)

def coherentPathDeformationEnriched {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) :
    EnrichedFunctor SSet.{u} (SimplicialThickening J) (SimplicialThickening K)

lemma coherentPathDeformationEnriched_reindex {I J K : Type u}
    [LinearOrder I] [LinearOrder J] [LinearOrder K]
    (g : I →o J) (A : J →o K) (t : J →o Fin 2) :
    (SimplicialThickening.functor g).comp SSet (coherentPathDeformationEnriched A t) =
      coherentPathDeformationEnriched (A.comp g) (t.comp g)

lemma coherentPathDeformationEnriched_zero {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) :
    coherentPathDeformationEnriched A (OrderHom.const J 0) = SimplicialThickening.functor A

def coherentSimplexMaximalization {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) : (SimplicialNerve C) _⦋n⦌

def coherentSimplexDeformationMap {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) :
    (Δ[n] : SSet.{max u v}) ⊗ Δ[1] ⟶ SimplicialNerve C

def coherentSimplexDeformation {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) :
    SSet.Homotopy (SSet.yonedaEquiv.symm σ)
      (SSet.yonedaEquiv.symm (coherentSimplexMaximalization σ))

lemma coherentSimplexDeformation_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) (x : (Δ[n] : SSet.{max u v}) _⦋0⦌) :
    (simplicialHomotopyVertexEdge (coherentSimplexDeformation σ) x).edge =
      PinchedHom.constant (coherentNerveVertex (σ.obj ⟨ULift.up (x.down.toOrderHom 0)⟩)) 1

lemma coherentSimplexDeformation_vertex_isInvertible
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) (x : (Δ[n] : SSet.{max u v}) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge (coherentSimplexDeformation σ) x).toTruncated

noncomputable def coherentSimplexMaximalizationIso
    {C : Type v} [Category.{u} C] [SimplicialCategory C] [Quasicategory (SimplicialNerve C)]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) :
    FunctorIso (SSet.yonedaEquiv.symm σ)
      (SSet.yonedaEquiv.symm (coherentSimplexMaximalization σ))

def coherentMaximalPath {J : Type u} [LinearOrder J] {i j : J} (h : i ≤ j) : Path i j

def coherentMaximalPathFunctor (J : Type u) [LinearOrder J] : J ⥤ SimplicialThickening J

lemma coherentPathDeformation_one_eq_maximal {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) {i j : J} (P : Path i j) :
    coherentPathDeformation A (OrderHom.const J 1) P =
      coherentMaximalPath (A.monotone P.le)

lemma coherentPathDeformationEnriched_one {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) :
    coherentPathDeformationEnriched A (OrderHom.const J 1) =
      enrichedFunctorOfOrderDiagram (A.toFunctor ⋙ coherentMaximalPathFunctor K)

def coherentEnrichedUnderlyingFunctor {C : Type v} {D : Type w}
    [Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) : C ⥤ D

lemma coherentEnrichedUnderlyingFunctor_vertex {C : Type v} {D : Type w}
    [Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) {X Y : C} (f : X ⟶ Y) :
    SimplicialCategory.homEquiv' (F.obj X) (F.obj Y) ((coherentEnrichedUnderlyingFunctor F).map f) =
      (F.map X Y).app (Opposite.op ⦋0⦌) (SimplicialCategory.homEquiv' X Y f)

lemma enrichedFunctorOfOrderDiagram_postcomp {J : Type u} [LinearOrder J]
    {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (A : J ⥤ C) (F : EnrichedFunctor SSet.{u} C D) :
    (enrichedFunctorOfOrderDiagram A).comp SSet F =
      enrichedFunctorOfOrderDiagram (A ⋙ coherentEnrichedUnderlyingFunctor F)

def coherentSimplexStrictDiagram {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) : ULift.{u} (Fin (n + 1)) ⥤ C

lemma coherentSimplexStrictDiagram_obj {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) (i : Fin (n + 1)) :
    (coherentSimplexStrictDiagram σ).obj (ULift.up i) = σ.obj ⟨ULift.up i⟩

lemma coherentSimplexMaximalization_eq_strictDiagram
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) :
    coherentSimplexMaximalization σ = enrichedFunctorOfOrderDiagram (coherentSimplexStrictDiagram σ)

noncomputable def coherentSimplexStrictificationIso
    {C : Type v} [Category.{u} C] [SimplicialCategory C] [Quasicategory (SimplicialNerve C)]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) :
    FunctorIso (SSet.yonedaEquiv.symm σ)
      (SSet.yonedaEquiv.symm (enrichedFunctorOfOrderDiagram (coherentSimplexStrictDiagram σ)))

def localKanDiagramBaseIso (n : ℕ) :
    (Δ[n] : SSet.{u + 1}) ≅
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin (n + 1))))

lemma localKanDiagramBaseIso_coherentNerve {n : ℕ}
    (F : ULift.{u} (Fin (n + 1)) ⥤ KanObject.{u}) :
    (localKanDiagramBaseIso n).hom ≫ kanDiagramCoherentNerve F =
      SSet.yonedaEquiv.symm (enrichedFunctorOfOrderDiagram F)

noncomputable def localKanDiagramStrictificationIso {n : ℕ}
    (σ : SpaceInfinity.{u} _⦋n⦌) :
    FunctorIso (SSet.yonedaEquiv.symm σ)
      ((localKanDiagramBaseIso n).hom ≫
        kanDiagramCoherentNerve (coherentSimplexStrictDiagram σ))

lemma exists_localKanDiagramStrictification {n : ℕ} (F : (Δ[n] : SSet.{u + 1}) ⟶ SpaceInfinity.{u}) :
    ∃ A : ULift.{u} (Fin (n + 1)) ⥤ KanObject.{u},
      Nonempty (FunctorIso F ((localKanDiagramBaseIso n).hom ≫ kanDiagramCoherentNerve A))

lemma exists_uliftLocalKanDiagramStrictification {n : ℕ}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[n] : SSet.{u}) ⟶ SpaceInfinity.{u}) :
    ∃ A : ULift.{u} (Fin (n + 1)) ⥤ KanObject.{u},
      Nonempty (FunctorIso F
        ((SSet.uliftFunctor.{u + 1, u}).map (stdSimplex.isoNerve n).hom ≫ kanDiagramCoherentNerve A))

lemma smallLeftUnstraighteningBaseChangeIso_hom_snd {B D : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    (smallLeftUnstraighteningBaseChangeIso F k).hom ≫
      pullback.snd (smallLeftUnstraighteningProjection F) k =
        smallLeftUnstraighteningProjection ((SSet.uliftFunctor.{u + 1, u}).map k ≫ F)

lemma exists_smallLeftUnstraighteningComparison_of_baseChangeIso
    {B D : SSet.{u}} [Quasicategory D]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (k : D ⟶ B)
    (η : FunctorIso F ((SSet.uliftFunctor.{u + 1, u}).map k ≫ G)) :
    ∃ f : smallLeftUnstraightening F ⟶ pullback (smallLeftUnstraighteningProjection G) k,
      f ≫ pullback.snd (smallLeftUnstraighteningProjection G) k =
        smallLeftUnstraighteningProjection F ∧ IsPrecompositionEquivalence f

lemma exists_smallLocalUnstraighteningStrictification {n : ℕ}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[n] : SSet.{u}) ⟶ SpaceInfinity.{u}) :
    ∃ (A : ULift.{u} (Fin (n + 1)) ⥤ KanObject.{u})
      (f : smallLeftUnstraightening F ⟶
        pullback (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve A))
          (stdSimplex.isoNerve n).hom),
      f ≫ pullback.snd (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve A))
        (stdSimplex.isoNerve n).hom = smallLeftUnstraighteningProjection F ∧
          IsPrecompositionEquivalence f

lemma exists_smallLocalUnstraighteningVertexIso {n : ℕ}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[n] : SSet.{u}) ⟶ SpaceInfinity.{u}) :
    ∃ A : ULift.{u} (Fin (n + 1)) ⥤ KanObject.{u},
      Nonempty (VertexIso (leftFibrationInfinityVertex (smallLeftUnstraighteningProjection F))
        (leftFibrationInfinityVertex
          (pullback.snd (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve A))
            (stdSimplex.isoNerve n).hom)))

def EdgewiseEnrichedObject (C : Type v)

def edgewiseEnrichedIdentity {C : Type v} [Category.{u} C] [SimplicialCategory C] (X : C) :
    𝟙_ SSet.{u} ⟶ edgewiseSubdivision (SimplicialCategory.sHom X X)

def edgewiseEnrichedComposition {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y Z : C) :
    edgewiseSubdivision (SimplicialCategory.sHom X Y) ⊗
      edgewiseSubdivision (SimplicialCategory.sHom Y Z) ⟶
        edgewiseSubdivision (SimplicialCategory.sHom X Z)

lemma edgewiseEnrichedIdentity_comp {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    (λ_ (edgewiseSubdivision (SimplicialCategory.sHom X Y))).inv ≫
      edgewiseEnrichedIdentity X ▷ _ ≫ edgewiseEnrichedComposition X X Y = 𝟙 _

lemma edgewiseEnrichedComposition_id {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) :
    (ρ_ (edgewiseSubdivision (SimplicialCategory.sHom X Y))).inv ≫
      _ ◁ edgewiseEnrichedIdentity Y ≫ edgewiseEnrichedComposition X Y Y = 𝟙 _

lemma edgewiseEnrichedComposition_assoc {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (W X Y Z : C) :
    (α_ (edgewiseSubdivision (SimplicialCategory.sHom W X))
      (edgewiseSubdivision (SimplicialCategory.sHom X Y))
      (edgewiseSubdivision (SimplicialCategory.sHom Y Z))).inv ≫
      edgewiseEnrichedComposition W X Y ▷ _ ≫ edgewiseEnrichedComposition W Y Z =
    _ ◁ edgewiseEnrichedComposition X Y Z ≫ edgewiseEnrichedComposition W X Z

instance edgewiseEnrichedObject_enrichedCategory (C : Type v)
    [Category.{u} C] [SimplicialCategory C] :
    EnrichedCategory SSet.{u} (EdgewiseEnrichedObject C)

instance edgewiseEnrichedObject_category (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    Category.{u} (EdgewiseEnrichedObject C)

instance edgewiseEnrichedObject_simplicialCategory (C : Type v)
    [Category.{u} C] [SimplicialCategory C] : SimplicialCategory (EdgewiseEnrichedObject C)

instance edgewiseEnrichedObject_sHom_kanComplex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] (X Y : EdgewiseEnrichedObject C) :
    KanComplex (SimplicialCategory.sHom X Y)

def edgewiseEnrichedRight (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    EnrichedFunctor SSet.{u} (EdgewiseEnrichedObject C) C

def edgewiseEnrichedInfinityMap (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    SimplicialNerve (EdgewiseEnrichedObject C) ⟶ SimplicialNerve C

lemma edgewiseEnrichedInfinityMap_isFullyFaithful (C : Type v) [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] :
    IsFullyFaithful (edgewiseEnrichedInfinityMap C)

lemma edgewiseEnrichedInfinityMap_isEssentiallySurjective (C : Type v)
    [Category.{u} C] [SimplicialCategory C] : IsEssentiallySurjective (edgewiseEnrichedInfinityMap C)

lemma edgewiseEnrichedInfinityMap_isQCatEquivalence (C : Type v) [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] :
    IsQCatEquivalence (edgewiseEnrichedInfinityMap C)

noncomputable def edgewiseEnrichedInfinityEquivalence (C : Type v) [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)] :
    QCatEquivalence (SimplicialNerve (EdgewiseEnrichedObject C)) (SimplicialNerve C)

def edgewiseInternalHomEvaluation (X Y : SSet.{u}) :
    edgewiseSubdivision X ⊗ edgewiseSubdivision ((ihom X).obj Y) ⟶ edgewiseSubdivision Y

def edgewiseKanEnrichedMap (X Y : SSet.{u}) :
    edgewiseSubdivision ((ihom X).obj Y) ⟶ (ihom (edgewiseSubdivision X)).obj (edgewiseSubdivision Y)

def edgewiseKanEnriched : EnrichedFunctor SSet.{u} (EdgewiseEnrichedObject KanObject.{u}) KanObject.{u}

lemma edgewiseInternalHomEvaluation_right (X Y : SSet.{u}) :
    edgewiseInternalHomEvaluation X Y ≫ edgewiseRight Y =
      (edgewiseRight X ⊗ₘ edgewiseRight ((ihom X).obj Y)) ≫ (ihom.ev X).app Y

def KanEnrichedComparison {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F G : EnrichedFunctor SSet.{u} C KanObject.{u})

lemma kanEnrichedComparison_app {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G)
    (X Y : C) {n k : SimplexCategoryᵒᵖ} (θ : (SimplicialCategory.sHom X Y).obj n)
    (α : n ⟶ k) (x : (F.obj X).obj.obj k) :
    ((G.map X Y).app n θ).app k α ((η.val X).app k x) =
      (η.val Y).app k (((F.map X Y).app n θ).app k α x)

def kanEnrichedComparisonDiagram {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) (X : C) :
    ULift.{u} (Fin 2) ⥤ KanObject.{u}

noncomputable def kanEnrichedComparisonMappingSimplex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G)
    (X Y : C) {n : SimplexCategoryᵒᵖ} (θ : (SimplicialCategory.sHom X Y).obj n) :
    strictDiagramMappingSimplex (kanEnrichedComparisonDiagram η X ⋙ kanObjectForget)
      (kanEnrichedComparisonDiagram η Y ⋙ kanObjectForget) n

noncomputable def kanEnrichedComparisonMappingSpaceMap {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) (X Y : C) :
    SimplicialCategory.sHom X Y ⟶ strictDiagramMappingSpace
      (kanEnrichedComparisonDiagram η X ⋙ kanObjectForget)
      (kanEnrichedComparisonDiagram η Y ⋙ kanObjectForget)

noncomputable def kanEnrichedComparisonArrowEnriched {C : Type v}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    EnrichedFunctor SSet.{u} C (KanDiagramObject (ULift.{u} (Fin 2)))

lemma kanEnrichedComparisonArrowEnriched_zero {C : Type v}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    (kanEnrichedComparisonArrowEnriched η).comp SSet
      (kanDiagramEvaluationEnriched (ULift.up (0 : Fin 2))) = F

lemma kanEnrichedComparisonArrowEnriched_one {C : Type v}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    (kanEnrichedComparisonArrowEnriched η).comp SSet
      (kanDiagramEvaluationEnriched (ULift.up (1 : Fin 2))) = G

noncomputable def kanEnrichedComparisonFamily {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    SimplicialNerve C ⟶ SpaceInfinityFunctor
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin 2))))

lemma kanEnrichedComparisonFamily_zero {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    kanEnrichedComparisonFamily η ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (0 : Fin 2)))) = coherentNerveMap F

lemma kanEnrichedComparisonFamily_one {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    kanEnrichedComparisonFamily η ≫
      evaluateFunctorAt (ULift.up (nerveVertex (ULift.up (1 : Fin 2)))) = coherentNerveMap G

noncomputable def kanEnrichedComparisonEdge {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) :
    Edge (functorVertex (coherentNerveMap F)) (functorVertex (coherentNerveMap G))

lemma kanEnrichedComparisonEdge_at {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G) (X : C) :
    (functorEdgeAt (kanEnrichedComparisonEdge η) (coherentNerveVertex X)).edge =
      (coherentNerveEdge (η.val X)).edge

lemma kanEnrichedComparisonEdge_isInvertible {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G)
    (hη : ∀ X, IsQCatEquivalence (X := (F.obj X).obj) (Y := (G.obj X).obj) (η.val X)) :
    IsInvertibleEdge (kanEnrichedComparisonEdge η)

noncomputable def kanEnrichedComparisonIso {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C KanObject.{u}} (η : KanEnrichedComparison F G)
    (hη : ∀ X, IsQCatEquivalence (X := (F.obj X).obj) (Y := (G.obj X).obj) (η.val X)) :
    FunctorIso (coherentNerveMap F) (coherentNerveMap G)

def edgewiseKanRightComparison :
    KanEnrichedComparison edgewiseKanEnriched.{u} (edgewiseEnrichedRight KanObject.{u})

def edgewiseKanInfinityMap :
    SimplicialNerve (EdgewiseEnrichedObject KanObject.{u}) ⟶ SpaceInfinity.{u}

noncomputable def edgewiseKanInfinityComparisonIso :
    FunctorIso edgewiseKanInfinityMap.{u} (edgewiseEnrichedInfinityMap KanObject.{u})

noncomputable def edgewiseKanInfinityEquivalence :
    QCatEquivalence (SimplicialNerve (EdgewiseEnrichedObject KanObject.{u})) SpaceInfinity.{u}

noncomputable def edgewiseCoherentDiagramLift {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) :
    B ⟶ SimplicialNerve (EdgewiseEnrichedObject KanObject.{u})

noncomputable def edgewiseCoherentDiagramLiftIso {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) :
    FunctorIso (edgewiseCoherentDiagramLift F ≫ edgewiseEnrichedInfinityMap KanObject.{u}) F

noncomputable def edgewiseCoherentReplacement {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) :
    B ⟶ SpaceInfinity.{u}

noncomputable def edgewiseCoherentReplacementIso {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) :
    FunctorIso (edgewiseCoherentReplacement F) F

noncomputable def smallEdgewiseCoherentReplacementEquivalence {B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    QCatEquivalence (smallLeftUnstraightening (edgewiseCoherentReplacement F))
      (smallLeftUnstraightening F)

def oppositeInternalHomEvaluation (X Y : SSet.{u}) :
    X.op ⊗ ((ihom X).obj Y).op ⟶ Y.op

def edgewiseOppositeInternalHomEvaluation (X Y : SSet.{u}) :
    X.op ⊗ edgewiseSubdivision ((ihom X).obj Y) ⟶ Y.op

def edgewiseOppositeKanEnrichedMap (X Y : SSet.{u}) :
    edgewiseSubdivision ((ihom X).obj Y) ⟶ (ihom X.op).obj Y.op

def edgewiseOppositeKanEnriched :
    EnrichedFunctor SSet.{u} (EdgewiseEnrichedObject KanObject.{u}) KanObject.{u}

lemma edgewiseInternalHomEvaluation_left (X Y : SSet.{u}) :
    edgewiseInternalHomEvaluation X Y ≫ edgewiseLeft Y =
      (edgewiseLeft X ⊗ₘ edgewiseLeft ((ihom X).obj Y)) ≫ oppositeInternalHomEvaluation X Y

def edgewiseKanLeftComparison :
    KanEnrichedComparison edgewiseKanEnriched.{u} edgewiseOppositeKanEnriched.{u}

def edgewiseOppositeKanInfinityMap :
    SimplicialNerve (EdgewiseEnrichedObject KanObject.{u}) ⟶ SpaceInfinity.{u}

noncomputable def edgewiseOppositeKanInfinityComparisonIso :
    FunctorIso edgewiseKanInfinityMap.{u} edgewiseOppositeKanInfinityMap.{u}

noncomputable def edgewiseKanOppositeInfinityComparisonIso :
    FunctorIso (edgewiseEnrichedInfinityMap KanObject.{u}) edgewiseOppositeKanInfinityMap.{u}

noncomputable def edgewiseOppositeKanInfinityEquivalence :
    QCatEquivalence (SimplicialNerve (EdgewiseEnrichedObject KanObject.{u})) SpaceInfinity.{u}

noncomputable def edgewiseCoherentOppositeReplacement {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) :
    B ⟶ SpaceInfinity.{u}

noncomputable def edgewiseCoherentOppositeReplacementIso {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) :
    FunctorIso F (edgewiseCoherentOppositeReplacement F)

def pinchedHomIsoOfIso {X Y : SSet.{u}} (e : X ≅ Y) (x y : X _⦋0⦌) :
    pinchedHom x y ≅
      pinchedHom (e.hom.app (Opposite.op ⦋0⦌) x) (e.hom.app (Opposite.op ⦋0⦌) y)

noncomputable def coherentOppositePinchedIso {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (x y : C) :
    pinchedHom (X := (SimplicialNerve C).op)
      (SSet.opObjEquiv.symm (coherentNerveVertex y))
      (SSet.opObjEquiv.symm (coherentNerveVertex x)) ≅
    pinchedHom (coherentNerveVertex (Opposite.op y)) (coherentNerveVertex (Opposite.op x))

noncomputable def coherentLeftPinchedFlagIso {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (x y : C) :
    pinchedHomLeft (coherentNerveVertex x) (coherentNerveVertex y) ≅
      (SSet.uliftFunctor.{v, u}).obj
        (coherentResolutionRightAdjoint.obj (SimplicialCategory.sHom x y)).op

noncomputable def coherentLeftResolution (X : SSet.{u}) : SSet.{u}

instance coherentLeftResolution_kanComplex (X : SSet.{u}) [KanComplex X] :
    KanComplex (coherentLeftResolution X)

noncomputable def coherentLeftResolutionFunctor : SSet.{u} ⥤ SSet.{u}

noncomputable def coherentLeftResolutionComparison (X : SSet.{u}) :
    X ⟶ coherentLeftResolution X

noncomputable def coherentLeftResolutionComparisonNat : 𝟭 SSet.{u} ⟶ coherentLeftResolutionFunctor

lemma coherentLeftResolutionComparisonNat_app (X : SSet.{u}) :
    coherentLeftResolutionComparisonNat.app X = coherentLeftResolutionComparison X

lemma coherentLeftResolutionComparison_isQCatEquivalence (X : SSet.{u}) [KanComplex X] :
    IsQCatEquivalence (coherentLeftResolutionComparison X)

noncomputable def pointedSpaceLeftResolutionIso (K : KanObject.{u}) :
    vertexFiber pointedSpaceProjection (spaceInfinityVertex (kanObjectOpFunctor.obj K)) ≅
      (SSet.uliftFunctor.{u + 1, u}).obj (coherentLeftResolution K.obj)

noncomputable def pointedSpaceLeftResolutionComparison (K : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj K.obj ⟶
      vertexFiber pointedSpaceProjection (spaceInfinityVertex (kanObjectOpFunctor.obj K))

lemma pointedSpaceLeftResolutionComparison_factorization (K : KanObject.{u}) :
    pointedSpaceLeftResolutionComparison K ≫ (pointedSpaceLeftResolutionIso K).hom =
      (SSet.uliftFunctor.{u + 1, u}).map (coherentLeftResolutionComparison K.obj)

lemma pointedSpaceLeftResolutionComparison_isQCatEquivalence (K : KanObject.{u}) :
    IsQCatEquivalence (pointedSpaceLeftResolutionComparison K)

noncomputable def edgewiseCoherentDiagramValue {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) : KanObject.{u}

lemma edgewiseCoherentOppositeReplacement_vertex {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (edgewiseCoherentOppositeReplacement F).app (Opposite.op ⦋0⦌) b =
      spaceInfinityVertex (kanObjectOpFunctor.obj (edgewiseCoherentDiagramValue F b))

noncomputable def edgewiseOppositeUnstraighteningFiberResolutionIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    vertexFiber (leftUnstraighteningProjection (edgewiseCoherentOppositeReplacement F)) b ≅
      (SSet.uliftFunctor.{u + 1, u}).obj (coherentLeftResolution (edgewiseCoherentDiagramValue F b).obj)

noncomputable def edgewiseOppositeUnstraighteningFiberComparison {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj (edgewiseCoherentDiagramValue F b).obj ⟶
      vertexFiber (leftUnstraighteningProjection (edgewiseCoherentOppositeReplacement F)) b

lemma edgewiseOppositeUnstraighteningFiberComparison_isQCatEquivalence {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    IsQCatEquivalence (edgewiseOppositeUnstraighteningFiberComparison F b)

noncomputable def coherentLeftResolutionParameterizedMap {X Y T : SSet.{u}} (f : X ⊗ T ⟶ Y) :
    coherentLeftResolution X ⊗ T ⟶ coherentLeftResolution Y

noncomputable def coherentLeftResolutionEnrichedMap (X Y : SSet.{u}) :
    (ihom X).obj Y ⟶ (ihom (coherentLeftResolution X)).obj (coherentLeftResolution Y)

noncomputable def coherentLeftResolutionKanEnriched :
    EnrichedFunctor SSet.{u} KanObject.{u} KanObject.{u}

lemma coherentLeftResolutionParameterizedMap_comparison {X Y T : SSet.{u}} (f : X ⊗ T ⟶ Y) :
    (coherentLeftResolutionComparison X ▷ T) ≫ coherentLeftResolutionParameterizedMap f =
      f ≫ coherentLeftResolutionComparison Y

noncomputable def coherentLeftResolutionKanComparison :
    KanEnrichedComparison (EnrichedFunctor.id SSet.{u} KanObject.{u})
      coherentLeftResolutionKanEnriched

noncomputable def coherentLeftResolutionInfinityMap : SpaceInfinity.{u} ⟶ SpaceInfinity.{u}

noncomputable def coherentLeftResolutionInfinityComparisonIso :
    FunctorIso (𝟙 SpaceInfinity.{u}) coherentLeftResolutionInfinityMap.{u}

noncomputable def coherentLeftResolutionInfinityEquivalence :
    QCatEquivalence SpaceInfinity.{u} SpaceInfinity.{u}

noncomputable def coherentLeftResolutionDiagramComparisonIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) : FunctorIso F (F ≫ coherentLeftResolutionInfinityMap)

lemma coherentOppositeRightHomComparison_pinchedIso
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (x y : C) :
    HomotopyLimits.coherentOppositeRightHomComparison x y ≫
      (coherentOppositePinchedIso x y).hom =
    coherentHomComparison (Opposite.op y) (Opposite.op x)

lemma coherentLeftHomComparison_flagIso
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (x y : C) :
    HomotopyLimits.coherentLeftHomComparison x y ≫
      (coherentLeftPinchedFlagIso x y).hom =
    (SSet.uliftFunctor.{v, u}).map
      (SSet.opFunctor.map (coherentResolutionComparison (SimplicialCategory.sHom x y)))

lemma coherentCosliceFiberComparison_flagIso
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (x y : C) :
    HomotopyLimits.coherentCosliceFiberComparison x y ≫
      (pinchedLeftCosliceFiberIso (coherentNerveVertex x) (coherentNerveVertex y)).inv ≫
      (coherentLeftPinchedFlagIso x y).hom =
    (SSet.uliftFunctor.{v, u}).map
      (SSet.opFunctor.map (coherentResolutionComparison (SimplicialCategory.sHom x y)))

noncomputable def pointedSpaceLeftCoefficientIso (K : KanObject.{u}) :
    K.obj ≅ (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj K)).op

lemma pointedSpaceLeftHomComparison_resolution (K : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso K).hom ≫
      HomotopyLimits.coherentLeftHomComparison pointKanObject (kanObjectOpFunctor.obj K) ≫
      (coherentLeftPinchedFlagIso pointKanObject (kanObjectOpFunctor.obj K)).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (coherentResolutionRightAdjoint.map
          (pointKanObjectHomIso (kanObjectOpFunctor.obj K)).hom)) =
    (SSet.uliftFunctor.{u + 1, u}).map (coherentLeftResolutionComparison K.obj)

noncomputable def pointedSpaceLeftCoherentComparison (K : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj K.obj ⟶
      vertexFiber pointedSpaceProjection (spaceInfinityVertex (kanObjectOpFunctor.obj K))

lemma pointedSpaceLeftCoherentComparison_resolution (K : KanObject.{u}) :
    pointedSpaceLeftCoherentComparison K ≫ (pointedSpaceLeftResolutionIso K).hom =
    (SSet.uliftFunctor.{u + 1, u}).map (coherentLeftResolutionComparison K.obj)

lemma pointedSpaceLeftCoherentComparison_eq_resolution (K : KanObject.{u}) :
    pointedSpaceLeftCoherentComparison K = pointedSpaceLeftResolutionComparison K

lemma pointedSpaceLeftCoherentComparison_isQCatEquivalence (K : KanObject.{u}) :
    IsQCatEquivalence (pointedSpaceLeftCoherentComparison K)

def pinchedHomLeftMap {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) :
    pinchedHomLeft x y ⟶
      pinchedHomLeft (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)

lemma pinchedHomLeft_eqToHom_app_val {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') {n : ℕ} (s : (pinchedHomLeft x y) _⦋n⦌) :
    pinchedLeftSimplexVal n
      ((eqToHom (congrArg₂ (fun a b ↦ pinchedHomLeft a b) hx hy)).app (Opposite.op ⦋n⦌) s) =
    pinchedLeftSimplexVal n s

lemma pinchedHomLeftMap_app_val {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : X _⦋0⦌} {n : ℕ} (s : (pinchedHomLeft x y) _⦋n⦌) :
    pinchedLeftSimplexVal n ((pinchedHomLeftMap f x y).app (Opposite.op ⦋n⦌) s) =
      f.app (Opposite.op ⦋n + 1⦌) (pinchedLeftSimplexVal n s)

noncomputable def coherentLeftPinchedHomMap
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (x y : C) :
    pinchedHomLeft (coherentNerveVertex x) (coherentNerveVertex y) ⟶
      pinchedHomLeft (coherentNerveVertex (F.obj x)) (coherentNerveVertex (F.obj y))

lemma coherentOppositeInverseSimplex_postcomp
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) {n : ℕ}
    (σ : (SimplicialNerve Cᵒᵖ) _⦋n⦌) :
    (HomotopyLimits.coherentOppositeInverseSimplex σ).comp SSet F =
      HomotopyLimits.coherentOppositeInverseSimplex
        (σ.comp SSet (HomotopyLimits.coherentEnrichedFunctorOp F))

lemma coherentLeftHomComparison_enriched_naturality
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (x y : C) :
    HomotopyLimits.coherentLeftHomComparison x y ≫ coherentLeftPinchedHomMap F x y =
      (SSet.uliftFunctor.{v, u}).map (SSet.opFunctor.map (F.map x y)) ≫
        HomotopyLimits.coherentLeftHomComparison (F.obj x) (F.obj y)

noncomputable def kanPointHomEnriched :
    EnrichedFunctor SSet.{u} KanObject.{u} KanObject.{u}

noncomputable def kanPointHomEnrichedComparison :
    KanEnrichedComparison kanPointHomEnriched
      (EnrichedFunctor.id SSet.{u} KanObject.{u})

noncomputable def kanPointHomInfinityMap : SpaceInfinity.{u} ⟶ SpaceInfinity.{u}

noncomputable def kanPointHomInfinityComparisonIso :
    FunctorIso kanPointHomInfinityMap.{u} (𝟙 SpaceInfinity.{u})

noncomputable def kanPointHomDiagramComparisonIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) : FunctorIso (F ≫ kanPointHomInfinityMap) F

lemma kanPointHomParameterizedMap_comparison {X Y : KanObject.{u}} {T : SSet.{u}}
    (f : X.obj ⊗ T ⟶ Y.obj) :
    ((ihom pointKanObject.obj).obj X.obj ◁ curry f) ≫
        MonoidalClosed.comp pointKanObject.obj X.obj Y.obj ≫ (pointKanObjectHomIso Y).hom =
      ((pointKanObjectHomIso X).hom ▷ T) ≫ f

noncomputable def leftPointHomParameterizedMap {X Y T : SSet.{u}} (f : X ⊗ T ⟶ Y) :
    ((ihom pointKanObject.obj).obj X.op).op ⊗ T ⟶
      ((ihom pointKanObject.obj).obj Y.op).op

lemma leftPointHomParameterizedMap_comparison {X Y : KanObject.{u}} {T : SSet.{u}}
    (f : X.obj ⊗ T ⟶ Y.obj) :
    leftPointHomParameterizedMap f ≫ (pointedSpaceLeftCoefficientIso Y).inv =
      ((pointedSpaceLeftCoefficientIso X).inv ▷ T) ≫ f

noncomputable def leftPointHomKanEnriched :
    EnrichedFunctor SSet.{u} KanObject.{u} KanObject.{u}

noncomputable def leftPointHomKanComparison :
    KanEnrichedComparison leftPointHomKanEnriched
      (EnrichedFunctor.id SSet.{u} KanObject.{u})

noncomputable def leftPointHomInfinityMap : SpaceInfinity.{u} ⟶ SpaceInfinity.{u}

noncomputable def leftPointHomInfinityComparisonIso :
    FunctorIso leftPointHomInfinityMap.{u} (𝟙 SpaceInfinity.{u})

noncomputable def leftPointHomDiagramComparisonIso {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) : FunctorIso (F ≫ leftPointHomInfinityMap) F

noncomputable def leftFibrationPrism_transportIso {A E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (e : SSet.Edge a b)
    (f : A ⟶ vertexFiber p a) (g : A ⟶ vertexFiber p b)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hH₀ : prismEndpoint 0 A ≫ H = f ≫ vertexFiberι p a)
    (hH₁ : prismEndpoint 1 A ≫ H = g ≫ vertexFiberι p b)
    (hHp : H ≫ p = fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge) :
    FunctorIso g (f ≫ edgeTransport p e)

lemma strictCoherentDiagram_edge {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) {i j : I} (f : i ⟶ j) :
    (HomotopyLimits.strictCoherentDiagram F).app (Opposite.op ⦋1⦌)
      (ULift.up (nerve.edgeMk f).edge) = (coherentNerveEdge (F.map f)).edge

lemma coherentCosliceFiberComparison_weighted_ι {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) (i : I) :
    HomotopyLimits.coherentCosliceFiberComparison x (F.obj i) ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (coherentNerveVertex (F.obj i)) =
    (SSet.uliftFunctor.{v, u}).map
      (weightedNerveConstantLift (HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) i) ≫
      HomotopyLimits.weightedCosliceComparison F x

noncomputable def weightedCosliceTransportPrism {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) {i j : I} (f : i ⟶ j) :
    (Δ[1] : SSet.{max u v}) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x (F.obj i)).op ⟶
      sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x))

lemma weightedCosliceTransportPrism_zero {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) {i j : I} (f : i ⟶ j) :
    prismEndpoint 0 _ ≫ weightedCosliceTransportPrism F x f =
      HomotopyLimits.coherentCosliceFiberComparison x (F.obj i) ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
          (coherentNerveVertex (F.obj i))

lemma weightedCosliceTransportPrism_one {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) {i j : I} (f : i ⟶ j) :
    prismEndpoint 1 _ ≫ weightedCosliceTransportPrism F x f =
      (SSet.uliftFunctor.{v, u}).map
        ((HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map f) ≫
      HomotopyLimits.coherentCosliceFiberComparison x (F.obj j) ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
          (coherentNerveVertex (F.obj j))

lemma weightedCosliceTransportPrism_projection {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) {i j : I} (f : i ⟶ j) :
    weightedCosliceTransportPrism F x f ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)) =
    fst (Δ[1] : SSet.{max u v})
      ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x (F.obj i)).op) ≫
      SSet.yonedaEquiv.symm (coherentNerveEdge (F.map f)).edge

noncomputable def coherentCosliceFiberComparison_transportIso
    {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [Quasicategory (SimplicialNerve C)] (F : I ⥤ C) (x : C) {i j : I} (f : i ⟶ j) :
    FunctorIso
      ((SSet.uliftFunctor.{v, u}).map
          ((HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map f) ≫
        HomotopyLimits.coherentCosliceFiberComparison x (F.obj j))
      (HomotopyLimits.coherentCosliceFiberComparison x (F.obj i) ≫
        edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
          (coherentNerveEdge (F.map f)))

lemma pointedSpaceLeftCoefficientIso_naturality {I : Type u} [Category.{u} I]
    (F : I ⥤ KanObject.{u}) {i j : I} (f : i ⟶ j) :
    (show (F.obj i).obj ⟶ (F.obj j).obj from F.map f) ≫
        (pointedSpaceLeftCoefficientIso (F.obj j)).hom =
      (pointedSpaceLeftCoefficientIso (F.obj i)).hom ≫
        ((HomotopyLimits.simplicialHomDiagram (F ⋙ kanObjectOpFunctor) pointKanObject ⋙
          SSet.opFunctor).map f)

noncomputable def coherentPointedFiberComparison (K : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj K.obj ⟶
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm
        (coherentNerveVertex pointKanObject))) (coherentNerveVertex (kanObjectOpFunctor.obj K))

lemma coherentPointedFiberComparison_isQCatEquivalence (K : KanObject.{u}) :
    IsQCatEquivalence (coherentPointedFiberComparison K)

noncomputable def coherentPointedFiberComparison_transportIso
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) {i j : I} (f : i ⟶ j) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (F.map f) ≫ coherentPointedFiberComparison (F.obj j))
      (coherentPointedFiberComparison (F.obj i) ≫
        edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm
          (coherentNerveVertex pointKanObject)))
            (coherentNerveEdge (kanObjectOpFunctor.map (F.map f))))

noncomputable def coherentPointedFiberComparison_morphismIso
    {K L : KanObject.{u}} (f : K ⟶ L) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map f ≫ coherentPointedFiberComparison L)
      (coherentPointedFiberComparison K ≫
        edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm
          (coherentNerveVertex pointKanObject)))
            (coherentNerveEdge (kanObjectOpFunctor.map f)))

lemma coherentPointedFiberTransport_isQCatEquivalence_iff
    {K L : KanObject.{u}} (f : K ⟶ L) :
    IsQCatEquivalence
      (edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm
        (coherentNerveVertex pointKanObject))) (coherentNerveEdge (kanObjectOpFunctor.map f))) ↔
      IsQCatEquivalence (X := K.obj) (Y := L.obj) f

def cosliceFiberVerticesIso {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ≅
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x')) y'

lemma pinchedLeftCosliceFiberIso_vertices {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') :
    (pinchedLeftCosliceFiberIso x y).hom ≫ (cosliceFiberVerticesIso hx hy).hom =
      eqToHom (congrArg₂ (fun a b ↦ pinchedHomLeft a b) hx hy) ≫
        (pinchedLeftCosliceFiberIso x' y').hom

lemma cosliceFiberVerticesIso_transport {X : SSet.{u}} [Quasicategory X]
    {x x' a a' b b' : X _⦋0⦌} (hx : x = x') (ha : a = a') (hb : b = b')
    (e : SSet.Edge a b) :
    (cosliceFiberVerticesIso hx ha).hom ≫
        edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm x')) (e.ofEq ha hb) =
      edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm x)) e ≫
        (cosliceFiberVerticesIso hx hb).hom

noncomputable def pointedSpaceCoherentFiberIso (K : KanObject.{u}) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm
      (coherentNerveVertex pointKanObject))) (coherentNerveVertex (kanObjectOpFunctor.obj K)) ≅
      vertexFiber pointedSpaceProjection (spaceInfinityVertex (kanObjectOpFunctor.obj K))

lemma coherentPointedFiberComparison_coordinates (K : KanObject.{u}) :
    coherentPointedFiberComparison K ≫ (pointedSpaceCoherentFiberIso K).hom =
      pointedSpaceLeftCoherentComparison K

noncomputable def pointedSpaceLeftResolutionComparison_transportIso
    {K L : KanObject.{u}} (f : K ⟶ L) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map f ≫ pointedSpaceLeftResolutionComparison L)
      (pointedSpaceLeftResolutionComparison K ≫ edgeTransport pointedSpaceProjection
        ((coherentNerveEdge (kanObjectOpFunctor.map f)).ofEq
          (spaceInfinityVertex_eq_coherent (kanObjectOpFunctor.obj K)).symm
          (spaceInfinityVertex_eq_coherent (kanObjectOpFunctor.obj L)).symm))

lemma pointedSpaceTransport_isQCatEquivalence_iff {K L : KanObject.{u}} (f : K ⟶ L) :
    IsQCatEquivalence
      (edgeTransport pointedSpaceProjection
        ((coherentNerveEdge (kanObjectOpFunctor.map f)).ofEq
          (spaceInfinityVertex_eq_coherent (kanObjectOpFunctor.obj K)).symm
          (spaceInfinityVertex_eq_coherent (kanObjectOpFunctor.obj L)).symm)) ↔
      IsQCatEquivalence (X := K.obj) (Y := L.obj) f

instance simplicialReplacementMap_mono {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) [∀ c, Mono (η.app c)] :
    Mono (simplicialReplacementMap η)

lemma strictDiagramMappingPre_scaffold_factorization {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) {E : SSet.{u}} (q : E ⟶ nerve C) :
    strictDiagramMappingPre η (leftStrictTransportDiagram q) =
      (strictDiagramMappingScaffoldIso G q).hom ≫
        relativeFunctorPre q (simplicialReplacementProjection G) (simplicialReplacementMap η) ≫
          (strictDiagramMappingScaffoldIso F q).inv

instance strictDiagramMappingPre_leftFibration {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) [∀ c, Mono (η.app c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q] :
    LeftFibration (strictDiagramMappingPre η (leftStrictTransportDiagram q))

lemma strictDiagramMappingPre_trivialKanFibration {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) [∀ c, Mono (η.app c)] (hη : ∀ c, IsQCatEquivalence (η.app c))
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q] :
    TrivialKanFibration (strictDiagramMappingPre η (leftStrictTransportDiagram q))

lemma strictDiagramMappingVertex_injective {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    Function.Injective (strictDiagramMappingVertex (F := F) (G := G))

def strictDiagramExtensionSpace {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} (η : F ⟶ G) {E : SSet.{u}} (q : E ⟶ nerve C)
    (θ : F ⟶ leftStrictTransportDiagram q) : SSet.{u}

lemma strictDiagramExtensionSpace_isContractibleKan {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) [∀ c, Mono (η.app c)] (hη : ∀ c, IsQCatEquivalence (η.app c))
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q]
    (θ : F ⟶ leftStrictTransportDiagram q) :
    IsContractibleKan (strictDiagramExtensionSpace η q θ)

lemma exists_strictDiagramExtension {C : Type u} [Category.{u} C]
    {F G : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) [∀ c, Mono (η.app c)] (hη : ∀ c, IsQCatEquivalence (η.app c))
    {E : SSet.{u}} (q : E ⟶ nerve C) [LeftFibration q]
    (θ : F ⟶ leftStrictTransportDiagram q) :
    ∃ Θ : G ⟶ leftStrictTransportDiagram q, η ≫ Θ = θ

end SerrePositivity.InfinityCategories
```

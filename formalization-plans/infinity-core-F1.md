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
open CategoryTheory Limits SSet
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

end SerrePositivity.InfinityCategories
```

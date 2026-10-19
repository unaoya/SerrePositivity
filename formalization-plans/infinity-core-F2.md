# F2：空間・Ind・presentable・随伴関手定理（レーン α3）

作成日：2026-10-18。状態：計画（着手は α2 の F1d（straightening）と N の γ3 の後）。
全体の正本は [foundations.md](foundations.md)。F1 は [infinity-core-F1.md](infinity-core-F1.md)。

## 0. 目標と範囲

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| F2a | 𝒮 = N^hc(Kan) の極限・余極限：γ3（homotopy 極限・余極限 = ∞ 極限・余極限）を Kan 複体の単体的モデル圏に適用。𝒮 は完備・余完備 | HTT 4.2.4.1、Kerodon 7.4–7.5 |
| F2b | filtered ∞ 圏、filtered 余極限、𝒮 で filtered 余極限と有限極限が交換すること | Kerodon 9.1 / HTT 5.3.1–5.3.3 |
| F2c | Ind(C)：前層のうち filtered 余極限で生成されるもの、普遍性（filtered 余極限を保つ関手の延長）、κ 版 | Kerodon 9.2? / HTT 5.3.5–5.3.6 |
| F2d | compact 対象、compactly generated、accessible ∞ 圏 | HTT 5.3.4、5.4 |
| F2e | presentable ∞ 圏：定義、Ind(C) の presentable 性、Fun(C^op, 𝒮) の presentable 性、随伴関手定理（HTT 5.5.2.9）、presentable の極限・余極限 | HTT 5.5.1–5.5.3 |
| F2f | Bousfield 局所化（反射的部分 ∞ 圏、局所対象、S⁻¹C）、accessible 局所化 | HTT 5.5.4 |
| F2g | P_Σ(C)（sifted 余極限で生成）と、単体的対象の coherent nerve との比較（HTT 5.5.8–5.5.9）。animated 環 := P_Σ(Poly) | HTT 5.5.8、5.5.9 |

使い先：K の非連結化 (a)（BGT §9：Ind(𝒞)^{ω₁}/𝒞 の Verdier 商）、β3（dg 商 = ∞ 局所化、HA 1.3.4）、
BS §7（animated 環、Construction 7.6 の左 Kan 拡張）、Sp の ∞ 的主張（γ3）。

## 1. 設計上の決定（暫定）

- 配置は `SerrePositivity/InfinityCategories/F2/`。
- 宇宙：𝒮 は `SSet.{u}` の Kan 複体の coherent nerve で `SSet.{u+1}`。presentable の議論では宇宙を明示する。
- Kerodon の第 9 章の範囲が足りない項目は HTT 第 5 章を原典とし、モデル構造を使う箇所（HTT 5.5.9 の
  単体的モデル圏）は γ3 の形に置き換える。

## 2. 現在地と主要宣言

（着手後に書き換える。）

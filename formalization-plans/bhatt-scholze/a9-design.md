# A9 の設計：界面の組み立てと E3 の消去（2026-11-02）

概要：E3 を消す道筋の最後の単位 A9。A4〜A8 で骨組みを置いた八つの欄（`perfd`・`unit`・`h0`・`universal`・`limitCone`・`limit_isLimit`・`integral`・
`excision`）から `PerfectoidizationInterfaceCAlg R p hR` の項を組み立て、既存の `nonempty_e3_of_cAlg`（EInfinity/Perfectoidization/DerivedCorollary）で
D(R) 版 `PerfectoidizationInterfaceE3` の存在を得て、唯一の引用 `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`（Inputs/PerfectoidizationInterface.lean:52、
`sorry`）を証明済みの定理に置き換える。
方針：界面の型は変えない（10-26 以降の規約）。組み立ては各欄の定理を項に詰めるだけ。Inputs の定理は同じ公開名・型のまま `nonempty_e3_of_cAlg ⟨…⟩` を
証明にする（下流の `Perfectoidization/Derived/{IntegralExistence,Excision}` は `Classical.choice (exists_perfectoidizationInterfaceE3 …)` で取り出しているので変更不要）。
規約：BS 側で `Inputs/` を書き換えるのは中身の段階（暦に載せてから）。そのとき監査（`make_area_audits.py` の許可一覧、Prop 8.10 の引用 3 件と結晶の黒箱）の更新を
調整役に知らせる。
使われ方：Serre positivity の perfectoid 側の `sorry` の消去。残るのは K 理論側の二件。

## 1. 欄と供給元

| 欄 | 供給する定理（drafts） | 単位 |
| --- | --- | --- |
| `perfd : algebraNerve R ⟶ CAlg_R R` | `e3Perfd p R`（A4/InterfaceFields） | A4-3 |
| `unit : FunctorHom (algebraEmbedding R) perfd` | `e3Unit p R` | A4-3 |
| `h0 : H0RingData R (perfd ≫ U) (underlyingUnit R unit)` | `e3H0RingData p R` | A4-3 |
| `universal` | `e3Universal p R`（A7/UniversalProperty） | A7-2 |
| `limitCone`・`limit_isLimit` | `e3LimitCone p R`・`e3LimitCone_isLimit p R`（A5/InterfaceLimitCone） | A5-1 |
| `integral` | `e3Integral p R`（A8/IntegralDiscreteness） | A8-4 |
| `excision` | `e3Excision p R`（A6/Excision） | A6-4 |

## 2. 形

- `def perfectoidizationInterfaceCAlg (R) (p) (hR) : PerfectoidizationInterfaceCAlg R p hR := { perfd := e3Perfd p R, unit := e3Unit p R, h0 := e3H0RingData p R,
  universal := e3Universal p R, limitCone := e3LimitCone p R, limit_isLimit := e3LimitCone_isLimit p R, integral := e3Integral p R, excision := e3Excision p R }`。
- `theorem nonempty_perfectoidizationInterfaceCAlg : Nonempty (PerfectoidizationInterfaceCAlg R p hR) := ⟨perfectoidizationInterfaceCAlg R p hR⟩`。
- `theorem exists_perfectoidizationInterfaceE3 … : Nonempty (PerfectoidizationInterfaceE3 R p hR) := nonempty_e3_of_cAlg R p hR (nonempty_perfectoidizationInterfaceCAlg R p hR)`
  — Inputs の定理の証明をこれに置き換える。docstring の「唯一の文献入力」の記述を更新し、原典の経路（A0〜A9）と残る引用（結晶 A1-2/A1-3、Prop 8.10 の 3 件、
  P⁰ の Rem 2.2.7 などの一般論の中の引用）を列挙する。

## 3. 依存の全体像（E3 の消去に要るもの）

- ∞ 側の一般論：S1〜S8（層・RΓ・脚注 10・層化・CAlg 値・κ・D(A) への適用・空間値の層、M12 系）、G3・G4・G6〜G10、DerivedGeneral（M13）、P⁰（M14）、
  descendability（M15）、F2 の P_Σ・Kan 延長。
- 論文の層の整理 2b の後：HA/DerivedCompletion の名前（完備化、Tot、Koszul）、Shared（cup 積・Bockstein・de Rham）。
- 引用として残るもの（`sorry`、監査の許可一覧へ）：結晶側 `hodgeTate_iso_polynomial_Zp`（A1-2/A1-3）、Prop 8.10 の 3 件（BS17 Thm 4.1、BM18 Thm 1.7、BS17 Lemma 6.3
  — 1c は証明予定）、P⁰ の Rem 2.2.7（Lur11、G-A4-1 の中で定理にする予定）。
- 古典的可換環論：Lemma 10.12（A8-3）、付値環の tilt・untilt（G-A6-3・6）、有限エタール代数の perfectoid 性（G-A8-6）。

## 4. 原典との差

界面の型そのものの原典との差は Inputs の docstring の六点 (i)〜(vi)（10-26）のまま。A9 は差を増やさない。

## 5. 単位と順序

A9-1：組み立て（骨組みのみ、drafts/A9/Assembly.lean）。中身の段階では A4〜A8 の全欄の中身が揃ってから Inputs を書き換える。

## 6. 決定事項

相談事項なし。Inputs の書き換えの時期は中身の段階で暦に載せる。

module

public import SerrePositivity.BhattScholze.Perfectoidization.Interface.Derived

/-! # 導来 perfectoid 化界面の存在（文献入力）

perfectoid 側の文献入力は本ファイルの界面の存在に集約する。
整代数の普遍環の存在と環の excision は、この界面から証明した定理である。

導来 perfectoid 化の E3 界面の存在をまとめて引用する。
根拠は BS 著者版 Definition 8.2、Lemma 8.4（pp.63–64）、Proposition 8.5（pp.64–65）、
Corollary 8.12（p.69）、Corollary 8.14（p.70）、Theorem 10.11（p.82）。
-/

public section
universe u
namespace SerrePositivity.BhattScholze.Inputs
open SerrePositivity.BhattScholze.PerfectoidizationInterface

/--
## 概要
Bhatt–Scholze, *Prisms and prismatic cohomology* の著者版から、導来 perfectoid 化の
E3 界面の存在を引用する。出典は `paper/refs/BS-prisms-author.pdf`、公開元は
https://people.mpim-bonn.mpg.de/scholze/prisms.pdf 。

## 方針
各欄の導出鎖は `formalization-plans/bhatt-scholze/perfectoidization-interface.md` §3 に対応する。
BS 著者版 Definition 8.2 の p 完備 E∞-S 代数から、底の D(R) の関手 perfd、自然な unit、H⁰ の環と
環準同型の関手性を取る。BS 著者版 Lemma 8.4（負次数のコホモロジーの消滅）は界面のどの欄からも読まれないので要求しない（2026-10-26 に欄を削除）。
BS 著者版 Proposition 8.5 と同証明の u-small な semiperfectoid cover の Čech 計算・coinitiality
（同計画 §2.1）から、Type u の perfectoid 標的の図式上の指定極限錐を得る。
HA Cor 3.2.2.5 による極限の忘却との整合性に加え、単位・H⁰ の射影の乗法整合性も保持する。
BS 著者版 Corollary 8.14 から離散の場合の perfectoid 性と環の射の普遍性を得る。
整代数の欄では、引用する定理から p 完備化した整代数の離散性と perfectoid 性を得て、
導来 p 完備化の H⁰ と perfectoid 標的への環 Hom の不変性（同計画 §2.2）で非完備始域へ延長する。
BS 著者版 Proposition 8.10 の arc 降下と Corollary 8.12 の E∞-S 代数の引き戻しから、
HA Cor 3.2.2.5 とスカラー制限の極限保存で D(R) の excision を得る。

## 規約
原文との差は同計画 §7 の六点である。(i) E3 の excision は底の D(R) で述べる。
(ii) 併記する E2a 案は homotopy 引き戻し・homotopy 写像空間で述べるが、ここで引用する型は E3。
(iii) universal は離散時の環準同型の普遍性に限定する。
(iv) limit は Type u の標的 `PerfUnder_u` に制限し、指定錐・単位・H⁰ の乗法との整合性を含める。
(v) 始域は導来 p 完備化の H⁰ を介して通常の非完備 R 代数まで拡張する。
(vi) 差写像の全射性は界面の欄に含めず、指定普遍環による四頂点の離散性と長完全列から証明する。
引き戻しだけから差の全射性を仮定してはならない。
本ファイルの一つの sorry が perfectoid 側に残す唯一の文献入力であり、
具体的な prismatic perfection とその降下の構成を実装したとは扱わない。

## 使われ方
`Perfectoidization/Interface/IntegralExistence.lean` と `Perfectoidization/Interface/Excision.lean` が界面を取り出し、
整代数の離散性と普遍性・環の excision の比較′ の証明済みの橋へ渡す。従来の公開名・型を通じて CLMST と主定理へ供給する。
-/
theorem exists_perfectoidizationInterfaceE3 (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) : Nonempty (PerfectoidizationInterfaceE3 R p hR) := by
  sorry

end SerrePositivity.BhattScholze.Inputs

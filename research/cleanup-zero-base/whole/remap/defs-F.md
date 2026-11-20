# 概念の定義書：F オペラドと E∞

小概念は out/remap-*.csv（B・D・F の担当分）の new_subconcept と一致する。ほかの大分類の担当が同じ概念へ送る小概念はここには入っていない。

## F オペラドと E∞/Barratt–Eccles と全射オペラド

**入るもの**：Berger–Fresse の二つのオペラドそのもの：Barratt–Eccles オペラド E（EΣₙ の正規化鎖、shuffle 合成）、全射オペラド χ、table reduction TR : E → χ、単体的鎖への χ の余作用（切断公式）。

**入らないもの**：
- BE 代数の圏の上の構成（cofibrant 代数、モデル構造、hammock、frame、CAlg、加群）は「F/E∞ 代数の圏（CAlg と加群）」へ。
- 一般の dg オペラド・代数・Schur 関手・セル代数は「F/dg オペラドと代数」へ。
- 一般の単体集合の正規化鎖・Alexander–Whitney・シャッフルは「B/単体的鎖・Dold–Kan・シャッフル」へ。
- BE の arity を巡回群の解像度として使うものは「F/冪作用の入力」へ。
- 対称群の隣接互換は「Z/組合せと順序」へ。

**小概念**：
- Barratt–Eccles オペラド（E(n) と shuffle 合成）
- table reduction（E → χ）
- 全射オペラド χ（全射語・削除微分・部分合成）
- 単体的鎖への χ の余作用（切断公式）
- shuffle 合成と微分の両立 — 印：補助
- table reduction の微分保存と合成保存 — 印：補助
- 切断公式の微分両立と余代数の公理 — 印：補助

**文献**：
- Berger–Fresse §1.1、§1.1.3
- Berger–Fresse §1.3.1、§1.4.2
- Berger–Fresse §1.2.1–§1.2.5
- Berger–Fresse §2.1、§2.2.3–§2.2.6、§3.1
- Berger–Fresse §1.1.3
- Berger–Fresse §1.4.4、§1.5.6–§1.5.9
- Berger–Fresse §1.2.3–§1.2.4、§2.2.6–§2.2.7、§3.1

## F オペラドと E∞/E∞ 代数の圏（CAlg と加群）

**入るもの**：BE 模型による E∞ 代数のホモトピー論：E 代数の転送モデル構造、cofibrant 代数と DK 局所化の神経としての CAlg_R、忘却・π₀・係数変更・余積、導来写像空間とホモトピー極限、E 代数上の加群とその導来 ∞ 圏。

**入らないもの**：
- オペラド E・χ そのものは「F/Barratt–Eccles と全射オペラド」へ。
- 任意のオペラド P についての代数・自由代数・セル代数は「F/dg オペラドと代数」へ。
- hammock・zigzag・DK 局所化の一般論は「C/局所化（Dwyer–Kan）」へ。frame の一般論は「E/ホモトピー関数複体と分解」へ。図式の射影モデル構造の一般論は「E/図式のモデル構造とホモトピー余極限」へ。
- 複体の図式（CarrierDiagram）だけの主張は「B/複体」へ。
- 複体の導来 ∞ 圏 D(R) は「D/導来 ∞ 圏」へ。dg 圏上の加群は「B/dg 加群」へ。
- モノイダル圏の一般論（二色のテンソル冪の分解など）は「Z/モノイダル圏」へ。

**小概念**：
- BE 模型の Tot による CAlg の源と二変数 Hom の pairing — 印：止めた経路「BE 模型の Tot 比較（IS-W2 の Tot 経路、D81 で止めた）」
- CAlg（E∞ 代数の ∞ 圏）：忘却・π₀・係数変更・余積
- E 代数のモデル構造・導来写像空間・ホモトピー極限
- E 代数上の加群
- E 代数上の加群のテンソルの余極限表示 — 印：補助
- E 代数の導来写像空間と hammock 局所化の Hom の比較 — 印：補助

**文献**：
- HTT 1.1.5；Dwyer–Kan；HA §3.2.2, 3.2.4.7
- Berger–Moerdijk 命題 4.1；Hovey §2.1, §5
- HA §4.2.1, §4.2.3, §1.3.5；Keller 定理 3.2
- HA §1.3.4, 1.3.1.6
- Dwyer–Kan；Low 命題 3.6–3.7；Hovey §5

## F オペラドと E∞/dg オペラドと代数

**入るもの**：非有界複体の対称列の上の対称 dg オペラドの一般論：部分合成と全合成、オペラドの射、Schur 関手と自由代数、オペラド代数と余代数、セル代数の次数つき自由表示。

**入らないもの**：
- 特定のオペラド（Barratt–Eccles、全射）は「F/Barratt–Eccles と全射オペラド」へ。
- E 代数のモデル構造と CAlg は「F/E∞ 代数の圏（CAlg と加群）」へ。
- 対称列の一般論（モノイダル圏の中の）は「G/対称列」へ。
- 複体の有限族のテンソル積と並べ替えは「B/複体」へ。
- dg 代数（結合的、非可換）は「B/dg 圏と dg 関手」「B/dg 代数のホモトピー論」へ。

**小概念**：
- Schur 関手と自由代数
- dg オペラド（対称列・部分合成・射）
- オペラドの全合成（複数の入力への代入）
- オペラド代数と余代数
- セル代数の次数つき自由表示（微分の消去）

**文献**：
- Berger–Moerdijk §1
- Berger–Moerdijk §1、命題 4.1；Berger–Fresse §3.1
- Berger–Moerdijk 命題 4.1

## F オペラドと E∞/冪作用の入力

**入るもの**：冪作用（DAG XIII Construction 2.2.6、May の設定）の入力の準備：p 巡回群とその BE の arity の中での実現、BE の arity を巡回部分群の射影解像度と見ること、閉元と p 重テンソルへの同次の作用。

**入らないもの**：
- Eilenberg–MacLane 空間（複体の Γ）は「G/Ω スペクトル（Bousfield–Friedlander）」へ。
- 型 A の隣接互換（Coxeter）は「Z/組合せと順序」へ。
- 全複体の相対圏と D(A) の比較（complexRelativeCategory など）は「D/導来 ∞ 圏」へ。
- BE オペラドそのものは「F/Barratt–Eccles と全射オペラド」へ。

**小概念**：
- 冪作用の入力（閉元と同次の作用）
- 巡回部分群と BE の解像度（May の設定）

**文献**：
- DAG XIII Construction 2.2.6（CyclicTensorInput のファイル冒頭）

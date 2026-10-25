# D-bar：D-8 c2・c6・c7

## 引き継ぎ（2026-10-25）
### 現在地
- 指定の foundations §6・§8、progress の D、D 計画の D-8 c を確認。
- MC は D の公開型そのものの仮定。実 bar 加群、全次数 Hom 同値、twisted 微分、閉列方程式を実装。
- 所有 All のビルド成功（3442 jobs、11葉）。専用公理監査成功（標準三公理のみ）。
- 非退化・退化 graded 因子の分裂と恒等射の二射影分解、退化次数 −1 作用素を構成。
- 実 bar 自己 Hom の MC 微分公式、実微分の境界による段階的射と恒等への全 dg 自然な鎖ホモトピーを供給。
- ラベル自由加群へ Mathlib の PInfty・homotopyPInftyToId・正規化 Moore 同値を直接適用。
- 19:40 にユーザーが正規化中間模型・同じ theta の微分に対する変形 retract を採用。再開中。
- c2・c6・c7 は未完。ordinary compact／perfect に置換しない。
### 残り（依存順）
- 1. MC 仮定付き実 bar 加群と正規化模型・変形 retract の構成（8–24時間）。
- 2. 元の coherent 図式の native 余錐と全 Hom の普遍性（8–24時間）。
- 3. native κ-filtered 余極限と strict dg 余極限の評価比較（8–24時間）。
- 4. representable・全 shift・κ未満 sphere-free 基底の native κ-compact 性（4–12時間）。
- 5. 生成元判定から c6 の実 perfect／retract、c7 の七入力へ接続（1–3時間）。
- 6. 自分の集約・監査・限定コミット（1時間）。
### 主要宣言
- dgCoherentBarMaurerCartan、dgCoherentBarModule、dgCoherentBarModule_d。
- dgCoherentBarHomDegreeEquiv、dgCoherentBarHomDegreeEquiv_d、dgCoherentBarHomColumnsEquiv。
- dgCoherentBarClosedColumnsEquiv、dgCoherentBar_native_degenerateTriangle。
- dgCoherentBar_raw_inclusion_ne_zero。
- dgCoherentBarNormalizedGraded、dgCoherentBarGraded_identity_decomposition。
- dgCoherentBarNormalizationStageHomotopy、dgCoherentBarEndRebase_d。
- dgCoherentBarLabelNormalizedEquiv、dgCoherentBarLabelProjection_eq_zero_of_degenerate。
### 依存と提供
- D の既存 Derived・DGNerve・DifferentialGraded と KST/NonConnective は読み取り専用。
- dgCoherentBarTheta と moduleMaurerCartan を使用する。
- DGKappaClosedCompactGeneratorCriterion を c6・c7 の正本として使用予定。
- MC の無条件結論が D から公開されたら、同じ仮定に代入する系を追加する。
- 編集所有は Derived/CoherentBar/、その All、専用監査、本計画のみ。
### 未コミット
- なし（保存済みの段階的作用素から、正規化性と安定化を続行）。
### 既知の問題
- native 余錐・普遍性と filtered 評価比較は未構成。代数的閉列同値を native 普遍性とは扱わない。
- 段階的射の像の正規化性・安定化と、退化部分の実微分での保存が残る。
  各有限段階の鎖ホモトピーと、完成した変形 retract を区別する。
- D の MC 無条件結論は未公開（確認時の公開名は _of_columns のみ）。仮定は維持。
### 次の一手
- Mathlib の PInfty・homotopyPInftyToId・Moore 正規化同値を参照し、退化部分の縮約を構成する。

## 採用された設計追加（19:40）
- 根拠：dgCoherentBarIndex は退化を含む全単体を独立因子にする。
  dgCoherentBar_raw_inclusion_ne_zero は非零因子の包含が零にならないことを示す。
  一方 dgCoherentBar_native_degenerateTriangle は任意の native 図式の退化三角形の
  最上 cochain が零であることを示す。生の因子包含を余錐の全高次成分にする直接案は退化を保存しない。
- 提案：既存 theta と実 bar 加群を保持し、所有葉内に正規化した中間模型と
  退化部分の縮約（変形 retract）を構成する。正規化側で native 余錐を作り、
  比較により元の bar へ戻す。Hom 普遍性はまず正規化側とのホモトピー同値で比較する。
- 既存 D の MC 検証に変更は依頼しない。深層編集・模型の置換・追加公理も提案しない。
- Mathlib の AlgebraicTopology/DoldKan を直接参照し、適用可能な API は import して使う。コピーしない。
- 二つの検査補題だけで正規化 retract の存在まで証明したとは扱わない。
- 三段目は報告の六項目で固定。c2/c6/c7 完了とはしない。

## 運用
- 新規 sorry・公理・引用なし。主経路に ModelCategory SSet 等の instance を置かない。
- F2.Compact.IsKappaCompact.{u, max (u+1) v} を使う。
- 深層・既存 D 集約・両監査・他レーンを編集しない。
- 自分の集約と監査のみ検証。根のビルド・.lake 削除はしない。
- set -o pipefail と git commit --only によって所有ファイルだけ保存する。
- 停止は二段目完了・設計変更提案・所有 import 閉包破損・稼働24時間。
- 提案・依頼はユーザーへ中継する。実施記録はコミット本文。

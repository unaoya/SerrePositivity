# D-bar：D-8 c2・c6・c7

## 引き継ぎ（2026-10-25）
### 現在地
- 指定の foundations §6・§8、progress の D、D 計画の D-8 c を確認。
- MC は D の公開型そのものの仮定。実 bar 加群、全次数 Hom 同値、twisted 微分、閉列方程式を実装。
- 所有 All のビルド成功（3678 jobs、55葉）。専用公理監査成功（596宣言、標準三公理のみ）。
- 非退化・退化 graded 因子の分裂と恒等射の二射影分解、退化次数 −1 作用素を構成。
- 実 bar 自己 Hom の MC 微分公式、実微分の境界による段階的射と恒等への全 dg 自然な鎖ホモトピーを供給。
- ラベル自由加群へ Mathlib の PInfty・homotopyPInftyToId・正規化 Moore 同値を直接適用。
- 元の theta の全退化列の非退化射影像が零であることを証明。
- 同じ MC 仮定のみで実正規化 dg 加群と、元の実 bar からの閉零射影を構成。
- 単体次数の標的支持により有限段階と累積ホモトピーが各単体上で安定することを証明。
- 安定値の実 bar 鎖自己写像と恒等への全 dg 自然な鎖ホモトピーを構成。
- D の公開 MC 定理（1017d8a9c）を代入した無条件版を所有葉 Unconditional に追加。
- 19:40 採用の正規化中間模型・同じ theta の変形 retract を続行中。
- 工程B：正規化実 bar の全次数 Hom・非退化列の微分同値、実 native 列と退化消滅を構成。
- D の Bianchi データを再利用し、全 HA 単体 NativeSimplex と全末端成分のラベル比較を構成。
- 単体作用に対する自然性・JoinCocone への貼り合わせ・native Hom 普遍性は未完。
- c2・c6・c7 は未完。ordinary compact／perfect に置換しない。
### 残り（依存順）
- 1. 工程A：変形 retract は D に移管。CoherentBar/Retract/ の新規葉は読み取り専用。
  正規化加群の公開型は維持。変更が必要なら実施前にユーザーへ報告。
- 2. 工程B：D-bar は正規化側の native 余錐と全 Hom の普遍性に専念（8–24時間）。
- 3. 工程C1/C2：strict 擬同型と比較の組み立ては D-e に移管。StrictComparison/ は読み取り専用。
  読み取り専用 KappaCovers.StrictComparison の DGKappaStrictFilteredColimitComparison R D κ の値として公開する。
  添字は Type u の κ-filtered poset。c2 もこの比較から導く。
  ∞ 圏から poset への共終性は後段の Ind.exists_cofinal_kappaFiltered_poset が担当。
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
- dgCoherentBarColumn_degenerate_normalizedProjection、dgCoherentBarNormalizedTheta_projection。
- dgCoherentBarNormalizedTheta_maurerCartan、dgCoherentBarNormalizedModule。
- dgCoherentBarNormalizedModuleProjection、dgCoherentBarNormalizationBoundary_cycle。
- dgCoherentBarNormalizedHomDegreeEquiv／NormalizedHomColumnsEquiv／NormalizedClosedColumnsEquiv。
- dgCoherentBarNativeColumn、dgCoherentBarNativeColumn_degenerate／vertex_closed／d_positive。
- dgCoherentBarNativeSimplex、dgCoherentBarNativeSimplex_front／last。
- dgCoherentBarNativeSimplexData_last_hom_heq。
### 依存と提供
- D の既存 Derived・DGNerve・DifferentialGraded と KST/NonConnective は読み取り専用。
- dgCoherentBarTheta と moduleMaurerCartan を使用する。
- DGKappaClosedCompactGeneratorCriterion を c6・c7 の正本として使用予定。
- MC の無条件結論が D から公開されたら、同じ仮定に代入する系を追加する。
- 編集所有は Derived/CoherentBar/（Retract/・StrictComparison/ を除く）、その All、専用監査、本計画のみ。
### 未コミット
- なし（工程Bの検証済み9葉・所有集約・監査・計画を限定保存）。
### 既知の問題
- native 余錐・普遍性と filtered 評価比較は未構成。代数的閉列同値を native 普遍性とは扱わない。
- 安定作用素が退化因子を消すことと、実射影の補正包含・変形 retract が残る。
  安定自己写像の恒等への鎖ホモトピーだけで、正規化模型との retract とは扱わない。
- MC 仮定付き API を保持し、公開 MC 定理を代入する無条件 API を併設。
### 次の一手
- 任意の単調写像に対する NativeSimplex の自然性を証明し、JoinCocone と全 Hom 普遍性へ進む。

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

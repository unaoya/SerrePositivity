# P-d：局所対象の accessibility

## 引き継ぎ

- 現在地：(2) の条件付き presentability を証明・公開した。
  (1) は反射を仮定しない filtered 閉性・内部余極限・包含の保存性まで証明済み。
  無条件の `IsAccessible (Category edges)` は未証明。工程全体を完了とはしない。
- 残り：HTT 5.5.4.2 の無条件の小 compact 生成表示。下記の依存順の変更を提案して停止する。
- 主要宣言：`isPresentable_of_reflection`、`isPresentable_of_localReplacements`、
  `exists_regular_inclusion_accessibilityCardinal`、`inclusion_isKappaAccessibleFunctor`。
- 名前空間：`SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects`。
- 依存：既存の LocalObjects、LocalReplacementReflection、ReflectionSmallColimits、
  CompactEndpoints、AccessibleFamilySaturationModels、全 Hom・分類輸送の葉を読み取り専用で使用。
- 提供先：P-f。(2) は既存の局所置換反射だけを入力に取り、局所対象圏の accessibility や
  小生成族の存在は追加入力にしない。提案・依頼はユーザー経由。
- 未コミット：なし（この計画を含む所有ファイルを限定コミットに記録する）。
- 既知の問題：(1) の filtered 閉性だけでは小 compact 生成表示を与えない。
  P の `pullback_isAccessible`・`fiber_isAccessible_of_presentable` はまだ未公開。
  P-f の無条件の局所置換の存在もまだ未公開。これらを存在仮定として追加していない。
- 次の一手：下記提案へのユーザー判断を受け、指定された供給定理を消費する。
  独立の無条件証明を継続する判断なら、同値条件への accessible 逆像の小生成表示を構成する。

## 三段目

1. l1：既存定義・反射・accessibility の公開界面を確認する（完了）。
2. l2：共通端点 compact 濃度、局所性の filtered 閉性、小 compact 生成表示を構成する
   （閉性・filtered 余極限・包含の保存は完了。無条件の生成表示は未完）。
3. l3：条件付き反射から presentability を公開する（完了）。
4. l4：所有集約と専用監査を検証し、限定コミットと P-f 向けの公開名を報告する
   （途中成果の検証・記録は完了。全工程の完了報告ではない）。

## 検証済みの構成

- `Definition`：小さい辺族の像集合に対する既存の `localObjectsSubcomplex` をそのまま使用。
  `Category edges` はその全単体を保持する別名。局所性は各添字の写像空間前合成の同値性。
- `LocalityInversion`：元の局所性と同じ表現可能前層による反対辺の反転を同定。
  元の前合成円柱・slice 輸送・分類辺の可逆性を両方向に比較する。
- `LocalityNaturalComparison`：共同 Hom の反変変数の辺作用を一つの全自然比較として保持し、
  同じ比較成分の可逆性を元の局所性と同定する。
- `FilteredClosure`：端点の compact 性で全共変 Hom が元の filtered 余錐を保存することと、
  全自然比較の余極限頂点での可逆性判定から、元の局所性の閉性を得る。
- `FilteredColimits`：周囲の同じ全余極限余錐を局所対象全部分圏へ持ち上げる。
  任意の内部余極限との全余錐同型から包含の保存性を得る。反射は仮定しない。
- `ReflectionColimits`：既存の条件付き局所置換反射から全小余極限を構成する。
- `ReflectiveAccessibility`：反射した小生成族の周囲での同型飽和を小模型へ移し、
  その同じ模型を全部分圏へ持ち上げる。全生成表示を移し、元の反射像の accessibility を得る。
  反射像に固定頂点写像の厳密な小ささを仮定しない。
- `Presentable`：共通端点濃度を超える周囲の accessibility 濃度を選び、反射した生成族の
  compact 性と小生成表示から条件付き accessibility を得て、全小余極限と合わせる。

## 公開界面と入力の区別

- `exists_regular_inclusion_accessibilityCardinal`：任意の下界を超える正則濃度で、
  元の局所対象圏の filtered 余極限と包含の filtered 保存を与える。反射入力なし。
  これは局所対象圏そのものの `IsAccessible` ではない。
- `isAccessible_of_reflection`：presentable C、小さい辺族、既存の反射を入力に取る。
- `isPresentable_of_reflection`：同じ入力で元の局所対象圏の presentable 性を与える。
- `isPresentable_of_localReplacements`：既存の局所置換の存在条件を直接入力に取る。

## 設計提案（ユーザー判断が必要）

- 推奨：上の (2) を先に P-f へ供給し、(1) の無条件版は P-f が f3 の無条件の
  局所置換存在を公開した後、その定理を消費して閉じる。最終的な (1) の型に
  反射や局所置換の存在仮定を追加しない。供給後の接続・監査は 1〜2 時間の見積もり。
- 依存順を変える理由：現行の反射なしの既存部品は filtered 閉性までを与える。
  無条件の生成表示を独立に完成する経路では、小さい前合成族の同値条件への
  accessible 逆像の生成性が必要になり、P が担当中の accessible 引き戻しと重なる。
- P-f の現行の置換構成は固定始域の生成射圏の accessibility を残している。
  局所対象圏の accessibility を入力にしていないため、この供給順は循環しない。
- 独立性を維持する判断なら、P の `pullback_isAccessible` の公開をユーザー経由で依頼し、
  元の小さい写像空間前合成族が同値となる部分圏への逆像として接続する。
  逆像模型・比較・監査は同定理の供給後 4〜10 時間の見積もり。
- いずれも現時点では無条件の accessibility の存在を仮定せず、定理としても主張しない。

## 検証と規約

- 所有集約8,299 jobs 成功。専用監査23宣言は標準三公理のみ。
- 所有 import 閉包4,656モジュール、他セッションの未コミット依存なし。
- 所有は Localization/LocalObjects/ の新規葉と集約、本計画、専用監査のみ。
- 既存の Localization と Presentable の葉・集約・監査は読み取り専用。
- 新規 sorry・公理・引用なし。主経路に ModelCategory SSet 仮定なし。
- 自分の集約と監査だけをビルドし、根のビルドと .lake の削除をしない。
- docstring は概要・方針・規約・使われ方。実施記録はコミットメッセージ本文。
- set -o pipefail と git commit --only を使い、他セッションの変更を stage しない。

# P-d：局所対象の accessibility

## 引き継ぎ

- 現在地：(1) HTT 5.5.4.2 の無条件 accessibility と
  (2) HTT 5.5.4.15(3) の条件付き presentability を証明・公開した。
- 残り：本割り当てにはなし。公開名をユーザー経由で P-f へ渡して停止する。
- 主要宣言：`isAccessible`、`isPresentable_of_reflection`、
  `isPresentable_of_localReplacements`、`exists_regular_inclusion_accessibilityCardinal`。
- 名前空間：`SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects`。
- 依存と提供：P-f の `bousfield_isReflectiveSubcategory` と
  `bousfieldLocalObjects_isPresentable` を読み取り専用で使用する。
  BousfieldReflection は条件付き定理の葉 Presentable だけを import するため循環しない。
- 未コミット：なし（本計画・新規 Accessible 葉・所有集約・専用監査を限定コミット）。
- 既知の問題：本割り当てにはなし。e5 一般版は別割り当てであり未完。
- 次の一手：P-f が公開された無条件 accessibility を消費する。
  e5 一般版はチェックポイント `b4611a01a` と未追跡の
  `AccessiblePullback/TrivialCosliceEndpoint.lean` を保持し、ユーザー指示まで停止。

## 三段目

1. l1：既存定義・反射・accessibility の公開界面を確認する（完了）。
2. l2：共通端点 compact 濃度、局所性の filtered 閉性、内部 filtered 余極限、
   包含の保存性を証明する（完了）。
3. l3：条件付き反射から presentability を公開し、P-f の Bousfield 反射の供給後に
   無条件 accessibility をその系として公開する（完了）。
4. l4：所有集約と専用監査を検証し、限定コミットと公開名を報告する（完了）。

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
- `Accessible`：P-f の構成した Bousfield 反射による presentability から
  元の局所対象圏の無条件 accessibility を取り出す。

## 公開界面と入力の区別

- `exists_regular_inclusion_accessibilityCardinal`：任意の下界を超える正則濃度で、
  元の局所対象圏の filtered 余極限と包含の filtered 保存を与える。反射入力なし。
  これは局所対象圏そのものの `IsAccessible` ではない。
- `isAccessible`：presentable C と小さい辺族だけで元の局所対象圏の accessibility を与える。
- `isAccessible_of_reflection`：presentable C、小さい辺族、既存の反射を入力に取る。
- `isPresentable_of_reflection`：同じ入力で元の局所対象圏の presentable 性を与える。
- `isPresentable_of_localReplacements`：既存の局所置換の存在条件を直接入力に取る。

## 採用した依存順

- ユーザー判断に従い (2) を先に P-f へ供給し、P-f の無条件の Bousfield 反射から
  `bousfieldLocalObjects_isPresentable` を得た後、`isAccessible` をその成分として閉じる。
- `isAccessible` の型は presentable C と小さい辺族だけを入力に取る。
  反射や局所置換の存在、accessible 引き戻し定理は仮定しない。
- `Accessible` は BousfieldReflection を読み、同モジュールは Presentable を読む。
  所有集約 All への逆依存はない。

## 検証と規約

- 所有集約9,538 jobs 成功。専用監査24宣言は標準三公理のみ。
- import 閉包5,849モジュールに他レーンの未コミット依存なし。
- 所有は Localization/LocalObjects/ の新規葉と集約、本計画、専用監査のみ。
- 既存の Localization と Presentable の葉・集約・監査は読み取り専用。
- 新規 sorry・公理・引用なし。主経路に ModelCategory SSet 仮定なし。
- 自分の集約と監査だけをビルドし、根のビルドと .lake の削除をしない。
- docstring は概要・方針・規約・使われ方。実施記録はコミットメッセージ本文。
- set -o pipefail と git commit --only を使い、他セッションの変更を stage しない。

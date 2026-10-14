# 共有ホモトピー論の契約（H0）

固定環境：Lean `v4.35.0-rc4`、Mathlib
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。
設計は `formalization-plans/k-theory.md` §123・§124。

## 基底の型と宇宙

- 圏は `C : Type u`、`Category.{v} C`。異なる圏の対象・射の宇宙は独立に保つ。
- 射のクラスはMathlibの `CategoryWithCofibrations`、`CategoryWithFibrations`、
  `CategoryWithWeakEquivalences` と `MorphismProperty C`。
- モデル構造は `HomotopicalAlgebra.ModelCategory C`。代替型を作らない。
- 随伴は `CategoryTheory.Adjunction`。Quillen条件は通常の関手上のPropとして追加する。
- ホモトピー圏は指定したWのMathlib局所化。導来関手・導来随伴は既存の
  `Functor.IsLeftDerivedFunctor` / `IsRightDerivedFunctor`、`Adjunction.derived`へ接続する。
- 図式の対象・射の宇宙 `w_obj`, `w_hom` と局所化先の宇宙は使用箇所で明示する。
  `ModelCategory`だけから任意小極限・余極限・関手的置換を取り出さない。
- モデル構造を複数選ぶ場合は局所instanceか射クラス選択用の型別名を使う。
  対象の定義を複製しない。Underの構造は基底の三クラスを忘却で引き戻す標準構造。

## 担当と依存

この系列はG0〜G8の共有一般論を所有する。M5側は任意可換環AのCh(A)、
dg圏・加群・局所化導来圏・tensor・商・Moritaと具体的検証を所有する。
Ch(A)固有の型・符号・smallnessの証拠をこのディレクトリへ埋め込まない。
M5の射影モデル比較D4mへQuillen・転送・monoidal一般論を供給する。
M5の局所化経路は共有転送の完成を待たず進められる。

`Foundations.lean`はこの系列専用の入口。共有ルート`SerrePositivity.lean`には追加しない。
具体的SSet・スペクトル・Ch(A)・論文の圏を一般論からimportしない。
一般論はsorry・引用axiomなし。当てはめの引用は別の`Inputs/`と引用台帳に置く。
既存Spectraのnamespace・宣言名・`StageTwo`の入口を保持する。
既存可換環論・CLMST・M5担当ファイルは変更しない。

## H0〜H2の受入と検証

H1は通常の随伴についてcof/trivial cof保存とfib/trivial fib保存の同値、
恒等関手・合成を扱う。H2はUnderの三クラス、二つの分解・lifting、
有限極限・余極限とMathlib ModelCategoryへの接続を扱う。
各単位で対象ビルド、公開APIの利用例、主要宣言を含むモジュール全宣言の公理監査を行う。
最後に既存 `scripts/check_spectra_stage2.lean` とスペクトル公理監査も再実行する。

## 完了したAPI（2026-10-14）

専用入口は `SerrePositivity.HomotopicalAlgebra.Foundations`。
H0〜H2は実装・ビルド・公理監査・既存API互換検証まで完了した。

| 単位 | 公開API | M5側からの利用 |
| --- | --- | --- |
| H1 | `SerrePositivity.Quillen.IsLeftQuillen`, `IsRightQuillen` | cof/trivial cof、fib/trivial fibの保存を既存MorphismProperty上で供給。クラス自体は保存性のみを表し、随伴の存在は通常のAdjunctionで別に渡す |
| H1 | `preserves_left_iff_preserves_right` | 任意の二つの弱分解系について、随伴による左右保存の同値。モデル構造・関手的分解は不要 |
| H1 | `isLeftQuillen_iff_isRightQuillen`, `isRightQuillen_of_isLeftQuillen`, `isLeftQuillen_of_isRightQuillen` | モデル圏間の通常随伴に適用。逆向き推論は明示的なlemmaで行い、循環するinstanceを登録しない |
| H1 | `isLeftQuillen_id/comp`, `isRightQuillen_id/comp`、四つの`map_*` lemma | 恒等・合成はinstance、個別の射の保存は明示的lemma。すべての弱同値の保存は主張しない |
| H2 | `HomotopicalAlgebra.ModelCategory.under`、`cofibrations_under_iff`, `fibrations_under_iff`, `weakEquivalences_under_iff` | 任意SのUnderへ標準構造を継承。Sのcofibrancy/fibrancyは不要。三クラスは基礎射`f.right`で判定 |
| H2 | `CategoryTheory.MorphismProperty.MapFactorizationData.under`, `HasFactorization.under` | 指定した基礎射の分解・一般の二クラスの分解をUnderへ移す |
| H2 | `CategoryTheory.CommSq.HasLift.under`, `HasLiftingProperty.under` | 基礎のsquareのlift・lifting propertyをUnderへ移す |

Underの有限極限は既存StructuredArrowの構成を明示的に特殊化した。
有限余極限は既存MathlibのUnder instanceを使用する。
ModelCategoryの二つの分解・lifting・retract・two-out-of-threeをすべて接続済み。

検証コマンド：

```sh
lake build SerrePositivity.HomotopicalAlgebra.Foundations SerrePositivity.Spectra.StageTwo SerrePositivity.Spectra.Foundations
lake env lean scripts/check_homotopical_foundations.lean
lake env lean scripts/audit_homotopical_foundations.lean
lake env lean scripts/check_spectra_stage2.lean
lake env lean scripts/audit_spectra.lean
```

すべて成功。新規一般論は4モジュール76宣言（内部補助宣言も含む）、
既存スペクトル・共有基盤は261モジュール2612宣言が標準公理
`propext`, `Classical.choice`, `Quot.sound`のみ。
新規監査は必須の4モジュールすべてが監査対象に含まれたことも検証する。
利用例は独立した宇宙、Quillen左右保存、Underの三クラスとtrivialクラス、
両分解・両lifting、有限極限余極限、二重UnderとStageTwoの併用を確認する。

コミット：H0 `b46de69`、H1 `d554602`、H2 `e382feb`。
次はH3（生成条件・転送認識）とH4（既存導来随伴への接続）。
M5はこの入口を利用できるが、dg加群のモデル構造・導来tensorのQuillen比較には
未実装のH3/G5/H4がなお必要。今回H3以降の完了を主張しない。

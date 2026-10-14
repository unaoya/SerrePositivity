# 一般対称スペクトル（H6）

入口：`SerrePositivity.Spectra.General.Foundations`。
既存単体的スペクトルとの比較：`SerrePositivity.Spectra.General.SimplicialComparison`。
固定環境はLean `v4.35.0-rc4`、Mathlib `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。

## 型と前提

`GeneralSymmetricSpectrum C K`は
`Mod (SymmetricSequence C) (SymmetricSequence.tensorPowerSequence K)`のabbrev。
既存のMathlib内部加群・Day convolution・テンソル冪の可換モノイドを使用する。
対象の宇宙と射の宇宙は独立な`C : Type u`, `Category.{v} C`。

Cに対称monoidal構造・閉構造・小さい余極限`HasColimitsOfSize.{0,0} C`を要求する。
Kにはcofibrancy、Cにはモデル構造・基点・零対象・単体的豊穣構造を要求しない。
既存のテンソル冪の括弧と置換作用の規約を保持する。

## 公開API

名前空間は`SerrePositivity.GeneralSymmetricSpectrum`。

| ファイル | APIと契約 |
| --- | --- |
| Basic | underlying, level, levelMap, forget, action, mk, homMk, hom_ext。作用の単位・結合・射との両立 |
| Free | freeObj K, freeFunctor K, generator K, lift K, freeHomEquiv K, freeForgetAdjunction K。生成元と延長の逆関係、unit/counit |
| Evaluation | evaluation (K := K) n, freeAt (K := K) n, freeAtAdjunction, freeAtHomEquiv, freeAtGenerator, freeAtLift。生成元の合成表示と延長の一意性 |
| Limits | 忘却による極限創出、評価の極限保存、limitLevelIsoと射影法則。指定した形の極限をCから継承 |
| Limitsの余極限 | Cの小さい極限を追加要求し、既存Day閉構造によるtensorの余極限保存から創出・保存を得る。指定した形の余極限をCから継承。colimitLevelIsoと包含法則 |
| SimplicialComparison | C=PointedSimplicialSet、K=circleで、旧SymmetricSpectrumの型・忘却・level・作用・free/evaluation・両随伴と定義上で一致 |

比較入口は具体的PSSをimportする。一般入口は具体的圏をimportしない。
旧namespace・宣言・import入口は変更していない。共有ルートimportにも追加していない。

## 検証と後続

```sh
lake build SerrePositivity.Spectra.General.Foundations SerrePositivity.Spectra.General.SimplicialComparison SerrePositivity.Spectra.StageTwo SerrePositivity.Spectra.Foundations
lake env lean scripts/check_general_spectra.lean
lake env lean scripts/audit_general_spectra.lean
lake env lean scripts/check_spectra_stage2.lean
lake env lean scripts/check_homotopical_foundations.lean
lake env lean scripts/audit_spectra.lean
```

すべて成功。一般スペクトルは5実装モジュール78宣言（内部補助を含む）、
スペクトルと共通基盤は266モジュール2679公開宣言。標準公理のみでsorry・引用依存なし。
集約ビルド2125ジョブ。任意C,Kの利用例と、旧StageTwo・H5入口を同時にimportした互換検証を含む。

H6は§123.6の一般対象・free/evaluation・旧特殊化比較の単位。
§123.4のS0とS1の入口を供給する。一般の構造射・各段の誘導表示（S2）、
tensor/closed/cotensor/作用の公開API一般化（S3）、豊穣構造（S4）、
レベル・安定モデル構造（S5）は後続単位である。
モデル圏の懸垂とK-tensorを同一視せず、安定性はここでは主張しない。

コミット：H6a `6321c83`、H6b `94c092b`。

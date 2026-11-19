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
| SimplicialComparison | 円周を座標とする具体版と、テンソル・内部 Hom・余テンソル・写像対象などを比較する |

比較入口は具体的PSSをimportする。一般入口は具体的圏をimportしない。
円周上の基本構成は一般版の特殊化を使う。具体版から一般版への宣言の対応は[段 1 の一覧](../../../research/cleanup-zero-base/spectra/stage1.csv)にある。

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

## 後続実装：構造射と自由各段（2026-10-15）

`StructureMaps`は一般Kの構造射と同変性・単位・結合・射との両立を提供する。
`FreeLevels`, `FreeLevelInduction`, `FreeLevelQuotient`は自由各段の分解・誘導・商と生成元の比較を提供する。
m<nの段は一般には始対象。零対象の主張にはHasZeroObject Cを要求する。
円への構造射・ブロック商比較の特殊化は旧APIと定義上で一致する。

入口と利用例を更新済み。一般公理監査は10モジュール138宣言（内部補助を含む）。
コミット`320ff01`, `0f85627`。段階2の作用・cotensor・豊穣の接続は後続。

レベルモデルの別入口は`SerrePositivity.Spectra.ModelCategory.LevelClasses`。
任意Pの全次数free像のrlpを各段のP.rlpと同定する。
この計算だけではモデル構造の存在は得られず、smallness・cell acyclicityの検証が後続に必要。
コミット`ae733ed`。専用利用例・全宣言公理監査は`check_spectrum_level_classes.lean`。

## 一般Cの作用・cotensor・写像対象（§133）

PointwiseTensorとCotensorは実際のSym(K)加群で、各段はX⊗E_nと[X,E_n]。
F_0との全体比較・随伴、作用単位・結同比較の自然性、両三角恒等式を提供する。
MappingObjectはスペクトル内部Homの第0段で、パラメータtensorを表現する。
ordinary HomはCの単位からの点と同値。cotensorとのHom同値も一致する。

円への対象・作用結同比較は旧APIと比較済み。StageTwoとの併用検証が成功。
一般監査14モジュール206宣言、全スペクトル監査284モジュール2832公開宣言が標準公理のみで通過。
新規利用例はcheck_general_tensor_cotensor.lean。コミット6c49348と026a1eb。
パラメータ自然性・全作用整合性と豊穣登録・H5/SM7接続は後続の証明対象。

## 一般C値の豊穣構造（§134）

`PointwiseTensorCoherence`はパラメータ射の各段公式、結合子の両パラメータ自然性、
pentagon・triangle・左単位則を提供する。
`MappingEnrichment`は既存のC値写像対象の評価を転置し、合成・単位・単位則・結合則を構成する。
`mappingEnrichedOrdinaryCategory`は既存の通常の加群圏との接続を含むMathlibの構造。
必要な箇所で`letI := mappingEnrichedOrdinaryCategory (C := C) (K := K)`として利用する。
そのHom対象はmappingObjectで、射の同値はordinaryHomEquivと定義上で一致する。
一般入口に含むが、グローバルinstanceとしては登録しない。

モデル構造は不要。豊穣Hom対象のtensor/cotensor表現性とH5 receiverへの接続、
スペクトル側SM7と具体的PSSモデル入力の検証は引き続き後続。

## パラメータ付き随伴（§135）

`ParametrizedCotensor`は作用とcotensorの二変数随伴、
`ParametrizedMapping`は作用のflipと既存mappingObjectBifunctorの二変数随伴を提供する。
いずれもMathlibのParametrizedAdjunctionで、objectwise随伴に加えてパラメータ自然性を証明した。
共有ParametrizedAdjunctionTransportは任意の圏での制限・左右の自然同型による移送を提供する。

eHomFunctorとの自然な比較によるH5 receiverへの接続と、C値Hom対象の表現性は引き続き後続。
一般スペクトル監査18モジュール265宣言、共有移送込み利用例監査254宣言が成功。
コミット31b0b5f・1e9b0ea。

## 豊穣写像関手の比較とH5 receiver（§136）

`MappingFunctorComparison`で構成した豊穣構造の両whiskeringが既存mappingObjectBifunctorの射と一致する。
`mappingEnrichedHomFunctorIso`はその両変数の自然な比較。
`TensorCotensorEnriched.spectrumTensorCotensor`は同じ作用・cotensor・豊穣構造上で
H5のEnriched.TensorCotensorを構成し、既存Hom同値との一致を証明する。
利用時にはmappingEnrichedOrdinaryCategoryを局所instanceとして装備する。

共有MappingWhiskeringは任意のVで評価の一意性から関手の射を比較する。
新規利用例・公理監査はcheck_general_tensor_cotensor.leanに含む。
一般監査20モジュール277宣言、共有補題込み利用例監査270宣言が成功。
コミットe01e093・174b3b5。Hom対象のEnrichedRepresentabilityと具体的SM7は引き続き後続。

## C値Hom対象の同型（§137）

TensorMappingObjectとCotensorMappingObjectは実際のC値Hom対象の同型を構成する。
それぞれmappingObject(pointwiseTensor X E,F)、mappingObject(E,cotensor X F)を
ihom XでmappingObject E Fを冪化した対象と比較する。
値域Fに自然で、任意パラメータZの転置を保つ法則を提供する。
共有ActionComparisonAdjunctionを異なる源・値域の圏の随伴へ一般化して再利用した。

一般監査22モジュール292宣言、共有比較込み利用例監査290宣言が成功。
コミットa132406・3daa093。源Eの自然性、Xの反変自然性と単位値点の両立を集約し、
EnrichedRepresentabilityへ登録する作業は後続。

## 両変数での豊穣Hom対象比較（§138）

TensorMappingSourceとCotensorMappingSourceで源Eの反変自然性を追加し、
両スペクトル変数でのmappingObject自然同型を構成した。
EnrichedMappingObjectsのtensorEnrichedMappingIso・cotensorEnrichedMappingIsoは、
H5の豊穣Hom関手からpowerHomへの二変数自然同型。
共有ActionComparisonNaturalityを異なる源・値域の圏にも一般化して利用する。

一般監査25モジュール304宣言、共有比較込み利用例監査309宣言が成功。
コミット6564adf・0f2d8fd。Xの反変自然性とordinary Hom点の両立を証明し、
EnrichedRepresentabilityへ登録する作業が残る。

## Hom対象比較のパラメータ反変自然性（§139）

TensorMappingParameter・CotensorMappingParameterは既存Hom対象同型のXに関する反変自然性を証明する。
EnrichedMappingParameterは各成分の比較と、H5のtensor_parameter・cotensor_parameterの法則を提供する。
残るEnrichedRepresentabilityの登録条件は通常の射の点についてのtensor_points・cotensor_points。
一般監査28モジュール314宣言、共有比較込み利用例監査319宣言が成功。コミットa7c54df。

## 豊穣表現性のreceiver完成（§140）

TensorMappingPointsとCotensorMappingPointsは通常の射の点と閉転置の両立を証明する。
EnrichedRepresentabilityのspectrumEnrichedRepresentabilityは、両変数自然同型・パラメータ法則・
両点の法則を持つH5の全フィールドを構成済み。
Hom対象比較の点は既存pointwiseTensorHomEquivに一致する。

一般監査31モジュール325宣言、共有比較込み利用例監査330宣言が成功。
コミット431f80e・dd56793。豊穣表現性の実装は完了し、モデル構造とのmonoidal/SM7適合は後続。


## 一般自由スペクトルのテンソルとレベルモデルへの適用（2026-10-16）

`TensorFreeAtSum`はSym(K)上の実際のbalanced tensorについて
F_m(X)⊗F_n(Y)≅F_(m+n)(X⊗Y)と両変数の自然性を構成する。
`FreePushoutProduct`はこの比較でpushout squareと出力射を移送し、自由生成射のpushout-productを
元のpushout-productの自由像とArrowの同型として比較する。両モジュールにモデル仮定はない。
`ModelCategory/GeneralLevelTensor`と`GeneralLevelEnriched`はこの計算を一般C,Kの元レベルモデルへ適用し、
pushout-productと実際のC作用・cotensor・eHomのSM7を証明した。
単位のcofibrancyはunitに関する十分条件として別に明示する。
受入`check_general_spectrum_level_monoidal`は26宣言・4モジュールを標準公理のみで監査。
実装`99e09cc7`。K局所化後の適合性は別の残項目であり、計画§217で区別している。


## 一般の次数シフト付きHomと随伴構造射（2026-10-16）

`ShiftedHom`は一般Sym(K)加群の作用を[X,E_(n+q)]へ実際に移送し、内部Hom(F_n(X),E)と比較する。
`ShiftedHomSuspension`は評価・元の懸垂構造射・出力のブロック交換による直接公式を証明する。
`ShiftedHomAdjoint`は随伴構造射を、元の随伴構造射への[X,-]の像と二つの同型の合成として記述する。
これらにモデル仮定は不要。`Stable/InternalHomOmega`はこの式とBrown補題から、
cofibrantなXについて次数シフト付きHom、実際の内部Hom(F_n(X),E)、cotensor(X,E)のΩ_K保存を証明する。
スペクトルのモデル構造や局所化はΩ_K保存の入力に含まない。
受入`check_general_spectrum_internal_hom_omega`は30宣言・5モジュールを標準公理のみで監査。
実装`06473b08`。局所化後のmonoidal/SM7への接続は計画§218。


## S3完了：通常の導来懸垂・ループの同値（2026-10-16）

`CircleSuspensionNaturality`と`DerivedSuspensionComparison`は通常のhomotopy pushout懸垂と
円tensorの左導来をホモトピー圏全体で自然同型にする。
`Stable/SimplicialStability`の`StableModelPresentation.exists_ordinarySuspensionLoopEquivalence`は
構成済み円局所化から、通常の導来懸垂を順関手、既存ループの右導来を逆関手とする同値を構成する。
局所化後の生成性・左固有性・SM7と円tensor可逆性は既存構成から取得する。
基点付き単体的集合の局所可呈示性も証明し、追加仮定に戻さない。
受入例は87宣言・8モジュールの標準公理監査とともに成功。
実装`459a6016`・`99696439`、詳細と全体の残項目は計画§223。

# K-cof：Thomason の共終性定理

## 引き継ぎ

### 現在地
- 二段目は任意の指定完備化射の一般共終性。主定理は未完成。
- D-22（57b4a57a4）、Sp-7（c85f08b8d）、Sp-8 (1)(2)（9b6037230）を実証明で消費済み。
- 指定完備化射は同じ全多次数の有限反復 S でも実際に冪等完備化。
- 元の相対旗は、wide 内へ全体として持ち上がる旗を頂点とする ambient 全関手圏の全部分圏。
  元の未置換零段と元の反復 S 対象の厳密同型は全多次数の構造射と可換。
- 相対 core 旗の対角評価は Δ[n] → Δ[n]×Δ[n] の対角制限。
  Sp-8 counit と rfl で一致。CompletionCoreFlagEvaluationInput を実証明で消去済み。
- 本質像を全多次数の ClosedStablePredicate として実装。元の始域との安定模型同値、
  S 交換同型、全 Ar 像条件、元の指定 K 射への比較を実装済み。
- wide 成分は双積和による可換群で、元の K₀ 余核と全多次数で自然に群同型。
- 元の区間制限・全ての面と退化による S 余核の bar 同型を構成済み。
  群 nerve の高次消滅へ Sp-8 (2) を代入済み。
- 元の自然な成分射影は全多次数で弱同値。元の相対先頭実現の二次以上の消滅を、
  Sp-8 (1)(2) の追加仮定なしで公開済み。
- K-B2-S1 は採用・発注済み。公開された明示入力付き相対四角形の正確な121葉閉包を消費。
  本質像を代入した供給側 R_P と元の相対旗の包含を保つ厳密同型・安定模型同型を構成。
- 元の相対旗の S 転置は、全 Ar 評価の分母判定で次段の元の相対旗へ持ち上がる。
  逆転置も全 Ar 成分で元の相対旗へ入り、全部分圏から gapped 性を反映する。
  completionRelativeSInterchangeIso で往復が厳密に恒等となる同型を構成済み。
  二方向の全ての面・退化の自然性を示し、供給側の元の相対実現との同型へ接続。
  completionClosedRelative_higher_subsingleton は供給右項の任意基点の高次消滅。
  同じ右項の Ex∞ 模型にも任意基点での実消滅を移送済み。
- 相対 fiber 本体の全旗自然性は未供給。公開された条件付き四角形を明示 Prop 引数で消費。
  元の包含の Kan 四角形、実引き戻し比較、射影回収、入力下の全基点 π 同型を接続。
  完備化前の K-6 と循環しない読み取り専用閉包だけを使用する。

### 残り（三段目、依存順）
1. [x] 所有閉包・指定 K 射・比較入口の確認。
2. [x] D-22 を全多次数へ代入し、反復 S の実完備化証拠を構成。
3. [ ] 相対 S• の実現比較（HLS §7.1、残り6〜10時間）。
   相対旗 S 交換と供給右項の実現同型は完了。Kan 四角形・相対 fiber を接続する。
4. [ ] 正次数全単射・零次単射（HLS §7.1、5〜8時間）。
5. [ ] 同じ kSpectrumMap f への照合と一般形公開（TT 1.10.1、3〜6時間）。
6. [ ] 自所有集約・監査・型仮定検査・限定コミット（2〜5時間）。
- 初期総見積り24〜40時間。現在の実装は主定理の二段目完了とはしない。

### 主要宣言
- Cofinality.completionCoreFlagEvaluationInput
- Cofinality.groupNerveHigherVanishingInput
- Cofinality.completionRelativeHead_higher_subsingleton
- Cofinality.completionRelativeFlagWideEvaluation_isWeak
- Cofinality.cutCokernelBarIso
- Cofinality.completionWideKZeroObstructionEquiv
- Cofinality.completionClosedFlagStableIso
- Cofinality.completionRelativeSTranspose
- Cofinality.completionClosedRelativeRealizationIso
- Cofinality.completionClosedRelative_higher_subsingleton

### 依存と提供
- 所有：KST/SConstruction/Cofinality/ 新規葉、同名集約、
  scripts/audit_kst_cofinality.lean、本計画（300行以内）。
- 読取専用：既存 SConstruction、F2/Idempotent、Stable/D-22、Sp/LocalizingInvariants。
  Fibration は採用済み旗定義の正確な121葉閉包だけを監査で許可。NonConnective は不使用。
- InfinityCategories、既存 SConstruction・他レーンの集約・監査は編集しない。

### 保存範囲・未コミット
- 1753deeff：元の全多単体的 wide 成分図式と K₀ 余核図式の自然同型。
- 0c5d6b4ea：元の区間制限・切断による K₀ とその余核の直積分解。
- 1d7d3618c：元の S 余核の bar 同型と条件付き高次消滅。
- 202d72e78：元の相対先頭実現への条件付き高次消滅の接続。
- fd7a87922：Sp-8 実消費、K-B2 の旗同型と元の相対旗の S 転置・逆転置。
- 今回：供給側の相対実現との同型・元の右項の無条件な高次消滅、
  明示入力付きの元の Kan 四角形・射影回収・可縮な核の全次数消滅。
  所有葉・集約・監査・本計画を限定保存する。実施記録はコミット本文。

### 既知の問題
- 主共終性・相対 fiber 本体・元の包含の Kan 完全列への接続は未完成。
- F ⊕ ΣF の像回収から元の F の像回収や K 射の正次数同型を推論しない。
- 主経路に始域の完備性・全射 K₀・ModelCategory SSet を追加しない。
- 検証済み：集約ビルド成功（8924 jobs）、97モジュール・674宣言の公理監査成功。
  標準三公理のみ、型の ModelCategory 仮定・禁止 import・新規 sorry・公理なし。

### 次の一手
- 一般 Kan 引き戻しの射影の群条件の追加供給をユーザー経由で提案（末尾、未採用）。
  採用時は元の Kan 四角形へ代入し、元の境界 K 空間との loop 比較を接続する。
- K-B2-S1 の相対 fiber 本体到着後、元の相対先頭実現の無条件な高次消滅を代入する。
  元の kSpectrumMap の正次数全単射・零次単射は未完。

## 目標型

```lean
∀ (X Y : StableModel.{u}) (f : X ⟶ Y),
  F2.Idempotent.IsIdempotentCompletion f.val →
    (∀ j : ℤ, 0 < j →
      Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
    Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0)
```

## 採用済みの一般供給

- D-22：指定完備化射 `f : C ⟶ D` の各 `d : ho D` について、
  `d ⊕ Σd ≅ (ho f).obj c` となる c を供給。実装を消費済み。
- Sp-7：安定 quasicategory の指定完備化射 f、本質像 P、
  `W = cofiberLocalizingEdges P` について、全辺が W に属する単体からなる部分複体 M、
  M の quasicategory 性、`continuousKanReplacement.obj M` の正次数の自明性。
  `LocalizingInvariants.idempotentCompletion_cofiberWide_discrete` を消費済み。
- 正確な消費型は `WideStageData` と `stableWideCofinalitySupply_of_api` が正本。
  型を単に記録しただけで、一般供給が届いたことにはしない。
- K-B2-S1 の公開旗定義 ClosedRealizationPullback の120葉と既存の一点 π 比較1葉の閉包を読み取り専用で消費済み。
  fiber 本体の到着とは区別する。

## 採用済み Sp-8：一般 core 旗比較を Sp 正本で供給

- ユーザー経由の依頼先：独立レーン Sp-8（採用・発注済み）。
- 理由：相対旗は ambient 関手圏の全部分複体であり、その core の対角実現と
  M の亜群化は定義的に等しくない。Sp-7 が離散性を与えるのは後者。
  必要な一般亜群化比較を K-cof の新規一般補題として複製しない（foundations §8 正本規約）。
- 供給仕様：任意の quasicategory C について
  `R(C)[n] = core Fun(Δ[n], C)` を、標準単体の前合成で単体的に束ねる。
  `diag R(C) ⟶ C` の対角評価 ε を構成し、
  `InfinityCategories.IsWeakHomotopyEquivalence ε` を証明する。
  ε は C の任意の関手による後合成で自然。零旗からの射を含め、元の評価を保持する。
- 対角は一般の定義
  `Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (R C)` を使用できる。
  KST/SConstruction の対角関手を import する必要はない。
- K-cof 側の消費：M 内部の旗の core と、実装した ambient 相対旗の core を比較。
  wide の辺条件と全可逆辺の所属からこの比較を作り、供給された自然な弱同値を使う。
  その後の S• 固有の相対実現、加法的 fiber 比較、障害の群同定は K-cof が担当する。
- 見積り：一般 core 旗比較4〜8時間（K-cof 推定）。
  この追加だけでも主定理は完成しない。相対実現の fiber 比較を別に証明する。
- 原典：Hebestreit–Lachmann–Steimle §7.1 第一証明の core と実現の交換。
  <https://arxiv.org/pdf/2205.06104#page=20>

## 採用済み K-B2-S1：商比較前の相対 fiber 本体

- 理由：HLS §7.1 第一証明の fiber 列は同論文2.7（Waldhausen）を使用する。
  Sp-8 は各全多次数の評価・離散性を供給し、この fiber 列を供給しない。
  K-B 既存の `weakStringConstantPostSquare_homotopyPullback` と
  `relativeSFibrationFiberIso` は `IsVerdierSequence i q` を要求する。
  完備化の本質像を商関手の厳密な核とみなすことはできず、そのまま代入できない。
- ユーザー経由で K-B2 へ発注済み。完備化前の相対加法性から閉じた安定部分圏版を切り出す。
  入力は `B : StableModel` と `P : ClosedStablePredicate B` のみ。
  `W = cofiberLocalizingEdges {x | P.predicate x}`、
  `R_P[n]` は `Fun(Δ[n], B)` の、W 内へ全体として持ち上がる旗の全部分圏。
  `F = coreSRealizationFunctor` として、定数旗からの元の射 `c_B` に対する
  `Q.obj (F.obj (closedStableModel P)) ≅ Q.obj (homotopyFiber c_B)` を供給する。
  同型の順射と fiber 射影の合成は、元の `Q.map (F.map (closedStableInclusion P))`。
  右辺は指定した零旗を基点とし、同じ合成の零化ホモトピーも保持する。
- 境界：商実現比較・`IsVerdierSequence`・冪等完備化・共終性を仮定しない。
  K-B の新規狭い葉は Cofinality と NonConnective を import しないことを供給条件とする。
  既存2葉の局所 import 閉包を調べ、Cofinality/NonConnective が無いことは確認済み。
  K-cof → 相対 fiber 共通葉 → K-S• 加法性の向きなら循環しない。
- K-cof が保持する仕事：本質像 P の代入、全 S 多次数との交換、Sp-8 消費、
  離散的障害の商群同定、同じ元の `kSpectrumMap f` の正次数全単射・零次単射。
- 見積り：共通葉の切り出しと一般化3〜6時間、K-cof の消費・照合2〜4時間。
  ユーザーが採用・発注を明示。K-cof は左項・全多次数の代入側を続行する。


## 採用済み Sp-8 (2)：一般 BG の高次ホモトピー消滅

- Sp-8 (2) は 9b6037230 で到着し、groupNerveHigherVanishingInput へ実証明を代入済み。
- 必要型：任意の `G : Type u`、`[Group G]`、`n : ℕ`、`1 < n`、基点 x について
  `Subsingleton (Spectra.KanHomotopy (F2.continuousKanReplacement.obj
    (nerve (AsSmall (SingleObj G)))) n x)`。
- `Spectra/GroupNerveCoordinates` と `GroupNerveFaces` の座標・面公式を確認したが、
  同じ一般消滅定理は KST の検索で見つからなかった。
- 提案理由：一般の群 nerve のホモトピー計算を読み取り専用の Spectra 正本に追加する分担。
  foundations §6 の Sp 所有と §8 運用 v3(2) に基づく分担変更案。
  既存の Sp-8・K-B2-S1 の仕様や主結論の仮定は変更しない。
- K-cof は元の全 S 余核図式の bar 同定、供給の代入、元の相対 fiber と K 射への接続を担当。
  `GroupNerveHigherVanishingInput` を明示的な仮定として保持。
  一方向の `cutCokernelBarIso` と条件付きの高次消滅を構成済み。
  元の全多次数相対旗の先頭実現へ条件付き高次消滅を接続済み。fiber 比較と主共終性は未完。
- 見積り：供給2〜4時間、K-cof 消費1〜3時間。


## 提案中：一般 Kan 引き戻しの第一射影の群条件（未採用）

- Sp への追加供給をユーザー経由で提案する。一般空間の完全列の計算は Spectra 正本。
- 正確な型は `Cofinality.KanPullbackCofinalityInput`。公理ではなく Prop 値の明示入力。
- 入力：Kan 複体 P, X, E, B、元の厳密 pullback 四角形 (q,s,g,p)、p の全 horn RLP、
  E の全基点・全次数のホモトピーの一意性、B の全基点で二次以上の一意性。
- 出力：任意の a : P₀ で元の q の π₁ が単射、全 n>1 で π_n が全単射。
  ModelCategory SSet の instance や基点の選び直しを追加仮定にしない。
- 既存の Spectra/FibrationExactness・FibrationNaturality は完全列と fiberMap を供給する。
  そのまま渡せる一般 pullback 射影のこの群条件は検索で見つかっていない。
- K-cof は元の相対実現の同型・両角の消滅・元の包含の Kan 比較を保持する。
  一般供給には SConstruction/Cofinality を import させない。
- 見積り：一般供給2〜4時間、元の相対四角形への代入と K 境界比較2〜4時間。
- foundations §6 の Sp 所有、§8 運用 v3(2)(4) に基づく分担変更の提案。
  主結論にこの入力を残す変更ではない。設計提案時の規約に従い停止する。

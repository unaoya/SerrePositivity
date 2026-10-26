# K-cof：Thomason の共終性定理

## 引き継ぎ

### 現在地
- 二段目は任意の指定完備化射の一般共終性。主定理は未完成。
- K-B2-S1 採用・発注済み（末尾）。現在の import は K-6 非依存、実供給は未到着。
- 06:29 採用の D-22（`Stable/IdempotentCompletionDensity`）を消費済み。
  同じ全多次数の有限反復 S で双積懸垂の像回収と全パラメータ族の回収を実装。
- **08:16 採用・再開**：HLS §7.1 の wide 部分圏の亜群化経路を採用。
  一般の wide 部分複体と亜群化の離散性は Sp-7 として Sp に発注済み。
  **09:03 到着（c85f08b8d）**：公開定理を読み取り専用 import し、実証明を代入済み。
- Sp-7 の結論を `StableWideCofinalitySupply` として明示的な仮定引数に取り、
  一般供給からの変換 `stableWideCofinalitySupply_of_api` も実装。
  `stableWideCofinalitySupply` で供給仮定を消去済み。一般共終性は未証明。
- 反復 S の標的の完備性を第一行同値から移し、D-22 から retract 条件を作った。
  したがって同じ指定射の全多次数の反復 S も実際に冪等完備化となる。
- Sp-7 の供給値から全多次数の厳密な wide 図式と元の S 図式への自然包含を構成。
  選択の自然性を仮定せず、全辺の cofiber 条件の保存で面・退化を構成する。
- 相対旗は wide 内部 Hom の頂点像を持つ ambient 関手圏の**全部分複体**。
  旗間の射は ambient の全射を保持。全 S 多次数と旗方向で厳密な図式に束ねた。
- 旗の未置換零段と元の同じ反復 S 対象との厳密な同型を構成。
  この比較は全多次数の構造射と可換。始域の旗を相対旗へ写す射も実装し、
  零段の比較後に元の指定反復 S 射を厳密に回収する。
- 実供給を代入した相対 core 旗の対角実現から、Sp-7 の具体的な wide 模型への
  全評価射を構成。水平辺・可逆な垂直辺・斜辺を検査し、全単体を持ち上げた。
  対角評価は包含後に元の評価を回収し、零単体で未置換零段比較と一致する。
- 同じ wide 成分内の本質像所属の同値を証明。連結なパラメータの一頂点が像に入れば
  全図式を同じ反復 S 射の始域へ一つの関手同型で回収できる。
- 選択した wide 模型を Sp の全辺模型と同定し、成分への実切断・全収縮も消費した。
- 実際の相対旗の頂点から wide 持ち上げを取り出し、連結な旗の一頂点の像所属から
  同じ相対旗圏内で始域の旗との頂点同型を回収。逆向きの判定も実装。
- 一頂点が像に入る相対旗の全部分圏と、元の始域の全旗圏との圏同値を構成。
  順方向の実射とその core 射が同値。像部分の安定性も移送済み。
- 元の `kSpectrumMap` の目標条件と未置換零段の群条件との同値は既存の自所有葉に実装済み。
- **Sp-8 採用済み**：一般 core 旗比較は独立レーンへ発注済み。実供給は未到着。
  評価は Δ[n] → Δ[n]×Δ[n] の対角制限と `rfl` で一致。変更不要。
- 内部 wide 旗と ambient 相対旗の core の自然同型、および対角同型を構成済み。
  ambient core 全体の wide への持ち上げから、可逆辺を wide 内へ反映する。
- `CompletionCoreFlagEvaluationInput` を明示的に受け取れば、同じ元の
  `completionRelativeFlagWideEvaluation` の弱同値性を結論する接続を検証済み。
  Kan 置換の全正次数の一意性まで接続。一般供給を公理や instance にしない。
- 連結な相対旗の回収障害を具体的 wide 模型の成分へ降ろし、元の始域像が
  任意の始域頂点の像の基点成分そのものであることを証明済み。
- 本質像を全多次数の `ClosedStablePredicate` として実装。元の始域との安定模型同値、
  S 交換同型、全 Ar 像条件との同値、全多次数の厳密な自然変換を構成済み。
- 本質像包含の各整数 K 群の全単射性・単射性を元の指定射と同値にした。
  wide 成分は双積和による可換群となり、元の三角圏 K₀ 余核と全多次数で自然に群同型。
- 元の S_n の左右の区間制限による K₀ 直積同型と、指定射の K₀ 余核の直積同型を構成。
  全面・退化を含む一方向の bar 同型を構成。Sp-8 (2) 入力下で二次以上の消滅まで接続。

### 残り（三段目、依存順）
1. [x] 所有閉包・指定 K 射・比較入口の確認。
2. [x] D-22 を同じ全多次数へ代入し、反復 S の実完備化証拠を構成。
3. [ ] 相対 S• の実現比較（HLS §7.1 第一証明、残り8〜12時間）。
   一般 core 旗比較の供給を消費し、相対図式の実現、加法的 fiber 比較、障害の同定を行う。
4. [ ] 正次数全単射・零次単射（HLS §7.1、5〜8時間）。
5. [ ] 同じ `kSpectrumMap f` への照合と一般形公開（TT 1.10.1、3〜6時間）。
6. [ ] 自分の集約・監査・型仮定検査・限定コミット（2〜5時間）。
- 初期総見積り24〜40時間。現在の実装は主定理の二段目完了とはしない。

### 主要宣言
- `Cofinality.cutCokernelBarIso`
- `Cofinality.cutCokernelEquiv`
- `Cofinality.completionWideKZeroObstructionEquiv`
- `Cofinality.completionRelativeFlagWideEvaluation`
- `Cofinality.completionWideComponentCokernelNatIso`
- `Cofinality.completionWideRelativeFlagDiagonalIso`
- `Cofinality.completionRelativeFlagWideEvaluation_isWeak_of_input`
- `Cofinality.completionMultiWide_componentRetraction`

### 依存と提供
- 所有：`KST/SConstruction/Cofinality/` の新規葉、同名集約、
  `scripts/audit_kst_cofinality.lean`、本計画（300行以内）。
- 読取専用：既存 SConstruction の第一行同値・実 K 段比較・一点関手評価、
  F2/Idempotent の全関手圏の完備性・図式回収、Stable の D-22。
- 一般局所化・亜群化 API は Sp 正本。現時点で Fibration・NonConnective は import なし。
  InfinityCategories と既存 SConstruction は編集しない。
- K-B 向けの主定理は未供給。完備始域の特殊場合で代用しない。

### 保存範囲
- `1753deeff`：元の全多単体的 wide 成分図式と K₀ 余核図式の自然同型。
- `0c5d6b4ea`：元の区間制限・切断からの K₀ および K₀ 余核の直積分解。
  今回の保存：元の一方向 S 余核と群 nerve の厳密同型および条件付き高次消滅。

### 既知の問題
- 一般共終性・相対 fiber 比較・一方向 bar と元の全多方向障害実現との接続は未証明。
- `F ⊕ ΣF` の像回収から元の F の像回収や元の K 射の正次数同型を推論しない。
- wide の亜群化の離散性と core 相対旗の実現の離散性は別の命題。
- 主経路に始域の完備性・全射 K₀・`ModelCategory SSet` を追加しない。
- 自所有集約ビルド成功（7907 jobs）。公理監査成功（64モジュール・545宣言、標準公理のみ）。
  型の ModelCategory 仮定・K-B への禁止 import なし。新規 sorry・公理なし。
- 根のビルドや `.lake` 削除はしない。

### 次の一手
- Sp-8 の到着後に `CompletionCoreFlagEvaluationInput` へ実供給を代入する。
  それまでは、この入力を明示的な引数にして相対 fiber 比較と障害の同定を続行する。
- 本質像を ClosedStablePredicate として代入し、全 S 多次数の像比較を接続する。
  一方向の元の余核の bar 同型は実装済み。全多方向障害実現への接続と主共終性は未完。
- 一般 BG の高次ホモトピー消滅は Sp-8 (2) として採用・発注済み（末尾）。
  到着まで明示仮定を保持し、元の S 余核図式の bar 同定を続行する。

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
- K-B2-S1 の依存追加は未実施。到着後に狭い供給葉を読み取り専用で使う。

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

- ユーザーが採用し、Sp-8 (2) として Sp-8 に発注済み。実供給は未到着。
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
  元の全多方向障害実現との照合と主共終性は未完。
- 見積り：供給2〜4時間、K-cof 消費1〜3時間。

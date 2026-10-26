# K-cof：Thomason の共終性定理

## 引き継ぎ

### 停止状態・最新コミット
- コーディネータのレーン再編指示により停止準備を完了し、再開指示を待つ。
- 最新実装コミット：3839a204d。直前保存：8ff1ace3c。
  この引き継ぎの保存コミットは停止報告で通知する。
- 二段目は任意の指定完備化射の一般共終性。無条件の主定理は未完成。
- 検証：自所有集約ビルド成功（8956 jobs）、専用監査成功
  （107モジュール・701宣言、標準三公理のみ）、所有範囲の diff --check 成功。

### 現在地
- D-22（57b4a57a4）、Sp-7（c85f08b8d）、Sp-8 (1)(2)（9b6037230）、
  Sp-8 (3)（b9bffc3c9）を実証明で消費済み。
- 指定完備化射の同じ全多次数の有限反復 S に対する完備化証拠、
  本質像 ClosedStablePredicate、元の始域との安定模型同値・S 交換を実装済み。
- 相対 core 旗の対角評価は Δ[n] → Δ[n]×Δ[n] の対角制限で、Sp-8 counit と rfl で一致。
- wide 成分の可換群は元の K₀ 余核と全多次数で自然に群同型。
  元の区間制限・面・退化を保つ S 余核の bar 同型と、相対先頭実現の高次消滅を構成済み。
- 相対旗の全 Ar 転置と逆転置、二方向の面・退化の自然性を証明。
  K-B2 供給側 R_P の元の相対実現との厳密同型へ接続済み。
  右項の任意基点の高次消滅を continuousKanReplacement と Ex∞ の双方で証明済み。
- 元の Kan 四角形・射影回収・可縮な核を接続し、Sp-8 (3) を実代入済み。
  相対 fiber 入力から元の本質像包含の π₁ 単射・二次以上全単射を得る。
- 元の core S 実現から境界商・Ex∞・SOA Kan・loop 空間への自然な比較を接続。
  同じ元の kSpectrumMap f の正次数全単射・零次単射まで到達した。
- 公開名 Cofinality.kSpectrumMap_cofinality_of_relativeFiber_input の唯一の残存入力は
  Fibration.Relative.ClosedStableFlagPostPullback
  (completionImageClosedPredicate 0 Fin.elim0 f hf)。K-B2-S1 の未供給本体である。
  Sp-8 (1)(2)(3) の明示仮定はこの公開名には残っていない。

### 残り（三段目、依存順）
1. K-B2-S1 の相対全旗自然性・fiber 本体と上流 WeakString 共通化の供給を確認する。
2. 本質像 P の ClosedStableFlagPostPullback を実証明で代入し、無条件の主共終性を公開する。
3. 元の指定 kSpectrumMap f の型・追加仮定なしを確認し、自所有集約・専用監査を再実行する。
4. 所有ファイルのみ限定保存し、公開名をユーザー経由で報告する。
- 残る K-cof 側の消費・照合の見積り2〜4時間（供給待ちを除く）。
  現時点を主定理の二段目完了とはしない。

### 依存と import 境界
- 所有：KST/SConstruction/Cofinality/ 新規葉、同名集約、専用監査、本計画。
- 既存 SConstruction・InfinityCategories・他レーンの集約・監査は読み取り専用。
  Fibration は監査の正確な121葉閉包だけを許可。NonConnective は不使用。
- Sp-8 (3) は独立入口 CoreFlag.KanPullbackAll から消費。
  一般補助葉は入力定義に非依存、互換定理のみ Cofinality の入力定義を import する。
  入力定義・旧 CoreFlag.All は KanPullbackAll と K-cof 消費葉を import しない。
  新消費葉の局所 import 閉包5532モジュールの非循環を確認済み。
- K-B2 共通葉は Cofinality/NonConnective を import せず、完備化前 K-6 と循環しない。
- 始域の完備性・全射 K₀・ModelCategory SSet を主経路へ追加しない。

### 未送付の供給依頼・設計提案
- なし。K-B2-S1 は既に採用・発注済みであり、残る既存依頼はその供給のみ。
- Sp-8 (3) は到着・消費済み。追加の分担変更は提案していない。

### 未追跡のまま残す所有ファイル
- なし。今回の新規10葉はすべて集約ビルド・専用監査を通過して3839a204dに保存済み。
  ビルド不能な作業中ファイルもない。他レーンの未追跡ファイルは対象外。

### 再開の第一工程
- K-B2-S1 の ClosedStableFlagPostPullback の実証明が到着しているかを確認する。
  到着後、KanPullbackSupply の kSpectrumMap_cofinality_of_relativeFiber_input へ代入する。
  供給が未到着なら新規項目へ進まず、再開時の指示に従う。

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


## 採用済み Sp-8 (3)：一般 Kan 引き戻しの第一射影の群条件

- Sp-8 (3) は b9bffc3c9 で到着し、KanPullbackSupply で実証明を消費済み。
- 正確な型は `Cofinality.KanPullbackCofinalityInput`。公理ではなく Prop 値の明示入力。
- 入力：Kan 複体 P, X, E, B、元の厳密 pullback 四角形 (q,s,g,p)、p の全 horn RLP、
  E の全基点・全次数のホモトピーの一意性、B の全基点で二次以上の一意性。
- 出力：任意の a : P₀ で元の q の π₁ が単射、全 n>1 で π_n が全単射。
  ModelCategory SSet の instance や基点の選び直しを追加仮定にしない。
- 既存の Spectra/FibrationExactness・FibrationNaturality は完全列と fiberMap を供給する。
  そのまま渡せる一般 pullback 射影のこの群条件は検索で見つかっていない。
- K-cof は元の相対実現の同型・両角の消滅・元の包含の Kan 比較を保持する。
  一般補助葉は入力定義に非依存。互換定理の入力定義への import は独立集約に隔離する。
  旧 CoreFlag.All と入力定義から KanPullbackAll・消費葉への逆 import を禁止する。
- 見積り：一般供給2〜4時間、元の相対四角形への代入と K 境界比較2〜4時間。
- foundations §6 の Sp 所有、§8 運用 v3(2)(4) に基づく分担変更の提案。
  主結論にこの入力を残す変更ではない。実証明を代入し、K 境界比較も接続済み。

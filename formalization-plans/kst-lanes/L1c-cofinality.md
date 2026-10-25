# K-cof：Thomason の共終性定理

## 引き継ぎ

### 現在地
- 二段目は任意の指定完備化射の一般共終性。主定理は未完成。
- K-6 に依存しない S• 直接経路。K-B の完備化前 fibration との逆依存はない。
- 06:29 採用の D-22（`Stable/IdempotentCompletionDensity`）を消費済み。
  同じ全多次数の有限反復 S で双積懸垂の像回収と全パラメータ族の回収を実装。
- **08:16 採用・再開**：HLS §7.1 の wide 部分圏の亜群化経路を採用。
  一般の wide 部分複体と亜群化の離散性は Sp-7 として Sp に発注済み。
- Sp-7 の結論を `StableWideCofinalitySupply` として明示的な仮定引数に取り、
  一般供給からの変換 `stableWideCofinalitySupply_of_api` も実装。
  この仮定の証明や一般共終性を供給済みとは数えない。
- 反復 S の標的の完備性を第一行同値から移し、D-22 から retract 条件を作った。
  したがって同じ指定射の全多次数の反復 S も実際に冪等完備化となる。
- Sp-7 の供給値から全多次数の厳密な wide 図式と元の S 図式への自然包含を構成。
  選択の自然性を仮定せず、全辺の cofiber 条件の保存で面・退化を構成する。
- 相対旗は wide 内部 Hom の頂点像を持つ ambient 関手圏の**全部分複体**。
  旗間の射は ambient の全射を保持。全 S 多次数と旗方向で厳密な図式に束ねた。
- 旗の未置換零段と元の同じ反復 S 対象との厳密な同型を構成。
  この比較は全多次数の構造射と可換。始域の旗を相対旗へ写す射も実装し、
  零段の比較後に元の指定反復 S 射を厳密に回収する。
- 元の `kSpectrumMap` の目標条件と未置換零段の群条件との同値は既存の自所有葉に実装済み。
- **設計供給境界の追加提案**：core 旗の対角実現と亜群化を結ぶ一般比較が必要。
  Sp-7 の離散性だけから相対旗の実現の離散性を結論しない。依頼の詳細は末尾。
  ユーザー経由での中継を明示的に依頼する。追加は未採用・未供給。

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
- `Cofinality.multiSEndofunctor_map_isIdempotentCompletion`
- `Cofinality.StableWideCofinalitySupply`
- `Cofinality.stableWideCofinalitySupply_of_api`
- `Cofinality.multiWideStageDiagram`
- `Cofinality.multiWideStageInclusion`
- `Cofinality.suppliedMultiRelativeFlagDiagram`
- `Cofinality.multiRelativeFlagZeroIso`
- `Cofinality.suppliedMultiRelativeFlagsMap_zero`
- `Cofinality.multiSourceToRelativeFlags_zero`
- `Cofinality.kSpectrumMap_cofinality_iff_boundary`

### 依存と提供
- 所有：`KST/SConstruction/Cofinality/` の新規葉、同名集約、
  `scripts/audit_kst_cofinality.lean`、本計画（300行以内）。
- 読取専用：既存 SConstruction の第一行同値・実 K 段比較・一点関手評価、
  F2/Idempotent の全関手圏の完備性・図式回収、Stable の D-22。
- 一般局所化・亜群化 API は Sp 正本。KST/Fibration・NonConnective は import しない。
  InfinityCategories と既存 SConstruction は編集しない。
- K-B 向けの主定理は未供給。完備始域の特殊場合で代用しない。

### 未コミット
- なし。自所有の新規8葉・集約・監査・計画を限定コミット。実施記録はコミット本文。

### 既知の問題
- 一般の共終性、相対実現の fiber 比較、離散的障害の群同定は未証明。
- `F ⊕ ΣF` の像回収から元の F の像回収や元の K 射の正次数同型を推論しない。
- wide の亜群化の離散性と core 相対旗の実現の離散性は別の命題。
- 主経路に始域の完備性・全射 K₀・`ModelCategory SSet` を追加しない。
- 自所有集約ビルド成功（7780 jobs）。監査は17所有葉の全125宣言で標準三公理のみ。
  型の ModelCategory 仮定・K-B への禁止 import なし。新規 sorry・公理なし。
- 根のビルドや `.lake` 削除はしない。

### 次の一手
- ユーザー経由で Sp への一般 core 旗比較の追加分担が採用されたら、
  その API を明示的な仮定引数にして、相対 core 旗と wide 内部旗の比較を続行。
- Sp-7 の公開名が届いたら `stableWideCofinalitySupply_of_api` に代入する。
  次いで相対実現の加法的 fiber 比較と障害の同定へ進む。

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
- 正確な消費型は `WideStageData` と `stableWideCofinalitySupply_of_api` が正本。
  型を単に記録しただけで、一般供給が届いたことにはしない。
- K-6 の fibration 定理への依存追加は行わない。

## 追加設計提案：一般 core 旗比較を Sp 正本で供給

- ユーザー経由の依頼先：Sp。Sp-7 への追加または独立の新規葉。
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

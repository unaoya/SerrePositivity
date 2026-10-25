# K-cof：Thomason の共終性定理

## 引き継ぎ

### 現在地
- K-S•-S2 を担当。目標は任意の `StableModel.{u}` 間の指定完備化射について、
  元の `kSpectrumMap` の全正整数次数での全単射性と零次での単射性。
- K-6 の fibration 定理を使わない S• 直接経路で開始。
  K-B の完備化前 fibration → 共終性 → 固定 K 比較という採用済み設計に逆依存を作らない。
- 完備始域の特殊場合を `Cofinality/CompleteSource` に実装。
  指定射を保持し、retract 閉性 → 実同値 → 全整数 π 同型へ接続。
  一般の非完備始域についての共終性とは数えない。
- 零次単射性と同じ完全関手の三角圏 K₀ 単射性の同値を `ZeroComparison` に実装。
  dense 包含の K₀ 単射性そのものは未証明。
- 同じ完全射の全 S_n と独立な全多次数の反復 S の充満忠実性を実装・検証。
- **設計変更提案で停止**：三段目2の一般安定圏の補対象部分を D 所有の新規葉へ分離する案。
  下の依頼型は Lean で検査済み。ユーザーへ中継を依頼した段階で、採用・供給済みとはしない。

### 残り（三段目、依存順）
1. [x] 所有 import 閉包・目標型・既存比較の確認（1〜2 時間）。
2. [ ] retract から有限 S 図式の補対象を構成する入口（4〜7 時間）。
3. [ ] dense 包含の相対 S• 比較と離散的な障害の同定（8〜12 時間）。
4. [ ] 正次数の全単射性と零次数の単射性（5〜8 時間）。
5. [ ] 同じ `kSpectrumMap f` との照合・一般形公開（3〜6 時間）。
6. [ ] 自分の集約・監査・禁止仮定検査・限定コミット（2〜5 時間）。
- 合計初期見積り：24〜40 時間。二段目は一般の Thomason 共終性全体。
- 原典：TT 1.10.1・1.10.2、Waldhausen 1.5.9。

### 主要宣言
- `Cofinality.completion_isEssentiallySurjective_of_complete_source`
- `Cofinality.completion_isQCatEquivalence_of_complete_source`
- `Cofinality.completionStableEquivalenceOfCompleteSource`
- `Cofinality.kSpectrumMap_piIsomorphism_of_complete_source`
- `Cofinality.sEndofunctor_map_isFullyFaithful`
- `Cofinality.multiSEndofunctor_map_isFullyFaithful`
- `Cofinality.kSpectrumMap_zero_injective_iff`

### 依存と提供
- 所有：`KST/SConstruction/Cofinality/` の新規葉、同名集約、
  `scripts/audit_kst_cofinality.lean`、本計画。
- 読取専用：既存 SConstruction の同値不変性・実 BF K・零次自然比較、
  F2/Idempotent の完備化・充満忠実像の retract 閉性、Stable の同値の完全性。
- KST/Fibration・NonConnective は import しない。InfinityCategories は編集しない。
- K-B の利用側は `DGKappaSuspensionCofinality` の `hcofinal` と一致する一般形を待つ。
  完備始域の特殊場合を代入して一般供給済みとはしない。

### 未コミット
- なし（本保存単位の実施記録はコミット本文）。

### 既知の問題
- 一般の共終性は未証明。圏論的な right/left cofinality から core S• の比較は出ない。
- TT 1.10.1 の原証明は弱同値を拡大し、1.8.2 の局所化定理を使用する。
  K-B の native Verdier 列の fibration 型と同一ではない。
  そのままの引用や、K-6 がこの拡大弱同値版を供給するとする扱いは禁止。
- 始域の完備性や `ModelCategory SSet` を一般形に追加しない。
- 深層モジュール・既存 SConstruction 集約・監査は編集しない。
- 自分の集約ビルド成功（7557 jobs）。repository import 閉包3899本に欠落なし。
  Fibration・NonConnective への逆依存なし。監査は3所有葉の全9宣言を検査し標準三公理のみ。
  型の ModelCategory 仮定なし、新規 sorry・公理・引用なし。

### 次の一手
- 分担変更が採用されたら、D の一般形を同じ `StableModel` 射へ特殊化し、
  全多次数の有限 S 図式における補対象と相対比較を構成する。
  一般の K₀ 単射性・正次数の π 同型はまだ証明されていない。

## 目標型

```lean
∀ (X Y : StableModel.{u}) (f : X ⟶ Y),
  F2.Idempotent.IsIdempotentCompletion f.val →
    (∀ j : ℤ, 0 < j →
      Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
    Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0)
```

## 証明境界

- 主経路は retract 条件からの dense 安定部分圏の S• 直接比較。
- 全射 K₀ や完備化射自体の同値を要求しない。
- 点ごとの補対象は、面・退化・元の core 射を保つ有限図式の比較とは別。
- 一般局所化・分数・Verdier 商 API は Sp 正本、一般安定圏 API は D 正本。
  所有外の新規一般補題が要る場合は複製しない。
- 完了時は集約と全所有宣言の公理監査を実行し、標準三公理だけであることを確認する。
  実施記録はコミット本文、計画本文は現在地のみ。根の全体ビルドや `.lake` 削除をしない。

## 分担変更提案・D への供給依頼（未採用）

- 依頼先：D（`InfinityCategories/Stable/` の新規葉）。
- 内容：指定完備化射の本質像に `d ⊕ Σd` が入ること。SConstruction 固有の import は不要。
- 調査した既存入口：`SplitCofiberProduct`・`HomotopyBinaryBiproduct` は
  指定された分裂 cofiber の積性を与える。
  `F2/Idempotent/CompletionArrowRetracts` は全辺の retract を与える。
  これらから必要な一般形を直接消費できる公開名は見つからなかった。
- 提案理由：一般安定圏の補対象計算を S• 固有の葉へ新設せず、D 正本の新規葉に保つ。
  K-cof は同じ指定射を有限 S 図式へ適用し、元の実 K 射へ戻す証明を担当する。
- 供給見積り：3〜5時間（K-cof 推定）。この供給だけで一般共終性は完成しない。
- 構成方針：`d` を `f(c)` の retract とし、補冪等射 `1-e` を充満忠実性で始域へ戻す。
  その cofiber の像を `d ⊕ Σd` と同定する。有限 S 図式上の整合性は別工程。
- 以下の依頼型を `#check` で検査済み（存在証明を供給済みとはしない）。

```lean
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories
universe u

∀ (C D : SSet.{u}) [Quasicategory C] [Quasicategory D]
  [IsStable C] [IsStable D] (f : C ⟶ D) [IsExactFunctor f],
  F2.Idempotent.IsIdempotentCompletion f →
  ∀ d : hoFunctor.obj D, ∃ c : hoFunctor.obj C,
    Nonempty (biprod d ((shiftFunctor (hoFunctor.obj D) (1 : ℤ)).obj d) ≅
      (hoFunctor.map f).toFunctor.obj c)
```

- K-6 の fibration 定理への依存追加は提案しない。
  K-B の完備化前 fibration と本供給の間の逆依存は引き続き禁止する。

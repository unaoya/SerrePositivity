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
- **10-26 06:29 採用・再開**：三段目2の一般安定圏の補対象部分は D-22 として D に発注済み。
  D-22 は `57b4a57a4` の `Stable/IdempotentCompletionDensity` から読み取り専用で消費済み。
  提案・依頼は必ずユーザー経由で中継し、計画への記録だけで中継済みとしない。
- 全 Ar 値の本質像条件から S_n の全族を回収し、全多次数の有限反復へ拡張済み。
  各値が双積懸垂として表される全パラメータ族も、同じ完全射の始域へ一つの関手同型で回収。
- 指定境界図式との比較を同じ始域内へ反映し、再度写すと指定像内比較そのものを回収。
  厳密な境界延長や多次数間の全自然性とは数えない。
- 元の `kSpectrumMap` の目標条件を、未置換の零段の正次数全単射・零次単射へ同値化済み。
- **設計変更提案で停止**：次の相対 S• 比較を、cofiber が本質像に入る辺の wide 部分圏の
  亜群化の離散性へ接続する案。必要な一般 API は Sp に依頼する（末尾の型）。
  ユーザー経由で中継を依頼した段階。未採用・未供給で、主定理は未完。

### 残り（三段目、依存順）
1. [x] 所有 import 閉包・目標型・既存比較の確認（1〜2 時間）。
2. [x] retract から有限 S 図式の補対象を構成する入口（4〜7 時間）。
   D-22 を全多次数の双積懸垂の本質像回収へ代入。実現後の相対比較は3に残す。
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
- `Cofinality.exists_sFamily_of_pointwise_image`
- `Cofinality.exists_multiSFamily_of_pointwise_image`
- `Cofinality.sBoundaryRecoveryIso_postcomp`
- `Cofinality.multiSBiprodShift_mem_image_of_completion`
- `Cofinality.exists_multiSFamily_of_biprodShift`
- `Cofinality.kSpectrumMap_cofinality_iff_boundary`

### 依存と提供
- 所有：`KST/SConstruction/Cofinality/` の新規葉、同名集約、
  `scripts/audit_kst_cofinality.lean`、本計画。
- 読取専用：既存 SConstruction の同値不変性・実 BF K・零次自然比較、
  F2/Idempotent の全図式の像回収、Presentable の全余錐の充満忠実性による反映、
  Stable の同値の完全性・D-22 の実密度供給。
- KST/Fibration・NonConnective は import しない。InfinityCategories は編集しない。
- K-B の利用側は `DGKappaSuspensionCofinality` の `hcofinal` と一致する一般形を待つ。
  完備始域の特殊場合を代入して一般供給済みとはしない。

### 未コミット
- なし（実施記録は本保存単位のコミット本文）。

### 既知の問題
- 一般の共終性は未証明。圏論的な right/left cofinality から core S• の比較は出ない。
- TT 1.10.1 の原証明は弱同値を拡大し、1.8.2 の局所化定理を使用する。
  K-B の native Verdier 列の fibration 型と同一ではない。
  そのままの引用や、K-6 がこの拡大弱同値版を供給するとする扱いは禁止。
- 始域の完備性や `ModelCategory SSet` を一般形に追加しない。
- 深層モジュール・既存 SConstruction 集約・監査は編集しない。
- 自分の集約ビルド成功（7765 jobs）。repository import 閉包4106本に欠落なし。
  Fibration・NonConnective への逆依存なし。監査は9所有葉の全51宣言を検査し標準三公理のみ。
  型の ModelCategory 仮定なし、新規 sorry・公理・引用なし。
- 双積懸垂が本質像に入ることから、元の K 射の正次数同型を直接推論しない。
  `F ⊕ ΣF` の回収は元の F の回収ではなく、相対実現比較の証明が必要。

### 次の一手
- 末尾の相対 S• 経路が採用されたら、Sp の wide 部分圏・亜群化の離散性を受け、
  同じ全多次数の相対図式と元の未置換零段へ接続する。
  一般の K₀ 単射性・正次数の π 同型は未証明。厳密境界延長も別工程。

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

## 採用済み分担・D-22（10-26 06:29 発注、消費済み）

- 依頼先：D（`InfinityCategories/Stable/` の新規葉）。
- 内容：指定完備化射の本質像に `d ⊕ Σd` が入ること。SConstruction 固有の import は不要。
- 調査した既存入口：`SplitCofiberProduct`・`HomotopyBinaryBiproduct` は
  指定された分裂 cofiber の積性を与える。
  `F2/Idempotent/CompletionArrowRetracts` は全辺の retract を与える。
  これらから必要な一般形を直接消費できる公開名は見つからなかった。
- 分担：一般安定圏の補対象計算は D 正本の新規葉に保つ。
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

## 三段目3の設計提案・Sp への依頼（未採用）

- 提案：cofiber が包含の本質像に入る辺だけを持つ wide 部分圏の亜群化を使う。
  その正次数ホモトピー群の消滅を、相対 S• 実現の障害が離散的であることへ接続する。
  原典：Hebestreit–Lachmann–Steimle §7.1 の第一証明（S• 側の接続は K-cof 所有）。
  <https://arxiv.org/pdf/2205.06104#page=20>
- 必要な理由：実装済みの図式回収と双積懸垂の密度だけでは、元の K 射への相対比較は出ない。
  亜群化・局所化の一般 API は Sp 正本なので、同じものを Cofinality に新設しない。
- 依頼先：Sp（新規葉）。一般の安定な C・D と指定完全射で供給し、SConstruction を import しない。
  初期見積り：wide 部分圏・閉性2〜4時間、亜群化の離散性6〜12時間（K-cof 推定）。
- 既存の `weakArrowCategory q` は商で可逆な辺の**図式圏**であり、この wide 部分圏とは異なる。
  完備化前の Verdier 列や K-B の fibration 定理へこの依頼を差し替えない。
- 以下は供給仕様の型。`M` の全単体条件を明記し、辺の集合だけで代用しない。
  `continuousKanReplacement` は既存の亜群化の Kan 模型を使う。

```lean
∀ (C D : SSet.{u}) [Quasicategory C] [Quasicategory D]
  [IsStable C] [IsStable D] (f : C ⟶ D) [IsExactFunctor f],
  F2.Idempotent.IsIdempotentCompletion f →
  let P : Set (D _⦋0⦌) :=
    {y | ∃ x : C _⦋0⦌, Nonempty (VertexIso (f.app (Opposite.op ⦋0⦌) x) y)}
  let W := cofiberLocalizingEdges P
  ∃ M : D.Subcomplex,
    (∀ (n : ℕ) (s : D _⦋n⦌), s ∈ M.obj (Opposite.op ⦋n⦌) ↔
      ∀ θ : ⦋1⦌ ⟶ ⦋n⦌, D.map θ.op s ∈ W) ∧
    Quasicategory (M : SSet.{u}) ∧
    ∀ (x : (F2.continuousKanReplacement.obj (M : SSet.{u})) _⦋0⦌)
      (n : ℕ), 0 < n →
      Subsingleton (KanHomotopy (F2.continuousKanReplacement.obj (M : SSet.{u})) n x)
```

- 型は `/tmp/kst-cofinality-wide-request.lean` で検査。存在証明は未供給。
- 別途 K-cof が証明するもの：全多次数の相対 S 図式との照合、元の K 射を保つ
  相対実現の比較、零次障害の同定、正次数同型と零次単射。

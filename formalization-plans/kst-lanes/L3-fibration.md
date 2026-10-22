# K-F レーン：K-6 fibration 定理（L3）

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §6 の K-F。K-S• の L1（∞-S•、加法性、homotopy fiber）と Sp の K-5
> （抽象 Verdier 列、Sp 値局所化不変量）を読み取り専用で使い、Verdier 列 D → C → C/D に対する連結 K の fiber 列を証明する。
> 非連結化（K-7、BGT §9）は F1b・N の Ind・冪等完備化の後に別途。

## 引き継ぎ（2026-10-22）

### 現在地
- 工程 (a) 完了。`IsVerdierSequence` の核条件から包含の本質像が安定閉包と一致すると証明。
  cofiber による W 所属と商の実辺の可逆性を同定し、実二単体の二対三性、実押し出し・
  引き戻しでの保存と反映、実 cofiber 列間のホモトピーに対する拡大安定性を証明済み。
- この工程は thick 性より弱い安定な本質像で成立する。商の冪等完備化や連結 K の
  fiber 性はまだ主張しない。拡大安定性の三角形の射は実ホモトピーから構成する。
- 対象ビルド 2830 jobs・専用監査 2 モジュール 13 宣言・全体 23534 jobs が成功。
  標準三公理のみ、宣言型の ModelCategory 検査と diff --check も成功。

### 残り（依存順）
1. S• の相対構成 S•(C, W) と加法性からの連結版 fibration 定理
   （Waldhausen 1985 1.6.4、BGT §7、暫定 40–80 時間）。
2. 必要な cofinality 条件の明示。K-S• の K-1（加法性）・K-2（homotopy fiber 比較）の
   宣言だけを入力にする（BGT §7–8、暫定 16–32 時間）。
3. K(D) → K(C) → K(C/D) の fiber 列（連結版、Sp 値）。K-5 の形と π 同値検出へ
   接続する（BGT §7–8、暫定 16–32 時間）。
4. 冪等完備化と非連結化への入力の整理（BGT §9、暫定 8–16 時間。K-7 本体は別工程）。

### 主要宣言（共通接頭辞 `SerrePositivity.KST.Fibration`）
- weakEquivalences、stableClosure_essentialImage、mem_weakEquivalences_iff、
  mem_weakEquivalences_iff_invertible、weakEquivalences_twoOfThree、
  weakEquivalences_pushout_iff、weakEquivalences_pullback_iff、weakEquivalences_extension。

### 依存と提供
- 読み取り専用：`KST/SConstruction/`（K-1・K-2）、`KST/LocalizingInvariants/`（K-5）、`KST/Spectra/`、`InfinityCategories/Derived/`（β3 の Verdier 列）。
- 提供先：K-7（非連結 K）、K-基盤 2（K が局所化不変量であること）。
- 工程 (a) の直接入力は K-5 の `VerdierSequence` と Stable の実 cofiber・八面体・
  基底変更・前三角構造。SConstruction と Spectra の直接 import はない。

### 未コミット
- なし（工程 (a) の所有ソース・集約・監査・本計画を同じ保存単位に含める）。

### 既知の問題
- 所有 import 閉包の破損なし。K-6 全体と連結版の cofinality 条件は未完。

### 次の一手
- 工程 (b)：K-1・K-2 の公開界面を確認し、W を辺条件として持つ相対 S• の配置を設計する。
  SConstruction 内部に追加界面が必要なら K-S• へ依頼して待ち、読み取り専用境界を守る。

## 規約
- 配置 `SerrePositivity/KST/Fibration/`、集約 `KST/Fibration.lean`、監査 `scripts/audit_kst_fibration.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。H⁰ の Verdier 普遍性で写像空間の比較を代用しない。Sp の IsStable は使わない。
- 原典：Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。

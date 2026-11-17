# K-cof：Thomason の共終性定理

## 引き継ぎ

### 現在地
- K-S•-S2 の無条件主定理 `Cofinality.kSpectrumMap_cofinality` を実装済み。
- 最新の前段保存は 3839a204d。S1 無条件供給は 69c370610。
  本工程の保存コミットは完了報告で通知する。
- D-22・Sp-7・Sp-8 (1)(2)(3) と K-B2-S1 の実証明を消費済み。
- 指定完備化射の元の `kSpectrumMap f` の正次数全単射・零次単射を結論する。
  相対 fiber 入力、始域の冪等完備性、全射 K₀、ModelCategory の追加仮定はない。
- 集約ビルド成功（9034 jobs）。最終専用監査の結果は下記「検証」を参照。

### 残り
- K-cof の K-S•-S2 実装に残る供給入力はない。
- K-B3 の K-7 e に対する実代入は K-B3 所有。公開名と使用例を提供する。

### 主要宣言
- `Cofinality.kSpectrumMap_cofinality`
- `Cofinality.kSpectrumMap_cofinality_of_relativeFiber_input`（既存互換界面）
- `Cofinality.kSpectrumMap_cofinality_of_inputs`（既存互換界面）
- `Cofinality.kanPullbackCofinalityInput`

### 依存と提供
- 所有：`KST/SConstruction/Cofinality/`、同名集約、`audit_kst_cofinality`、本計画。
- 他レーンの実装・集約・監査は読み取り専用。
- S1 は `Fibration.Relative.ClosedStableFiberUnconditional` を狭い入口として使用。
  同じ供給の `Fibration.closedStableFlagPostPullback` を既存の条件付き経路へ代入する。
- Sp-8 (3) は独立入口 `LocalizingInvariants.CoreFlag.KanPullbackAll` から消費。
  入力定義・旧 CoreFlag.All から消費葉への逆 import は追加しない。
- 主経路は相対 Kan 四角形と加法性による。Verdier 列・商比較・K-6 を使用しない。
  供給側の一般補題の import 経由で Verdier 用葉が環境に入るため、
  モジュール閉包の許可とは別に主定理の型・証明の推移依存を監査する。
- `NonConnective` は推移 import も禁止する。

### 未コミット
- なし。本工程の新規葉 `Thomason.lean` と集約・専用監査・本計画のみ限定保存。
  保存コミットは完了報告を参照。他レーンの作業中ファイルは保存対象外。

### 既知の問題
- なし。既存の条件付き公開名・型を保持する。

### 次の一手
- K-B3 は `kSpectrumMap_cofinality f hf` の二成分を K-7 e へ代入する。
  K-cof 自体は主工程完了後に停止する。

## 公開界面（K-B3 向け）

入口は `SerrePositivity.KST.SConstruction.Cofinality`。
正本の宣言は `Cofinality/Thomason.lean` に置く。

```lean
open CategoryTheory
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra

-- {X Y : StableModel.{u}}, f : X ⟶ Y
-- hf : F2.Idempotent.IsIdempotentCompletion f.val
#check Cofinality.kSpectrumMap_cofinality
-- 正次数：
-- (Cofinality.kSpectrumMap_cofinality f hf).1 j hj
-- 零次：
-- (Cofinality.kSpectrumMap_cofinality f hf).2
```

主定理の型（追加の供給引数なし）：

```lean
∀ (X Y : StableModel.{u}) (f : X ⟶ Y),
  F2.Idempotent.IsIdempotentCompletion f.val →
    (∀ j : ℤ, 0 < j →
      Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
    Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0)
```

## 証明経路と境界

1. D-22 の biproduct-shift 密度を全反復 S と指定完備化射へ移す。
2. Sp-7 の wide 離散性と Sp-8 (1) の自然な core 旗評価比較を消費する。
3. 元の全多次数 S 余核図式を群 nerve の bar と同定し、Sp-8 (2) で高次消滅を得る。
4. 元の相対旗と供給側の閉じた全旗を全 S 方向で比較する。
5. S1 の閉じた安定部分圏の全旗自然性を実代入し、元の相対 Kan 四角形を得る。
6. 可縮な核と右項の高次消滅を Sp-8 (3) の一般 Kan 引き戻し定理へ渡す。
7. 元の本質像包含の π₁ 単射・二次以上全単射を境界商・Ex∞・SOA Kan・loop 比較へ移す。
8. 元の始域と本質像の安定模型同値を消去し、同じ `kSpectrumMap f` を結論する。

S1 の無条件同型・射影公式・零化ホモトピーも同じ入口から到着している。
本経路は既に保持する元の四角形を使うため、同型を組み直さず、
それらと同じ `closedStableFlagPostPullback` の証明を最後の一入力へ代入する。
本質像を Verdier 商の核に置き換えたり、retract 閉包を追加したりしない。

## 検証

- `lake build SerrePositivity.KST.SConstruction.Cofinality`：成功、9034 jobs。
- `lake env lean scripts/audit_kst_cofinality.lean`：成功、108 モジュール・702 宣言、標準三公理のみ。
- 専用監査は所有全宣言の標準三公理、ModelCategory 型仮定の不在、
  許可した狭い Fibration 閉包、NonConnective 不在を強制する。
- 主定理の完全な公開型を宇宙多相な `example` で検査する。
- 主定理の型と不透明な定理本文を含む推移依存を走査し、
  `IsVerdierSequence`・`ModelCategory`・Verdier 核比較定理の使用を拒否する。
- 所有範囲の `git diff --check`：成功。計画は300行以内、引き継ぎは100行以内。

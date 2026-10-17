# dg 理論の係数変更（U12f・U15d）

正本は `dg-theory.md` §15 冒頭・§15.2 U12f・§15.5 U15d。
任意可換環、非有界 cochain 複体、微分 +1、ホモトピー −1、Mathlib
`EnrichedCategory` を維持する。係数環・Hom 加群の宇宙は `u`、対象宇宙は独立な `v`。
直和を使う箇所だけ添字の `Small.{u}` を要求する。

## 編集境界

- `Derived/KFlatBimodule*`、既存の bimodule 合成系、既存 `Quotient/`、`Perfect/`、
  `DifferentialGraded/README.md`、`Stage*.lean` は編集しない。
- ルートの import は自分の行だけ追加・部分 stage する。
- `dg-theory.md` への参照追加は両単位の完了時のみ。
- 新規 sorry・axiom・引用は追加しない。

## 作業順と受入状況

1. U12f underived：複体上の restriction/extension 随伴、同じ添字の直和、
   coequalizer、tensor 比較を先行する。dg 圏・dg 加群・相対 tensor、単位・結合・自然性へ進む。
2. U12f derived：quasiIso 保存の条件を underived の余極限保存と区別する。
   非 flat な係数変更も扱い、underived との一致に必要な置換条件を記載する。
3. U15d：固定した path 添字の比較、最終微分、単位・合成との整合性。

現時点では U12f・U15d の全受入を完了扱いしない。

## 実装中の API

`Tensor/ScalarExtensionColimits.lean` の namespace は
`SerrePositivity.DifferentialGraded.ScalarExtension`。
`extension`・`restriction` は各次数への Mathlib の係数変更であり、
`adjunction` は加群の随伴の単位・余単位を複体へ持ち上げる。
`coproductIso`・`coequalizerIso` は余極限保存から得る同型で、平坦性を要求しない。
`tensorIso`・`tensorIso_naturality` は既存の非有界 total tensor 比較を再利用する。
`identityIso`・`compositionIso` は係数変更を一回または二回施す比較。

`Tensor/ScalarExtensionCoherence.lean` では sphere・単位複体の比較と
tensor 比較の単位・結合整合性を証明する。

## 2026-10-17：U12f の基礎部分

`Tensor/ScalarExtension.lean` で `extensionMonoidal` を構成し、
Mathlib の `TransportEnrichment` により `DGBaseChange` を定義した。
`homObject_eq`・`identity_eq`・`composition_eq` は実際の Hom・単位・合成の式である。
`dgFunctor` は Hom 上の係数拡大から得られる dg 関手で、単位と合成を保存する。

検証：`lake build SerrePositivity.DifferentialGraded.Tensor.ScalarExtension` 成功
（1969 jobs、警告なし）。
`lake build SerrePositivity.DifferentialGraded.Checks.ScalarExtension` 成功
（1970 jobs）。後者は `ℤ → ZMod 2` による強モノイダル構造と dg 圏の型検査を含む。
同ファイルの主要14宣言の `#print axioms` はすべて
`propext`・`Classical.choice`・`Quot.sound` の標準3公理のみ。
コミット：`3368f633`。

これは U12f の部分受入である。複体上の随伴を dg 加群上の随伴と同一視しない。
dg 加群の係数変更・その随伴、相対 tensor の比較、導来比較、U15d の最終微分と
単位・合成比較は未完であり、次の部分単位で実装する。

## 2026-10-17：全次数 Hom 比較と加群の対象

`Tensor/ScalarExtensionHom.lean`：

- `homComparison` は評価射の係数拡大を tensor–Hom 転置して作る。
  Hom の係数変更が同型であるとは主張しない。
- `homComparison_apply` は全整数次数で `1 ⊗ f` と `1 ⊗ x` の評価を与える。
- `homComparison_identity`・`homComparison_composition` から
  `complexDGFunctor` を作る。後者は Koszul 符号を保持する。

`Tensor/ScalarExtensionModule.lean`：

- `tensorIso_braiding`・`oppositeDGFunctor` により係数変更と opposite を交換する。
- `rightModule`・`leftModule` は実際の Mathlib 豊穣関手であり、
  各値が複体の係数拡大になる。
- `rightModule_action` は純粋生成元上の全次数作用の比較。

検証：`lake build SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionModule` 成功
（1978 jobs、警告なし）。
`lake build SerrePositivity.DifferentialGraded.Checks.ScalarExtensionModule` 成功
（1979 jobs）。後者は `ℤ → ZMod 2` による左右加群の型検査と、主要12宣言の
`#print axioms` を含む。すべて標準3公理のみ。新規 sorry・axiom・引用は0件。
ルートには `Tensor.ScalarExtensionModule` の import 行のみ追加し、`git add -p` で
その hunk のみ stage した。

### 残る受入条件（完了宣言しない）

1. dg 加群の **射** の係数変更と関手、restriction と extension の加群圏上の随伴。
   現在の `adjunction` は複体圏上のもの。
2. 相対 balanced tensor の二つの関係射を上記 coequalizer 比較で運び、比較同型を作る。
3. 非 flat な係数変更の導来関手と、underived 比較に必要な K-flat 置換条件。
   `Derived/ScalarExtension.lean` は未作成。`Derived/KFlatBimodule*` は未編集。
4. U15d の固定 path 添字の同型、最終微分、単位・合成の比較。
   `Quotient/ScalarExtension.lean` は未作成。既存 `Quotient/` は未編集。

正本 `dg-theory.md` への完了参照はまだ追加しない。

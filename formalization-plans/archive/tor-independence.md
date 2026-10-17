# 完全 F_p 環の Tor 独立性

> **アーカイブ（2026-10-18）**：完了。要点は `CommutativeAlgebra/PerfectTorIndependence/Basic.lean` の docstring。将来は削除する予定で、以下は当時の計画と実施記録のまま。


## 担当と主張（2026-10-17）

本レーンは BS 著者版 `paper/refs/BS-prisms-author.pdf` の Lemma 10.3
（印刷 pp.78–79）の証明で参照される完全標数 p 環の Tor 独立性を供給する。
Lemma 10.3 自体は完備導来乗法の同型性と混合項の消滅を主張しており、
任意の perfectoid 環図式の離散性はその証明中の一般化した補助主張である。
ここではその mod p の入力だけを扱う。Corollary 8.12 は宣言も使用もしない。
未採用の `bs-clmst-citation-elimination.md` は根拠としない。

## 実装前の紙上検証

1. テンソルの底を k = F_p と明記して
   P_n = A ⊗_k A^{⊗_k n} ⊗_k B とする。これは augmented two-sided bar
   B_•(A,A,B) で、面は隣接因子の積（最後は A の B への作用）、退化は単位の挿入。
   B の k ベクトル空間としての自由性により各項は A 自由加群である。
   「自由 A 代数」という表現は訂正が必要で、各項の多項式代数としての自由性は不要であり、
   一般には成立しない。augmentation は余分な退化によって k 加群として縮約し、
   alternating face map complex は B の A 自由分解となる。
2. D_n = P_n ⊗_A C は単体的可換 k 代数であり、正規化 Moore 複体のホモロジーは
   Tor_i^A(B,C) を計算する。Mathlib の Tor は第 2 変数で導来するので、
   B の分解での計算からは balanced comparison／対称性も必要となる。
   Dold–Kan 同値だけで Tor との比較が自動的に得られるとはしない。
3. 各項は k 上の A,B,C のテンソル積で、その Frobenius は各因子の Frobenius の
   テンソル積である。k の Frobenius は恒等であり、逆写像も k 線形なので同型となる。
   A 線形性は一般にはないが、単体的 k 代数の自己同型としては問題ない。
4. p ≥ 2 とし、基点を零とする。μ_p : D^{×p} → D は単体的な基点付き集合の写像である。
   これは一般には加法写像でも環準同型でもないため、Dold–Kan や加群のホモロジー関手を
   μ_p に直接適用してはならない。基点付き単体集合のホモトピー群を使えば、i ≥ 1 で
   (μ_p)_* は群準同型であり、π_i(D^{×p},0) = π_i(D,0)^p となる。
   第 k 因子の包含 ι_k は他の座標を零とするから μ_p ∘ ι_k = 0。
   よって各座標因子上で (μ_p)_* は零であり、群準同型性から全体で零となる。
   i = 1 でも π_1(D,0) は単体的加群から来る可換群なので、この加法表示は有効である。
   Frobenius = μ_p ∘ Δ は従って正次数で零を誘導し、かつ同型なので π_i(D,0) = 0。

結論：手順 4 は基点付きホモトピー群を経由すれば成立する。
「各変数について加法的」だけを根拠に μ_p を加法圏の射として扱う解釈は成立しない。
分割冪構造と [Lur11] はこの紙上議論には不要である。

## 既存成果との接続と証明方針の差

正本の `clmst.md` の KL-E1c・C1（2026-10-16）と既存コードを照合したところ、
`SerrePositivity.perfectRing_tor_subsingleton` が既に任意の完全環図式に対する
全正次数の Tor 消滅を証明している。新規実装ではこの証明を再利用する。
BS17 Lemma 3.16 を引用せず、今回の単体的 bar 証明を Lean で構築したとも主張しない。

既存証明は、自由完全多項式 A 代数 P から B への全射を取り、P の A 平坦性、
P ⊗_A C の完全性、完全環の全射に対する Tor 消滅、Tor-acyclic 底変換を組み合わせる。
全射の場合は根基イデアルの互換 p 冪根とその商に関する既存 Tor 計算を使う。
これは上記の単体的証明とは異なる代数的証明である。
新しい単体的分解／Dold–Kan と Tor の一般比較補題は追加しない。

## 公開入口と検証

新規公開入口は `SerrePositivity.tor_vanishing_of_perfect` とする。
型は指定どおり、同じ universe の可換環 A,B,C、A 代数 B,C、素数 p、
三環の CharP と PerfectRing のみを仮定し、全 i > 0 で
`IsZero (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A B)).obj (ModuleCat.of A C))`
を結論とする。全射性・平坦性・有限性などの追加仮定は置かない。
型全体の検査は専用監査の `example` でも固定する。

検証結果（2026-10-17）：

- `set -o pipefail` を付けた既存依存先の対象ビルドは 3318 jobs、
  新規集約の対象ビルドは 3320 jobs、`lake build` 全体は 6562 jobs で、すべて終了コード 0。
  新規ファイルの警告はなく、共有の既存 linter 警告のみ。
- `lake env lean scripts/audit_perfect_tor_independence.lean` は終了コード 0。
  公開宣言の `assert_no_sorry`、指定された型全体の検査、
  `collectAxioms` による標準三公理以外の拒否をすべて通過。
  実際の依存公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
- 新規入口からのリポジトリ内 import 閉包は 206 モジュール。
  `BhattScholze`・`CLMST`・`Inputs`・`Paper` への import はなく、
  原典の引用定理を経由していない。
- `python3 scripts/check_documentation.py` は終了コード 1。
  17 Markdown files と 320 exposition references を検査し、
  exposition の `BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotient`
  が未解決であるという 1 件の失敗を報告した。本レーンが変更せず依存もしない箇所なので、
  他チャットのファイルを修正することも回避策を追加することもしない。
- `git diff --check` は成功。ルートへの変更は本レーンの集約 import 1 行のみ。

BS Lemma 10.3 の完備導来 tensor の比較とレーン B 側の仮定解消は本レーンの範囲外であり、
この入口の供給と区別する。

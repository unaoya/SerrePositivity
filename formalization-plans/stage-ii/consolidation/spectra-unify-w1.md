# SU-W1　対称スペクトルの二つの版を一つにする（一段ずつ）

2026-11-20、調整役。レーン ⑧（`../SerrePositivity-cited`）。**main から新しい枝 `refactor/spectra-unify` を切って行う**（`research/cited-coverage` の見本の 2 コミットは載せない。その枝は残す）。

## 0. 背景

宣言を依存関係で整理した結果（`research/cleanup-zero-base/`）、対称スペクトルは三つの層になっていた。

- A：一般の理論。`CategoryTheory/Monoidal/Mod/`、`CategoryTheory/Enriched/`、`Spectra/SymmetricSequence/`。数学の中身はほぼここにある。
- B：`Spectra/General/`（`GeneralSymmetricSpectrum C K`、畳んだ後 341 宣言）。A に Sym(K) 上の加群を当てはめたもの。
- C：`Spectra/SymmetricSpectrum/`（`SymmetricSpectrum`、660 宣言）。A に球面の対称列上の加群を当てはめたもの。B の特殊な場合（C = 基点付き単体集合、K = 円周）だが、B を経由せず A からもう一度作ってある。

C の 660 宣言のうち 416 は、一行の言い換え（一行の定義 211、`rfl` の定理 74、補題一つの適用 131）。`Spectra/General/SimplicialComparison.lean` には `simplicial_type : GeneralSymmetricSpectrum PointedSimplicialSet circle = SymmetricSpectrum := rfl` をはじめ、B の特殊化が C と一致するという `rfl` の比較が並んでいる。

目標の形：B を対称スペクトルの唯一の定義にし、C は「B で基礎圏を単体集合、座標を円周にしたもの」とする。C に残るのは、単体集合に固有の内容だけ。

材料：`research/cleanup-zero-base/spectra/decls.jsonl.gz`（B・C・`CategoryTheory/Enriched`・`Adjunction/Comparison` の全宣言。型、型の中で使う宣言、値の中で使う宣言、ソースの位置）。`dump.lean` で採り直せる。

## 1. 進め方の規則

- **一回の依頼は一段だけ**。段の終わりでコミットし、報告を書いて止まる。次の段は調整役の連絡を待つ。
- 変えないもの：文献の対応表（`research/*-coverage/` の `review/*.csv`・`external.csv` など）が名指しする宣言の名前と主張。段の最初に、対象の宣言が名指しされていないかを自分で確かめ、結果を報告に書く。
- それ以外の宣言は、名前も主張も変えてよい。消してよい。範囲の外の使用箇所（`Spectra/ModelCategory`、`Spectra/Stable`、`scripts/` の監査・検査など）は、同じ作業の中で直す。
- 判断に迷う所、指示にない削除や範囲の拡大が要る所は、進めずに報告に書いて止まる。
- ビルドは `--class bulk` の鍵で、対象と、それを import する側だけ。root 全体は調整役。⑦ が別名の削除で全体を建て直している間は、鍵を待つ。
- 判定（各段共通）：対象と使う側のビルドが通る。公理と sorry が増えない。変えた監査・検査が通る。対応表が名指しする宣言の（カーネル名・型）が前後で一致。

## 2. 段 1：基本の部分で、C を B の特殊化に置き換える

対象は、`SimplicialComparison.lean` に `rfl` の比較がある C の宣言（型・`forget`・`level`・`action`・自由スペクトル・評価・`freeAt` とその随伴など）と、それらが置かれている C のファイル。

1. `SymmetricSpectrum` の定義を、`GeneralSymmetricSpectrum PointedSimplicialSet circle` を使う形にする（`abbrev`）。
2. 対象の C の宣言ごとに、次のどれかにする。優先はこの順。
   - **消す**：使う側を B の宣言に直す。対応する `simplicial_…` の比較も消す。
   - **B の宣言の一行の別名として残す**：使う側で引数（`C`・`K`）を毎回書くことになって読みにくくなる場合だけ。理由を記録する。
   - **そのまま残す**：B に対応がなく、単体集合に固有の内容である場合。どこで固有の性質を使うかを記録する。
3. C のファイルで、中身がなくなったものは消し、import を追従する。

この段では、テンソル積・内部 Hom・余テンソル・写像空間・懸垂には進まない（`rfl` の比較があっても、段 2 以降）。段 1 の範囲に入れるか迷う宣言は、入れずに一覧にする。

### 段 1 の完了の条件

- 対象の C の宣言の全部について、表（`research/cleanup-zero-base/spectra/stage1.csv`）に一行ずつ：C の宣言、扱い（消す・別名・残す）、B の相手の宣言（消す・別名のときは必須）、理由、直した使用箇所の数。
- 判定（§1）を満たす。
- 報告（`formalization-plans/stage-ii/consolidation/report-spectra-unify.md`）：宣言の数と行数の前後（C・B・使う側）、扱いごとの件数、つまずいた所（型クラスの解決、宇宙、`K` の推論、名前空間の衝突など）と対処、段 2 でそのまま通用しそうなやり方と、しなさそうな所。かかった時間（読む・書き換える・ビルド）。

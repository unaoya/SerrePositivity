# scripts

検証用のスクリプト。CI では実行していない。いずれもリポジトリの根から実行する。

## 主要な監査

| スクリプト | 内容 |
| --- | --- |
| `audit_axioms.lean` | 主定理の未証明入力の正本。`lake env lean scripts/audit_axioms.lean 2>&1 \| grep "has sorry"` |
| `check_documentation.py` | 解説の `\ld{}` 参照と Markdown のリンクを検査する（`lake env python3 scripts/check_documentation.py`） |
| `audit/<系列>.lean` | 系列ごとの全宣言の監査。下記 |

## 系列ごとの監査（`audit/`）

`python3 scripts/make_area_audits.py` が生成する。手で編集しない。
各ファイルは系列の追跡済みモジュールをすべて import し、そこで定義された全宣言について

- Lean が報告する公理が propext・Classical.choice・Quot.sound・sorryAx だけであること（新しい axiom や native_decide がない）、
- `sorry`・`admit` を書いてよいのは、許可した引用のファイルだけであること（ソースで検査する）

を確かめる。import した定理の証明本体はモジュール方式では読めないので、sorry はソースで調べる。

| ファイル | 対象 | 許可した引用 |
| --- | --- | --- |
| `audit/dg.lean` | `DifferentialGraded/`、`Inputs/DifferentialGraded/` | なし |
| `audit/clmst.lean` | `CLMST/` | なし（BS の引用に依存する宣言は数だけ表示） |
| `audit/bhatt_scholze.lean` | `BhattScholze/` | `Inputs/Perfectoidization.lean`（Thm 1.17(1)）、`Inputs/ArcExcision.lean`（Cor 8.12） |
| `audit/adams.lean` | `KTheory/`、`IntersectionMultiplicity/` | なし |
| `audit/shared.lean` | 共有層（`HomologicalAlgebra/`、`CommutativeAlgebra/`、`PerfectComplex/`、`Paper/`、`Inputs/` など） | K 理論の二入力と `Inputs/Homotopy/KanQuillen.lean` |

モジュールを追加・削除したら生成し直す。系列や許可した引用を変えるときは `make_area_audits.py` の `AREAS` を編集する。

## 構造の監査（Python）

| スクリプト | 内容 |
| --- | --- |
| `audit_bhatt_scholze_structure.py` | BS の import の境界（CLMST を import しない等）と、BS の監査の登録 |
| `check_adams_import_boundaries.py` | Adams 系列の import の境界 |
| `audit_homotopical_layout.py` | 共有ホモトピー論の配置（`homotopical_generalization_manifest.json` を使う） |
| `audit_stage4_dependencies.py` | K 理論の段階 4 の依存監査（`formalization-plans/archive/stage4-dependency-audit.md` を生成） |

## その他の `audit_*.lean`・`check_*.lean`

進行中・検討中の系列（K 理論、ホモトピー論、スペクトル、∞ 圏）の工程ごとの確認と、
現行の文書から参照されている監査。完了した系列（dg、CLMST、BS、Adams）の工程ごとの確認は
2026-10-18 に `audit/` へ置き換えて削除した。進行中の系列も、区切りに達したら同じように置き換える。

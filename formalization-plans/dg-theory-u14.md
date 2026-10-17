# U14：指定dg生成元とendomorphism表示

正本は `dg-theory.md` §15冒頭・§15.4。任意可換環、非有界cochain複体、
微分次数+1、ホモトピー次数−1、Mathlib Enrichedを主モデルとする。
引用・追加公理・sorryは導入しない。U14全受入はまだ未完。

## U14a.1：一対象EndとHom bimodule（2026-10-17）

- `Endomorphism/Basic.lean`：指定対象で添字付けした一対象型、元の全Hom複体・
  単位・forward合成を継承するdg構造、指定対象への包含。
  dg関手に沿うEndの写像と包含の可換正方形も証明。
- `Endomorphism/HomBimodule.lean`：右End(E)・左Dのbimoduleの値はHom(E,X)。
  右作用は既存representableの制限、左作用はdg Yonedaの全次数Hom写像のE成分。
  左右の交換は主Hom endの豊穣自然性で保持する。
  E自身の像がEnd(E)の正則representableになることを、作用も含めて証明。
  U13の `SmallPerfectDGModuleOver` 内の指定対象への適用を公開。
- 対象宇宙は独立。大きいenhancement全体のsmall性を仮定せず、
  U13の小さい代表系を用いる。生成集合を無限直和で一対象化する操作はしていない。
- 検証：`lake build SerrePositivity.DifferentialGraded.Endomorphism.ChecksBasic` 成功。
  同ファイルの8主要宣言の `#print axioms` は全て
  `propext`, `Classical.choice`, `Quot.sound` の標準3公理のみ。

## U14a.2：balanced評価と複体値随伴との比較（2026-10-17）

- `Endomorphism/Evaluation.lean`：Hom(X,E)の左End(E)加群と
  Hom(E,Y) ⊗_End(E) Hom(X,E) → Hom(X,Y)を構成。
  純粋斉次元の評価は `(-1)^(rs) forward(t,m)`。
  balanced関係の証明は結合則と指数
  `rp + (r+p)s = r(p+s) + ps` を使い、負次数も除外しない。
- `Endomorphism/EvaluationAdjunction.lean`：評価の転置を閉零End(E)加群射として構成し、
  U11のtensor–Hom随伴の単位との式と余単位による評価の因子化を証明。
  これはHom(X,E)を固定する複体値随伴であり、enhancementとEnd(E)加群の間の
  再構成随伴の完成を主張するものではない。
- `ChecksEvaluation.lean`：整数係数の次数−1・+1での評価、およびZMod 2係数の
  非有界複体に対する一対象構造を検証。
  対象ビルド成功。8主要宣言の公理は標準3公理のみ。

## 残る受入条件

- U14a：enhancement／End(E)加群間の再構成随伴と、その単位・余単位。
- U14b：thick生成からPerf比較。全Homの擬同型とH⁰の本質的全射を別々に証明する。
- U14c：導来圏全体の比較にはcompact生成性が必要。
  無限生成集合の直和はcompactとは限らず、thick生成だけから全導来圏の比較は出さない。
  DG-GEN/DG-MORの採用が必要になったら採用せず停止・報告する。
- 既存導来tensorとの計算比較、shift・三角性・係数変更の図式。

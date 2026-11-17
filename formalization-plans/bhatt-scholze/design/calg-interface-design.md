# CAlg_R の界面の設計（D71〜D73、2026-11-10）

作成：段階 II の調整役。決定：ユーザー（11-10、「BS-W14 は (A)」）。材料：`research/einfinity-route/README.md`（drafts の使われ方、BS が要る性質、比較定理の文献）。

## 0. 目的

BS の証明を「E∞ 代数の ∞ 圏をどう作るか」から切り離す。今の `EInfinity/` は Barratt–Eccles の dg の模型で `CAlg_R` を定義している。HA の方向（∞-オペラッドで CAlg(D(R)) を作り、模型と比べる）は **D75（11-11）で段階 II の BS の経路から外した**（HA の基盤の課題として別に持つ）。界面はそのまま残す：将来 HA の方向の実例ができたときに差し替えるため。どちらに決めても BS の証明を書き直さずに済むように、**BS は CAlg を性質の一覧（界面）を通してだけ使う**。

## 1. 決定

- **D71**：BS（本体と drafts）は E∞ 代数の ∞ 圏を、構造 `EInfinityTheory`（§2）を通してだけ使う。`CAlg_R` の模型の中身（Barratt–Eccles の作用、cofibrant な代表、hammock の単体、`cofibrantAlgebraDKInclusion` など）を直接使う宣言は作らない。
- **D72**：今の模型は `EInfinityTheory` の実例 `barrattEcclesTheory` の一つにする。欄の証明が揃っていないもの（表現可能性 G12、P⁰ M14 など）は、実例の側で sorry のまま drafts に置き、④（∞ 供給：E∞）の仕事にする。BS の定理は `(E : EInfinityTheory)` を引数に取って述べ、最後に実例を代入する。
- **D73**：HA の方向で作る場合は、同じ構造の別の実例を作り、Hinich Thm 4.1.1（または Pavlov–Scholbach Thm 7.11）で今の実例と比べる。BS 側は変えない。原典の「E∞ 代数」との一致（D73 の比較）は、BS の主張の型ではなく実例の側の定理として置く（原典どおりの定義の方針、`bs-faithful-definitions` と両立）。

## 2. 欄（案）

基底の可換環ごとの族として持つ（係数の拡大・制限が要るため）。名前は案。最終の型は BS-W14 の段 0 で ⑤a が drafts の使い方に合わせて詰める。

| 欄 | 内容 | HA など | 今の模型での状況 | 使う drafts |
| --- | --- | --- | --- | --- |
| `CAlg S` | 各可換環 S の E∞-S 代数の ∞ 圏（準圏） | HA 3.1 | `CAlg_R` | 全体 |
| `forget S` | U : CAlg S → D(S) | HA 3.2.2 | `cAlgForgetDerived` | 全体 |
| `forget_conservative` | U は保存的 | HA 3.2.2.6 | 要確認 | A5・A6 |
| `forget_preservesLimits` | U は極限を作る・保つ | HA 3.2.2.5 | 一部（`cAlgForgetDerived_mapJoinCone_isLimit_of_transport`） | A5・A6・Sheaves |
| `forget_preservesSifted` | U は sifted 余極限を作る・保つ | HA 3.2.3.1 | 模型の側（`Operad/AlgebraSiftedColimits`）、∞ 側は要確認 | A2・A4 |
| `presentable` | CAlg S は表現可能 | HA 3.2.3.5（G12） | なし | Sheaves/CAlgValued |
| `coproduct_tensor` | 余積 ＝ 導来テンソル（U の下で） | HA 3.2.4.7 | 要確認 | A2・A7 |
| `restrict f`・`baseChange f` と随伴 | 環の射 f : S → T に沿う制限と係数の拡大、U との両立 | M13 | drafts で sorry（`DerivedGeneral/ScalarRestriction`） | A2・A5・A7 |
| `discrete S` | 離散な可換 S 代数の埋め込み、U ∘ discrete は環そのもの | HA 7.1.3.18 | `algebraEmbedding` | 全体 |
| `pi0` | π₀（H⁰ の環）の関手と、H⁰(U X) との一致 | HA 7.1.3.15 | 模型の中身で（`cAlgH0Ring`） | A2・A4・DerivedGeneral |
| `ofCosimplicial` | 余単体的可換環から CAlg への関手と、U ∘ それ ≃ Tot | G-A1-11、Berger–Fresse | drafts で sorry（`totEInfinityFunctor`） | A0・A1・Shared |
| `ofCdga` | 可換 dg 代数から CAlg への関手と U との両立 | — | drafts（`cdgaCAlg`、`formsCAlg`） | A1 |
| `powerOp0` | E∞-F_p 代数の P⁰ と、その性質（Frobenius 半線形など、BS Lemma 8.4 が使う形） | M14、Lurie DAG XIII Constr 2.2.6 | なし（drafts `Shared/EInfinityPowerOperation`） | A4 |

- descendability（M15）は Mod_R（D(R)）の言葉なので、界面に入れない（U の像で述べる）。
- 欄は BS が実際に使うものに限る。足りなければ BS-W14 の段 0 で足す。

## 3. 置き場所

- 構造の定義：`SerrePositivity/EInfinity/Interface/`（新設）。InfinityCategories と D(R)（`derivedInfinityCategory`）だけを import し、Barratt–Eccles を import しない。KL-W1 の移動の後は、改名表で import を直す。
- 実例 `barrattEcclesTheory`：`SerrePositivity/EInfinity/BarrattEccles/Theory.lean`（11-10、BS-W14 §3 の 2）。証明済みの欄だけ本体、残りは drafts（`drafts/Shared/BarrattEcclesTheory.lean`）。
- BS の drafts：`(E : EInfinityTheory)` を引数に取る形へ書き換える。模型の中身に触れていた 8 本（README §1 の (a)(b)）は、`pi0`・`ofCosimplicial`・`ofCdga`・`powerOp0` の欄を通す形にする。

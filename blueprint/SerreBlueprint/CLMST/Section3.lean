import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§3 F-signature and Hilbert-Kunz multiplicity via perfection in positive characteristic" =>
%%%
number := false
tag := "clmst-3"
%%%

CLMST（Cai–Lee–Ma–Schwede–Tucker, arXiv 2209.04046v4）§3 の項目と、本体の宣言との対応。本文は対応表（`research/clmst-coverage`）の照合の理由で、論文の本文の写しではない。

:::definition "clmst_eq_3_0_0_1"
**式 (3.0.0.1)**　正標数での有限段と p 冪根拡大の挟み込み。対応表の状態：なし。

原典 PDF p.22; layout L1158。原典の「正標数での有限段と p 冪根拡大の挟み込み」を同じ仮定・結論で述べる宣言を確認できない。 本体の等標数の長さ代数は conductor を用いる別構成であり、原典の Frobenius 非分裂イデアルと不変量の同一視ではない。

外の文献：PT18 Lemma 2.3

:::

:::definition "clmst_3_0_1"
**定義 3.0.1**　Frobenius 非分裂イデアル I\_e。対応表の状態：なし。

原典 PDF p.22; layout L1167。原典の「Frobenius 非分裂イデアル I\_e」を同じ仮定・結論で述べる宣言を確認できない。 本体の等標数の長さ代数は conductor を用いる別構成であり、原典の Frobenius 非分裂イデアルと不変量の同一視ではない。

:::

:::proposition "clmst_3_0_2"
**命題 3.0.2**　I\_e の Frobenius 遷移と colon の関係。対応表の状態：なし。

原典 PDF p.23; layout L1178。原典の「I\_e の Frobenius 遷移と colon の関係」を同じ仮定・結論で述べる宣言を確認できない。 本体の等標数の長さ代数は conductor を用いる別構成であり、原典の Frobenius 非分裂イデアルと不変量の同一視ではない。

外の文献：BST12 Lemma 3.4、Tuc12 Lemma 4.4

:::

:::definition "clmst_3_0_3"
**定義 3.0.3**　完全化の非分裂イデアル I\_infty。対応表の状態：なし。

原典 PDF p.23; layout L1191。原典の「完全化の非分裂イデアル I\_infty」を同じ仮定・結論で述べる宣言を確認できない。 本体の等標数の長さ代数は conductor を用いる別構成であり、原典の Frobenius 非分裂イデアルと不変量の同一視ではない。

:::

:::proposition "clmst_3_0_4" (uses := "clmst_3_0_2")
**命題 3.0.4**　I\_infty と I\_e の比較。対応表の状態：なし。

原典 PDF p.23; layout L1196。原典の「I\_infty と I\_e の比較」を同じ仮定・結論で述べる宣言を確認できない。 本体の等標数の長さ代数は conductor を用いる別構成であり、原典の Frobenius 非分裂イデアルと不変量の同一視ではない。

:::

:::definition "clmst_3_0_5"
**定義 3.0.5**　F signature と Hilbert–Kunz 重複度。対応表の状態：なし。

原典 PDF p.23; layout L1213。原典の「F signature と Hilbert–Kunz 重複度」を同じ仮定・結論で述べる宣言を確認できない。 本体の等標数の長さ代数は conductor を用いる別構成であり、原典の Frobenius 非分裂イデアルと不変量の同一視ではない。

外の文献：HL02、Kun76、Mon83、PT18、SVdB97、Tuc12

:::

:::lemma_ "clmst_3_0_6" (uses := "clmst_eq_3_0_0_1")
**補題 3.0.6**　I\_infty の有限段への縮約と colon イデアルによる包含。対応表の状態：なし。

原典 PDF p.24; layout L1229。原典の「I\_infty の有限段への縮約と colon イデアルによる包含」を同じ仮定・結論で述べる宣言を確認できない。 本体の等標数の長さ代数は conductor を用いる別構成であり、原典の Frobenius 非分裂イデアルと不変量の同一視ではない。

:::

:::theorem "clmst_3_0_7" (uses := "clmst_2_2_6, clmst_3_0_4, clmst_3_0_6")
**定理 3.0.7**　完全化による F signature と HK 重複度の表示。対応表の状態：なし。

原典 PDF p.24; layout L1261。原典の「完全化による F signature と HK 重複度の表示」を同じ仮定・結論で述べる宣言を確認できない。 本体の等標数の長さ代数は conductor を用いる別構成であり、原典の Frobenius 非分裂イデアルと不変量の同一視ではない。

外の文献：PT18 Lemma 4.13、PT18 Theorem 4.3

:::


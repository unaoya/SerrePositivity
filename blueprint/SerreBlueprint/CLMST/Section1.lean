import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§1 Introduction" =>
%%%
number := false
tag := "clmst-1"
%%%

CLMST §1 の項目と、本体の宣言との対応。本文は対応表（`research/clmst-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "clmst_eq_"
*式 (\*)*　F signature の非分裂イデアル I\_e による極限表示。対応表の状態：なし。

原典 PDF p.3; layout L106。原典の「F signature の非分裂イデアル I\_e による極限表示」を同じ仮定・結論で述べる宣言を確認できない。 導入で参照される本節の定理は edges.csv に記録し、導入の同値・不等式全体の形式化と区別する。

:::

:::theorem "clmst_A" (uses := "clmst_4_0_22, clmst_4_1_5")
*定理 A*　perfectoid 不変量の基本不等式。対応表の状態：なし。

原典 PDF p.4; layout L188。原典の「perfectoid 不変量の基本不等式」を同じ仮定・結論で述べる宣言を確認できない。 導入で参照される本節の定理は edges.csv に記録し、導入の同値・不等式全体の形式化と区別する。

外の文献：HL02、HY02、WY00

:::

:::theorem "clmst_B" (uses := "clmst_5_2_1, clmst_5_2_2")
*定理 B*　BCM 正則性と正の perfectoid signature。対応表の状態：なし。

原典 PDF p.5; layout L204。原典の「BCM 正則性と正の perfectoid signature」を同じ仮定・結論で述べる宣言を確認できない。 導入で参照される本節の定理は edges.csv に記録し、導入の同値・不等式全体の形式化と区別する。

外の文献：AL03、HL02

:::

:::theorem "clmst_C" (uses := "clmst_6_0_1")
*定理 C*　有限準エタール分裂拡大の変換則。対応表の状態：なし。

原典 PDF p.5; layout L222。原典の「有限準エタール分裂拡大の変換則」を同じ仮定・結論で述べる宣言を確認できない。 導入で参照される本節の定理は edges.csv に記録し、導入の同値・不等式全体の形式化と区別する。

外の文献：CRST18、HL02、VK12

:::

:::theorem "clmst_D" (uses := "clmst_7_0_12, clmst_7_0_2")
*定理 D*　局所基本群と類群の捩れの有限性。対応表の状態：なし。

原典 PDF p.5; layout L238。原典の「局所基本群と類群の捩れの有限性」を同じ仮定・結論で述べる宣言を確認できない。 導入で参照される本節の定理は edges.csv に記録し、導入の同値・不等式全体の形式化と区別する。

外の文献：CR22、CRST18

:::

:::theorem "clmst_E" (uses := "clmst_4_0_20, clmst_4_1_4")
*定理 E*　perfectoid 不変量による正則性の特徴づけ。対応表の状態：なし。

原典 PDF p.6; layout L277。原典の「perfectoid 不変量による正則性の特徴づけ」を同じ仮定・結論で述べる宣言を確認できない。 導入で参照される本節の定理は edges.csv に記録し、導入の同値・不等式全体の形式化と区別する。

外の文献：Kun76、WY04

:::

:::theorem "clmst_F" (uses := "clmst_5_2_5")
*定理 F*　perfectoid HK 重複度による BCM 閉包と extended plus closure の検出。対応表の状態：なし。

原典 PDF p.6; layout L285。原典の「perfectoid HK 重複度による BCM 閉包と extended plus closure の検出」を同じ仮定・結論で述べる宣言を確認できない。 導入で参照される本節の定理は edges.csv に記録し、導入の同値・不等式全体の形式化と区別する。

外の文献：HH90

:::

:::theorem "clmst_G" (uses := "clmst_5_4_11")
*定理 G*　BCM 有理性と有理 signature の正値性。対応表の状態：なし。

原典 PDF p.7; layout L321。原典の「BCM 有理性と有理 signature の正値性」を同じ仮定・結論で述べる宣言を確認できない。 導入で参照される本節の定理は edges.csv に記録し、導入の同値・不等式全体の形式化と区別する。

外の文献：ST24

:::


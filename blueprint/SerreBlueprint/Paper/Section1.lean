import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§1 Introduction" =>
%%%
number := false
tag := "paper-1"
%%%

本論文 §1 の項目と、本体の宣言との対応。本文は対応表（`research/paper-coverage`）の照合の理由で、論文の本文の写しではない。

:::theorem "paper_1_1" (uses := "paper_eq_5_10, paper_eq_5_11, paper_2_2, paper_2_3, paper_2_5, paper_2_6, paper_3_1, paper_4_7, paper_5_1, paper_5_2, paper_5_5, paper_5_6, ext_Stacks_03QH, ext_Stacks_0BRI, ext_Stacks_0BRJ")
**定理 1.1**　Serreの交点重複度の狭義正値性。対応表の状態：未証明の入力に依存。

原典 PDF p.1 / layout L27。一般の正則局所環と非零有限生成加群、有限長テンソルと相補次元からchi\>0という主張の型は一致する。宣言自身はsorryなしだが、完全な証明はperfectoidizationのE3入力・通常のK0降下・漸近K0降下の三つのsorry付き入力に依存する。

宣言：`SerrePositivity.main_statement`、`SerrePositivity.core_statement`

外の文献：Stacks 03QH、Stacks 0BRI、Stacks 0BRJ

:::

# §1.2 Proof strategy

%%%
number := false
tag := "paper-1-2"
%%%

:::definition "paper_fig_1" (uses := "paper_eq_5_18, paper_5_2, paper_5_6")
**図 Figure 1**　二つのnorm比較の図。対応表の状態：一部。

原典 PDF p.3 / layout L127。二つの有限群和の等式に対応する宣言はあるが、図全体のデータやc\_sigma、b\_sigma,gammaの整合的な一括実現は独立の宣言にしていない。比較の適用には下記の未証明降下入力が残る。

宣言：`SerrePositivity.firstComparison`、`SerrePositivity.Section5.secondComparison_of_approximation`

:::

# §1.3 Consequences

%%%
number := false
tag := "paper-1-3"
%%%

:::corollary "paper_1_2" (uses := "paper_1_1, ext_Jannsen_A_4_1, ext_Skalit15_3_10, ext_Skalit15_3_4, ext_Skalit15_3_5, ext_Skalit15_3_8")
**系 1.2**　有限なstrict transform交叉と重複度積の下界。対応表の状態：なし。

原典 PDF p.4 / layout L155。associated gradedのテンソルTの次元≤1という条件からchiとHilbert–Samuel重複度積の不等式、および等号とdim T=0の同値をまとめる宣言を確認できない。KST/DerivedBlowupのチャートや主定理だけをこの系の証明とはしない。

外の文献：Jannsen A.4(1)、Skalit15 3.10、Skalit15 3.4、Skalit15 3.5、Skalit15 3.8

:::


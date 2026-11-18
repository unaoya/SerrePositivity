import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "§3 Structure theorem for finitely presented subtrusions" =>
%%%
number := false
tag := "rydh-3"
%%%

Rydh §3 の項目と、本体の宣言との対応。本文は対応表（`research/rydh-coverage`）の照合の理由で、原典の本文の写しではない。

:::definition "rydh_3_1"
*記法 3.1*　既約成分の一般点集合。対応表の状態：なし。

原典 PDF p.12, y=153.3。blowup・strict transform・refinement・fppf・surjectiveの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：RG71

:::

:::lemma_ "rydh_3_2"
*補題 3.2*　一般点を含む集合からの全射性。対応表の状態：一部（special）。

原典 PDF p.12, y=216.6。アフィン基底のすべての極小素点を含む開集合の逆像の閉包からの全射性を得る。任意の部分集合や一般の S-subtrusive 射の範囲は含まない。

宣言：`SerrePositivity.AlgebraicGeometry.surjective_openImage_of_vCover_affine_of_contains_minimalPrimes`

:::

:::definition "rydh_3_3"
*定義 3.3*　爆発と狭義変換。対応表の状態：一部（component）。

原典 PDF p.12, y=298.8。有限生成中心の爆発の固有性、中心の補集合上の同型、選んだ開の逆像のスキーム論的閉包による狭義変換を与える。原典は開を中心の補集合に固定し、その準コンパクト性も述べる。

宣言：`SerrePositivity.AlgebraicGeometry.blowup`、`SerrePositivity.AlgebraicGeometry.blowupπ`、`SerrePositivity.AlgebraicGeometry.blowupπ_isProper`、`SerrePositivity.AlgebraicGeometry.blowupπ_restrict_complement_isIso`、`SerrePositivity.AlgebraicGeometry.strictTransform`、`SerrePositivity.AlgebraicGeometry.strictTransformπ`

外の文献：Stacks 081T

:::

:::proposition "rydh_3_4" (uses := "rydh_3_2")
*注意 3.4*　狭義変換の全射性。対応表の状態：一部（special）。

原典 PDF p.12, y=403.4。Noether 基底・コンパクトな有限型の v 被覆・稠密開を入力とし、爆発の狭義変換が全射になる。一般の基底での結論は含まない。

宣言：`SerrePositivity.AlgebraicGeometry.strictTransformπ_surjective_of_vCover`

外の文献：lazard\_autour、olivier\_sem\_samuel

:::

:::lemma_ "rydh_3_5"
*補題 3.5*　準コンパクト稠密開上の平坦性。対応表の状態：一部（special）。

原典 PDF p.12, y=507.0。被約 Noether アフィン基底で準コンパクトな始域なら稠密平坦開を得る。Noether 基底では開は準コンパクト。原典の一般点集合の準コンパクト性だけを仮定する基底には拡張していない。

宣言：`SerrePositivity.AlgebraicGeometry.exists_dense_open_flat_restrict_of_compactSpace`

外の文献：egaIV

:::

:::proposition "rydh_3_6" (uses := "rydh_3_4, rydh_3_5")
*命題 3.6*　爆発による狭義変換の平坦化。対応表の状態：一部（special）。

原典 PDF p.12, y=611.8。被約 Noether アフィン基底では、稠密平坦開上での平坦化からその補集合を中心とする全射な爆発を得る。狭義変換は平坦かつ全射であり、Noether 基底上の有限型性から有限表示。一般点集合の準コンパクト性だけを仮定する基底は含まない。

宣言：`SerrePositivity.AlgebraicGeometry.exists_dense_open_flat_restrict_of_compactSpace`、`SerrePositivity.AlgebraicGeometry.exists_admissible_flat_strictTransformπ_of_finiteType`、`SerrePositivity.AlgebraicGeometry.strictTransformπ_surjective_of_vCover`、`SerrePositivity.AlgebraicGeometry.exists_fppf_blowup_refinement_of_flat_strictTransform_vCover`

外の文献：RG71、Stacks 081T

:::

:::proposition "rydh_3_7" (uses := "rydh_3_2, rydh_3_5")
*命題 3.7*　一般点集合が準コンパクトな基底での細分。対応表の状態：一部（special）。

原典 PDF p.13, y=119.0。被約アフィン基底で極小素点集合が準コンパクト、始域もアフィンのときに fppf–proper 細分を与える。一般の始域・非被約基底および普遍開の場合の nilimmersion の追加結論は含まない。

宣言：`SerrePositivity.AlgebraicGeometry.exists_fppf_proper_refinement_vCover_affineReduced_compact_minimalPrimes`

外の文献：RG71、egaIV

:::

:::definition "rydh_3_8"
*定義 3.8*　全整閉スキームの定義。対応表の状態：なし。

原典 PDF p.13, y=529.5。TIC の代用として極小素点集合を準コンパクトにする整拡大を供給するが、すべての点閉包の正規性とその分数体の代数閉性を要求する TIC の定義には対応しない。

外の文献：hochster\_TIC

:::

:::proposition "rydh_3_9"
*Properties 3.9*　全整閉スキームの性質。対応表の状態：なし。

原典 PDF p.13, y=619.4。blowup・strict transform・refinement・fppf・surjectiveの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：artin\_Hensel-join、hochster\_TIC

:::

:::theorem "rydh_3_10" (uses := "rydh_3_6, rydh_3_7")
*定理 3.10*　アフィンまたは Noether 基底の fppf–固有細分。対応表の状態：一部（special）。

原典 PDF p.14, y=428.8。任意のアフィン基底で、始域のアフィン性や基底の Noether 性を要求せず fppf–proper 細分を与える。一般の非アフィン Noether 基底と、元の射が普遍開の場合の nilimmersion の追加結論は含まない。

宣言：`SerrePositivity.AlgebraicGeometry.exists_fppf_proper_refinement_vCover_affineBase`、`SerrePositivity.AlgebraicGeometry.exists_fppf_proper_refinement_vCover_affineNoetherian`

外の文献：egaIV

:::

:::theorem "rydh_3_11" (uses := "rydh_1_4, rydh_3_2, rydh_3_9")
*定理 3.11*　準有限な被覆の開被覆–有限細分。対応表の状態：なし。

原典 PDF p.14, y=725.7。blowup・strict transform・refinement・fppf・surjectiveの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：egaIV、voevodsky\_homology

:::

:::theorem "rydh_3_12" (uses := "rydh_3_10, rydh_3_11")
*定理 3.12*　準コンパクト開被覆–固有細分。対応表の状態：なし。

原典 PDF p.15, y=556.6。アフィン基底で fppf–proper 細分を与える 3.10 の型を確認したが、3.12 の第一因子は準コンパクト開被覆。アフィン v 被覆への細分にも、この二因子を同時に与える結論はない。

外の文献：egaIV

:::

:::proposition "rydh_3_13" (uses := "rydh_3_10, rydh_3_12")
*注意 3.13*　qcqs 基底への一般化。対応表の状態：なし。

原典 PDF p.15, y=725.7。blowup・strict transform・refinement・fppf・surjectiveの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：TT

:::

:::proposition "rydh_3_14" (uses := "rydh_3_10, rydh_3_12, rydh_3_6, rydh_4_1, rydh_4_2")
*注意 3.14*　有限型から有限表示への拡張。対応表の状態：なし。

原典 PDF p.16, y=153.3。blowup・strict transform・refinement・fppf・surjectiveの関連宣言を検索し、この項目の仮定から結論を直接得る型を確認できなかった。

外の文献：RG71、TT、conrad\_nagata、egaI\_NE

:::


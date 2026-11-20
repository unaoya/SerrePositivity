-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Monoidal.Arrow
import Mathlib.CategoryTheory.Monoidal.PushoutProduct
import SerrePositivity.HomotopicalAlgebra.Monoidal.CofibrantTensor
import SerrePositivity.HomotopicalAlgebra.Monoidal.ModelCategory
import SerrePositivity.HomotopicalAlgebra.Monoidal.MonoidAxiom

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 4.5 Modules over Commutative Algebras" =>
%%%
number := false
tag := "ha-4-5"
%%%

HA 4.5 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 4.5.4 Rectification of Commutative Algebras

%%%
number := false
tag := "ha-4-5-4"
%%%

:::definition "ha_4_5_4_1" (lean := "CategoryTheory.MonoidalCategory.Arrow.pushoutProduct, CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.symmetricCategory")
*HA 記法 4.5.4.1*　Rectification of Commutative Algebras (p. 606)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=606)）。対応表の状態：一部（component）。

*主張*　押し出し積を $`n` 回反復した $`f:X\to Y` の射 $`\wedge^n(f)\to Y^{\otimes n}` は対称群作用と両立し、余不変対象を取ると $`\sigma^n(f):\operatorname{Sym}^n(Y;X)\to\operatorname{Sym}^n(Y)` になる。

KB-W2型再照合：仮定：押し出しを持つモノイダル圏（Lean は二項構成に対称性も全余極限も要求しない。矢印圏の対称構造は始対象を持つ Cartesian 閉の場合）。結論：HA の二項押し出し積と、特殊な場合の矢印圏の対称構造に一致。Σₙ 同変反復と余不変量の写像 σⁿ は型に含まれない。

反復押し出し積の始域には、少なくとも一つの因子に $`X` を使ったテンソルの張り合わせが現れる。対称性は因子の置換に由来する。

:::

:::definition "ha_4_5_4_2" (lean := "SerrePositivity.Quillen.HasMonoidAxiom, SerrePositivity.Quillen.tensorCells_retracts_le_weakEquivalences")
*HA 定義 4.5.4.2*　Rectification of Commutative Algebras (p. 606)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=606)）。対応表の状態：一部（component）。

*主張*　冪余ファイブレーションとは、全ての反復押し出し積が対称群作用付き対象の射影的モデル構造で余ファイブレーションとなる射である。

KB-W2型再照合：仮定：モノイダル圏とモデル構造（Lean は組合せ性と対称性を要求しない）。結論：指定宇宙のテンソル生成セルとそのレトラクトの弱同値性（F1 のモノイド公理の範囲に一致）。F2 の組と Σₙ 射影モデルでの F3 は型に含まれない。

始対象からの射がこの条件を満たせば対象を冪余ファイブラントと呼ぶ。freely powered の条件は、モノイド公理、左固有性と指定の図式圏の余ファイブレーションの余ファイブラント対象間での生成性、全余ファイブレーションの冪余ファイブレーション性である。

:::

:::proposition "ha_4_5_4_3" (lean := "SerrePositivity.Quillen.pushoutProduct_cofibration")
*HA 注意 4.5.4.3*　Rectification of Commutative Algebras (p. 607)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=607)）。対応表の状態：一部（special）。

*主張*　余ファイブレーションの反復押し出し積は作用を忘れれば余ファイブレーションで、元の射が自明なら自明である。冪余ファイブレーションでは対称群作用付きの圏で余ファイブレーション性を要求する。

KB-W2型再照合：仮定：モデル圏のテンソルが Quillen 二関手で、f が余ファイブレーション（HA の仮定の下で f を両入力とする）。結論：f□f が底で余ファイブレーション（n=2 で作用を忘れた主張に一致）。全ての n、自明性および Σₙ 射影余ファイブレーション性はこの型に含まれない。

モノイダルモデル構造の押し出し積公理で、作用を忘れた主張を反復して得る。射影的モデル構造での条件には、対称群作用に関した追加の制約がある。

:::

:::lemma_ "ha_4_5_4_10" (lean := "SerrePositivity.Quillen.pushoutProduct_cofibration, SerrePositivity.Quillen.tensor_isCofibrant")
*HA 補題 4.5.4.10*　Rectification of Commutative Algebras (p. 608)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=608)）。対応表の状態：一部（special）。

*主張*　組合せ的対称モノイダルモデル圏の二つの射影的図式圏で余ファイブレーションを取ると、外部押し出し積は添字圏の積上の射影的余ファイブレーションである。

KB-W2型再照合：仮定：Quillen テンソルを持つモデル圏で底の二つの余ファイブレーションまたは余ファイブラント対象（Lean が強い：添字圏は両方とも一点、対象については組紐付き閉の場合）。結論：押し出し積が余ファイブレーション、テンソル積が余ファイブラント（その場合に二つの結論が一致）。一般の二つの射影図式の外部積は型に含まれない。

各変数の添字を独立に動かし、テンソルを外部積として取る。始対象からの射に適用すると、余ファイブラントな二つの図式の外部テンソルが余ファイブラントとなる。

:::


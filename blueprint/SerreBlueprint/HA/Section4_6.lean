import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 4.6 Duality" =>
%%%
number := false
tag := "ha-4-6"
%%%

HA 4.6 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 4.6.1 Duality in Monoidal ∞-Categories

%%%
number := false
tag := "ha-4-6-1"
%%%

:::definition "ha_4_6_1_1" (lean := "CategoryTheory.ExactPairing")
*HA 定義 4.6.1.1*　Duality in Monoidal ∞-Categories (p. 616)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=616)）。対応表の状態：Mathlib にある。

*主張*　双対データは $`1\to X\otimes X^\vee` と $`X^\vee\otimes X\to1` が二つの三角恒等式を満たすことであり、$`X^\vee` を $`X` の右双対とする。

仮定：通常のモノイダル圏と対象 X、Y（HA と一致）。結論：評価 Y⊗X → 1、余評価 1 → X⊗Y と二つの三角恒等式を双対データとして定義する（HA と一致）。HA がこの項目で扱う通常圏の定義と一致する。

一方の恒等式では $`X` に余評価を左から加えてから右側を評価する。もう一方では $`X^\vee` に余評価を右から加えてから左側を評価する。左右を区別するためにテンソルの順序を固定する。

:::


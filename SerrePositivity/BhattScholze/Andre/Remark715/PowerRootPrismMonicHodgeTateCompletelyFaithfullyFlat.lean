module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicHodgeTateCompletelyFlat
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PowerRootHodgeTateReduction

/-!
# André R1：Hodge–Tate 商の完全忠実平坦性の移行

## 概要

元の正次数モニック源の Hodge–Tate 商の完全忠実平坦性は、hpR を要求しない証明を使う。
BS Rem 7.15（著者版 p.62）の元の候補を変更しない。

## 方針

旧 hpR 付き公開定理の全呼出しを
`powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional` へ移す。
原典の p ねじれなしへの帰着とは異なる実源の純性による経路。

## 規約

旧定理は不要になったため削除した。正次数仮定は忠実性のため保持する。

## 使われ方

既存の import 経路で無条件版を公開し、元の H の二元完全平坦性へ渡す。
-/

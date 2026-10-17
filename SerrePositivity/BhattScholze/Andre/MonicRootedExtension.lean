module

public import SerrePositivity.BhattScholze.Andre.OrdinaryMonicRoot
public import SerrePositivity.BhattScholze.Andre.MonicRelation
public import SerrePositivity.BhattScholze.Andre.PerfectPrismMonicCandidate
public import SerrePositivity.BhattScholze.Andre.MonicPDFlat
public import SerrePositivity.BhattScholze.Andre.MonicRawPDivision
public import SerrePositivity.BhattScholze.Andre.MonicFamilyRawRegular

/-!
# André E1・E2 の集約

## 概要

BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）のモニック根付き拡大に向けた証明を集約する。

## 方針

通常のモニック商の自由性と独立変数の関係式の正則性から準備し、
任意の関係族の δ 除算から perfectoid 根候補を構成する。
原典の Prop 7.11 を使う経路とは異なる pd 計算による構成を目指す。

## 規約

目標には正次数を要求する。通常根添加の結果だけで perfectoid 拡大の存在を主張しない。
目標 `exists_monicRootedPerfectoidExtension` は未証明であり宣言しない。

## 使われ方

ルートの公開入口から本レーンの検証済み結果を読み込む。
-/

module

public import SerrePositivity.BhattScholze.Inputs.ArcExcision
public import SerrePositivity.BhattScholze.PerfectoidizationExcision

/-!
# 環の excision の引用とその二つの系の集約
## 概要
BS 著者版 Cor 8.12（印刷 p.69）の環の引用と、標準閉側四角形に関する二つの系を公開する。
## 方針
既存の引用モジュールと、その引用だけから導いた系のモジュールを読み込む。
## 規約
引用入力は ArcExcision の一件であり、系の証明に新しい引用を追加しない。
## 使われ方
ルートの一行の import と、CLMST-D・KL-T への公開入口に使う。
-/

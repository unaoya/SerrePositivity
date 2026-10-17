module

public import SerrePositivity.BhattScholze.PerfectoidIdealIdempotent
public import SerrePositivity.BhattScholze.PerfectoidAlmostExtension

/-!
# B5 の公開入口
## 概要
BS 著者版 Lemma 10.3（印刷 pp.78–79）、Remark 10.7（印刷 p.80）の冪等性、
Prop 10.2（印刷 p.78）の導来完備 almost 零加群の拡大閉性をまとめる。
## 方針
既存 B3・B4 と、完全 prism による実完備導来 tensor の一般定理を再利用する。
## 規約
核と mod p 冪像の既存定義を保持し、全定理は追加の引用なしに証明されている。
## 使われ方
ルートの一つの import と、KL-T・CLMST への証明済み公開定理の受渡しに使う。
-/

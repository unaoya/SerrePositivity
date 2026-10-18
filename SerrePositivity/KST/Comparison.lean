module

public import SerrePositivity.KST.Comparison.DoldKanGL
public import SerrePositivity.KST.Comparison.ComponentSubcomplex
public import SerrePositivity.KST.Comparison.DGAlgebra
public import SerrePositivity.KST.Comparison.GammaH0Ring
public import SerrePositivity.KST.Comparison.ConnectiveTruncation
public import SerrePositivity.KST.Comparison.GrouplikeGL
public import SerrePositivity.KST.Comparison.RegularBar
public import SerrePositivity.KST.Comparison.BarEdge
public import SerrePositivity.KST.Comparison.RegularBarContraction
public import SerrePositivity.KST.Comparison.GrouplikeTranslations

/-!
# K-L2：比較定理の入口

概要：KST §2 の比較定理に向けた宣言を公開する。
方針：SS03 (2.9) の AW 環、π₀ の環、KST 式 (2.2) の単体的モノイドを公開する。
規約：π₀ĜL の群性と Γ と H⁰ の環比較を証明する。群完備化、H_*、plus、K の比較は残工程。
使われ方：K-L2 の対象ビルドと公理監査。比較定理の完成を主張する入口ではない。
-/

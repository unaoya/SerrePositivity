module

public import SerrePositivity.KST.LocalizingInvariants.CoreFlag.All
public import SerrePositivity.KST.LocalizingInvariants.CoreFlag.KanPullbackCofinality

/-!
概要：Sp-8 (1)(2) と K-cof の Kan 引き戻し入力の実証明を合わせた独立集約。
方針：既存 All の上に K-cof 所有の入力定義と今回の供給を追加する。
規約：入力定義は既存 All に依存するため、この集約を All から import してはいけない。
使われ方：Sp-8 (3)、K-cof への供給の公開入口。
-/

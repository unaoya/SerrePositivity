# F1 の規約

概要：fibration・straightening・Yoneda の実装を配置する。
方針：`formalization-plans/infinity-core-F1.md` §1 の順に進める。
規約：namespace は `SerrePositivity.InfinityCategories`。Core・Coherent・DGNerve・Derived は参照のみ。
使われ方：Kerodon 第 5・6・7.3・8 章に対応する一般論。

## F1a：辺と fibration

Kerodon Definition 5.1.1.1 に従い、辺は一単体として表す。
cartesian 辺では最後の辺を固定した最後の外側ホーン、cocartesian 辺では最初の辺を
固定した零番目の外側ホーンの相対持ち上げ性を要求する。次元は `n + 2` とする。

Kerodon Definition 5.1.4.1 に従い、fibration は内ホーンの `MorphismProperty.rlp` と
指定端点からの cartesian/cocartesian 辺の存在を組み合わせる。
持ち上げの選択は構造に含めない。底の quasicategory 性は定義に含めない。
`Core/RightFibration.lean` の right/left fibration はそれぞれ cartesian/cocartesian
fibration に接続する。底変換の射は `pullback.snd p q` とする。

## 後続工程の境界

F1d 着手前に Kerodon 5.3〜5.6 を照合し、left fibration・𝒮 値の場合を先に完成させる
文言と証明方針を本書に記録・報告する。
𝒮 と Cat_∞ は γ1 の coherent nerve を用いる。その極限・余極限は F2 の担当とする。

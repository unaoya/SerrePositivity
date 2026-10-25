module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.Generators
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactEndpoints

/-!
概要：P-f レーンの独立集約と引き継ぎ。既存の Presentable 集約は編集しない。
方針：N の局所対象を再利用し、小さい生成辺族を明示する。
規約：局所置換の存在を未証明の入力で置き換えて完成扱いしない。
使われ方：HTT 5.5.4.15 の実装作業。

## 引き継ぎ（2026-10-25、設計変更提案による停止）

現在地：f1 の生成族・全パラメータ Hom 判定と生成系の比較を検証済み。
f2 の準備として、全生成辺の両端点に共通の正則 compact 濃度を検証済み。
局所置換・反射の存在・局所対象圏の presentable 性は未証明。P-1 f は未完了。

設計変更案：f2 の直接の小対象論法を、原典の飽和射圏経路に変更する。
通常の小対象論法は通常圏の厳密な lifting を構成するため、ho(C) への適用では
全写像空間の局所性を得られない。モデル圏用の LocalFibrantApproximation は
ModelCategory SSet 等を要求し、主経路の入力には使えない。
この案は未採用で、以下の存在性を新たな仮定として追加していない。

残り（依存順、見積もりは実装・ビルド状況により再評価）：
* f2a：強飽和生成閉包の辺を対象とする全射圏の presentable 性
  （5.5.4.13–14、16–40 時間）。compact な射の小さい全部分模型と Ind 表示を構成し、
  pushout・三角形の同時細分で像の強飽和性を証明する。
* f2b：固定始点 x の閉包内射の圏の presentable 性
  （5.5.5.11・14、8–20 時間）。source 評価の fiber を元の coslice と比較する。
  並行 P の e5 の引き戻し accessibility は公開後に読み取り専用で利用する候補。
* f2c：その圏の終対象から、元の x を始点とする閉包内の辺を取り出し、
  pushout と Hom fiber で終点の局所性を証明（5.5.5.12–14、8–20 時間）。
* f3：N の LocalReplacementReflection に接続し、coherent な反射を構成。
  局所対象の accessibility と反映による余完備性から、その presentable 性も証明
  （5.5.4.2・15(2)(3)、8–20 時間）。
* f4：N の LocalReplacementSaturation で生成閉包との一致を得て、同じ反射が
  反転する元の辺との同値を証明（5.5.4.15(4)、4–10 時間）。
* f5：独立集約・監査・主経路の仮定検査・閉包 digest の検査と保存（1–3 時間）。

主要宣言：isLocalObject_range_iff、isLocalObject_range_iff_constantHom_bijective、
localEquivalenceHom_range_iff_constantHom_bijective、localEquivalences_eq_iff_generators、
localEquivalences_eq_iff_localObjects、exists_regular_compactEndpoints。

依存と提供：LocalEquivalences・LocalHomCriterion・Definition・ObjectCompactCardinals を
読み取り専用で利用。公開済みの N の条件付き反射・強飽和性は再実装しない。
一般の任意辺局所化・分数 API を新設する案ではなく、presentable 圏の存在部分に限定する。
禁止 import：Inputs/Homotopy/KanQuillen。既存の Presentable・HomotopyLimits は変更禁止。
所有はこの Localization/ と scripts/audit_infinity_presentable_localization.lean の新規分だけ。
保存対象は All・Generators・CompactEndpoints と独立監査の4ファイル。
既知の問題：存在部分が未実装であり、条件付き N の再包装では解消しない。
次の一手：設計変更案の判断後、f2a の元の射圏と小さい compact 全部分模型から着手する。
-/

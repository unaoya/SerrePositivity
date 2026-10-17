# U17a・U13d の実装記録

正本：`dg-theory.md` §15.7 U17a、§15.3 U13d、§17.86–17.87。

## 担当・境界

- U17a は `DifferentialGraded/Verdier/` に新設する。既存の有限 cell・Perf・Mathlib の三角構造と指定局所化を再利用する。
- U17b/c の受け渡し先として既存 `karoubiVerdierOrderEquivalence`、`paperRankEquivalence`、`paperSequenceComparison` の型を先に確認した。
- U13d は引用なしの compact ⇒ Perf を検討・実装する。DG-PER 採用が必要となれば採用せずに停止して報告する。
- 既存の dg 合成・KFlatBimodule・cell 系・Quotient・Endomorphism と既存一般論は編集しない。
- 新規ファイルの同名有無を事前確認。新規 sorry・axiom・引用なし。amend・rebase・reset なし。
- ルート import は自分の hunk だけを部分 stage。正本には参照一行のみを追加する。

## 型と数学的区別

`tria(D)` は既存 `DerivedFiniteCellCategoryOver A D Set.univ` を用いる。
S⊆D は明示的 dg 商の full 部分圏と同じ対象添字。S の代表加群の三角閉包を tria(D) 内に取り、
商はその `trW.Localization`、U17b の比較先は既存 `Karoubi` を施した型とする。

一般の Verdier 商の核は三角部分圏の retract 閉包であり、tria(S) そのものと無条件に同一視しない。
Mathlib の `triangEnvelope` は retract も含む厚い閉包なので、その区別を公開 API に保持する。
Karoubi を先に取った側は既存 `karoubiNullEnvelope` をそのまま使う。

## U17a（完了）

- `Verdier/Tria.lean`：既存の有限 cell 本質像を `TriaCategory` とし、
  `triaImage_le_iff_generators` で S の代表対象を含む最小の三角部分圏であることを証明。
- `Verdier/NullObjects.lean`：既存の Verdier 分数計算と三角形の Hom 完全性から
  `verdierQuotient_isZero_iff_retractClosure` を証明。商で恒等射が零なら、分母射を零にでき、
  その錐への retract が得られる。逆は三角関手の核の retract 閉性。
- `triaQuotient_isZero_iff_triaNull` と `triaQuotient_isZero_iff_perfect` で、
  零対象の逆像・thick 閉包・既存の Perf_S の制限が一致する。
- U17b の比較先は `CompletedTriaQuotient`。U17c へは既存の
  `karoubiVerdierOrderEquivalence` をそのまま用い、`triaKaroubiComparison` は
  `paperSequenceComparison` と同じ向きの自然同型。U17b/c 自体を証明済みとはしない。
- A は任意の可換環、D の対象宇宙 v は係数・Hom の宇宙 u と独立、仮定は `Small.{u} D`。
  体・有界性・局所有限性は仮定しない。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.VerdierTria` 成功。
  主要10宣言の `#print axioms` は全て `propext, Classical.choice, Quot.sound` のみ。
  新規 sorry・axiom・引用なし。

## U13d（継続中）

compact ⇒ Perf はまだ未完。引用は採用していない。引用なしの telescope と有限因子分解の経路を検討する。

### U13d2：可算 telescope の有限段階因子分解

- `Perfect/CompactConverseTelescope.lean`：任意の導来対象列 F と遷移射 d に対して、
  余積上の `1-shift` を定義。compact な始域の Hom 上で単射であることを、
  各成分への射影と自然数帰納法で証明した。shift 後も随伴の Hom 加法同型で単射。
- `moduleCompact_telescope_factor`：指定 telescope 三角形への射は有限段階 F n を経由する。
  `moduleCompact_telescope_retract`：compact な telescope 対象はある F n の retract。
  有限高さを有限個の cell と同一視していない。
- 可算添字は `ULift.{u} ℕ`。既存の u-small 余積と compact 性のまま処理し、
  導来圏全体の smallness や Hom_D の追加仮定を置かない。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.CompactConverseTelescope` 成功。
  主要8宣言の公理監査は標準3公理のみ。新規 sorry・axiom・引用なし。
- 残部：semifree filtration の余極限と telescope の比較、有限高さの無限自由 cell から
  有限 cell への因子分解。U13d 全体は未完、引用採用の必要性はまだ確定していない。
- U17a のコミット：`8c9f2e13`。

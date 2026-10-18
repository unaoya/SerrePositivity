# α-S：安定 ∞ 圏と D(S) の安定性

作成日：2026-10-18。状態：S1・S2 完了、S3 実装中。S4〜S7 未完了。
全体の正本は [foundations.md](foundations.md) §1（F3）・§4。
担当は旧 α の A4・A5 と D7。実施経緯・検証結果は各保存単位のコミットメッセージに記す。

## 現在地

S1 は完了。零対象、coslice の始対象としての余極限錐、余極限の一意性、
Λ[2,0]⋆Δ[0] と正方形の同型による押し出し四角形、零角の fiber/cofiber 四角形を定義した。
span の二辺が正方形の下辺・左辺に写ることも証明済み。
S2 は完了。HA 1.1.1.9 の三条件を `IsStable` に定義し、有限極限・有限余極限と
全四角形の引き戻し／押し出しの一致から安定性を証明した（HA 1.1.3.4 の十分な向き）。
外側ホーンの極限／余極限から、指定した辺を持つ fiber/cofiber 四角形を直接構成している。
S3 の準備として、始頂点が h C の始対象となること、零頂点が h C の零対象となること、
始対象・余極限錐の h(sliceUnder) の同型による不変性を直接証明した。
二つの零角を持つ suspension/loop 四角形は全頂点で構成でき、安定性によって同じ四角形が
互いの普遍四角形となる。四角形を関手 ∞ 圏の全部分圏 `suspensionDiagrams`・
`loopDiagrams` に束ね、全ての角の評価が単体的な射であること、安定性による二つの族の
同型とその評価との可換性、始点／終点評価の本質的全射性も証明した。
残る中心は始点／終点評価の充満忠実性（図式の族における普遍余錐／錐の相対充填）。
その証明後に逆関手を取り h C の ΣΩ と選択間の自然同型を構成する。
余錐側では制限射 `coconeRestriction` の fiber `coconeFamily`、その零単体と
`JoinCocone` の同値、coslice からの比較射と零次成分の式を構成した。
左図式を固定した fat join 比較の同値性も証明済み。coslice の比較射自体の同値性と、
余極限性から図式の族における相対充填への接続は未完了。
現段階は関手性・選択の自然な比較・自己同値の完成ではない。
安定性から全有限極限・余極限を導く逆向き、S3 の関手性と自己同値、三角構造・D7 は未完了。
Core・F1・DGNerve・DoldKanComparison・HomotopyLimits は参照専用。
実装は `InfinityCategories/Stable/`、D7 は `InfinityCategories/Derived/` に置く。
引用・追加公理・sorry を使わず、各工程を対象・集約ビルドと公理監査の後に保存する。

## 目標と原典

| 主張 | 原典 | 完成の条件 |
| --- | --- | --- |
| 安定 ∞ 圏の定義 | HA Definition 1.1.1.9 | 零対象、全射の fiber/cofiber の存在、零角の fiber/cofiber 列の同値 |
| 有限極限・余極限による判定 | HA Proposition 1.1.3.4 | S1・S2 以降で実際に使う向きを証明し、未証明の逆向きを主張しない |
| h C の三角構造 | HA Theorem 1.1.2.14 | cofiber 列の像による distinguished triangle、TR1〜TR4、Mathlib Pretriangulated instance |
| 完全関手と自然変換 | HA §1.1.4 | 零・fiber/cofiber 四角形の保存、h の三角関手、完全関手間の自然変換 |
| 四角形の貼り合わせ | HTT Proposition 4.4.2.1 | A2 の join・slice による証明。A6 待ちの箇所が生じれば正確に特定 |
| D(S) の安定性と三角構造の一致 | 上記と D3・N7 | cofiber 四角形の押し出し性も coslice で直接証明し、D3 を三角比較へ昇格 |

HA §1.1 に対応する Kerodon の章はない。原典は定義と命題の照合に用い、引用公理にはしない。

## 工程

| 工程 | ファイル | 必須の到達点 | 状態 |
| --- | --- | --- | --- |
| S1 | `Stable/Pointed.lean` | 零対象、coslice の始対象としての IsColimitCone、IsPushoutSquare、fiber/cofiber 四角形 | 完了 |
| S2 | `Stable/Definition.lean` | HA 1.1.1.9 の安定性、HA 1.1.3.4 の必要な向き | 完了 |
| S3 | `Stable/Suspension.lean` | h C の Σ・Ω 関手、選択の比較、安定な場合の自己同値 | 実装中 |
| S4 | `Stable/Pasting.lean`、`Stable/Triangulated.lean` | 四角形の貼り合わせ、cofiber 三角形、TR1〜TR4、Pretriangulated | 未着手 |
| S5 | `Stable/LongExactSequence.lean` | fiber 列に Hom を適用した長完全列 | 未着手 |
| S6 | `Stable/ExactFunctor.lean` | 完全関手、h の三角関手、完全関手間の自然変換 | 未着手 |
| S7（D7） | `Derived/Stable.lean` | D(S) の安定性と D3 による通常の導来圏の三角構造との一致 | 未着手 |

## 設計上の決定

- namespace は `SerrePositivity.InfinityCategories`。SSet の実際の頂点・辺・単体的四角形を用いる。
- 零対象は A2e の `IsInitialVertex` と `IsTerminalVertex` の両方を満たす頂点。
- 余極限錐は `sliceUnder`・`sliceUnderEquiv` による coslice の始対象で定義する。
  押し出しは A2g の双対と照合し、単に h C の押し出しへ置き換えない。
- 安定性の定義に三角圏の公理や Σ の自己同値性を入力として追加しない。
- Σ・Ω は極限・余極限の選択から h C 上に構成し、A2f・A3d で選択の比較を証明する。
- distinguished triangle は cofiber 列の像を条件にする。TR4 も独立に受入基準へ含める。
- N7f（cofiber 四角形の押し出し性）は未実施。S7 で既証明として扱わず、coslice の充填を構成する。
- D3 の同値だけで安定性を定義したり、通常の導来圏の三角構造を無条件に移したりしない。
  実際の fiber/cofiber 列との一致を証明し、D2f の CommShift と照合する。
- 公理監査は `scripts/audit_infinity_stable.lean`。許されるのは propext・Classical.choice・Quot.sound。
- 集約 `InfinityCategories/Stable.lean` を作り、共有ルートへの追記はその public import 一行だけ。
  他チャットの変更・既存の未保存差分をコミットに含めない。

## 主要宣言

| 範囲 | 宣言・正確な前提 | 状態 |
| --- | --- | --- |
| 零対象 | `IsZeroVertex z : Prop`、`ZeroVertex X`、`HasZeroVertex X : Prop`、`zeroVertexIso`（Quasicategory の下で） | 完了 |
| 余極限錐 | `JoinCocone p`、`IsColimitCone c : Prop`、`HasColimit p : Prop`、`colimitVertexIso`（Quasicategory の下で） | 完了 |
| 押し出し | `spanCoconeSquareIso`、`pushoutSpan`、`pushoutCocone`、`IsPushoutSquare F : Prop` | 完了 |
| fiber/cofiber | `ZeroTriangle X`、`IsFiberSequence`、`IsCofiberSequence`、`FiberSquare f`、`CofiberSquare f` | 完了 |
| 有限形状 | `edgeCospan`、`edgeSpan`、`coneSquare`、`coconeSquare` と境界・普遍性の保存 | 完了 |
| fiber/cofiber の存在 | `exists_fiberSquare_of_cospan_limits`、`exists_cofiberSquare_of_span_colimits`（零頂点と該当ホーンの極限／余極限のみ） | 完了 |
| 安定性 | `IsStable X : Prop`（`[Quasicategory X]`。零対象、全辺の fiber/cofiber、零角の列の同値） | 完了 |
| 有限極限による判定 | `isStable_of_finite_limits_colimits`（Quasicategory、HasZeroVertex、HasFiniteLimits、HasFiniteColimits、全四角形の引き戻し iff 押し出し） | 完了 |
| h C の零対象 | `IsInitialVertex.isInitialHo`、`IsZeroVertex.isZeroHo`、`hasZeroObject_ho`（Quasicategory と該当する頂点条件） | 完了 |
| 余極限の同型不変性 | `IsInitialVertex.of_vertexIso`、`IsColimitCone.of_vertexIso`（Quasicategory、同じ図式の coslice 内の同型） | 完了 |
| ΣΩ の四角形 | `chosenSuspensionSquare x`、`chosenLoopSquare x`（Quasicategory、IsStable）、`SuspensionSquare.toLoopSquare` と双対 | 完了（対象と四角形のみ） |
| ΣΩ の図式の族 | `suspensionDiagrams`、`loopDiagrams`（Quasicategory）、`suspensionLoopDiagramsIso`（IsStable）、評価の可換性と本質的全射性 | 完了（評価の充満忠実性は未完了） |
| 余錐の族の比較 | `coconeFamilyVertexEquiv`、`cosliceCoconeFamilyMap_app_zero`、`isQCatEquivalence_fatJoinComparison_fixedLeftDiagram`（最後のみ Quasicategory） | 完了（coslice 比較の同値性・相対充填は未完了） |
| S3〜S7 | ΣΩ の関手性・自然な選択比較・自己同値、三角構造・完全関手・D7 | 未完了 |

正確な公開型と構造体の構成子は [型一覧](archive/infinity-core-stable-log.md) に記録する。

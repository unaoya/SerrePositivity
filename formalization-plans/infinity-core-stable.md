# α-S：安定 ∞ 圏と D(S) の安定性

作成日：2026-10-18。状態：S1〜S3 完了。S4 実装中、S5〜S7 未完了。
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
suspension 図式の始点評価は、零対象へ向かう二辺の輸送と普遍余錐の相対充填により
trivial Kan fibration であることまで証明した。その逆と右上の評価から h C 上の
`suspensionFunctor` を構成し、同じ始点の族の二つの選択の自然同型も構成した。
任意の指定した `SuspensionSquare x` の右上と Σx の同型も公開する。
loop 側でも零対象から出る二辺を延長して cospan を貼り、普遍錐の相対終点境界充填を
適用した。終点評価は trivial Kan fibration であり、`loopFunctor`、族の選択の
自然同型、任意の指定した LoopSquare と Ω の対象上の比較を構成した。
二つの評価の同値の間に安定性による図式の族の同型を挟み、
`suspensionEquivalence` を構成した。順方向は `suspensionFunctor`、逆方向は
`loopFunctor` と厳密に一致し、単位・余単位を自然同型として公開する。S3 は完了。
余錐側では制限射 `coconeRestriction` の fiber `coconeFamily`、その零単体と
`JoinCocone` の同値、coslice からの比較射と零次成分の式を構成した。
左図式を固定した fat join 比較に加え、太い coslice の任意パラメーターの普遍性、
可逆円柱による固定図式上の同型判定、直接定義の coslice と太い coslice の比較同値を証明した。
この結果、`cosliceCoconeFamilyMap` 自体の同値性と、余極限性が `coconeFamily` の始対象性と
同値であることまで完成した。境界・始終対象・頂点上の fiber の反転も整備した。
`InitialBoundaryLifting` を定義し、反転した射に `CocartesianHornFibration` がある場合は
fiber の始対象から相対始点境界充填を得た。さらに最後の外側ホーンと境界の積の充填、
任意の単射に沿う骨格延長を反転により証明し、余錐の頂点で可逆な辺の cartesian 性を得た。
終点の余錐を固定した prism の輸送は cartesian な辺を与え、反転した
`coconeRestriction` 自身の `CocartesianHornFibration` を認証した。
これを使い、`IsColimitCone` と余錐制限射に対する `InitialBoundaryLifting` の同値を、
輸送の追加仮定なしに証明した。相対始対象の全部分圏への制限は正次元の全境界を
持ち上げる。普遍余錐の全部分圏 `colimitCocones` を作り、各頂点で余極限が存在する
任意の図式の族に沿う射影が trivial Kan fibration であることを証明した。
その厳密な切断による全単体に自然な余極限の選択と、二つの選択の関手同型も構成した。
suspension 側ではこれを span の族へ適用済み。二本の零終点の辺の始点評価の
trivial Kan fibration 性を証明し、span を貼って普遍余錐を充填した。
loop 側の双対的な適用も完了した。S4 に着手し、`Δ[2] × Δ[1]` の左・右・外側の
四角形、共有辺、上下の二単体との一致を構成した。さらに、右上の終端角を除いた
五頂点図式 `pastingCorner` と、その右側の三頂点部分 `pastingRightSpan` を構成した。
横座標を max(x,t) に写す固定部分つき収縮により後者の包含の right anodyne 性を
証明した。任意の right anodyne な単射による coslice の制限が trivial Kan fibration
であることと、その制限が余極限性を保ち反映することも証明し、この五頂点図式に適用した。
右側の三頂点部分は `pastingRightSpanIso` により標準 span `Λ[2,0]` と同定した。
同型を長方形へ含めると右四角形の span の包含に厳密に一致する。これを用いて、
五頂点図式の余錐の余極限性を右四角形の標準 span 上で判定する補題まで証明した。
全長方形の join 表示 `pastingCornerJoinIso` を構成した。二座標の最後の頂点への
評価で余錐を作り、終端角になる最初の頂点から切断を復元して各次数の全単射性を証明した。
この同型には値域や安定性の仮定はない。押し出し側の貼り合わせの普遍性まで完了した。
右 span への制限は右四角形の余錐と厳密に一致することまで証明した。
`pastingCocone_isColimitCone_iff_right` により、値域の quasicategory 性のみの下で、
五頂点図式上の余極限性と右四角形の押し出し性が同値である。
下側三角形と左辺からなる四頂点図式 `pastingOuterBase` を構成し、外側 span を
固定する収縮により、その包含の right anodyne 性を証明した。外側 span は
`pastingOuterSpanIso` で標準ホーンと同定し、その包含は外側四角形の span に一致する。
`pastingOuterCocone_isColimitCone_iff_outer` により、四頂点図式へ制限した余錐の
余極限性は外側四角形の押し出し性と同値である（値域 Quasicategory）。
左四角形が押し出しなら
`IsColimitCone (pastingCocone F) ↔ IsColimitCone (pastingOuterCocone F)`
となる五頂点／四頂点の比較を `pastingCocone_isColimitCone_iff_outerCocone` として証明した。
標準 span の形状の不一致も解消済み。
この比較に必要な二重 coslice の計算のため、空次数を含む join の統一した
切断表示 `stableAugJoinEquiv` とその自然性を証明した。三因子の頂点数ごとの
同値 `stableAugJoinAssociatorEquiv` は、二つの切断の再添字付けと直和・直積の
同値で構成した。`stablePullCut_leftMap`・`stablePullCut_rightMap`・
`stablePullCut_middle` により三因子の切断位置の引き戻しを計算できる。
三因子の組み替えは空次数を含む全ての順序写像に関して自然であることを証明し、
単体集合の結合同型 `stableJoinAssociator K L M : (K⋆L)⋆M ≅ K⋆(L⋆M)` を構成した。
三因子それぞれの射に関する自然性と、左の二因子・右端の因子の包含との厳密な
可換性も証明した。さらに中間因子の空区間に関する包含の式も証明し、
`nestedCosliceIso c` により `sliceUnder c.val` と `sliceUnder (yonedaEquiv.symm c)`
（後者は `sliceUnder p` 内での coslice）を単体集合として同定した。
`colimitCosliceRestriction c : sliceUnder c.val → sliceUnder p` は、uncurry すると
基底の包含 `K → K⋆Δ[0]` に沿う制限となり、X への頂点射影と厳密に可換である。
`IsColimitCone c ↔ TrivialKanFibration (colimitCosliceRestriction c)` を
値域の quasicategory 性を仮定せず証明した。さらに、余極限余錐を任意の図式の
pushout で付け加えた場合、残りの図式への coslice 制限が trivial Kan fibration
であることを全ての単射の持ち上げにより直接証明した。形状の射の単射性も不要。
左四角形と四頂点図式の和が五頂点図式であることを部分複体の格子から証明し、
左四角形・共通 span の標準形との包含の一致を通じてこの一般補題を適用した。
`isPushoutSquare_pasting_iff F hleft` により、任意の quasicategory に値を持つ
長方形について、左四角形が押し出しなら右が押し出し iff 外側が押し出しとなる。
二つの押し出しの合成と、左・外側から右を判定する系も公開した。
HTT Lemma 4.4.2.1 の押し出し側は完了。A6 を待つ箇所は生じていない。
引き戻しへの双対化と三角構造も未完了。Mathlib の三角構造の構成には h C の
前加法構造・整数シフトとその加法性も証明する必要があり、S4 の義務として保持する。
安定性から全有限極限・余極限を導く逆向き、S4〜S7 の三角構造・長完全列・完全関手・D7 は未完了。
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
| 四角形の貼り合わせ | HTT Lemma 4.4.2.1 | A2 の join・slice による証明。A6 待ちの箇所が生じれば正確に特定 |
| D(S) の安定性と三角構造の一致 | 上記と D3・N7 | cofiber 四角形の押し出し性も coslice で直接証明し、D3 を三角比較へ昇格 |

HA §1.1 に対応する Kerodon の章はない。原典は定義と命題の照合に用い、引用公理にはしない。

## 工程

| 工程 | ファイル | 必須の到達点 | 状態 |
| --- | --- | --- | --- |
| S1 | `Stable/Pointed.lean` | 零対象、coslice の始対象としての IsColimitCone、IsPushoutSquare、fiber/cofiber 四角形 | 完了 |
| S2 | `Stable/Definition.lean` | HA 1.1.1.9 の安定性、HA 1.1.3.4 の必要な向き | 完了 |
| S3 | `Stable/Suspension.lean` | h C の Σ・Ω 関手、選択の比較、安定な場合の自己同値 | 完了 |
| S4 | `Stable/Pasting.lean`、`Stable/Triangulated.lean` | 四角形の貼り合わせ、cofiber 三角形、TR1〜TR4、Pretriangulated | 実装中（形状のみ完了） |
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
| ΣΩ の図式の族 | `suspensionDiagrams`、`loopDiagrams`（Quasicategory）、`suspensionLoopDiagramsIso`（IsStable）、評価の可換性と本質的全射性 | 両評価の同値まで完了 |
| 太い coslice | `laxCosliceHomEquiv`（任意の形状・値域・パラメーター）、`isQCatEquivalence_cosliceLaxMap`（値域 Quasicategory） | 完了 |
| 余錐の族の比較 | `isQCatEquivalence_cosliceCoconeFamilyMap`（値域 Quasicategory、任意図式） | 完了 |
| 余極限性の判定 | `isColimitCone_iff_isInitialVertex_coconeFamily`（値域 Quasicategory、任意図式の JoinCocone） | 完了（相対境界充填との同値も証明済み） |
| 相対始対象 | `InitialBoundaryLifting`、`initialBoundaryLifting_of_isInitialVertex_fiber_op`（元・標的 Quasicategory、反転した射の CocartesianHornFibration、fiber の始対象） | 完了。余錐制限射にも適用済み |
| 余錐の辺の輸送 | `exists_cocone_fixedVertex_prism`、`coconeRestriction_hasLiftingProperty_finalVertex`（値域 Quasicategory、任意の形状） | 完了。`exists_cartesian_cocone_lift` により cartesian 性も認証済み |
| 余錐制限の輸送 | `isCartesianEdge_coconeRestriction_of_apex`、`cocartesianHornFibration_coconeRestriction_op`（値域 Quasicategory、形状は任意） | 完了 |
| 相対余極限性 | `IsColimitCone.initialBoundaryLifting`、`isColimitCone_iff_initialBoundaryLifting`（値域 Quasicategory、任意図式の JoinCocone） | 完了 |
| 相対始対象の族 | `relativeInitialVertices`、`relativeInitialProjection_hasLiftingProperty_boundary`（任意の射、正次元境界）、`relativeInitialProjection_trivialKanFibration`（頂点全射を仮定） | 完了 |
| 普遍余錐の族の選択 | `colimitCocones`、`colimitCoconeProjection_pullback_trivialKanFibration`、`exists_colimitCoconeFamily`、`colimitCoconeFamilyIso`（値域 Quasicategory、族の各頂点で HasColimit、基底は任意） | 一般の族、suspension と loop の両側への適用は完了 |
| suspension の始点評価 | `suspensionDiagramEvaluation_source_trivialKanFibration`、`suspensionDiagramSourceEquivalence`（Quasicategory、IsStable） | 完了 |
| h C の Σ と選択の比較 | `suspensionFunctor`、`suspensionDiagramFamilyIso`、`suspensionFunctorChoiceIso`、`SuspensionSquare.suspensionFunctorObjIso`（Quasicategory、IsStable。族の比較は同じ始点の族） | 完了 |
| loop の終点評価 | `loopDiagramEvaluation_target_trivialKanFibration`、`loopDiagramTargetEquivalence`（Quasicategory、IsStable） | 完了 |
| h C の Ω と選択の比較 | `loopFunctor`、`loopDiagramFamilyIso`、`loopFunctorChoiceIso`、`LoopSquare.loopFunctorObjIso`（Quasicategory、IsStable） | 完了 |
| ΣΩ の逆性 | `suspensionEquivalence`、`suspensionEquivalence_functor`、`suspensionEquivalence_inverse`、`suspensionLoopUnitIso`、`loopSuspensionCounitIso`（Quasicategory、IsStable） | 完了 |
| 貼り合わせの形状 | `pastingSquare`、`pastingBottomTriangle`、`pastingTopTriangle`、`pastingSquare_sharedEdge`、外側二辺・上下辺の一致（任意の `Δ[2] × Δ[1] → X`、X に追加の仮定なし） | 完了（押し出し側の普遍性も完了） |
| right anodyne な制限 | `sliceUnderRestrict_trivialKanFibration`、`isColimitCone_iff_restrict_of_rightAnodyne`（値域 Quasicategory、right anodyne な単射） | 完了 |
| 部分長方形の右への制限 | `pastingRightSpan_rightAnodyne`、`pastingCornerRestrict_trivialKanFibration`、`pastingCorner_isColimitCone_iff_rightSpan`（後二者は値域 Quasicategory） | 完了（引き戻し側は未完了） |
| 右 span の標準形 | `pastingRightSpanIso : (horn 2 0 : SSet) ≅ pastingRightSpan`、`pastingRightSpanIso_hom_ι`（値域の図式を選ぶ前の単体集合の同型と辺の一致） | 完了 |
| 標準 span 上の余極限判定 | `pastingCornerRestrict_standardSpan_trivialKanFibration`、`pastingCorner_isColimitCone_iff_standardSpan`（値域 Quasicategory、五頂点図式の任意の余錐） | 完了 |
| 全長方形の join 表示 | `pastingCornerCocone`、`pastingCornerCocone_inl`、`pastingCornerCocone_app_injective`、`pastingCornerCocone_app_surjective`、`pastingCornerJoinIso`（任意の宇宙、追加仮定なし） | 完了 |
| 右四角形の余錐の比較 | `pastingCornerCocone_rightSpan`、`pastingCocone`、`pastingCocone_isColimitCone_iff_right`（後者は値域 Quasicategory、左四角形への仮定なし） | 完了 |
| 四頂点図式から外側 span | `pastingOuterSpan_rightAnodyne`、`pastingOuterBaseRestrict_standardSpan_trivialKanFibration`、`pastingOuterBase_isColimitCone_iff_standardSpan`（後二者は値域 Quasicategory） | 完了 |
| 外側四角形の余錐の比較 | `pastingOuterSpanIso`、`pastingOuterSpanIso_hom_ι`、`pastingCornerCocone_outerSpan`、`pastingOuterCocone_isColimitCone_iff_outer`（後者は値域 Quasicategory、左四角形への仮定なし） | 完了 |
| 空次数を含む join | `StableAugJoin`、`stableAugJoinEquiv`、`stableAugJoinEquiv_naturality`（任意の二因子、有限順序写像） | 完了 |
| join の結合の各次数の同値 | `stableJoinCutEquiv`、`stableAugReassociationEquiv`、`stableAugJoinAssociatorEquiv`（任意の三因子、頂点数 r） | 各次数と組み替えの自然性まで完了 |
| 二段の切断の引き戻し | `stablePullCut_leftMap`（a≤b）、`stablePullCut_rightMap`、`stablePullCut_middle`（a≤b） | 完了 |
| join の結合同型 | `stableJoinAssociator`、`stableJoinAssociator_naturality`、`stableJoinAssociator_inl`、`stableJoinAssociator_inr`（任意の三因子とその射、追加の仮定なし） | 完了。二重 coslice への適用も完了 |
| 二重 coslice | `nestedCosliceDiagramEquiv`、`nestedCosliceHomEquiv`、`nestedCosliceIso`（任意の余錐 c、値域の追加仮定なし） | 完了 |
| 余極限余錐の coslice 制限 | `colimitCosliceRestriction`、`colimitCosliceRestriction_uncurry`、`colimitCosliceRestriction_projection`、`isColimitCone_iff_colimitCosliceRestriction`（任意の余錐、値域の追加仮定なし） | 完了。pushout に沿う適用と押し出し貼り合わせも完了 |
| 余極限頂点の pushout での付加 | `cosliceRestriction_lift_of_colimit_attachment`、`cosliceRestriction_trivialKanFibration_of_colimit_attachment`、`isColimitCone_iff_restrict_of_colimit_attachment`（前二者は任意の値域、最後は Quasicategory） | 完了 |
| 左四角形の余極限頂点の付加 | `pastingLeftAttachment_isPushout`、`pastingCornerRestrict_outerBase_trivialKanFibration`、`pastingCocone_isColimitCone_iff_outerCocone`（最後は値域 Quasicategory、後二者は左が押し出し） | 完了 |
| 押し出しの貼り合わせ | `isPushoutSquare_pasting_iff`、`isPushoutSquare_pasting`、`isPushoutSquare_pasting_cancel_left`（値域 Quasicategory、左が押し出し） | 完了（引き戻しへの双対化は未完了） |
| S4〜S7 | 引き戻しの貼り合わせ・三角構造・長完全列・完全関手・D7 | 未完了 |

正確な公開型と構造体の構成子は [型一覧](archive/infinity-core-stable-log.md) に記録する。

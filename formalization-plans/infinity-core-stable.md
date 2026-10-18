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
引き戻しへの双対化の準備として、`stableJoinReverseIso K L : (K⋆L).op ≅ L.op⋆K.op`
を構成した。空次数を含む自然性、二つの因子の射との両立、左右包含の交換も証明済み。
錐の図式の反転を固定条件へ制限し、`sliceOverOpIso p : (sliceOver p).op ≅
sliceUnder (opFunctor.map p)` を構成した。標準単体のパラメーターの反転との
両立と、値域への頂点射影の可換性も厳密に証明した。
`JoinCone.reverseCocone c` は反転した図式への余錐で、
`isLimitCone_iff_reverseCocone` により `IsLimitCone c ↔ IsColimitCone c.reverseCocone`。
これらは値域の quasicategory 性を仮定しない。反転した余錐の頂点も opObjEquiv による
元の頂点の反転に一致する。
長方形の面の反転は `reverseGrid_pastingSquare` で証明した。
`reverseGrid` は任意の標準格子の両座標を反転し、後合成との両立と二重反転の恒等式も満たす。
余面 i は i.rev に移るため左・右を交換し、外側を保つ。値域に追加の仮定は不要。
標準 span／cospan の二辺を反転で交換し、点と辺の標準 join の反転を計算して、
`squareConeReverseShape_square` により錐の反転と格子反転を厳密に照合した。
基底の同型による余極限性の保存・反映 `isColimitCone_iff_restrict_of_isIso` は
値域への追加仮定なしに成り立つ。これと極限錐の反転を合成して
`isPullbackSquare_iff_reverseGrid`（引き戻し iff 反転した四角形が押し出し）を証明した。
`isPullbackSquare_pasting_iff F hright` により、任意の quasicategory に値を持つ
長方形で、右が引き戻しなら左が引き戻し iff 外側が引き戻しとなる。
二つの引き戻しの合成と、右・外側から左を判定する系も公開した。
HTT Lemma 4.4.2.1 の両側は完了し、A6 を待つ箇所はない。
S4 の三角構造へ向け、四辺を端点つきの辺と h C の射として取り出し、二つの合成
三角形による `square_homMk_comm` を証明した（値域の quasicategory 性も不要）。
零頂点があると h C の零射を零対象から構成でき、零角の四角形では下辺と右辺の合成が
零になる。`ZeroTriangle.hoShortComplex` はこの二射を Mathlib の短複体にまとめる。
一般の零角の四角形のこの構成には Quasicategory と任意の HasZeroMorphisms を仮定する。
指定した cofiber/fiber 四角形について、短複体の第一／第二射の Arrow 表示が元の射の類と
一致することも証明済み。四角形の h 上の図式間の自然変換から短複体の射
`ZeroTriangle.hoShortComplexMap` を作り、恒等・合成との両立を証明した。
実際の単体的ホモトピーからの構成も `hoShortComplexMapOfHomotopy` に公開する。
`exists_cofiber_hoShortComplex` と `exists_fiber_hoShortComplex` により、安定な X の
h C の全ての射が、cofiber 短複体の第一射／fiber 短複体の第二射として現れる。
この存在定理自体は短複体まで。接続射、整数シフト、通常の Triangle、distinguished 集合の定義、
TR1 の存在部分と TR3 は下記のとおり追加した。恒等射の三角形・回転・八面体は未証明。
接続射と cofiber 列の射に向け、`exists_colimitCoconeFamily_extension` により
各頂点で余極限が存在する族の任意の単射部分族上で、指定した普遍余錐の族を
厳密に保持して延長できることを証明した。`colimitCoconeVertex` とその射影の等式により
与えた余極限余錐を普遍余錐全体の頂点として扱える。
`exists_colimitCocone_edge` は任意の図式間の実際の辺を、両端を指定した普遍余錐間の
辺へ持ち上げる。`exists_colimitCoconeHomotopy` はその辺を余錐の間の単体的ホモトピーに
直し、元の図式への制限が元の辺の uncurry と厳密に一致することも保証する。
この二つの持ち上げには値域 Quasicategory と両端の IsColimitCone のみを仮定し、
中間図式の余極限の存在は追加仮定しない。
`exists_terminalArrowComparison` は共通の始点の辺から終対象へ向かう辺への、始点を
厳密に固定したホモトピーを与える。合成三角形を左辺を潰した正方形で引き戻して構成した。
二辺をホーンの pushout で貼り合わせた `exists_terminalSpanComparison` も始点を固定する。
四角形の二辺からの span の表示を通じ、`exists_suspensionSpanComparison` により任意の
四角形の span から同じ始点の指定 suspension 四角形の span へ比較できる。
`exists_cofiberSuspensionComparison` は、この span の比較を両端の普遍余錐へ持ち上げ、
始点を全パラメーターで厳密に固定した四角形間のホモトピーを与える。
`chosenCofiberSuspensionComparison` はその比較を選び、始点固定の式も公開する。
`cofiberSuspensionShortComplexMap` の第三成分が指定 suspension の頂点への接続射で、
`cofiberConnecting` は S3 の対象比較同型を用いて実際の suspensionFunctor の値 ΣX に送る。
`cofiberConnecting_comp_eq_zero` により、cofiber 列の第二射の後に接続射を合成すると零。
固定した頂点でのホモトピーは h の自然変換で恒等成分を与えることを
`homotopyNatTrans_fixedVertex_arrow` と両端を指定した版で証明した（quasicategory 仮定なし）。
比較ホモトピーの始点固定条件への適用により、`cofiberSuspensionShortComplexMap` の
第一成分は元の始点の恒等射と Arrow として一致する。さらに
`cofiberSuspensionShortComplexMap_τ₁_eqToHom` はその第一成分を
suspension の source_eq の逆向きによる eqToHom として厳密に記述する。
第一成分の同型性と第二成分の零射性も公開した。
`pinchedHomMap_boundary_of_boundary_succ` は元の射の n+1 次元境界の持ち上げから
右写像空間の n 次元境界の持ち上げを導く。境界と点の join の標準同型を使うため、
頂点上の全射性は不要。正次元の全境界を持ち上げる射は写像空間で充満忠実となる。
`relativeInitialProjection_isFullyFaithful` と `colimitCoconeProjection_isFullyFaithful` により、
普遍余錐の図式への射影も充満忠実。全図式の余極限の存在は要求しない。
`colimitCoconeProjectionHoFullyFaithful` は h 上の充満忠実関手を構成し、
`colimitCoconeProjection_ho_map_injective` は射影した射の等号を反映する。
`colimitCoconeLiftHom` は指定された二つの普遍余錐間に図式側の h の射を一意に
持ち上げる。射影との逆関係、一意性、恒等射・合成との両立も公開済み。
これは基底の h の射を固定した持ち上げの選択独立性である。
span 比較側の一意性のため、`stable_prism_extend_terminal_last` により境界の最後の
終点だけが終対象であれば始点側を指定した prism を延長できることを証明した。
`terminalBoundaryLifting_arrowSource_of_terminalTarget` と
`terminalBoundaryLifting_spanSource_of_terminalTargets` は、辺の終点／span の両端が
終対象であれば始点評価に関して相対終点境界を充填することを保証する。
これらの充填自体には値域の quasicategory 性は不要。
相対終点境界充填から、その頂点への写像空間上の trivial Kan fibration を構成した。
`homotopyCategoryMap_bijective_of_terminalBoundaryLifting` は、元・値域が quasicategory
のとき、その頂点への h の Hom が基底の Hom と全単射で対応することを証明する。
`spanSourceEvaluation_homMap_bijective` により終対象を両端とする span への h の射は
共通始点の成分だけで決まる。suspension の span への適用も `suspensionSpan_hom_ext` に公開。
`homotopyEvaluation_arrow` はホモトピーの関手辺を評価した類と自然変換の頂点成分を照合し、
固定頂点での類の一致を `homotopyEvaluation_eq_of_fixedVertex` に導いた。
`suspensionSpanHomotopy_homMk_eq` は始点を厳密に固定した二つの suspension span への
比較ホモトピーが h で同じ射を与えることを保証する。
`exists_fullSubcomplexEdgeLift` により、両端が全部分単体集合に属する任意の辺を持ち上げた。
`colimitCoconeHomotopy_homMk_eq` は普遍余錐間の実際のホモトピーについて、図式へ制限した
h の類の一致から元の h の類の一致を導く。`stableHomotopyPrecomp` と関手辺の前合成の
一致を用い、span の比較の一意性を四角形の比較へ移した。
`cofiberSuspensionComparison_homMk_eq` は、押し出し四角形から指定した同じ始点の suspension
四角形への、始点固定の二つの比較ホモトピーが h で同じ射を与えることを証明する。
`homotopyEvaluationOfEndpoints_arrow` で最後の頂点の成分に移し、
`cofiberComparison_τ₃_eq_of_source_fixed` と `cofiberComparison_τ₃_eq_connectingToSuspension` により、
指定 suspension を固定したときの接続射が比較ホモトピーの選択によらないことまで証明した。
`colimitCocone_hom_ext` は任意の h の射に余錐の射影の忠実性を適用できる。
`pushoutSquare_hom_ext` は両端が押し出しなら span への制限の一致から四角形間の射の一致を導き、
`cofiberSuspensionComparison_hom_ext` は指定 suspension への射が始点成分だけで決まることを示す。
これらは厳密に始点固定なホモトピーに限定しないので、h での比較の合成にも適用できる。
`cofiberSuspensionComparisonHom` の始点成分は source_eq の逆の eqToHom、終点成分は
`cofiberConnectingToSuspension`。中間の suspension を経由した比較の合成が直接の比較と一致する。
`SuspensionSquare.diagramComparisonIso` と `comparisonIso` は同じ指定始点の suspension の
四角形／終点の標準比較同型で、恒等・三つの選択の間の合成則も証明した。これらは
X の Quasicategory 性のみを要求し、X 全体の安定性や特定の零頂点の選択は不要。
`cofiberConnectingToSuspension_comparisonIso` は接続射がこの比較同型で互いに移ることを保証する。
`cofiberConnecting_eq_via_suspensionComparison` により、任意の suspension から標準比較で
選択済みの suspension に移し、その S3 の対象比較同型で Σ へ送ると `cofiberConnecting` を得る。
`cofiberSuspensionComparisonHom_naturality` と `cofiberConnectingToSuspension_naturality` は、
元の二つの押し出し四角形間の h の射と suspension 四角形間の h の射が、始点で
source_eq の輸送を介して可換であれば、標準比較／接続射が可換となることを示す。
二つの始点は異なってよい。ここでは suspension 間の射と始点での可換式を入力する。
これらの追加条件を除き Σ に移した自然性は下記で証明した。
`sourceDiagramObjIso` は S3 と同じ fiber 内の比較を suspension 図式間の同型として取り出す。
始点では恒等射となり、終点で評価すると既存の `suspensionFunctorObjIso` に厳密に一致する。
`comparisonIso_eq_suspensionFunctorObjIso` により、標準比較同型は S3 の二つの対象比較同型の
逆・順方向の合成に等しい。`cofiberConnectingToSuspension_comp_objIso_inv` は、任意の指定
suspension の頂点を S3 の同型で Σ に送ると `cofiberConnecting` に一致することを保証する。
始点評価の圏同値で任意の始点の射を持ち上げる `liftSourceHom` とその始点の式、
対象比較同型の順・逆方向の自然性も証明した。
`cofiberConnecting_naturality` は、二つの cofiber 四角形間の任意の h の射 a について
「最後の成分 ≫ δ = δ ≫ Σ(始点の成分)」を証明する。追加の suspension 間の射や
始点での可換式は不要。`cofiberConnecting_naturality_of_homotopy` は実際の四角形間の
ホモトピーが与える短複体の比較の τ₁・τ₃ を用いて同じ可換式を述べる。
この自然性の定理自体は図式の比較を入力する。任意の h の可換正方形からの延長は下記で追加した。
`cofiberConnecting` の前提は Quasicategory と IsStable のみで、列は零角の四角形と
IsCofiberSequence の証明で与える。S3 の対象比較との整合と図式の比較に対する自然性は完成。
`homotopyEvaluation_arrow_of_vertexPath` はホモトピーを頂点上の指定した道で評価した類を計算する。
`SquareHorizontalHomotopies` の最大値・最小値による変形は、四角形を右の列へ動かし、
左の列から四角形へ戻す。前者の始点成分は下辺、後者は恒等射である。
`exists_squareRightToSuspensionLeft` は右の列から同じ始点の suspension の左の列への
始点固定の比較を構成し、横に一定な四角形へ引き戻しても始点成分は恒等射である。
この三つを h で合成した `exists_squareToSuspension_zero_target` は、任意の四角形 F から
右下の頂点の suspension へ、始点成分が下辺、最後の成分が零射となる比較を与える。
元の四角形の押し出し性は不要で、Quasicategory と任意の HasZeroMorphisms のみを要求する。
この比較を suspension への射の始点成分による一意性で標準比較の合成と同定し、
S3 の対象比較の自然性で Σ に移した。
`cofiberConnecting_comp_suspension_map_eq_zero` により δ ≫ Σf = 0 が成り立つ
（Quasicategory、IsStable、IsCofiberSequence）。f ≫ g = 0、g ≫ δ = 0 と合わせ、
cofiber 列の三つの隣接零合成は完成。回転・八面体を含む三角圏の公理は未完了。
`stableEquivalenceHasShift` は任意の圏の自己同値から整合的な整数シフトを構成する。
skeleton 上の mapSkeleton は充満忠実かつ対象全単射なので厳密な自己同型となり、その
Aut(Cat) の整数冪の等号から ShiftMkCore を作る。HasShift.induced により元の圏へ戻す。
skeleton は内部の補助構成だけに用い、h C の対象・射は変更しない。
`hasShift_ho` により h C は HasShift ℤ を持つ。`shiftOneSuspensionIso` と
`shiftNegOneLoopIso` は +1 と −1 のシフトを既存の Σ・Ω と自然同型で比較する。
単位・加法・結合の整合条件を含む整数シフトは完成。前加法構造とシフトの加法性は未完了。
`cofiberTriangle` は cofiber 列を Mathlib の通常の Triangle にまとめ、三つの隣接零合成も満たす。
`cofiberTriangleMapOfHomotopy` は実際の四角形間のホモトピーを三角形の射に移す。
`cofiberDistinguishedTriangles` はこれらの三角形の同型による閉包で、同型不変性も証明済み。
`exists_cofiberDistinguishedTriangle` は任意の射 f : a ⟶ b について、a・b・f を厳密に指定した
Triangle.mk f g h がこの集合に属することを証明する（TR1 の存在部分）。
これは単なる Arrow 表示での存在には留めていない。恒等射の三角形の所属は未証明。
S4 の三角構造は未完了。前加法構造・シフトの加法性、恒等射の三角形の判定、
回転・八面体および Pretriangulated instance は残る S4 の義務として保持する。TR3 は下記で完成。
`exists_stableSquare_of_homMk_comm` は、h で可換な四つの指定辺を二つの合成三角形の
貼り合わせで実際の正方形にする。`exists_arrowHomotopy_of_homMk_comm` は二つの縦の辺を
厳密な端点の道として持つホモトピーに直す。
`exists_edge_lift_of_terminalBoundaryLifting` と `exists_terminalArrowHomotopy_of_sourcePath` は、
零頂点へ向かう枝の比較を同じ始点の道に沿って構成する。二本の枝を span に貼り、
`exists_pushoutSquareHomotopy_lift_span` で普遍余錐へ延長する。
`exists_cofiberSquareHomotopy_of_comm` により、cofiber 列の最初の二成分の任意の h の
可換正方形は、入力の道を厳密に保持した cofiber 四角形間のホモトピーへ延長できる。
この図式の延長は X の Quasicategory 性と両端の IsCofiberSequence のみを要求し、IsStable は不要。
`exists_cofiberTriangleMorphism_of_comm` はその二成分を厳密に保持した通常の三角形の射を作る。
`exists_cofiberDistinguishedTriangleMorphism` は同型による輸送で distinguished 集合全体に拡張する。
`complete_cofiberDistinguishedTriangle_morphism` は第三成分と残る二つの可換式を返す。
これら三角形上の定理には Quasicategory と IsStable を仮定する。定義済みの集合に対する TR3 は完成。
前加法構造・シフトの加法性、恒等射の三角形、回転、八面体、Pretriangulated instance、
恒等射の三角形に向けた準備として、一点の恒等余錐の余極限性
`cosliceIdentityCone_isColimit` と、定値写像で表した版
`isColimitCone_of_point_constant` を証明した。さらに区間の終点を重複する退化二単体の
余錐 `edgeTerminalCocone` を構成し、`edgeTerminalCocone_isColimit` を証明した。
これらの余極限性には値域の Quasicategory のみを仮定する。
恒等射の cofiber を零対象で実現する退化四角形の押し出し性への適用は未完了。
安定性から全有限極限・余極限を導く逆向き、S5〜S7 の長完全列・完全関手・D7 は未完了。
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
| S4 | `Stable/Pasting.lean`、`Stable/Triangulated.lean` | 四角形の貼り合わせ、cofiber 三角形、TR1〜TR4、Pretriangulated | 実装中（押し出し・引き戻しの貼り合わせは完了、三角構造は未完了） |
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
| 部分長方形の右への制限 | `pastingRightSpan_rightAnodyne`、`pastingCornerRestrict_trivialKanFibration`、`pastingCorner_isColimitCone_iff_rightSpan`（後二者は値域 Quasicategory） | 完了（引き戻しの貼り合わせへの双対化も完了） |
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
| 押し出しの貼り合わせ | `isPushoutSquare_pasting_iff`、`isPushoutSquare_pasting`、`isPushoutSquare_pasting_cancel_left`（値域 Quasicategory、左が押し出し） | 完了（引き戻しへの双対化も完了） |
| join の反転 | `stableJoinReverseIso`、`stableJoinReverse_naturality`、`stableJoinReverse_inl`、`stableJoinReverse_inr`（任意の二因子とその射） | 完了 |
| slice の反転 | `coneDiagramReverseEquiv`、`sliceOverOpIso`、`sliceOverOpIso_projection`（任意の図式、追加仮定なし） | 完了 |
| 極限錐の反転 | `JoinCone.reverseCocone`、`isLimitCone_iff_reverseCocone`、`JoinCone.reverseCocone_vertex`（任意の錐、追加仮定なし） | 完了。標準四角形の照合と引き戻し貼り合わせも完了 |
| 格子の反転 | `reverseGrid`、`reverseGrid_postcomp`、`reverseGrid_double`、`reverseGrid_pastingSquare`（任意の単体集合、追加の仮定なし） | 完了。普遍四角形との比較も完了 |
| 基底の同型と余極限 | `isColimitCone_iff_restrict_of_isIso`、`isLimitCone_iff_reverseCocone_restrict`（基底の射は同型、値域への追加仮定なし） | 完了 |
| 標準四角形の双対性 | `squareConeReverseShape_square`、`JoinCone.reverseCocone_val`、`isPullbackSquare_iff_reverseGrid`（値域への追加仮定なし） | 完了 |
| 引き戻しの貼り合わせ | `isPullbackSquare_pasting_iff`、`isPullbackSquare_pasting`、`isPullbackSquare_pasting_cancel_right`（値域 Quasicategory、右が引き戻し） | 完了 |
| h C の零射と短複体 | `hasZeroMorphisms_ho`（Quasicategory、HasZeroVertex）、`square_homMk_comm`（任意の X）、`ZeroTriangle.homMk_comp_eq_zero`、`ZeroTriangle.hoShortComplex`（Quasicategory、任意の HasZeroMorphisms） | 完了 |
| 零角の短複体の射 | `ZeroTriangle.hoShortComplexMap`、恒等・合成則、`hoShortComplexMapOfHomotopy`（Quasicategory、任意の HasZeroMorphisms） | 短複体の射として完了。実際のホモトピーからの比較の接続射との可換性は下記で完成 |
| 任意の h C の射を含む列 | `exists_cofiber_hoShortComplex`、`exists_fiber_hoShortComplex`（Quasicategory、IsStable） | 短複体・通常の三角形と接続射の構成は完了。TR1 の存在部分も下記で完成、恒等射の三角形の判定は未完了 |
| 部分族を保持した普遍余錐の延長 | `exists_colimitCoconeFamily_extension`（値域 Quasicategory、部分族の射は単射、全頂点の余極限の存在） | 完了 |
| 普遍余錐間の辺 | `colimitCoconeVertex`、`colimitCoconeVertex_projection`、`exists_colimitCocone_edge`、`exists_colimitCoconeHomotopy`（値域 Quasicategory、両端が余極限） | 完了。接続射の構成に適用済み |
| 始点固定の suspension との比較 | `exists_terminalArrowComparison`、`exists_terminalSpanComparison`、`exists_suspensionSpanComparison`（Quasicategory、指定終点が終対象）、`exists_cofiberSuspensionComparison`（さらに元の四角形は押し出し） | 完了 |
| cofiber 列の接続射 | `cofiberConnectingToSuspension`（Quasicategory、HasZeroMorphisms、指定 suspension）、`cofiberConnecting`、`cofiberConnecting_comp_eq_zero`（Quasicategory、IsStable、IsCofiberSequence） | 構成・第二射の後の零合成・指定 suspension を固定した比較の選択独立性まで完了。標準比較同型による suspension の変更も下記で完成。S3 の対象比較同型との一致と図式の比較に対する自然性も下記で完成。三角構造は未完了 |
| suspension 比較の最初の二成分 | `homotopyNatTrans_fixedVertex_arrow`（追加仮定なし）、`cofiberSuspensionShortComplexMap_τ₁_arrow`、`cofiberSuspensionShortComplexMap_τ₁_eqToHom`、`cofiberSuspensionShortComplexMap_τ₁_isIso`、`cofiberSuspensionShortComplexMap_τ₂_eq_zero`（Quasicategory、HasZeroMorphisms、cofiber 列と指定 suspension） | 完了。指定 suspension を固定した選択独立性も下記で完成。標準比較同型による変更は下記で完成。S3 の対象比較同型との一致と図式の比較に対する自然性も下記で完成 |
| 正次元境界による充満忠実性 | `pinchedHomMap_boundary_of_boundary_succ`、`pinchedHomMap_trivialKanFibration_of_boundary_succ`（元・値域の仮定なし）、`isFullyFaithful_of_boundary_succ`（元・値域 Quasicategory） | 完了 |
| 普遍余錐の射影と射の一意な持ち上げ | `relativeInitialProjection_isFullyFaithful`（元・基底 Quasicategory）、`colimitCoconeProjection_isFullyFaithful`、`colimitCoconeProjectionHoFullyFaithful`、`colimitCoconeLiftHom` と射影・一意性・恒等・合成則（X が Quasicategory） | 基底の h の射を固定した一意性まで完了。span 比較側の一意性と、指定 suspension への接続射への照合も下記で完成 |
| 終対象への辺・span の相対境界充填 | `stable_prism_extend_terminal_last`、`terminalBoundaryLifting_arrowSource_of_terminalTarget`、`terminalBoundaryLifting_spanSource_of_terminalTargets`（指定終点の終対象性、Quasicategory は不要） | 完了 |
| 相対終点と写像空間 | `TerminalBoundaryLifting.exists_joinBoundary_lift`、`pinchedHomMap_trivialKanFibration_of_terminalBoundaryLifting`（追加仮定なし）、`homotopyCategoryMap_bijective_of_terminalBoundaryLifting`（元・値域 Quasicategory） | 完了 |
| 始点固定の span 比較の一意性 | `spanSourceEvaluation_homMap_bijective`、`suspensionSpan_hom_ext`、`suspensionSpanHomotopy_homMk_eq`（X が Quasicategory、指定 suspension への始点固定の比較） | 完了。指定 suspension への接続射への照合も下記で完成 |
| 普遍余錐の実際のホモトピーの一意性 | `exists_fullSubcomplexEdgeLift`（追加仮定なし）、`colimitCoconeHomotopy_homMk_eq`（X が Quasicategory、両端が余極限、図式への制限の h の類が一致） | 完了 |
| 指定 suspension への比較と接続射の選択独立性 | `stableHomotopyPrecomp` と関手辺・h の類との整合（追加仮定なし）、`cofiberSuspensionComparison_homMk_eq`（X が Quasicategory、元が押し出し、両比較は始点固定）、`cofiberComparison_τ₃_eq_of_source_fixed` と `cofiberComparison_τ₃_eq_connectingToSuspension`（さらに HasZeroMorphisms、cofiber 列） | 指定 suspension を固定した場合は完了。標準比較同型による変更は下記で完成。S3 の対象比較同型との一致と図式の比較に対する自然性も下記で完成 |
| 任意の h の比較の判定 | `colimitCocone_hom_ext`（両端が余極限）、`pushoutSquare_hom_ext`（両端が押し出し）、`cofiberSuspensionComparison_hom_ext`（元は押し出し、先は指定 suspension）；いずれも X が Quasicategory | 完了。始点固定なホモトピーに限らない |
| suspension の標準比較と接続射の整合 | `cofiberSuspensionComparisonHom_comp`、`SuspensionSquare.diagramComparisonIso`・`comparisonIso` と恒等・合成則（X が Quasicategory）、`cofiberConnectingToSuspension_comparisonIso`（さらに HasZeroMorphisms、cofiber 列）、`cofiberConnecting_eq_via_suspensionComparison`（Quasicategory、IsStable） | 標準比較同型による整合は完了。S3 の既存対象比較同型二つの合成との一致も下記で完成 |
| 図式の比較に対する接続射の可換性 | `cofiberSuspensionComparisonHom_naturality`（Quasicategory、両端が押し出し）、`cofiberConnectingToSuspension_naturality`（さらに HasZeroMorphisms）；suspension 間の射と始点での可換式を入力 | この形では完了。Σ に値を持つ接続射の自然性も下記で完成 |
| S3 の対象比較と S4 の標準比較の一致 | `sourceDiagramObjIso` と始点・終点の式、`comparisonIso_eq_suspensionFunctorObjIso`、`cofiberConnectingToSuspension_comp_objIso_inv`（Quasicategory、IsStable） | 完了。S3 の定義は変更していない |
| Σ に値を持つ接続射の自然性 | `liftSourceHom` と始点の式、`suspensionFunctorObjIso_naturality`・逆方向版、`cofiberConnecting_naturality`、`cofiberConnecting_naturality_of_homotopy`（Quasicategory、IsStable、後二者は二つの cofiber 列） | 図式の関手圏の h の任意の射／実際のホモトピーに対して完成。任意の h の可換正方形の延長（TR3）も下記で完成 |
| ホモトピーの道と水平変形 | `homotopyEvaluation_arrow_of_vertexPath`、`squareHorizontalRightHomotopy`・`squareHorizontalLeftHomotopy` と始点成分の式（追加仮定なし） | 完了 |
| 最後の成分が零となる suspension への比較 | `exists_squareRightToSuspensionLeft`（Quasicategory）、`exists_squareToSuspension_zero_target`（さらに任意の HasZeroMorphisms、任意の四角形と右下の頂点の指定 suspension） | 完了。元の四角形の普遍性は不要 |
| 接続射の後の零合成 | `cofiberConnecting_comp_suspension_map_eq_zero`（Quasicategory、IsStable、cofiber 列） | 完了。三つの隣接零合成が揃った。三角構造は未完了 |
| h C の整数シフト | `stableEquivalenceHasShift`（任意の圏の自己同値）、`hasShift_ho`、`shiftOneSuspensionIso`、`shiftNegOneLoopIso`（Quasicategory、IsStable） | HasShift ℤ の全整合条件と Σ・Ω との比較まで完了。加法性は未完了 |
| Mathlib の cofiber 三角形 | `cofiberTriangle`、三つの隣接零合成、`cofiberTriangleMapOfHomotopy`（Quasicategory、IsStable、cofiber 列） | 通常の Triangle とその射として完了 |
| distinguished 集合と TR1 の存在部分 | `cofiberDistinguishedTriangles` と同型不変性、`exists_cofiberDistinguishedTriangle`（Quasicategory、IsStable、任意の h C の射） | 集合の定義・同型不変性・厳密に指定した射を含む三角形の存在は完了。TR3 も下記で完成。恒等射の三角形・回転・八面体・Pretriangulated は未完了 |
| 可換正方形の図式への延長 | `exists_stableSquare_of_homMk_comm`、`exists_terminalArrowHomotopy_of_sourcePath`、`exists_cofiberSquareHomotopy_of_comm`（Quasicategory、最後は両端が cofiber 列） | 完了。入力の二つの辺の一次単体を保持 |
| TR3 | `exists_cofiberTriangleMorphism_of_comm`、`exists_cofiberDistinguishedTriangleMorphism`、`complete_cofiberDistinguishedTriangle_morphism`（Quasicategory、IsStable、指定した最初の二成分の可換正方形） | 定義済み distinguished 集合の全ての三角形について完成。Pretriangulated instance は未完了 |
| 一点・区間の終点余極限 | `cosliceIdentityCone_isInitialVertex`、`cosliceIdentityCone_isColimit`、`isColimitCone_of_point_constant`、`edgeTerminalCocone_isColimit`（Quasicategory のみ） | 完了。恒等射の cofiber 四角形への適用は未完了 |
| S4〜S7 | 三角構造・長完全列・完全関手・D7 | 未完了 |

正確な公開型と構造体の構成子は [型一覧](archive/infinity-core-stable-log.md) に記録する。

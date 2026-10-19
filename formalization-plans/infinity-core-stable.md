# α-S：安定 ∞ 圏と D(S) の安定性

作成日：2026-10-18。状態：S1〜S6 完了。S7（D7）実装中。
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
TR1〜TR4 は下記のとおり証明済み。前三角構造と八面体公理を instance として公開した。
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
cofiber 列の三つの隣接零合成は完成。回転・八面体を含む三角構造も下記で完成。
`stableEquivalenceHasShift` は任意の圏の自己同値から整合的な整数シフトを構成する。
skeleton 上の mapSkeleton は充満忠実かつ対象全単射なので厳密な自己同型となり、その
Aut(Cat) の整数冪の等号から ShiftMkCore を作る。HasShift.induced により元の圏へ戻す。
skeleton は内部の補助構成だけに用い、h C の対象・射は変更しない。
`hasShift_ho` により h C は HasShift ℤ を持つ。`shiftOneSuspensionIso` と
`shiftNegOneLoopIso` は +1 と −1 のシフトを既存の Σ・Ω と自然同型で比較する。
単位・加法・結合の整合条件を含む整数シフトは完成。前加法構造とシフトの加法性も下記で完成。
`cofiberTriangle` は cofiber 列を Mathlib の通常の Triangle にまとめ、三つの隣接零合成も満たす。
`cofiberTriangleMapOfHomotopy` は実際の四角形間のホモトピーを三角形の射に移す。
`cofiberDistinguishedTriangles` はこれらの三角形の同型による閉包で、同型不変性も証明済み。
`exists_cofiberDistinguishedTriangle` は任意の射 f : a ⟶ b について、a・b・f を厳密に指定した
Triangle.mk f g h がこの集合に属することを証明する（TR1 の存在部分）。
これは単なる Arrow 表示での存在には留めていない。
`contractibleTriangle_mem_cofiberDistinguishedTriangles` により任意の対象 a の
可縮三角形 `(a → a → 0 → a[1])` の所属も証明済み。同型不変性・任意の射を含む存在と
合わせて、定義済み distinguished 集合に対する TR1 が揃った。
S4 の三角構造は下記で完成。前加法構造・シフトの加法性・回転・八面体と二つの instance を構成済み。
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
恒等射の三角形に向けた準備として、一点の恒等余錐の余極限性
`cosliceIdentityCone_isColimit` と、定値写像で表した版
`isColimitCone_of_point_constant` を証明した。さらに区間の終点を重複する退化二単体の
余錐 `edgeTerminalCocone` を構成し、`edgeTerminalCocone_isColimit` を証明した。
これらの余極限性には値域の Quasicategory のみを仮定する。
`squareColumnDiagram_isPushout` は一本の辺を二列に並べた四角形の押し出し性を証明する。
標準 span を一点の恒等余錐の付加で表し、区間の終点余錐に制限して判定した。
`columnZeroTriangle` は終点が零頂点である場合の cofiber 列で、第一射は恒等射。
`columnCofiberTriangleIso` はその cofiber 三角形と始点の可縮三角形を同型で比較する。
有限余極限から前加法構造へ進むため、`exists_colimitCocone_extension_of_trivialRestriction`
を追加した。coslice 制限が trivial Kan fibration なら、選んだ部分図式上の余極限余錐を
全体へ延長し、その制限と頂点を等号で保つ。`hasColimit_iff_of_trivialRestriction` は
余極限の存在自体を保存・反映する。right anodyne 制限と余極限付加への適用も公開した。
`exists_pastingExtension_of_outerColimit` は、左が押し出しである五頂点図式と
四頂点の外側基底で選んだ余極限から、右も押し出しとなる長方形を構成する。
元の五頂点上の図式と外側基底上の余錐の実際の射を厳密に保持する。
これらは Quasicategory のみを仮定する。
`pastingBottomFaceIso` と `pastingBottomIntersectionIso` は底辺三角形と共通辺の標準形を与える。
`pastingCornerBottom_isPushout` は左四角形と底辺二単体が五頂点図式を作る形状の pushout。
`pastingCornerGlue` とその二つの制限の式により、入力の四角形と合成二単体を厳密に保持できる。
`exists_pushoutRectangle_of_left_and_bottom` はこの貼り合わせを余極限の延長に適用し、
左四角形・底辺二単体・外側余錐を保つ右押し出し長方形を構成する。
外側余錐を cofiber から与える工程も、下記の指定零枝の輸送によって完成した。
この輸送の一般部分として、`sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence`
を証明した。前合成の同値条件を持つ単射による coslice 制限は trivial Kan fibration である。
join の相対的な和の包含が同値条件を持つことを、pushout と二対三則で直接証明した。
`hasColimit_iff_of_functorIso` は任意の同型な図式の余極限の存在の同値を証明する。
可逆円柱の両端の形状の同値と、指定した余極限余錐の厳密な延長を使う。
`nonempty_functorIso_span_of_first_eq_terminal_second` により、第一枝が同じで
第二枝が終対象へ向かう二つの span の FunctorIso を構成した。始点評価の fiber 内で
二つの第二枝が終対象となることと、その終対象全体の可縮性を使う（Quasicategory のみ）。
`hasColimit_span_of_terminal_second`・`hasColimit_span_of_zero_second` により、安定な X では
指定した零枝を持つ span に余極限が存在する。
`hasColimit_pastingOuterBase_of_zeroCorner` と `exists_pushoutRectangle_of_zeroTriangle` は
これを貼り合わせに適用し、外側余極限の追加仮定を外した。
`exists_zeroSourcePushoutSquare` は任意の二頂点 x・y について、(0,0) が零、
(1,0) が x、(0,1) が y である押し出し四角形の存在を証明する。
y の loop 四角形の右に、右下の零頂点から x への辺との合成二単体を貼って構成した。
二つの入力頂点と実際の押し出し性まで完成。h C 上の二項余積としての普遍性・instance も下記で完成。
双積・前加法構造への移行は次の工程。
この普遍性へ向けて `diagramNestedCosliceIso` を追加した。任意の c : L → sliceUnder p に対し、
sliceUnder (sliceUnderUncurry c) と sliceUnder c を join の結合同型で比較する。
`sliceUnderPostcomp_trivialKanFibration_of_trivial` は任意の形状の固定図式について、
trivial Kan fibration の後合成が coslice でも trivial Kan fibration となることを示す。
`diagramNestedCosliceProjection` は二重 coslice の同型の後で内側の射影を適用する射で、
`diagramNestedCosliceProjection_uncurry`・`_val`・`_vertex` により脚の厳密な制限と頂点保持を計算する。
`diagramNestedCosliceProjection_trivial_of_initial` と `isColimitCone_iff_forget_initial` は、
始対象の下の図式からその始対象を忘れても余極限性が同値であることを証明する。
余極限性の同値は Quasicategory を仮定するが、射影の充填性・射の計算は値域に仮定しない。
`spanPointJoinIso` は標準 span を一点と離散二点の join と同定する。
共通始点と二つの終点の包含の式も厳密に証明した。
`isColimitCone_iff_restrict_joinInr_of_initial` は、始点が始対象である左 cone の余錐を
右因子へ実際に制限しても余極限性が同値であることを示す。
`binaryPointDiagram x y` は二つの指定頂点を値とする離散二点図式。
`hasColimit_binaryPointDiagram` により安定な X の任意の二頂点について余極限の存在が完成した。
零始点の押し出しの余錐を標準 span の join 表示へ移し、始対象の零始点を除いて構成した。
h C の二項余積の Hom の存在・一意性と HasBinaryCoproducts instance まで完成した。
`JoinCocone.leg` は任意の余錐の各脚を端点つきの辺とし、`legCompStruct` は
余錐間の辺の頂点成分との合成三角形を実際の二単体で与える。
`leg_comp_projection` はその h C での可換式（これらには Quasicategory は不要）。
`exists_coconeVertexFactorization` は任意の形状の余極限余錐から任意の同じ図式の余錐へ、
全ての脚を保つ h C の頂点の射を作る（Quasicategory）。一般の形状で一意性は主張しない。
`binaryCoconeOfEdges` は指定された共通終点の二本の辺から二点図式の余錐を作り、
その頂点と二本の脚の一次単体を厳密に計算する（値域に仮定なし）。
`exists_binaryColimit_desc` は任意の二点図式の余極限 c と、同じ指定頂点 z への二本の h C の射について、
c の二つの脚との合成がそれぞれ指定射となる h C の射 c.vertex → z の存在を証明する。
Quasicategory と IsColimitCone c のみを仮定し、安定性は不要。
`coconeLegTriangle` と両端・右辺・固定左辺の式で合成二単体を点下の余錐の族に戻し、
`exists_binaryCoconeTriangleFamily` は共通の頂点の辺に沿って二つの族を貼る。
`exists_binaryCoconeEdgeLift` は両脚の合成二単体から余錐間の辺を作り、射影の一次単体を保つ。
ここまでは値域への仮定なし。Quasicategory では `exists_binaryCoconeEdgeLift_of_comm`・
`exists_binaryCoconeHomLift` が両脚との可換式だけから持ち上げを与える。
`binaryColimit_hom_ext_to_cocone` と `binaryColimit_hom_ext` は coslice の始対象性で一意性を証明する。
`binaryColimit_isColimit` はこの普遍性を Mathlib の BinaryCofan の IsColimit として公開する。
`hasBinaryCoproduct_of_binaryColimit` は二点図式の余極限から h C の二項余積を得る一般補題。
`hasBinaryCoproducts_ho {X : SSet} [Quasicategory X] [IsStable X] :
HasBinaryCoproducts (hoFunctor.obj X)` により h C の二項余積 instance が完成した。
反対圏を用いる二項積側も構成した。`spanSwapIso` は標準 span の二枝を交換する同型、
`isPushoutSquare_iff_transpose`・`isPullbackSquare_iff_transpose` は四角形の転置不変性。
`sliceUnderPostcomp_isIso` と `isPushoutSquare_iff_postcomp_isIso`・
`isPullbackSquare_iff_postcomp_isIso` は値域の同型による不変性を与える。
`dualSquare` は二座標を反転・交換し、(0,1) の零角を保持して値域を反対にする。
`isPushoutSquare_iff_dualSquare`・`isPullbackSquare_iff_dualSquare` は押し出しと引き戻しの交換、
頂点と二辺の式は零角と指定辺の保持を与える（ここまでは値域への仮定なし）。
`hasZeroVertex_op` は零対象の双対化、`isStable_op` は `[Quasicategory X] [IsStable X]` から
`IsStable X.op` を三条件の直接証明で与える。全有限極限・余極限は仮定しない。
`exists_zeroTargetPullbackSquare` は二つの指定頂点を右下・左上に持つ零終点の引き戻しを与える。
`edgeHomotopyUnopFunctor` とその充満忠実性・同値を辺の類で構成し、
`homotopyOppositeEquivalence X : hoFunctor.obj X.op ≌ (hoFunctor.obj X)ᵒᵖ` を得た（Quasicategory）。
`hasBinaryProducts_ho {X : SSet} [Quasicategory X] [IsStable X] :
HasBinaryProducts (hoFunctor.obj X)` はその同値で反対側の二項余積を輸送する。
h C の二項積・二項余積は完成。双積性は下記で完成。前加法構造も下記で完成。
その比較のため、零始点の押し出しの包含を、分裂する cofiber/fiber 列へ延長した。
`exists_zeroReturnTriangle` は零対象から出る辺に、長辺が実際の恒等辺となる戻り二単体を与える
（Quasicategory、安定性は不要）。`pastingOuterStandardSpan_bottomEdge` と
`pastingOuterCocone_restrict_standardSpan_val` は長方形の形状の厳密な式。
`exists_pushoutRectangle_of_returnTriangle` は戻り二単体と列四角形の普遍余錐を保持し、
指定左押し出しを外側が指定列四角形で右も押し出しとなる長方形へ延長する（Quasicategory）。
`pastingTop_isSplitEpi_of_outer_column` は上側二単体から右上辺の切断を与える（値域に仮定なし）。
`exists_splitCofiberRectangle` は安定性を転置した右零角へ適用し、右側の引き戻し性も得る。
`exists_cofiberSequence_of_zeroSourcePushout` はその右側を転置し、元の第一包含を厳密に保つ
cofiber/fiber 列を作る。三対象は元の右下・右上・左上の指定頂点で、第二射は IsSplitEpi。
`cofiberConnecting_eq_zero_of_epi` と `cofiberTriangle_mor₃_eq_zero_of_epi` は第二射の全射性だけで
接続射・三角形の第三射が零となることを示す。
`exists_splitCofiber_of_zeroSourcePushout` は指定した包含・三対象・cofiber/fiber 性・
第二射の切断・接続射の消滅をまとめる（Quasicategory、IsStable）。
この構成だけで双積性や前加法構造の完成とは数えない。
幾何学的な包含と二項余積の標準包含・射影を照合した。
`squareBinaryCocone` は四角形の中間二頂点を底とする余錐を取り出し、
`squareBinaryCocone_leg_left`・`_right` はその脚の一次単体が元の右辺・上辺に等しいことを示す。
`binaryCofan_isColimit_of_edge_eq` は端点の表示も含む二項余錐の余極限性の輸送。
`squareBinaryCocone_isColimit` と `zeroSourcePushout_isBinaryCoproduct` は始点が始対象の
押し出しの右辺・上辺が h C の普遍二項余錐であることを示す（Quasicategory、安定性は不要）。
`zeroSourcePushoutCoproductIso` は Mathlib の選ばれた余積から終端頂点への同型で、
標準の二包含を右辺・上辺へ送る式も持つ。
`zeroSourceCoproductFst`・`Snd` と四つの包含との合成式は零射のみを追加仮定にする。
`pastingTopCompStruct`・`pastingTop_hom_comp` と列四角形の場合の Arrow の式は、
上側の合成を元の第二包含を保持する形で記録する（値域に仮定なし）。
`exists_pastingProjection_eq_coproductSnd` は列四角形への延長の右上辺を元の頂点間の辺として取り出し、
その類が標準第二射影に等しいことを余積の一意性で証明する（Quasicategory、零射）。
`exists_coproductCofiberSequence` は零始点の押し出しの第一包含・標準第二射影を
Arrow の等号で指定する cofiber/fiber 列を与える。三対象の頂点、第二射の分裂性、接続射の消滅も保持する
（Quasicategory、IsStable）。双積性は下記で完成。前加法構造も下記で完成。
比較に使う零 cofiber・零 fiber からの同型判定を整備した。
`homotopyOppositeEquivalence_map_homMk` と双対四角形の辺の式は、反対ホモトピー圏の比較が
実際の辺の反転を保つことを示す。`terminalTargetPullback_isBinaryProduct` は終点が終対象の
引き戻しを下辺・左辺による h C の二項積として公開する（Quasicategory、安定性不要）。
`isIso_squareHoBottom_of_pullback_terminal_top` と
`isIso_squareHoRight_of_pushout_initial_left` は終対象因子・始対象因子からの同型判定。
`ZeroTriangle.isIso_f_of_zero_cofiber` と `isIso_g_of_zero_fiber`、
`CofiberSquare.homMk_isIso_of_zero` と `FiberSquare.homMk_isIso_of_zero` は安定性で零角の列を交換し、
cofiber または fiber の零性から元の射の同型性を証明する。逆向きも下記で完成した。
`ZeroTriangle.zero_cofiber_of_zero_source_middle`、`zero_middle_of_zero_source_cofiber`、
`zero_source_of_zero_middle_cofiber` と fiber 版は、三対象の任意の二つが零なら第三も零となる判定。
前加法構造や三角圏の公理は使わない。
`colimitCoconeHomotopy_isInvertible_of_restriction` と precomp 版は、普遍余錐の充満忠実射影で
基底に制限した比較の可逆性を反映する。
`pushoutSquareHomotopy_isInvertible_of_span` と `exists_pushoutSquareFunctorIso_lift_span` は
span で可逆な比較を押し出し全体へ延長し、指定した制限の順射の類を保持する。
`nonempty_cofiberSquareFunctorIso`・`cofiberSquareComparisonIso`・`cofiberSquare_zero_iff` は
同じ辺の任意の二つの cofiber 四角形の関手同型、cofiber 頂点の比較同型、零性の選択独立性を与える
（Quasicategory、安定性不要）。
`homotopyVertex_isInvertible_of_functorEdge` と区間の端点による判定、
`spanHomotopy_isInvertible_of_branches` により、指定した比較の可逆性を二枝から判定する。
`cofiberSquareHomotopy_isInvertible_of_vertexPaths` と
`exists_invertibleCofiberSquareHomotopy_of_comm` は、最初の二成分が同型の cofiber 比較を
全体が可逆なホモトピーへ延長する（Quasicategory のみ）。
`ZeroTriangle.zero_cofiber_of_isIso_bottom`・`CofiberSquare.zero_of_homMk_isIso` は
恒等射の零 cofiber との比較により同型から零 cofiber を得る（Quasicategory のみ）。
`FiberSquare.opCofiber` は指定辺を保って fiber 四角形を双対化する（値域に仮定なし）。
`FiberSquare.zero_of_homMk_isIso` も Quasicategory のみで完成した。
`CofiberSquare.homMk_isIso_iff_zero`・`FiberSquare.homMk_isIso_iff_zero` は
任意の選んだ cofiber/fiber による同型判定を同値として公開する（Quasicategory、IsStable）。
同型から零となる向きは安定性不要、零から同型となる向きに安定性を使う。
任意の押し出しの右に零対象を付加する構成が完成した。
`exists_terminalCompositeTriangle` は最初の辺を固定し、指定終対象へ向かう二単体を作る
（Quasicategory）。`hasColimit_span_of_terminal_first` と
`exists_pushoutRectangle_of_zeroEnd` は外側 span の第一零枝から余極限を得て、
左四角形と底辺二単体を保持した両側押し出しの長方形へ延長する（Quasicategory、IsStable）。
`IsStable.pullback_of_pushout_square` は右側と外側の零角に安定性を適用し、
引き戻し貼り合わせを打ち消して任意の押し出しを引き戻しにする。
`IsStable.pushout_of_pullback_square` は反対の安定性から逆方向を与え、
`IsStable.pullback_iff_pushout_square` は全四角形での同値を公開する（Quasicategory、IsStable）。
HA 1.1.3.4 の四角形の条件は逆方向も完成したが、全有限極限・余極限の存在はまだ未証明。
`ZeroTriangle.binaryProductOfRetraction` は cofiber 列の第一射の任意の左逆と第二射を
中間対象上の二項積とする（Quasicategory、IsStable）。
`binaryProductOfRetraction_of_arrow_eq` は三対象・二射の表示の変更を Arrow の等号で処理する
（任意の圏）。`zeroSourcePushout_isBinaryProduct_of_retraction` と標準射影版は、
第一包含の任意の左逆と標準第二射影の積性を与える。
`zeroSourcePushoutBinaryBiproduct` は元の押し出し頂点と標準包含・射影を使う双積データ。
`hasBinaryBiproducts_ho` は h C の二項双積 instance として完成した（Quasicategory、IsStable）。
h C の前加法構造とシフトの加法性が完成した。
`stableHomAddCommMonoid` は二項双積からの Mathlib の Eckmann–Hilton 構成を使う。
`exists_additiveInverse_of_zeroSourcePushout` は、第一射影 p に q ≫ f を加えた左逆で
二項積を作り、零と恒等射を持ち上げて f の加法左逆元を得る。
`exists_stableHom_additiveInverse` は任意の二対象を指定二入力の押し出しに表示して転送する。
`stableHomAddCommGroup` は加法と零を保ったまま逆元を選び、
`preadditive_ho : Preadditive (hoFunctor.obj X)` に合成の左右の分配則と束ねた
（以上 Quasicategory、IsStable）。モノイド・群の補助定義は大域 instance にせず、
最終的な前加法構造だけを instance とする。
`hasFiniteProducts_ho` と `hasFiniteBiproducts_ho` は零対象・二項積・前加法性から
h C の有限積・有限双積を与える（Quasicategory、IsStable）。
∞ 圏自体の全有限極限・余極限の存在を代用するものではない。
`suspensionFunctor_additive`・`loopFunctor_additive`・`shiftFunctor_additive_ho` は
自己同値が二項積と零射を保つことから Σ・Ω・全整数シフトの加法性を与える
（Quasicategory、IsStable）。元の Σ・Ω・HasShift ℤ は変更しない。
cofiber 列の回転の幾何学的構成と最初の二射の照合が完成した。
`pastingLeftToOuterShape`・`pastingLeftToOuterHomotopy` は長方形の左四角形から外側への
左列を固定する変形を構成する。始点・終点・固定始点・右上の道を厳密に計算した
（値域の仮定なし）。
`CofiberRotationRectangle t` は、左面が t の四角形と厳密に同じ、右下が零、
右面・外側が押し出しの長方形のデータ。`nonempty_cofiberRotationRectangle` と
`chosenCofiberRotationRectangle` は任意の cofiber 列でその存在と選択を与える
（Quasicategory、IsStable）。外側は入力の始点の `suspensionSquare`、右面の転置は
`rotatedZeroTriangle` となり、`rotated_isCofiber` がその押し出し性を与える
（回転長方形を入力すれば値域の仮定なし）。
`rotated_source`・`rotated_middle`・`rotated_target` は三対象を B・C・指定 suspension と照合する。
`rotated_f_arrow` は第一射が元の第二射、`rotated_g_arrow_connecting` は第二射が
外側 suspension への接続射であることを端点も含めて示す
（Quasicategory、任意の HasZeroMorphisms、後者は IsCofiberSequence t）。
`cofiberTailShortComplex t ht` は厳密に B → C → ΣA の短複体。
`CofiberRotationRectangle.tailShortComplexIso` と `exists_cofiberTailShortComplex` は
その二射列が cofiber 列の短複体の像と同型となることを、追加の条件なしに証明する
（Quasicategory、IsStable）。
回転後の列の接続射が −Σf となる符号の同定は下記で完成。
通常の Triangle の回転の所属とその逆方向も下記で完成。**TR2 は完了**。
suspension の二つの零枝の交換の幾何学と自然性を整備した。
`SuspensionSquare.transpose` は二つの零角を交換し、始点・suspension 頂点を保つ。
`transpose_transpose`・`transpose_vertex` は二回で元に戻ることと頂点の保持を示す
（値域に仮定なし）。`swapIso` は元の四角形と転置の標準比較による同じ頂点上の自己同型
（Quasicategory）。
`squareTranspose_evaluation`・`squareDiagramHoEvaluation_transpose` は対角頂点の評価の
転置不変性を単体的な射・h の射の両方で示す。
`diagramComparisonIso_hom_transpose`・`comparisonIso_hom_transpose` は標準比較との両立。
`swapIso_hom_eq_reverse`・`swapIso_hom_comp_self` は交換が逆向きの標準比較とも一致し、
その二乗が恒等になることを証明する（Quasicategory、IsStable は不要）。
`diagramComparisonIso_transpose_naturality`・`swapIso_naturality` は、異なる始点を持つ
suspension 図式の任意の h の射に対して交換作用が可換となることを証明する
（Quasicategory、安定性・加法性の追加仮定なし）。
**交換の二乗が恒等であることを負の恒等射との一致とは数えない**。
構成済みの加法で `swapIso.hom = -𝟙` を証明する工程は、以下のループ表示と加法の照合により完成した。
その証明のため、HA Lemma 1.1.2.10 の終点固定余錐空間 D(p) を構成した。
原典の証明は D(σ) を、可縮な二因子 D(f) の D(A) 上の引き戻しとして扱い、
ループ模型への比較で二枝交換をループ反転へ移す。
[coconeMappingSpace の参照箇所](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=25)。
これは証明方針の参照であり、形式化で引用公理として使っていない。
`coconeMappingSpace p y` は既存の coslice 射影の頂点 fiber で、
`coconeMappingSpace_kanComplex` が Kan 性を与える（Quasicategory、安定性不要）。
`coconeMappingSpace_restrict_fibration` は任意の単射による部分図式への制限が
全ホーンの持ち上げ性を持つことを示す（Quasicategory、Mono）。
`coconeMappingSpace_point_isContractibleKan` は始対象からの空間の可縮性、
`coconeMappingSpace_edge_isContractibleKan` は始対象へ向かう辺からの空間の可縮性を与える
（後者は Quasicategory、前者は不要）。
`exists_coconeMappingSpace_glue` と `coconeMappingSpace_hom_ext_of_pushout` は、
図式の pushout に沿う任意パラメーターの余錐の厳密な貼り合わせの存在・一意性。
`spanCoconeMapping_isPullback` は二枝の余錐空間の共通始点上の厳密な引き戻しを与える
（以上、値域の仮定なし）。右脚 `spanCoconeMappingRightBase` は、共通始点の二つの図式表示を
ホーンの等号で輸送する。制限と輸送は一般の uncurry の補題へ分離し、カーネル検査の時間切れを解消した。
`coconeMappingSpace_spanSwap_left`・`right` は span の交換によって二枝が交換されることを
任意パラメーターの余錐の等号として示す（値域の仮定なし）。
D(p) の連結成分と Hom、および空間そのものと左写像空間の比較が完成した。
`leftFibrationInitialTotal` は始点固定の coslice の底の終点を固定した中間空間。
`leftFibrationInitialProjection` は底の coslice fiber への射影で、left fibration の下で自明 Kan fibration。
`leftFibrationInitialEvaluation` は元の fiber への評価で、始点の始対象性の下で自明 Kan fibration。
始対象性からの自明性には p の充填性を要求しない。底が Quasicategory で p が LeftFibration なら
中間空間は Kan 複体となる。`leftFibrationInitialBaseIso` は底の coslice fiber を左 pinched 模型と同型にする。
`leftFibrationInitialFiberPiZeroEquiv` は始点 c が始対象のとき
π₀(vertexFiber p y) ≃ Hom(p(c), y) を与える（底 Quasicategory、p は LeftFibration）。
`coconeMappingSpacePiZeroEquiv` は余極限余錐 c にこの比較を適用し、
π₀ D(p) ≃ Hom(c.vertex, y) を与える。`pushoutCoconeMappingSpacePiZeroEquiv` は
押し出しの終端頂点に対する同値（いずれも Quasicategory、安定性不要）。
`leftFibrationInitialSection`・`leftFibrationInitialHomComparison` は終点評価の切断から
fiber → 左写像空間の実際の射を構成する。この射は上の条件で単体的ホモトピー同値。
`coconeMappingSpaceHomComparison` とそのホモトピー同値性は余錐空間への適用。
`leftFibrationInitialFiberPiZeroEquiv_evaluation` は中間空間の二射影による計算則、
`leftFibrationInitialFiberPiZeroEquiv_eq_comparison`・`coconeMappingSpacePiZeroEquiv_eq_comparison` は
π₀ の同値と実際の比較射の π₀ への作用が一致することを示す。
比較射は切断の選択を含む。比較 span から π₀ 上の自然性を証明した。
`stableCoslicePostcomp` は表示変更を含む後合成で、射影・uncurry・二段階の合成と可換。
`leftFibrationInitialTotalMap` は底を保つ関手 f と始点の像の等号から中間空間の射を構成し、
`leftFibrationInitialTotalMap_evaluation`・`projection` は二射影との可換性を示す（充填性不要）。
`leftFibrationInitialFiberCoslicePiZeroEquiv` は左模型へ移す前の coslice fiber の π₀ の同値で、
同名の `_naturality` は始点とその像が始対象のとき底上の関手との両立を与える。
`leftFibrationInitialFiberPiZeroEquiv_naturality` はこれを Hom 表示へ移した等号で、
底の始点の像の等号を Hom の前合成として明示する（底 Quasicategory、両射は LeftFibration）。
`coconeMappingSpacePiZeroEquiv_restrict` は制限前後が余極限余錐なら形状の制限との両立、
`_reindex` は同型な形状、`_spanSwap` は二枝交換への適用（Quasicategory、元の余極限性のみ）。
二枝交換の場合は c.restrict spanSwap の Hom 表示と比較している。
`stablePinchedHomLeftPiZeroEquiv_mk`・`stableCosliceFiberPiZeroEquiv_mk` は左模型・coslice fiber の
零単体が対応する辺の h の類へ移ることを示す（Quasicategory）。
`leftFibrationInitialFiberPiZeroEquiv_total_vertex` は中間空間の頂点の像を底の辺の類で計算する。
`_total_initialHom` と `leftFibrationInitialFiberPiZeroEquiv_mk` はこれを始対象からの一意の射の像として表す。
`leftFibrationInitialFiberPiZeroEquiv_change_initial` は二つの始対象による Hom 表示が、
Core の initialVertexIso を底へ送った射による前合成で一致することを示す
（全空間・底 Quasicategory、LeftFibration、両始点の始対象性）。
`coconeMappingSpacePiZeroEquiv_change_cocone` は同じ図式の二つの余極限余錐の Hom 表示が
colimitVertexIso による前合成で一致することを示す（Quasicategory、両余極限性）。
`_restrict_change_cocone` と `_spanSwap_change_cocone` は形状制限・二枝交換の後の任意の余極限余錐での表示へ適用する。
実際の選択付き比較射の厳密な自然性はまだ主張しない。
coslice から余錐の関手単体集合への `cosliceCoconeDiagramMap` と、正方形への `cosliceSquareDiagramMap`
を構成した。前者は零次の余錐・固定図式への制限・余錐頂点での評価、後者は元の四角形の
零次表示・固定 span への制限・終端頂点評価と厳密に可換（Quasicategory 性不要）。
`colimitSquareComparisonIso` は coslice の標準同型を四角形へ移した同型。
`cosliceSquareDiagramMap_hom_restriction_arrow`・`_hom_source_arrow` はその span・始点成分の
恒等性、`colimitSquareComparisonIso_target_arrow` は終端成分が colimitVertexIso であることを示す
（Quasicategory、前者の二つは任意の coslice の h の射に適用）。
`SuspensionSquare.comparisonIso_eq_colimitVertexIso_arrow` は同じ span 上の二つの余極限余錐が
s、r の四角形表示を持つとき、既存の suspension 標準比較と colimitVertexIso が Arrow として
一致することを示す。始点成分による一意性で、二種類の比較を初めて照合した。
`SuspensionSquare.swapIso_eq_colimitVertexIso_arrow_of_sameSpan` はこれを転置へ適用するが、
**pushoutSpan s.transpose.square = pushoutSpan s.square を追加仮定する**。
任意の suspension では二つの零枝が異なり得るため、この等号は自動ではない。
`pushoutSpan_transpose` は転置と span の交換の厳密な計算、`edgeSpan_self_swap` は
同じ辺を二度使う span の交換不変性を示す（値域の仮定なし）。
`hasColimit_edgeSpan_self` は指定した零対象への辺 f を二度使う span の余極限の存在を与える。
`symmetricSuspensionSquare f hz` はその余極限を四角形へ戻した suspension で、
`_span` は元の edgeSpan f f の等号、`_sameSpan` は転置前後の span の等号（Quasicategory、IsStable）。
`chosenSymmetricSuspensionSquare x` は選んだ零対象への辺を一つ選んだ各頂点の補助模型。
`chosenSymmetricSuspensionSquare_sameSpan` により、`_swap_comparison` はその swapIso が
同じ coslice 内の colimitVertexIso であることを追加の span の等号なしで示す。
従来の chosenSuspensionSquare・suspensionFunctor の選択は変更しない。
`SuspensionSquare.swapIso_comparison` は標準比較との可換性（Quasicategory のみ）、
`swapIso_eq_neg_id_of_comparison` と `_of_chosenSymmetric` は一つの模型での負号を任意の同じ始点の
suspension へ移す（Quasicategory、IsStable）。これらの条件付き転送定理の仮定となる負号そのものも下記で証明した。
具体的な頂点の Hom では、既存の preadditive_ho を X.HomotopyCategory の型表示に局所的に与える。
加法構造を新たに選んだり変更したりはしない。
`fixedCosliceReindex p i hi` は i ≫ p = p を満たす形状の自己射の、同じ coslice 上の自己作用。
終点射影と可換で、i が対合なら自己作用も対合。`fixedCoconeMappingReindex` は同じ終点の
余錐空間に制限した自己作用で、これも対合となる（値域の充填性不要）。
`JoinCocone.reindexFixed` と `vertex_reindexFixed` は同じ図式・頂点での再添字付け。
対合なら余極限性を保ち、`fixedCoconeReindexVertexIso` は元の余極限余錐との標準比較を自己同型にする。
`coconeMappingSpacePiZeroEquiv_reindexFixed` は D(p) の π₀ の作用がこの自己同型の前合成となる公式
（Quasicategory、余極限余錐）。`fixedCosliceReindex_uncurry` と余錐空間版は、
同じ図式のまま定義した自己作用が展開後には join の左因子の前合成であることを示す。
`SuspensionSquare.pushoutCocone_reindexFixed_spanSwap` は再添字付けた余錐が転置余錐に等しいこと、
`fixedReindexVertexIso_eq_swapIso_arrow` は標準頂点自己同型が swapIso と Arrow として一致することを示す
（Quasicategory、転置前後の span の等号）。`chosenSymmetricSuspensionSquare_reindex_swap_arrow` は
対称模型でこの等号の追加仮定を除く（Quasicategory、IsStable）。
`symmetricCoconeSwap f y` は edgeSpan f f の D(p) 上の二枝交換の実際の自己写像。
`_comp_self`・`_Iso` で対合・自己同型、`_left`・`_right` で任意パラメータの二枝交換を示す
（値域の充填性や f の終点の零対象性は不要）。`_piZero` は余極限の Hom 表示での前合成の公式
（Quasicategory、指定した余極限余錐）。
`vertexFiberι_isQCatEquivalence_of_contractible_base` と `_homotopyEquivalence_of_contractible_base` は、
可縮な Kan 複体を底に持つ Kan fibration の任意の fiber の包含が実際のホモトピー同値であることを示す。
点から可縮な底への同値を、可逆 path の相対持ち上げを持つ射に沿って引き戻した。
`kanKernelPairLoopComparison r hE e` は Kan fibration r : E → B、可縮な E、基点 e に対し、
E ×_B E → pinchedHomLeft (r e) (r e) の実際の射を与える。
第二射影の fiber 包含のホモトピー逆を選び、元の r の fiber の表現可能な比較へ合成する。
`_homotopyEquivalence` は E・B が Kan のときの実際の同値性。
`kanKernelPairPiZeroLoopEquiv` は π₀(E ×_B E) と h B の基点 r e の自己射の型との同値。
`_fiber` は固定点の fiber の包含上で、元の r の Hom 同値に一致する計算則。
`coconeBranchSource f y` は辺の余錐空間から始点の余錐空間への Kan fibration（X Quasicategory）。
辺の終点が始対象なら、`coconeBranchKernelPairLoopComparison` とそのホモトピー同値性、
`coconeBranchKernelPairPiZeroLoopEquiv` を構成した。安定性全体は不要。
比較射はホモトピー逆の選択を含む。
`symmetricCoconeFirst`・`Second` は edgeSpan f f の両枝を同じ指定辺の余錐空間へ制限する射。
それぞれの uncurry の式、共通始点での一致、二枝交換が First と Second を交換する等号を証明した。
`symmetricCoconeBranches_isPullback` は貼り合わせの存在・一意性による自己引き戻しの普遍性、
`symmetricCoconeKernelPairIso` は D(edgeSpan f f) と同じ coconeBranchSource の自己引き戻しの標準同型。
両射影の計算と `symmetricCoconeKernelPairIso_swap` は、この同型が symmetricCoconeSwap を
引き戻しの二成分交換 pullbackSymmetry へ厳密に移すことを示す（値域の充填性不要）。
`symmetricCoconeLoopComparison f hz y e` はこの同型を枝のループ比較へ合成した実際の射で、
`_homotopyEquivalence` は X Quasicategory・z 始対象の下での同値性。安定性全体は不要。
`symmetricCoconePiZeroLoopEquiv` と `_eq_comparison` は π₀ の Hom 同値と実際の射の一致。
これで対称 span 全体の余錐空間からループ模型への表示の輸送まで完成した。
`kanKernelPairFiberInclusion` は元の基点の像の fiber を第二成分固定の自己引き戻しに含め、
E が可縮な Kan・射が Kan fibration なら π₀ で全単射となる。
`exists_kanKernelPairSwap_fiber_path` は交換された頂点から固定 fiber へ戻す辺を、
基点への辺とその底への像の持ち上げの組として構成する。
`kanKernelPairPiZeroLoopEquiv_comp_swap`・`_swap` は二成分交換をループの逆射へ送り、
`symmetricCoconePiZeroLoopEquiv_comp_swap`・`_swap` は対称 span の二枝交換への適用。
二乗が恒等という性質だけから逆射を推論せず、二辺の底への厳密な一致から合成の恒等式を証明した。
`kanKernelPairMap`・`kanKernelPairFiberMap` は底を変える可換正方形が誘導する射。
`kanKernelPairFiberMap_inclusion` は固定 fiber の包含との可換性。
`leftFibrationInitialVertexHom_square` は四空間が quasicategory で始点と像が始対象のとき、
代表辺を二通りに底へ送る公式を比較する。これにより `kanKernelPairPiZeroLoopEquiv_naturality` を
両射が Kan fibration・両全空間が可縮な Kan・両底が Kan の仮定で証明した。
底の基点の等号は eqToHom による可換式として明示する。
`kanKernelPairDiagonal` は自己引き戻しの対角、`kanKernelPairPiZeroLoopEquiv_diagonal` は
基点の対角成分がループの恒等射を表すことを示す。
`kanKernelPairLoopProduct` はループの射の合成を π₀ に移した演算。
結合則、対角成分の左右単位、交換による右逆元、可換正方形での積の自然性を証明した。
`representableOperation_eq_add` は一般の前加法圏で二項双積が存在するとき、
後合成に自然で零射を左右単位に持つ Hom(A,B) 上の演算が既存の加法に一致することを示す。
演算の結合性や可換性は仮定しない。`representableRightInverse_eq_neg` はその右逆元を負号に同定する。
`leftFibration_prism_lift` は任意パラメーターの区間族を指定先頭から left fibration に持ち上げる。
`LeftFibrationFiberTransport` は fiber の射と包含を結ぶ区間族を、両端・底への像の等号付きで保持する。
`nonempty_leftFibrationFiberTransport` は底の任意の辺についてその存在を証明する
（left fibration のみ、全空間・底の quasicategory 性は不要）。
`exists_leftFibrationFiberTransport_lift` は中間の fiber の輸送を、left fibration である制限射に沿って
持ち上げる。区間族と fiber の射の両方で制限と厳密に可換となる。
`LeftFibrationFiberTransport.vertexEdge_over` は輸送の各頂点の辺が底の指定辺そのものに写る等号。
`leftFibrationInitialFiberPiZeroEquiv_transport` は全空間・底 quasicategory、left fibration、始対象の下で、
輸送が Hom 表示で底の辺との後合成になることを証明する。
`nonempty_coconeEndpointTransport`・`coconeMappingSpacePiZeroEquiv_transport` は
余錐空間と余極限頂点からの Hom 表示への適用（Quasicategory、後者は余極限余錐）。
`exists_coconeEndpointTransport_restrict` は任意の単射による図式制限に対し、
部分図式で選んだ輸送を変更せず全図式の輸送を制限と厳密に可換に選べることを示す（Quasicategory）。
`exists_coslice_glue_of_pushout`・`coslice_hom_ext_of_pushout` は終点固定条件なしの coslice の族の
貼り合わせの存在・一意性。`exists_coconeEndpointTransport_glue` はこれにより
二枝の輸送の区間族が共通部分で一致するという入力から、全図式の輸送を両枝と厳密に可換に構成する。
これら三つの貼り合わせ結果に値域の quasicategory 性や余極限性は不要。
`LeftFibrationFiberTransport.changeDiagram` と `_map`・`_uncurry` は固定図式の等号による
表示変更を輸送の射と区間族に適用する。`coconeEndpointTransport_restrict_uncurry` は
共通部分への区間族の制限を展開後に計算する（充填性の仮定不要）。
これにより、共通始点の輸送を先に選び同じ枝に持ち上げた場合、対称 span の二枝の表示変更後の
区間族は厳密に共通始点で一致する。
`exists_symmetricCoconeEndpointTransport` はこの整合条件を仮定せず検証し、
同じ枝と対称 span 全体の輸送を両枝と厳密に可換に構成する（Quasicategory のみ）。
枝の終点の零性や全体の余極限性は不要。
`symmetricCoconeTransport_kernelPair`・`_piZero` は、この全体の輸送が自己引き戻し表示で
枝と共通始点の輸送から誘導される kanKernelPairMap に一致することを示す
（三つの輸送と可換性を入力とすれば充填性不要）。
`symmetricCoconeLoopProduct`・`symmetricCoconeLoopUnit` は自己引き戻しの積と対角を全体の π₀ に移す。
二つの `_kernelPair`、積の左右単位、二枝交換が右逆元である式を証明した。
積とその単位・逆元の性質は Quasicategory・枝の終点の始対象性・枝の余錐の基点を仮定する。
単位の定義自体には充填性や始対象性は不要。
`symmetricCoconeLoopProduct_transport` は前述の整合する三つの輸送に対する積の保存、
`symmetricCoconeLoopUnit_transport` は単位の保存を示す。
これらの式では、終域側の枝の基点は始域側の枝の基点を枝の輸送で送った像とする。
任意に選び直した終域の基点でも同じ積となる独立性は、まだ証明していない。
`leftFibrationInitialVertexHom_eq_zero_of_factor` は底の零対象を経由する頂点の Hom 表示が
零射になることを示す（全空間 Quasicategory、底の零射構造）。
`leftFibrationInitialFiberPiZeroEquiv_map_eq_zero` は同じ底上の関手の元に零像を持つ始対象がある場合、
その fiber の像全体の Hom 表示が零射となることを示す
（全空間二つ・底 Quasicategory、標的射が left fibration、標的の始対象、元の始対象と零像）。
`spanFold` と両枝の式は、対称 span の二枝を同じ標準辺へ畳む。
`spanFold_edgeSpan` は同じ二枝の図式が畳み込みによる引き戻しであることを示す。
`symmetricSpanFoldCoslice`・`symmetricCoconeFold` はこの形状の制限を
元の対称 span の図式表示のまま余錐・終点固定余錐空間へ移す。
通常の制限との一致・射影・uncurry・両枝への恒等式、自己引き戻し表示での対角との一致を証明した。
`symmetricCoconeLoopUnit_eq_fold` は対角から得た単位が畳んだ枝の基点の成分であることを示す
（これらの畳み込みと単位の表示に充填性や零対象性は不要）。
`edgeTerminalCocone_vertex` は辺の終点余錐の頂点の厳密な式。
`coconeMappingSpacePiZeroEquiv_fold_eq_zero` は枝の終点が零対象なら、畳んだ辺の余錐の像全体の
全体の Hom 表示が零射になることを示す。
`symmetricCoconeLoopUnit_hom_eq_zero` はループ単位が Hom 表示で零射となることを示す。
仮定は X Quasicategory、h X の零射構造、枝の零終点、指定した全体の余極限余錐であり、安定性全体は不要。
零対象を経由する因子分解には辺の終点余錐の始対象性を用いた。
`leftFibrationInitialVertexHom_edge` と `_FiberPiZeroEquiv_edge` は、二つの fiber 頂点を結ぶ辺の像を
Hom 表示の後合成として読む。`LeftFibrationFiberTransport.piZero_inclusion` は輸送前後の全空間での
連結成分が同じになることを示す。`kernelPairFiberTransport_hom` は自己引き戻しの第二射影の輸送を
第一射影へ送り、固定した始対象による Hom 表示が底の辺との後合成で変わることを示す。
`kanKernelPairPiZeroLoopEquiv_basepoint` はこれと始対象変更を組み合わせ、
異なる基点のループ表示を基点間の辺の底への像で結ぶ共役の可換式を証明する
（Kan fibration、E 可縮な Kan、B Kan）。
`kanKernelPairLoopProduct_basepoint` は共役が合成を保つことから積の基点独立性を証明し、
`symmetricCoconeLoopProduct_basepoint` は全体の余錐空間への適用。
`symmetricCoconeLoopProduct_transport_basepoints` により、両端の枝の基点を自由に選んでも積の輸送が可換になる。
`symmetricCoconeHomProduct` は全体の余錐の Hom 表示へループ積を移した演算。
基点独立性、零射の左右単位、二枝交換の頂点自己同型による前合成が右逆元になる式を証明した。
`symmetricCoconeHomProduct_naturality` は任意の頂点間の h X の射による後合成への自然性を、
辺の代表元と整合する三つの輸送から証明する（Quasicategory、枝の零終点、全体の余極限余錐）。
`representableOperation_eq_add_of_surjective_objects` は全射的な対象表示の上の自然な零単位演算が
既存の前加法圏の加法と一致する一般補題。双積の対象の表示を一つ選び、二射影と余対角で計算する。
対象の表示を大域的に選んで新しい圏を作り直すことはしない。
`symmetricCoconeHomProduct_eq_add` は安定な X の全対象の頂点表示、二項双積、
既存の preadditive_ho を用い、Hom に移したループ演算と構成済みの加法の一致を証明する。
`fixedCoconeSwap_eq_neg_id` は恒等射の右逆元の式にこれを適用し、対称 span の交換を負の恒等射に同定する。
`fixedCoconeSwap_eq_neg_id_of_diagram_eq` は等しい図式の表示へ適用し、
`chosenSymmetricSuspensionSquare_swapIso_eq_neg_id` で対称な懸垂模型の swapIso に照合する。
`SuspensionSquare.swapIso_eq_neg_id` は既存の選択変更の可換性により任意の懸垂四角形へ移す。
**懸垂の二枝交換と負の恒等射の一致は完成**（Quasicategory、IsStable、追加の対称性の仮定なし）。
`pastingOuterToRightHomotopy` は回転長方形の外側から右面への変形を構成し、
始点の道は左面の下辺、終点は固定される（値域への追加仮定なし）。
`CofiberRotationRectangle.suspensionComparison` はこれに二回目の回転比較の転置を合成する。
始点成分は元の第一射を等号で輸送した射、終点成分は回転後の接続射である。
`SuspensionSquare.ambientHom_target` は四角形の関手圏の h の任意の射について、
懸垂間の終点成分が指定始点の射を suspensionFunctor で送ったものになると示す
（Quasicategory、IsStable、始点成分の式）。全部分圏からの持ち上げを追加入力しない。
`SuspensionSquare.transpose_objIso_inv` は転置した懸垂の対象比較の逆射が元の逆射の負号となる式。
`CofiberRotationRectangle.connecting_eq_neg_suspension` はこれらを合わせ、
回転後の接続射を懸垂対象の比較と始点の等号輸送を通して -Σf に同定する。
仮定は Quasicategory、IsStable と指定回転長方形であり、元の列の cofiber 性は長方形の存在に使う。
**回転第三接続射の負号と TR2 は完成**。
`CofiberRotationRectangle.triangleIsoRotate` は回転長方形の右面の cofiber 三角形と
元の三角形の順回転の実際の同型であり、第三射には証明済みの負のシフトを使う。
`exists_cofiberPredecessor` は反対圏での回転を双対化して戻し、
元の第一辺を第二辺に持つ cofiber 列を、単体的な辺の厳密な一致付きで構成する。
`cofiberTriangleIsoOfFunctorIso` と `nonempty_cofiberTriangleIso_of_bottom_eq` は
図式同型を接続射とシフトを含む三角形同型へ移す。
`exists_cofiberTriangle_rotate_iso` により任意の cofiber 三角形を別の cofiber 三角形の順回転で表示し、
`cofiberTriangle_invRotate_mem`・`invRotate_mem_cofiberDistinguishedTriangles` で逆回転への閉性を得る。
`cofiberDistinguishedTriangles_rotate_iff` は任意の通常の Triangle の distinguished 性と
その順回転の distinguished 性の同値。これらの最終的な回転の定理は Quasicategory と IsStable のみを仮定する。

2026-10-19 の検証を停止させた HomotopyLimits の循環はレーン N が解消済み。
現ソースで KanEquivalencePaths が FibrationDerivedFiberSpan を import しないことを確認した。
新規四モジュールを統合し、対象・Stable 集約ビルド（2664 jobs）、全宣言監査
（325 モジュール・2356 宣言、標準三公理のみ）、公開16宣言の正確な型抽出が成功した。
`pretriangulated_ho` は構成済みの前加法構造と整数シフトに対する Mathlib の
Pretriangulated instance。TR1・TR2・TR3 を既存の cofiberDistinguishedTriangles に対して束ねる。
`distinguishedTriangles_ho_eq` はその distinguished 集合が既存の cofiber の像の集合同士で
定義的に一致することを公開する。Quasicategory と IsStable のみを仮定する。
対象ビルド2791 jobs・集約ビルド2807 jobs、326モジュール・2360宣言の公理監査が成功した。
**Pretriangulated instance は完成**。八面体・TR4 と S4 全体も下記で完成。

TR4 の幾何学的構成を進めた。
`CofiberCompositionRectangle` と存在定理は、元の cofiber 列と合成する二射の二単体を保持し、
外側に合成射の cofiber 列を持つ押し出し長方形を構成する。
`triangleMorphism` の第一成分は恒等射、第二成分は右面の下辺、第三成分は右面の上辺となる。
これらは端点の表示を含む Arrow の等号で照合し、`connecting_comm` で接続射の可換式を得る。
`PushoutCofiberRectangle` は任意の押し出し四角形へ零終点を付加し、
外側と右面を転置した二つの cofiber 列を同時に構成する。
実際の比較ホモトピーの始点成分 `sourceHom` は左面の下辺、終点成分は恒等射である。
`connecting_comp` と `triangle_connecting_comp` は右面の接続射・第三射を、
外側の接続射・第三射と始点成分の懸垂・一回シフトとの合成として計算する。
一回シフトへの輸送は一般補題 `cofiberTriangle_mor₃_naturality` に分離した。
`CofiberOctahedronDiagram` は最初の右面の転置を第二の左面として二つの長方形を束ねる。
その存在、二つ目の元の射と最後の列の第一辺、最後の始点成分と元の第二射との Arrow の等号を証明した。
`lastTriangle_mem` は、最後の cofiber 三角形の第三射を外側の第三射と元の第二射のシフトの
合成として表示した三角形の distinguished 性である。始点の表示変更は sourceHom に保持する。
存在定理の仮定は Quasicategory、IsStable、入力 cofiber 列、第一辺と合成二単体の一致のみ。
外側の余極限・比較の選択の整合は追加入力しない。

対象ビルド2178 jobs・対象と集約ビルド2813 jobs、332モジュール・2458宣言の監査と
構成子・射影を含む公開50項目の型抽出が成功した（標準三公理のみ）。
具体的なシフト式のカーネル検査には、その定理だけ maxHeartbeats=1000000 を設定した。
合成射の cofiber から二つ目の元の射の cofiber への比較も構成した。
`CofiberOctahedronDiagram.rightToNextHomotopy` は第一長方形の右面から第二の外側の列への比較。
転置した左から外側への比較は底辺の両端を固定し、右上を第二長方形の上辺に沿って動かす。
`nextComparisonHom` は第一の外側から右面への比較とこれを関手圏の h で合成する。
その始点は元の第一射、中間は恒等射、終点は最後の列の第二射である（Arrow の等号）。
`cofiberTriangleHoMap` は関手圏の任意の h の射を cofiber 三角形の射に送り、
三成分が元の射の各角の評価に等しいことを証明する。
これを使う `nextTriangleMorphism` と `nextConnecting_comm` が第二の三角形の射と接続射の可換式。
`firstTriangle_middle_arrow`・`last_first_arrow`・`nextTriangle_source_arrow`・
`nextTriangle_middle_arrow`・`last_second_arrow` により、二つの三角形の射の成分と
三つの元の列・最後の列の射を同時に照合した。
始点や cofiber の表示変更は Arrow に保持し、型の等号を暗黙に捨てていない。
新規五モジュールの対象・集約ビルド2818 jobs、337モジュール・2496宣言の監査、
公開31宣言の universe 付き型抽出が成功した。標準三公理のみ。

**TR4 と S4 は完成**。
`OctahedronModel` は最初の二辺が指定した Arrow と等しい、六対象・三つの distinguished 三角形・
Mathlib の Octahedron を持つ模型の存在を表す。
`exists_octahedron_of_triangle_comparisons` は任意の前三角圏で、二つの三角形比較と最後の列の所属から
対象の表示を Arrow の等号で統一し、四可換式と最後の三角形の所属を備えた八面体を構成する。
この補題は八面体公理を仮定しない。
`CofiberOctahedronDiagram.octahedronModel` が二長方形に適用し、
`octahedronModel_of_morphisms` は任意の二射の辺の代表と合成二単体、第一辺の cofiber を選んで
模型を作る。模型の二辺は元の二射と端点を含めて Arrow として等しい。
`isTriangulated_of_octahedronModels` はその等号から三対象の等号同型と可換式を得て、
Mathlib の IsTriangulated.mk' を使い、任意の三つの distinguished 三角形へ同型輸送する。
`isTriangulated_ho` は Quasicategory X と IsStable X のみを仮定する八面体公理の instance。
既存の preadditive_ho、hasShift_ho、pretriangulated_ho を変更していない。
従って h C は cofiber 列の像を distinguished とする三角圏である（HA 1.1.2.14）。
対象ビルド2808 jobs、対象・Stable 集約ビルド2824 jobs、342モジュール・2504宣言の監査と
公開7宣言の universe 付き型抽出が成功した。標準三公理のみ。
**S5 は完成**。
`fiberTriangle` は fiber 列を安定性で cofiber 列とみなす三角形であり、distinguished である。
`fiberHomFunctor W` の次数 n の台は Hom(W,A[n])、射はシフトした射との後合成である。
`fiberHomConnecting` は Hom(W,C[n]) → Hom(W,A[n+1]) の準同型で、
第三射の n 回シフトと整数シフトの比較同型による評価式と、三角形の射に対する自然性を公開する。
`fiberHomSequence` は A[n]・B[n]・C[n] と次次数の三項からなる六項部分列、
`fiberHomSequence_exact` は任意の W・任意の整数 n の完全性である。
`fiberContravariantHomFunctor W` の次数 n の台は Hom(A,W[n])、射は前合成。
`fiberContravariantHomConnecting` とその評価式、反対三角形を用いる
`fiberContravariantHomSequence`・`fiberContravariantHomSequence_exact` も公開した。
反変の六項は Hom(C,W[n]) → Hom(B,W[n]) → Hom(A,W[n]) →
Hom(C,W[n+1]) → Hom(B,W[n+1]) → Hom(A,W[n+1]) である。
両側とも全 n の部分列は同じ関手・接続射を使って重なり、全ての位置の完全性を覆う。
仮定は Quasicategory X、IsStable X、入力 fiber 列のみ。有界性や compact 性は不要。
対象ビルド3051 jobs、対象・Stable 集約ビルド3067 jobs、343モジュール・2523宣言の監査、
公開17宣言の universe 付き型抽出が成功した。標準三公理のみ。

安定性から全有限極限・余極限を導く逆向きの一般論と、S6 は完全関手・h の三角関手・全整数シフトと両立する自然変換まで完成。S7 の D7 は未完了。
Core・F1・DGNerve・DoldKanComparison・HomotopyLimits は参照専用。
実装は `InfinityCategories/Stable/`、D7 は `InfinityCategories/Derived/` に置く。
引用・追加公理・sorry を使わず、各工程を対象・集約ビルドと公理監査の後に保存する。


D7 の現在地：零対象・任意の cospan の極限・全辺の fiber は構成済み。
標準 cofiber 余錐の coslice 境界を二セルに分け、既知面からのデータ回収、
零未知データの共通面の一致、後続・脚側・三角形側の全残差整合条件まで証明した。
次は最初の境界頂点が標準余錐であることから固定三角形を回収し、
cofiber Hom 座標へ残差を移して六未知成分を解く。coslice 初期性・D(S) の安定性・
D3 を通じた三角構造の一致は未完了であり、これらを既証明として使わない。

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
| S4 | `Stable/Pasting.lean`、`Stable/Triangulated.lean` | 四角形の貼り合わせ、cofiber 三角形、TR1〜TR4、Pretriangulated | 完了（貼り合わせ、TR1〜TR4、Pretriangulated・IsTriangulated instance） |
| S5 | `Stable/LongExactSequence.lean` | fiber 列に Hom を適用した長完全列 | 完了（共変・反変、全整数次数、六項部分列の完全性、接続準同型の評価式） |
| S6 | `Stable/ExactFunctor.lean` と関連モジュール | 完全関手、h の三角関手、完全関手間の自然変換 | 完了。零対象・cofiber/fiber 列・全押し出し／引き戻しの保存、CommShift ℤ、IsTriangulated、加法性、自然変換の全整数シフトとの両立・三角形の像の自然変換まで公開 |
| S7（D7） | `Derived/Stable.lean` | D(S) の安定性と D3 による通常の導来圏の三角構造との一致 | 進行中。零対象・fiber 完成、cofiber の普遍性を構成中 |

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
| 任意の h C の射を含む列 | `exists_cofiber_hoShortComplex`、`exists_fiber_hoShortComplex`（Quasicategory、IsStable） | 短複体・通常の三角形と接続射の構成は完了。TR1 と TR3 も下記で完成 |
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
| h C の整数シフト | `stableEquivalenceHasShift`（任意の圏の自己同値）、`hasShift_ho`、`shiftOneSuspensionIso`、`shiftNegOneLoopIso`（Quasicategory、IsStable） | HasShift ℤ の全整合条件と Σ・Ω との比較まで完了。加法性も下記で完成 |
| Mathlib の cofiber 三角形 | `cofiberTriangle`、三つの隣接零合成、`cofiberTriangleMapOfHomotopy`（Quasicategory、IsStable、cofiber 列） | 通常の Triangle とその射として完了 |
| distinguished 集合と TR1 の存在部分 | `cofiberDistinguishedTriangles` と同型不変性、`exists_cofiberDistinguishedTriangle`（Quasicategory、IsStable、任意の h C の射） | 集合の定義・同型不変性・厳密に指定した射を含む三角形の存在は完了。TR3 も下記で完成。可縮三角形も下記で完成。回転・八面体・Pretriangulated も下記で完成 |
| 可換正方形の図式への延長 | `exists_stableSquare_of_homMk_comm`、`exists_terminalArrowHomotopy_of_sourcePath`、`exists_cofiberSquareHomotopy_of_comm`（Quasicategory、最後は両端が cofiber 列） | 完了。入力の二つの辺の一次単体を保持 |
| TR3 | `exists_cofiberTriangleMorphism_of_comm`、`exists_cofiberDistinguishedTriangleMorphism`、`complete_cofiberDistinguishedTriangle_morphism`（Quasicategory、IsStable、指定した最初の二成分の可換正方形） | 定義済み distinguished 集合の全ての三角形について完成。Pretriangulated instance も下記で完成 |
| 一点・区間の終点余極限 | `cosliceIdentityCone_isInitialVertex`、`cosliceIdentityCone_isColimit`、`isColimitCone_of_point_constant`、`edgeTerminalCocone_isColimit`（Quasicategory のみ） | 完了。恒等射の cofiber 四角形への適用も下記で完成 |
| 恒等射の cofiber と TR1 | `squareColumnDiagram_isPushout`（Quasicategory）、`columnZeroTriangle`、`columnZeroTriangle_isCofiber`、`columnZeroTriangle_f_eq_id`（Quasicategory、HasZeroVertex）、`columnCofiberTriangleIso`、`contractibleTriangle_mem_cofiberDistinguishedTriangles`（Quasicategory、IsStable） | 可縮三角形の所属まで完了。定義済み distinguished 集合の TR1 が揃った |
| 余極限の存在の転送・貼り合わせによる長方形の構成 | `exists_colimitCocone_extension_of_trivialRestriction`、`hasColimit_iff_of_trivialRestriction`、right anodyne・余極限付加版、`exists_pastingExtension_of_outerColimit`（Quasicategory） | 指定した余錐・頂点と五頂点図式を厳密に保持して完成。零始点の押し出し四角形への適用も下記で完成。h C の二項余積は下記で完成。前加法構造も下記で完成 |
| 左四角形と底辺二単体の貼り合わせ | `pastingCornerBottom_isPushout`、`pastingCornerGlue` と制限の式（値域に仮定なし）、`exists_pushoutRectangle_of_left_and_bottom`（Quasicategory、指定した左押し出しと外側基底の余極限） | 指定した左四角形・底辺二単体・外側余錐を保持する構成まで完成。外側余錐を cofiber から与える工程も下記で完成 |
| 同値な形状・同型な図式の余極限の輸送 | `sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence`（Quasicategory、Mono、IsPrecompositionEquivalence）、`hasColimit_iff_of_functorIso`（Quasicategory、FunctorIso） | 一般の図式で完成。指定零枝を持つ span 間の同型の構成も下記で完成 |
| 指定零枝の cofiber と二項余積四角形の存在 | `nonempty_functorIso_span_of_first_eq_terminal_second`（Quasicategory）、`hasColimit_span_of_zero_second`、`exists_pushoutRectangle_of_zeroTriangle`、`exists_zeroSourcePushoutSquare`（Quasicategory、IsStable） | 指定した二頂点を持つ零始点の押し出しまで完成。h C の二項余積の普遍性・instance は下記で完成。前加法構造も下記で完成 |
| 始対象の下の図式から始対象を忘れる | `diagramNestedCosliceIso`、`sliceUnderPostcomp_trivialKanFibration_of_trivial`、`diagramNestedCosliceProjection` と射・頂点の式、`diagramNestedCosliceProjection_trivial_of_initial`（値域に仮定なし）、`isColimitCone_iff_forget_initial`（Quasicategory） | 一般の図式で完成。標準 span と離散二点図式への適用も下記で完成。h C の二項余積の普遍性は下記で完成 |
| 離散二点図式の余極限 | `spanPointJoinIso` と三頂点の包含の式、`isColimitCone_iff_restrict_joinInr_of_initial`（Quasicategory、始点の始対象性）、`binaryPointDiagram`、`hasColimit_binaryPointDiagram`（Quasicategory、IsStable） | 任意の二つの指定頂点の余極限の存在まで完成。h C の二項余積の Hom の普遍性・instance は下記で完成 |
| 二項余積の Hom の存在部分 | `JoinCocone.leg`、`legCompStruct`、`leg_comp_projection`、`binaryCoconeOfEdges` と脚・頂点の式（値域に仮定なし）、`exists_coconeVertexFactorization`、`exists_binaryColimit_desc`（Quasicategory、余極限性） | 指定された共通終域への二本の射の因子分解の存在まで完成。一意性・HasBinaryCoproducts instance も下記で完成 |
| 二項余積の Hom の一意性と instance | `coconeLegTriangle` と制限の式、`exists_binaryCoconeTriangleFamily`、`exists_binaryCoconeEdgeLift`（値域に仮定なし）、`exists_binaryCoconeEdgeLift_of_comm`、`exists_binaryCoconeHomLift`、`binaryColimit_hom_ext_to_cocone`、`binaryColimit_hom_ext`、`binaryColimit_isColimit`、`hasBinaryCoproduct_of_binaryColimit`（Quasicategory、後四者は余極限性）、`hasBinaryCoproducts_ho`（Quasicategory、IsStable） | 完成。双積性は下記で完成。前加法構造も下記で完成 |
| 安定性の自己双対性と二項積 | `spanSwapIso`、`isPushoutSquare_iff_transpose`、`sliceUnderPostcomp_isIso`、`isPushoutSquare_iff_postcomp_isIso`、`isPullbackSquare_iff_postcomp_isIso`、`dualSquare` と二つの普遍性判定（値域に仮定なし）、`isStable_op`、`exists_zeroTargetPullbackSquare`（Quasicategory、IsStable）、`homotopyOppositeEquivalence`（Quasicategory）、`hasBinaryProducts_ho`（Quasicategory、IsStable） | 完成。双積性は下記で完成。前加法構造も下記で完成 |
| 零始点の押し出しの包含の分裂列 | `exists_zeroReturnTriangle`、`exists_pushoutRectangle_of_returnTriangle`（Quasicategory）、`pastingTop_isSplitEpi_of_outer_column`（値域に仮定なし）、`exists_splitCofiberRectangle`、`exists_cofiberSequence_of_zeroSourcePushout`、`cofiberConnecting_eq_zero_of_epi`、`cofiberTriangle_mor₃_eq_zero_of_epi`、`exists_splitCofiber_of_zeroSourcePushout`（Quasicategory、IsStable） | 指定した包含・三対象の cofiber/fiber 列、第二射の切断、接続射の消滅まで完成。双積性は下記で完成。前加法構造も下記で完成 |
| 幾何学的二項余積と標準包含・射影の照合 | `squareBinaryCocone` と脚の式、`binaryCofan_isColimit_of_edge_eq`（値域に仮定なし）、`squareBinaryCocone_isColimit`、`zeroSourcePushout_isBinaryCoproduct`、`zeroSourcePushoutCoproductIso`（Quasicategory）、`zeroSourceCoproductFst`・`Snd` と四合成式（さらに零射）、`pastingTop_hom_comp`（値域に仮定なし）、`exists_pastingProjection_eq_coproductSnd`（Quasicategory、零射）、`exists_coproductCofiberSequence`（Quasicategory、IsStable） | 指定された標準射影を持つ cofiber/fiber 列まで完成。双積性は下記で完成。前加法構造も下記で完成 |
| 零 cofiber・零 fiber と比較の可逆性 | `terminalTargetPullback_isBinaryProduct`（Quasicategory）、`ZeroTriangle.isIso_f_of_zero_cofiber`・`isIso_g_of_zero_fiber`、`CofiberSquare.homMk_isIso_of_zero`・`FiberSquare.homMk_isIso_of_zero`、三対象の二つの零性からの消滅判定（Quasicategory、IsStable）、`colimitCoconeHomotopy_isInvertible_of_restriction`、`exists_pushoutSquareFunctorIso_lift_span`、`cofiberSquareComparisonIso`、`cofiberSquare_zero_iff`（Quasicategory） | 零 cofiber/fiber から同型となる向きと cofiber の零性の選択独立性が完成。逆向きも次行で完成。双積性は下記で完成。前加法構造も下記で完成 |
| 同型と零 cofiber/fiber の同値 | `cofiberSquareHomotopy_isInvertible_of_vertexPaths`、`exists_invertibleCofiberSquareHomotopy_of_comm`、`ZeroTriangle.zero_cofiber_of_isIso_bottom`、`CofiberSquare.zero_of_homMk_isIso`・`FiberSquare.zero_of_homMk_isIso`（Quasicategory）、`FiberSquare.opCofiber`（仮定なし）、`CofiberSquare.homMk_isIso_iff_zero`・`FiberSquare.homMk_isIso_iff_zero`（Quasicategory、IsStable） | 任意の指定 cofiber/fiber で完成。双積性は下記で完成。前加法構造も下記で完成 |
| 任意の四角形の双カルテジアン判定 | `exists_terminalCompositeTriangle`（Quasicategory）、`hasColimit_span_of_terminal_first`、`exists_pushoutRectangle_of_zeroEnd`、`IsStable.pullback_of_pushout_square`・`pushout_of_pullback_square`・`pullback_iff_pushout_square`（Quasicategory、IsStable） | 全四角形で完成。全有限極限・余極限の存在は未完了 |
| 分裂 cofiber 列と二項双積 | `binaryFan_isLimit_of_edge_eq`（値域の仮定なし）、`ZeroTriangle.binaryProductOfRetraction`、`zeroSourcePushout_isBinaryProduct_of_retraction`・標準射影版、`zeroSourcePushoutBinaryBiproduct`、`hasBinaryBiproducts_ho`（Quasicategory、IsStable） | 二項双積 instance まで完成。前加法構造も下記で完成 |
| h C の前加法構造 | `stableHomAddCommMonoid`、`exists_additiveInverse_of_zeroSourcePushout`、`exists_stableHom_additiveInverse`、`stableHomAddCommGroup`、`preadditive_ho`（Quasicategory、IsStable） | Hom の可換群・合成の双加法性・Preadditive instance まで完成 |
| h C の有限双積とシフトの加法性 | `hasFiniteProducts_ho`、`hasFiniteBiproducts_ho`、`suspensionFunctor_additive`、`loopFunctor_additive`、`shiftFunctor_additive_ho`（Quasicategory、IsStable） | 全有限双積・Σ・Ω・全整数シフトの加法性まで完成。∞ 圏自体の全有限極限・余極限の存在は未証明 |
| cofiber 列の回転の幾何学的構成と二射列 | `pastingLeftToOuterHomotopy`（値域の仮定なし）、`CofiberRotationRectangle` とその存在・選択（Quasicategory、IsStable）、`rotated_isCofiber`（データを入力すれば仮定なし）、`rotated_f_arrow`・`rotated_g_arrow_connecting`（Quasicategory、零射、後者は元の cofiber 性）、`tailShortComplexIso`・`exists_cofiberTailShortComplex`（Quasicategory、IsStable） | B → C → ΣA の cofiber 短複体表示まで完成。第三の接続射の負号も下記で完成。Triangle の回転所属・逆方向も下記で完成。TR2 は完了 |
| suspension の二枝交換 | `SuspensionSquare.transpose`・`transpose_transpose`・`transpose_vertex`（値域に仮定なし）、`swapIso`、`comparisonIso_hom_transpose`、`swapIso_hom_comp_self`、`diagramComparisonIso_transpose_naturality`・`swapIso_naturality`（Quasicategory） | 標準比較との両立・自然性・二乗が恒等まで完成。加法の負号との一致も下記で完成。TR2 も下記で完成 |
| 終点固定余錐空間と二枝の引き戻し | `coconeMappingSpace`、`coconeMappingSpace_kanComplex`（Quasicategory）、`coconeMappingSpace_restrict_fibration`（Quasicategory、Mono）、`coconeMappingSpace_edge_isContractibleKan`（Quasicategory、枝の終点の始対象性）、`exists_coconeMappingSpace_glue`・`coconeMappingSpace_hom_ext_of_pushout`・`spanCoconeMapping_isPullback`・`coconeMappingSpace_spanSwap_left`・`right`（値域の仮定なし） | 空間・充填性・可縮な枝・引き戻し・交換の二成分まで完成。π₀ と Hom の比較は下記で完成。ループ模型と、零終点の対称 span に対する演算と加法の一致も下記で完成 |
| 余錐空間と余極限頂点の Hom | `leftFibrationInitialFiberPiZeroEquiv`（底 Quasicategory、LeftFibration、始点の始対象性）、`coconeMappingSpacePiZeroEquiv`・`pushoutCoconeMappingSpacePiZeroEquiv`、`coconeMappingSpaceHomComparison_homotopyEquivalence`・`coconeMappingSpacePiZeroEquiv_eq_comparison`（Quasicategory、余極限性または押し出し性） | π₀ と Hom の同値・実際の比較射のホモトピー同値・二つの比較の一致まで完成。形状制限・再添字付け・二枝交換による制限余錐での Hom 表示との両立まで完成。同じ図式の余錐の変更に対する colimitVertexIso との両立も完成。選択済みの swapIso への接続とループ模型・加法との照合も下記で完成 |
| coslice の余錐比較と suspension 標準比較 | `cosliceSquareDiagramMap` と制限・評価の計算（値域の仮定なし）、`colimitSquareComparisonIso_target_arrow`、`SuspensionSquare.comparisonIso_eq_colimitVertexIso_arrow`（Quasicategory、同じ span の余極限余錐での表示）、`swapIso_eq_colimitVertexIso_arrow_of_sameSpan`（さらに転置前後の span の等号） | 同じ span の表示の下で標準比較の一致まで完成。対称な模型と転置前後の span の等号を構成済み。負号の主張を任意の選択へ転送する補題も完成。対称模型での負号そのものも下記で完成 |
| 対称 span の余錐空間の自己作用 | `fixedCosliceReindex`・`fixedCoconeMappingReindex`・`symmetricCoconeSwap` と対合・枝の交換（値域の仮定なし）、`coconeMappingSpacePiZeroEquiv_reindexFixed`・`symmetricCoconeSwap_piZero`（Quasicategory、余極限余錐）、`chosenSymmetricSuspensionSquare_reindex_swap_arrow`（Quasicategory、IsStable） | 実際の交換自己同型、二枝への作用、Hom 表示での前合成、対称模型の swapIso との同定まで完成。ループ模型と加法の負号との一致も下記で完成 |
| 可縮な枝の自己引き戻しとループ模型 | `vertexFiberι_homotopyEquivalence_of_contractible_base`（Kan fibration、Kan な全空間・可縮な底）、`kanKernelPairLoopComparison_homotopyEquivalence`（Kan fibration、E・B Kan、E 可縮、基点 e）、`kanKernelPairPiZeroLoopEquiv_fiber`、`coconeBranchKernelPairLoopComparison_homotopyEquivalence`（Quasicategory、枝の終点の始対象性、枝の余錐の基点） | 実際のホモトピー同値・π₀ の Hom 同値と固定 fiber 上の計算まで完成。交換と逆射の両立も下記で完成。零終点の対称 span に対する演算と加法の一致も下記で完成 |
| 対称 span 全体からのループ比較 | `symmetricCoconeBranches_isPullback`・`symmetricCoconeKernelPairIso`・`symmetricCoconeKernelPairIso_swap`（値域の仮定なし）、`symmetricCoconeLoopComparison_homotopyEquivalence`・`symmetricCoconePiZeroLoopEquiv_eq_comparison`（Quasicategory、辺の終点の始対象性、枝の余錐の基点） | 全体の余錐空間のループ模型への実際のホモトピー同値と、自己引き戻しへの交換作用の転送まで完成。ループの逆射との一致も下記で完成。加法の負号との一致も下記で完成 |
| 二成分・二枝交換とループの逆射 | `kanKernelPairFiberInclusion_piZero_bijective`（Kan fibration、E Kan・可縮）、`exists_kanKernelPairSwap_fiber_path`（同前）、`kanKernelPairPiZeroLoopEquiv_comp_swap`・`kanKernelPairPiZeroLoopEquiv_swap`（さらに B Kan）、`symmetricCoconePiZeroLoopEquiv_comp_swap`・`symmetricCoconePiZeroLoopEquiv_swap`（Quasicategory、枝の終点の始対象性、枝の余錐の基点） | 成分交換と二枝交換がループの逆射となることまで完成。零終点の対称 span に対する加法・懸垂交換の負号との一致も下記で完成。TR2 も下記で完成 |
| ループ積の自然性と加法の一般判定 | `kanKernelPairPiZeroLoopEquiv_naturality`（両射 Kan fibration、両全空間 Kan・可縮、両底 Kan、可換正方形）、`kanKernelPairPiZeroLoopEquiv_diagonal`・`kanKernelPairLoopProduct` と結合則・左右単位・交換右逆元・自然性（同前）、`representableOperation_eq_add`・`representableRightInverse_eq_neg`（一般の前加法圏、二項双積、演算の零単位・後合成自然性） | 自己引き戻しの π₀ 上の自然なループ積と、加法へ照合する一般補題が完成。余錐の Hom 表示に移した演算の後合成自然性・零単位の照合と適用も下記で完成 |
| 余錐空間の終点輸送と貼り合わせ | `nonempty_leftFibrationFiberTransport`（left fibration のみ）、`exists_leftFibrationFiberTransport_lift`（中間の輸送、制限射が left fibration）、`leftFibrationInitialFiberPiZeroEquiv_transport`（全空間・底 Quasicategory、left fibration、始対象）、`coconeMappingSpacePiZeroEquiv_transport`（Quasicategory、余極限余錐）、`exists_coconeEndpointTransport_restrict`（Quasicategory、Mono）、`exists_coconeEndpointTransport_glue`（二枝の区間族の整合を入力、充填性・余極限性不要） | 終点輸送の存在、単射の制限との同時可換性、Hom の後合成への対応、整合条件付きの全図式の輸送の貼り合わせまで完成。対称 span での整合条件の検証も下記で完成。基点の整合・零射の照合と加法への適用も下記で完成 |
| 対称 span 全体の輸送とループ積 | `exists_symmetricCoconeEndpointTransport`（Quasicategory、選んだ共通始点の輸送）、`symmetricCoconeTransport_kernelPair`・`_piZero`（三つの輸送と可換性、充填性不要）、`symmetricCoconeLoopProduct`・`Unit` と左右単位・交換右逆元（Quasicategory、枝の終点の始対象性、枝の基点）、`symmetricCoconeLoopProduct_transport`・`Unit_transport`（整合する輸送、終域の基点は輸送の像） | 貼り合わせ条件の実際の検証と全体の輸送、自己引き戻しへの可換性、全体の積・単位とその輸送による保存まで完成。任意の基点変更の独立性・単位と零射の照合・加法への適用も下記で完成 |
| ループ単位の零射との照合 | `leftFibrationInitialVertexHom_eq_zero_of_factor`・`leftFibrationInitialFiberPiZeroEquiv_map_eq_zero`（零像を通る因子分解、詳細は本文）、`spanFold`・`symmetricCoconeFold` と両枝・対角の式、`symmetricCoconeLoopUnit_eq_fold`（充填性不要）、`coconeMappingSpacePiZeroEquiv_fold_eq_zero`・`symmetricCoconeLoopUnit_hom_eq_zero`（Quasicategory、h X の零射、枝の零終点、全体の余極限余錐） | 単位が零射となることまで完成。積の基点独立性・Hom 上の後合成自然性の確定・加法への適用も下記で完成 |
| 基点独立性・Hom の加法・懸垂交換の負号 | `kanKernelPairPiZeroLoopEquiv_basepoint`・`kanKernelPairLoopProduct_basepoint`（Kan fibration、E 可縮な Kan、B Kan）、`symmetricCoconeHomProduct_naturality` と零単位・右逆元（Quasicategory、零終点、全体の余極限余錐。零単位・右逆元は零射構造）、`symmetricCoconeHomProduct_eq_add`・`fixedCoconeSwap_eq_neg_id`・`SuspensionSquare.swapIso_eq_neg_id`（Quasicategory、IsStable） | ループ積の基点独立性、Hom の後合成自然性・加法との一致、任意の懸垂交換と -id の一致まで完成。回転第三接続射の負号・TR2 も下記で完成 |
| 回転第三接続射の符号 | `pastingOuterToRightHomotopy` と二成分（値域の仮定なし）、`CofiberRotationRectangle.suspensionComparison` と二成分（Quasicategory、終点は零射構造）、`SuspensionSquare.ambientHom_target`・`transpose_objIso_inv`、`CofiberRotationRectangle.connecting_eq_neg_suspension`（Quasicategory、IsStable） | 対象比較と始点の等号輸送を含め、回転後の接続射が -Σf となる式まで完成。Triangle の回転所属・逆方向・TR2 も下記で完成 |
| 三角形の回転 TR2 | `CofiberRotationRectangle.triangleIsoRotate`、`exists_cofiberPredecessor`、`cofiberTriangleIsoOfFunctorIso`、`nonempty_cofiberTriangleIso_of_bottom_eq`、`rotate_mem_cofiberDistinguishedTriangles`、`invRotate_mem_cofiberDistinguishedTriangles`、`cofiberDistinguishedTriangles_rotate_iff`（Quasicategory、IsStable） | 第三射の符号を含む順回転同型、前の列、逆回転の所属、回転による所属の同値まで完成 |
| 前三角構造の公開 | `pretriangulated_ho`、`distinguishedTriangles_ho_eq`（Quasicategory、IsStable） | Mathlib の Pretriangulated instance と cofiber の像の集合との定義的一致まで完成。TR4 も下記で完成 |
| 八面体の二長方形と最後の三角形 | `CofiberCompositionRectangle` と存在・三成分・`connecting_comm`、`PushoutCofiberRectangle` と存在・`connecting_comp`・`triangle_connecting_comp`、`CofiberOctahedronDiagram` と存在・辺の式・`lastTriangle_mem`（存在と三角形の主張は Quasicategory、IsStable） | 二長方形と第一の三角形比較、最後の第三射の合成表示と distinguished 性まで完成。Mathlib の Octahedron 全体・TR4 も下記で完成 |
| 八面体の第二比較と三角形の射 | `cofiberTriangleHoMap` と三成分、`CofiberOctahedronDiagram.nextComparisonHom` と三成分、`nextTriangleMorphism`・`nextConnecting_comm`、二比較と最後の列の Arrow 照合（最終的な三角形の主張は Quasicategory、IsStable） | 第二比較と第一・第二の三角形の射の成分の照合まで完成。共通の対象表示での Octahedron の組み立て・任意の三角形への輸送・TR4 も下記で完成 |
| 八面体公理と三角構造の公開 | `OctahedronModel`、`exists_octahedron_of_triangle_comparisons`、`CofiberOctahedronDiagram.octahedronModel`、`isTriangulated_of_octahedronModels`、`octahedronModel_of_morphisms`、`isTriangulated_ho`（最終的な instance は Quasicategory、IsStable のみ） | 任意の二射と任意の三つの distinguished 三角形について八面体公理が完成。S4 は完了 |
| Hom 長完全列 | `fiberTriangle` と所属、`fiberHomFunctor`・`fiberContravariantHomFunctor` と台・射の計算、両接続準同型と評価式、`fiberHomSequence_exact`・`fiberContravariantHomSequence_exact`（Quasicategory、IsStable、fiber 列） | 両側の Hom 長完全列が全整数次数で完成。有界性・compact 性は不要 |
| 完全関手の定義と四角形の保存 | `PreservesZeroVertices`、`ZeroTriangle.map`、`IsExactFunctor`、恒等・合成の完全性、`IsExactFunctor.preservesFiber`、`isExactFunctor_of_preservesFiber`、`preservesPushoutSquare`・`preservesPullbackSquare`（後四者は始域・終域 Quasicategory、IsStable） | 完全性は零対象と cofiber 列の保存で定義。任意の四角形の保存を追加仮定せず導出済み。suspension 図式の後合成と懸垂比較自然同型も完成。整数シフトの CommShift も完成。接続射の両立と自然変換も下記で完成 |
| 完全関手と懸垂 | `squareDiagram_postcomp`、`IsExactFunctor.preservesSuspensionDiagramVertex`、`exactFunctorSuspensionDiagrams` と全角の評価式、`SuspensionSquare.map`、`exactFunctorSuspensionFamilyIso`、`exactFunctorSuspensionIso` | 全単体に自然な図式の後合成と Σ ⋙ hF ≅ hF ⋙ Σ まで完成。後二者は始域・終域 Quasicategory、IsStable、IsExactFunctor F のみ |
| 完全関手と整数シフト | `StableShiftCommutation` と群構造、`stableCommShiftOfOne`・`stableCommShiftOfOne_one`（任意の整数シフトを持つ二圏の関手と一回比較）、`exactFunctorShiftOneIso`、`exactFunctorCommShift`・`exactFunctorCommShift_one`（Quasicategory、IsStable、IsExactFunctor F） | 全整数の零・加法の整合条件を持つ CommShift ℤ と一回比較の厳密な復元まで完成。三角関手も完成。完全関手間の自然変換も下記で完成 |
| 完全関手と指定懸垂への cofiber 比較 | `squareDiagramHoEvaluation_postcomp`、`cofiberSuspensionComparisonHom_postcomp`、`cofiberConnectingToSuspension_postcomp`、`functorHomotopyEvaluation_map_app_arrow`・後合成の成分式、`functorIsoOfTrivialKanFibration_projection_arrow`・`_component_arrow`、`exactFunctorSuspensionFamilyIso_source_component_arrow` | 写した懸垂への接続射の保存と、選んだ図式比較の始点が恒等であることまで完成。Σ への接続射の両立・三角関手も完成。完全関手間の自然変換も下記で完成 |
| 完全関手が誘導する三角関手 | `exactFunctorSuspensionIso_comp_objIso`・逆射版、`cofiberConnecting_postcomp`、`exactFunctor_map_cofiberTriangle_mor₃`、`exactFunctorCofiberTriangleIso`、`exactFunctor_isTriangulated`、`exactFunctor_additive`（Quasicategory、IsStable、IsExactFunctor F、cofiber 比較には指定 cofiber 列） | 接続射・第三射の保存、cofiber 三角形の像の同型、Mathlib の三角関手と加法性まで完成。完全関手間の自然変換も下記で完成。D7 は未完了 |
| 完全関手間の自然変換 | `homotopyNatTransOfEndpoints_precomp_app_arrow`、`stableShiftCommutationNeg_naturality`・`stableNatTransCommShiftOfOne`、`exactFunctorNatTrans`・接続射の自然性・`exactFunctorNatTrans_suspension_comm`・`exactFunctorNatTrans_commShift`・`exactFunctorNatTransTriangle` | 任意の単体的自然変換 H に対する h の自然変換、全整数シフトとの両立、三角形の像の間の自然変換まで完成。H の成分の可逆性は不要。S6 は完了 |
| D7 の零対象・fiber の存在 | `derivedInfinityZeroVertex_isZeroVertex`、`derivedInfinityCategory_hasZeroVertex`、`derivedCospanPresentation`・各頂点の所属、`derivedCospanFiberSquare` と普遍性・cospan 一致、`derivedInfinityCategory_hasLimit_cospan`、`derivedInfinityCategory_fiber_exists`（任意の可換環） | IsStable を仮定せず実際の零頂点・cospan 極限・全辺の fiber 四角形を構成済み。cofiber と安定性は未完了 |
| D7 の cofiber の全次数座標と標準四角形 | `cofiberHomCoordinates` と二成分・逆写像・`symm_differential`、`cofiberDifference`・`pushoutCofiber` と二包含、`pushoutHomotopy_differential`、`standardCofiberSquare` と二三角形・四辺、`standardCofiberCocone`（任意の可換環と非有界複体） | 全次数の座標・微分・符号・標準余錐を構成済み。`IsColimitCone`／`IsPushoutSquare` はまだ主張せず、coslice の境界充填が未完了 |
| D7 の span の join と coslice 境界 | 正規化した `cofiberJoinStdSimplexIso` と包含式、`spanJoinLeft`・`spanJoinRight`・`spanJoin_isPushout`、両セルの可変面の式、`cosliceBoundary_first_cocone`・`cosliceJoinBoundaryFaces_fixed`・`sliceUnderCurry_boundary_of_joinFaces`（値域の充填性は不要） | 二セルの pushout、全可変面、指定最初の余錐の回収、全 join 面からの coslice 境界充填への変換まで完成。dg nerve の未知成分・残差方程式の解は未完了 |
| D7 の span 境界データと未知集合 | `spanSuffixFaces`・被覆と既知成分の判定、`spanUnknown_cases`、`spanBoundaryLeft`・`spanBoundaryRight` と面の復元、`spanBoundaryLeftData`・`spanBoundaryRightData` と既知面・既知方程式（任意の可換環・dg 圏、任意の次元） | 境界から左右の候補を組み立て、未知集合を各四種類に分類。後続全頂点を含まない集合の方程式は境界から従う。未知成分を解くことは未完了。零未知データの共通面は下記で一致を証明済み |
| D7 の共通面と最初の残差整合 | `spanBoundaryLeftZeroData`・`spanBoundaryRightZeroData` と未知成分の零、`spanCommonFaces` と像・面合成式、`spanBoundaryZeroData_common`、`differential_rhs_spanSuffix` と境界データへの適用、`differential_rhs_span_onePrefix_single`（任意の可換環・dg 圏） | 零未知データの共通面の一致、可変頂点集合の右辺の閉性、固定一点追加の Bianchi が余錐頂点の単一寄与となることを証明済み。脚側の寄与の展開・符号は下記で完成。二固定点追加の残差も下記で完成。未知成分の可解性と cofiber の普遍性は未完了 |
| D7 の脚側の符号付き残差条件 | `spanSuffix_insert_leftCut`・`rightCut`・`sign`、`differential_rhs_span_onePrefix`、`spanSuffixHom`・`Rhs`・`Residual`、`spanOnePrefixRhs_differential`・`of_suffix_zero`、左右の `ZeroData_onePrefix_differential`、共通対象・右辺の比較（任意の可換環・dg 圏、全次元） | 脚側右辺の微分は後続残差と脚の合成の (-1)^(n+1) 倍の負。零未知データでは後続右辺と脚の符号付き合成。左右の全可変対象・始点 A・共通右辺も比較済み。二固定点追加の方程式の微分は下記で完成。六成分の解は未完了 |
| D7 の三角形側残差と二寄与 | `spanUniv_*` の切断・削除・符号、`differential_rhs_span_twoPrefix_pair`、二寄与の展開、`differential_rhs_span_twoPrefix`・`of_unknown_zero`、`spanTwoPrefixRhs`・`FirstRhs`、`spanTwoPrefixRhs_differential_of_unknown_zero_normalized`、左右の `ZeroData_twoPrefix_differential`（任意の可換環・dg 圏、全次元） | 一般の境界の残差整合条件が揃った。三角形側の微分は (-1)^(n+1) を共通係数として、後続右辺と三角形成分の合成、A 側右辺、脚側右辺と脚の合成の負の三項。標準 cofiber の座標への移送・六成分の解・coslice 初期性は未完了 |
| S7 | D7 | 零対象・任意の cospan の極限・全ての指定辺の fiber の存在まで完成。cofiber の普遍性・安定性・三角構造の比較は未完了 |

正確な公開型と構造体の構成子は [型一覧](archive/infinity-core-stable-log.md) に記録する。

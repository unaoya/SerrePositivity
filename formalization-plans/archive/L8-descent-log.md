# L8-descent の記録（2026-10-19 に本文から移動）

## 1. 目的と現在地

作成日：2026-10-18。
レーン名：K-L8（論文 §3 の降下）。
正本は [KST 経路](stage-i/kst-lanes/k-theory-kst-route.md)。
基盤の正本は [foundations](stage-i/infinity-lanes/foundations.md)。
特に KST 経路 §2.2、§3、§5 E、§13 の決定 4・5 を優先する。
本計画は L8 の設計、工程、現在地、宣言の対応を管理する。
実施の経緯はコミットメッセージに記録する。
現在の判断（§100–101）：§100 の提案 1–7 は 2026-10-19 に承認され、正本 §13 決定 15 に記録された。
主経路と条件付き補助を分離し、L9 の実 Tot への乗せ替えを開始する。
既存56モジュールは内容を変更せず、比較用補助として保持する。

状態：L8a の次数付き前層、指定比較、図式上の transfer による比較の retract、
有理不変部分の完全性とホモロジー保存、底変換後の Čech nerve の分裂を実装。
公理 (3) の幾何学的な型と不変性の法則の型、抽象 blowup の幾何データ、
指定制限写像と境界を持つ長完全列の比較、有限次元の真閉部分の次元低下を実装。
有限個の一致場所の和の真閉性・次元低下と、G 同変な長完全列の不変部分を実装。
一致場所を台とする被約閉中心を有限型の圏内で構成し、次元低下を実際の中心へ移した。
被約閉中心の引き戻しの実際の Cartesian 正方形を構成した。
アフィン Noether の reduction の核の冪零性と、公理 (3) による比較を証明した。
一般の reduction の普遍性・関手性と、その包含の自然性を証明した。
有限型の圏内にも reduction 関手を構成し、Noether 基底上で公理 (3) から
全次数の降下比較とその reduction の比較の同値を証明した。
有限個の切断の非交和からの有限・固有な軌道射と、コピーの G 置換作用を構成した。
被約化への軌道射の有限性・同変性と、明示した像の被覆条件からの全射性を証明した。
一致中心の外の制限切断の像の互いに素と、被約な終域の有限閉被覆の非交和同型を証明した。
有限非交和と開制限の標準同型で軌道射そのものの開制限の同型性へ接続した。
有限型の圏内の軌道射と、基底の一致中心を引き戻した中心による実際の抽象 blowup を構成した。
この軌道正方形の四頂点の G 作用と四辺の同変性も有限型の圏内で構成した。
前層の指定制限と差の同変性を証明し、境界の同変性を入力する長完全列への接続を実装した。
境界が幾何正方形の射に関して自然な列の接続データを型にし、そこから境界の同変性を導いた。
軌道正方形から基底の恒等中心正方形への同変立方体を構成し、
中項・例外部分の固定比較から実際の指定 PiDescent を得る軌道判定を証明した。
実際の軌道のコピーの包含・fold と、有限型の圏内の非交和の普遍性を証明した。
コピーの積を保つ前層について (3.8) の指定対角比較を幾何的な fold へ接続し、
中心上の降下から実際の中項の固定比較を導いた。
例外部分を Z のコピーの非交和として有限型の圏内で構成し、既存の作用が添字を置換することを証明した。
自然な blowup 列とコピーの有限積保存のもとで、中心上の降下だけから
実際の軌道段階の全次数 PiDescent を得る定理を証明した。
Noether な終域への全射閉埋め込みの冪零性と、Noether な対象への底変換後の冪零性を証明した。
公理 (3) から、冪零な基底変更の前後の全次数降下の同値を証明した。
基底を固定した始域だけの被約化の比較も証明し、被約化した中心上の降下を
実際の非被約な中心の軌道段階へ移した。
一つの切断の移動から、重複を除いた有限・非空・推移的な添字と相異なる族を構成した。
この族の一致中心での次元低下と、基礎点のファイバーの推移性からの像の被覆を証明した。
既存の環論的な幾何的推移性から通常の点のファイバーの推移性を導き、
切断を持つ有限型アフィン対象の実際の移動切断の被覆へ接続した。
任意の A 代数 B への係数拡大で、既存の幾何的推移性が保存されることを証明した。
基底変更後のアフィン対象の被覆、および基底を固定した始域の被約化での点の推移性を証明した。
被約な基底では元の切断を始域の被約化へ持ち上げ、実際の移動切断の被覆へ接続した。
任意の閉中心への実際の引き戻しに切断・点の推移性・被約化後の被覆を移し、
構成済みの orbitCenterAction と実際の中心の射影へ直接接続した。
二つの閉部分の被覆を実際の抽象 blowup 正方形とし、自然な列のデータから
閉和の境界を含む全次数列を得る構成も実装した。
閉被覆を始域へ引き戻した二つの閉部分と交わりから、元の閉被覆への実際の比較立方体を構成した。
四頂点の群作用と立方体の同変性を証明し、自然な列の有理不変部分を比較した。
二つの閉部分と実際の交わりの指定 PiDescent から元の射の全次数 PiDescent を導く閉和の貼り合わせを証明した。
既約成分を同じ基底上の整な有限型閉部分スキームとして構成し、Noether の場合の有限閉被覆を証明した。
一成分と残りの被約閉和に分け、実際の交わりの次元低下を証明した。
残りを他の元の整成分からの実際の閉埋め込みで覆い、その被覆の成分数が一つ減ることを証明した。
閉和の交わりの指定比較へ元の切断と点の推移性を移し、両側の被約化後の移動切断による被覆を証明した。
被約化が切断・点の推移性・次元を保つことと、同型射・空の基底の全次数降下も証明した。
厳密に低い次元に限った帰納仮定から、整な基底の軌道段階を閉じた。
中心の切断・推移性・被覆・次元低下を実際に供給し、Noether 性と公理 (3) で始域の被約性も外した。
零より低い次元に対する帰納仮定は、空の基底の降下から証明した。
残り自身の既約成分数の厳密な減少を証明し、内側の成分数の強い帰納を完了した。
外側の次元上界の帰納も実行し、切断を持つ射の全次数 PiDescent を低次元の仮定なしで証明した。
環の分裂から固定した S 上の切断を構成し、分裂する底変換と自己底変換の
テンソル積モデルに同じ L の全次数降下を適用した。
テンソル積の指定二射影の実際の Cartesian 性と、右射影の同変性を証明した。
この二射影・作用・切断を同じ S 上の有限型の圏内にも構成し、
その Cartesian 性と指定第一射影の全次数降下を証明した。
Noether 基底上の有限型の圏に有限極限を構成し、実際の Čech nerve・各段での
底変換の関手・二重 Čech 図式と元の前層による像を構成した。
各非増強段の底変換に実際の切断と extra degeneracy を構成した。
Cartesian モデルと指定引き戻しの標準同型の同変性を証明し、アフィン底変換の
指定 pullbackAction に関する全次数降下を実際の第一射影へ移した。
Čech 各段のファイバーの作用の外側の単体射との同変性と、
元の前層の全次数の指定不変比較の自然性を証明した。
有限型の圏の包含の有限極限保存とスキームへの忘却の有限連結極限保存を証明した。
実際のアフィン Čech 各段と底変換の始域のアフィン性・S 上の分離性を証明した。
局所 Noether 基底では、各段の有限次元上界も実際の構造射から供給した。
元の環論的な幾何的推移性から任意のアフィン基底変更の点の推移性を導き、
元の有限型の圏内の指定作用と、実際の Čech 各段へ移した。
切断・推移性・分離性・次元上界を全て供給し、実際の各段の全次数降下を証明した。
増強 Čech nerve の右随伴性から実際の底変換比較を証明した。
恒等射の Čech の定数図式との自然同型、および実際の二重 Čech 全体の
軸交換の自然同型を構成した。値域の Tot の Fubini は引き続き未完である。
同じ基底上の平行な Čech 細分比較の間の実際の単体ホモトピーを構成した。
相互細分の指定比較は両側のホモトピー逆を持ち、元の前層の像にもホモトピーを移した。
元の前層の実際の底変換から自然な pullback を構成し、自然な transfer と局所 rank 公式から
基底の値を含む指定 Čech 増強比較の retract を構成した（§44）。
底変換された係数図式を実際の底変換被覆の Čech 図式と自然同型で結び、
増強先を含む矢の圏の同型から、実際の底変換被覆を使う transfer 還元を得た（§45）。
元の値域の線形性なしでも、実際の図式関手の像に対する観測後の rank 公式から
全次数ごとに transfer を正規化する経路を構成した（§46）。
有限全射の実際の strict transform の有限性・全射性を証明し、局所 Noether 基底で
実際の構造射が平坦なら有限忠実平坦な細分を取り出した（§47）。
この図式を同じ有限型の圏へ持ち上げ、底変換した元の被覆への Čech 細分比較と、
実際の blowup の抽象 blowup 正方形を構成した（§48）。
基底の生成点の持ち上げから全射な被約既約成分を選び、その成分の平坦化後の
有限忠実平坦被覆を元の有限全射の底変換へ細分する射を構成した（§49）。
Noether 整域上の有限加群の非零元による自由化を証明し、実際の全チャートで純変換を
平坦にする中心の存在に必要だった境界外の平坦性を供給した（§50）。
加群純変換を実際の商代数と同定し、その Spec を基本開のスキーム論的像に
閉包含と構造射を保つ同型で結び、全チャートのその像の有限平坦性を証明した（§51）。
像と開底変換の両立から global strict transform の開チャートを周辺チャートの像で表示し、
その構造射を保つ同型と Zariski 局所性で平坦性を貼り合わせた（§52）。
非零因子の境界基本開の逆像の実際の blowup 上の稠密性を証明し、中心補集合と
同一視せず、平坦化で使う同じ D(r) の全射性と有限忠実平坦な細分へ接続した（§53）。
テンソル積の Spec と実際の周辺チャートを同定し、二つの基底への構造射と
同じ境界元の基本開を保つことを証明した（§54）。
その周辺同型で実際の像を移し、同じ境界の純変換加群の平坦性から
元の strict transform の実際のチャートの平坦性を導いた（§55）。
元のアフィンスキームの全切断環による表示を保持し、全標準チャートの貼り合わせから
有限射の真閉平坦化中心の存在を証明した（§56）。有限全射には同じ有限型の圏内で
blowup 後の有限忠実平坦細分を構成した。アフィンの場合の幾何入力であり、降下定理は未完。
さらに実際の blowup の既約性からその細分の正の定 rank を導き、
同じ抽象 blowup 正方形の中心の次元低下とまとめた（§57）。
一般の有限忠実平坦有限表示射にも有限な定 rank の開被覆を構成した。
定 rank とは別に、実際の有限自由な基本開自明化と正の有限基底を証明し、
元のアフィン射の表示・実際の有限開被覆・Cartesian チャートへ接続した（§58）。
一般の基底でも実際の有限自由チャートを各点で構成し、準コンパクト性で有限被覆を得た。
全ての四辺を元の有限型の圏へ持ち上げ、指定引き戻しとの同型と二射影の保存も証明した（§59）。
自由チャートの任意のアフィン底変換の Cartesian 性と同じ rank、選んだ基底の
係数写像への自然性と反復底変換の標準同型との整合性を証明した（§60）。
有理化での持ち上げから分母・ねじれを消す一般補題と、指定 PiDescent・自然な比較データ
から整数群の不変類の正整数倍を同じ写像で持ち上げる比較補題を証明した（§61）。
これは K0・T2 の比較データの存在や (3.6) の証明を代替しない。
異なる二つの射の混合二重 Čech と軸交換の自然同型を構成し、
細分射から各行の分裂・元の前層の像の収縮ホモトピーを得た（§62）。
実際のアフィン平坦化の低次元中心・正の定 rank の有限平坦細分にも同じ分裂を接続した。
抽象 blowup 正方形の任意の底変換と比較立方体を構成し、全側面の Cartesian 性と
例外部分の指定底変換との同型・二射影の保存を証明した（§63）。
指定底変換と抽象 blowup の正方形の族を関手にし、元の正方形への比較立方体を自然変換にした。
圏の選択された pullback との自然同型を増強先を保って混合 Čech と元の前層の像へ移した（§64）。
抽象 blowup の四頂点の列を元の被覆の実際の底変換の Čech nerve と自然同定し、
指定増強を保つ増強単体対象の同型へまとめた（§65）。
任意のスキームおよび元の有限型の圏の底変換へ、元の環論的な幾何的推移性から
点のファイバーの推移性を供給した。有限アフィン被覆の次元上界を貼り合わせ、
一般の有限型対象と実際の一般の Čech 各段の有限次元性も証明した（§66）。
非アフィンな基底への分裂した指定底変換を、同じ前層の全次数降下へ接続した。
抽象 blowup の三つの非自明な頂点の分離性も基底の分離性から導いた（§67）。
自己準同型の局所化比較から中心台を恒等射の冪ねじれ・有限生成イデアル冪で判定し、
中心を逆にした後の閉台の空性と実際の可換係数の有限射影複体の零対象性も証明した（§68）。
中心局所化の共通核を既存の scalarSupported の部分圏と同定し、
元の圏への忘却と局所化に可換な係数変更への自然性を保つ加法的な線形圏同値を構成した（§69）。
単体的重みつき錐空間の Fubini を実際の右随伴の自然同型として証明した。
積添字と反復した射影的模型の Quillen 随伴から外重みの cofibrancy を導き、
既存の二つのホモトピー錐の重みの外積にも可縮な指定増強を構成した（§70）。
任意の cofibrant な可縮重みが実際のホモトピー極限を計算することを導来随伴で証明し、
積添字の実際のホモトピー極限を共通 fibrant 置換後の反復錐空間と自然同定した（§71）。
各行・外側を独立に置換する指定比較の弱同値と、共通置換を外す比較を構成し、
単体集合の実際の積添字と反復ホモトピー極限の自然同型を得た（§72）。
指定増強との整合性と、Sp 内の Tot への実現は別工程である。
重みつき Fubini の指定同型が錐の随伴像・単位・余単位を保つこと、
導来定数比較が指定重み増強と可換し、指定増強の随伴像を計算することも証明した（§73）。
随伴と計算同型を同じ指定導来データから構成するよう正規化し、
実際の計算同型と重み変更の合成同型そのものが指定増強の像を保つことを証明した（§74）。
増強つき図式の圏上の指定比較を自然変換とし、その弱同値による実際の降下条件が
cofibrant な可縮重みの変更で不変であることを証明した（§75）。
外重みの指定増強を二段の指定増強と結合子で同定し、
重みつき Fubini が反復した指定比較と図式全体で可換することを証明した（§76）。
構成済みの実際の導来 Fubini 全体が指定増強と可換することを証明し、
積添字と直接構成した反復指定比較の弱同値による降下条件を同値にした（§77）。
各行の指定比較を自然に束ね、反復指定比較が各行の比較の後の外側比較に一致することと、
その表示での実際の降下条件の同値も証明した（§78）。
各行の増強元が変わる二重増強図式を構成し、各行と外側の実際の降下から
積添字の実際の指定降下を証明した。局所化データを内部構成する入口も持つ（§79）。
`Theorem31.lean` では (3.8) と中心上の帰納仮定による代数的な軌道貼り合わせを証明。
正本 D7 に従う導来値域への実現の型を §19 に明示する。
検証状態：`lake build SerrePositivity.KST.Descent` が成功。
元の前層と実際の底変換後の前層から、指定増強を保つ空間図式への実際の関手を構成した。
前層の transfer retract から実際のホモトピー比較の降下を戻せる（§80）。
添字随伴の実際の局所化と、左随伴な添字への制限による実際のホモトピー極限の自然同型を構成した（§81）。
指定増強との可換式と分裂余単体対象への適用は次工程。
最小元を保つ有限非空順序の圏と、自由な最小元の付加・忘却の実際の随伴を構成した（§82）。
切断を持つ射の Čech nerve を最小元を保つ添字全体へ実際に拡張し、指定増強と空座標の基底同型も保持した（§83）。
始対象での指定成分による実際の降下の判定を証明し、切断を持つ Čech の拡張側の実降下を証明した（§84）。
指定増強を保持する添字変更による実降下の同値を証明し、切断を持つ射の元の Čech の実降下まで接続した（§85）。
これは明示した SSet 模型の仮定の下での universe 0 の空間値前層についての証明であり、Sp の実現は別工程。
実際の底変換 Čech と transfer の空間図式を指定増強ごと同定し、自然な正 rank の transfer から元の実 Čech 降下を証明した（§86）。
混合二重 Čech を元の前層の実際の二重増強空間図式にし、全行の実降下から外側の実降下を反映した（§87）。
細分射が与える側の各行の実降下も分裂定理から内部で証明した。
混合二重 Čech の空間の軸交換が指定増強を保つことを証明し、他方向の全行の実降下から細分による元の実降下の反映を証明した（§88）。
自然な transfer を任意の基底変更へ実際に制限し、同じ rank 公式と全基底変更での実 Čech 降下を証明した（§89）。
細分射がない場合の基底上の実降下の局所性と、前層の射の局所的な弱同値の反映を証明した（§90）。
各点で弱同値な transfer の合成を局所化後に正規化し、実際の降下を戻す定理も証明した。
Noether 基底上の有限型の圏に任意の有限非交和とその extensive 性を構成した（§91）。
有限非交和の引き戻し成分で異なる正 rank を持つ作用の可逆性も、有限積保存から証明した。
実際の有限自由 chart を有限型の圏内の有限 Zariski 被覆に束ね、Čech の零番目の成分の異なる正 rank の検査から基底の作用の弱同値を反映した（§92）。
射影公式からの各成分の rank の式と Zariski の実降下の供給は未完の入力として明示する。
有限被覆族の各多重交叉の値の積から実際の全自然な Čech 図式と指定増強を構成し、公理 (1) の法則の型を定義した（§93）。
有限非交和の保存はこの法則から導く工程に残し、別の基本公理には加えない。
空被覆から空対象上の値の弱可縮性を導き、終対象を持つ添字圏で任意の空間の定数図式の実降下を証明した（§94）。
任意の有限添字の積が成分ごとの弱同値を保つことを、全空間の cofibrancy・二項テンソル・有限帰納から証明した（§95）。
非交和被覆の多重交叉を計算し、定数添字の列の指定対角による値の積への自然変換と元の指定増強の可換性を証明した（§96）。
公理 (1) から有限非交和の値と各成分の値の積の指定比較の弱同値を導き、実際の有限自由 chart の rank 検査も被覆族の実降下から直接得た（§97）。
この入口は有限積保存・別の単一被覆射の降下を前提にせず、局所 rank の式だけを射影公式からの未完の入力に残す。
被覆族の指定降下を Over へ移し、同じ有限 chart の正 rank の式から Over の全対象の合成の弱同値と元の実 Čech 降下を証明した（§98）。
射影公式からの局所 rank の式は明示した入力に残し、最小公理 (4) 全体の実現の完成とは区別する。
底変換した transfer の合成が元の合成の制限と一致することから、同じ局所 rank の式による全底変換の実降下と、持ち上げのある細分先の実降下を証明した（§99）。
監査状態：`scripts/audit_kst_descent.lean` は 251 モジュール・2627 宣言を検査し成功。
許容公理は標準三公理のみ。主定理や八つの公理の完成を意味しない。
切断を持つ射の帰納の区切りとして、全体ビルド `lake build` も成功（9418 ジョブ）。
終了コードは `set -eo pipefail` で確認。ログは `/tmp/l8-sectioned-full-build.log`。
§38 の Čech 図式の区切りでの全体ビルドは、所有範囲外の
`KST/ProExcision/LinearizedTensor.lean` の 110 行・104 行・140 行のエラーで失敗。
ログは `/tmp/l8-finite-type-cech-full-build.log`、終了コード 1 を確認した。
L8 の対象ビルドと監査は成功しており、import 閉包の破損ではない。
今回の §40 の幾何条件の区切りの全体ビルドは成功（9756 ジョブ）。
`set -eo pipefail` で終了コード 0 を確認し、ログは `/tmp/l8-cech-geometry-full-build.log`。
§41 の全体ビルドはルート集約で失敗。`InfinityCategories/F1/CocartesianPath` の import が
`InfinityCategories/Core/CocartesianPathVertices` と `cocartesianPathVertex._proof_1` を重複登録する。
所有範囲外の衝突で、L8 の対象ビルドと監査は成功したままである。
§45 の transfer 幾何接続の区切りでは全体ビルドが成功（10024 ジョブ）。
`set -eo pipefail` で終了コード 0 を確認。ログは `/tmp/l8-cech-transfer-geometry-full-build.log`。
§48 の strict transform の有限平坦細分の幾何接続でも全体ビルドが成功（10100 ジョブ）。
`set -eo pipefail` で終了コード 0 を確認。ログは `/tmp/l8-strict-transform-refinement-full-build.log`。
終了コード 1 を確認し、ログは `/tmp/l8-affine-cech-descent-full-build.log`。
§42 の全体ビルドも同じ所有範囲外の宣言重複でルート集約に失敗（終了コード 1）。
ログは `/tmp/l8-double-cech-comparison-full-build.log`。L8 の対象ビルド・監査は成功。
L8a 全体の完成とは区別する。
L8b の切断を持つ射について「整 → 被約 → 一般」の帰納を完了した。
自然な列・有限積保存・冪零不変性を明示的に入力する条件付きの段階である。
実際の軌道正方形は構成済み。前層の実降下・Čech 還元とは未接続。
L8c の基本幾何補題を実装。有限型スキームの有限次元上界との接続は残る。
L8d の (3.6) は K0・T2 への明示的な引数として設計する。
L8e の E への接続は外部レーンの成果を使う。
未完成の命題を `sorry` や新しい公理で埋めない。
標準三公理だけの監査通過を、数学的な工程の完成と取り違えない。

## 17. 主要宣言の表

| 宣言（§99） | 内容 | 状態 |
| --- | --- | --- |
| `BaseChangeTransfer.baseChange_composite`、`_app`、`_weak` | 底変換後の自然な合成と元の合成の制限の指定一致・弱同値の移送 | rank や加法性を使わない |
| `BaseChangeTransfer.cechDescent_everyBaseChange_of_rankCharts`、`_of_finiteFreeChartRanks` | 元の有限 chart の局所式から全底変換の指定 Čech 降下 | 底変換ごとの別の降下を仮定しない |
| `BaseChangeTransfer.cechDescent_of_rankCharts_of_lift`、`_of_finiteFreeChartRanks_of_lift` | 持ち上げのある細分先の指定 Čech 降下 | 実際の底変換の切断を内部構成 |

| 宣言（§98） | 内容 | 状態 |
| --- | --- | --- |
| `familyCechTermFunctorIso`、`_naturality`、`_inv_naturality` | 有限 wide pullback を保つ関手による各段の指定同型と単体自然性 | 終対象保存は要求しない |
| `familyCechFunctorSpaceIso`、`familyOverPresheafSpaceIso` | 関手による像と元の前層の増強つき図式の同型、Over への移送 | 指定増強を保持 |
| `FiniteTypeZariskiCover.baseChange`、`.baseChangeOverProjection` | 任意の構造射への実際の有限被覆と元の chart への Over 射 | 同じ有限添字を保持 |
| `overZariskiAction_weak_everywhere_of_fixedRankCharts` | 同じ chart の局所 rank 公式から Over の全対象で弱同値 | 自然変換の定義域を変更しない |
| `BaseChangeTransfer.cechDescent_of_weakComposite` | 自然な合成の全対象の弱同値から元の実降下 | 分裂した自己底変換と局所化後の正規化を使用 |
| `BaseChangeTransfer.cechDescent_of_rankCharts`、`.cechDescent_of_finiteFreeChartRanks` | chart ごとに異なる正 rank の合成公式から元の指定 Čech 降下 | 射影公式からの局所 rank の式は明示した入力 |

| 宣言（§97） | 内容 | 状態 |
| --- | --- | --- |
| `finiteProductRestrictionIso`、`finiteProductRestriction_weak` | 終対象の補因子を除く指定同型・弱可縮な補因子を除く弱同値 | 因子の基点や fibrancy を要求しない |
| `constantCechTupleProductIso`、`disjointFamilyCechDiagonalProjection_weak` | 定数の列の指定積同型と各段の指定対角比較の弱同値 | 空交叉の値を公理 (1) から除く |
| `finiteCoproductZariskiCover`、`zariskiFiniteCoproductComparison_weak` | 元の標準有限非交和の実被覆と元の指定比較の弱同値 | 有限非交和保存を公理 (1) から導出 |
| `familyCechPresheafMap_weak_on_base`、`finiteZariskiPresheafMap_weak_on_base` | 被覆族の全多重交叉での弱同値から基底の弱同値を反映 | 元の前層の非交和保存は不要 |
| `familyCechAction_weak_of_localPositiveRanks`、`finiteZariskiAction_weak_of_rankOverCharts` | 各交叉または各 chart 上の対象での正 rank 作用から基底を検査 | 公理 (1) を直接使用 |
| `finiteFreeChartFamilyAction_weak` | 実際の有限自由 chart の正基底の本数で検査 | 射影公式からの局所式だけを残す入口 |

| 宣言（§96） | 内容 | 状態 |
| --- | --- | --- |
| `familyCechDiagonalIso`、`_naturality`、`_inv_naturality` | 単射の同じ成分の多重交叉の指定同型と両方向の単体自然性 | 指定射影と対角から証明 |
| `disjointFamilyCech_isInitial` | 異なる成分を含む非交和被覆の実際の多重交叉は始対象 | 有限 extensive 性と始対象の厳密性を使用 |
| `familyCechDiagonalComparison`、`_augmentation` | 値の積の定数図式への自然変換と指定増強の保持 | 各次数だけの同型へ弱めない |
| `familyCechToConstantProduct` | 元の比較を左成分に持つ増強つき図式の実際の射 | 段ごとの弱同値の供給は別工程 |

| 宣言（§95） | 内容 | 状態 |
| --- | --- | --- |
| `optionProductTensorIso`、`_naturality` | Option 添字の積の指定 Cartesian テンソル分解と自然性 | 全ての射影を使う実際の同型 |
| `cechTensor_weak` | 二つの弱同値の Cartesian テンソルの弱同値 | 全空間の cofibrancy と左右の左 Quillen 性を使用 |
| `cechFiniteProduct_weak` | 任意の有限添字の積は成分ごとの弱同値を保つ | 添字の universe を制限せず元の fibrancy も不要 |

| 宣言（§94） | 内容 | 状態 |
| --- | --- | --- |
| `terminalAugmentedCechSpace_descent` | 終対象の定数図式の実際の指定降下 | 任意の添字圏で成立 |
| `cechSpaceSource_weak_of_descent_of_terminal_components` | 各段が終対象の場合に元の値の弱可縮性を反映 | 両側の実降下と成分の同型から導出 |
| `emptyFiniteTypeZariskiCover`、`emptyZariskiValue_weak` | 実際の空被覆と公理 (1) から空対象上の値への帰結 | 空対象の値の追加法則を要求しない |
| `terminalIndexAdjunction`、`constantAugmentedCechSpace_descent` | 終対象を持つ添字圏の定数図式の実際の恒等増強の降下 | fibrancy を要求せず指定添字変更で証明 |

| 宣言（§93） | 内容 | 状態 |
| --- | --- | --- |
| `familyCechTerm`、`familyCechMap` | 任意の有限被覆族の実際の多重引き戻しと添字変更 | 幾何の合成則を証明 |
| `familyCechDiagram`、`familyCechAugmentation` | 各多重交叉の値の有限積と指定比較 | 前層の非交和保存を要求しない |
| `familyAugmentedCechFunctor`、`familyCechSpace` | 前層の自然変換に関する全自然な増強つき図式 | 空間の実際の降下条件へ接続 |
| `FiniteZariskiCechDescent` | 空被覆を含む有限 Zariski 被覆族での指定降下の法則 (1) | 法則の型であり E の実現は未完 |

| 宣言（§92） | 内容 | 状態 |
| --- | --- | --- |
| `cechPresheafEndomorphism_weak_of_localPositiveRanks` | 各 Čech 段の零番目の座標の引き戻し成分の異なる正 rank から基底の作用の弱同値を反映 | 非交和の有限積保存と実 Čech 降下を使用 |
| `cechPresheafDescent_of_weakComposite`、`_of_observedWeakComposite` | 元の前層の transfer の合成の弱同値から元の実 Čech 降下へ戻す | 元の射と値域関手を全自然に写す |
| `FiniteTypeZariskiCover`、`.morphism_surjective`、`finiteFreeChartZariskiCover` | 元の有限型の圏内の有限開被覆・指定非交和射の全射性・実際の有限自由 chart の接続 | Zariski 降下の法則自体とは区別 |
| `finiteFreeChartAction_weak` | 構成済みの chart の正基底の本数で基底の作用を検査 | 射影公式からの局所 rank の式と実 Zariski 降下は明示した入力 |

| 宣言（§91） | 内容 | 状態 |
| --- | --- | --- |
| `naturalMap_isIso_of_isLimit`、`naturalEndomorphism_isIso_of_positiveRanks` | 極限保存による成分の可逆性の反映・成分ごとに異なる正 rank 作用 | 通常の有限積の計算であり Tot ではない |
| `finiteTypeCoproduct`、`finiteTypeCoproductIsColimit` | 異なる有限型対象の実際の有限非交和と指定包含の普遍性 | Noether 基底上、空の非交和を含む |
| `finiteTypeSchemes_finitaryExtensive` | 有限型の圏の有限非交和は引き戻しで安定・互いに素 | 忘却の極限・非交和保存と同型反映から導出 |
| `finiteCoproductPullbackIsColimit`、`naturalEndomorphism_isIso_of_rankOnPullbackComponents` | 非交和の任意の射による引き戻し成分の普遍性と各成分の正 rank の反映 | rank の一様性は不要 |

| 宣言（§90） | 内容 | 状態 |
| --- | --- | --- |
| `cechSpaceDescent_locality_iff`、`cechSpaceDescent_of_baseCover` | 細分射なしで両方向の各行の実降下から元の実降下を比較・反映 | 指定 Fubini と指定軸交換から証明 |
| `cechSpaceMap_left_weak_of_descent`、`cechPresheafMap_weak_on_base` | 各 Čech 段の弱同値と両側の実降下から基底の射の弱同値を反映 | 実際の比較の自然性と弱同値の合成を使用 |
| `naturalComparison_isIso_of_isoComposite`、`cechSpaceDescent_of_weakComposite` | 局所化後に transfer の合成を正規化し、元の実降下を戻す | 元の値域の加法性や厳密な retract 恒等式は不要 |

| 宣言（§89） | 内容 | 状態 |
| --- | --- | --- |
| `transferBaseChangeStageIso`、`transferBaseChangeGeometryIso` | 元の引き戻しと底変換後の二重引き戻しの指定自然同型 | 第一射影の式と全射への自然性を証明 |
| `transferBaseChangePresheafIso_pullback` | 指定前層同型は元の自然な pullback の制限と可換 | 元の第一射影の式を反変に写す |
| `BaseChangeTransfer.baseChange`、`.baseChange_rank_identity` | 元の自然な transfer の実際の制限と同じ rank 公式の保存 | 底変換後の transfer・rank 公式は追加入力不要 |
| `BaseChangeTransfer.cechDescent_everyBaseChange` | 自然な正 rank transfer を持つ射の全基底変更での実降下 | 制限した transfer と証明済みの分裂降下から導出 |

| 宣言（§88） | 内容 | 状態 |
| --- | --- | --- |
| `mixedCechSpaceSwapDiagramIso`、`mixedCechSpaceSwapIso` | 混合 Čech の反変な空間図式の全自然同型と指定増強の保持 | 幾何の逆同型の自然性と指定二射影から証明 |
| `mixedDoubleCechSpace_swap_descent_iff` | 二つの被覆と軸を交換しても実際の指定降下は同値 | 積添字の交換随伴と指定同型を使用 |
| `cechSpaceDescent_refinement_iff`、`cechSpaceDescent_of_refinement` | 他方向の全行の実降下と細分から元の実 Čech 降下を反映 | 分裂する側の各行は内部で証明 |

| 宣言（§87） | 内容 | 状態 |
| --- | --- | --- |
| `DoubleAugmentedCechDiagram.descent_iff_outer` | 各行が実降下なら積添字と外側の実降下は同値 | 外側比較の弱同値と Fubini から証明 |
| `presheafAugmentedSpaces`、`mixedCechSpaceRows`、`mixedDoubleCechSpace` | 元の前層から混合二重 Čech の実際の増強つき空間図式へ | 全行の関手と指定外側増強を保持 |
| `mixedCechSpaceRows_descent_of_refinement` | 細分する被覆上では元の被覆の各行が実降下 | 実際の切断と分裂降下から内部で証明 |
| `mixedDoubleCechSpace_descent_iff`、`_of_refinement` | 積添字の実降下と元の外側 Čech の実降下の同値 | 軸交換による他方向との比較は次工程 |

| 宣言（§86） | 内容 | 状態 |
| --- | --- | --- |
| `presheafCosimplicialSpaces` | 元の余単体添字での前層の指定空間図式の実際の関手 | 二重反対圏は指定前合成で除く |
| `cechOverPresheafSpaceIso`、`cechBaseChangedPresheafSpaceIso` | 元の Čech と実際の底変換 Čech への指定増強を保つ空間同型 | 既存の幾何・増強同型を同じ値域関手で写す |
| `BaseChangeTransfer.cechDescent_of_splitBaseChange`、`.cechDescent_of_lift` | 分裂する底変換・被覆への持ち上げから元の実 Čech 降下 | 分裂降下は証明済みの結果を使用 |
| `BaseChangeTransfer.cechDescent_of_rank` | 自然な正 rank の transfer を持つ射の実 Čech 降下 | transfer と自然な rank 公式の明示した入力下 |

| 宣言（§85） | 内容 | 状態 |
| --- | --- | --- |
| `CechReindex.weight_isCofibrant` | 元の射影的 cofibrant 重みは右随伴への前合成で cofibrant | 左 Quillen 性から証明 |
| `CechReindex.coneIso_augmentation` | 移した重みの実際の錐同型は両側の指定増強を保持 | 元の自然性と合成随伴から証明 |
| `CechReindex.computedConeComparison_augmentation`、`.descent_iff` | 独立な置換後の可換式・左随伴な添字への制限での実降下の同値 | 局所化と弱同値を内部構成 |
| `cechAugmentedPresheafSpace`、`cechAugmentedPresheafSpace_descent_of_split` | 切断の選択に依存しない元の指定 Čech 空間図式と分裂時の実降下 | SSet 模型の明示した仮定下、universe 0 |

| 宣言（§84） | 内容 | 状態 |
| --- | --- | --- |
| `initialCechConstantAdjunction`、`initialCechConeIso_augmentation` | 始対象での評価との随伴・指定錐の成分の計算 | 実際の Hom 同値と指定単位同型から証明 |
| `initialCechUnitWeight_isCofibrant` | 始対象があれば定数単位重みは射影的 cofibrant | 評価の右 Quillen 性から導出 |
| `initialCechComputedAugmentation_fac`、`cechSpaceDescent_initial_iff` | 指定置換後の比較の式・始対象の指定成分での実降下判定 | 元の図式の fibrancy は不要 |
| `splitCechAugmentedSpaceExtension_descent` | 切断を持つ Čech の拡張側の実際の降下 | 降下を仮定せず、指定基底同型から証明 |

| 宣言（§83） | 内容 | 状態 |
| --- | --- | --- |
| `splitCechTerm`、`splitCechPoint`、`splitCechMap`、`splitCechExtension` | 最小元の座標には実際の切断を使う拡張幾何図式 | 関手性を全座標の等式から証明 |
| `splitCechExtensionRestrictionIso`、`splitCechExtensionAugmentation_restriction` | 元の Čech nerve と指定増強への制限 | 定義による実際の一致 |
| `splitCechEmptyIso` | 空座標の段は指定基底射で基底と同型 | 証明済み |
| `splitCechPresheafExtension`、`splitCechPresheafExtensionAugmentation` | 元の反変前層による実際の拡張と増強 | 始対象での指定増強が同型であることも証明 |

| 宣言（§82） | 内容 | 状態 |
| --- | --- | --- |
| `BottomSimplex`、`.adjoin`、`.forget`、`.homEquiv`、`.adjunction` | 最小元を保つ添字圏・自由な最小元の付加と忘却の随伴 | Hom 同値と自然性を実際に証明 |
| `BottomSimplex.initial` | 一点順序はこの添字圏の始対象 | 証明済み |
| `BottomSimplex.homotopyLimitRestrictionIso` | 自由な最小元の付加による実際のホモトピー極限の制限の自然同型 | 指定増強との接続は別工程 |

| 宣言（§81） | 内容 | 状態 |
| --- | --- | --- |
| `CechReindex.localized`、`.comparison`、`.adjunction` | 添字前合成の実際の局所化・指定比較・随伴の移送 | 対象ビルド済み |
| `CechReindex.constantIso` | 局所化後の前合成が定数図式と可換 | 対象ビルド済み |
| `CechReindex.homotopyData`、`.homotopyAdjunction`、`.homotopyComputationIso` | 相関した実際の導来計算と定数随伴 | 対象ビルド済み |
| `CechReindex.homotopyLimitIso`、`.homotopyLimitCanonicalIso` | 左随伴な添字への制限による実際のホモトピー極限の自然同型 | 指定増強との整合性は次工程 |

| 宣言（§80） | 内容 | 状態 |
| --- | --- | --- |
| `cechSpaceComparisonRetract`、`cechSpaceDescent_of_retract` | 指定ホモトピー比較の実際の retract と弱同値の移行 | 対象ビルド済み |
| `presheafAugmentedCechSpaces` | 基底上の幾何図式と値域関手から指定増強を保持する実際の関手 | 対象ビルド済み |
| `presheafCechSpaceDescent_of_retract`、`BaseChangeTransfer.cechSpaceDescent` | 前層の retract・局所 rank 公式から実際の指定降下を戻す | 対象ビルド済み、分裂側の降下の証明は別工程 |

| 宣言（§79） | 内容 | 状態 |
| --- | --- | --- |
| `DoubleAugmentedCechDiagram`、`.outer`、`.flatten` | 各行の増強元が変わる二重増強図式・外側増強・積添字への指定増強 | 対象ビルド済み |
| `DoubleAugmentedCechDiagram.curryIso`、`rowComparison`、`homotopyRowsFactorization` | 指定 curry 同型を保持した元の各行への比較と実際の行比較の因子化 | 対象ビルド済み、行の図式を定義上同じとはしない |
| `cechSpaceDescent_iso_iff`、`cechSpaceDescent_map_iff`、`cechSpaceDescent_map_iff_canonical` | 指定増強つき図式の同型・元と図式が各点で弱同値な射による降下条件の移送 | 対象ビルド済み |
| `DoubleAugmentedCechDiagram.rowHomotopyComparison`、`outerComparison`、`rowLimitIso` | 各行の実際の比較の列と外側の指定比較の正方形・同型 | 対象ビルド済み |
| `DoubleAugmentedCechDiagram.descent`、`descentCanonical` | 各行の実際の降下と外側の実際の降下から積添字の実際の指定降下 | 対象ビルド済み、局所化関手の追加入力は不要にできる |


| 宣言（§78） | 内容 | 状態 |
| --- | --- | --- |
| `augmentedCechRows` | 二重図式の増強から各行の増強つき図式の実際の関手 | 対象ビルド済み、外側の自然性を導出 |
| `rowWeightedCechAugmentation`、`rowWeightedCechDiagram`、`rowwiseWeightedCechAugmentation` | 各行の指定重み比較と、それを増強とする外側の直接比較 | 対象ビルド済み |
| `cechWhiskerRight_homEquiv_app`、`cechCurrying_homEquiv_app_app` | 持ち上げ・curry の指定随伴の成分での計算式 | 対象ビルド済み |
| `iteratedWeightedCechAugmentation_rowwise` | 二つの重みの反復比較と各行・外側の直接比較の一致 | 対象ビルド済み、降下や Fubini の結論は不使用 |
| `rowHomotopyCechAugmentation`、`rowHomotopyCechDiagram` | 各行の既存の実際の指定比較の自然な束ねと外側の増強図式 | 対象ビルド済み |
| `iteratedHomotopyCechAugmentation_rowwise`、`cechSpaceDescent_rowwise_iff` | 実際の反復指定比較の行表示と対応する降下条件の同値 | 対象ビルド済み、行・外側の置換は独立 |


| 宣言（§77） | 内容 | 状態 |
| --- | --- | --- |
| `iteratedHomotopyCechAugmentation` | 二つの指定重み増強と行・外側の独立な置換から直接構成した反復指定比較 | 対象ビルド済み、Fubini から逆算しない |
| `homotopyCechAugmentation_fubini` | §72 の実際の導来 Fubini 同型全体と指定増強の可換式 | 対象ビルド済み、増強つき図式の圏全体の自然変換の等式 |
| `homotopyCechAugmentation_fubiniCanonical` | 導来定数比較を内部で構成した指定 Fubini でも同じ可換式 | 対象ビルド済み、比較の追加入力は不要 |
| `cechSpaceDescent_fubini_iff` | 積添字の実際の指定降下条件と直接構成した反復指定比較の弱同値の同値 | 対象ビルド済み、模型の飽和性を使用 |


| 宣言（§76） | 内容 | 状態 |
| --- | --- | --- |
| `cechAdjunctionAugmentation` | 定数への指定比較を持つ任意の実際の随伴から指定増強の自然変換を構成 | 対象ビルド済み、単一・反復重みに共通 |
| `cechTensorAugmentation_assoc` | 単位への二つの射の外テンソル増強と二段増強の結合子を通じた一致 | 対象ビルド済み、任意のモノイダル圏 |
| `constantCechUncurryIso`、`iteratedCechTensorAugmentation` | 二段の定数図式の自然同型と二つの指定重み増強の合成 | 対象ビルド済み |
| `externalCechTensorIso_augmentation` | 外重みの指定増強と二段の指定増強の可換式 | 対象ビルド済み、自然変換の等式 |
| `iteratedWeightedCechAugmentation`、`weightedCechAugmentation_fubini` | 直接構成した反復側の指定比較と、指定 Fubini との全自然性を持つ可換式 | 対象ビルド済み、Fubini からの逆算ではない |


| 宣言（§75） | 内容 | 状態 |
| --- | --- | --- |
| `AugmentedCechDiagram`、`cechAugmentedSource`、`cechAugmentedDiagram` | 増強元・図式・増強を同時に動かす実際の comma 圏と両射影 | 対象ビルド済み |
| `weightedCechAugmentation`、`computedWeightedCechAugmentation`、`homotopyCechAugmentation` | 指定重みの錐と実際の置換後の比較を全ての増強つき図式の射に自然に構成 | 対象ビルド済み |
| `HasCechSpaceDescent` | 既存の実際のホモトピー極限への指定比較の弱同値という条件 | 定義、降下の証明そのものではない |
| `computedWeightedCechAugmentation_weightChange` | 実際の重み変更と指定比較の可換式を関手全体で保持 | 対象ビルド済み |
| `computedWeightedCechAugmentation_isIso_iff` | 局所化後の指定比較の同型性の重み変更による不変性 | 対象ビルド済み |
| `computedWeightedCechAugmentation_descent_iff` | 実際の指定比較の弱同値による降下条件の重み変更による不変性 | 対象ビルド済み、模型の飽和性から導出 |


| 宣言（§74） | 内容 | 状態 |
| --- | --- | --- |
| `CofibrantCechWeight.DerivedData`、`derivedData` | 左右の関手・同じ指定比較・導来性を相関して保持し、実際に構成 | 対象ビルド済み、新しい存在仮定は不要 |
| `CofibrantCechWeight.DerivedData.constantAdjunction`、`computationIso` | 同じ導来比較から随伴と計算同型を構成 | 対象ビルド済み、独立な選択を排除 |
| `CofibrantCechWeight.computesDerivedIso_fac` | 実際の計算同型が元の指定 β を保持 | 対象ビルド済み、元の図式は fibrant でなくてもよい |
| `CofibrantCechWeight.DerivedData.augmentation_mate` | 相関した随伴・計算同型と指定増強の像の可換式 | 対象ビルド済み |
| `CofibrantCechWeight.comparisonIso_augmentation` | 構成した重み変更の合成同型そのものが同じ指定増強の像を保持 | 対象ビルド済み、同じ a と指定重み増強を使用 |


| 宣言（§73） | 内容 | 状態 |
| --- | --- | --- |
| `cechConeMate_rightAdjointUniq`、`weightedCechFubiniIso_mate` | 指定右随伴同型・指定 Fubini 同型が元の錐の随伴像を保持 | 対象ビルド済み |
| `weightedCechFubiniIso_unit`、`weightedCechFubiniIso_counit` | 指定 Fubini と単位・余単位の可換式 | 対象ビルド済み |
| `CofibrantCechWeight.derivedTensorConstantIso_fac`、`derivedTensorConstantIso_inv_fac` | 構成した導来定数比較の両方向と指定重み増強の可換式 | 対象ビルド済み |
| `CofibrantCechWeight.derivedConstantAdjunction_augmentation_mate` | 指定増強の導来定数随伴の像と、元の重みつき錐の導来像の一致 | 対象ビルド済み、増強を保持する計算式 |


| 宣言（§72） | 内容 | 状態 |
| --- | --- | --- |
| `cechDiagram_isFibrant_iff`、`cechFibrant_row` | 射影的図式の各成分・各行の fibrancy | 対象ビルド済み、各行の fibrancy を導出 |
| `innerCechConeFunctor_isFibrant` | 内側の実際の cofibrant 重みの錐空間の列の fibrancy | 対象ビルド済み、右 Quillen 性を使用 |
| `innerCechConeComparison`、`iteratedCechConeComparison` | 各行と外側の独立な実際の置換の指定比較 | 対象ビルド済み、全ての射への自然性を保持 |
| `innerCechConeComparison_weakEquivalence`、`iteratedCechConeComparison_weakEquivalence` | fibrant 二重図式上の指定比較の弱同値 | 対象ビルド済み |
| `iteratedCechHomotopyLimit_map_weakEquivalence` | 実際の反復ホモトピー極限の各点の弱同値の保存 | 対象ビルド済み、fibrancy は不要 |
| `fibrantIteratedCechComparisonIso`、`iteratedCechReplacementComparisonIso` | 共通置換後の独立置換の比較と共通置換を外す自然同型 | 対象ビルド済み、実際の弱同値を局所化 |
| `cechHomotopyLimitFubiniIso`、`cechHomotopyLimitFubiniCanonicalIso` | 積添字と独立に反復した実際の単体集合のホモトピー極限の自然同型 | 対象ビルド済み、導来定数関手の比較は内部構成可能 |


| 宣言（§71） | 内容 | 状態 |
| --- | --- | --- |
| `CofibrantCechWeight.weightedFunctor`、`computesDerivedIso` | 任意の cofibrant 重みの実際の錐空間と右導来関手の比較 | 対象ビルド済み、指定 fibrant 置換を使用 |
| `CofibrantCechWeight.derivedTensorConstantIso`、`derivedConstantAdjunction` | 可縮増強から導来定数関手との比較・その実際の右随伴を導出 | 対象ビルド済み |
| `CofibrantCechWeight.exists_rightAdjoint_constant`、`comparisonIso` | 右導来関手の実際の存在と既存のホモトピー極限との自然同型 | 対象ビルド済み、新しい存在仮定は不要 |
| `homotopyCechProductWeightComparisonIso` | cofibrant な可縮外重みが積添字の実際のホモトピー極限を計算 | 対象ビルド済み |
| `homotopyCechWeightedFubiniIso` | 積添字の実際のホモトピー極限と共通 fibrant 置換後の反復錐空間の自然同型 | 対象ビルド済み、独立な反復置換との比較は次工程 |


| 宣言（§70） | 内容 | 状態 |
| --- | --- | --- |
| `externalCechWeight`、`externalCechWeightIso` | 二つの単体的重みの外積と反復テンソル関手による表示 | 対象ビルド済み |
| `externalCechTensorIso`、`iteratedCechConeAdjunction`、`weightedCechFubiniIso` | 実際の左随伴の結合子と右随伴の一意性による錐空間の Fubini | 対象ビルド済み、導来性の比較は別工程 |
| `cechCurry_isRightQuillen`、`cechUncurry_isLeftQuillen` | 積添字と反復した射影的模型の Quillen 随伴 | 対象ビルド済み、左クラスを点ごととはしない |
| `externalCechWeight_isCofibrant` | 射影的 cofibrant 重みの外積の cofibrancy | 対象ビルド済み、左 Quillen 関手で導出 |
| `externalCechWeightAugmentation`、`externalCechWeightAugmentation_weakEquivalence` | 二つの可縮重みの外積の指定増強と各点の弱同値 | 対象ビルド済み |
| `homotopyCechProductWeight`、`homotopyCechProductWeight_isCofibrant`、`homotopyCechProductWeightAugmentation_weakEquivalence` | 既存の選択されたホモトピー錐の二つの重みの cofibrant な可縮外積 | 対象ビルド済み、新しい置換の仮定は不要 |


| 宣言（§69） | 内容 | 状態 |
| --- | --- | --- |
| `centralLocalizationKernel`、`centralLocalizationKernel_iff_scalarSupported`、`centralLocalizationKernel_eq_scalarSupported` | 中心局所化の共通核と既存の正指数の台条件の同定 | 対象ビルド済み、自己準同型の局所化比較は明示 |
| `centralKernelScalarEquivalence` | 共通核と既存の台つき部分圏の圏同値 | 対象ビルド済み、対象・射は元の圏のまま |
| `centralKernelScalarEquivalence_forget`、`centralKernelScalarEquivalence_inverse_forget` | 両方向とも元の圏への忘却と可換する自然同型 | 対象ビルド済み |
| `centralKernelScalarEquivalence_functor_additive`、`functor_linear`、`inverse_additive`、`inverse_linear` | 両方向の加法性と中心線形性 | 対象ビルド済み |
| `centralLocalizationKernel_map`、`centralKernelMap`、`centralScalarSupportMap` | 局所化と可換する指定係数変更の両部分圏への制限 | 対象ビルド済み、核保存を導出 |
| `centralKernelScalarEquivalence_naturality` | 台の圏同値と指定係数変更の可換性 | 対象ビルド済み、全ての射への自然性を保持 |


| 宣言（§68） | 内容 | 状態 |
| --- | --- | --- |
| `centralLocalization_isZero_iff` | 自己準同型の局所化比較から、対象の消滅と中心冪による恒等射の消滅を同定 | 対象ビルド済み、比較の供給は compact 性・T2 の責務 |
| `centralSupport_iff_power_annihilation` | 有限個の異なる局所化先の圏での消滅と共通指数の同値 | 対象ビルド済み |
| `central_ideal_power_annihilation_iff` | 各中心元の冪ねじれと有限生成イデアル冪による恒等射の消滅の同値 | 対象ビルド済み |
| `support_preimage_empty_after_inversion`、`scheme_support_preimage_empty_after_inversion` | 根基の中心元を逆にした後の閉台の空性と任意のスキーム射への適用 | 対象ビルド済み、Noether 性は不要 |
| `supported_perfect_baseChange_acyclic` | 実際の台つき有限射影複体の底変換後の acyclic 性 | 対象ビルド済み、既存の可換係数の複体模型 |
| `supported_perfect_baseChange_nullHomotopy`、`supported_perfect_baseChange_isZero` | 同じ複体の恒等射の零ホモトピーとホモトピー圏の零対象性 | 対象ビルド済み、K₀ 類だけの消滅ではない |


| 宣言（§67） | 内容 | 状態 |
| --- | --- | --- |
| `finiteTypePullback_isSeparated` | 分離射の底変換と構造射の合成による指定引き戻しの分離性 | 対象ビルド済み |
| `finiteTypeBaseChangeAction_over_base` | 同じ指定作用が同じ第二射影の基底上にあること | 対象ビルド済み |
| `finiteTypeBaseChangeSection`、`finiteTypeBaseChangeSection_identity` | 持ち上げからの指定切断と切断恒等式 | 対象ビルド済み |
| `NaturalBlowupSequences.generalBaseChange_piDescent` | 一般の分裂底変換の指定比較の全係数・全整数次数の同型 | 対象ビルド済み、自然な列などの条件は明示 |
| `NaturalBlowupSequences.localNoether_generalBaseChange_piDescent` | 局所 Noether 基底から次元上界を供給した同じ結論 | 対象ビルド済み、有限次元仮定を残さない |
| `AbstractBlowupSquare.modification_isSeparated`、`center_isSeparated`、`exceptional_isSeparated` | 基底が S 上分離なら三つの非自明な頂点も S 上分離 | 対象ビルド済み、中心の被約化は不要 |


| 宣言（§66） | 内容 | 状態 |
| --- | --- | --- |
| `schemePullbackChange`、`schemePullbackChange_isPullback` | 二段の指定底変換の比較射と Cartesian 性 | 対象ビルド済み |
| `schemeBaseChange_transitive` | 任意のスキームへの底変換での点のファイバーの推移性 | 対象ビルド済み、アフィン性・有限型性は不要 |
| `finiteTypeBaseChange_transitive` | 元の有限型の圏の指定引き戻し・指定作用への推移性の供給 | 対象ビルド済み、底変換側のアフィン性は不要 |
| `openCover_dimension_le`、`finiteOpenCover_dimension_bound` | 開被覆の共通上界・有限被覆の個別上界から全体の次元上界 | 対象ビルド済み |
| `schemeMorphism_dimension_bound`、`localNoether_schemeMorphism_dimension_bound` | 準コンパクトな有限型スキームの有限次元性 | 対象ビルド済み、基底の有限次元性は明示 |
| `localNoether_generalCechStage_dimension_bound` | 実際の一般の Čech 各段の有限次元上界 | 対象ビルド済み、始域のアフィン性は不要 |


| 宣言（§65） | 内容 | 状態 |
| --- | --- | --- |
| `finiteTypeCechColumnIso`、`finiteTypeCechColumnIso_augmentation`、`finiteTypeCechColumnIso_toOriginal` | 指定底変換列と実際の底変換被覆の Čech nerve の自然同型、増強・元の Čech への指定射の保存 | 対象ビルド済み |
| `AbstractBlowupSquare.baseChangeExceptionalNatIso` | 例外部分と元の例外部分の指定底変換との全基底射に自然な同型 | 対象ビルド済み |
| `AbstractBlowupSquare.cechColumn₁Iso`、`cechColumn₂Iso`、`cechColumn₃Iso` | 三つの非自明な頂点の列と実際の底変換被覆の Čech nerve の自然同型 | 対象ビルド済み |
| `AbstractBlowupSquare.cechColumn₁Iso_augmentation`、`cechColumn₂Iso_augmentation`、`cechColumn₃Iso_augmentation` | 同じ指定増強の保存 | 対象ビルド済み |
| `AbstractBlowupSquare.cechColumn₁AugmentedIso`、`cechColumn₂AugmentedIso`、`cechColumn₃AugmentedIso`、`cechColumn₄AugmentedIso` | 四頂点全ての列と実際の増強 Čech nerve の同型 | 対象ビルド済み、増強先を含む |


| 宣言（§64） | 内容 | 状態 |
| --- | --- | --- |
| `finiteTypeBaseChangeMap`、`finiteTypeOverBaseChangeArrow`、`finiteTypeOverBaseChangeToOriginal` | 実際の指定モデルの底変換関手と元の射への自然比較 | 対象ビルド済み、二射影で関手性を検査 |
| `finiteTypeBaseChangeArrowNatIso` | 指定モデルと圏の選択された底変換 Arrow 関手の自然同型 | 対象ビルド済み、対象の型クラスを変更しない |
| `AbstractBlowupSquare.baseChangeFunctor`、`baseChangeToOriginal` | 抽象 blowup 底変換の関手と自然な比較立方体 | 対象ビルド済み |
| `AbstractBlowupSquare.cechBaseChangeSquares`、`cechBaseChangeToOriginal` | 全 Čech 段と全単体射に対する実際の正方形と自然な比較 | 対象ビルド済み |
| `finiteTypeMixedAugmentedCechIso`、`finiteTypeMixedAugmentedCechIso_augmentation` | 指定モデルと混合増強 Čech の図式全体の自然同型と増強の保存 | 対象ビルド済み |
| `finiteTypeMixedCechImageIso` | 元の同じ前層の像での増強二重図式の自然同型 | 対象ビルド済み、Tot の交換は使わない |


| 宣言（§63） | 内容 | 状態 |
| --- | --- | --- |
| `pullback_snd_iso_over_open` | 指定開部分上での実際の同型性の任意の底変換での保存 | 対象ビルド済み |
| `AbstractBlowupSquare.baseChange` | 元の有限型の圏内の任意の射への抽象 blowup の実際の底変換 | 対象ビルド済み、中心の厚みを保持 |
| `AbstractBlowupSquare.baseChangeCube` | 元の正方形への指定比較立方体と四面の可換性 | 対象ビルド済み |
| `AbstractBlowupSquare.baseChangeCube_cartesian₁₂`、`cartesian₁₃`、`cartesian₂₄`、`cartesian₃₄`、`cartesian₁₄` | 全側面と例外部分全体の実際の Cartesian 性 | 対象ビルド済み |
| `AbstractBlowupSquare.baseChangeExceptionalIso`、`baseChangeExceptionalIso_hom_fst`、`baseChangeExceptionalIso_hom_snd` | 例外部分と指定底変換との標準同型、二射影の保存 | 対象ビルド済み |


| 宣言（§62） | 内容 | 状態 |
| --- | --- | --- |
| `overBaseChangeArrow`、`overBaseChangeArrowToOriginal` | 任意の基底上の対象の底変換 Arrow の関手と元の射への自然比較 | 対象ビルド済み |
| `mixedAugmentedCech`、`mixedCech_isPullback` | 異なる二つの射の混合二重 Čech と指定各段の実際のファイバー積 | 対象ビルド済み |
| `mixedCechSwapNatIso`、`mixedCechSwapIso_involutive` | 二つの射と全単体軸の交換の自然同型と往復の恒等性 | 対象ビルド済み |
| `mixedCechRefinementStageExtraDegeneracy` | 細分射から混合二重 Čech の片方向の全行の実際の分裂 | 対象ビルド済み、切断の外側の自然性は要求しない |
| `mixedCechRefinementImage_contractingHomotopy` | 元の同じ前層の像の各行の実際の収縮ホモトピー | 対象ビルド済み、Tot の降下は別工程 |
| `exists_affine_flat_refinement_with_split_mixed_rows` | 実際のアフィン平坦化細分、低次元中心、正の定 rank、元の被覆の混合行の分裂 | 対象ビルド済み、元の射の平坦性は不要 |


| 宣言（§61） | 内容 | 状態 |
| --- | --- | --- |
| `positive_multiple_of_rational_tensor_lift`、`positive_multiple_of_rational_tensor_lift_right` | 両方のテンソル順で有理持ち上げから分母・ねじれを消して正の整数倍を持ち上げる | 対象ビルド済み、ねじれなし性・有限生成性不要 |
| `rational_tensor_lift_iff_positive_multiple` | 有理持ち上げと正の整数倍の持ち上げの同値 | 対象ビルド済み |
| `IntegralPullbackComparison` | 有理化した整数群と前層の指定次数の比較と指定写像の自然性 | 接続データの型、K0・T2 からの存在は未供給 |
| `IntegralPullbackComparison.positive_multiple_of_piDescent`、`positive_multiple_of_invariant` | 指定 PiDescent と比較データから同じ整数写像での不変類の正整数倍の持ち上げ | 対象ビルド済み、条件付きの一般比較補題 |


| 宣言（§60） | 内容 | 状態 |
| --- | --- | --- |
| `FiniteFreeAffineChart.baseChangeBasis`、`baseChange_isPullback` | 任意のアフィン底変換の同じ添字の基底と実際の指定 Cartesian 性 | 対象ビルド済み、追加の平坦性は不要 |
| `FiniteFreeAffineChart.rank_on_base`、`baseChange_rank` | 元の射と任意のアフィン底変換の実際の rank が同じ基底の本数に一致 | 対象ビルド済み |
| `FiniteFreeAffineChart.baseChangeBasis_naturality`、`baseChangeBasis_iterated` | 基底の係数写像への自然性と反復底変換の標準同型との一致 | 対象ビルド済み、各段で基底を選び直さない |


| 宣言（§59） | 内容 | 状態 |
| --- | --- | --- |
| `FiniteFreeAffineChart` | 実際の座標環、正の有限基底、開包含と Cartesian 正方形を持つチャートのデータ | 構成結果の型、前層の追加公理ではない |
| `exists_finiteFreeAffineChart_at_point` | 一般基底の有限忠実平坦有限表示射の各点での実際の有限自由チャート | 対象ビルド済み、Noether 性は不要 |
| `finiteFreeAffineOpenCover` | 準コンパクト基底全体を覆う実際の有限自由アフィン開被覆 | 対象ビルド済み、添字有限 |
| `FiniteFreeAffineChart.toProjection_isPullback` | 自由チャートの四辺の元の有限型の圏内での Cartesian 性 | 対象ビルド済み |
| `FiniteFreeAffineChart.toProjection_flatCover`、`toProjection_rank` | 同じ指定射の有限忠実平坦性・有限表示性と基底の本数との rank の一致 | 対象ビルド済み |
| `FiniteFreeAffineChart.toPullbackIso`、`toPullbackIso_hom_snd`、`toPullbackIso_hom_fst` | 元の有限型の圏の指定引き戻しとの同型と二射影の保存 | 対象ビルド済み |
| `finiteTypeFreeCharts_covers` | 元の有限型の圏へ持ち上げても有限部分族が基底全体を覆う | 対象ビルド済み |


| 宣言（§58） | 内容 | 状態 |
| --- | --- | --- |
| `exists_free_tensor_away_at_prime` | 各素点での局所化テンソル積の自由性と stalk rank の一致 | 対象ビルド済み |
| `exists_finite_free_tensor_cover` | 単位イデアルを生成する有限個の元による実際の自由自明化 | 対象ビルド済み |
| `exists_positive_basis_tensor_cover` | 有限忠実平坦代数の局所化テンソル積の正の有限基底 | 対象ビルド済み |
| `finiteFlatFreeSpecCover`、`finiteFlatFreeSpecChart_isPullback` | 実際の有限アフィン開被覆と元の有限射の Cartesian チャート | 対象ビルド済み |
| `tensorFreeBasisBaseChange` | 自由基底の同じ添字を任意の係数底変換で保持 | 対象ビルド済み、追加の平坦性は不要 |
| `exists_affinePresentation_positive_basis_cover` | 元のアフィン有限忠実平坦射の表示への正の有限自由自明化の適用 | 対象ビルド済み、実際の代数構造を明示 |


| 宣言（§57） | 内容 | 状態 |
| --- | --- | --- |
| `finiteFlatRankOpenCover`、`finiteFlatRankIndex_positive` | 有限忠実平坦射の正の定 rank の開被覆、準コンパクト基底で添字有限 | 対象ビルド済み |
| `finiteFlatRankOpen_baseChange_rank` | 各層の同じ定 rank の任意の底変換での保存 | 対象ビルド済み |
| `finiteTypeOpen`、`finiteTypeRankOpen_pullback_rank` | 元の有限型の圏内での rank 開部分と指定底変換の rank | 対象ビルド済み |
| `blowup_irreducible_of_affine_boundary` | 非零境界を避ける中心の blowup の実際の既約性 | 対象ビルド済み、既約性を仮定しない |
| `exists_affine_flat_refinement_with_rank_and_dimension` | 正の定 rank の平坦細分と同じ正方形の中心の次元低下 | 対象ビルド済み、有限次元上界を明示 |


| 宣言（§56） | 内容 | 状態 |
| --- | --- | --- |
| `strictTransformChartModelIso`、`strictTransformChartModelPullbackIso` | 任意の Cartesian 表示から実際の strict transform チャートへの同型 | 対象ビルド済み、構造射保持 |
| `affineTopPresentation`、`affinePresentationMap` | 元のアフィンスキームの全切断環による表示と実際の有限環準同型 | 対象ビルド済み |
| `blowupTopChartCover` | 実際の全標準チャートによる blowup のアフィン開被覆 | 対象ビルド済み |
| `strictTransform_flat_of_topChart_pureTransforms` | 全標準チャートの純変換加群の平坦性から global strict transform の平坦性 | 対象ビルド済み |
| `exists_affine_finite_flattening_center` | 整アフィン Noether 基底への有限射の真閉平坦化中心の存在 | 対象ビルド済み、存在を仮定しない |
| `exists_affine_finiteFlat_refinement` | 有限全射の blowup 後の有限忠実平坦細分 | 対象ビルド済み、有限型の圏内 |


この表は検証済みの宣言と予定を区別する。

| 宣言・モジュール | 役割 | 検証状態 |
| --- | --- | --- |
| `FiniteTypeSchemes` | 基底上有限型の圏 | 実装済み |
| `GradedPresheaf` | H、n ∈ ℤ、有理加群、反変性 | 実装済み |
| `GradedPresheaf.pullback_comp` | 反変合成 | 対象ビルド済み |
| `GradedPresheaf.invariantComparison` | 幾何学的な引き戻しの値域制限 | 対象ビルド済み |
| `GradedPresheaf.PiDescent` | 全次数の指定比較が同型という命題の型 | 定義のみ、主定理未証明 |
| `normalizedTransfer_comp` | 正 rank の局所公式から左逆 | 対象ビルド済み |
| `pullback_injective_of_transfer` | 同公式から各次数の単射性 | 対象ビルド済み |
| `normalizedTransfer_naturality` | rank による正規化は自然性を保つ | 対象ビルド済み |
| `permutationInvariants_constant` | 推移的作用の不変族は定数 | 対象ビルド済み |
| `permutationInvariantsEquiv` | (3.8) の代数的な線形同型 | 対象ビルド済み |
| `permutationInvariantsEquiv_apply_eq` | 評価点に依存しない | 対象ビルド済み |
| `piIsomorphisms` | 指定した観測関手による全整数次数の比較 | 対象ビルド済み |
| `piIsomorphisms_of_retract` | 比較射の retract による全次数同型の移行 | 対象ビルド済み |
| `PresheafRealization` | V 値前層と次数付き前層の自然な比較 | 型を実装、実際の E の実現は未構成 |
| `rankTransferRetract` | 導来図式を保持する有理線形圏の retract | 対象ビルド済み |
| `naturalTransferRetract` | 自然変換としての transfer の retract | 対象ビルド済み |
| `naturalComparisonRetract` | 自然な比較そのものの矢の圏の retract | 対象ビルド済み |
| `piComparison_of_transfer` | rank 公式と分裂側の比較から全次数比較 | 対象ビルド済み |
| `trivialInvariantsEquiv` | 自明表現の通常の不変部分の同型 | 対象ビルド済み |
| `averageMap_naturality` | 平均作用素の同変写像に対する自然性 | 対象ビルド済み |
| `invariantMap_surjective` | 有理不変部分は有限群の全射を保つ | 対象ビルド済み |
| `invariantMap_exact` | 有理不変部分は任意の隣接二射の完全性を保つ | 対象ビルド済み |
| `GradedPresheaf.pullbackRepresentation` | 逆元による引き戻しの左表現 | 対象ビルド済み |
| `GradedPresheaf.invariantMap_equivariantPullback` | 表現論的な制限と指定比較の一致 | 対象ビルド済み |
| `rationalInvariants_preservesHomology` | 有理不変部分関手のホモロジー保存 | 対象ビルド済み |
| `invariantsHomologyIso` | 任意の短複体のホモロジーと不変部分の比較 | 対象ビルド済み |
| `baseChangeSplitEpi` | 被覆への持ち上げがある基底変更の切断 | 対象ビルド済み |
| `baseChangeCechExtraDegeneracy` | 非増強 Čech 項上の section への還元用分裂 | 対象ビルド済み |
| `selfPullbackCechExtraDegeneracy` | 自身による底変換後の Čech nerve の分裂 | 対象ビルド済み |
| `selfPullbackCechImageExtraDegeneracy` | 任意の前層を適用した余単体図式の分裂 | 対象ビルド済み |
| `selfPullbackCechImage_contractingHomotopy` | 前層の Čech 図式の収縮ホモトピー | 対象ビルド済み |
| `IsNilpotentThickening` | 核イデアル層が冪零な閉埋め込み | 型を実装 |
| `Nilinvariant` | 係数つき前層に要求する公理 (3) | 法則の型を実装、E の検証は未完 |
| `nilpotentThickening_surjective` | 冪零 thickening の点全射性 | 対象ビルド済み |
| `nilpotentThickening_isIso_of_reduced` | 終域が被約な場合の同型性 | 対象ビルド済み |
| `proper_of_finite` | 有限射の固有性 | 対象ビルド済み |
| `isIso_of_surjective_closedImmersion` | 被約な終域への点全射閉埋め込みの同型性 | 対象ビルド済み |
| `closedImmersion_of_section` | 分離射の切断の閉埋め込み性 | 対象ビルド済み |
| `closedImmersion_equalizer` | 分離な対象への二射の等化子の閉埋め込み性 | 対象ビルド済み |
| `equalizer_range_ne_univ_of_ne` | 被約な始域からの異なる二射の一致場所は真閉 | 対象ビルド済み |
| `topologicalKrullDim_properClosed_lt_bound` | 有限次元上界からの真閉部分の次元低下 | 対象ビルド済み |
| `integral_properClosed_dimension_lt` | 有限次元の整スキームの真閉部分の次元低下 | 対象ビルド済み |
| `AbstractBlowupSquare` | 有限型・Cartesian・固有・閉中心・補開集合上の同型 | 幾何データの型を実装 |
| `GradedMayerVietoris.Hom.bijective_mapA` | 全次数の境界の自然性を使う五項補題 | 対象ビルド済み |
| `GradedPresheaf.squareDifference_comp_squareRestriction` | 指定制限と符号付きの差の零合成 | 対象ビルド済み |
| `SquareMayerVietoris` | 前層の指定制限を持つ長完全列 | 列のデータの型を実装、実降下からの供給は未完 |
| `SquareMayerVietoris.bijective_base_of_three_vertices` | 三頂点の全次数比較から元の指定比較の同型 | 対象ビルド済み |
| `finite_iUnion_proper_closed` | 既約空間上の有限個の真閉部分の和の真閉性 | 対象ビルド済み |
| `coincidenceLocus` | 相異なる添字の射の等化子の像の和 | 定義済み |
| `coincidenceLocus_ne_univ` | 既約被約な基底上の一致場所の和の真閉性 | 対象ビルド済み |
| `eq_index_of_common_restriction_outside` | 補集合で異なる二射の共通の制限を排除 | 対象ビルド済み |
| `coincidenceLocus_dimension_lt_bound` | 一致場所の和における有限次元低下 | 対象ビルド済み |
| `GradedMayerVietoris.Action.fixedSequence` | G 同変な長完全列の有理不変部分も全次数完全 | 対象ビルド済み |
| `GradedMayerVietoris.EquivariantHom.fixedHom` | 境界に自然な比較の不変部分への制限 | 対象ビルド済み |
| `GradedMayerVietoris.EquivariantHom.bijective_fixed_mapA` | 固定部分の B、C の比較から A の比較の全単射性 | 対象ビルド済み |
| `permutationRepresentation` | コピーの逆元による添字置換の左表現 | 定義済み |
| `permutationDiagonal_bijective` | (3.8) の指定対角比較の全単射性 | 対象ビルド済み |
| `permutationDiagonal_naturality` | 指定対角比較と同じ係数写像のコピーへの適用の可換性 | 対象ビルド済み |
| `invariantsProdEquiv` | 積の通常の不変部分と不変部分の積の具体的な線形同型 | 対象ビルド済み |
| `invariantMap_product_bijective` | 成分の不変部分の比較から積の不変部分の比較の同型性 | 対象ビルド済み |
| `splitMayerVietoris` | 比較元の恒等的な正方形の分裂長完全列 | 対象ビルド済み |
| `splitMayerVietorisComparison` | 境界の自然性も差の全射性から導く列の比較 | 対象ビルド済み |
| `orbitStep_pi_bijective` | (3.8) と中心上の帰納仮定による全次数の軌道貼り合わせ | 対象ビルド済み、主定理全体は未完 |
| `Theorem31.lean` | 最小公理から主定理へ | 代数的貼り合わせと実際の軌道段階を公開、全体の証明は未完 |
| `reducedClosedSubscheme` | 任意の閉集合の消滅イデアル層による被約閉構造 | 対象ビルド済み |
| `reducedClosedHomeo` | 被約閉部分スキームとその台の位相同型 | 対象ビルド済み |
| `reducedClosedAsFiniteType` | 基底上有限型の圏内の被約閉中心 | 対象ビルド済み |
| `coincidenceCenter` | section の一致場所の和の被約閉構造 | 対象ビルド済み |
| `coincidenceCenter_dimension_lt_bound` | 実際の一致中心のスキームの次元低下 | 対象ビルド済み |
| `closedCenterSquare_cartesian` | 中心の引き戻しの実際の Cartesian 性 | 対象ビルド済み |
| `abstractBlowupOfReducedCenter` | 中心の外で同型な固有射から抽象 blowup 正方形 | 対象ビルド済み、軌道射自体は未構成 |
| `affine_nilradical_isNilpotent` | アフィン Noether の nilradical イデアル層の冪零性 | 対象ビルド済み |
| `Nilinvariant.affineReduction_pullback_bijective` | 公理 (3) から実際のアフィン被約化の全次数比較 | 対象ビルド済み |
| `schemeReductionLift`、`schemeReductionLift_unique` | 被約な始域からの一意な因子分解 | 対象ビルド済み |
| `schemeReductionFunctor`、`schemeReductionInclusionNat` | 一般の reduction の関手と包含の自然変換 | 対象ビルド済み |
| `schemeReductionAction_comp_inclusion` | 被約化上への群作用の移行と包含の同変性 | 対象ビルド済み |
| `idealSheaf_isNilpotent_of_finite_affine_cover` | 有限被覆上の冪零指数の統一 | 対象ビルド済み |
| `noetherian_nilradical_isNilpotent` | 非アフィンを含む Noether スキームの nilradical の冪零性 | 対象ビルド済み |
| `finiteTypeScheme_isNoetherian` | Noether 基底上の有限型対象の Noether 性 | 対象ビルド済み |
| `finiteTypeReductionFunctor` | 前層 L の定義域内の reduction と包含の自然性 | 対象ビルド済み |
| `GradedPresheaf.invariantPullback_bijective` | 全単射な同変引き戻しの不変部分への制限 | 対象ビルド済み |
| `GradedPresheaf.piDescent_iff_of_bijective_square` | 同変正方形による指定降下比較の移行 | 対象ビルド済み |
| `Nilinvariant.piDescent_iff_reduction` | Noether 基底上の「一般 → 被約」の全次数還元 | 対象ビルド済み、公理 (3) を仮定 |
| `isNilpotentThickening_of_surjective_of_noetherian` | Noether な終域への点全射閉埋め込みの核の冪零性 | 対象ビルド済み |
| `nilpotentThickening_pullback_fst` | Noether な対象への底変換後の冪零性 | 対象ビルド済み |
| `Nilinvariant.piDescent_iff_thickening_baseChange` | 冪零な基底変更の前後の全次数比較 | 対象ビルド済み、公理 (3) を仮定 |
| `Nilinvariant.piDescent_iff_reducedSource` | 基底を固定した始域だけの被約化 | 対象ビルド済み、公理 (3) を仮定 |
| `NaturalBlowupSequences.orbit_piDescent_of_reduced_center` | 被約化した中心上の降下から実際の軌道段階へ | 対象ビルド済み、次元帰納そのものは未完 |
| `TranslatedSectionIndex` | 一つの切断の移動から重複を除いた添字 | 対象ビルド済み、有限・非空・推移的な作用 |
| `translatedSection_identity`、`translatedSection_injective` | 相異なる実際の切断族 | 対象ビルド済み |
| `translatedSection_covering` | 基礎点のファイバーの推移性からの像の被覆 | 対象ビルド済み、アフィンの幾何的推移性との接続も実装 |
| `translatedSection_center_dimension_lt_bound` | 移動切断の一致中心での次元低下 | 対象ビルド済み、有限次元上界を明示 |
| `exists_common_geometric_points` | 同じ基底点上の二点を共通の代数閉体から表示 | 対象ビルド済み |
| `geometricTransitivity_on_fibers` | 既存の環論的な幾何的推移性から通常の点の推移性 | 対象ビルド済み |
| `specAction`、`specAction_over_base` | 逆元を介した Spec の左作用と基底の保存 | 対象ビルド済み |
| `affineAlgebraObject`、`affineAlgebraAction` | 有限型の圏内の実際のアフィン対象と群作用 | 対象ビルド済み |
| `affine_translatedSection_covering` | 幾何的推移性から重複を除いた実際の移動切断の被覆 | 対象ビルド済み、切断の存在は入力 |
| `tensorBaseChangeMulSemiringAction`、`tensorBaseChange_smulCommClass` | B ⊗_A T 上の B 線形な群作用 | 対象ビルド済み |
| `tensorBaseChangeFiberEquiv_equivariant` | 幾何ファイバーの標準同型と作用の両立 | 対象ビルド済み |
| `geometricTransitivity_baseChange` | 任意の係数拡大による既存の幾何的推移性の保存 | 対象ビルド済み、平坦性・有限型性は不要 |
| `reducedSourceAction_transitive_on_fibers` | 始域だけの被約化による点のファイバーの推移性の保存 | 対象ビルド済み、Noether 性は不要 |
| `finiteTypeReductionLift`、`finiteTypeReductionLift_comp_inclusion` | 被約な始域から有限型の圏内の被約化への指定持ち上げ | 対象ビルド済み |
| `affine_baseChange_liftedSection_covering` | 基底変更と始域の被約化後の、元の切断からの移動切断の被覆 | 対象ビルド済み、基底は被約 |
| `closedBaseChangeAction_transitive_on_fibers` | 任意の閉中心への実際の引き戻しでの点の推移性 | 対象ビルド済み |
| `closedBaseChangeSection`、`closedBaseChangeSection_identity` | 元の切断から実際の閉中心上の切断を構成 | 対象ビルド済み |
| `closedBaseChange_reducedSection_covering` | 被約な閉中心上の始域の被約化後の被覆 | 対象ビルド済み |
| `orbitCenterAction_transitive_on_fibers`、`orbitCenterSection` | 構成済みの軌道中心への推移性と切断の直接接続 | 対象ビルド済み |
| `orbitCenter_reducedSection_covering` | 実際の軌道中心の始域の被約化後の移動切断の被覆 | 対象ビルド済み |
| `closedCoverAbstractBlowup` | 被約な終域の二つの閉部分による被覆を抽象 blowup とする | 対象ビルド済み、交わりは実際の引き戻し |
| `NaturalBlowupSequences.closedCoverSequence` | 閉和の全次数の境界と完全性を供給 | 対象ビルド済み、自然な blowup 列のデータを入力 |
| `closedCoverPullback_covering`、`closedCoverPullbackBlowup` | 始域へ引き戻した実際の閉被覆と抽象 blowup | 対象ビルド済み |
| `closedCoverPullbackCube` | 引き戻した交わりから元の交わりへの射と比較立方体 | 対象ビルド済み |
| `closedCoverPullbackSquareAction`、`closedCoverPullbackCube_equivariant` | 閉和の四頂点の作用と比較の同変性 | 対象ビルド済み |
| `NaturalBlowupSequences.closedCoverFixedComparison` | 閉和の境界を含む有理固定部分の列の比較 | 対象ビルド済み |
| `NaturalBlowupSequences.closedCover_piDescent` | 二つの閉部分と交わりの指定降下から元の射の全次数降下 | 対象ビルド済み、自然な列と三つの局所降下を入力 |
| `integralComponent`、`integralComponent_isIntegral` | 各既約成分の整な有限型閉構造 | 対象ビルド済み |
| `irreducibleComponentIndex_finite`、`integralComponent_covering` | Noether の場合の有限な整成分の閉被覆 | 対象ビルド済み |
| `componentSplitBlowup` | 一成分と残りの被約閉和の実際の正方形 | 対象ビルド済み |
| `componentSplit_intersection_dimension_lt_bound` | 非被約なままの実際の交わりの次元低下 | 対象ビルド済み、自然数上界を明示 |
| `componentRemainder_cover_card_lt` | 残りを覆う元の成分数の減少 | 対象ビルド済み |
| `reducedClosedMapOfLE` | 閉集合の包含から被約閉構造間の実際の射 | 対象ビルド済み |
| `componentToRemainder_covering` | 他の元の整成分から残りへの実際の有限閉被覆 | 対象ビルド済み |
| `fiberTransitivity_of_injective_square` | 同変で始域側が点上単射な正方形による推移性の移行 | 対象ビルド済み |
| `finiteTypeReductionMap_section`、`finiteTypeReductionAction_transitive_on_fibers` | 始域・基底の同時の被約化後の切断と点の推移性 | 対象ビルド済み |
| `finiteTypeReduction_dimension` | 有限型の圏内の被約化の次元保存 | 対象ビルド済み |
| `closedCoverIntersectionSection_identity` | 元の切断から交わりの指定比較の実際の切断を構成 | 対象ビルド済み |
| `closedCoverIntersection_transitive_on_fibers` | 実際の交わりの指定比較の点の推移性 | 対象ビルド済み |
| `closedCoverIntersection_reduced_covering` | 両側の被約化後の交わり上の移動切断の被覆 | 対象ビルド済み、幾何条件を元の射から導出 |
| `GradedPresheaf.piDescent_of_isIso`、`GradedPresheaf.piDescent_of_empty_target` | 同型と空の基底の全次数降下 | 対象ビルド済み、前層の降下公理は不要 |
| `SectionedDescentBelow` | 厳密に低い基底次元の切断を持つ射に対する帰納仮定の型 | 定義済み、前層の公理には含めない |
| `sectionedDescentBelow_zero` | 零より低い次元の帰納仮定を空の基底から供給 | 対象ビルド済み |
| `NaturalBlowupSequences.integral_reducedSource_piDescent_of_below` | 整な基底と被約な始域の段階を低次元から閉じる | 対象ビルド済み、中心上の降下は低次元から導出 |
| `NaturalBlowupSequences.integral_piDescent_of_below` | 整な基底と一般の始域の全次数降下の帰納段階 | 対象ビルド済み、Noether 性と公理 (3) を明示 |
| `irreducibleComponents_card_le_of_closed_cover` | 有限既約閉被覆による実際の既約成分数の上界 | 対象ビルド済み |
| `componentRemainder_componentCount_lt` | 残り自身の既約成分数の厳密な減少 | 対象ビルド済み |
| `SectionedDescentFewerComponents` | 成分数が厳密に少ない被約基底への帰納仮定の型 | 定義済み、最小公理には含めない |
| `NaturalBlowupSequences.reducedBase_piDescent_of_below` | 成分数の強い帰納を実行した被約基底の段階 | 対象ビルド済み、成分数の仮定は残らない |
| `NaturalBlowupSequences.piDescent_of_below` | 被約化を戻した一般の基底の一段 | 対象ビルド済み、低次元の仮定だけを入力 |
| `NaturalBlowupSequences.sectionedDescentBelow` | 外側の次元帰納による全ての低次元の仮定の構成 | 対象ビルド済み |
| `NaturalBlowupSequences.sectioned_piDescent` | 切断を持つ射の全次数降下 | 対象ビルド済み、局所降下・次元・成分数の帰納仮定は残らない |
| `affineSplitSection`、`affineSplitSection_identity` | 環の分裂から固定した S 上の切断 | 対象ビルド済み |
| `NaturalBlowupSequences.affine_split_piDescent` | 分裂するアフィン射の全次数降下 | 対象ビルド済み、元の L を使用 |
| `tensorBaseChangeRetraction` | 指定された T → B から底変換の分裂 | 対象ビルド済み、B 代数射 |
| `NaturalBlowupSequences.affine_baseChange_piDescent` | 分裂するテンソル積底変換の全次数降下 | 対象ビルド済み |
| `NaturalBlowupSequences.affine_selfBaseChange_piDescent` | 自己底変換の全次数降下 | 対象ビルド済み |
| `tensorSpecSquare_isPullback` | 指定二射影の実際の Cartesian 性 | 対象ビルド済み |
| `tensorSpecSquare_right_equivariant` | 右射影の元の作用との同変性 | 対象ビルド済み |
| `affineTensorSquare_isPullback` | 同じ S 上の有限型の圏内の Cartesian 性 | 対象ビルド済み |
| `affineTensorSection`、`affineTensorSection_identity` | 指定環射から有限型の圏内の切断と分裂恒等式 | 対象ビルド済み |
| `affineTensorAction_over_base`、`affineTensorSnd_equivariant` | 有限型の圏内の二射影の同変性 | 対象ビルド済み |
| `NaturalBlowupSequences.affineTensorFst_piDescent` | 指定された実際の底変換の第一射影の全次数降下 | 対象ビルド済み、元の L を使用 |
| `finiteTypeMorphism_locallyOfFiniteType` | 有限型対象間の射の局所有限型性 | 対象ビルド済み、Noether 性は不要 |
| `finiteTypePullback_isPullback` | Noether 基底上の実際の引き戻しを有限型の圏内へ構成 | 対象ビルド済み |
| `finiteTypeSchemes_hasFiniteLimits` | Noether 基底上の有限型の圏の有限極限 | 対象ビルド済み、幾何的な通常の極限 |
| `finiteTypeAugmentedCech` | 元の前層の定義域内の増強 Čech nerve | 対象ビルド済み |
| `finiteTypeCechBaseChange` | Čech 各段での底変換を束ねた Arrow の関手 | 対象ビルド済み、全単体射に対して定義 |
| `finiteTypeDoubleCech`、`finiteTypeDoubleCechImage` | 実際の二重 Čech 図式と元の前層の像 | 対象ビルド済み |
| `finiteTypeCechStageSplitEpi` | 各非増強段での底変換の実際の切断 | 対象ビルド済み、切断の外側自然性は主張しない |
| `finiteTypeCechStageExtraDegeneracy`、`finiteTypeCechStageImageExtraDegeneracy` | 各行の全次数の分裂と同じ前層の像での分裂 | 対象ビルド済み、Tot の実降下は未完 |
| `isPullback_isoPullback_equivariant` | Cartesian モデルと指定引き戻しの標準同型の同変性 | 対象ビルド済み、任意の圏で証明 |
| `pullbackAction_map_trivialBase` | 基底変更の射と元の始域の作用の可換性 | 対象ビルド済み |
| `affineTensorPullbackIso_equivariant` | テンソル積モデルと実際のアフィン引き戻しの作用の比較 | 対象ビルド済み |
| `NaturalBlowupSequences.affine_pullback_piDescent` | 指定引き戻しの第一射影の全次数降下 | 対象ビルド済み、元の L と指定作用を保持 |
| `finiteTypeCechStageAction_over_base` | 実際の Čech 各段のファイバーへの群作用 | 対象ビルド済み |
| `finiteTypeCechStageAction_naturality` | 外側の全単体射による底変換の射の同変性 | 対象ビルド済み |
| `GradedPresheaf.finiteTypeCechStageComparison_naturality` | 全係数・全整数次数の指定不変比較の外側自然性 | 対象ビルド済み |
| `finiteTypeOverInclusion_preservesFiniteLimits` | 有限型の圏から Over への包含の有限極限保存 | 対象ビルド済み、Noether 基底 |
| `finiteTypeSchemesForget_preservesFiniteConnectedLimits` | スキームへの忘却の有限連結極限保存 | 対象ビルド済み、終対象保存とは区別 |
| `finiteTypeLimit_isAffine` | アフィン有限型対象の有限連結極限のアフィン性 | 対象ビルド済み |
| `finiteTypeCechStage_isAffine`、`finiteTypeCechStageSource_isAffine` | 実際の Čech 段と底変換の始域のアフィン性 | 対象ビルド済み |
| `finiteTypeCechStageSource_isSeparated` | 各段の底変換の始域の S 上の分離性 | 対象ビルド済み、S の分離性は不要 |
| `finiteType_spec_dimension_bound` | Noether 基底環の上界から有限型代数の有限次元上界を供給 | 対象ビルド済み、多項式環の商を使用 |
| `localNoether_spec_dimension_bound` | 局所 Noether 基底の極大イデアルの生成元数による上界 | 対象ビルド済み |
| `affineMorphism_dimension_bound` | 実際の有限型アフィン射の始域の次元上界 | 対象ビルド済み、座標環の代数構造と有限型性を導出 |
| `localNoether_finiteTypeCechStage_dimension_bound` | 局所 Noether 基底の実際の Čech 各段の有限次元上界 | 対象ビルド済み、段ごとの上界を仮定しない |
| `schemeFiberTransitivity_of_iso` | 同変な始域・基底の同型による点の推移性の移行 | 対象ビルド済み |
| `schemeFiberTransitivity_of_injective_square` | underlying scheme の同変な単射正方形による推移性の移行 | 対象ビルド済み |
| `affineSchemeBaseChange_transitive` | 任意のアフィン基底変更の指定作用の点の推移性 | 対象ビルド済み、元の幾何的推移性から導出 |
| `affineFiniteTypeBaseChange_transitive` | 有限型の圏の指定引き戻しの点の推移性 | 対象ビルド済み、忘却による Cartesian 比較を使用 |
| `affineCechStage_transitive` | 実際のアフィン Čech 各段での底変換の推移性 | 対象ビルド済み、段ごとの推移性を仮定しない |
| `NaturalBlowupSequences.affineCechStage_piDescent` | 実際の Čech 各非増強段での全次数降下 | 対象ビルド済み、局所 Noether 基底、段ごとの幾何条件と降下の仮定は残らない |
| `arrow_isPullback_of_components` | Arrow の両端での Cartesian 性の検査 | 対象ビルド済み |
| `augmentedCechNerve_preservesPullbacks` | 増強 Čech nerve の引き戻し保存 | 対象ビルド済み、既存の右随伴性を使用 |
| `baseChangeAugmentedCech_isPullback` | 底変換した射の増強 Čech 図式の Cartesian 性 | 対象ビルド済み |
| `identityCechIso` | 恒等射の Čech nerve と定数図式の自然同型 | 対象ビルド済み、指定増強が hom |
| `baseChangeCechIso` | Čech の実際の底変換比較の全単体次数の同型 | 対象ビルド済み、図式全体の標準同型 |
| `doubleCech_isPullback` | 実際の二重 Čech 各対象のファイバー積表示 | 対象ビルド済み、二射影を指定 |
| `doubleCechSwapIso_involutive` | 二重 Čech の軸交換の二回の合成が恒等 | 対象ビルド済み |
| `doubleCechSwapIso_inner_naturality`、`doubleCechSwapIso_outer_naturality` | 全ての単体射と軸交換の整合性 | 対象ビルド済み |
| `doubleCechSwapNatIso` | 実際の二重 Čech 全体の軸交換の自然同型 | 対象ビルド済み、Tot の交換とは区別 |
| `cechMixIndex` と七つの添字恒等式 | 細分ホモトピーの重複座標と比較タグ | 対象ビルド済み、有限順序集合の算術 |
| `refinementCechHomotopy` | 同じ基底上の平行な細分 Čech 比較の単体ホモトピー | 対象ビルド済み、全ての面射・退化射を検査 |
| `refinementCechMap_id`、`refinementCechMap_comp` | 指定細分比較の恒等射・合成の保存 | 対象ビルド済み |
| `refinementCechHomotopyLeftInverse`、`refinementCechHomotopyRightInverse` | 相互細分の両側のホモトピー逆 | 対象ビルド済み、持ち上げの合成が恒等である仮定は不要 |
| `refinementCechImageHomotopyLeftInverse`、`refinementCechImageHomotopyRightInverse` | 元の前層の像における両側のホモトピー | 対象ビルド済み、Tot の実降下とは区別 |
| `baseChangePresheafPullback`、`baseChangePresheafPullback_at_base` | 元の前層の実際の底変換の自然な pullback と基底での比較 | 対象ビルド済み、実際の二射影を使用 |
| `BaseChangeTransfer.retract` | 自然な transfer と局所 rank 公式からの前層 retract | 対象ビルド済み、transfer の存在は明示入力 |
| `presheafAugmentationComparison`、`BaseChangeTransfer.augmentationRetract` | 基底の値を含む指定増強の自然性と retract | 対象ビルド済み、全ての図式射を保持 |
| `BaseChangeTransfer.cechAugmentationRetract` | 実際の Čech 増強比較の矢の圏の retract | 対象ビルド済み、Tot はまだ接続しない |
| `BaseChangeTransfer.piCechComparison_of_transfer` | 図式関手での像の全次数比較の移行 | 対象ビルド済み、実際の観測関手は明示入力 |
| `cechBaseChangeGeometryIso` | 実際の底変換被覆の Čech と Over 底変換図式の自然同型 | 対象ビルド済み、二射影と全単体射を保持 |
| `cechBaseChangeStageIso_augmentation`、`cechBaseChangeAugmentationIso` | 幾何的増強の可換性と前層の増強比較の矢の圏の同型 | 対象ビルド済み、増強先も含む |
| `BaseChangeTransfer.cechBaseChangedCoverRetract` | 実際の底変換被覆の Čech 比較への retract | 対象ビルド済み、transfer と局所 rank 公式は明示入力 |
| `BaseChangeTransfer.piCechComparison_of_baseChangedCover` | 実際の底変換被覆の全次数比較から元への還元 | 対象ビルド済み、Tot の実構成と分裂降下は別工程 |
| `invertibleCompositeRetract`、`naturalComparisonRetractOfIsoComposite` | 往復の合成の同型性による比較射の retract | 対象ビルド済み、圏の線形性は不要 |
| `piComparison_of_observedComposite`、`piComparison_of_observedRank` | 観測後の同型・rank 公式による全次数比較の移行 | 対象ビルド済み、元の圏に線形性を課さない |
| `BaseChangeTransfer.piCechComparison_of_observedRank` | 実際の底変換被覆からの観測後の transfer 還元 | 対象ビルド済み、rank 公式は実際の図式関手の像で要求 |
| `surjective_of_proper_dense_restrict` | 固有射の稠密開集合上の全射性から全射性 | 対象ビルド済み、開部分での同型性は不要 |
| `strictTransformπ_isFinite`、`strictTransformπ_restrict_surjective` | 実際の strict transform の有限性と開部分上の全射性 | 対象ビルド済み、既存の実際の閉包含を使用 |
| `strictTransformπ_centerComplement_surjective` | 有限全射の中心外からの strict transform の全射性 | 対象ビルド済み、実際の blowup の中心外の稠密性を使用 |
| `strictTransformπ_locallyOfFinitePresentation` | 局所 Noether 基底上の有限射の strict transform の有限表示性 | 対象ビルド済み、基底の局所 Noether 性を明示 |
| `exists_finiteFlat_refinement_of_flat_strictTransform` | 平坦化した実際の strict transform から有限忠実平坦な細分を取り出す | 対象ビルド済み、平坦化中心の存在は別工程 |
| `finiteTypeBlowup`、`finiteTypeBlowupProjection` | 元の有限型の圏内の実際の blowup と構造射 | 対象ビルド済み、Noether 基底上 |
| `finiteTypeStrictTransform`、`finiteTypeStrictTransformProjection`、`finiteTypeStrictTransformToOriginal` | 元の有限型の圏内の実際の strict transform と二つの指定射 | 対象ビルド済み、有限射を要求 |
| `finiteTypeStrictTransformToPullback`、`finiteTypeStrictTransformCechRefinement` | 実際の底変換被覆への細分射と Čech 比較 | 対象ビルド済み、全単体射と指定増強を保持 |
| `finiteTypeStrictTransform_flatCover` | 平坦化後の指定射の有限性・平坦性・全射性・局所有限表示性 | 対象ビルド済み、平坦性は実際の構造射の入力 |
| `finiteTypeBlowupSquare` | 実際の blowup の抽象 blowup 正方形 | 対象ビルド済み、被約閉中心と実際の引き戻しを使用 |
| `surjective_of_proper_genericPoint_mem_range` | 生成点を像に含む固有射の全射性 | 対象ビルド済み、既約性と閉像性を使用 |
| `integralComponentMap`、`integralComponentMap_isFinite` | 被約既約成分から元の基底への指定射と有限性 | 対象ビルド済み、同じ有限型の圏内 |
| `exists_surjective_integralComponent` | 既約基底への固有全射から全射な整成分を選ぶ | 対象ビルド済み、Noether 性も成分の有限個性も不要 |
| `exists_finite_surjective_integralComponent` | 整基底への有限全射から平坦化すべき整な有限全射成分を選ぶ | 対象ビルド済み、始域の被約性は不要 |
| `exists_finiteFlat_cover_refining_blowup` | 支配する整成分の平坦化後の被覆から元の射の底変換への細分 | 対象ビルド済み、指定中心での実際の平坦性は入力 |
| `exists_nonzero_away_free_of_finite` | Noether 整域上の有限加群の非零元による自由化 | 対象ビルド済み、元の平坦性は不要 |
| `exists_nonzero_away_flat_of_finite` | 同じ有限加群の境界外の平坦性 | 対象ビルド済み、生成点付近の自由化から導出 |
| `exists_nonzero_finite_module_flattening_center` | Noether 整域上有限な加群の実際の全チャート純変換の平坦化中心 | 対象ビルド済み、スキームの strict transform との同定は別工程 |
| `boundaryTorsionIdeal`、`algebraPureTransform` | 境界ねじれを除く実際のイデアルと商代数 | 対象ビルド済み、有限性は定義に不要 |
| `algebraPureTransformModuleEquiv`、`boundaryTorsionIdeal_eq_ker` | 加群純変換との線形同型と環の局所化の核との一致 | 対象ビルド済み、代表元を保つ |
| `algebraPureTransformToLocalization_injective` | 商代数から一元局所化への単射 | 対象ビルド済み、全射性は主張しない |
| `algebraPureTransformSpecπ_flat`、`algebraPureTransformSpecπ_isFinite` | 商の実際の Spec の平坦性・有限性 | 対象ビルド済み、元の加群の性質から移送 |
| `algebraPureTransformImageIso`、`algebraPureTransformBasicOpenImageIso` | 商の Spec と局所化・基本開の実際のスキーム論的像との同型 | 対象ビルド済み、閉包含を保持 |
| `algebraPureTransformBasicOpenImageIso_hom_structure` | 基本開の像との同型の基礎環上の可換性 | 対象ビルド済み、構造射を保持 |
| `algebraBoundaryOpen_image_flat`、`algebraBoundaryOpen_image_isFinite` | 基本開の実際のスキーム論的像の構造射の平坦性・有限性 | 対象ビルド済み、構造層を保持 |
| `exists_nonzero_finiteFlat_image_charts` | 実際の全 blowup チャート上のアフィン像を有限平坦にする中心 | 対象ビルド済み、global strict transform とのチャート比較・貼り合わせは別工程 |
| `ker_of_openBaseChange`、`ker_pullback_open` | 準コンパクトな射の核と開底変換の両立 | 対象ビルド済み、イデアル層としての等式 |
| `imageOpenBaseChangeIsoOfIsPullback`、`imageOpenBaseChangeIso` | 実際の像と開底変換の標準同型 | 対象ビルド済み、具体的な Cartesian モデルにも適用可 |
| `strictTransformOpen_quasiCompact` | 局所 Noether 基底上の有限型射の strict transform の定義開包含の準コンパクト性 | 対象ビルド済み、像の底変換の入力を供給 |
| `strictTransformOpenChartIso`、`strictTransformOpenChartIso_hom_snd` | 周辺チャートの像と global strict transform の実際のチャートの同型 | 対象ビルド済み、チャート基底への構造射を保持 |
| `strictTransform_chart_flat_of_image_flat` | 周辺チャートの像の平坦性から strict transform のチャートの平坦性 | 対象ビルド済み、実際のスキームの射に適用 |
| `strictTransform_flat_of_openChart_images` | 周辺チャートの全ての像の平坦性から global strict transform の平坦性 | 対象ビルド済み、実際の開被覆を使う |
| `basicOpen_dense_of_nonZeroDivisor` | 非零因子の基本開の稠密性 | 対象ビルド済み、Noether 性・被約性は不要 |
| `affineBlowup_boundary_dense` | アフィン blowup 上の境界基本開の逆像の稠密性 | 対象ビルド済み、中心補集合との一致は不要 |
| `blowup_boundary_dense_of_isAffine` | アフィン基底の実際の global blowup 上の境界逆像の稠密性 | 対象ビルド済み、全体のアフィンモデルから移送 |
| `strictTransformπ_boundary_surjective` | 平坦化と同じ境界基本開からの有限全射の strict transform の全射性 | 対象ビルド済み、生成点・中心の補集合の置換はしない |
| `exists_finiteFlat_cover_refining_boundary` | 同じ境界での整成分の平坦化から元の有限射を細分する有限忠実平坦被覆 | 対象ビルド済み、実際の平坦性は引き続き供給すべき入力 |
| `strictTransformTensorChart_isPullback`、`strictTransformTensorChart_ambient_isPullback` | テンソル積モデルと実際の周辺チャートの共通の Cartesian 表示 | 対象ビルド済み、チャートの係数射との可換性を明示 |
| `strictTransformTensorChartIso` | テンソル積の Spec と実際の周辺チャートの標準同型 | 対象ビルド済み、引き戻しの普遍性を使用 |
| `strictTransformTensorChartIso_hom_snd`、`strictTransformTensorChartIso_hom_base` | チャート基底と元の基礎環への構造射の保存 | 対象ビルド済み、同じ指定射を使用 |
| `strictTransformTensorChartIso_preimage_boundary` | 同じ境界基本開の二つのチャートでの一致 | 対象ビルド済み、型の一致だけではなく開集合として証明 |
| `openImageAmbientIso`、`openImageAmbientIsoOfEq` | 周辺同型が対応させる開部分の実際のスキーム論的像の同型 | 対象ビルド済み、閉包含を保持 |
| `strictTransformTensorImageIso` | テンソル積の像と実際の周辺チャートの像の同型 | 対象ビルド済み、同じ境界 D(r) |
| `strictTransformTensorPullbackIso`、`strictTransformTensorPullbackIso_hom_snd` | テンソル積の像と global strict transform のチャートの基底 C 上の同型 | 対象ビルド済み、指定構造射を保持 |
| `strictTransform_chart_flat_of_tensorPureTransform` | チャート係数環 C 上の純変換加群の平坦性から実際の strict transform のチャートの平坦性 | 対象ビルド済み、係数射の可換式と開チャートを明示 |
| `finiteCoproductDesc_isFinite` | 共通の終域への有限個の有限射を非交和にまとめる | 対象ビルド済み |
| `sectionOrbitMap_isFinite`、`sectionOrbitMap_isProper` | 分離射の有限個の切断からの軌道射の有限性・固有性 | 対象ビルド済み |
| `reducedSectionOrbitMap_isFinite` | 被約化への切断の軌道射の有限性 | 対象ビルド済み |
| `sectionOrbitAction` | コピーの添字の左作用による非交和の自己同型 | 対象ビルド済み |
| `reducedSectionOrbitMap_equivariant` | 被約化への軌道射の G 同変性 | 対象ビルド済み |
| `reducedSectionOrbitMap_surjective` | 明示した像の被覆から軌道射の全射性 | 対象ビルド済み、幾何的推移性との接続は未完 |
| `openImmersion_of_closedImmersion_of_open_range` | 被約な終域への開像を持つ閉埋め込みの開埋め込み性 | 対象ビルド済み |
| `finiteClosedCoproduct_isIso` | 被約な終域の互いに素な有限閉被覆の非交和は同型 | 対象ビルド済み |
| `eq_index_of_equal_section_points_outside` | 共通像を持つ点を引き戻しへ持ち上げた一致場所の判定 | 対象ビルド済み |
| `disjoint_restricted_section_ranges_outside` | 中心の逆像を避ける開集合上の切断の像の互いに素 | 対象ビルド済み |
| `restrictedSectionCoproduct_isIso` | 制限切断の非交和から被約な補開集合への同型 | 対象ビルド済み |
| `coproductRestrictionIso` | 有限非交和と開制限の標準同型 | 対象ビルド済み、指定制限との可換式を保持 |
| `sectionOrbitMap_restrict_isIso` | 軌道射自体の一致中心の外での同型 | 対象ビルド済み |
| `abstractBlowupOfClosedImmersion` | 非被約な閉中心も許す実際の引き戻し正方形 | 対象ビルド済み |
| `orbitSource`、`orbitMorphism` | 有限型の圏内の軌道射と有限性 | 対象ビルド済み |
| `orbitAbstractBlowup` | 中心 V ×_B Z を保持する実際の抽象 blowup | 対象ビルド済み、像の被覆を明示的に仮定 |
| `orbitAction`、`orbitMorphism_equivariant` | 有限型の圏内のコピーの作用と軌道射の同変性 | 対象ビルド済み |
| `pullbackAction` | 基底の作用も許す実際の引き戻し上の G 作用 | 対象ビルド済み、両射影の同変性も証明 |
| `finiteTypeActionOfSchemeAction` | 構造射を保つスキームの作用の有限型の圏への持ち上げ | 対象ビルド済み |
| `closedPullbackAction` | 閉中心の引き戻しの有限型の圏内の作用 | 対象ビルド済み、非被約な中心を許す |
| `SquareAction` | 四頂点の作用と四辺の同変性 | 幾何データの型を実装 |
| `orbitAbstractBlowupAction` | 実際の軌道正方形の四頂点・四辺の同変性 | 対象ビルド済み |
| `SquareAction.restriction_equivariant`、`difference_equivariant` | 前層の指定制限と差の同変性 | 対象ビルド済み |
| `SquareMayerVietoris.withSquareAction` | 幾何正方形と境界の同変性から全次数の列の作用 | 対象ビルド済み、境界の同変性は明示的な入力 |
| `SquareMayerVietoris.pullbackComparison` | 異なる幾何正方形の射による長完全列の比較 | 対象ビルド済み、境界の自然性を入力 |
| `NaturalBlowupSequences` | 実降下から供給する自然な全次数の列の接続データ | 型を実装、実降下からの存在の構成は未完 |
| `NaturalBlowupSequences.boundary_equivariant` | 境界の自然性から同変性を導出 | 対象ビルド済み |
| `NaturalBlowupSequences.fixedComparison_bijective_base` | 同変立方体の固定部分の列の全次数五項補題 | 対象ビルド済み |
| `identityCenterSquare`、`identityCenterBlowup` | 基底と中心の恒等変形の比較元 | 対象ビルド済み、境界の零性も証明 |
| `orbitComparisonCube`、`orbitComparisonCube_equivariant` | 実際の軌道正方形から基底の分裂正方形への同変立方体 | 対象ビルド済み |
| `NaturalBlowupSequences.orbitFixedComparison` | 指定幾何射からの不変部分の全次数比較 | 対象ビルド済み |
| `NaturalBlowupSequences.orbit_piDescent_of_fixed_components` | 中項・例外部分の固定比較から実際の PiDescent | 対象ビルド済み、(3.8)・帰納からの仮定の供給は未完 |
| `GradedPresheaf.copyEvaluation`、`copyEvaluationIntertwining` | 各コピーの包含の引き戻しと置換表現への同変性 | 対象ビルド済み |
| `GradedPresheaf.copyEvaluation_fixed_fold` | 実際の fold の比較と指定対角写像の一致 | 対象ビルド済み |
| `GradedPresheaf.copyEvaluation_bijective_of_preservesProduct` | 非交和の普遍性と積保存から指定評価の全単射性 | 対象ビルド済み、有限積保存は実降下からの供給が残る |
| `orbitComponent`、`orbitComponent_action`、`orbitFold` | 有限型の圏内のコピーの包含と fold、置換との両立 | 対象ビルド済み |
| `orbitSourceIsCoproduct` | 有限型の圏内の軌道の非交和の実際の普遍性 | 対象ビルド済み |
| `orbitFold_piDescent_of_preservesProduct` | コピーの有限積保存から (3.8) の幾何的な全次数比較 | 対象ビルド済み |
| `GradedPresheaf.fixedPullbackIntertwining_bijective` | 指定降下比較を幾何的自明作用からの固定比較へ移す | 対象ビルド済み |
| `NaturalBlowupSequences.orbitProductComparison_bijective` | (3.8) と中心上の降下から実際の中項の固定比較 | 対象ビルド済み |
| `NaturalBlowupSequences.orbit_piDescent_of_center_and_exceptional` | 中心上の降下と例外部分の比較から軌道段階を閉じる | 対象ビルド済み、後続の定理で例外部分の入力も導出 |
| `finiteTypeCofanIsColimitOfSchemeIsColimit` | スキームの非交和の普遍性を有限型の圏へ反映 | 対象ビルド済み |
| `closedImmersionSquare_isPullback` | 閉中心の具体的な引き戻しの有限型の圏内の普遍性 | 対象ビルド済み、持ち上げと二射影の公式も実装 |
| `orbitExceptional_isPullback` | 二段の例外部分の合成引き戻し W ×_B Z の普遍性 | 対象ビルド済み、スキームの圏でも証明 |
| `orbitExceptionalIsCoproduct` | 実際の例外部分が指定された Z のコピーの非交和 | 対象ビルド済み、有限型の圏内の普遍性 |
| `orbitExceptionalComponent_action` | 既存の引き戻し作用が指定包含を添字で置換 | 対象ビルド済み |
| `orbitExceptional_piDescent_of_preservesProduct` | 例外部分の (3.8) による全次数降下 | 対象ビルド済み、Z のコピーの有限積保存を入力 |
| `NaturalBlowupSequences.orbitExceptionalComparison_bijective` | 実際の比較立方体の例外部分の固定比較の同型 | 対象ビルド済み |
| `NaturalBlowupSequences.orbit_piDescent_of_center` | 自然な列・二つのコピーの積保存・中心上の降下から実際の軌道段階 | 対象ビルド済み、主定理の次元帰納は未完 |
| `SchemeFacts` | 幾何入力の証明 | 基本補題を実装、有限型での次元上界との接続は未完 |
| support comparison（予定） | K0・T2 から (3.6) | 未実装 |
| E realization（予定） | 外部レーンの実装への接続 | 未実装 |

## 18. 設計の確認点

次数付き可換群値の前層だけから Tot を復元しない。
各次数の通常の極限で Tot を置換しない。
導来降下を記述するための値域の追加構造を区別する。
π_* の公開界面とスペクトルの具体的な構成を分離する。
界面を確定する場合は L9 の所有と整合させる。
既に完成したとの体裁で未実装の法則を bundle に隠さない。
正本 D7 がすでに認める導来値域の型の具体化は §19 に従って進める。
必要な数学的設計変更があれば具体的な差分を提示して停止する。
独立に証明できる代数的基礎は先に検証可能にする。
import 閉包破損で停止した場合は失敗した import とログを記録する。
工程完了時は現在地と主要宣言表を更新する。
その報告後は承認を待たず次の工程に進む。

## 19. 導来値域への実現と全次数の公開界面

正本 D7 は Sp と Sp 内の極限を γ から受けることをすでに指定している。
従って導来値域を外部の引数にすることは、その既存の方針の型への具体化である。
次数付き可換群値の前層だけでは、公理 (1) の Tot と公理 (2) の
ホモトピー引き戻しを定義できないため、このデータを区別する。
全次数の群を保持することと、導来図式を保持することは別の条件。
最小公理そのものの数学的内容は変更しない。
公開主張を全次数 π_* 同型に保ちながら、実現のデータを外部から受ける。

### 19.1 誤った置換が生む具体的な問題

有理 Eilenberg–Mac Lane スペクトルを Hℚ とする。
ホモトピー引き戻し `0 ×ʰ_{Hℚ} 0` は `ΩHℚ`。
従ってその π₋₁ は ℚ で非零。
一方、各次数の通常の引き戻し `0 ×_{π_n(Hℚ)} 0` はすべて零。
このため、blowup 降下を各次数の群の通常の pullback としては書けない。
必要なのは境界写像を含む長完全列とその自然性。
Tot でも、単に次数ごとの通常の極限を取る定義は使えない。
補題 3.2 の transfer の左逆も、導来図式上の自然な retract である必要がある。
π_* の上でだけ分裂を作り、Tot にそのまま移してはならない。

### 19.2 実装した実現の界面

L9 が所有する導来値域 V とその図式・homotopy limit の構造を引数として受ける。
本レーンでは V の具体的なモデルを新設しない。
H ごとに V 値の反変前層 `value H` を保持する。
各 n の有理加群値の観測関手を引数にする。
L8 ではこれを π_n として新たに定義せず、L9 の実構成を後で代入する。
その合成と現在の `GradedPresheaf H n` との自然な比較同型を保持する。
記号的には `observation n ∘ value H ≅ L H n`。
Lean では `PresheafRealization.comparison` の自然同型として保持する。
π_n はこの界面に接続し、L8 で別の π_n を定義しない。
Zariski Čech 比較は V の実際の Tot に対して書く（未実装）。
抽象 blowup 比較は V の実際のホモトピー引き戻しに対して書く（未実装）。
transfer は導来図式を保持する圏の自然な射として持つ。
`rankTransferRetract` は任意の有理線形圏の射でこの分裂を証明する。
通常の関手圏の場合は `naturalTransferRetract` に特殊化する。
実際の導来図式の圏に二つの関手と比較自然変換があれば、
`naturalComparisonRetract` と `piComparison_of_transfer` が降下の retract を与える。
局所自明化後の rank 倍の恒等式もその図式上で書く。
Fubini・分裂降下・細分の法則は、対応する実際の homotopy limit に対して証明する。
全次数 π_* 同型という公開主張は現在の `PiDescent` のまま保つ。
K0・T2 の (3.6) 同定は別の明示的な引数として保持する。
E の実現でこの追加データを実際に供給する責任を残す。
界面の存在や導来降下の結論を新しい公理で埋めない。
固定点の π_* 比較も通常の不変部分の定義と分離する。

### 19.3 残る型と証明

L8a は次数付き前層とその導来値域への実現に対して八つの性質を記述する。
`PresheafRealization` は前層の実現データだけであり、八つの性質はまだ含まない。
L8b の数学的な証明経路は変わらない。
L8c の幾何補題の主張も変わらない。
L8d の K0・T2 依存を明示する方針も変わらない。
L8e の E の実現はこの持ち上げまで含めて検証する。
L9 の実装を編集したり、所有を移したりしない。
π_* の関手だけでは足りない導来図式の界面を、L9 との接続点として明示する。
現在の基礎モジュールはこの変更後もそのまま使用できる。

### 19.4 次の実装順序

L9 の Tot・hG の実構成は未着手で、現在の型は π_* の基礎が中心。
その実装を変更せず、L8 内で実際の比較図式とその法則の型を具体化する。
最小公理 (1)–(8) の定義を完成させる。
それから補題 3.2・3.3 と定理 3.1 の証明に進む。
独立な代数的基礎の実装を主定理の完成として数えない。

## 20. 最小公理と証明の未完部分

| 項目 | 証明・実装済みの範囲 | 残る責務 |
| --- | --- | --- |
| (1) Zariski Čech | 底変換後の実際の nerve の分裂・収縮 | Tot と比較、被覆での降下法則 |
| (2) 抽象 blowup | 幾何正方形、境界を持つ長完全列と三頂点比較、同変列の不変部分の完全性、自然な列から境界の同変性と固定比較 | 実際の降下からの列と境界の自然性の供給 |
| (3) 冪零不変性 | 冪零閉埋め込みの条件、点全射性、不変性の法則の型、Noether スキームの reduction の冪零性、全次数降下比較の被約化への還元 | 一般の thickening の底変換、E の不変性の検証 |
| (4) transfer | rank 公式から図式の retract、比較の全次数同型への移行 | 有限平坦な幾何射の transfer、底変換、射影公式、自明化による貼り合わせ |
| (5) 有理固定点 | 通常の不変部分の完全性・ホモロジー保存、指定対角比較、W と例外部分の実際の同変なコピー分解と指定前層比較、中心上の降下との積の固定比較 | L9 の実際の hG と π_* の比較、実降下からのコピーの有限積保存、導来 Shapiro への接続 |
| (6) 平坦化 | 原典と必要な型の調査 | Fitting 版の平坦化と細分の型・証明 |
| (7) スキーム補題 | 有限⇒固有、全射閉埋め込み⇒同型、切断・等化子、一致中心と次元低下、被約化、軌道正方形、係数拡大と閉中心への幾何入力の移行、閉和の同変比較、整成分の有限閉被覆と実際の交わりの次元低下 | 有限型スキームの有限次元上界、次元と有限被覆の個数による帰納を閉じる接続 |
| (8) (3.6) | 実現の自然同型を保持する型 | K0・T2 に対する台の比較と二重 fiber の同定 |
| L8b | 比較の retract、分裂 Čech、同変な全次数比較、(3.8) と中心の帰納仮定による軌道貼り合わせ、一般から被約への還元 | Fubini、細分、補題 3.2・3.3、実際の軌道正方形との接続、整→被約の帰納 |
| L8e | 接続先を分離した設計 | E の実構成による (1)–(6) の検証と界面への接続 |

これらは現在の未完部分であり、証明義務を削減した完成条件ではない。
有理不変部分のホモロジー保存を、スペクトルの hG の完成と取り違えない。
Čech nerve の extra degeneracy を、実際の Tot の全構成の完成と取り違えない。
対象ビルドと公理監査の成功だけでは、八つの公理や定理 3.1 の完成を認定しない。

## 21. 被約閉中心と reduction の適用範囲

任意の閉集合の消滅イデアル層から、実際の被約閉部分スキームを構成する。
その包含の像を元の閉集合と同定し、位相同型で次元を移す。
有限型対象内の構造射と包含も構成する。
これにより、一致場所の和の真閉性・次元低下が実際の中心 Z への帰納に使える。
元の有限個の等化子が非被約である場合、そのすべてが Z へ因子分解するとは主張しない。
必要な中心の台と、スキームとしての因子分解を区別する。

有限型対象の射と被約閉中心について、実際の引き戻しを有限型の圏内で構成する。
固有性と補集合上の同型を証明できれば `AbstractBlowupSquare` に包める。
この構成では例外部分が被約であることは仮定しない。
定理 3.1 の軌道射は有限個の切断の標準の非交和から構成した。
各切断の閉埋め込み性と二項非交和の有限性から、有限な添字の帰納で有限性を証明した。
コピーを置換する作用を構成し、section の族の同変性から軌道射の同変性を証明した。
被約な始域の場合は、終域の reduction への持ち上げ後にも有限性と同変性が成り立つ。
section の像が全体を覆うことを入力すれば全射性も得る。
有限型の圏内の軌道射と中心の引き戻しによる抽象 blowup は構成した。
幾何的推移性からの被覆条件は、切断を持つ有限型アフィン対象に対して §28 で接続した。
任意の係数拡大と、アフィン基底を固定した始域の被約化後の被覆は §29 で接続した。
実際の閉中心への幾何的入力は §30 で直接構成した。
中心上の降下の帰納仮定そのものの証明は残る。

補集合上の同型のため、被約な終域の互いに素な有限閉被覆の非交和同型を証明した。
各閉像は残りの有限閉像の和の補集合でもあるため開。
閉埋め込みをその開像へ持ち上げ、被約な終域への全射閉埋め込みの同型性を使う。
有限閉被覆の非交和からの開埋め込みは全射なので同型となる。
さらに、二つの切断の像が同じ点を含むと、その二つの原像点を実際のスキームの
引き戻しへ持ち上げ、切断の恒等式で二射影を等しくし、一致場所へ写す。
この議論で、中心を避ける開集合上の切断の像の互いに素を証明した。
像の被覆も明示すれば、制限切断の非交和からの射が同型になる。
有限非交和の universal colimit 性を成分ごとの開制限の引き戻し正方形に適用した。
これにより、制限の非交和と非交和射の制限の二つを同じ引き戻しの表示として比較した。
標準同型と指定射の可換式により、軌道射自体の制限の同型性も得た。
この過程に前層の降下を仮定していない。
`orbitAbstractBlowup` は中心 V ×_B Z を引き戻しの構造のまま保持する。
中心を V 上でさらに被約化していないため、原典の軌道正方形の幾何に対応する。

一般のスキームの reduction について、被約な始域からの一意な持ち上げを証明した。
その普遍性から関手と包含の自然性、自己同型群を通した G 作用を構成した。
これらの普遍性にはアフィン性も Noether 性も不要。
核の冪零性は Noether スキーム全体で証明した。
有限アフィン部分被覆上の指数の最大値を取り、イデアル層の零を被覆上で判定する。
さらに、有限型の圏内の reduction 関手とその G 作用・包含の同変性を構成した。
Noether 基底上有限型なら各対象が Noether であることを使い、両包含に公理 (3) を適用した。
同変な全単射の不変部分への制限も全単射であることと、指定比較の可換性から、
`Nilinvariant.piDescent_iff_reduction` が「一般 → 被約」の全次数還元を与える。
これは任意の群について成立し、有限群の平均作用素に頼らない。
一般の thickening の底変換、被約な場合の主定理の証明、E の冪零不変性は残る。

## 22. 実際の同変軌道正方形と境界の責務

有限型の圏内の軌道射の始域 W に、コピーの添字を置換する G 作用を構成した。
section の族の同変性から W の構造射が保存され、基底上の自己同型となることを確認する。
中心 V ×_B Z には V の作用と B・Z の自明作用から誘導される作用を構成した。
例外部分 W ×_V (V ×_B Z) には、三頂点の作用を含む cospan の引き戻し作用を用いる。
逆元による逆写像と群の法則、両射影の同変性を普遍性で証明した。
`orbitAbstractBlowupAction` が四頂点と四辺を保持する。

任意の前層 L の逆元の引き戻し表現を適用すると、指定された制限とその差が同変となる。
これは四辺の可換式と反変関手の合成保存から証明した。
`SquareMayerVietoris.withSquareAction` は、境界が同変であることを入力すれば、
既存の `GradedMayerVietoris.Action` に接続する。
その後は有限群の有理不変部分を取った全次数の完全列が利用できる。
境界の同変性は、公理 (2) の実降下から得る長完全列の自然性で供給すべき責務である。
幾何の射の同変性だけで境界も同変だと仮定せず、この入力を明示的に残す。

## 23. 境界の自然性と実際の軌道比較から PiDescent への接続

`NaturalBlowupSequences` は、各抽象 blowup の指定された長完全列と、幾何正方形の
射全体に対する境界の自然性を保持する。
このデータの存在は、L9 の実際の fiber・長完全列と、公理 (2) の実降下から供給する。
群ごとの列の存在をホモトピー引き戻し性の定義へ置き換えたものではない。
群元の逆元が定める正方形の自己射に自然性を適用し、境界の同変性を導いた。
有限群の有理不変部分を取ることで、全次数の完全列とその自然な比較が得られる。

軌道正方形の右下の射 V → B と、中心の第二射影 V ×_B Z → Z から、
基底の恒等中心正方形への実際の立方体を構成した。
上の二頂点の射は正方形の辺との合成で指定し、四つの面の可換性を証明した。
さらに、この立方体の四頂点の射が同変であることを示した。
恒等中心正方形の境界は、指定された差の全射性と完全性から零となる。

`orbit_piDescent_of_fixed_components` は、実際の比較の中項と例外部分の不変部分の
同型性を全次数で供給すれば、公開する `L.PiDescent p action over_base` を結論する。
基底の自明作用の不変部分を元の L(B) と同定し、終域の不変部分の二つの記述を
移す際、比較の値が元の幾何射 p の引き戻しそのものであることも確認した。
中項の比較は、コピーの有限積保存と (3.8)、中心上の降下から供給できるようになった。
例外部分の比較も実際の同変コピー分解から供給できるようになった。
中心上の降下を次元帰納から供給する作業は残る。
この条件付きの軌道段階を、最小公理からの定理 3.1 全体の証明とは数えない。

## 24. 実際のコピー評価と (3.8) の中項比較

`orbitComponent` は W = ⊔_I B の各包含を有限型の圏内に構成する。
軌道射との合成が指定 section、fold との合成が恒等射、作用との合成が添字の置換である。
`orbitSourceIsCoproduct` は、スキームの非交和の desc を基底上の射へ持ち上げ、
その存在と一意性を有限型の圏内で証明する。
コピーを並べた対象だけを非交和と呼び、普遍性を仮定して済ませてはいない。

前層の `copyEvaluation` は、各包含による実際の引き戻しを並べた指定線形写像。
これは逆元の添字置換への同変写像で、fold の固定比較との合成が指定対角写像となる。
この錐が積なら、有理数の自由加群からの射の普遍性で評価の全単射性を証明できる。
ULift ℚ を使い、コピーの添字の宇宙と前層の値の宇宙を無理に同一視していない。
反対圏のコピーの有限積を前層の各次数が保存すれば、この錐が積となる。
ここでの通常の積は有限非交和の値に限り、Čech Tot の代用ではない。
この有限積保存を実際の Zariski 降下から導く責務は残る。

推移的で非空なコピーの置換作用に対し、fold の全次数の指定比較は (3.8) から全単射。
これと中心 V ×_B Z → Z の降下を、幾何的な自明作用の不変部分の比較に移す。
積の不変部分の具体的な同型を通し、実際の比較立方体の中項が全単射となる。
従って中項全体の同型性を追加仮定にする必要はなくなった。
例外部分 W ×_V (V ×_B Z) のコピー分解と、その作用・指定射との両立も証明した（§25）。

## 25. 例外部分のコピーと実際の軌道段階

閉中心の引き戻しに対し、有限型の圏内の持ち上げと両射影の公式を構成した。
またスキームの cofan が非交和なら、有限型の圏内の cofan も非交和となることを、
Over の忘却と充満部分圏の余極限の反映を通じて証明した。

例外正方形と中心の正方形を合成し、E = W ×_V (V ×_B Z) が W ×_B Z の
普遍性も持つことを、スキームの圏と有限型の圏内の両方で証明した。
Z → B → W と Z の恒等射を持ち上げ、各 Z のコピーの E への指定包含を構成した。
スキームの有限非交和の底変換を適用し、これらの包含が非交和の普遍性を持つことを示した。
E と中心の非被約な構造を変更していない。

例外部分の既存の引き戻し作用は、これらの包含を g 倍の添字の包含へ写す。
E → Z は不変で、各コピー上では恒等射となる。
従って Z のコピーの有限積を前層の各次数が保存すれば、(3.8) が実際の E → Z に適用できる。
この指定比較を実際の固定部分の列の例外部分の写像へ移し、その全単射性を証明した。

`orbit_piDescent_of_center` は、中項・例外部分の同型性を個別の仮定に持たず、
自然な blowup 列、B と Z の二つのコピーの積保存、中心上の降下から全次数の降下を結論する。
`Theorem31.lean` もこの実際の軌道段階を公開する。
実降下からの自然な列と有限積保存の構成、一般の基底変更後の切断の被覆を得ること、
有限忠実平坦の Čech 還元と真閉中心上への次元帰納は引き続き未完。

## 26. 閉中心の冪零不変性と被約な始域への移行

Noether な終域への点全射な閉埋め込みの核は、台の判定から nilradical に含まれる。
大域的な nilradical の冪零指数を核へ移し、この射が冪零 thickening であることを証明した。
閉埋め込みと点全射性の底変換安定性を使い、Noether な対象への底変換の第一射影も
冪零 thickening となる。終域の Noether 性のない一般の底変換安定性は主張していない。

有限型の圏内で実際の閉埋め込みの引き戻しを用い、公理 (3) を第一射影と基底の包含へ適用した。
基底と閉部分の自明作用から引き戻し作用を構成し、指定された PiDescent が
冪零な基底変更の前後で同値であることを、任意の係数と整数次数について証明した。
この比較には群の有限性は不要である。

中心の帰納では基底 Z を固定する必要があるため、別に始域だけの被約化の比較を構成した。
始域の Noether 性から被約化の包含に公理 (3) を適用し、基底の恒等射との同変正方形で比較する。
`orbit_piDescent_of_reduced_center` はこの比較を実際の中心 V ×_B Z → Z に適用する。
被約化した始域から同じ Z への降下があれば、構成済みの軌道段階へ入力できる。
正方形そのものの中心を被約化して Cartesian 性を壊す操作はしていない。
被約化した中心の射に対する帰納仮定を、幾何的推移性と次元低下から供給する責務は残る。

## 27. 相異なる移動切断の有限推移的な添字

`TranslatedSectionIndex action s` は、実際の射 s ≫ g の集合の部分型である。
群元をそのまま添字にして切断の重複を許す方式では、一致中心の真閉性を使えない。
この部分型への作用を後合成から構成し、群の積の向きを自己同型の合成と合わせた。
有限性・非空性・推移性を証明し、射の族の単射性も Over の射として証明した。
安定化群による商との同型は使わず、軌道の部分型を直接用いる証明経路である。

元の射 p が作用の基底上にあり s が切断なら、族の全ての射が p の切断である。
有限群、既約被約な基底、分離な終域の構造射、明示した有限次元上界のもとで、
この族の一致中心が次元の下がる実際の被約閉中心となる。

`translatedSection_covering` は、基礎点の各ファイバーの推移性を入力すると、
各点 y と s(p(y)) を結ぶ群元から、重複を除いた切断族の像の被覆を結論する。
この入力は基礎点の性質であり、既存の `IsGeometricallyTransitive` の定義そのものではない。
環のテンソル積上の幾何ファイバーからこの入力を導くことは §28 で実装した。
係数拡大による幾何的推移性の保存と始域の被約化後の被覆は §29 で実装した。
一般の閉中心に対する帰納仮定の構成は残る。

## 28. 既存の幾何的推移性からアフィンの移動切断の被覆へ

`exists_common_geometric_points` は同じ基底点の上にある二点を引き戻しの点へ持ち上げ、
その剰余体の代数閉包を使い、共通の代数閉体からの二つの射として表示する。
両射の基底への合成はスキームの射として等しく、選んだ一点の像は元の二点である。

アフィンの場合、Spec の充満忠実性によりこの二つの射を T から体 Ω への環準同型へ移す。
基底への合成の等式から同じ A 代数構造を使えることを確認し、テンソル積からの射に拡張する。
既存の `IsGeometricallyTransitive A T G` をこの二つの素イデアルへ適用し、
左因子への射影から、同じ基底点上の元の二つの素イデアルを群元で結ぶ。
新たな推移性の公理や、代数閉体の選択を仮説に追加していない。

Spec の反変性に合わせて g の作用を g⁻¹ の環作用の comap とし、左群作用を構成した。
その作用が Spec A 上にあることを代数射の係数の保存から証明する。
有限型 A 代数を前層の定義域内の有限型アフィン対象とし、この作用を持ち上げた。
`affine_translatedSection_covering` は、既存の幾何的推移性と実際の切断から、
重複を除いた移動切断の像が全体を覆うことを結論する。
基底変更後と始域の被約化後の被覆へは §29 で接続した。
有限忠実平坦な Čech 還元による切断の存在、一般の閉中心への帰納の適用、
主定理全体の証明は未完である。

## 29. 係数拡大と始域の被約化後の被覆

B ⊗_A T では B を固定し T を動かす群作用を実際のテンソル積の map から構成した。
作用の法則と B 線形性を証明し、標準の B 代数構造を保持した。
幾何ファイバー (B ⊗_A T) ⊗_B Ω と T ⊗_A Ω の A 代数同型を、
因子の交換と係数拡大の打ち消しから構成し、その指定同型が群作用と可換であることを証明した。
この同型の素イデアル上の写像を使い、既存の `IsGeometricallyTransitive` が
任意の A 代数 B への係数拡大で保存されることを証明した。
B の平坦性、有限型性、Noether 性はこの保存に不要である。

有限型 A 代数 T に対しては、変更後の B 代数も有限型となる既存定理を使う。
従って変更後に切断があれば、実際の有限型アフィン対象の移動切断で全体を覆える。
ここまででは係数拡大前の切断から変更後の切断を構成する Čech 還元は扱っていない。

別に、基底を固定した始域の被約化は、同変な包含の点の単射性から
基礎点の各ファイバーの推移性を保つことを証明した。この点の比較に Noether 性は不要。
被約な始域からの射の reduction への持ち上げを有限型の圏内にも構成し、包含との合成公式を証明した。
基底が被約なら元の切断は始域の被約化へ持ち上がり、同じ基底上の切断となる。
`affine_baseChange_liftedSection_covering` は、元の切断から構成したこの切断の移動が
被約化した始域全体を覆うことを、既存の幾何的推移性から結論する。
実際の閉中心への幾何的入力は §30 の直接的な経路でも供給した。
次元帰納を閉じる責務は残る。

## 30. 実際の閉中心への直接移行と閉和の正方形

閉埋め込みの底変換である第一射影は、基礎点上で単射である。
従って元の射の点のファイバーを結ぶ群元を選び、第一射影の同変性と単射性を使うと、
閉中心への実際の引き戻しの点のファイバーの推移性を直接証明できる。
中心のアフィン表示やテンソル積との別の同型を構成する必要は、この幾何的入力にはない。
これは閉底変換の点の推移性に関する証明経路であり、一般の基底変更の幾何的推移性を
単なる基礎点の推移性で置き換える主張ではない。

元の切断は、中心の包含との合成と中心の恒等射を引き戻しへ持ち上げることで、
中心上の実際の切断となる。第二射影との合成の恒等式も証明した。
中心が被約ならこの切断を引き戻しの始域の被約化へ持ち上げ、
構成済みの作用の移動による被覆を得る。
これらを一致中心の包含へ適用し、`orbitCenterAction`、実際の第二射影、
`orbitCenterSection` に対して直接証明した。中心の非被約な構造は変更していない。

また被約な終域を二つの閉部分が覆うとき、一方の閉部分の補集合では他方の閉埋め込みが
点全射となる。その開集合の被約性から制限は同型であり、閉埋め込みの固有性と合わせて
`closedCoverAbstractBlowup` を構成した。交わりは元の二つの閉埋め込みの実際の引き戻し。
`NaturalBlowupSequences.closedCoverSequence` は、この正方形へ指定データを適用し、
境界と三箇所の完全性を持つ全整数次数の列を供給する。
閉和の同変な比較と、三つの局所降下からの貼り合わせは §31 で実装した。
実降下から自然な列のデータを供給する責務、および次元帰納は残る。

## 31. 閉和の同変な比較と指定降下の貼り合わせ

二つの閉部分 Y・Z が基底 B を覆うとき、任意の射 f : V → B への引き戻しの
第一射影の像は元の像の逆像である。この公式から、始域 V も二つの実際の閉部分で覆われる。
V が被約なら、この引き戻した閉被覆も抽象 blowup 正方形を与える。
元の被覆の正方形への比較では、三頂点の射は f と二つの第二射影で指定する。
残る交わりの射は引き戻しの普遍性で構成し、四つの面の可換性を証明した。

f が基底上の群作用を持つとき、引き戻した二つの閉部分と交わりに既存の引き戻し作用を入れる。
元の閉被覆の四頂点には自明に作用する。二つの第二射影と f の不変性から、
交わりへの射の不変性も比較先の引き戻しの普遍性で導く。
四つの比較の同変性を入力仮定として追加してはいない。

自然な blowup 列のデータにこの同変な立方体を適用し、有理不変部分を取ることで、
境界も含む全整数次数の列の比較を得る。
`closedCover_piDescent` は、二つの第二射影と交わりへの指定射の三つの PiDescent を入力し、
中項を二つの局所比較の積、交わりを三つ目の比較として五項補題を適用する。
最後に自明作用の不変部分と指定比較の同定を通じ、元の幾何射 f の PiDescent を結論する。
元の射の降下や無関係な中項全体の同型性を追加仮定にはしていない。

基底 B と始域 V の被約性は閉被覆の抽象 blowup を作るために明示する。
二つの部分と交わりは非被約でもよく、必要なら構成済みの reduction の比較を適用する。
有限な既約成分分解と次元低下を組み合わせて三つの局所降下を供給すること、
実降下から自然な列を構成すること、Čech 還元と主定理全体の証明は残る。

## 32. 整成分の有限閉被覆と二つの帰納の幾何データ

`IrreducibleComponentIndex` は基礎空間の既約成分の部分型である。
各成分に消滅イデアル層による被約閉構造を入れ、台との同相から既約性を移すことで、
同じ基底 S 上の整な有限型対象 `integralComponent` を構成した。
Noether 空間では添字は有限であり、各成分の閉包含の像が元の対象全体を覆う。
元の対象の被約性はこの構成そのものには不要である。

一つの成分 c を選び、他の全成分の有限和を `componentRemainder` とする。
既約な閉集合が有限和に含まれるとき一つの項に含まれることと、成分の極大性から、
c は残りに含まれない。従って残りは真閉で、元の対象が既約でない場合には c の像も真閉である。
この二つの部分は全体を覆い、被約な元の対象に対する実際の抽象 blowup 正方形を与える。

実際の交わりを c へ送る第一射影は閉埋め込みで、その像は真閉である。
閉像との同相により、交わりが非被約のままでも次元低下を証明した。
元の対象の次元が自然数 d 以下なら、各整成分の次元も d 以下で、交わりの次元は d 未満となる。
空の交わりの次元を零へ丸めてはいない。

残りには被約閉構造を入れる。閉集合の包含が与えるイデアル層の包含を使い、
各 d ≠ c の整成分から残りへの実際の射 `componentToRemainder` を構成した。
元の対象への合成が成分の閉包含であることから、この射も閉埋め込みである。
これらの像が残り全体を覆うことを、元の対象への包含の点の単射性で証明した。
残りを覆う元の成分の集合は有限で、その個数は一つ減る。
これは新しいスキームの既約成分との同一視を仮定することなく、有限被覆の個数を使う帰納へ入力できる。

これらの幾何データを閉和の三つの局所降下へ供給して、
次元と有限被覆の個数による帰納を閉じる工程は残る。
自然な blowup 列と有限積保存を実降下から構成する工程、Čech 還元、(3.6) の接続も未完である。

## 33. 交わりの帰納入力と被約化・空の基底

`fiberTransitivity_of_injective_square` は、同変な可換正方形で始域側の射が点上単射なら、
元の射の点のファイバーの推移性を新しい射へ移す。
基底側の射が単射または全射であることは要求しない。
被約化の包含の正方形に適用し、始域と基底の両方を被約化した射でも点の推移性が保たれることを証明した。
元の切断の恒等式には被約化関手を適用でき、被約化した射の切断を得る。
被約化の次元保存も、台との同相から有限次元や Noether 性を使わずに証明した。

閉和の交わりへの指定比較の切断は、二つの閉部分上の切断を交わりへ持ち上げて構成する。
比較先の二つの射影で検査し、指定比較との合成が恒等射であることを、有限型の圏内の等式として証明した。
推移性は、左側の閉部分上の点の推移性と、交わりからの第一射影の同変性・点の単射性から移す。
これらは比較立方体の指定射そのものについての証明であり、別の同型なモデルへ変更していない。

`closedCoverIntersection_reduced_covering` は、構成した切断と点の推移性を両側の被約化へ移し、
その切断の移動による実際の像の被覆を得る。
従って非被約な交わり上の局所降下を被約な場合の帰納へ戻す際、
切断・推移性・次元の幾何条件を追加仮定にする必要がない。
PiDescent 自体の被約化との同値には、既存の公理 (3) と Noether 性に関する定理を適用する。

また、指定引き戻しが全次数で全単射なら不変部分への値域制限も全単射となることを証明した。
同型射の場合は前層の同型保存からこれを適用できる。
空の基底へのスキームの射は同型であり、有限型の圏への忘却が同型を反映することから、
元の有限型の圏内の射も同型である。これにより空の基底の PiDescent を得る。
空対象での前層の値を零とする公理や有限積保存は、この始点には使っていない。
有限閉被覆と次元の帰納を閉じる工程、および実降下・Čech 還元・(3.6) の接続は残る。

## 34. 整な基底の段階を低次元から閉じる

`SectionedDescentBelow L G d` は、基底次元が自然数 d 未満である切断を持つ射に対する
指定 PiDescent の帰納仮定を量化する。始域は S 上分離な有限型対象で、
指定作用・基底上の不変性・切断・点のファイバーの推移性を保持する。
これは最小公理の一つでも追加公理でもなく、厳密に低い次元だけに適用する帰納仮定の型である。

整な基底 B、被約な始域 V、元の切断 s に対し、相異なる移動切断の添字を実際に選ぶ。
族の単射性・有限性・推移性・像の被覆を構成済みの証明から供給する。
一致中心 Z の実際の被約閉構造は B より次元が低い。
V ×_B Z の指定作用と射影には元の切断から切断と点の推移性を供給し、
その始域が S 上分離であることも閉埋め込みの合成から確認する。
従って低次元の帰納仮定を中心の射に適用でき、中心上の PiDescent を得る。
既存の実際の軌道段階へこれを入力して、V → B の全次数 PiDescent を結論する。
中心上の降下を、低次元とは独立した入力仮定に残してはいない。

この段階で使う有限積保存は、前層の各次数の有限非交和に対する実降下から供給すべき条件である。
通常の有限積を Čech Tot の代用品として使ってはいない。
自然な blowup 列も、実際の降下と L9 の長完全列から供給すべき条件として明示する。

Noether な S と公理 (3) があれば、始域 V が被約でない場合も扱える。
整な B は被約なので s を V_red へ持ち上げ、始域だけを被約化した射に被約な場合を適用する。
包含の同変性による点の推移性の移行、切断の合成公式、始域の分離性を実際に確認し、
公理 (3) の指定比較で元の V → B へ戻す。

`sectionedDescentBelow_zero` は、零より低い次元の仮定が空の基底の場合だけであることを使う。
点が存在すればその一点の閉包が既約閉集合となり、Krull 次元は非負となる。
したがって空の基底の指定降下から、この帰納の始点を供給できる。
被約で可約な基底の有限閉和を組み合わせる成分数と次元の帰納は §35 で完了した。
実降下からの条件の供給、Čech 還元、(3.6) と E への接続も未完である。

## 35. 成分数と次元の二つの帰納の完了（切断を持つ場合）

有限な既約閉被覆の各既約成分は、被覆の一項に含まれ、極大性によりその項と等しい。
この項を各成分について選ぶと、成分の添字から被覆の添字への単射が得られる。
これにより既約成分数は有限被覆の項数以下であることを、空の場合も含めて証明した。
残りの閉和に他の元の整成分による被覆を適用し、残り自身の既約成分数が元より少ないことを証明した。
新旧の既約成分を同一視する仮定は使っていない。

被約な基底と被約な始域について、一つの整成分・残り・交わりの三つの局所降下を供給する。
整成分には §34 の整な段階、残りには厳密に少ない成分数の仮定、
交わりには厳密に低い次元の仮定を適用する。
引き戻した始域と交わりの S 上の分離性も、閉包含の合成から確認した。
構成済みの閉和の貼り合わせに三つを入力して元の射の指定降下を得る。
始域の被約性は、被約な基底からの切断の持ち上げと冪零不変性で外す。

`reducedBase_piDescent_of_below` は実際に成分数の強い自然数帰納を実行する。
残り自身の成分数の減少を使うので、成分数に関する仮定は結論に残らない。
さらに始域と基底を同時に被約化して、切断・点の推移性・次元を保ちながら被約な場合へ戻す。
公理 (3) の指定比較で元に戻すと、一般の基底に対する `piDescent_of_below` を得る。

`sectionedDescentBelow` は外側の次元上界に関する自然数帰納を実行する。
零の始点は空の基底から得る。次の段階では、次元が d + 1 未満なら d 以下であることを使い、
直前までに構成した低次元の仮定を一般の基底の一段へ適用する。
従って全ての自然数 d に対する帰納仮定が実際に構成される。

`sectioned_piDescent` の結論は、指定された切断を持つ射の全係数・全整数次数の PiDescent。
中心上・閉部分上・交わり上の降下、低次元の帰納仮定、成分数の帰納仮定を外部入力には残さない。
数学的入力は Noether な S、S 上分離な始域、有限な群、基底上の指定作用、
切断、点の各ファイバーの推移性、明示した有限な基底次元上界である。
前層に関する入力は、自然な blowup 列のデータ・各次数の有限積保存・冪零不変性。
自然な列と有限積保存を実際の降下から供給すること、切断を持たない射への Čech 還元、
最小公理 (1)–(8) 全体、(3.6) と K0・T2・E の接続は未完である。
この条件付きの切断を持つ段階の完成を、定理 3.1 全体の完成とは呼ばない。

## 36. 環の分裂とアフィン底変換の全次数降下

`affineOverObject` と `affineAlgebraOverObject` は、任意の固定した S 上で
Spec A と Spec T を有限型の圏の対象にする。構造射を保持したまま、
指定射影と元の環の群作用も同じ圏内に構成する。
A 代数射 r : T → A の係数保存から Spec r が実際の切断となることを証明した。
`affine_split_piDescent` はこの切断と元の幾何的推移性を使い、§35 の完成した帰納を適用する。
前層を別の基底上の任意の前層に交換する操作はしていない。

A 代数射 φ : T → B があれば、テンソル積の普遍性により
`tensorBaseChangeRetraction φ : B ⊗_A T →ₐ[B] B` を実際に構成できる。
純テンソル b ⊗ t の像は b · φ(t) である。
既存の係数拡大の推移性と組み合わせ、Spec B が同じ S 上の有限型かつ分離な対象で、
その次元に明示した有限上界があれば、Spec(B ⊗_A T) → Spec B の指定された
全係数・全整数次数の PiDescent を元の L に対して証明した。
自己底変換では φ を T の恒等射とし、乗法による分裂から同じ結論を得る。
左因子 B または T は固定し、右因子だけに元の群作用を適用する。

`tensorSpecSquare_isPullback` は Mathlib の `pullbackSpecIso` の二射影の公式を使い、
指定された係数射影と右射影が実際のスキームの Cartesian 正方形を成すことを証明する。
右射影は元の Spec T の作用と同変であり、左射影は Spec B 上の作用である。
単なる対象同型の存在だけを使って引き戻しであると称してはいない。

ここで完成したのは、分裂を持つ底変換の全次数降下と、その幾何的な正方形である。
有限型の圏内の Čech 各段との関手的な比較、Tot と引き戻しの Fubini、
分裂余単体対象の実降下、細分補題、および元の切断を持たない射への還元は残る。
自然な blowup 列・有限積保存を実降下から供給する工程と、有限次元上界の接続も残る。
最小公理 (1)–(8) 全体、(3.6)、K0・T2・E の接続も未完であり、
本段階を論文 補題 3.2 または定理 3.1 全体の完成とは呼ばない。

## 37. 前層の定義域内の同変な底変換正方形

`affineTensorObject` は Spec(B ⊗_A T) を、左因子 B を通る構造射で同じ S 上の
有限型対象にする。`affineTensorFst` と `affineTensorSnd` はそれぞれ実際の
係数射影と右因子への射影をこの圏内に持ち上げた射である。
右射影の構造射との可換性は §36 の Spec の正方形から導出する。
Over の忘却と充満部分圏の包含は極限を反映するので、
指定された四辺がこの有限型の圏内でも引き戻しを成すことを証明した。
従って、単にスキームとして同型な対象へ前層を勝手に適用しているのではない。

`affineTensorAction` は左因子を固定した右因子上の既存の作用を持ち上げる。
第一射影の基底上の不変性と、第二射影の元の作用との同変性をこの圏内の等式で証明した。
指定された A 代数射 T → B から `affineTensorSection` を構成し、
第一射影との合成が恒等射であることもこの圏内で証明した。
有限型対象に保存済みの局所有限型性と準コンパクト性の証明は、
反復するアフィン底変換の構成に明示的に渡している。

`affineTensorFst_piDescent` は、指定されたこの第一射影そのものについて、
元の L の全係数・全整数次数の降下を結論する。
基底の明示した有限次元上界、Noether な S と分離な構造射、
有限な群、幾何的推移性、自然な blowup 列・有限積保存・冪零不変性が入力である。
Čech 各段の関手的な比較、分裂余単体対象の実降下、Fubini・細分による
元の切断を持たない射への還元は引き続き未完である。

## 38. 有限型の圏内の実際の二重 Čech 図式

有限型対象間の射は局所有限型である。これは基底への合成の局所有限型性から導き、
Noether 性を必要としない。Noether 基底上では有限型対象の underlying scheme は Noether であり、
その始域を持つ全てのスキームの射は準コンパクトとなる。
従って任意の二射の実際の引き戻しも同じ基底上の有限型対象として構成できる。
第一・第二射影を Over の射に持ち上げ、スキームへの忘却による極限の反映から
有限型の圏内での引き戻しの普遍性を証明した。
基底自身の恒等構造射はこの圏の終対象である。
終対象と全ての引き戻しから `finiteTypeSchemes_hasFiniteLimits` を得る。

この有限極限により、`finiteTypeAugmentedCech` は元の前層の定義域内の
実際の増強 Čech nerve となる。各非増強段には零番目の射影から X への射がある。
増強の成分で元の f を底変換し、この零番目の射影を持ち上げに使うと、
`finiteTypeCechStageSplitEpi` の実際の切断を構成できる。
この切断を使い、各行の Čech nerve の全次数の extra degeneracy を構成した。
同じ反変前層を適用した像にも extra degeneracy と全ての分裂の恒等式が移る。

`finiteTypeCechBaseChange` は各段の底変換の Arrow を、全ての単体射に対する
引き戻しの map で束ねた実際の関手である。
恒等射と合成の保存は二射影と元の Čech の関手性を用いて検査した。
増強 Čech nerve 関手を合成して `finiteTypeDoubleCech` を構成し、
さらに元の前層を適用して二重図式全体の像を構成した。
零番目の射影を選ぶ切断の外側の単体射についての自然性は主張していない。
二重図式の射の構成に切断の自然性は使っていない。

ここで作った極限は幾何的な通常の極限であり、前層の値域の Tot の代用ではない。
各段での作用・推移性・分離性・有限次元上界を既存の切断つき全次数降下へ渡す工程、
実際の Tot の分裂降下・Fubini・細分による元の射への還元は残る。
自然な blowup 列・有限積保存の導出と、最小公理全体・(3.6)・E の実現も残る。

## 39. 指定引き戻しへの同変な移行と Čech 比較の自然性

`isPullback_isoPullback_equivariant` は任意の圏で、四頂点の指定作用と
二射影の同変性から、Cartesian モデルと指定引き戻しの標準同型の同変性を証明する。
比較先の作用を共役で新しく定義する方法は使っていない。
比較先は既存の `pullbackAction` であり、同変性を二射影で実際に検査する。

アフィン底変換に適用すると、テンソル積モデルの作用と指定引き戻しの作用を
`affineTensorPullbackIso_equivariant` で結べる。
指定第一射影への比較は元の L を適用した同変正方形を成す。
標準同型の引き戻しの全単射性と不変部分の比較の自然性により、
モデルの PiDescent を実際の引き戻しの第一射影へ移した。
`affine_pullback_piDescent` は指定された作用と幾何射の全係数・全整数次数の主張である。
環の射 T → B による分裂、明示した次元上界、有限型性・分離性・Noether 性、
有限な群と幾何的推移性、自然な blowup 列・有限積保存・冪零不変性を入力する。

`finiteTypeCechStageAction` は実際の Čech 各段で底変換した元の始域に作用する。
Čech の基底の段自身は固定する。これは Čech の全座標への対角作用とは異なる。
第二射影はこの作用について基底上にある。
`pullbackAction_map_trivialBase` は基底変更の射と元の始域の作用の可換性を、
二つの pullback.map の合成公式から証明する一般補題である。
これを適用して、全ての外側の単体射について段間の射の同変性を証明した。
切断を選ぶ零番目の射影が外側の射について自然であることは使わない。

この同変性を指定比較の一般の自然性へ渡し、元の L の全係数・全整数次数について
`finiteTypeCechStageComparison_naturality` を得る。
各段の比較の左辺・右辺はいずれも元の前層の幾何射からの引き戻しであり、
無関係な群の抽象同型に置き換えてはいない。

一般の実際の Čech 各段に対する幾何的推移性の移行、分離性と有限次元上界の供給は残る。
通常の点のファイバーの推移性だけを任意の底変換で保存すると仮定してはいない。
実際の Tot の分裂降下・Fubini・細分、実降下からの自然な列と有限積保存、
最小公理全体、(3.6)、K0・T2・E の接続も引き続き未完である。

## 40. 実際の Čech 各段のアフィン性・分離性・有限次元

`finiteTypeOverInclusion` は同じ S 上の有限型の圏から Over S への包含である。
構成済みの引き戻しモデルは両圏で Cartesian であり、基底の恒等構造射による
終対象も保たれる。従ってこの包含は有限極限を保つ。
Over からスキームへの忘却は連結極限を保つので、合成により
`finiteTypeSchemesForget_preservesFiniteConnectedLimits` を得る。
スキームへの忘却は終対象を保つとは主張しない。

`finiteTypeLimit_isAffine` は、元の有限型の圏で指定した有限連結な極限錐を
スキームの極限錐に写し、Mathlib のアフィン対象の極限の定理を適用する。
Čech の有限 wide pullback では図式の全頂点が元の始域または基底である。
両者がアフィンなら、実際の各非増強段もアフィンとなる。
各段への底変換の始域についても、三頂点の cospan に同じ議論を適用する。
アフィンなスキームは絶対分離的なので、底変換の始域の S への構造射も分離的である。
S 自身の分離性は入力していない。

Noether 環 A に自然数の次元上界 d があるとする。
有限型 A 代数 T を有限変数多項式環の商として表示し、全射による次元の不増大と
dim A[X₁,…,Xₙ] = dim A + n を使って、Spec T の自然数上界を実際に供給した。
A が局所 Noether の場合、Krull の高さ定理から極大イデアルの最小生成元数が上界となる。
一般の Noether 環の有限次元性を主張していない。

実際のアフィンスキーム X の有限型射 X → Spec A については、
isoSpec の逆射と構造射の合成の Spec.preimage により Γ(X,⊤) に A 代数構造を入れる。
この射の局所有限型性から座標環の有限型性を証明し、上記の環論的な上界を適用する。
isoSpec の同相による次元の等式で、指定された X 自身の上界へ戻す。
従って座標環の有限型性や始域の有限次元性は追加仮定に残らない。

`localNoether_finiteTypeCechStage_dimension_bound` は、局所 Noether な A の Spec を基底とする
実際の Čech 各段へこれを適用する。
増強射の局所有限型性は、同じ S 上の有限型対象間の射であることから導く。
各段の有限次元上界を結論として供給するので、後の次元帰納へそのまま渡せる。

幾何的推移性を実際の各段の底変換へ移す工程は残る。
これを供給して完成した切断つき降下を各段へ適用し、さらに Tot の実降下・Fubini・細分で
元の射へ戻す必要がある。最小公理全体・(3.6)・K0・T2・E の接続も未完である。

## 41. 幾何的推移性の実際の Čech 各段への供給と全次数降下

同変な始域・基底の同型の正方形で、点のファイバーの推移性を移せることを証明した。
逆同型で二点を戻し、基底同型の点の単射性で同じファイバーにあることを検査する。
始域だけが点上単射の正方形による移行も、underlying scheme に対して証明した。
これらは通常の点の推移性の任意の底変換での保存を仮定する補題ではない。

元の環 A → T の幾何的推移性を、任意の A 代数 B へ係数拡大する。
既存の環論的な係数拡大の定理により、B ⊗_A T の Spec B 上で点のファイバーは推移的になる。
基底 Z に Spec B からの構造射を保つ同型があれば、テンソル積の二射影の
Cartesian 正方形を Z 上へ移せる。
モデルの両射影の同変性から指定引き戻しへの標準同型も同変となり、
実際の pullbackAction の点の推移性を得る。

アフィンな Z → Spec A では、Γ(Z,⊤) に構造射から A 代数構造を入れ、
isoSpec の逆を使って上記の表示を実際に供給する。
従って座標環の表示や底変換後の推移性を追加仮定に残さず、
任意のアフィン基底変更の点の推移性を元の幾何的推移性から証明できた。
この段階には有限型性・Noether 性・群の有限性は不要である。

有限型の圏の指定引き戻しの Cartesian 性を、忘却の極限保存でスキームへ移す。
有限型の圏の pullbackAction の二射影の同変性も忘却し、
underlying scheme の指定引き戻しへの標準同型との同変性を検査した。
この同型の点の単射性で推移性を元の有限型対象へ反映する。
従って作用を別の共役作用へ置き換えることなく、元の圏の指定作用を保持できる。

実際の Čech 各非増強段は §40 でアフィンと証明済みであり、
この任意のアフィン基底変更の推移性を各段の指定射へ適用できる。
`affineCechStage_transitive` は、元の幾何的推移性から実際の各段の推移性を導く。

`affineCechStage_piDescent` は、局所 Noether な A の Spec 上の有限型アフィン射について、
実際の各非増強 Čech 段での底変換の全係数・全整数次数の PiDescent を証明する。
切断は零番目の射影、点の推移性は本節、始域の分離性と自然数の次元上界は §40 から供給する。
段ごとの切断・推移性・分離性・有限次元上界・降下のいずれも独立した仮定に残らない。
自然な blowup 列・各次数の有限積保存・冪零不変性は、引き続き明示した前層の条件である。
自然な列と有限積保存は実際の導来降下から供給すべき帰結であり、その導出は未完である。

本節で完了したのは、実際の二重 Čech 図式の各行の切断つき全次数降下である。
元の射への Tot・Fubini・細分による還元、有限平坦 transfer の導来図式への接続、
最小公理全体・(3.6)・K0・T2・E の接続は残る。
各行の次数ごとの同型から Tot と π_* の交換を仮定してはいない。

## 42. Čech の底変換と二重図式全体の軸交換

L9 の現在の計画では L9e の Tot・hG は未着手であることを確認した。
L8 側ではそれらの実構成を置き換えず、先行できる幾何的な Čech 比較を証明する。
通常の極限を Tot と呼ぶ代用品は導入しない。

Arrow の正方形が Cartesian であることは、その始域・終域の正方形で検査できる。
Comma の二射影による極限の共同反映でこれを証明した。
底変換の射 X ×_Y Z → Z は、Arrow 内で元の f と恒等射 𝟙 Z の引き戻しとなる。
増強 Čech nerve は既存の右随伴であり、従ってこの引き戻しを保つ。
これにより増強図式全体の実際の Cartesian 正方形を得た。

恒等射の Čech nerve の各段は、恒等射の族の wide pullback である。
普遍性から増強成分の逆射を構成し、全ての成分が同型であることを証明した。
従って指定増強を hom とする `identityCechIso` は定数図式との自然同型となる。
増強を忘れる関手の引き戻し保存も検査し、この同型で底変換の正方形の基底を移す。
`baseChangeCechIso` は、底変換した射の実際の Čech nerve と、
元の Čech nerve の定数図式による引き戻しとの図式全体の標準同型である。

元の有限型の圏の二重 Čech に適用すると、各二重次数の対象は
二つの元の Čech 段の増強のファイバー積となる。
指定二射影を保持して交換同型を構成し、二回の合成が恒等となることを証明した。
二射影の内側・外側の全ての単体射についての自然性も証明し、
交換が両方向の単体射と可換することを検査した。
積添字に uncurry した `doubleCechBifunctor` に対して、
`doubleCechSwapNatIso` は二重図式全体と軸を交換した図式との自然同型となる。
段ごとの同型の存在だけを図式全体の同型と呼んではいない。

本節の結果は、Fubini・細分に使う幾何的な比較の入力である。
値域の実際の Tot の Fubini、分裂降下、有限平坦 transfer の図式との接続、
元の切断を持たない射への還元は残る。
実降下からの自然な blowup 列と有限積保存、最小公理全体・(3.6)・K0・T2・E も未完である。

## 43. 平行な細分比較のホモトピーと相互細分のホモトピー逆

同じ基底 Y への二つの射 f : X → Y、g : W → Y と、
基底上の二つの持ち上げ a,b : X → W を取る。
`refinementCechMap` は指定された持ち上げからの実際の Čech 比較である。
持ち上げの一致は要求せず、この二つの比較の間に実際の単体ホモトピーを構成した。

ホモトピーの射は、出力座標を一つ重複させ、切替位置の左側では a、右側では b を使う。
`cechMixIndex` は元の座標と、どちらの比較射を使うかのタグを保持する。
最初・最後の面、切替位置の前・中央・後の面、前後の退化射の七つの関係を
有限順序集合の算術に還元して証明した。
実際のスキームの射の証明では、この有限添字の等式を使って各射影を検査する。
共通の基底へも lift の合成公式で一致し、wide pullback の普遍性で射の等式となる。

`refinementCechHomotopy` は Mathlib の `SimplicialObject.Homotopy` の全ての条件を満たす。
各次数の写像の存在だけをホモトピーと呼んではいない。
全ての面射・退化射の整合性と、二つの指定比較への端点の恒等式を検査済みである。

さらに基底上の持ち上げ a : X → W と b : W → X が両方向に存在するとする。
これらの合成が恒等射であることは仮定しない。
`refinementCechMap_id` と `refinementCechMap_comp` で比較の恒等射・合成の保存を確認し、
合成持ち上げと恒等持ち上げの間のホモトピーを適用する。
これにより Čech 比較の二つの合成はそれぞれ恒等写像にホモトピックとなる。

任意の同じ反変前層を、その反対圏への共変関手として適用できる。
実際の単体ホモトピーを写すことで、前層の像でも両側のホモトピー逆を得る。
これらは実際の Tot のホモトピー不変性に供給する細分比較の入力である。
Tot の実降下や任意の細分の降下保存を、この結果だけで結論してはいない。
L9 の実際の Tot・hG とその性質、Fubini、transfer の自然な図式、
実降下からの自然な列・有限積保存、最小公理全体・(3.6)・K0・T2・E の接続は残る。


## 44. 元の前層の実際の底変換と Čech transfer retract

固定した f : X → Y に対し、Over Y の底変換関手は Z → Y を Z ×_Y X → Y に写す。
元の反変前層をこの関手で制限して `baseChangedPresheaf` を構成した。
Over の底変換随伴の余単位を元の前層で写すことで、全ての基底変更とその射に自然な
`baseChangePresheafPullback` を得る。その成分は実際の第一射影の引き戻しである。
基底自身の底変換と X の標準同型も、現在選択された引き戻しの二射影から直接構成した。
この同型のもとで基底での pullback は元の f の引き戻しと一致する。

`BaseChangeTransfer` は底変換後から元への自然変換を保持する。
これは公理 (4) の自然性部分の入力であり、有限平坦 transfer の存在や射影公式の証明ではない。
局所自明化後の正の rank について rank 公式が与えられると、有理数で正規化して
前層そのものの retract を構成する。一般の有限平坦射に大域的な定数 rank 公式を仮定してはいない。

基底上の任意の図式について、その構造射から指定増強を作り、前層についての自然性を証明した。
この自然性により前層 retract は増強比較の矢の圏の retract へ移る。
実際の Čech nerve の指定増強を Over の構造射にした図式へ適用し、
`BaseChangeTransfer.cechAugmentationRetract` を得た。増強先の基底の値も同時に含む。
任意の図式関手で写しても retract は保たれ、底変換後の比較が全次数観測で同型なら
元の指定比較も全次数で同型となる。

この結果だけで補題 3.2 の実降下が完成したとはしない。
底変換後の係数図式と底変換した被覆の Čech 図式との増強を保つ自然同型、
L9 の実際の Tot・π_*・hG とホモトピー不変性、Fubini・分裂降下を接続する必要がある。
§44–45 の正規化経路では有理線形値域の実現が別途必要で、L9 のスペクトル圏の線形性を仮定しない。
§46 では代わりに観測後の両端の rank 公式から正規化する経路を追加する。
有限平坦 transfer 自体、射影公式、自然な blowup 列と有限積保存の実降下からの導出、
最小公理全体・(3.6)・K0・T2・E の接続は残る。


## 45. transfer 図式と実際の底変換被覆の増強 Čech の接続

§44 に残していた底変換係数図式と実際の底変換被覆の Čech 図式の同型を構成した。
`baseChangeCech_isPullback` を各単体次数で評価し、実際の底変換被覆の段と
元の増強段の引き戻しとの標準同型を得る。
この同型は元の Čech への指定比較と、底変換基底 X への指定増強を保つ。
Over の底変換関手の射は実際の二射影による lift なので、
その二射影で検査することで、全ての面射・退化射を含む自然性を証明した。
`cechBaseChangeGeometryIso` は二つの幾何図式全体の自然同型となる。

さらに底変換された増強は、基底自身の引き戻しから X への標準同型のもとで
実際の底変換被覆の増強と可換することを証明した。
元の同じ反変前層でこれを写し、増強先の値の同型と図式全体の自然同型を組み合わせる。
`cechBaseChangeAugmentationIso` は指定増強比較の矢の圏の同型である。
したがって各段の値の同型だけから増強や全図式の同型性を主張してはいない。

transfer の比較射 retract とこの矢の圏の同型を合成し、
元の被覆の指定 Čech 比較が、実際の底変換被覆の指定比較の retract となることを証明した。
実際の図式関手の像で底変換被覆の比較が全次数同型であれば、元の比較も全次数同型となる。
ここでは底変換被覆そのものの降下は入力であり、実際の Tot の分裂降下は未接続である。
通常の極限を Tot と呼ぶ置換も π_* と Tot の無証明の交換も行っていない。

L9 の実際の Tot・π_*・hG、ホモトピー不変性、Fubini・分裂降下、
有理線形値域での実際の transfer と局所 rank 公式の供給、
実降下から自然な blowup 列と有限積保存を導出する部分、
最小公理全体・(3.6)・K0・T2・E の接続は引き続き残る。

§45 の保存検証：集約対象ビルド成功。公理監査は 115 モジュール・1420 宣言で標準三公理のみ。
全体ビルドも 10024 ジョブで成功し、全て `set -eo pipefail` で終了コード 0 を確認した。


## 46. 元の値域の線形性を要求しない観測後の正規化

§44–45 の rank の逆数倍による正規化は、前層の値域の有理線形性を使っていた。
L9 の実際のスペクトル圏の線形性を L8 側で仮定することを避けるため、
元の圏には単に射・自然変換を要求する別の正規化経路を証明した。

一般の圏で i : A → B、r : B → A の合成 i ≫ r が同型なら、
r にその合成の逆を後合成することで A を B の retract にできる。
自然な比較の両端で往復の合成の像が同型であれば、
往復の二つの自然性正方形の合成は矢の圏の同型となり、比較射の retract が得られる。
これを各整数次数の観測先で実行し、観測後に両端の合成が同型なら、
比較先の全次数同型から元の比較の全次数同型を導いた。
有理加群値の観測後に正の局所 rank 倍の公式があれば、この合成は同型である。

この操作を実際の Čech 増強比較に適用した。
増強先の定数図式と Čech 図式に実際の図式関手を適用した二つの関手を定義し、
それらの自然な増強比較に観測後の rank 正規化を適用する。
§45 の増強比較の矢の圏の同型により、底変換被覆の実際の比較の降下を入力できる。
`BaseChangeTransfer.piCechComparison_of_observedRank` は、
前層の値域 V と図式関手の値域 D の加法性・有理線形性を要求しない。

二つの rank 公式は実際の図式関手の像を観測した後の公式として明示する。
各段の rank 公式から Tot の像の公式を無証明で推論してはいない。
実際の有理化・transfer・図式関手からこの公式を供給する部分は残る。
この経路は π_* と Tot の交換も通常の極限による Tot の置換も行わない。
L9 の実際の Tot・hG と分裂降下・Fubini、実降下からの自然な列・有限積保存、
最小公理全体・(3.6)・K0・T2・E の接続は引き続き未完である。

§46 の保存検証：集約対象ビルドと公理監査が成功。116 モジュール・1433 宣言、標準三公理のみ。
§45 の全体ビルド成功後、今回の保存単位では全体ビルドを反復しない。


## 47. 補題 3.3 の有限全射の strict transform と有限忠実平坦な細分

L9 の現状を再確認し、L9e の Tot・hG は引き続き未着手である。
一方、SchemeLemmas 側の実際の strict transform は、
元の空間と blowup のファイバー積における開部分のスキーム論的像として構成されている。
その閉包含と構造射を読み取り、L8 の補題 3.3 の幾何に接続した。
他レーンのファイルは変更していない。

有限射 f : X → Y の strict transform の構造射は、
有限射の引き戻しに実際の閉包含を合成したものなので有限である。
元の f が全射なら、その引き戻しも全射であり、制限した射も全射となる。
strict transform の閉包含は定義に用いた開部分で同型なので、
構造射のその開部分上の制限も全射となる。
ここで元の f が開部分で同型になるという仮定は不要である。

固有射の稠密な開部分上の全射性から全体の全射性を導く補題を証明した。
制限射の各点の持ち上げから開部分を像に含め、固有性による閉像性で閉包も含める。
実際の blowup の中心外の逆像は常に稠密なので、
中心外を用いて構成した有限全射の strict transform は全射となる。
平坦化や降下の結論をこの全射性の仮定としては使っていない。

局所 Noether 基底では blowup も局所 Noether であり、有限射の有限型性から
strict transform の構造射の局所有限表示性を導いた。
したがって、この実際の構造射が平坦になっていれば、
有限・平坦・全射・局所有限表示な射と元の X への射、および基底上の可換式を取り出せる。
`exists_finiteFlat_refinement_of_flat_strictTransform` はこの実際の空間と射を返す。

これは平坦化後から有限忠実平坦細分までの幾何的な段階を完了するものである。
公理 (6) の平坦化中心の存在、整な基底を支配する被約既約成分の選択、
元の有限型の圏内の全図式への持ち上げ、Čech 細分と中心上の帰納の接続は残る。
SchemeLemmas の有限加群のチャート平坦化を直ちに strict transform のスキームの平坦性と
同一視してはいない。実際の同定が必要である。
最小公理全体、実際の Tot・hG、自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§47 の保存検証：集約対象ビルドと公理監査が成功。117 モジュール・1440 宣言、標準三公理のみ。


## 48. 同じ有限型の圏の平坦細分と実際の blowup 正方形

§47 の幾何はスキームの圏で記述していた。
元の前層は固定した S 上の有限型対象を定義域とするので、その圏内へ持ち上げる必要がある。
Noether な S 上の有限型対象 Y は Noether スキームであり、
Y の実際の blowup は固有であることから、同じ S 上有限型の対象となる。
`finiteTypeBlowup` とその指定構造射を構成した。
有限射の実際の strict transform の構造射も有限なので、
これを同じ有限型の圏の対象とし、blowup と元の X への二つの射を構成した。
実際の二射影の可換式から、S 上の可換性と有限型の圏内の可換正方形を証明した。

元の f と blowup 構造射の実際の引き戻しは、既に有限型の圏内で構成されている。
その普遍性に strict transform の二つの射を入れ、
元の f の底変換被覆への細分射を構成した。
この細分射は blowup 基底への構造射を保ち、実際の Čech nerve 関手で写すと
`finiteTypeStrictTransformCechRefinement` という全単体射を保持する比較となる。
この比較が指定増強も保つことを増強 Čech の同じ Arrow の射から証明した。
同じ前層の定義域を全スキームの圏へ変更してはいない。

中心外を用いた有限全射の strict transform については、
同じ指定射の有限性・全射性を確認し、平坦化後の実際の平坦性が与えられれば
有限忠実平坦で局所有限表示な被覆となることを元の有限型の圏内で公開した。
この Čech 比較そのものが降下を保つことは、Tot の細分計算で別途示す必要がある。

さらに、中心の台を被約閉中心として、その実際の引き戻し・blowup の固有性・
中心外の同型性を組み合わせ、`finiteTypeBlowupSquare` を構成した。
これは既存の `AbstractBlowupSquare` の全ての幾何条件を満たす。
中心の冪零構造を保存した正方形であるとは主張せず、
明示した被約中心を使う抽象 blowup 降下と中心上の帰納の入力である。

平坦化中心の存在、整な基底を支配する被約既約成分の選択、
Čech 細分の実降下と中心上の帰納による元の有限全射の降下への還元は残る。
実際の Tot・hG、最小公理全体、自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§48 の保存検証：集約対象ビルドと公理監査が成功。118 モジュール・1467 宣言、標準三公理のみ。
§48 の幾何接続の区切りの全体ビルドも成功（10100 ジョブ）。
`set -eo pipefail` で終了コード 0、ログは `/tmp/l8-strict-transform-refinement-full-build.log`。


## 49. 整な基底を支配する成分の選択と元の有限全射への細分

補題 3.3 の前段として、既約な基底への固有全射から、
基底に全射な被約既約成分を実際に選ぶ部分を証明した。
基底の生成点の持ち上げ x を取り、x を含む既約成分に既存の被約閉構造を入れる。
この成分の像は固有性で閉じており、基底の生成点を含むので全ての特殊化を含む。
したがってその指定射は全射である。
この選択には Noether 性や既約成分の有限個性は不要である。
始域が既に被約であるという仮定も置かない。

指定射 `integralComponentMap` は元の有限型の圏内の実際の閉包含と元の射の合成である。
元の射が有限ならこの射も有限なので、整基底への有限全射から
平坦化する整な有限全射成分を選べる。
成分の存在や支配性を未証明のフィールドとして新たに要求してはいない。

この成分と中心 J を固定し、その実際の strict transform の構造射が平坦であるとする。
§47–48 の有限性・全射性・局所有限表示性をその指定射に適用する。
strict transform から成分への射に、成分の元の X への閉包含を合成すると、
元の f と blowup の構造射の上で可換する。
この可換式を、元の f の実際の引き戻しの普遍性に入れ、
有限忠実平坦被覆から元の有限射の底変換への細分射を構成した。
`exists_finiteFlat_cover_refining_blowup` は同じ有限型の圏内の被覆とこの細分射、
その有限性・平坦性・全射性・局所有限表示性、および基底上の指定可換式を返す。

これにより「支配する整成分の選択」と「その成分の平坦化後から元の被覆への細分」が接続した。
適切な平坦化中心の存在は引き続き未証明であり、
SchemeLemmas の有限加群のチャート平坦化を strict transform の平坦性と同一視してはいない。
この実際の同定と、Čech 細分の実降下・中心上の帰納による有限全射降下への還元が残る。
実際の Tot・hG、最小公理全体、自然な blowup 列・有限積保存の導出、(3.6)・K0・T2・E も未完である。

§49 の保存検証：集約対象ビルドと公理監査が成功。120 モジュール・1473 宣言、標準三公理のみ。
§49 の区切りの全体ビルドも成功（10118 ジョブ）。`set -eo pipefail` で終了コード 0。
ログは `/tmp/l8-dominating-component-full-build.log`。


## 50. 生成点付近の自由化から実際の有限加群のチャート平坦化中心へ

SchemeLemmas の有限加群の平坦化中心の存在定理は、
正則な境界元 r と、r の外での加群の平坦性を入力としていた。
整なアフィン基底でこの入力を実際に供給するため、
Noether 整域 R 上の有限加群 M について生成点付近の自由化を証明した。
元の M の平坦性・捩れなし性は要求しない。

有限加群は Noether 性から有限表示である。
分数体 K への基底変更 K ⊗_R M は K 上のベクトル空間なので自由となる。
有限表示加群の局所化の自由基底を一つの分母へ広げる Mathlib の定理を適用し、
非零元 r で局所化した M が R[1/r] 上自由になることを得た。
この自由性から境界外の平坦性を導出した。

その実際の局所化と非零元を既存の有限加群の平坦化中心の構成へ渡した。
`exists_nonzero_finite_module_flattening_center` は、
非零元 r と有限生成イデアル J、D(r) を避ける中心という条件、および
全ての実際の blowup チャート上の加群の純変換の平坦性を返す。
境界外の平坦性を追加仮定として残していない。
新しい平坦化公理や未証明の中心の存在のフィールドは導入していない。

結論は基礎環上有限な加群のチャート純変換に関するものに限る。
有限型代数上でのみ有限な一般の加群や、スキームの strict transform の平坦性を
この加群の結論だけから推論してはいない。
有限代数の純変換との環としての同定、実際の strict transform のアフィンチャートとの同型、
開被覆によるスキームの平坦性の貼り合わせを通して §47–49 に接続する必要がある。
Čech 細分の実降下・中心上の帰納、実際の Tot・hG、最小公理全体、
自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§50 の保存検証：集約対象ビルドと公理監査が成功。121 モジュール・1476 宣言、標準三公理のみ。
§49 で全体ビルドを確認済みなので、この代数入力の保存単位では反復しない。


## 51. 純変換商の Spec と基本開の実際のスキーム論的像

§50 の加群の平坦化を実際のスキーム射に移すため、
境界ねじれを除く商を実際の可換代数として構成した。
R 代数 B と f ∈ R について、B 自身上の境界元の像のねじれ部分加群は B のイデアルである。
`boundaryTorsionIdeal` はこのイデアル、`algebraPureTransform` はその実際の商環である。
スカラー制限の同型を使い、この商環の R 加群と既存の `modulePureTransform f B` を
代表元を保つ線形同型で結んだ。したがって加群の有限性と平坦性を商代数へ移せる。

環の局所化と加群の局所化の核は、同じ冪消滅条件で記述される。
これにより境界ねじれイデアルが B → B[1/f] の環準同型の核であることを証明した。
商代数からこの一元局所化への実際の環準同型を構成し、その単射性を示した。
局所化全体との同型や、この写像の全射性は主張していない。

商代数の Spec と B への閉包含、R への構造射を構成した。
加群の平坦性・有限性から、これらの実際のスキームの射の平坦性・有限性を得た。
Spec のイデアル対応を使い、商写像の Spec と局所化の Spec の核イデアル層が一致することを示す。
二つの閉埋め込みの lift の普遍性により、商の Spec と局所化の実際のスキーム論的像の
閉包含を保つ標準同型を構成した。

基本開 D(f) と局所化の Spec の標準同型は元の B の Spec への射を保つ。
この同型を通して核を比較し、商の Spec と基本開の実際のスキーム論的像の標準同型も構成した。
この同型は閉包含と R への構造射を保つ。
その逆射と商の Spec の構造射の合成を使い、
基本開の実際のスキーム論的像の平坦性・有限性へ移した。
点集合の閉包による代用や、構造層を忘れた同定は行っていない。

最後に Noether 整域 R 上有限な代数 B について、§50 の実際の中心を選び、
各 blowup チャート C 上の B の基底変更 C ⊗_R B に以上の同定を適用した。
全ての実際のチャートで、境界基本開のスキーム論的像の構造射が有限平坦になる。
これは実際のスキームの射についての結論であり、各チャートでの加群の平坦性だけには留めない。

ここで定義したアフィン像を、元の global strict transform の各チャートへ引き戻したものと
同定する部分はまだ残る。像の形成と開埋め込みによる底変換の両立、
実際のテンソル積のアフィン引き戻しとの比較、境界基本開の一致、
開被覆上の平坦性の貼り合わせを行う必要がある。
全射性は §47–49 の global な判定へ接続して供給し、現在の局所像について独立に仮定しない。
Čech 細分の実降下・中心上の帰納、実際の Tot・hG、最小公理全体、
自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§51 の保存検証：集約対象ビルドと公理監査が成功。125 モジュール・1517 宣言、標準三公理のみ。
§51 の区切りの全体ビルドも成功（10179 ジョブ）。`set -eo pipefail` で終了コード 0。
ログは `/tmp/l8-affine-pure-transform-full-build.log`。


## 52. 像の開底変換と global strict transform のチャートでの平坦性の貼り合わせ

準コンパクトな射 f と開埋め込み g の実際の Cartesian 正方形について、
底変換後の核イデアル層が元の核の引き戻しと一致することを証明した。
各アフィン開集合で Mathlib の核の公式とイデアル層の引き戻しの公式が一致することを使う。
選択された引き戻しだけでなく、具体的な Cartesian モデルにも適用できる。
これと閉包含の引き戻しの核の公式を合わせ、
局所のスキーム論的像と元の像の実際の引き戻しの間に、閉包含を保つ標準同型を構成した。
像を点集合の閉包で代用せず、構造層を持つ閉スキームとして比較している。

strict transform を定義する開包含の準コンパクト性も供給した。
局所 Noether 基底上の有限型射では、blowup と周辺空間が局所 Noether なので、
その実際の開包含は準コンパクトである。
したがってこの像の開底変換の定理を実際の strict transform に適用できる。

blowup の開チャート j に対し、周辺空間の実際の底変換と、
strict transform を定義する開部分のその逆像を構成した。
この開部分の像は、元の strict transform の閉包含を周辺チャートへ引き戻したものと同型になる。
二射影の交換と二段の Cartesian 正方形の貼り合わせを通して、
`strictTransformOpenChartIso` はこれを元の構造射 `strictTransformπ` の実際の底変換に結ぶ。
この同型がチャート基底への指定構造射を保つことも全ての射影公式から証明した。
別の引き戻しの型クラスを選んで対象を変更してはいない。

この同型の逆を使い、周辺チャートの像の平坦性から
元の strict transform の構造射のそのチャート上での平坦性を得た。
平坦性の標的上の Zariski 局所性により、実際の開被覆の全ての像が平坦なら
元の global な `strictTransformπ` が平坦となる。
型クラス探索が Mathlib の一般の局所性を自動取得できない箇所では、
`HasRingHomProperty.instIsZariskiLocalAtTarget` の既存の証明を明示して適用した。
新しい平坦性の局所性の仮定や公理は導入していない。

§51 のテンソル積のアフィン像を、この周辺チャートの像と同定する工程は残る。
実際のテンソル積 Spec のファイバー積表示と、境界基本開の一致を使って
二つの具体的なチャートを対応させる必要がある。
その後、既に証明したこの貼り合わせと §47–49 の全射性・有限平坦細分へ接続する。
Čech 細分の実降下・中心上の帰納、実際の Tot・hG、最小公理全体、
自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§52 の保存検証：集約対象ビルドと公理監査が成功。127 モジュール・1549 宣言、標準三公理のみ。
§52 の区切りの全体ビルドも成功（10226 ジョブ）。`set -eo pipefail` で終了コード 0。
ログは `/tmp/l8-strict-transform-open-charts-full-build.log`。

後続の接続で区別する開部分：§50–51 が返す中心 J は D(r) を避けるので、
D(r) ≤ centerComplement J であるが、両者の等号は主張していない。
加群の r-ねじれを除く計算は U = D(r) の像に対応する。
§47 の中心外を使う全射性をそのまま無証明で適用してはならない。
blowup 上の D(r) の逆像の稠密性を証明して一般の稠密開版へ渡すか、
支配する整成分で開部分の拡大に対する strict transform の不変性を証明する必要がある。


## 53. 平坦化に使う境界基本開の逆像の稠密性と同じ境界での有限平坦細分

§52 の末尾で区別した D(r) と中心補集合の問題について、
今回は blowup 上の D(r) の逆像の稠密性を直接証明する経路を実装した。
D(r) = centerComplement J という未証明の等号は使わない。

任意の可換環の非零因子 r に対し、局所化 R → R[1/r] は単射である。
Spec の稠密像の判定と局所化の像の公式から、基本開 D(r) の稠密性を得た。
これは零環の場合も含み、Noether 性や被約性は不要である。
非零因子は実際の全 blowup チャートへの係数写像で非零因子に保たれるので、
各チャートの境界基本開も稠密になる。
各点の標準チャートによる表示と連続写像による閉包の包含を使い、
アフィン blowup 全体で境界基本開の逆像が稠密となることを証明した。
中心の有限生成性も必要ない。

さらにアフィン基底 S の全体のアフィンモデルから global な実際の blowup への
標準射が全射であることを像の公式から得た。
その構造射との可換性と基本開の逆像の公式を使い、
`blowup_boundary_dense_of_isAffine` は実際の global blowup 上の稠密性を与える。

この結果を既存の稠密開の全射性判定へ渡し、
有限全射 f の strict transform を平坦化に使った同じ U = D(r) で定義した場合に、
その実際の構造射が全射であることを得た。
元の有限全射の開部分上の同型性や D(r) と中心補集合の一致は不要である。
したがって、選んだ支配する整成分のこの同じ D(r) による strict transform が平坦なら、
元の有限射の底変換を細分する有限忠実平坦・局所有限表示被覆を同じ有限型の圏内で取り出せる。
`exists_finiteFlat_cover_refining_boundary` はこの被覆と指定細分射・可換式を返す。

残る幾何接続は、§51 のテンソル積のアフィン像と §52 の周辺チャートの像の一致である。
その一致と貼り合わせで同じ境界の実際の平坦性を供給すれば、今回の全射性の結果を適用できる。
Čech 細分の実降下・中心上の帰納、実際の Tot・hG、最小公理全体、
自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§53 の保存検証：集約対象ビルドと公理監査が成功。129 モジュール・1554 宣言、標準三公理のみ。
全体ビルドは §52 の区切りで成功済み。この保存単位では対象ビルドと監査を実行した。


## 54. テンソル積の Spec と実際の周辺チャートの同型と境界の保存

アフィン射 Spec B → Spec R と、blowup 上のチャート j : Spec C → Bl_J を取る。
R から C の係数射の Spec が j と blowup 構造射の合成に一致するという式を明示する。
この式は実際の blowup チャートで検証して適用すべき幾何条件であり、
チャートや底変換を任意の別のものへ交換する仮定ではない。

C を左因子とするテンソル積 C ⊗_R B の Spec の指定二射影の Cartesian 性を使い、
この Spec が元の射と j の基底への合成の引き戻しを表すことを証明した。
一方、実際の strict transform の周辺チャートは二段の選択された引き戻しである。
その二つの Cartesian 正方形を縦に貼り合わせ、同じ引き戻しを表すことを検査した。
両者の同じ引き戻しへの標準同型を合成して `strictTransformTensorChartIso` を構成した。
別の引き戻しの型クラスを選んで対象を変更してはいない。

この標準同型は C への射影を保つ。
元の二つの引き戻しの可換性とチャートの係数射との可換式を組み合わせると、
R の Spec への構造射も保つことが分かる。
この構造射の等式で境界 D(r) を引き戻し、
周辺チャートの strict transform を定義する開部分が、
テンソル積の係数の像による基本開 `algebraBoundaryOpen C (C ⊗_R B) (r の C での像)` に
対応することを証明した。

これにより §51 のアフィン像と §52 の周辺チャートの像を比較するための
実際の周辺空間の同型と開部分の対応が揃った。
この周辺同型のもとでスキーム論的像を移す比較を構成し、構造射の可換性を使って
平坦性を移す工程を続ける必要がある。
実際の全 blowup チャートの係数射の公式を適用して §52 の貼り合わせに渡し、
§53 の同じ境界の全射性と有限忠実平坦細分へ接続する工程はまだ残る。
Čech 細分の実降下・中心上の帰納、実際の Tot・hG、最小公理全体、
自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§54 の保存検証：集約対象ビルドと公理監査が成功。130 モジュール・1564 宣言、標準三公理のみ。
全体ビルドはアフィン平坦化の global 接続の区切りで再確認する。


## 55. 周辺同型での像の移送から実際の strict transform のチャートの平坦性へ

§54 の周辺同型が二つの境界開部分を対応させることを使い、
その実際のスキーム論的像を移す一般的な比較を構成した。
準コンパクトな開包含の像を周辺同型で引き戻し、
像と開底変換の同型に、同型に沿う引き戻しの第二射影による同型を合成する。
同じ開集合を別の表示で指定する場合も、その等式による標準同型を先に合成できる。
この全ての同型が、実際の閉包含と周辺同型の hom に関する可換式を満たすことを証明した。
別の引き戻しの型クラスを選んで対象を変更してはいない。

strict transform を定義する開包含の準コンパクト性から、
その周辺チャートの逆像開包含の準コンパクト性を実際の Cartesian 正方形で導いた。
チャート環の Noether 性をここで別途仮定する必要はない。
この入力により、§54 の周辺同型と同じ境界の基本開の等式を使って、
`strictTransformTensorImageIso` はテンソル積の基本開の実際の像と
周辺チャートの開部分の実際の像を同定する。

これを §52 の global strict transform のチャートとの同型に合成した。
`strictTransformTensorPullbackIso` は、
テンソル積の基本開のスキーム論的像を元の構造射の実際の底変換に同定する。
二つの像の比較と周辺同型の C 射影の公式を合成し、
この同型が C への指定構造射を保つことを証明した。
したがってチャート係数環 C 上の純変換加群が平坦なら、
§51 のアフィン像の平坦性をこの同型の逆で移し、
元の strict transform の実際のチャートも平坦になる。
`strictTransform_chart_flat_of_tensorPureTransform` はこの結論を実際のスキームの射で主張する。

この段階のチャート j と R → C の係数射の可換式は明示した引数である。
実際の blowup の標準チャートの公式を適用し、全開被覆のチャートで入力を供給して
§52 の貼り合わせと §53 の同じ境界の全射性・有限忠実平坦細分へ渡す工程はまだ残る。
全切断環とその Spec との標準同型による係数の表示を保持し、
元の環とその全切断環を無証明で同じ環として扱ってはならない。
Čech 細分の実降下・中心上の帰納、実際の Tot・hG、最小公理全体、
自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§55 の保存検証：集約対象ビルドと公理監査が成功。132 モジュール・1588 宣言、標準三公理のみ。
§55 の区切りの全体ビルドも成功（10342 ジョブ）。`set -eo pipefail` で終了コード 0。
ログは `/tmp/l8-tensor-image-flatness-full-build.log`。


## 56. 実際の全標準チャートからアフィン有限射の平坦化中心と忠実平坦細分へ

論文 補題 3.3 の有限射の平坦化に必要なアフィン幾何入力を証明した。
整なアフィン Noether 基底 Y への有限射 X → Y に対して、非零全切断 r と
イデアル層 J が存在し、D(r) は中心の補集合に含まれ、J の台は真閉で、
同じ D(r) で定義した実際の strict transform の構造射が平坦になる。
平坦化中心の存在や strict transform の平坦性を引数にしていない。

Y と Spec Γ(Y,⊤)、有限性からアフィンとなる X と Spec Γ(X,⊤) の同型を明示する。
表示した有限環準同型に §50 の有限加群の平坦化中心を適用し、
アフィンのイデアルとイデアル層の同値で元の Y の中心へ戻す。
このイデアル層の全アフィン上の有限生成性は Noether 性から得る。
元の Y の top アフィンの実際の blowup 標準チャートを使い、
係数射と blowup 構造射の既存の可換式を各チャートに適用した。
§55 の像の比較を元の X,Y のアフィン表示へ一般化し、
純変換加群の平坦性を実際の strict transform の各チャートへ移す。
実際の標準チャート開被覆と平坦性の Zariski 局所性で全体へ貼り合わせる。
R と Γ(Spec R,⊤) を無証明で同じ環として扱っていない。

整性から非零 r の D(r) は非空であり、中心がこれを避けることから台の真閉性を得る。
有限全射の場合は生成点を支配する整成分を選び、その有限射に上の中心を適用する。
§53 の同じ境界基本開の稠密性と全射性を組み合わせ、
元の有限全射の blowup による底変換を細分する、実際の有限忠実平坦射を得た。
すべて同じ基底 S 上の有限型スキームの圏内で構成し、細分射の可換式も返す。

これは公理 (6) の整アフィン Noether 基底・有限射の場合の幾何的証明である。
一般基底での貼り合わせ、有限忠実平坦 Čech 降下から細分先への還元、
中心上の帰納と補題 3.3 全体への接続は引き続き残る。
原典の τ 位相の層論を実際の Čech 計算へ置換する方針は変えない。
実際の Tot・hG、最小公理全体、自然な blowup 列と有限積保存の導出、
(3.6)・K0・T2・E も未完であり、この保存を主定理の完成とはしない。

§56 の保存検証：集約対象ビルドと公理監査が成功。138 モジュール・1626 宣言、標準三公理のみ。
全体ビルドは所有範囲外の `KST/SConstruction/FrameCofiberShapes.olean` が存在せず、
ルート集約 `SerrePositivity.lean:1:0` で失敗した。終了コード 1 を `set -eo pipefail` で確認。
ログは `/tmp/l8-affine-finite-flattening-full-build.log`。L8 の対象ビルド・監査は成功しており、
自分の import 閉包の破損ではない。所有範囲外を編集・回避せず次の工程を進める。


## 57. 実際の rank 開被覆、平坦化後の正の定 rank と中心の次元低下

論文 補題 3.2 で使う正の rank を、元の有限忠実平坦射から取り出した。
有限平坦有限表示射の rank の局所定数性を Mathlib の実際の関数に適用し、
その値域を添字とする開被覆を構成した。準コンパクトな基底では値域が有限であり、
全射性から各添字の rank は正となる。各開部分への実際の底変換の rank は
指定された値に一致し、さらに任意の底変換でも同じ値を保つ。
Noether 基底上では開部分を元の有限型の圏へ持ち上げ、指定された引き戻し射でも
同じ rank になることを証明した。空の基底に非空な添字を無理に選んでいない。

§56 で構成した平坦化中心の場合には、より強い一様性が成り立つ。
非零境界 D(r) が中心を避けるため、中心外の開部分は非空で既約である。
blowup の中心外同型でその逆像も既約となる。§53 の境界の稠密性から、
より大きい中心外の逆像も稠密であり、既約な稠密開の閉包によって
実際の blowup 自体の既約性を証明した。被約性はここでは主張しない。
したがってその有限忠実平坦細分の局所定数 rank は大域的に一定となり、全射性で正となる。

同じ中心の真閉性と有限次元上界 d から、実際の `finiteTypeBlowupSquare` の
左下の被約中心の次元が厳密に d より小さいことも証明した。
`exists_affine_flat_refinement_with_rank_and_dimension` はこの低次元の中心と
正の定 rank の有限忠実平坦細分を、元の有限全射の底変換への細分射とともに返す。
中心上の次元低下や blowup の既約性、正の定 rank を追加の入力にはしていない。

注意：定 rank とベクトル束の自明化は別である。正本 §13 決定 12 のとおり、
一般の transfer の射影公式は `[p_*O]` を使う。この保存ではその作用を整数 rank と
同一視していない。局所自明化と実際の transfer 自然変換の rank 公式への接続、
Tot による Čech 降下・細分・中心上の帰納は残る。
最小公理全体、自然な blowup 列の導出、(3.6)・K0・T2・E も未完である。

§57 の保存検証：集約対象ビルドと公理監査が成功。140 モジュール・1647 宣言、標準三公理のみ。
この保存単位は対象ビルド・監査を実行し、全体ビルドの所有範囲外の失敗は §56 の記録どおり。


## 58. 定 rank と区別した実際の有限自由自明化と Cartesian チャート

論文 補題 3.2 のベクトル束の自明化を、実際の有限表示平坦加群について証明した。
各素イデアル p での有限自由性を Mathlib の基底の拡張定理で一元局所化 R[1/r] へ広げる。
局所化加群と R[1/r] ⊗_R M の実際の線形同型で自由性を移し、
その有限 rank が元の p での stalk rank に一致することも保持した。

この自由自明化を持つ元はどの極大イデアルにも全ては含まれない。
したがってその集合が単位イデアルを生成し、有限部分集合を選んでも単位イデアルを生成する。
各元にはそれを避ける素点も保持し、対応する局所化が非零であることを検証する。
有限忠実平坦代数 B では、Spec の全射性からその素点での rank が正となり、
実際の R[1/r] ⊗_R B に Fin rank で添字付けた有限基底を構成した。
これは局所定数 rank だけから自由性を推測したものではない。

選んだ有限個の元から実際の有限アフィン開被覆を構成した。
各チャートは Spec R[1/r]、射は局所化写像の Spec であり、
Spec (R[1/r] ⊗_R B) の指定二射影が元の有限射とこのチャート射の
実際の Cartesian 正方形になることを証明した。
この自由基底をさらに任意の代数へ底変換し、二重テンソル積の実際の標準同型で
直接のテンソル積へ移す定義も構成した。同じ添字 Fin rank を保ち、追加の平坦性は不要。

元のスキーム射のアフィン表示についても、表示環準同型の平坦性・有限表示性と
その Spec の全射性を元の射の性質から証明した。有限性と有限表示性から
表示代数の加群としての有限表示性を供給し、上の正の有限基底被覆を適用した。
元の射から選んだ同じ toAlgebra を用い、環と全切断環を無証明で同一視していない。

残る接続：一般の基底の有限アフィン被覆とこの自明化被覆の合成、元の有限型の圏への
全チャートの持ち上げ、実際の transfer の射影公式・加法性から局所 rank 公式の導出。
Tot による Čech 降下・細分と中心上の帰納、最小公理全体、自然な blowup 列の導出、
(3.6)・K0・T2・E も未完である。原典の τ 位相の層論を Čech 計算へ置換する方針は同じ。

§58 の保存検証：集約対象ビルドと公理監査が成功。143 モジュール・1669 宣言、標準三公理のみ。
この保存単位では対象ビルドと監査を実行した。全体ビルドの所有範囲外の失敗は §56 の記録どおり。


## 59. 一般基底の有限自由アフィン被覆と元の有限型の圏への持ち上げ

論文 補題 3.2 の局所自明化を一般の基底へ拡張した。
`FiniteFreeAffineChart` は、元のスキーム射の実際の底変換を表す二つの可換環、
代数構造、基底の開包含、元の始域への射、正の自然数、実際の有限基底と
指定射影のスキームの Cartesian 性を保持する。これは構成される幾何データの型であり、
その存在を前層の公理に追加してはいない。

各基底点でアフィン近傍 Spec R → Y を選び、有限射をそこへ引き戻す。
有限性から始域もアフィンになり、§58 の実際のアフィン表示の自明化を適用する。
単位イデアルを生成する元のうちその点を避ける r を選び、
Spec (R[1/r] ⊗_R B) の指定二射影による Cartesian 正方形を
元のアフィン近傍の引き戻し正方形に横に貼り合わせた。
したがって元の射そのものの底変換として、正の有限基底を持つチャートが得られる。
各点での存在には基底の Noether 性も準コンパクト性も不要である。

基底が準コンパクトなら各チャートの開像による被覆から有限部分族を選べる。
選んだチャートの環・有限基底・Cartesian 性は変更せず、実際の有限アフィン開被覆を構成した。
空の基底は空の有限添字集合でも扱え、基底の非空性を追加していない。

Noether 基底 S 上では、チャートの基底と始域の開包含を元の構造射へ合成し、
全ての四辺を同じ有限型の圏に持ち上げた。始域への開包含性は実際の Cartesian 性から得る。
元のスキームでの Cartesian 性を忘却関手で反映して、有限型の圏内でも引き戻しであると証明した。
元の前層が使う指定された `finiteTypePullback` との同型も構成し、
その hom が指定二射影を保つことを証明した。別の引き戻し型クラスへの変更はしていない。

同じ射影の有限忠実平坦性・有限表示性と、実際の rank が基底の本数に等しいことも証明した。
有限部分族の持ち上げ後の基底包含も実際に全体を覆う。
これで局所自明化の幾何入力を、元の前層の定義域と実際の底変換射に接続した。
残るのは実際の transfer の射影公式・加法性からの局所 rank 公式、
Tot の Zariski Čech 降下・細分・Fubini と中心上の帰納の接続である。
最小公理全体、自然な blowup 列の導出、(3.6)・K0・T2・E も未完である。
原典の τ 位相の層論を Čech 計算へ置換する方針は変わらない。

§59 の保存検証：集約対象ビルドと公理監査が成功。146 モジュール・1731 宣言、標準三公理のみ。
一般基底の有限自由チャート接続の区切りで全体ビルドも成功。`set -eo pipefail` で終了コード 0 を確認。
ログは `/tmp/l8-finite-free-charts-full-build.log`。§56 の所有範囲外の一時的な欠落は今回再現しなかった。


## 60. 自由チャートの底変換と同じ基底の自然性・反復整合性

論文 補題 3.2 の transfer を各 Čech 段へ渡すため、§59 の同じ自由チャートを
任意のアフィン係数底変換へ移す証明を追加した。
基底の座標環 C の任意の可換代数 S に対して、実際の S ⊗_C B の指定二射影を使い、
元の射への Cartesian 正方形を横に貼って実際の底変換であることを証明した。
基底は同じ Fin rank を添字にした標準的な底変換であり、各段で選び直していない。

有限平坦な元の射の rank は元のチャート上で基底の本数に一致し、
任意のアフィン底変換の実際の構造射の rank も同じ値になる。
係数環 S の非零性や平坦性は仮定しない。点が存在する場合に rank を評価する。

さらに C 代数写像 S → T によるテンソル積の写像が各基底ベクトルを
T での対応する基底ベクトルに送ることを証明した。
C → S → T での反復底変換の基底も、二重テンソル積から直接の底変換への
実際の標準同型により直接の基底と等しくなる。
したがって二重 Čech の自明化に必要な射と基底の整合性を保てる。
これは transfer 自然変換や Tot の降下自体の構成を代替しない。

未完の接続は §59 のとおり。最小公理全体、自然な blowup 列の導出、
Tot・hG、(3.6)・K0・T2・E も未完である。

§60 の保存検証：集約対象ビルドと公理監査が成功。147 モジュール・1738 宣言、標準三公理のみ。
全体ビルドは §59 の区切りで成功済み。この保存単位では対象ビルドと監査を実行した。


## 61. 有理持ち上げの分母・ねじれ消去と指定 PiDescent の整数形への一般比較

論文 定理 3.1 の有理全射性から、(3.2) と §4 で使う整数形へ移る群論を証明した。
任意のアーベル群の射 f : A → B について、1 ⊗ b が有理拡大の指定写像で持ち上がれば、
正の自然数 n と a ∈ A が存在して n・b = f(a) となる。
有理テンソル積への標準射が非零整数による加群の局所化であることを使い、
まず有理持ち上げ元の分母を払う。その後、有理化で等しくなった二つの元に
別の非零整数を掛けてねじれの差を消す。最後に符号を調整して正の自然数へ直す。
元の群の有限生成性やねじれなし性を仮定していない。

テンソルの順が A ⊗ ℚ の場合も、交換同型と指定写像の自然性で同じ結論を得る。
逆に正の整数倍が持ち上がるならその整数の逆数を左係数にした単純テンソルで
有理持ち上げを構成でき、二つの条件の同値も証明した。
指定された部分加群への有理全射性から同じ整数形を得る形も公開した。

`IntegralPullbackComparison` は、二つの整数群の有理化と元の前層の指定次数との
線形同型、および元の整数写像と指定引き戻しに関する可換式を保持する。
このデータと指定 `PiDescent` から、不変な有理類を持ち上げて同じ整数写像の
正の整数倍の持ち上げへ戻す一般比較補題を証明した。
整数群の左 G 作用との比較には、前層の左作用が逆元による引き戻しであることを明示し、
整数の G 不変性から前層の不変部分への所属を導く。

重要な未完部分：この構造体は接続データの型であり、その存在や (3.6) の同定の証明ではない。
実際の K0・T2 の支持つき局所化・中心局所化の台判定から比較データを供給する工程は残る。
二つの read-only の K0 降下定理をこの保存で証明済みとはしない。
Tot の Čech 降下・細分・Fubini、中心上の帰納への接続、最小公理全体と E も未完。

§61 の保存検証：集約対象ビルドと公理監査が成功。149 モジュール・1768 宣言、標準三公理のみ。
全体ビルドは §59 の区切りで成功済み。この保存単位では対象ビルドと監査を実行した。


## 62. 異なる被覆の混合二重 Čech と細分射からの全行の分裂

論文 補題 3.2・3.3 の細分を実際の Čech 計算で扱うため、
同じ被覆の自己底変換だけでなく、異なる二つの射 f : X → Y、g : W → Y の
混合二重増強 Čech 図式を構成した。任意の基底上の対象の指定底変換 Arrow を作る関手と、
元の射への自然比較を先に構成し、g の全 Čech 段の図式へ合成した。
全ての面射・退化射を保持し、元の有限型の圏にもそのまま適用できる。

各二重次数で、混合 Čech の二つの指定射影が元の f の Čech 段と g の Čech 段の
基底上のファイバー積であることを証明した。この指定 Cartesian 性から、
f と g および二つの単体軸を交換する標準同型を構成した。
内側・外側の全単体射に関する自然性を二射影で検査し、積添字の図式全体の自然同型にした。
二回交換すると恒等同型になることも同じ二射影で証明した。

a : X → W、a ≫ g = f という細分射があれば、f の各 Čech 段の零番目の射影と a を合成し、
g のその段上での底変換に実際の切断を構成できる。
この片方向の各行の Čech 図式に extra degeneracy を与え、
元の同じ前層の像でも片側逆と反対側の合成の収縮ホモトピーを構成した。
零番目の射影で選んだ切断の外側の全単体射に関する自然性は仮定・主張していない。

最後に §57 の実際のアフィン平坦化細分の同じ細分射 a と可換式をこの構成へ適用した。
元の有限全射の平坦性を要求せず、低次元の実際の抽象 blowup 中心、
正の定 rank の有限忠実平坦細分と、元の底変換被覆の混合 Čech の全行の分裂を同時に返す。
中心や細分、分裂の存在を追加の仮定にしていない。

ここまでの分裂は実際の幾何図式と前層の像のデータである。
Tot のホモトピー不変性・Fubini・Zariski Čech 降下に接続して細分降下を結論する工程は残る。
原典の τ 位相の層論を混合 Čech・分裂降下・Fubini へ置換する方針に従う。
最小公理全体、自然な blowup 列の導出、(3.6)・K0・T2・E も未完である。

§62 の保存検証：集約対象ビルドと公理監査が成功。153 モジュール・1822 宣言、標準三公理のみ。
平坦化と混合 Čech の分裂の接続の区切りで全体ビルドも成功。`set -eo pipefail` で終了コード 0。
ログは `/tmp/l8-flattening-mixed-cech-full-build.log`。


## 63. 抽象 blowup の任意の底変換と全側面が Cartesian な比較立方体

論文 補題 3.3 の抽象 blowup 降下を実際の Čech 各段へ移す幾何を証明した。
まず、スキーム射が指定開部分上で同型なら、任意の底変換の第二射影も
逆像の開部分上で同型になることを、実際の四開部分への制限の Cartesian 正方形で証明した。

Noether 基底 S 上の元の有限型の圏内で、抽象 blowup の右辺と閉中心を任意の射 h へ引き戻す。
固有性と閉埋め込み性を実際の底変換で保ち、中心の像の補集合が
元の中心補集合の逆像に等しいことを指定射影の像の公式で検査した。
上の開制限の同型保存を使い、中心外同型も満たす実際の抽象 blowup 正方形を得た。
中心を被約化せず、引き戻した中心の厚みを保持する。

元の正方形への比較立方体では、三頂点に指定底変換の射影を使い、
例外部分の射は元の Cartesian 正方形の普遍性で構成した。
四面の可換式を保持し、右辺・中心の面だけでなく、上辺と左辺の面の Cartesian 性も
新旧の正方形の貼り合わせと消去で証明した。さらに二つの面を縦に貼り、
新しい例外部分自体が元の例外部分の h による実際の底変換であることを得た。

この例外部分を元の圏の指定 `finiteTypePullback` と結ぶ標準同型を構成し、
その hom が元の例外部分への射と新しい基底への構造射を保つことを証明した。
引き戻しの型クラスを別のものに交換する回避策は使っていない。

残る工程：Čech の全単体射に関してこの底変換族と比較立方体を関手・自然変換へまとめ、
実際の抽象 blowup 降下から自然な列を供給して Tot の比較へ接続する。
最小公理全体、Tot の細分・Fubini、(3.6)・K0・T2・E も未完である。

§63 の保存検証：集約対象ビルドと公理監査が成功。156 モジュール・1850 宣言、標準三公理のみ。
全体ビルドは §62 の区切りで成功済み。この保存単位では対象ビルドと監査を実行した。


## 64. 指定底変換の関手性、自然な抽象 blowup 族と混合 Čech の比較

論文 補題 3.3 の §63 の段ごとの底変換正方形を全単体射へ接続した。
まず、元の有限型の圏の実際の `finiteTypePullback` の map を指定 Cartesian 正方形の
普遍性から構成し、第一・第二射影の公式で恒等射と合成の保存を証明した。
基底上の全対象と射に対する Arrow の関手と、元の射への自然な比較を構成した。

圏の選択された pullback と実際の `finiteTypePullback` は別の指定モデルなので、
型クラスを変更せずに二射影を保つ標準同型で比較した。
この同型が基底上の全射に自然であることを二射影で検査し、Arrow 関手の自然同型を得た。
任意の別の被覆の Čech 図式へ制限し、増強 Čech nerve 関手で写すと、
指定モデルの混合図式と §62 の圏論的な混合図式を全単体射を保って同定できる。
増強先が同じであることと、指定増強の可換式も確認した。
元の同じ反変前層を適用した後の増強二重図式の自然同型も構成した。

抽象 blowup では、右上と左下に同じ指定 map を使い、左上への射は
終域の Cartesian 正方形の普遍性で構成した。
終域が Cartesian な正方形の射は三頂点で決まるという一般補題を使い、
左上の射を選び直すことなく恒等射・合成の保存と元の正方形への比較の自然性を証明した。
全基底射に関する正方形の関手と自然な比較立方体を元の Čech 図式へ制限し、
全ての面射・退化射に自然な抽象 blowup の底変換族を得た。
中心・例外部分の被約化や、指定引き戻しの交換はしていない。

残る接続：この正方形の各頂点の Čech 列を、底変換した元の被覆の実際の Čech nerve と
指定射・増強を保って比較し、実際の抽象 blowup 降下から自然な列を供給する。
Tot の Fubini・分裂降下・細分の結論、最小公理全体、(3.6)・K0・T2・E も未完である。
原典の τ 位相の層論を Čech 計算へ置換する方針に従う。

§64 の保存検証：集約対象ビルドと公理監査が成功。160 モジュール・1900 宣言、標準三公理のみ。
区切りの全体ビルドは所有範囲外の `KST/DerivedBlowup/ExteriorCochainFunctoriality.lean`
67 行の rfl と 68 行の introN のエラーで失敗。`set -eo pipefail` で終了コード 1 を確認。
ログは `/tmp/l8-blowup-basechange-functor-full-build.log`。L8 の import 閉包は対象ビルドと監査を通過している。
所有範囲外を編集・回避せず、指定底変換の Čech 列の比較を続ける。


## 65. 抽象 blowup の四頂点の列と実際の増強 Čech nerve の比較

論文 補題 3.3 の抽象 blowup を元の被覆の全 Čech 段に底変換して得る列を、
実際に元の被覆を各頂点へ底変換した被覆の Čech nerve と同定した。
まず一般の射 f と被覆 cover について、指定 `finiteTypePullback` の列の
二つの自然な射影を構成し、列全体が定数図式と元の増強の幾何的引き戻しであることを
各段の指定 Cartesian 性から証明した。Čech 底変換の Cartesian 正方形と比較することで、
選択された底変換被覆の Čech nerve との自然同型を得る。
さらに実際の `finiteTypePullbackSnd cover f` の Arrow の標準同型を Čech nerve で写し、
実際の指定底変換被覆そのものとの自然同型を構成した。
増強先 X への増強と元の cover の Čech nerve への指定射も両方保持する。

抽象 blowup の右上・左下・右下の列は、それぞれ指定底変換列・元の Čech nerve と
定義から同じ関手になる。左上の例外部分については §63 の標準同型が
全基底射に自然であることを二射影で証明した。
この一般の Over の自然同型を元の Čech 図式へ制限し、例外部分の列との比較を得た。
Čech の巨大な各段の型を直接展開せず、先に全基底射に関する証明を行う構造である。

元の正方形への自然な比較立方体を各頂点の評価関手で写し、指定増強を固定した。
三つの非自明な頂点の列の自然同型がそれぞれの増強を保つことを証明し、
四頂点全てについて、元の被覆の実際の底変換の増強 Čech nerve との同型にまとめた。
これは各頂点の値の同型の寄せ集めではなく、全ての単体射と増強先を保つ同型である。
元の前層には増強単体対象の関手としてそのまま適用できる。
前層が幾何的引き戻しを保存することや π_* と Tot の交換は使っていない。

残る工程：実際の抽象 blowup 降下から自然な fiber 列・全次数の列を供給し、
Tot の Fubini・分裂降下・細分と、この四頂点の実際の Čech 比較を接続する。
最小公理全体、(3.6)・K0・T2・E の実現も未完である。
原典の τ 位相の層論を Čech 計算へ置換する方針は同じ。

§65 の保存検証：集約対象ビルドと公理監査が成功。163 モジュール・1953 宣言、標準三公理のみ。
この保存単位では対象ビルドと監査を実行した。全体ビルドの所有範囲外の失敗は §64 の記録どおり。


## 66. 一般の底変換の推移性と有限型対象の有限次元性

論文 補題 3.2・3.3 の blowup と閉中心への底変換で必要な二つの幾何条件から、
底変換側のアフィン性の仮定を取り除いた。
共通の基底点のアフィン近傍を取り、その点と元のファイバーの二点を
実際のスキームの引き戻しの点として持ち上げた。
二段の指定底変換の比較射の Cartesian 性を普遍性から証明し、
アフィン近傍上で得た群元を同変な比較射で元の基底へ戻した。
この推移性の証明には群の有限性・有限型性・Noether 性自体は不要である。
元の環論的な幾何的推移性を用い、通常の点の推移性の底変換保存は仮定していない。
忘却が保つ Cartesian 正方形との同変な標準同型を使い、
元の有限型の圏の実際の指定引き戻しと指定群作用にも同じ結論を移した。

次元については sober 空間の既約閉集合と点の順序同型を経由し、
開埋め込みで点の coheight が変わらないことから、開被覆の共通次元上界を貼り合わせた。
有限被覆なら各自然数上界の有限最大値が使える。準コンパクトなスキームの
有限アフィン部分被覆の各構造射へ既存の有限型代数の次元上界を適用し、
アフィン性を要求しない有限型対象の自然数上界を得た。
一般の Noether 環だけからの有限次元性は主張せず、明示的な基底上界、
または局所 Noether 基底の高さ定理から上界を供給する。
局所 Noether 基底上の実際の一般の Čech 各段にも、始域のアフィン性を仮定せず適用した。

残る接続：これらの一般の幾何条件を切断つき全次数降下へ接続し、
実際の抽象 blowup 降下による自然な列と Tot の Fubini・分裂降下・細分へ進める。
最小公理全体、(3.6)・K0・T2・E の実現は未完。
原典の τ 位相の層論を Čech 計算へ置換する方針は同じである。

§66 の保存検証：集約対象ビルドと公理監査が成功。166 モジュール・1966 宣言、標準三公理のみ。
区切りの全体ビルドはルートの import 時に、所有範囲外の二モジュール
`InfinityCategories.F1B.RelativeFunctorHomotopyComposition` と
`InfinityCategories.F1.RelativeFunctorVertices` が同じ `relativeFunctorVertex` を含むため失敗。
`set -eo pipefail` で終了コード 1 を確認した。
ログは `/tmp/l8-general-basechange-full-build.log`。L8 の import 閉包は対象ビルドと監査を通過。
所有範囲外の宣言を変更せず、切断つき降下への接続を続ける。


## 67. 一般の分裂底変換への全次数降下の接続

論文 補題 3.2・3.3 の非アフィンな基底変更に対し、§66 の推移性と次元上界を
切断を持つ場合の完成済みの二重帰納へ渡した。
元の射への持ち上げから、指定引き戻しへの切断を実際に作り、第二射影との恒等式を証明した。
指定群作用は元の有限型の圏の pullbackAction のままであり、第二射影の基底上にあることも導いた。
有限型の圏からの忘却が保つ Cartesian 正方形を使い、元の射が分離的なら
第二射影も分離的であることを示し、底変換基底の構造射と合成して始域の分離性を供給した。
これにより、アフィン性を要求せず、元の同じ前層・作用・射による全次数 PiDescent を得た。
局所 Noether 基底では構造射の局所有限型性から §66 の次元上界を供給するため、
底変換した基底の有限次元性も追加仮定には残らない。

抽象 blowup の固有射側と閉中心の分離性は、それぞれ固有射・閉埋め込みと基底の
構造射の合成から得た。例外部分には中心の閉埋め込みの実際の Cartesian 底変換を使い、
固有射側への閉埋め込みと構造射を合成した。
基底 S 自体の分離性、頂点のアフィン性、中心の被約化は使っていない。

自然な blowup 長完全列・冪零不変性・有限積保存を実降下から供給する責務は残る。
Tot の Fubini・分裂降下・細分と、最小公理全体、(3.6)・K0・T2・E の実現も未完。
L9 の計画の §67 までを確認したが、L9d は進行中で Tot・hG の接続は未実装である。
原典の τ 位相の層論を Čech 計算へ置換する方針に従い、通常の極限で代用していない。

§67 の保存検証：集約対象ビルドと公理監査が成功。168 モジュール・1985 宣言、標準三公理のみ。
この保存単位では対象ビルドと監査を実行。全体ビルドの所有範囲外の失敗は §66 の記録どおり。


## 68. 中心局所化の台判定と実際の台つき複体の消滅

論文 (3.6) 直後の中心局所化の台判定を、自己準同型加群の局所化比較を明示的な入力として証明した。
R 線形な前加法圏と加法的 R 線形関手について、恒等射を局所化の零元検出へ渡すと、
局所化した対象が零であることと、中心元のある冪が元の恒等射を殺すことが同値になる。
係数代数や自己準同型環に可換性を課していない。中心作用の基底環 R だけを可換とする。
自己準同型の局所化比較の存在は compact 性・T2 から供給すべき入力であり、
この補題をもって比較の存在や TT 局所化を証明したとは数えない。

有限個の生成元については各指数の有限最大値を取り、異なる局所化先の圏でも
共通指数で恒等射を殺す条件へ移した。さらに恒等射が張る巡回加群の零化イデアルを用い、
各元の中心冪ねじれを根基包含へ移す。有限生成イデアルの根基包含から冪包含を得る Mathlib の定理により、
イデアルの一つの冪全体が恒等射を殺す条件との同値も証明した。

幾何側では、閉台のイデアルの根基に入る元が単元へ写る任意の環準同型で、
閉台の逆像が空になることを素イデアルが単元を含まないことから証明した。
指定された Away 局所化と、その局所化を経由する非アフィンなスキーム射にも適用できる。
論文の p ∈ J より弱い p ∈ √J で十分であり、Noether 性も要求しない。

既存の可換係数の有限射影複体には、実際の底変換によるホモロジーの台の保存を適用した。
逆像の閉台が空なので底変換後の複体は acyclic となる。
底変換後も有限射影で K-projective であることから恒等射の実際の零ホモトピーを構成し、
実際のホモトピー圏での零対象性も証明した。ホモロジーの消滅や K₀ 類の消滅だけに留めていない。

残る工程：(3.6) の非可換係数の compact kernel の同定と TT 局所化、
K0・T2 からの自然な比較の供給、および二重 fiber の実際の比較。
最小公理全体、Tot・hG と E の実現も未完であり、既存の二つの K₀ 主定理は置換していない。

§68 の保存検証：集約対象ビルドと公理監査が成功。171 モジュール・1999 宣言、標準三公理のみ。
この保存単位では対象ビルドと監査を実行。全体ビルドの所有範囲外の失敗は §66 の記録どおり。


## 69. 中心局所化の共通核と台つき部分圏の自然な線形圏同値

論文 (3.6) の compact kernel の台判定を、対象ごとの命題から充満部分圏の比較へ進めた。
各中心局所化で零になる対象の共通核を定義し、§68 の自己準同型の局所化比較を
全対象について入力する。共通指数を一つ増やすことで、既存の scalarSupported の
正指数の規約へ合わせ、二つの対象条件の同値と等式を証明した。
元の圏の恒等同値をこの二つの充満部分圏へ制限し、圏同値を構成した。
両方向とも元の対象・射を保持し、忘却との可換性は各対象の恒等同型による自然同型で与えた。
両方向の加法性と中心 R 線形性も検証した。

係数変更 F と各局所化が自然同型を通じて可換する場合、局所化先の関手が
零対象を保つことから F が共通核を保つと導いた。核保存を別の仮定にはしていない。
この F を共通核と既存の scalarSupported の両部分圏へ制限し、
上の圏同値を先に使う場合と後に使う場合の二つの経路を自然同型で結んだ。
元の対象は両経路とも F.obj P であり、全ての射への自然性も保持する。
これは Y = S, X の比較を定理 3.1 の指定引き戻しへ接続するための型である。

局所化関手と係数変更の可換性、および自己準同型の局所化比較の存在は、
K0・T2 から実際に供給すべき明示的な入力である。
この圏同値を TT 局所化や非連結 K の fiber の同定そのものとは数えない。
(3.6) 全体、自然な blowup 列の実現、Tot・hG・最小公理全体・E の実現は未完。

§69 の保存検証：集約対象ビルドと公理監査が成功。173 モジュール・2021 宣言、標準三公理のみ。
区切りの全体ビルドはルートの import 時に、§66 と同じ所有範囲外の
`InfinityCategories.F1B.RelativeFunctorHomotopyComposition` と
`InfinityCategories.F1.RelativeFunctorVertices` の `relativeFunctorVertex` 重複で失敗。
`set -eo pipefail` で終了コード 1 を確認。ログは `/tmp/l8-central-kernel-full-build.log`。
L8 の対象ビルド・監査は成功しており、所有範囲外の宣言は変更しない。


## 70. 単体的重みつき錐空間の Fubini と cofibrant な可縮外重み

論文 補題 3.2・3.3 の二重 Čech の Fubini へ進むため、既存の単体集合の
WeightedCones の実際の右随伴を使った模型での比較を構成した。
二つの重み W, V の外テンソル積を積添字上の実際の関手として作り、
外重みとのテンソルと二段のテンソル関手の間を結合子の逆で自然同定した。
二つの重みつき随伴と curry/uncurry の同値の随伴を合成し、
右随伴の一意性から外重みの錐空間と反復した錐空間の自然同型を得た。
通常の極限をホモトピー極限として代用したものではなく、実際の重みつき右随伴の比較である。

積添字上の射影的模型と、内側・外側の順に反復した射影的模型について、
curry は右 Quillen であると二つの添字で右クラスを評価して証明した。
随伴から uncurry の左 Quillen 性を得た。射影的 cofibration を点ごとの cofibration と
同一視せず、二つの重みがそれぞれ実際に射影的 cofibrant であるという条件から、
内側とのテンソル関手の左 Quillen 性を外側へ持ち上げ、uncurry して
外テンソル積の実際の射影的 cofibrancy を導いた。

二つの単位重みへの増強のテンソル積と単位子で、外重みの指定増強を構成した。
単体集合の全 cofibrancy と左右テンソルの左 Quillen 性から、二つの元の増強が
各点で弱同値なら外重みの増強も各積添字で弱同値であることを証明した。
既存の HomotopyCones の選択された二つの重みへ適用し、
積添字上の cofibrant で各点で可縮な外重みを実際に得た。

残る接続：fibrant な図式に対する重みの変更と実際のホモトピー極限の比較、
反復した fibrant 置換との比較を行い、導来 Fubini へ進める。
Sp 内の Tot と hG は L9 の実現を使う責務が残り、ここまでを Tot の Fubini の完成とは数えない。
原典の τ 位相の層論を Čech 計算へ置換する方針に従う。
(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§70 の保存検証：集約対象ビルドと公理監査が成功。176 モジュール・2045 宣言、標準三公理のみ。
この保存単位では対象ビルドと監査を実行。全体ビルドの所有範囲外の失敗は §69 の記録どおり。


## 71. 可縮な cofibrant 重みの変更と実際のホモトピー極限の比較

論文 補題 3.2・3.3 の導来 Fubini のため、§70 の模型の同型を実際のホモトピー極限へ接続した。
既存の単体的 HomotopyCones の構成の証明を任意の cofibrant 重みへ一般化し、
既存の射影的 fibrant 置換後の重みつき錐空間が、任意の実際の右導来関手を計算することを証明した。
fibrant 対象での導来比較と、指定置換の弱同値の局所化を使うため、
通常の図式の極限や群ごとの極限による置換はしていない。

重みに単位重みへの各点での弱同値がある場合、重みとのテンソル関手から定数関手への
指定比較も全空間で各点の弱同値になる。これを実際に導来し、
重みつき右導来錐関手が、弱同値で局所化した定数関手の右随伴であることを証明した。
導来関手の存在は既存の Quillen 随伴の導来関手の構成から導出し、新しい入力にはしていない。
既存の選択された重みの右随伴との一意性を使い、任意の cofibrant な可縮重みと
既存の実際のホモトピー極限を、弱同値で局所化した後の自然同型で比較した。

§70 の実際の cofibrant な可縮外重みへ適用し、その錐空間が積添字の実際の
ホモトピー極限を計算する自然同型を得た。さらに §70 の右随伴の Fubini を合成し、
積添字の実際のホモトピー極限を、共通の射影的 fibrant 置換後の反復錐空間と自然同定した。
この比較は図式の全ての射への自然性を保持する。

残る接続：共通 fibrant 置換後の反復錐空間と、各行・外側で別々に既存の実際の
ホモトピー極限を取る反復計算の比較。これにより単体集合の導来 Fubini を仕上げる。
Sp 内の Tot・hG への実現は L9 の責務と接続し、原典の τ 位相の層論を Čech 計算へ置換する。
(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§71 の保存検証：集約対象ビルドと公理監査が成功。178 モジュール・2072 宣言、標準三公理のみ。
この保存単位では対象ビルドと監査を実行。全体ビルドの所有範囲外の失敗は §69 の記録どおり。


## 72. 独立な反復置換と実際の単体集合のホモトピー極限の Fubini

論文 補題 3.2・3.3 の導来 Fubini に向け、§71 の共通置換後の計算を
各行・外側を独立に置換する既存の実際のホモトピー極限の反復計算へ接続した。
任意の既存の生成された射影的模型について、図式の fibrancy と全成分の fibrancy の同値を
評価の右 Quillen 性と終対象への点ごとの fibration 判定で証明した。
二重図式が fibrant なら各行も射影的 fibrant であり、
内側の cofibrant 重みの錐関手が右 Quillen なので、内側の錐空間の列も外側で fibrant となる。
いずれの fibrancy も追加仮定として残さず、二重図式から導出した。

各行の錐空間からその指定 fibrant 置換後の実際の計算への比較を自然変換で構成し、
外側の指定比較と合成した。fibrant な二重図式上では、各行・外側の双方で
既存の実際の比較の弱同値の定理が適用できるので、この合成も弱同値である。
反復した実際のホモトピー極限は任意の図式の各二重添字での弱同値を保存することも
内側・外側の保存から証明し、共通置換の指定比較を反復計算で写した弱同値を得た。

これら二つの指定弱同値を局所化して自然同型にし、§71 の共通置換後の Fubini と合成した。
これにより、積添字の実際の単体集合のホモトピー極限と、各行・外側を独立に
実際の置換で計算する反復ホモトピー極限の自然同型を構成した。
導来定数関手とその比較を入力する一般形に加え、既存の局所化の普遍性から
その定数関手と指定比較を内部で構成する入口も公開した。
通常の極限や各次数の群の極限は使わず、実際の Quillen 導来関手の弱同値を比較した。

残る接続：この Fubini 同型と指定された錐・増強との整合性、
分裂余単体対象と細分の指定比較への適用、および L9 の Sp 内の Tot・hG への実現。
単体集合の計算の自然同型を、これらを全て満たす降下定理の完成とは数えない。
原典の τ 位相の層論を Čech 計算へ置換する方針は同じ。
(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§72 の保存検証：集約対象ビルドと公理監査が成功。181 モジュール・2093 宣言、標準三公理のみ。
区切りの全体ビルドは所有範囲外の `KST/DerivedBlowup/TwistTransitions.lean` で失敗。
詳細は `/tmp/l8-derived-cech-fubini-full-build.log` に記録し、`set -eo pipefail` で終了コード 1 を確認。
L8 の対象ビルド・監査は成功しており、import 閉包の破損ではない。
所有範囲外を変更・回避せず、指定錐・増強との整合性の証明を続ける。


## 73. 指定重みつき Fubini と錐・増強の随伴対応の保持

論文 補題 3.2・3.3 の指定 Čech 増強との整合性に向け、§70–72 の同型の構成を追跡した。
まず右随伴の一意性の指定同型が、同じ左随伴の同じ射の随伴像を保つことを
単位の比較と自然性から証明した。§70 の指定 Fubini 同型へ適用し、
外重みの錐と反復した錐の随伴像が、指定テンソル結合子を通じて一致することを得た。
同じ指定同型の単位・余単位の可換式も、右随伴の一意性の構成の公式から証明した。
同型の存在だけに留めず、構成済みの同型そのものが元の錐の評価を保つことを検査した。

導来側では §71 の導来テンソルと定数関手の同型の定義を評価し、
局所化からの fully faithful な制限の逆像が元へ戻る公式から、
その hom が実際の導来比較 α、指定重み増強 q、定数関手の比較 e の合成に一致することを得た。
可逆性から逆比較の可換式も得た。
この可換式と既存の実際の Quillen 随伴の導来 Hom の計算を合成し、
指定された増強 a : const X → F の導来定数随伴の像が、
q を使って得た元の重みつき錐の随伴像を導来したものに一致することを証明した。
増強 a・q と導来比較 α・β を全て保持する式である。

残る接続：§72 の合成 Fubini 同型全体と、導来した指定増強の比較を結び、
分裂余単体対象・細分の指定比較へ適用する。Sp の Tot・hG への実現は L9 と接続する。
原典の τ 位相の層論を Čech 計算へ置換する方針は同じ。
(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§73 の保存検証：集約対象ビルドと公理監査が成功。183 モジュール・2103 宣言、標準三公理のみ。
この保存単位では対象ビルドと監査を実行。全体ビルドの所有範囲外の失敗は §72 の記録どおり。


## 74. 導来比較の相関と実際の重み変更の指定増強の保持

論文 補題 3.2・3.3 の指定増強の整合性を追跡するため、§71 の重み変更の内部構成を正規化した。
存在定理から随伴と計算同型を別々に選ぶだけでは、両者が同じ導来比較 β から来るという
対応が型に残らず、増強の可換式へは進めない。この選択の分離を取り除いた。
左右の実際の導来関手とその指定比較 α・β・導来性を DerivedData に同時に保持し、
既存の totalLeftDerived・totalRightDerived とその指定比較からこのデータを実際に構成した。
このデータの存在を新しい入力にはせず、随伴と計算同型の両方を同じ α・β から構成する。
重み変更 comparisonIso の型を変えず、その内部をこの相関した構成による比較へ置き換えた。
§71–72 の自然同型としての主張はそのままである。

実際の計算同型について、元の錐空間から指定 fibrant 置換後の計算への射との合成が、
元の指定右導来比較 β に一致することを、β の自然性と計算同型の構成から証明した。
元の図式に fibrancy を要求しない。この式と §73 の指定増強の導来随伴の計算を合成し、
相関したデータの随伴像と実際の計算同型の可換式を得た。

最後に元の重みと既存の選択重みの相関した二つのデータを使い、
同じ定数関手の右随伴同型が同じ錐の随伴像を保つことを適用した。
comparisonIso の合成を実際に評価し、指定増強 a : const X → F をそれぞれの指定重み増強で
錐空間へ送った二つの像が、構成した重み変更の同型そのもので可換することを証明した。
任意の同型の存在へ弱めたり、増強の整合性を別の仮定にしたりはしていない。

残る接続：この増強を保つ重み変更と、§72 の反復した導来 Fubini の合成全体の指定増強を結ぶ。
分裂余単体対象・細分の指定比較への適用、Sp の Tot・hG への実現も引き続き残る。
原典の τ 位相の層論を Čech 計算へ置換する方針は同じ。
(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§74 の保存検証：集約対象ビルドと公理監査が成功。183 モジュール・2133 宣言、標準三公理のみ。
この保存単位では対象ビルドと監査を実行。全体ビルドの所有範囲外の失敗は §72 の記録どおり。


## 75. 増強つき図式全体の指定比較と実際の降下条件の重み不変性

論文 補題 3.2・3.3 の指定 Čech 比較を全ての増強つき図式の射に自然に扱う入口を構成した。
定数図式関手と図式の恒等関手の comma 圏に、増強元 X、図式 F、指定増強 const X → F を保持する。
元の空間と図式への両射影を使い、重み増強と指定増強の合成の随伴像を自然変換にした。
自然性は随伴の Hom の四角形と二つの指定増強の可換式から証明した。
既存の指定 fibrant 置換比較を合成し、選択された重みについては
実際の HomotopyCones の関手への指定増強比較を得た。

この指定写像が模型の弱同値になるという HasCechSpaceDescent を定義した。
これは実際の計算への指定比較の主張であって、降下の証明やその結論を公理にしたものではない。
§74 の指定増強の保持の式を comma 圏で束ね、重み変更の同型と指定比較が
関手全体で可換することを証明した。増強元・図式・増強の全てを同時に変えられる自然性を保持する。

局所化後の同型射との合成の消去から、指定比較の同型性が重み変更で不変であることを得た。
既存の模型の弱同値の飽和性の定理を用い、局所化後の同型性を実際の弱同値へ反映した。
これにより、任意の cofibrant な可縮重みでの指定比較の弱同値は、
既存の実際のホモトピー極限への指定比較の弱同値と同値になることを証明した。
導来定数関手とその比較も既存の局所化の普遍性で内部構成し、追加の入力にしていない。

残る接続：この指定降下比較を二重図式の反復計算と原来の前層の実際の Čech 図式へ渡す。
Fubini の合成全体の指定増強の保持、分裂余単体対象・細分への適用、Sp の Tot・hG への実現も残る。
原典の τ 位相の層論を Čech 計算へ置換する方針は同じ。
(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§75 の保存検証：集約対象ビルドと公理監査が成功。185 モジュール・2144 宣言、標準三公理のみ。
この保存単位では対象ビルドと監査を実行。全体ビルドの所有範囲外の失敗は §72 の記録どおり。


## 76. 外重みと二段の指定増強、重みつき Fubini の図式全体での保持

論文 補題 3.2・3.3 の指定比較を保持する Fubini のため、外重みの増強を二段の増強と同定した。
まず任意のモノイダル圏で、単位への二つの射の外テンソル増強が
結合子を通じて二段の指定増強に等しいことを、結合子の自然性と三角恒等式で証明した。
定数図式の二段の定数化と uncurry の自然同型を構成し、
外側の指定テンソル増強を内側のテンソル関手で写した後、内側の指定増強を合成した。
その実際の反復テンソル増強が、指定結合子を介して外重みの増強と可換することを
全ての入力空間と積添字で検査し、自然変換の等式として証明した。

§75 の増強つき図式の比較を任意の随伴と定数への自然変換へ一般化した。
既存の重みつき比較の型は変えず、この共通の構成を使う形へ整理した。
反復テンソル増強と実際の反復随伴から反復側の指定増強比較を直接構成した。
これは Fubini 同型の逆から定義した比較ではない。
上のテンソル増強の可換式と §73 の指定錐の随伴像の保持を合成し、
指定重みつき Fubini が二つの指定増強比較と、増強つき図式の圏全体で自然に可換することを得た。

残る接続：この式を §72 の指定 fibrant 置換・反復置換の比較と合成し、
実際の導来 Fubini 全体が指定増強を保持することを示す。
分裂余単体対象・細分への適用、Sp 内の Tot・hG への実現も残る。
原典の τ 位相の層論を Čech 計算へ置換する方針は同じ。
(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§76 の保存検証：集約対象ビルドと公理監査が成功。186 モジュール・2153 宣言、標準三公理のみ。
この保存単位では対象ビルドと監査を実行。全体ビルドの所有範囲外の失敗は §72 の記録どおり。


## 77. 指定増強を保つ実際の導来 Fubini と指定降下条件の同値

論文 補題 3.2・3.3 の二重 Čech の計算に向け、§72 の実際の導来 Fubini 同型全体が
指定増強を保持することを証明した。反復側の指定比較は、§76 の二つの指定重み増強と
行・外側を独立に置換する既存の比較から直接構成した。Fubini 同型の逆からは定義していない。

増強元を保持し、図式だけを指定 fibrant 置換へ送った増強つき図式と元からの射を取った。
外重みの指定比較の自然性により、元の重みつき計算への増強は置換後の生の錐への増強に一致する。
§74–75 の増強を保つ重み変更、§76 の指定重みつき Fubini、
反復指定比較の置換射に関する自然性を順に適用し、最後に共通置換の比較の逆を消去した。
構成済みの Fubini 同型の合成そのものを評価して証明した式であり、
指定増強の整合性を別の仮定にはしていない。
増強元・図式・増強の全てを動かす圏での自然変換の等式としてまとめた。

導来定数関手とその比較を既存の局所化から内部で構成する場合にも同じ式を適用した。
さらに実際の模型の弱同値の飽和性を使い、積添字の既存の実際のホモトピー極限への
指定増強比較が弱同値であることと、直接構成した反復指定比較が弱同値であることの同値を得た。
通常の極限や各次数の群の極限をホモトピー極限として使ってはいない。

残る接続：反復指定比較と各行の既存の増強比較を順に取る表示を同定し、
各方向の降下の貼り合わせ・分裂余単体対象・細分の比較へ適用する。
Sp 内の Tot・hG への実現は引き続き L9 と接続する。
この単体集合モデルの指定増強を保つ Fubini をもって、最小公理全体や定理 3.1 の完成とは数えない。
原典の τ 位相の層論を Čech 計算へ置換する方針は同じ。
(3.6)・TT・自然な blowup 列・E の実現も未完。

§77 の保存検証：集約対象ビルドと公理監査が成功。187 モジュール・2158 宣言、標準三公理のみ。
区切りの全体ビルドはルートの import 時に所有範囲外の
`InfinityCategories.F1B.RelativeFunctorHomotopyComposition` と
`InfinityCategories.F1.RelativeFunctorVertices` の `relativeFunctorVertex` 重複で失敗。
`set -eo pipefail` で終了コード 1 を確認。ログは `/tmp/l8-augmented-derived-fubini-full-build.log`。
L8 の対象ビルド・監査は成功しており、import 閉包の破損ではない。
所有範囲外を変更・回避せず、各行の指定比較による反復表示を続ける。


## 78. 各行の指定比較と実際の反復計算の表示

論文 補題 3.2・3.3 の各方向の降下を貼り合わせるため、二重図式の指定増強から
各行の増強つき図式の実際の関手を構成した。外側の各射の増強元の成分を恒等射にし、
curry した増強の自然性を comma 圏の可換式に使った。
この関手に既存の指定重み比較を前合成し、各行の比較を自然な外側の増強として束ねた。
各行の比較の自然性は追加仮定ではなく、この関手の構成から導出する。

持ち上げた随伴と curry/uncurry の指定随伴の Hom の対応を各成分で計算する補題を証明した。
合成随伴の Hom の公式を分解し、内側の随伴対応の始域自然性を各行で使うことで、
二つの重みの反復指定比較が、各行の重み比較の後に外側の指定比較を取る写像と等しいことを示した。
この段階では降下の結論や Fubini の同型自体を仮定していない。

各行の実際のホモトピー極限への指定比較も同じ行の関手で束ねた。
生の行の比較を内側の指定置換比較で写すと、各行の実際の比較に一致する。
これを外側の増強つき図式の間の実際の comma 射にし、
外側の指定ホモトピー比較の自然性を適用した。
その結果、直接構成した実際の反復比較は、各行の実際の比較を増強とする外側の
実際の指定比較に等しいことを証明した。行・外側の置換はいずれも既存の独立な構成である。
§77 の Fubini と合わせ、積添字の指定降下条件とこの外側の指定降下条件の同値も得た。

残る接続：各行の増強元が外側の各段で変わる別々に増強された二重図式を扱い、
各行の降下と外側の降下から積添字の降下を導く。
分裂余単体対象・細分への適用と、Sp 内の Tot・hG への実現も残る。
原典の τ 位相の層論を Čech 計算へ置換する方針は同じ。
(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§78 の保存検証：集約対象ビルドと公理監査が成功。188 モジュール・2175 宣言、標準三公理のみ。
この保存単位では対象ビルドと監査を実行。全体ビルドの所有範囲外の失敗は §77 の記録どおり。


## 79. 各行と外側の実際の降下の貼り合わせ

論文 補題 3.2・3.3 の二重 Čech に必要な、各行の増強元が外側の各段で変わる場合を実装した。
行の増強つき図式への実際の関手と、その行の増強元の列への外側の増強を comma 圏で保持した。
外側増強を内側で定数化し、各行の指定増強と合成して uncurry することで、
積添字の指定増強を構成した。各成分が二段の指定増強の合成であることも証明した。

元の各行と積添字化を戻した各行は、定義上同じとは仮定せず、
curry/uncurry の指定同型を保持した。外側増強を左成分、この同型の逆を右成分にした
各行への実際の comma 射を構成した。既存の実際の指定比較の自然性により、
積添字の各行の比較が外側増強と元の各行の比較へ因子化することを、自然変換の等式で証明した。

指定増強つき図式の同型による降下条件の移送を Arrow の同型から証明した。
増強元と図式の各点が弱同値な射の場合にも、既存の実際のホモトピー極限の弱同値の保存と
模型の飽和性で指定降下を比較する定理を供給した。局所化関手は実際に内部構成できる。

各行の実際の降下を、各行の指定比較の点ごとの弱同値として外側の実際の関手で写した。
その弱同値を外側の実際の降下比較と合成し、指定比較の自然性で行の計算後の外側の降下を得た。
指定 curry 同型で積添字化した行の外側の図式へ移し、§78 の増強を保つ Fubini の行表示へ渡した。
その結果、各行の実際の降下と外側の実際の降下だけから、積添字の実際の指定降下を証明した。
各行の増強元を全体の増強元と同一視していない。指定比較の整合性や積添字の降下を別の仮定にはしない。
局所化圏・関手も Mathlib の実際の局所化で内部構成する共通入口を公開した。

残る接続：原来の前層と幾何的な混合 Čech をこの二重増強図式へ移し、
分裂余単体対象・細分の降下へ適用する。Sp 内の Tot・hG への実現は L9 と接続する。
原典の τ 位相の層論を Čech 計算へ置換する方針は同じ。
(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§79 の保存検証：集約対象ビルドが 3822 jobs で成功。公理監査は 191 モジュール・2196 宣言、標準三公理のみ。
工程区切りの全体ビルドは所有範囲外の `KST/DerivedBlowup/PolynomialPushoutBaseChange.lean`
56 行の型不一致・70 行の `IsScalarTower` 合成失敗で終了コード 1。
ログは `/tmp/l8-double-cech-descent-full-build.log`。自分の import 閉包は成功しており、
所有範囲外を編集・回避せず、実際の指定比較の retract と前層への接続へ進む。


## 80. 前層の transfer から実際の指定ホモトピー比較の retract へ

論文 補題 3.2 のため、増強元と図式の両方を保持する retract を、指定ホモトピー比較の
矢の圏の retract へ移した。指定比較の自然性を用いた実際の構成であり、
図式の fibrancy や比較射の整合性を別の仮定にしていない。
模型の弱同値の retract 安定性から、実際の指定降下を元の増強図式へ戻した。

基底上の任意の幾何図式と元の前層の構造射からの指定増強を、明示した値域関手で写し、
指定増強を保持する空間図式への実際の関手を構成した。
前層射の構造射についての自然性が comma 射の可換性を与える。
関手で前層の retract を写して、元の前層の実際の指定降下を戻す定理を証明した。
既存の実際の底変換からの pullback と自然な transfer、正の局所 rank 公式を用いると、
底変換後の前層の実際の指定降下から元の前層の実際の指定降下が従う。
値域の加法性・有理線形性は前層の retract の構成だけに使うため、単体集合に要求していない。

残る接続：分裂余単体対象の実際の降下と細分を証明する。ここでは分裂側の降下を未証明の
結論として取り込まず、定理の入力に明示した。原典の τ 位相の層論を Čech 計算で置換する。
Sp 内の Tot・hG、(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§80 の保存検証：集約対象ビルドと公理監査が成功。193 モジュール・2205 宣言、標準三公理のみ。
全体ビルドは工程区切り §79 に記録した所有範囲外の失敗のまま。


## 81. 左随伴な添字への制限と実際のホモトピー極限

論文 補題 3.2 の分裂余単体対象の降下のため、添字前合成の実際の局所化を構成した。
前合成が元の点ごとの弱同値を保つことを検査し、局所化の因子化同型を指定比較として保持した。
添字随伴は前合成で向きを反転し、その随伴と同じ指定比較を局所化後の随伴へ移した。
定数図式と前合成の厳密な一致も、指定因子化同型を用いて局所化後へ持ち上げた。

元のホモトピー極限の左右の導来関手・比較・随伴を相関した同じデータから構成した。
一方の導来定数随伴に局所化した前合成随伴を合成し、定数図式の指定同型で始域を移すと、
他方の定数図式関手の右随伴が得られる。その右随伴の一意性と、両方の実際の計算同型を合成し、
左随伴な添字への制限で実際のホモトピー極限が局所化後に自然同型となることを証明した。
点ごとの弱同値での図式の局所化は Mathlib の実際の構成を内部で選べる。
通常の極限の保存や、定数図式が射影的 cofibrant であるとの誤った仮定は使っていない。

残る接続：この指定同型が増強を保つことを同じ導来データから検査し、
分裂余単体対象の添字と実際の extra degeneracy に適用する。
原典の τ 位相の層論を Čech 計算で置換する。
Sp 内の Tot・hG、(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§81 の保存検証：集約対象ビルドと公理監査が成功。195 モジュール・2219 宣言、標準三公理のみ。
この単位では対象検証を実施し、全体ビルドは §79 の工程区切りの記録を維持する。


## 82. 分裂余単体対象に向けた最小元を保つ添字圏

論文 補題 3.2 の分裂余単体対象を扱うため、有限非空順序と最小元を保つ単調射の実際の圏を構成した。
単体圏の広い部分圏とし、恒等射・合成が最小元を保つことを検査した。
単体添字の先頭に新しい最小元を自由に付加する関手を、零と後続元の像を指定して構成した。
この新しい最小元を持つ始域からの射の尾を取ると、元の順序から忘却した終域への任意の単調写像になる。
逆に任意の単調写像へ零を付加して逆対応を構成し、両側自然性から実際の随伴を証明した。

この添字圏では一点順序が始対象であることも証明した。
構成した実際の添字随伴を §81 へ渡し、自由な最小元の付加への制限により
実際のホモトピー極限が局所化後に自然同定されることを証明した。
ここでは単体集合の universe 0 での添字を使う。必要な大きさへの持ち上げは別工程。

残る接続：指定増強との可換式、始対象での値の実際の計算、
分裂 Čech の実際の拡張図式をこの添字へ構成する。
原典の τ 位相の層論を Čech 計算で置換する方針は変わらない。
Sp 内の Tot・hG、(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§82 の保存検証：集約対象ビルドと公理監査が成功。196 モジュール・2248 宣言、標準三公理のみ。
全体ビルドは §79 の工程区切りの記録を維持する。


## 83. 切断を持つ射の Čech nerve の実際の拡張

論文 補題 3.2 の分裂側のため、最小元を保つ添字全体へ実際の幾何図式を拡張した。
各段は最小元以外の座標の wide pullback とし、最小元の座標は基底射と固定した切断の合成、
その他の座標は指定射影とした。切断の恒等式と wide pullback の可換式から全座標が同じ基底上にあり、
添字射の像で座標を指定する lift を構成できる。
全座標との可換式を証明し、wide pullback の一意性で恒等射と合成を検査した。

自由な最小元の付加への制限は、元の Čech nerve と全射にわたって定義上同じである。
基底への指定増強も制限で元の増強そのものに一致する。
空座標の段は空族の lift を逆として指定基底射で基底と同型となる。
元の反変前層でこの幾何図式と指定増強を写す実際の拡張も構成し、
始対象での指定増強が元の指定基底同型の像であり、実際に同型となることを証明した。

残る接続：始対象で実際の指定ホモトピー比較を計算し、
添字随伴の同型が指定増強を保つことを検査して、元の Čech の実降下へ戻す。
原典の τ 位相の層論を Čech 計算で置換する。
Sp 内の Tot・hG、(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§83 の保存検証：集約対象ビルドと公理監査が成功。197 モジュール・2276 宣言、標準三公理のみ。
全体ビルドは §79 の工程区切りの記録を維持する。


## 84. 始対象での実際の指定比較の計算と分裂拡張の降下

論文 補題 3.2 の分裂側の拡張添字に向け、始対象での評価を定数図式の実際の右随伴にした。
Hom 同値は指定増強の始対象での成分を取り、逆に始対象からの射で全成分を作るものである。
同じ随伴をテンソル単位同型で移し、定数単位重みの実際の錐空間と評価の自然同型を構成した。
指定重み増強の随伴像が、この同型の下で指定増強の始対象での成分になることを証明した。

評価は射影的模型で右 Quillen なので、構成した随伴により定数図式は左 Quillen となる。
これで単位空間の cofibrancy を写し、定数単位重みの射影的 cofibrancy を実際に証明した。
一般の添字圏についてこの性質を仮定していない。
指定 fibrant 置換への自然性と指定錐の計算から、置換後の指定比較が
始対象での指定成分と置換比較の合成になることを証明した。
置換比較と錐同型を弱同値の合成から消去し、増強を保持する重み変更で元の実際の比較に戻すと、
実際の指定降下は始対象の指定増強成分の弱同値と同値となる。
局所化は Mathlib の実際の構成を内部で使い、元の図式の fibrancy は不要である。

切断を持つ射の元の空間値前層から、最小元を保つ添字全体の指定増強つき図式を束ねた。
§83 の始対象での指定基底同型の像とこの実際の判定を使い、拡張側の実際の指定降下を証明した。
この降下自体を追加仮定にはしていない。

残る接続：添字変更が指定増強を保つことを検査し、元の Čech の実降下へ戻す。
原典の τ 位相の層論を Čech 計算で置換する。
Sp 内の Tot・hG、(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。

§84 の保存検証：集約対象ビルドと公理監査が成功。200 モジュール・2291 宣言、標準三公理のみ。
工程区切りの全体ビルドはルートの所有範囲外の宣言重複、
`InfinityCategories.F1B.RelativeFunctorHomotopyComposition` と
`InfinityCategories.F1.RelativeFunctorVertices` の `relativeFunctorVertex` 重複で終了コード 1。
ログは `/tmp/l8-initial-cech-descent-full-build.log`。L8 の import 閉包は成功したため、
所有範囲外を編集・回避せず、指定増強を保持する添字変更へ進む。


## 85. 指定増強を保つ添字変更と元の分裂 Čech の実降下

論文 補題 3.2 のため、右随伴への前合成で重みを移す実際の計算を構成した。
添字前合成は射影的模型で右 Quillen であり、添字随伴により右随伴への前合成は左 Quillen となる。
この左 Quillen 関手で元の重みを写すことで、移した重みの射影的 cofibrancy を証明した。
テンソルの指定同型と前合成の実際の随伴を合成して錐同型を構成した。
合成随伴の Hom 対応を成分で計算し、添字随伴の単位についての指定テンソル増強の自然性を使って、
この錐同型が両方の指定重み増強と元の増強を保持することを証明した。
増強はこの同型の逆で定義せず、両方の指定射から可換式を導出した。

移した重みで元の添字圏の図式を fibrant 置換した後、錐同型と制限側の独立な置換比較を合成した。
元の置換の制限は射影的 fibrant なので、その独立な比較も弱同値となる。
生の錐同型の自然性と指定増強の式を二つの置換比較へ適用し、実際の二つの比較の可換式を証明した。
二つの置換の弱同値を合成から消去し、増強を保つ重み変更を用いると、
左随伴な添字への制限の前後で実際の指定降下が同値となる。

元の幾何的 Čech nerve と元の前層から、切断の選択に依存しない指定増強つき空間図式を構成した。
分裂拡張を自由な最小元の付加で制限すると、この元の指定図式に増強元を含めて一致する。
§84 の拡張側の実降下を、構成した指定増強を保つ添字変更で元の Čech へ戻すことで、
切断を持つ任意の射の元の指定 Čech 比較が実際に弱同値となることを証明した。
この分裂降下自体を追加仮定にしていない。
明示した SSet 模型・生成・テンソル bifunctor・mono cofibration の仮定の下で、
現状の元の Čech の適用は universe 0 の空間値前層についてである。

残る接続：実際の基底変更 Čech と transfer の幾何同型を空間の指定増強へ移し、
局所 rank 公式を持つ transfer と分裂降下から元の有限平坦降下へ接続する。
細分・blowup の実降下への接続と Sp 内の Tot・hG、
(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。
原典の τ 位相の層論を Čech 計算で置換する方針は同じ。

§85 の保存検証：集約対象ビルドが 3836 jobs で成功。公理監査は 204 モジュール・2317 宣言、標準三公理のみ。
全体ビルドは直前の工程区切り §84 の所有範囲外の宣言重複を記録したまま。


## 86. 底変換 Čech と自然な transfer からの実降下

論文 補題 3.2 のため、前層の実際の指定増強つき空間図式を元の余単体添字で扱う関手を構成した。
前層の値域からの関手と添字の大きさを、幾何の対象の universe から独立にした。
既存の二重反対圏の図式へ指定の二重反対の添字を前合成して、元の単体圏で比較できる。
元の前層を基底上に制限した図式は元の指定 Čech 空間図式と同型である。
実際の底変換前層の図式も、基底自身の引き戻し同型・全段の幾何同型・既存の増強の可換式を
同じ値域関手で写すことで、実際の底変換被覆の指定 Čech 空間図式と comma 圏で同型になった。

元の前層と実際の底変換前層の自然な transfer と正の rank 公式から得た retract を、
この全自然な空間図式の関手で写した。底変換被覆が切断を持つと、§85 の証明済みの実降下と
指定同型から底変換前層の実降下が得られ、retract 安定性で元の指定 Čech 比較へ戻る。
被覆への幾何的な持ち上げがある場合には、その実際の切断を内部構成した。
射自身を被覆に選べば対角切断が得られるので、自然な正 rank の transfer を持つ射の
元の指定 Čech 比較の実際の弱同値を証明した。分裂降下や底変換降下の同値自体は入力にしていない。

これは明示した SSet 模型下の空間値観測での結果であり、transfer は元の有理線形な値域に要求する。
有限平坦射の変動 rank は局所自由な chart の構成と Zariski の貼り合わせへ接続する必要がある。
Sp の実現、細分・blowup の実降下への接続、(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。
原典の τ 位相の層論を Čech 計算で置換する方針を維持する。

§86 の保存検証：集約対象ビルドと公理監査が成功。206 モジュール・2327 宣言、標準三公理のみ。
全体ビルドの所有範囲外の宣言重複は §84 に記録済み。


## 87. 元の混合 Čech の二重増強空間図式と実降下の反映

論文 補題 3.2・3.3 のため、各行が実際に降下するとき、積添字の指定降下と外側の指定降下が
同値であることを証明した。指定外側比較は増強元で恒等、図式の各点で各行の実際の比較なので、
その弱同値による反映と、増強を保つ Fubini・指定 curry 同型を合成すればよい。
外側の降下を先に仮定することなく両方向の同値を得た。

元の前層で増強つき幾何図式を反変に写す実際の関手を、Mathlib の反対圏の余単体化と
同じ前層による whiskering から構成した。幾何の混合 Čech の全行をこの関手で写し、
元の基底の前層の値から元の外側 Čech への指定増強を付加して実際の二重増強空間図式にした。
各行は実際の底変換被覆の指定 Čech 図式で、外側は元の外側被覆の指定 Čech 図式に一致する。

細分する被覆の各 Čech 段からの持ち上げは既存の零番目の射影と細分射で与えられ、
その実際の引き戻し切断に §85 の分裂降下を適用して各行の実降下を内部で証明した。
その各行の降下を二重図式の反映へ渡すと、混合積添字の指定降下は元の外側 Čech の実降下と同値になる。
各行の切断の外側の全単体射についての自然性は仮定していない。

残る接続：既存の混合 Čech の幾何の軸交換を、両方の指定増強を保持する空間図式の同型へ移し、
他方向の全行の実降下と合わせて元の被覆の降下を細分から反映する。
Sp の実現、blowup の実降下への接続、(3.6)・TT・自然な blowup 列・最小公理全体・E の実現も未完。
原典の τ 位相の層論を Čech 計算で置換する方針は同じ。

§87 の保存検証：集約対象ビルドが 3840 jobs で成功。公理監査は 208 モジュール・2338 宣言、標準三公理のみ。
全体ビルドは §84 の工程区切りの記録を維持する。


## 88. 混合 Čech の指定増強を保つ軸交換と実際の細分降下

論文 補題 3.2・3.3 のため、既存の幾何的な全図式の軸交換同型の逆を元の前層で反変に写した。
反変な像と uncurry の合成順序は定義上一致すると仮定せず、両方向の行の自然性で交換してから
元の前層の合成保存を用いて、空間図式の全単体射についての自然同型を証明した。

増強元は元の基底の前層の値の恒等同型を使う。
軸交換の逆の指定二射影の公式と、実際の Cartesian 正方形の可換式により、
二つの幾何的増強の合成を交換しても同じ基底射になる。
その式を元の前層で反変に写して、空間図式の自然同型が全体の指定増強も保持することを証明した。
積添字の交換の実際の随伴に §85 の指定添字変更を適用すれば、両方向の混合積添字の実降下が同値となる。

細分する被覆上では元の被覆の各行が分裂するので、§87 の証明済みの各行の実降下と Fubini で
混合積添字の実降下はその細分被覆の元の実降下と同値になる。
軸を交換し、他方向の各行の実降下を入力して Fubini の反映を適用すると、
元の被覆と細分被覆の指定 Čech 降下が同値となる。
元の被覆の各 Čech 段への底変換で細分被覆が降下する、という明示した入力による共通入口も公開した。
原典の τ 位相の層論を用いず、実際の混合 Čech・分裂降下・指定 Fubini・指定軸交換で細分降下を証明した。

残る接続：有限平坦の自然な transfer の各底変換への制限と、変動 rank を局所自由な chart と
Zariski 降下で貼り合わせる。blowup の実降下と自然な全次数列への接続も残る。
Sp の実現、(3.6)・TT・最小公理全体・E の実現も未完。

§88 の保存検証：集約対象ビルドが 3842 jobs で成功。公理監査は 210 モジュール・2346 宣言、標準三公理のみ。
工程区切りの全体ビルドはルートの所有範囲外の宣言重複、
`InfinityCategories.F1B.RelativeFunctorHomotopyComposition` と
`InfinityCategories.F1.RelativeFunctorVertices` の `relativeFunctorVertex` 重複で終了コード 1。
ログは `/tmp/l8-cech-refinement-descent-full-build.log`。L8 の import 閉包は成功しており、
所有範囲外を編集・回避せず、自然な transfer の底変換への制限へ進む。


## 89. 自然な transfer の全基底変更への制限と同じ rank の保存

論文 補題 3.2 のため、元の射を基底上の対象で引き戻すことと、その基底上へ先に射を引き戻してから
対象へ引き戻すことを、実際の二重引き戻しの指定同型で比較した。
同型と逆は二射影への指定 lift で構成し、両合成は引き戻しの普遍性で検査した。
第一射影を保つ式と、基底上の全射についての自然性を証明し、幾何関手の指定自然同型に束ねた。

その幾何同型を元の反変前層で写すことで、底変換した射の前層は元の底変換前層の制限に自然同型となる。
元の自然な pullback の成分公式と第一射影の保存を使い、この同型が指定 pullback を元の制限へ移すことを
自然変換の等式で証明した。同型の後に元の transfer の制限を合成して、底変換後の transfer を実際に構成した。
指定 pullback の比較式から、元の自然な rank 公式が同じ rank のまま任意の基底変更へ移ることを証明した。

正の rank の場合、実際に制限した transfer と証明済みの rank 保存を §86 の実際の Čech 降下へ渡すことで、
任意の基底変更後の元の前層の指定 Čech 比較が実際に弱同値となることを証明した。
底変換後の transfer の存在・rank 公式・降下を別の追加入力にはしていない。
これで細分降下の他方向の全行と、局所自由 chart 上の各 Čech 段へ同じ rank 公式を供給できる。

残る接続：変動 rank を持つ有限平坦射について、実際の局所自由 chart と Zariski 降下で貼り合わせる。
blowup の実降下と自然な全次数列への接続、Sp の実現、(3.6)・TT・最小公理全体・E の実現も未完。
原典の τ 位相の層論を Čech 計算で置換する方針を維持する。

§89 の保存検証：集約対象ビルドと公理監査が成功。213 モジュール・2367 宣言、標準三公理のみ。
全体ビルドは §88 の工程区切りの所有範囲外の宣言重複を記録したまま。


## 90. 基底上の局所性・射の局所検査・局所化後の transfer の正規化

論文 補題 3.2 の変動 rank の貼り合わせのため、二つの被覆間の細分射を必要としない
実際の指定 Čech 降下の基底上の局所性を証明した。
両方向の各行が実際に降下するとき、混合 Čech の指定軸交換で二つの外側の反映を結び、
二つの元の被覆の指定降下を比較する。各行を実際の底変換被覆の Čech 比較で書いた入口も供給した。

両側が実際の指定降下を満たす増強図式間の射について、図式の各点の弱同値から
増強元の射の弱同値を反映する定理を証明した。
指定比較の自然性と実際のホモトピー極限の弱同値の保存により、二つの降下比較を合成から消去する。
元の前層間の自然変換を実際の指定空間図式の関手で写すことで、元の Čech の各段での弱同値と
両側の実降下から、元の基底での射の弱同値を反映する結果も得た。

一般の自然な比較について、pullback と transfer の合成が始域・終域の両関手で同型なら、
矢の圏でその合成を逆にし、実際の retract に正規化できることを証明した。
これを実際の指定 Čech 比較の自然性に適用し、合成が増強元と図式の各点で弱同値なら、
局所化した矢の圏で正規化して元の降下を戻せることを証明した。
元の値域の加法性や、元の空間での厳密な scalar の逆・厳密な retract 恒等式を要求しない。
局所化は Mathlib の実際の構成を内部で使用する。

残る接続：実際の局所自由 chart の有限 Zariski 被覆と有限平坦 transfer の射影公式から、
変動 rank の合成の局所的な可逆性を供給して貼り合わせる。
blowup の実降下と自然な全次数列への接続、Sp の実現、(3.6)・TT・最小公理全体・E の実現も未完。
原典の τ 位相の層論を Čech 計算で置換する方針は同じ。

§90 の保存検証：集約対象ビルドと公理監査が成功。216 モジュール・2373 宣言、標準三公理のみ。
全体ビルドは §88 の工程区切りの所有範囲外の宣言重複を記録したまま。


## 91. 異なる有限型対象の有限非交和と変動 rank の成分

論文 補題 3.2 の局所自由 chart の有限和のため、異なる有限型対象の有限非交和を構成した。
構造射はスキームの標準非交和の desc を使う。局所有限型性は元の各成分から Zariski 局所性で導き、
各成分の準コンパクト性と有限な標準開被覆から始域の準コンパクト性を得た。
局所 Noether 性と合わせて任意の元の基底への構造射の準コンパクト性を供給し、同じ有限型の圏に収めた。
指定包含の非交和の普遍性をスキームから反映し、空の非交和も含む有限非交和の存在を構成した。

スキームへの忘却はこの実際の有限非交和を保存し、同型を反映することも証明した。
既存の引き戻しの保存と合わせ、スキームの有限 extensive 性を有限型の圏へ移した。
その有限非交和の普遍的余極限性から、任意の射で非交和の各成分を引き戻した対象も
元の対象の実際の非交和となることを、任意の有限添字の universe で証明した。

一般の極限を保つ関手間の自然な射について、各成分の同型による極限点の指定同型と自然性を比較し、
元の自然な射の極限点での成分も同型であることを証明した。
有理線形な値域で正の整数倍の恒等射の指定逆を構成し、成分ごとに異なる正 rank の作用へ適用した。
非交和の引き戻し成分を反対圏の有限積へ移せば、有限積を保つ前層の自然な作用は、
各引き戻し成分で異なる正 rank 倍であっても元の対象上で可逆となる。
ここでの有限積を Tot と呼ぶことはなく、Čech の降下の検査は §90 と別に接続する。

残る接続：Čech の零番目の座標を局所自由 chart の有限非交和へ射影し、
その引き戻し成分での射影公式と rank 作用を供給して §90 の局所検査へ渡す。
blowup の実降下と自然な全次数列への接続、Sp の実現、(3.6)・TT・最小公理全体・E の実現も未完。

§91 の保存検証：集約対象ビルドと公理監査が成功。219 モジュール・2408 宣言、標準三公理のみ。
全体ビルドは §88 の工程区切りの所有範囲外の宣言重複を記録したまま。


## 92. Čech の零番目の座標での変動 rank と実際の有限自由 chart

論文 補題 3.2 のため、有限非交和からの被覆の各 Čech 段を、零番目の座標を経由して
各成分へ引き戻した非交和として扱った。§91 の有限積による可逆性の反映で、
成分ごとに異なる正 rank の自然な作用は各 Čech 段で可逆になる。
これを任意の値域関手で空間に写し、§90 の実際の Čech 降下による局所的な射の検査へ渡すと、
元の基底での作用の像は実際に弱同値となる。値域関手が同型を反映する必要はない。

元の前層間の二つの自然な射を指定増強つき空間図式で全自然に写し、
各対象での合成の弱同値から、局所化後の正規化により元の前層の実降下を戻す入口も構成した。
元の値域から任意の値域関手で写した後に合成の弱同値を検査する形式も公開した。

元の有限型の圏内で、有限添字・開埋め込み・全基礎点の実際の持ち上げを持つ有限 Zariski 被覆の
幾何データを定義した。その有限非交和からの指定射の全射性を、指定包含の合成公式から証明した。
構成済みの有限平坦全射の有限自由 chart の実際の対象・包含・点の持ち上げをこの被覆に接続した。
各 chart の rank は元の選んだ正の有限基底の本数を保持し、その被覆の各 Čech 段の引き戻し成分の
rank 作用の等式から、元の基底の作用の弱同値を反映する定理を証明した。

未完の入力を区別する：各成分の rank の等式は有限平坦 transfer の射影公式と自由基底から供給する必要があり、
有限 Zariski 被覆での実降下は公理 (1) の正しい被覆族の Čech と有限非交和の保存から接続する必要がある。
今回の定理はこれらを明示した入力に保持し、有限平坦降下全体や最小公理の完成とは主張しない。
blowup の実降下と自然な全次数列への接続、Sp の実現、(3.6)・TT・最小公理全体・E の実現も未完。

§92 の保存検証：集約対象ビルドと公理監査が成功。223 モジュール・2441 宣言、標準三公理のみ。
全体ビルドは §88 の工程区切りの所有範囲外の宣言重複を記録したまま。


## 93. 有限被覆族そのものの Čech 図式と公理 (1)

論文 補題 3.2・3.3 と公理 (1) の接続として、被覆族の各添字の列に沿う実際の
多重引き戻しを構成した。単体射による座標の選択の恒等則・合成則を証明し、
反変前層の各多重交叉の値の有限積を用いて、実際の余単体図式と指定増強を構成した。
前層間の自然変換も全ての次数で写し、増強つき図式の圏への実際の関手を構成した。

有限 Zariski 被覆族のこの指定比較が弱同値であることを、公理 (1) の法則の型とした。
空被覆も含める。前層が非交和を積に写すことは前提に加えず、公理 (1) から導く工程に残す。
単一の非交和射の Čech のみでは非交和保存を導けないため、被覆族の積の図式を明示する。
実際の単体集合の模型構造と余極限を計算する入力は引き続き明示しており、
L9 の Sp による実現・E の法則の実証明とは区別する。
原典の τ 位相の層論を Čech 計算で置換する方針は同じ。

残る接続は空被覆からの空対象の値の可縮性、非交和の被覆族からの有限非交和の保存、
有限自由 chart の射影公式による局所 rank の式である。blowup の実降下から自然な全次数列、
(3.6)・TT・最小公理全体・E の実現・主定理も未完である。

§93 の保存検証：集約対象ビルドと公理監査が成功。226 モジュール・2474 宣言、標準三公理のみ。
全体ビルドは §88 の工程区切りの所有範囲外の宣言重複を記録したまま。


## 94. 空被覆の帰結と定数図式の実降下

論文 公理 (1)、補題 3.2・3.3 の被覆族の計算のため、終対象の定数図式の
実際の指定ホモトピー比較が弱同値であることを証明した。重みつき錐の右随伴が
終対象を保つこと、射影的図式の fibrancy と各成分の fibrancy の同値、
fibrant 図式の実際の置換比較の弱同値を使い、通常の極限の計算だけで止めなかった。
各段が終対象である増強つき図式の実降下から、元の値から終対象への一意射の弱同値も反映した。

有限型の圏内の空スキームに、空添字の実際の有限 Zariski 被覆を構成した。
各次数の添字の列は零番目の成分を持つので空であり、その値の空積は実際に終対象となる。
公理 (1) をこの被覆へ適用して、元の前層の空スキーム上の値から終対象への弱同値を証明した。
空対象の値の追加法則や有限非交和保存は前提に加えていない。

さらに、終対象を持つ任意の小添字圏から一対象圏への射影と、終対象を選ぶ関手の随伴を構成した。
一対象圏の始対象での指定比較の判定と、指定増強を保つ随伴添字変更を使い、
任意の空間の定数図式の恒等増強が実際に降下することを証明した。
元の空間の fibrancy は不要である。これを非交和の被覆族の比較先として使う。

有限非交和の被覆族による値の積との比較、および有限自由 chart の局所 rank の式は未完。
Sp の実現・blowup の実降下と自然な全次数列・(3.6)・TT・最小公理全体・E の実現・主定理も未完。
原典の τ 位相の層論を Čech 計算で置換する方針は同じ。

§94 の保存検証：集約対象ビルドと公理監査が成功。229 モジュール・2496 宣言、標準三公理のみ。
全体ビルドは §88 の工程区切りの所有範囲外の宣言重複を記録したまま。


## 95. 被覆族の各段の有限積の弱同値

論文 公理 (1)、補題 3.2・3.3 の非交和の被覆族の比較のため、
任意の有限添字の積が成分ごとの実際の弱同値を保つことを証明した。
まず Cartesian テンソルの両射影を使い、Option 添字の指定積と先頭の値・残りの指定積の
テンソルとの指定同型を構成し、その同型が元の各成分の射に自然であることを証明した。

cofibration が単射であるという模型の入力から全ての単体集合の cofibrancy を導き、
左右のテンソルの左 Quillen 性と cofibrant 対象間の弱同値の保存で二項テンソルの弱同値を得た。
空積、Option の分解、添字の同値についての有限帰納で、任意の有限添字の Pi.map の弱同値を証明した。
右 Quillen 性だけで全ての弱同値の保存を主張せず、元の各値の fibrancy も要求しない。

これにより、空の交叉の値を §94 の終対象への弱同値で置換する際、
有限被覆族の Čech の各段でその置換の弱同値を検査できる。
非交和被覆の幾何の多重交叉と指定増強を保つ比較への接続は引き続き未完。
Sp の実現・blowup の自然な全次数列・局所 rank の式・(3.6)・TT・最小公理全体・E の実現・主定理も未完。
原典の τ 位相の層論を Čech 計算で置換する方針は同じ。

§95 の保存検証：集約対象ビルドと公理監査が成功。231 モジュール・2509 宣言、標準三公理のみ。
全体ビルドは §88 の工程区切りの所有範囲外の宣言重複を記録したまま。


## 96. 非交和被覆の多重交叉と指定対角比較

論文 公理 (1)、補題 3.2・3.3 の非交和被覆の計算として、同じ単射の成分を繰り返す
多重交叉の零番目の射影と対角が指定逆であることを証明した。
全ての単体射について指定射影と指定対角の自然性も証明した。
有限 extensive な圏の非交和被覆で異なる二つの成分が現れる場合、
その多重交叉を互いに素な二つの包含の引き戻しへ写した。
その引き戻しが始対象であることと始対象の厳密性から、多重交叉そのものが始対象となる。

定数の添字の列の積射影の後に指定対角を前層で写した射を合成し、
有限被覆族の実際の余単体図式から各成分上の値の積の定数図式への自然変換を構成した。
この自然変換は、元の被覆射の引き戻しを束ねた指定比較と全次数で可換する。
元の比較を左成分に持つ増強つき図式の圏の射として束ね、
通常の積の対象ごとの同型に留めず実際の降下の比較へ渡せる形とした。

各次数のこの射の弱同値は、非定数の添字の列に対応する空の交叉を除く有限積の計算へ残す。
空の交叉の値は §94、有限積の弱同値は §95 で既に証明済みである。
有限自由 chart の局所 rank、Sp の実現、blowup の自然な全次数列、
(3.6)・TT・最小公理全体・E の実現・主定理も未完。
原典の τ 位相の層論を Čech 計算で置換する方針は同じ。

§96 の保存検証：集約対象ビルドと公理監査が成功。233 モジュール・2543 宣言、標準三公理のみ。
全体ビルドは §88 の工程区切りの所有範囲外の宣言重複を記録したまま。


## 97. 公理 (1) から有限非交和の値の比較と実際の局所 rank 検査

論文 公理 (1)、補題 3.2・3.3、(3.8) へ向けて、有限積から指定部分の添字だけを残す射を構成した。
補成分が実際に終対象である場合は、一意射を用いる指定逆を構成した。
補成分が弱可縮である場合には、その補成分だけを終対象へ置換する有限積の弱同値と
指定部分積への同型を比較して、元の指定制限射の弱同値を証明した。因子の基点や fibrancy は不要。

定数の添字の列は零番目の座標によって元の添字と同値である。
この添字変更と元の幾何の対角同型を同時に積へ写し、
部分積への制限と指定同型の合成が §96 の対角比較そのものに一致することを証明した。
非定数の列の交叉は実際に始対象なので、忘却の有限非交和保存により underlying scheme は空である。
§94 の空被覆の帰結を使い、この空の交叉の値を除けば、各段の指定対角比較は弱同値となる。

明示的な有限型非交和と標準非交和の指定余極限同型を構成し、
スキームの標準非交和の実際の開被覆の点の持ち上げを標準非交和へ移した。
標準包含そのものの開埋め込み性を証明し、同じ包含による有限 Zariski 被覆を得た。
公理 (1) をこの被覆へ適用し、値の積の定数図式の実降下と各段の対角比較の弱同値を比較して、
有限非交和上の値から各成分上の値の積への元の指定比較が弱同値であることを証明した。
有限非交和保存を別の基本公理には加えていない。

さらに、有限被覆族の全ての多重交叉での弱同値を基底へ反映する局所検査を証明した。
各段の射は元の自然変換の各成分の有限積であり、§95 の有限積の弱同値保存を適用した。
公理 (1) から両側の実降下を直接供給する形も公開した。
各交叉の零番目の成分の正 rank 倍となる自然な作用は、正 rank の指定逆で各交叉で可逆であり、
任意の値域関手で空間へ写した後に基底で弱同値となる。
各 chart 上の任意の対象での rank の式を、零番目の指定射影でこの計算へ渡す入口も構成した。
実際の有限自由 chart の元の正基底の本数をこの入口に接続した。

§92 の入口と比べ、この新しい被覆族を直接使う入口では前層の有限積保存や
単一の非交和被覆射の降下を別に前提にしない。局所 rank の等式は有限平坦 transfer の
射影公式から供給すべき明示した入力に残している。
これは同じ Čech 証明方針の公理 (1) への接続であり、Sp による全次数の実現や有限平坦降下全体の完成ではない。
blowup の自然な全次数列、(3.6)・TT・最小公理全体・E の実現・主定理も未完。
原典の τ 位相の層論を Čech 計算で置換する方針は同じ。

§97 の保存検証：集約対象ビルドと公理監査が成功。240 モジュール・2579 宣言、標準三公理のみ。
工程区切りの全体ビルドは共有ルートの所有範囲外の宣言重複で失敗。
`InfinityCategories.F1.RelativeFunctorVertices` と `InfinityCategories.F1B.RelativeFunctorHomotopyComposition` の
`relativeFunctorVertex` が重複している。13598 ジョブ中、ルートで終了コード 1。
ログは `/tmp/l8-zariski-family-full-build.log`。L8 の import 閉包・集約ビルド・監査は成功しており、回避策は作らない。


## 98. Over 上の変動 rank の transfer と元の実 Čech 降下

論文 公理 (1)・(4)、補題 3.2 のため、有限 wide pullback を保つ関手で
元の多重交叉の幾何を移す指定同型を構成した。各座標・基底の射影を保ち、
単体射について両方向の自然性を持つ。同型を反変前層で写して有限積に束ね、
指定増強を保つ実際の余単体・増強つき図式の同型を構成した。
スライス圏の忘却は connected な wide pullback を保つので、
元の被覆族とその同じ構造射での Over 内への持ち上げの指定空間図式を同定した。
Over の忘却による終対象や非連結な有限極限の保存は仮定しない。

元の有限 Zariski 被覆族を任意の構造射へ、実際の finiteTypePullback で底変換した。
各包含の開埋め込み性は底変換で保たれ、点の持ち上げは元の点の持ち上げと
スキームの引き戻しの実際の点から構成した。同じ有限添字と各 chart の正 rank を保持する。
第一射影を元の基底上の Over 射に束ね、底変換した chart 上の対象から元の chart への射を得た。

Over 上の自然な作用について、各 chart 上の対象の rank 公式を、
Over 内の各多重交叉の零番目の指定射影に適用した。元の前層の公理 (1) の実降下を Over へ移し、
chart ごとの正 rank の作用の弱同値を元の構造射の対象へ反映した。
同じ chart を各構造射へ底変換し、Over 上の全ての成分で合成が弱同値となることを証明した。
作用を元の圏上の自然変換へ任意に延長することはない。

元の pullback と transfer の二つの自然変換を、元の Čech の指定増強つき図式の関手で写した。
その合成が全対象で弱同値なら、増強元と全段でも合成は弱同値となる。
局所化後に合成を正規化する証明済みの retract と、実際の底変換被覆の分裂降下を使い、
元の被覆の実 Čech 降下を戻した。自身による底変換では対角切断を内部構成する。

これらを合わせ、元の有限 chart ごとに異なる正 rank の合成公式から
元の射の実際の指定 Čech 比較の弱同値を証明した。
構成済みの有限平坦全射の有限自由 chart と元の正基底の本数へも接続した。
大域で共通の rank、有限非交和保存、単一 Zariski 被覆射の降下は前提にしない。
局所 rank の式は公理 (4) の射影公式と自由基底から供給すべき入力に残す。
この法則の実現、Sp への実現、blowup の自然な全次数列、
(3.6)・TT・最小公理全体・E の実現・主定理は引き続き未完。
原典の τ 位相の層論を Čech 計算で置換する方針は同じ。

§98 の保存検証：集約対象ビルドと公理監査が成功。248 モジュール・2620 宣言、標準三公理のみ。
全体ビルドは §97 の工程区切りの所有範囲外の宣言重複を記録したまま。


## 99. 同じ局所 rank の公式による全底変換と細分先の実降下

論文 公理 (4)、補題 3.2・3.3 のため、底変換後の pullback と transfer の合成は
元の二つの自然変換の合成を制限したものに厳密に一致することを証明した。
既存の指定二重引き戻しの比較が pullback を保つ式を使い、対象ごとの存在でなく自然変換の等式を得た。
この等式により、元の合成の全対象の弱同値は任意の値域関手での観測後も全底変換へ移る。
この移送自体には rank や値域の線形性は不要である。

§98 の、元の有限 chart の正 rank の合成公式による Over 上の全対象の弱同値を
この指定式で底変換した transfer へ移した。既存の分裂した自己底変換からの
実降下の移行に適用し、元の射の任意の底変換の指定 Čech 比較が弱同値であることを証明した。
構成済みの有限平坦全射の実際の有限自由 chart と正基底の本数による入口も公開した。
底変換ごとに chart・transfer・rank 公式・降下を選び直したり、新たな仮定にしたりしない。

同じ元の合成の全対象の弱同値を使い、元の被覆への幾何的な持ち上げがある場合は
実際の底変換の切断を内部構成して、細分先の指定 Čech 降下も得た。
有限自由 chart の元の rank の式をこの持ち上げの場合へ渡す入口も公開した。
これで、構成済みの有限平坦な細分を実際の空間での指定降下へ接続する準備が整った。

射影公式からの元の局所 rank の式、公理 (4) 全体の実現、Sp の実現、
blowup の実降下からの自然な全次数列、(3.6)・TT・最小公理全体・E の実現・主定理は未完。
原典の τ 位相の層論を Čech 計算で置換する方針は同じ。

§99 の保存検証：集約対象ビルドと公理監査が成功。251 モジュール・2627 宣言、標準三公理のみ。
全体ビルドは §97 の工程区切りの所有範囲外の宣言重複を記録したまま。


## 100. 主経路の Tot の実現を正本へ戻す設計変更案（判断待ち）

### 確認した問題

正本 `k-theory-kst-route.md` §13 の決定 1 はモデル構造を coherent nerve（γ3）にだけ使う。
決定 3 は γ-B の Kan 複体による Ω スペクトルを採り、Tot・hG をレベルごとの Kan 複体で構成し、
HT-KQ を主定理経路外に置く。決定 9 はこの対象を BF の単射な構造射の模型へ具体化している。
L9 の `PointedHomotopyLimit.lean` は N の実際の Bousfield–Kan end とホーン充填による Kan 性を使い、
L9 計画も HT-KQ や Reedy モデル圏を使わないことを明記している。

一方、L8 の `homotopyCechAugmentation` は `HomotopyCones.functor` を使い、
`ModelCategory SSet`、cofibrantly generated な射影的模型、cofibration が mono であること、
テンソルの Quillen bifunctor 性の入力を持つ。§93 の `FiniteZariskiCechDescent` もこの比較で述べている。
これらの仮定は追加の公理として宣言しておらず、標準三公理の監査は成功している。
ただし、この条件付き補助結果から、正本のモデル構造を使わない主経路が完成するとは言えない。
既存の条件付き模型圏エンジンを、単なる「L9 の実現待ち」として主経路へ接続する判断は修正が必要である。

また、§98・99 の局所 rank からの入口は、補助値域 V の Preadditive・Linear ℚ を使う。
L9 の実際の Ω スペクトルの通常の圏にこれらの構造があるとは確認していない。
元の Sp の射を有理数で厳密に割るのではなく、実際の全次数 π_* で rank を検査し、
L9 の π_* 同型の判定を使う主経路にしなければならない。

### 提案する変更（まだ実装・承認していない）

1. 主経路の指定増強比較を、L9 の実 `PointedHomotopyLimit`、Tot、整数次数の π_* の構成に対して定義する。
   `ModelCategory SSet` は主定理の仮定・最小公理の構造体に入れず、
   Theorem31 の証明をこの仮定付きの補助定理に依存させない。
   通常の次数ごとの極限を Tot と呼ぶ置き換えはしない。
2. L8 内で、指定比較を保持する Fubini、分裂余単体対象の降下、随伴添字変更、細分を、
   実 Bousfield–Kan end の切断・自然性・ホモトピー不変性に対して証明する。
   N/L9 の所有ファイルは読み取りだけとし、必要な L8 側の証明は Descent 内に置く。
3. 模型圏側の検証済みの補助結果は削除・書き換えによる再解釈をせず、比較用の条件付き結果として保持する。
   これらを主経路の証明済み部分へ暗黙に読み替えない。
4. 有限型の圏、有限被覆族の多重交叉、自然変換としての transfer、底変換、
   指定対角、軌道正方形、中心・次元の帰納は再利用する。
   これらの模型圏に依存しない定義・証明と、模型圏側の補助結果の import を分ける。
5. transfer の自然な合成は元の Sp 上に保持し、局所 rank 公式は各整数次数の π_* で供給する。
   正 rank の逆を使うのは有理加群の観測先だけとし、元の Sp の通常の圏の ℚ 線形性は要求しない。
6. 最小公理 (1)・(2) は実 Tot・実ファイバーの指定比較で述べる。
   L9 の自然な長完全列の界面を通して既存の `NaturalBlowupSequences` への帰結を証明し、
   LES の帰結だけを抽象 blowup の実降下の定義に置き換えない。
7. 定理 3.1 は引き続き全次数の指定 π_* 比較の同型とする。
   (3.6) は K0・T2 の明示的な界面に対して書き、E の実現は L4・L10 の成果へ接続する。

| 範囲 | 保存する検証済み結果 | 主経路で新たに必要なもの |
| --- | --- | --- |
| 幾何と群の作用 | 有限型、還元、軌道正方形、有限自由 chart、平坦化、次元・成分帰納 | 実 Tot の指定比較への接続 |
| Čech の被覆族 | 実多重交叉、単体射、指定増強、Over と底変換、非交和の対角 | モデル構造を使わない各段の π_* 同型・降下の反映 |
| transfer | 実 pullback、自然な transfer、二重底変換と合成の厳密な一致 | 各整数次数の rank 公式から元の指定比較へ戻す実 BK/Tot の証明 |
| 模型圏側の Čech | §70–99 の条件付き実計算 | 比較用補助として保持。主経路の完成には数えない |
| 主定理 | 条件を明示した π_* 比較と幾何の帰納 | 最小公理の実現を前提にした Theorem31 の結合 |

### 判断のための状態

これは証明済みの設計変更ではなく、正本に合わせるための具体的な変更案である。
現時点で `theorem_3_1_K0`、`supportedRankK0_descent`、最小公理全体、E の実現は未完である。
他レーンのファイルを修正せず、引用・追加公理・sorry を導入しない条件は維持する。
ユーザー指定の「設計変更の提案で停止」に従い、この案の判断を待つ。
ゴールを達成扱いにはしない。

§100 の提案保存時の確認：集約対象ビルド成功、公理監査は 251 モジュール・2627 宣言で標準三公理のみ。
Lean の宣言は変更していない。ログは `/tmp/l8-bk-design-review-target.log` と `/tmp/l8-bk-design-review-audit.log`。


## 101. 承認された主経路と条件付き補助の分離

§100 の提案 1–7 はユーザーが承認し、正本 §13 決定 15 に記録済み。
判断待ちの状態は終了。指定された順で主経路を組み直す。
`Descent.Auxiliary` は従来の全 import を保持し、既存56ファイルは変更しない。
`Descent.Main` とルートの `Descent` は模型圏に条件づけた56モジュールを import しない。
全体の公理監査は Auxiliary も明示的に import して従来の結果を検査し、
別の主経路監査は実際の import 閉包に56モジュールがないことを検査する。

| 工程 | 補助（条件付き） | 主経路 |
| --- | --- | --- |
| 幾何・作用・次元帰納 | 保存 | 既存の模型圏に依存しない部分を再利用 |
| 指定 Čech 比較 | §70–99 の比較を保存 | L9 の実点つき Tot へ乗せ替え中 |
| Fubini・分裂・添字変更・細分 | 条件付きの既存結果を保存 | 実 Tot/BK end の指定比較に対して証明予定 |
| transfer・局所 rank | ℚ 線形な補助値域の結果を保存 | 元の Sp の自然変換、各整数次数の観測で検査予定 |
| 最小公理 (1)(2) | 旧模型圏側の法則を保存 | 実 Tot・実 fiber の指定比較で構築予定 |
| 最小公理全体・定理 3.1 | 未完成 | 全体の構造体・主定理の #check を完成時に監査へ追加 |
| 監査 | 全補助の標準三公理監査 | 56モジュールの import 排除と公開型の記録 |

API の確認：`ContractibleTotalSequence` は全空間のホモトピー群が自明な fiber 列の次数移動で、
extra degeneracy の降下を直接述べるものではない。
Tot の段ごとの π_* 同型保存は `TotalizationHomotopyInvariance` にあり、
`CosimplicialKanMapEquivalence` は Reedy 置換の各段の π_* 同型を述べる。
`PointedTotalization`・`ReplacedTotalization` に点つき対象・基点・置換した Tot の API があるので再利用する。
この名前の相違は設計変更を要さず、実際の宣言を用いる。

### §101 の主要宣言と検証

| 宣言／入口 | 現在の意味 |
| --- | --- |
| `Descent.Main` | 条件付き56モジュールを含まない主経路の集約 |
| `Descent.Auxiliary` | 従来の import をそのまま保持する比較用入口 |
| `Main.AugmentedTotDiagram` | 点つきの増強元と実余単体図式の comma 圏 |
| `Main.rawTotComparison` | 指定増強から L9 の通常の実 Tot への基点保存射 |
| `Main.totComparison` | Reedy 置換の実際の単位を合成した Kan Tot への指定射 |
| `Main.HasTotDescent` | この指定射の全基点・全自然数次数の空間側の π_* 同型 |
| `Main.rawTotComparison_naturality` | 増強元と図式を同時に動かす指定比較の自然性 |
| `Main.totComparison_naturality` | 置換した Tot まで含む指定比較の自然性 |

上記の空間側の条件を Sp の全整数次数の条件に読み替えない。
最小公理全体・定理 3.1 全体の型はまだ宣言しておらず、最終的な `#check` は未実装である。
現存する前層・全次数比較・sectioned 降下・実 Tot の公開型を主経路監査に記録した。
そのログに `ModelCategory`・`CofibrantlyGenerated`・`IsQuillenBifunctor` が無いことを確認した。
56 モジュールの定義ファイルは無変更で、import 閉包による排除検査も成功した。

保存単位の検証：対象ビルドは 4622 jobs 成功。
主経路監査は 1470 宣言、補助を含む監査は 252 モジュール・2637 宣言で標準三公理のみ。
ログは `/tmp/l8-main-separation-target.log`、`/tmp/l8-main-separation-main-audit.log`、
`/tmp/l8-main-separation-full-audit.log`。
次は一般形状の実点つき homotopy limit の指定比較、および実 Tot の分裂・細分へ進む。


## 102. 実 end の指定比較と段ごとの不変性

| 宣言 | 主経路で証明した内容 |
| --- | --- |
| `Main.underlyingAugmentationCone` | 元の指定増強の基礎の実錐 |
| `Main.homotopyLimitComparison` | 実 `PointedHomotopyLimit` への基点保存比較 |
| `Main.homotopyLimitComparison_naturality` | 元と図式を同時に動かす指定比較の自然性 |
| `Main.HasHomotopyLimitDescent` | 実 BK 比較による空間側の π_* 判定 |
| `Main.hasHomotopyLimitDescent_iff_of_stagewise_piIsomorphism` | 段ごとの同型と元の同型による保存・反映 |
| `Main.hasTotDescent_iff_of_stagewise_piIsomorphism` | 実 Reedy Tot の同型保存と指定比較の正方形による保存・反映 |
| `Main.augmentationCone` | 増強を元の点つき錐として保持 |
| `Main.weightedEndComparison` | 任意の実 `PointedWeightedEnd` への指定比較 |
| `Main.weightedEndComparison_naturality` | 指定 end 比較の自然性 |
| `Main.weightedEndComparison_underlying` | 忘却後も N の元の指定比較と一致 |
| `Main.weightedEndComparison_bousfieldKan` | BK 重みで一般形状の指定比較と一致 |

細分射の各段が同型であるという幾何・添字側の結論は、これらの不変性だけでは証明していない。
Fubini・extra degeneracy 降下・随伴添字変更は引き続き未完。
Sp の整数次数の接続と最小公理全体の構造体・主定理も未完である。
L9 の `PointedWeightedConeUnderlying` の基点を含む既存の実比較を読み取りで再利用した。
N・L9 のファイルは変更していない。

対象ビルドは 4646 jobs 成功。主経路は 1485 宣言、補助を含む監査は
255 モジュール・2652 宣言で標準三公理のみ。56 条件付きモジュールの排除も成功。
公開型のログに模型圏・cofibrant generation・Quillen bifunctor の三仮定はない。
ログは `/tmp/l8-main-weighted-target.log`、`/tmp/l8-main-weighted-main-audit.log`、
`/tmp/l8-main-weighted-full-audit.log`。


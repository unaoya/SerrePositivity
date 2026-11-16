# 整理 OE-W1 報告

## 0 段0：範囲・配置・分類・目録案（2026-11-16）

基準main：**30ae8948f339beec42d9340feb02f2031c22c72b**（49967c102を祖先に含む）。このmainから、旧worktree SerrePositivity-bs-d68で枝 **refactor/organize-einfinity** を作成した。IS-W2の枝math/inf-supply-bと検証済みの履歴は保持している。指示書organize-einfinity-general.md §0〜§4と、KL-W1の配置・名前空間の規則、B3/B3′の保存比較・追従資料、⑤dのresearch/g12-monad-route/README.mdを読んだ。主張・証明の変更、宣言削除、drafts、⑤aの界面の型、BSの数学の実装には入らない。

### 0.1 段1の全件移動表・旧名と新名

3b-4の274本と、周辺三ディレクトリ357本の和集合は**588本・43,633行**。重複43本を一度だけ数えた。内訳は移動456本と現位置を保つ132本。個別の旧パス→新パス、旧module→新module、旧namespace→新namespace、行数、原ソースSHAは **organize-einfinity-w1/stage1-modules.csv（588行）** に全件記録した。module-map.jsonとnamespace-targets.jsonも同じ資料に置く。

| ID | 元の束 | 件数・行数 | 移動先・扱い |
|---|---|---:|---|
| OE01 | 274本中、既にEInfinity外の一般部品 | 132本・8,821行 | Kerodon／HomotopicalAlgebra等の現位置を保持。入口・引用・保存比較の対象から外さない |
| OE02 | EInfinity/HomotopyWeight/ 全体 | 61本・4,697行 | HomotopicalAlgebra/Diagram/HomotopyWeight/。BK重み・Kan係数・射影cofibrancy・重み付き切断 |
| OE03 | EInfinity/FrameHom/ 全体 | 144本・10,729行 | 142本は HomotopicalAlgebra/HomotopyFunctionComplex/FrameHom/。下の二本はKerodonのKan複体の節 |
| OE04 | EInfinity/SimplicialLocalization/ 全体 | 152本・12,011行 | InfinityCategories/HA/ModelCategoryComparison/SimplicialLocalization/。HA 1.3.4とDwyer–Kanの単体的局所化・模型圏の比較 |
| OE05 | 3b-4のBE固有のTot比較 | 99本・7,375行 | EInfinity/BarrattEccles/StoppedRoutes/ISW2Tot/。停止済みの経路であることをmodule docstringに一行追加 |

OE03の例外：AnodyneWeakDetection.leanは模型圏を仮定しないKan標的／anodyneの検出なので、**InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/**へ置く。AnodyneFamilyHomotopy.leanは全パラメータのinterval族の不変性を用いるため、**InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/MorphismSpaces/**へ置く（段1準備の静的予覧で修正）。任意の模型圏のframeを使うものと分ける。HA配置のOE04もportableな∞中核への格上げを意味しない。

名前空間は新しい数学の配置に合わせる。OE02はSerrePositivity.EInfinity.HomotopyWeight→SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight、OE03の142本はEInfinity.FrameHom→HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom、OE04はEInfinity.SimplicialLocalization→InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization。上のAnodyne二本はファイル別の表を優先する。

OE05は**99ファイルが所有する宣言だけ**をEInfinity.BarrattEccles.StoppedRoutes.ISW2Totへ移す。EInfinity.BarrattEccles全体の文字列置換はしない。operad・既存CAlg_R・既存FramedLimit・他のBE実装の宣言は元の名前のまま。元の同じ型・同じ射・指定path・証明を保存する。互換aliasやwrapperを新設して宣言を増やす案は取らず、利用側のimportと実際の参照を機械的に追従させる。

source-declaration-map.csvにはソース上の名前付き宣言候補**2,314行、うち名前変更候補1,884行**の旧名→新名・所有元を記録した。これはnative環境の全宣言数ではない。匿名instance、生成された宣言、privateのkernel名、既存の別namespaceへの拡張は、準備で原環境を採取して所有元を確定し、正式な書換表と保存比較用の表を作る。ファイル名から宣言の所有元を推測して適用しない。

### 0.2 範囲・層・引用と検査の見込み

移動対象は§1の588本の範囲内。HA/Monads/179本は**置き場所の検討だけ**にとどめる。現状は一般の∞モナド／walking adjunctionの部品で、179本のソース中にBarrattEccles・CAlg_Rへの明示的な適用は0本。HA 4.7の現位置と既存の停止経路の目録を保つ案とし、BEへの新しい適用は追加しない。

直接の外部importerは**203ファイル**（EInfinity 180、InfinityCategories 15、KST 7、EInfinityの集約入口1）。移動以外のこれらのソースは、同じ宣言を参照するmodule/import/名前の追従だけを対象とする。BSの本体への直接のimport追従候補は0。実際の短名の束縛は原環境のcollectで確認する。rootと正式監査のmodule一覧、層のmetadata、対応表の所有元リンク、移動した宣言の引用は同じ束で移送し、監査範囲を落とさない。

範囲外の既存EInfinityへの直接依存は**82辺**（Hammock 58、BarrattEccles 19、ComplexLimits 2、PowerOperation 1、FrameRealizationLifting 1、Interface 1）。stage0資料static-imports.jsonに全辺を残す。段1だけでEInfinityの全一般部品の依存を消したとは言わない。Hammock等を依存閉包として勝手に段1へ引き込まず、既存の辺を保持する。境界や層を証明変更なしに移せないファイルは取り下げ、元位置に残して記録する。

現行layers.jsonの五段の割当では、この588本は全てConsumers（非∞ファイルの既定を含む）。移動だけを理由にPortableへ格上げしない。各ファイルのtier、実装境界、承認済み逆辺の理由を同じmodule対応で移送し、原グラフと移送後グラフの対応を照合する。新しいnamespaceで古い例外を余分に広げない。実際の逆辺・衝突・孤立したimport・循環を先に調べる。

文献の対応候補は現在のKerodonレビューから**6行**：AnodyneWeakDetection.isWeakHomotopyEquivalenceにown 4件（3.1.7.14、3.3.6.7、3.3.6.8、3.3.7.4）、FrameArrows.nerveMap_leftAdjoint_isLeftCofinalにpartial 7.2.3.7、modelBifibrantSourceRightKanExtension_refl_of_frameCofinalityにpartial 7.3.1.18。citation-review-candidates.jsonを参照する。原環境の宣言との一致・既存属性・番号とTagの実データを照合してから適切なcite/kerodon属性を付ける。partialを一般定理の完全証明へ読み替えない。レビュー内の旧名や移動前の所有元のリンクも同じ表で追う。

検査はB3の順：静的import・層・衝突→対象ビルド→**v3b保存比較の未説明0**（型・証明項・公理・kernel属性、元のprivate所有元込み）→引用とTagの期待値に対する欠落0／余分0→root→正式な全監査→verify。原ソースと元のolean環境を独立に保持し、移送後の環境で原環境を代用しない。移動元の名前空間だけを雑に書き換えた比較や、型だけの比較で済ませない。

ビルド・原環境のcompiler採取・native snapshotは **--class bulk --wait 3600**。昼は3〜5分（guard 280秒以下）の塊、鍵を保持するのは実際の処理中だけ。rootの大きな束・正式全監査・verifyは夜に回す。所要の紙の見込みは準備・原環境採取2〜4時間、適用・静的な再照合1〜2時間、対象ビルド／v3b 2〜5時間、root・全監査・verify 4〜8時間、目録・最終追従資料1〜2時間（鍵待ちを除く）。現時点では通過した検査として数えない。

### 0.3 他のレーンの枝への影響と条件付きの事前承認

原mainに未取り込みの各枝のコミットが触ったLeanを、その枝のHEADの内容で読み取った。加えて各worktreeの変更済み・未追跡Leanを読み取り専用で照合した。moduleの完全名、旧namespaceの完全名／部分修飾、BE側の固有module短名の**文字列一致は合計0ファイル**。draftsも文字列の影響表には含め、実際の書換対象には入れない。他のworktreeは変更していない。branch-impact.jsonにHEAD、候補数、SHAと一致を保存した。

| 枝 | 未取り込みコミットが触ったLean | HEAD・未コミットを含む一致ファイル |
|---|---:|---:|
| math/inf-supply | 216 | 0 |
| codex/bulk-5inf3a | 167 | 0 |
| math/scheme | 133 | 0 |
| math/bs-impl | 0 | 0 |
| codex/g12-monad-catalog | 0 | 0 |

原環境で宣言を採取する前なので、openを通した短名の束縛まで検証済みとはしていない。準備のcollectと新しい正式な宣言名表で影響を再計算し、新しい一致が30ファイルを超える場合は適用前に止めて報告する。現時点の§1の範囲内・文字列一致0≤30という二条件を満たすので、指示書§3の事前承認に従い、段0の報告をコミットして**承認待ちで止まらず準備へ進む**。段1の適用・検査・目録が完成した所が停止点である。

### 0.4 段2の分類表（紙のみ）

基準mainのEInfinityには3,886本。BarrattEccles（集約入口を含む）・Interface・PowerOperation・Modulesを除く分類対象は**2,621本・192,973行**。各ファイルの分類・根拠・行数・段1に含むかどうかはstage2-classification.csvに全件記録した。段1で既に動かす三束357本を除いた、段2として残る範囲は**2,264本**である。

これは**主用途による段0の分類**。純粋な有限組合せの補題がBEの計算の補助に混在する場合の宣言単位の切り出しは、段2の適用前に判断する。一般性だけでHA経路に必ず必要と数えず、strictなdg operadの一般論をHAの∞-operadそのものと同一視しない。

| 族 | 主用途の分類 | ファイル | 行 |
|---|---|---:|---:|
| AlexanderWhitney | 一般 | 28 | 2,875 |
| BergerFresse | BE固有 | 3 | 202 |
| ComplexLimits | 一般 | 382 | 21,979 |
| CosimplicialNormalization | 一般 | 9 | 591 |
| DGAlgebra | 一般 | 26 | 2,646 |
| FrameHom | 一般 | 144 | 10,729 |
| FrameRealizationLifting.lean | 一般 | 1 | 85 |
| Hammock | 一般 | 354 | 21,620 |
| HomBiprodRestriction.lean | 一般 | 1 | 79 |
| HomHomotopy.lean | 一般 | 1 | 100 |
| HomRestriction.lean | 一般 | 1 | 57 |
| HomologyZero | 一般 | 16 | 1,055 |
| HomotopyWeight | 一般 | 61 | 4,697 |
| IntervalCuts | BE固有 | 205 | 20,124 |
| NatTensor | 一般 | 5 | 518 |
| NativeBinaryCoconeHom.lean | 一般 | 1 | 44 |
| NegativeTensor | 一般 | 14 | 1,398 |
| Operad | E∞の一般論 | 327 | 27,658 |
| OppositeFactorization.lean | 一般 | 1 | 61 |
| ProjectiveCofibrantUnit.lean | 一般 | 1 | 117 |
| ProjectiveCofibration.lean | 一般 | 1 | 59 |
| ProjectiveHomotopyInverse.lean | 一般 | 1 | 99 |
| ProjectiveModel.lean | 一般 | 1 | 429 |
| Shuffle | 一般 | 45 | 4,229 |
| SimplexCuts | BE固有 | 426 | 25,665 |
| SimplicialLocalization | 一般 | 152 | 12,011 |
| StrictAdjunctionBar.lean | 一般 | 1 | 266 |
| Surjection | BE固有 | 202 | 16,661 |
| TableReduction | BE固有 | 211 | 16,919 |

集計：一般1,247本・85,744行、BE固有1,047本・79,571行、E∞の一般論327本・27,658行。Operad/は一般の対称dg operadと代数・自由忘却・模型の移送を含むため、HA経路でも残る候補として第三分類に置いた。BergerFresse・Surjection・TableReduction・IntervalCuts・SimplexCutsは、具体的なBE／全射operad作用の計算の束として第二分類に置いた。これらの中の純粋な複体・有限順序の補題は、後の宣言単位の分離で第一分類へ移る可能性がある。今回この2,264本の配置やnamespaceは変更しない。

### 0.5 目録の構成案と停止点の提出物

1. **research/einfinity-general/README.md**：一般部品489本（OE01〜OE04）の目録。基準コミット・原ソースSHA・対応表・文献の略記、役割別のファイル数／行数、各ファイルの主な構成と型の抜粋（局所variable文脈付き）、使用する入力・既知の仮定・未完部分、入口と監査・検収の出所。文献の番号は利用箇所と当該定理の完成を区別する。
2. **research/is-w2-be-route/README.md**：D81で止めた99本の目録。停止理由、R01〜R12と追加13項目の到達点（12/25）、未完のR03d/R03hと未着手のR06〜R10、BEに固定した実例・frame・同じnative射の型、一般部品への新しい参照、将来整流比較を採る場合の再利用候補と、今回は実装を再開しないことを記録。
3. **research/g12-monad-route/README.md**への相互リンク：179本の一般HA/Monadsと、その未完のwalking adjunctionの到達点を既存の目録で参照する。段1で移動・再実装しない。
4. **B4資料**：正式なmodule-map、native所有元付きの宣言名表、import所有元表、原環境collect→rewriteのコマンド、各枝への影響表と一時のプレビューの保留、static／v3b／引用／root／正式全監査／verifyの結果、取り下げ一覧。

段1の完成報告では、これらの目録を含めて実測の件数・保留・取り下げ・各検査の結果とコミットを記録して停止する。主張・証明の追加やD81で止めた経路の再開は、この整理の作業へ含めない。

一覧：済み 0／全体 5（うち追加 0）。束のIDはOE01〜OE05。段0の資料作成は済んだが、段1の検査完了とは数えない。

## 1 段1の準備：原環境と層の予覧（2026-11-16）

### 1.1 基準側の層metadataと、配置の一修正

現行の元設定では∞のper-file tierが348本未登録で、層チェッカーは初期化時点で失敗した。段0の「588本がConsumers」は、未登録ファイルを既定のConsumersとして数えた静的な仮集計であり、588本全部の登録が検収済みという意味ではない。ここを訂正して区別する。348本のうち段1の588本に含むものは124本。B3′の既存の機械規則（依存順に、実装やConsumers依存はConsumers、Comparison依存はComparison、残りはPortable）で、**一時の読取専用の補完案**を作った。内訳{'Portable': 245, 'Consumers': 67, 'Comparison': 36}。既存のtierと例外は変更していない。実際のscripts/refactor/layers.jsonはまだ書き換えていない。

補完案を使う基準グラフは33,254モジュール、既存の違反86件（reverse-section 63、tier-order 23）。baseline-layer-violations.jsonに全件保存した。基準の86件を今回の移動が解決したとも、層検査が全件PASSしたとも数えない。

最初の移送予覧ではAnodyneFamilyHomotopyを3.1の下へ置くと、元から必要だった4.6のIntervalFamilyInvarianceへの依存が新しいreverse-sectionになると分かった。そのため同じファイルを**4.6のMorphismSpaces/**へ置く案へ修正した。主張・証明・依存そのものは変えず、3.1のAnodyneWeakDetectionの配置は保持した。修正後は、同じtier／境界／理由をmodule-mapで移した予覧で、基準86件に対し予覧86件、**新規違反0・消えた違反0**。新しい例外を追加して帳尻を合わせていない。段1の範囲は同じ588本で、他の枝の文字列の影響も再集計0本。

### 1.2 原ソース・oleanの独立保持と最初のnative採取

/private/tmp/oe-w1-before-30ae8948f に基準30ae8948fのdetached worktreeを作り、元の .lake/build をAPFSのcopy-on-writeで独立に保持した。第三者のpackagesだけを共有し、projectのoleanを移送後の作業木と同じディレクトリへ向けてはいない。588ソースのSHAを段0の表と全件照合して一致。代表の元oleanはSHA一致・inode相違を確認した。frozen-before-receipt.jsonに記録。mainの作業木では編集・ビルドしていない。

原環境のcompiler採取はProjectiveWeightComparison一本で終了0、998参照と12のscope/openコマンドを保存した。--class bulk --wait 3600、280秒guardの一枚の鍵で実行し、返却済み。引用registryの読取専用checkも25 keysで一致。

さらに独立した原環境で、ProjectiveWeightComparison・AnodyneWeakDetection・AnodyneFamilyHomotopy・ModelRightFrameComparison・StrictDiagramTotJointSourceRawCoslicePathの五本のnative inventoryを採取した。元のv3b検証専用binaryとreceiptのSHAが一致し、共有のdecl_snapshot.leanのSHAも一致。5モジュール・**31宣言**、huge_terms 0、終了0、実処理84.96秒。--class bulk --wait 3600、280秒guardで実行し、鍵は返却済み。**これは原環境のinventoryの検証であり、最終の名前正規化を用いた移送前後のv3b比較は未実行**。

証跡はorganize-einfinity-w1/preparation/の各receipt、層予覧のsummary、原inventoryとcompiler参照のgzip。生の記録・ログは/private/tmp/oe-w1-captures/。表の再集計スクリプトは一時ファイルへの依存をなくし、source_names.pyを添えた。ソース上の宣言候補をnative所有元と混同しない。

### 1.3 次の順序と現在の未完

残る原環境のnative所有元・private名・生成宣言の採取、書換対象の原参照の採取、正式な所有元付き改名表、全プレビューの保留の解消へ進む。保留のある書換えを適用しない。基準側の86件は今回の移動の追加差分と区別し、最終の層検査でも記録を落とさない。移動そのものの適用・移送後の対象ビルド・v3b未説明0・引用／Tag・root・正式全監査・verify・目録の検収は、まだ済んでいない。Leanの主張・証明は未変更。

一覧：済み 0／全体 5（うち追加 0）。

## 2 原環境の全所有元表・参照採取と目録の準備（2026-11-16 午後）

### 2.1 全588本の原環境と正式な改名候補

独立した原環境で、対象588本すべての `lake build` が終了0。最初に不足していた68本も同じ原環境でビルドした。主張・証明は変更していない。native所有元だけを採取する検証専用ツール `oe_native_owners.lean` を作り、既存v3bの五本・31宣言と `(module, kernel_name, name, is_private)` が完全一致することを確認した。このツールは保存比較の型・本体・公理のfingerprintを置き換えない。

全588本のnative所有元は **4,160宣言、private 157（public 4,003）**。privateの `(module, user name)` の衝突0。名前つき宣言を持たないモジュールはTensorConeUnitPointのみ。正式な所有元付きの改名候補はpublic 3,280名、private user name 75名を変更する。`namespace-rewrite-map.json` は既存 `Migration` の検証を通り、候補先名の衝突0、openの候補の曖昧さ0。これは移送後の実名を観測済みという意味ではない。

原native inventory・receipt・検証専用ソースのSHAと、所有元ごとの移送先候補をpreparation/に保存した。通常privateはraw kernel名と所有元を保持し、最終v3bでは移送後の実名から所有元つきの正規化を照合する。ソースの行番号だけで生成宣言を対応させない。

### 2.2 compiler参照の範囲と最初のプレビュー

原環境のnative `.ilean` の正確な所有モジュール／kernel参照と、module名・namespace・BEの一意な名前の文字列候補を併用した結果、候補は956本と正式監査2本。正式監査2本のcompiler採取は監査全体を実行するため、**夜へ回す**。BS本体の利用側の編集候補は0本。

956本のうち、OE01の132本はnamespace・moduleを保持し、native参照／importと文字列候補にも該当しない。全132本の原SHAを固定し、ソースのbyteを変更しない。採取したことにするJSONは作らず、対象ビルド・v3b・引用・正式監査の範囲からも除かない。残る824本を実際のcompilerで採取している。最初の13本は原ソースのSHAとcollector SHAを照合し、書換プレビュー **13本、保留0**。全体の保留0や適用完了を意味しない。

昼の鍵は `--class bulk --wait 3600`、280秒guardで返す。最初の原参照採取は順次実行。次の塊からはB3と同じ条件（利用可能メモリ20GiB以上なら独立した読取専用frontendを最大2つ、それ未満は1つ、LEAN_NUM_THREADS=1）で採取する準備をした。lake buildを並行には流さない。元ソースの成功receiptだけを採用し、timeout・失敗・保留を隠さない。

### 2.3 目録の下準備と残る検査

一般部品489本・36,258原行と、D81停止BE99本・7,375原行の二つの目録を準備した。各ファイルのmodule docstringとnative所有元表に実在する公開宣言の型を原ソースから抜き出し、universe・variable文脈を併記した。目録には現在が準備中であること、移送後の型と全検査をまだ検収していないことを明記した。BEの12/25と未完・未着手を記し、HA Monads179本は既存目録へ案内した。適用後に実際の新しいソースから再生成し、検証出所を更新する。

今回、数学のLeanファイルの移動・書換えは未適用。原参照の全採取と保留解消、実適用、層の基準差分、移送後の対象ビルド、v3b未説明0、引用／Tag欠落・余分0、夜のroot・正式全監査・verifyが残る。共有鍵では現在mainの登録ビルドと他のレーンの小検査を待っている。条件付きの事前承認に従い、待ちの間も目録・照合の準備を続ける。

一覧：済み 0／全体 5（うち追加 0）。

### 2.4 引用表のnative名による全再走査

ソース上の名前候補だけでなく、nativeの公開宣言名を用いてKerodon・HA・HTTのown／both／partial表を走査した。該当は**11行（Kerodon 6・HA 5）、宣言ごとの文献対応14件**。HAのpartial対応8件とKerodonのown対応4件は、既に実ソースに属性が付いていることを確認したため保持する。Kerodonのpartial 2件のみ、通常圏の随伴／具体的モデル圏とフレームという範囲を明記したcomment付きのnative tagを足す準備とした。`preparation/citation-review-all-native.json`に全対応と元の根拠を保存。属性の重複を足さず、HAのpartialを一般定理のexactな完成に読み替えない。まだ属性の追加そのものは適用していない。

利用側も含む保存比較の範囲はcore候補956本とし、132本のbyte不変ファイルも比較する。956本中、原環境で自身のoleanが不足する38本を確認した。原参照の採取とは別に、この38本も最終v3bの前に原環境で温める。移動対象588本だけの比較で利用側の変更の検証を省かない。

一覧：済み 0／全体 5（うち追加 0）。

### 2.5 監査範囲を落とさないmetadataの予覧

EInfinity監査の元の接頭辞判定を残すだけでは、一般部品357本が移動した後にその公理監査の対象から外れる。そこで新しい三つの束の接頭辞と、Kerodonへ分ける二つのmoduleの完全名を追加する案を作り、元の全ソースのmodule集合に対して照合した。**元の3,887モジュール（directoryの3,886本と集約入口）と、同じmodule-mapで運んだ3,887モジュールが一致、過不足0**。EInfinity監査という既存の名前でも、今回の移動によって元の対象を落とさない。

原監査のコピーだけを使うmetadata予覧では、compilerのterm参照と別に保管されるquoted Nameの必要名表がEInfinity側1,334箇所、BS側1箇所の移送候補になった。この数は元コピーに対する予覧であり、最終compilerプレビューとの重複は適用時に除く。原監査そのものの実行ではない。最終の二監査の原参照採取・新環境での実行は夜に行う。元の全必要名の配列と型付きのfixtureは保持し、計算上限も変更しない。

前後の実際のnative所有元が揃った後にだけ、所有元付きprivate規則と比較名表を出すprepare_preservation.pyも準備した。未対応・余分・private名の衝突があれば表の完成扱いにせず止め、既存のv3b snapshot・comparatorの本体は変更しない。

一覧：済み 0／全体 5（うち追加 0）。

### 2.6 SimplicialLocalizationの文献配置の訂正

文献表の全native再走査で、模型圏の局所化の対応は**HA §1.3.4**であることを確認した。当初の「HTT §1.3.4」は誤記なので訂正する。OE04の152本の置き場所も、新しいHTTの束を立てる案から、既存の **InfinityCategories/HA/ModelCategoryComparison/SimplicialLocalization/** の下へ変更した。一般の模型圏・相対圏の部品である点、主張・証明、対象588本と他のレーンの旧参照の範囲は同じ。原参照のソース・collector SHAも変わらない。

正式な改名候補、層の予覧、採取済みプレビュー、二つの目録案をこの配置で更新する。まだ数学のソースの移動は適用していない。

一覧：済み 0／全体 5（うち追加 0）。

HA配置へ訂正した後の再検査：正式なMigrationの検証終了0。新しい表による採取済み13本のプレビューは保留0。層の予覧も基準86件・予覧86件、新規0・消失0。他の五つのレーンの最新HEADと未コミット／untracked Leanを読取専用で再確認し、bare namespaceも含む文字列一致は0本。branch-impact.jsonを更新した。共有鍵の一回の待ちは3600秒で終了75となったため、重複する整理券を残さず新しい一枚で並び直す。参照採取の中身の失敗ではなく、新しいcompiler採取はこの待ちでは実行していない。

目録の抜粋はnativeの `(module, public name)` に一致する宣言に限るよう整えた。移送後の再生成には、実際の移送後native所有元表を必須にし、候補の名前だけから存在を推測しない。適用手順も、全compilerプレビューと夜の二監査の実採取・保留0・元ソース全SHA一致・metadata overlayの前後SHAが揃うまでは書き込めないdry-run既定の形で準備した。まだその適用は実行していない。

一覧：済み 0／全体 5（うち追加 0）。

## 3 compiler生成宣言の親名の照合（2026-11-16 午後）

元のnative表の公開等式・合同補題のうち、元の `.ilean.decls` に直接のソース宣言を持たない179件を別に調べた。ファイルのnamespaceだけを使う案では、次の2件が改名漏れになる。

| 元の生成補題 | 実際の親 | 親に従った先のnamespace | 元の観測された生成元 |
|---|---|---|---|
| FrameHom.frameLeftRoofNerveMap.congr_simp | FrameHom.frameLeftRoofNerveMap | HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom | SimplicialLocalization.ModelBifibrantSourceFrameGraph |
| SimplicialLocalization.modelSourceFrameFamily.congr_simp | SimplicialLocalization.modelSourceFrameFamily | InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization | BarrattEccles.StrictDiagramTotFrameHomInfinity |

この2件は明示したソースの宣言を新しく足す操作ではない。既存の実在する親を改名するとき、その親からcompilerが生成する合同補題の完全名も同じように運ぶ。179件の元kernel名・観測した所有元・ソース宣言の有無・親の名と対応を `preparation/compiler-child-parent-review.json` に保存した。親が移らないMathlib・Kerodon・Hammockの子は同じ完全名に保つ。生成補題の移送後の実際のproviderはまだ観測していないので、source-owned APIのimport元と混同しない。

正式な候補表の変更名はこれにより **public 3,282（当初3,280に生成補題2件を追加）、private user name 75**。全nativeは同じ4,160件で、移動するファイル数や数学の主張・証明は変わらない。Migration検証終了0、採取済み13本のプレビューは保留0。原環境の参照の採取は同じsource／helper SHAのまま続けられる。前後の全nativeを組み合わせる準備手順も、生成補題の名前はfile namespaceだけで推測せず、正式な親の対応を使うよう整えた。

一覧：済み 0／全体 5（うち追加 0）。

## 4 mainのCitation略号表の更新との分離（2026-11-16 16:25の調整役の連絡）

main cd79e9cc5でDAG XIII・NSの対応表とCitationの略号表が更新され、ほぼ全体の再コンパイルになるため、昼のmain rootは16:23に中断、23時以降に再開するとの連絡を受けた。**この停止点まではmainを取り込まない**。OE-W1の基準は引き続き30ae8948fで、現在の枝・独立した原環境のCitationと略号表を固定して比較する。新しいmainのroot未確認と、この枝で行う検査結果を混同しない。停止点後にmainを取り込む場合も、夜のroot完了後にする。

読取専用で、main・作業枝・原環境のproject `.lake/build/lib/lean` がそれぞれ別のディレクトリであることを再確認した。原環境が共有するのは第三者packagesであり、mainの途中のproject oleanを原環境の保存比較へ流用しない。共有鍵の原環境参照の待ちは、一度3600秒の終了75の後、一枚の新しい整理券で継続している。

一覧：済み 0／全体 5（うち追加 0）。

### 4.1 鍵の取得後の最初の参照採取（16:34）

原環境のcompiler参照は **33／824本**（byte不変の132本は別、正式監査2本は夜）。この塊の新規20本は2 reader、217.67秒で終了0となり鍵を返却した。source／collector SHAは固定のまま。33本の書換プレビューは、生成補題2件の親名の補正を含む正式表（SHA bffb2434…）で**保留0**。次の一枚の整理券で採取を継続している。

`preparation/reference-progress-20261116-1634.json`に成功数とこの塊の時間、プレビュー結果を保存。これは数学のソースの実適用や移送後の保存比較の完了ではない。全体のcompiler参照と保留解消が揃うまでは適用しない。

一覧：済み 0／全体 5（うち追加 0）。

### 4.2 比較全域の原環境と実引用の採取（17:13）

`lake --no-build build`による原環境956本の準備確認は75.57秒で終了0、22,525 jobsが全てup-to-date。欠けていたown oleanは0本になった。原環境の同じ956本を一度にimportして、**9,649 native宣言・private 224、同じ所有元内のcanonical名の衝突0**を採取した。実際の引用metadataも終了0、対象内**61件（HTT 42・HA 15・Kerodon 4）**。二つの独立した読取専用readerは126.09秒で終了し、鍵を返却した。

文献表の14対応を実metadataと全件照合し、既存12件は各1件、追加予定のKerodon 02P3・039Nは各0件で一致した。追加を含む最終の期待値は既存61件の輸送と新規2件で63件となる。実metadataのgz、receipt、14対応の照合をpreparation/に保存した。

588本だけをimportしたときと956本をimportしたときでは、公開compiler生成補題5件のprovider差を観測し、別の2件は956本の選択領域には現れなかった（選択領域外の実providerは未照会）。588本の所有元に属する行は4,160から4,155になった。全て生成された等式・合同補題であり、明示したAPI宣言の移動ではない。元の両contextを `compiler-provider-before-contexts.json` に保存した。最終比較は全域956本の原nativeを正本とし、移送後の実providerを改めて照合する。これらをsource-owned APIの確定したimport元と扱わない。

原参照は66／824本、66本のプレビュー保留0。対象集合とsource／helper署名は変えず、移動する456本を先に採取する順へ整えた。昼280秒、夜は取得時刻で最大1,680秒、各ファイルの上限190秒は変更しない。夜の長い待ちの塊へ切り替えるため、成功した塊の返却後に一度だけcontrollerを区切った（終了76、数学の検査失敗ではない）。重複整理券なしで再開済み。

一覧：済み 0／全体 5（うち追加 0）。

## 5 匿名local instanceの綴りの個別確認（17:49）

137本目のプレビューで、StrictDiagramTotModelSource.lean:25の `local instance : ModelCategory (operad A).Algebra := modelCategory A` のbinderが保留になった。原compilerはkeyword `instance` のspanを、実在する `SerrePositivity.EInfinity.BarrattEccles.instModelCategoryAlgebraOperad` に解決している。原native表でも同じ所有元・同じ公開名を確認した。

この一件のみ、輸送後の `…BarrattEccles.StoppedRoutes.ISW2Tot.instModelCategoryAlgebraOperad` を明示する。型・値・localな属性と位置は変えない。既存の匿名宣言の名前を明示する操作で、新しいinstanceやモデル構造を加える操作ではない。元のsource SHA、元の正確な一行、compiler binderのbyte spanと名前、実在native名と移送後の候補を `reviewed-anonymous-instances.json` に個別記録した。

共有書換器のguardは変更せず、個別記録と全条件が一致するbinderに限って、keywordを `instance _root_.<同じ宣言の新名>` にする準備用adapterを使う。他のbinderや他の曖昧な構文は元のguardで保留する。全137本のプレビューは保留0になった。匿名の綴りと明示名のkernel上の一致は、実適用後の対象ビルド・v3bで検収する。

一覧：済み 0／全体 5（うち追加 0）。

### 5.1 同じ個別確認の追加（17:58）

152本目でStrictDiagramTotRightFrameComparison.lean:25–26の匿名local instance二件が同じguardに当たった。元native名は `…instModelCategoryAlgebraOperad_1` と `…instHasFunctorialFactorizationAlgebraOperadCofibrationsTrivialFibrations`。前者は既存のBEモデル構造、後者は既存のcofibration／trivial fibrationの関手的分解を指定している。同じ根拠・source SHA・正確なbinder span・原native表で個別確認し、輸送後の名前のみを明示する記録を追加した（計3件）。型・値・localな属性を変更しない。152本のプレビューは保留0。

一覧：済み 0／全体 5（うち追加 0）。

### 5.2 18:08の参照採取と停止経路の全予覧

原参照198／824本、198本のプレビュー保留0。内訳ではOE05（D81で止めたBEの99本）は**99／99本を原compilerで採取し、全プレビューが保留0**になった。OE03は35／144本、OE04は先行sampleの1本、OE02は未採取。原ソースを静的に走査した匿名local instanceの候補は計4件で、個別確認済み3件のほかにHomotopyWeight/KanDiagramBrown.lean:32が一件ある。これは実compiler binderの採取後に個別確認する。

この数は参照とプレビューの進捗であり、OE05の実適用・対象ビルド・v3b・Tag・root・全監査・verifyが済んだという意味ではない。数学のソースの移動はまだ適用していない。

一覧：済み 0／全体 5（うち追加 0）。

## 6 相対修飾された宣言binderの個別確認（18:19）

255本目でHomInfinityLocalizationTransport.leanの `def CoherentLocalizationComparison.homInfinityTransport` が保留になった。原compilerのbinderは実在する `…EInfinity.FrameHom.CoherentLocalizationComparison.homInfinityTransport` に解決しているが、記録されたnamespaceは既にCoherentLocalizationComparisonまで延びており、共有書換器の相対名の判定と合わない。さらに同じspanに名前もmoduleも空のlocalマーカーが一つ重なっていた。

`reviewed-qualified-binders.json`にsource SHA・正確な綴り・byte span・原native名・移送後の名を個別記録し、同じ宣言の新しい完全名のみを明示した。adapterはspanの直前が実際のdef等の宣言keywordであり、同じspanの記録がこのbinderと名前のないlocalマーカーだけであることも確認する。この個別条件以外の局所変数の解決や共有guardは変更しない。型・引数・値は変更しない。

255本のプレビューは保留0。実適用と対象ビルド・v3bでの検収は未実行。

一覧：済み 0／全体 5（うち追加 0）。

### 6.1 残る匿名local instanceの確認（18:43）

340本目で、静的な候補の最後の一件KanDiagramBrown.lean:32のbinderが保留になった。実名 `…HomotopyWeight.instIsStableUnderBaseChangeSSetFibrations_serrePositivity` を原compilerと原native表で確認し、既存のlocalなbase change安定性のinstanceの新名のみを明示する記録を追加した。元のscoped SSet模型、型、値、localな属性と計算上限は変更しない。モデル構造や仮定を新しく加えていない。個別記録は匿名instance計4件、相対修飾binder1件。

340本のプレビュー保留0を確認して採取を続ける。

一覧：済み 0／全体 5（うち追加 0）。

## 7 原参照の半分を超えた所（18:56）

原参照438／824本、全438本のプレビュー保留0。半分を超えている。個別の確認は既存の匿名local instance4件と相対修飾binder1件の計5件で、いずれも名前の明示だけ。型・値・計算上限の変更や、新しい数学的構成の追加はない。移動対象と利用側の全域、byte不変132本、夜の正式監査2本の範囲も変更していない。group別の採取件数を `reference-preview-halfway.json` に保存した。

残る原参照386本の採取と保留の解消を続け、二監査の原参照は夜に採取する。その後に全体の実適用・対象ビルド・v3b・実引用／Tag・root・正式全監査・verify・移送後の実native名に基づく目録の更新を行う。実適用はまだ行っていないため、段1の検収済みの束とは数えない。

一覧：済み 0／全体 5（うち追加 0）。

### 7.1 正式監査の全件一覧（19:01）

`audit_*.lean` と `scripts/audit/**/*.lean` を実ファイルから列挙し、audit_manifest.txtと完全一致を確認した。**106正式監査、元ソースから抽出した必要import先7,259モジュール**。`all-audit-inventory-before.json`に全件保存した。選択除外はしていない。これは実行結果ではなく、移送後に必要import先を再計算してから夜に全件を実行する。現時点の原参照／プレビューは460本、保留0。

一覧：済み 0／全体 5（うち追加 0）。

## 8 移動456本の全原参照と全予覧（19:12）

移動する456本すべての実compiler参照が揃い、全プレビューが保留0になった。内訳：OE02 HomotopyWeight 61／61、OE03 FrameHom 144／144（Kerodonへ分ける二本を含む）、OE04 SimplicialLocalization 152／152、OE05 D81停止BE経路99／99。`preparation/all-moving-previews.json`にsource／preview SHAと全件を保存した。

原参照全体は521／824本。残る利用側303本の参照と、夜の二つの原監査の採取を続ける。byte不変132本の範囲も保持する。移動456本の予覧が揃ったことは、実適用・移送後ビルド・v3b・Tag・root・106正式監査・verifyの完成ではないため、検収済みの束にはまだ数えない。

一覧：済み 0／全体 5（うち追加 0）。

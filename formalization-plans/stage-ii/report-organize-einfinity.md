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
| OE04 | EInfinity/SimplicialLocalization/ 全体 | 152本・12,011行 | InfinityCategories/HTT/ModelCategoryLocalization/SimplicialLocalization/。HTT 1.3.4とDwyer–Kanの単体的局所化・模型圏の比較 |
| OE05 | 3b-4のBE固有のTot比較 | 99本・7,375行 | EInfinity/BarrattEccles/StoppedRoutes/ISW2Tot/。停止済みの経路であることをmodule docstringに一行追加 |

OE03の例外：AnodyneWeakDetection.lean、AnodyneFamilyHomotopy.leanは模型圏を仮定しないKan標的／anodyneの一般論なので、**InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/**へ置く。任意の模型圏のframeを使うものと分ける。HTT配置のOE04もportableな∞中核への格上げを意味しない。

名前空間は新しい数学の配置に合わせる。OE02はSerrePositivity.EInfinity.HomotopyWeight→SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight、OE03の142本はEInfinity.FrameHom→HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom、OE04はEInfinity.SimplicialLocalization→InfinityCategories.HTT.ModelCategoryLocalization.SimplicialLocalization。上のAnodyne二本はファイル別の表を優先する。

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

# 整理 IC-W1：∞ 圏のコードを InfinityCategories に集め、内容ごとにディレクトリを分ける

作成：2026-11-16 夜（調整役）。決定：ユーザー（11-16「内容に合わせてディレクトリ分けをしたいのと、無限圏は InfinityCategories に移したい」「模型は a で」「3b のチャットは不調なので別のチャットで」）。担当：IC-0 は ③-b が今の OE-W1 の段 1 として続ける。IC-1 以降は、IC-0 の取り込みの後に新しいチャット（レーン ⑦）が持つ（ユーザー 11-16「OE-W1 はそのまま続けさせて、そのあとで新しいチャットで」）。

## 0. 目的

1. ∞ 圏の一般論を `InfinityCategories/` に集め、Kerodon・HTT・HA の節に置く（`kerodon-layout` の規則、`InfinityCategories/<Kerodon|HTT|HA>/...`）。
2. それ以外も内容ごとに分ける：一般のホモトピー論・モデル圏は `HomotopicalAlgebra/` の主題ごと、K 理論に固有のものは `KST/` の中で K の文献ごと。
3. **模型は `InfinityCategories/Models/`**（ユーザー決定、案 a）：KST の Sp（BF の Ω スペクトル）は `Models/Spectra/OmegaSpectra/`、Spectra/ の対称スペクトルは `Models/Spectra/Symmetric/`、厳密な dg 圏の模型は `Models/DGCategories/`、BE の模型は `Models/EInfinity/BarrattEccles/`（名前は段 0 で決める）。docstring に「模型。文献の定義との比較は後で」（`p0-plan-draft.md` §6）と一行。
4. 主張・証明は変えない（移動・改名・docstring・import だけ）。

## 1. 範囲と順序

| 束 | 中身 | 資料 |
| --- | --- | --- |
| IC-0 | **OE-W1 の段 1**（③-b が続ける。`refactor/organize-einfinity`、作業木 `SerrePositivity-bs-d68`。456 本の移動、目録） | `organize-einfinity-general.md`、`report-organize-einfinity.md` |
| IC-1 | EInfinity の残り（OE-W1 の段 2：一般 1,247 本、BE 固有 1,047 本 → Models、E∞ の一般論 327 本） | OE-W1 の `stage2-classification.csv` |
| IC-2 | KST・HomotopicalAlgebra・Spectra の一般の ∞ 圏論 1,725 本 | `research/infinity-outside-map/files.csv`（738be1c06） |
| IC-3 | 同じく模型 3,776 本 → `InfinityCategories/Models/` | 同上 |
| IC-4 | 同じく一般のホモトピー論・モデル圏 2,415 本 → `HomotopicalAlgebra/` の主題ごと、K 固有 912 本 → `KTheory/<文献>/`（§4）、今の `KTheory/` の 35 本も `KTheory/` の中の節へ。`KST/` は論文の層だけ | 同上 |
| IC-5 | **HomologicalAlgebra/ の主題ごとの配置**（510 本、うち 365 本が最上位に平たく並ぶ。名前空間は `SerrePositivity`・`SerrePositivity.DerivedCompletion`・`SerrePositivity.HomologicalAlgebra`・`SerrePositivity.BhattScholze` などが混在）。IC-W1 の分類表には入っていないので、段 0 で主題ごとの下位ディレクトリ（例：複体・分解・Koszul・導来完備化・局所コホモロジー・Čech・余単体など）と名前空間の方針を決める | 新しく作る（`research/infinity-outside-map` と同じ形で `HomologicalAlgebra/` の分類表） |
| 後回し | 未定 1,243 本（一般の補題と K の構成が一つのファイルに混ざるもの）。ファイルを分けてから分類し直す。IC-W1 では動かさない | 同上 |

IC-0 の完成（OE-W1 の段 1 の停止点）で ③-b は止まる。取り込みの後、⑦ が IC-1 の段 0 から始める。

## 2. 規則（B3・OE-W1 と同じ）

- 検査：静的な import・層・衝突 → 対象ビルド → 保存比較（v3b、未説明 0）→ 引用・タグの再照合（欠落・余分 0）→ root → 正式な全監査 → verify。直せない移動は取り下げて元の場所に残し、記録して進む。
- 置き場所は対応表（`research/kerodon-coverage`・`htt-coverage`・`ha-coverage`）の番号に合わせる。番号が付かない補助は、それを使う項目の節へ。
- 文献の属性（`@[cite …]`・`@[kerodon …]`）は対応表で own・partial に当たるものに付ける（Kerodon の partial は付けない）。docstring の出典の番号は概要か方針の側に。**略号表（`Util/Citation.lean`）は変えない**（変えると全体の再ビルド、BR54）。
- 他のレーン：③-a（`InfinityCategories/Sheaves/`、枝のみ）、⑥（`AlgebraicGeometry/`、KST を import しているか段 0 で確かめる）、一括（`BhattScholze/Prismatic/HodgeTate/`）、`blueprint/kerodon`（枝 `docs/kerodon-blueprint`）。動かす宣言を他の枝が使っていれば影響の一覧と改名表に入れる（B4 の資料）。
- ビルドは共有の鍵 `--class bulk`。昼は 3〜5 分の塊、適用と全体の再ビルド・全監査・verify は夜。
- 凍結は短く：適用の直前に調整役に一行で知らせ、調整役はその間、動かす範囲に触る取り込みを止める。

## 3. 止め方

- 各束の段 0（紙）：移動・改名の表、層の検査の見込み、他のレーンへの影響、所要時間。**条件付きの事前承認**：束が §1 の範囲に収まり、他のレーンの枝への影響が 30 ファイル以下なら、報告して止まらずに準備・適用へ。超えるか範囲の外が要るときは止まって報告。
- 各束の完成が停止点。完了の報告（結果の表、取り下げ、B4 の資料）をコミットし、調整役が取り込む。取り込みの後、次の束の段 0 へ止まらずに進む。
- 報告は `report-infinity-consolidation.md`（新設）に。区切りごとに「一覧：済み n／全体 m（うち追加 k）」（束と、その中の移動の単位を ID に）。

## 4. K 理論の置き場所（11-17、ユーザー承認）

ユーザーの意見（「K 理論の基礎は KST/ とは別のディレクトリにした方がよいかもしれない」）を受けた案を承認（11-17「okです」）。IC-4 はこの配置で：
- **K の基礎は最上位の `KTheory/` に、文献ごとの節で置く**（`InfinityCategories/<Kerodon|HTT|HA>/` と同じ考え方）：`KTheory/Waldhausen/`・`BGT/`・`Schlichting/`・`Barwick/`・`ThomasonTrobaugh/`・`LandTamme/`・`Tamme/` など。節の名前と番号は K の文献ごとの対応表（`research/k-coverage/maps/`：bgt・land-tamme・tamme・kst・others）に合わせる。IC-W1 の分類で K 固有の 912 本（S 構成 552、Fibration 227、NonConnective 80、LocalizingInvariants 50 など）はここへ。
- **`KST/` は Kerz–Strunk–Tamme の論文の層だけ**にする（導来ブローアップ、降下、pro 切除、§5。`BhattScholze/` と同じ「論文の層」）。分類で「未定」の多く（DerivedGeometry 296、DerivedBlowup 197、Descent 169、ProExcision 150）は KST の論文に固有なので、`KST/` に残すのが自然。
- **今の `KTheory/`（35 本：G₀・K₀ の局所化、係数、Adams 作用、比較）との名前の衝突**：別名（`AlgebraicKTheory/`）を作ると K の置き場所が二つになって紛らわしいので、**`KTheory/` に一本化**し、今の 35 本は内容の文献に合わせて `KTheory/` の中の節（例：G₀・K₀ の基礎は `KTheory/Classical/`、Adams 作用は対応する文献の節）へ移す案。今の 35 本を import しているのは論文の層（`IntersectionMultiplicity/`・`PerfectComplex/` など）で、import の書き換えだけで済む。
- 実施は IC-4。K の再開（`k-restart-draft.md`）の前の整理として、移動だけで主張・証明は変えない。

## 5. 名前空間と下位ディレクトリの方針（IC-4・IC-5 の段 0 で最初に決める、11-17）

- **`HomotopicalAlgebra/`** は IC-4 で 2,415 本を受け入れて 3,500 本を超える。IC-4 の段 0 で、移す前に**下位ディレクトリの設計**（今の主題 Simplicial・Diagram・HomotopyFunctionComplex・Reedy・Rectification・Quillen・Smith・Localization などを基に、受け入れる分をどこに置くか）を決める。
- **名前空間**：`SerrePositivity.HomotopicalAlgebra` は使わない（Mathlib の `HomotopicalAlgebra` 名前空間を `SerrePositivity` の中で隠す）。今の主題ごとの名前空間（`SerrePositivity.SimplicialModel`・`SerrePositivity.HomotopyFunctionComplex`・`SerrePositivity.DiagramModel` など）に揃える案を基本に、段 0 で表にする。`HomologicalAlgebra/` の名前空間（IC-5）も同じ考え方で、Mathlib の名前空間と衝突・隠蔽しない形に揃える。
- 名前空間を変える宣言は改名表に入れ、他のレーンの枝の追従（B4 の資料）を作る。

## 6. 未決：DifferentialGraded/・Checks/・スペクトルの模型（IC-1 の段 0 の前に決める、11-17）

DifferentialGraded/（473 本。本体 164 本・約 13.6 万行、Checks/ 309 本）は分類表（`research/infinity-outside-map/files.csv`）に入っていない。InfinityCategories の 464 本と KST の 367 本が import している。調整役の案：
- **(a) に決定（11-17、ユーザー）**：dg 理論そのもの（dg 圏・dg 加群・Morita・Verdier・perfect・分解など。Keller・Toën・Drinfeld などの dg の文献の主題）は `DifferentialGraded/` に残す。∞ との接点だけを外へ出す：dg nerve とその性質は Kerodon 2.5 の項目なので `InfinityCategories/Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/`、∞ の対象を dg で作る模型（D(A) の dg の模型、半自由な模型など）は `InfinityCategories/Models/DGCategories/`。どれをどちらに出すかは、IC-1 の段 0 で DifferentialGraded/ の分類表（同じ形）を作って決める。
- (b) 全部を移すと IC-W1 で最大級の移動になり、dg の文献の主題と ∞ の模型が混ざる。
- **Checks/ は IC-W1 では動かさない（11-17、ユーザー）**：`DifferentialGraded/Checks/`（309 本、example 1,280 個の受け入れの例、root からは import されず `scripts/audit/dg.lean` が全部を import）は今の場所のまま、IC-W1 の移動の確かめ（インスタンスの解決・open の範囲）に DG の監査で回す。IC-W1 の後に、公開する主な構成の受け入れの例だけ残し、残りは `Archive/` に移すか消す（U12e の前例）。`Asymptotic/DGVerdier/ChecksU17Integration.lean` が Checks の Verdier 5 本を import している点もそのときに扱う。
- **スペクトルの模型の二系統**は目録に関係を書く：`Spectra/` の対称スペクトル（1 圏の smash 積、`StableModelPresentation` は `[ModelCategory SSet]` を仮定）と、`KST/Spectra/` の Ω スペクトル（BF、coherent nerve の `Sp`、安定性は条件つき）。どちらも HA の Sp の模型で、互いの比較・HA の定義との比較は今ない。置き場所は `InfinityCategories/Models/Spectra/Symmetric/`・`Models/Spectra/OmegaSpectra/`（§0）。

## 7. IC-1 の段 0 に含める：弱い存在命題からの choose の洗い出し（BR55、ユーザー決定 11-17 案 A）

IC-1 の段 0（紙）で、InfinityCategories の全ファイルを内容ごとに並べるのと同じ回に、**弱い存在命題から `Classical.choose` でデータを選んで作った定義**を全部列挙する（概数 23〜28 個。例：`exists_colimitCoconeFamily`・`exists_quasicategory_localization`・`trivialKanFibration_exists_section`・`exists_chosenColimitSection`・`presheafElementsYonedaDiagram_exists_colimitCone`・dg gluing の零対象・正規化の存在から選んだもの）。表の列：宣言名・ファイル・選ぶ存在命題・利用側が後で要る指定構成との両立（要る／要らない／不明。利用側を読んで判定）・直し方（同じ名前・型・仮定で、指定構成に沿う選び方に替える）・推移的な importer の数・他のレーンの枝が触るか。③-a が 5∞-1 のために出した列挙（候補 255 本、`research/infinity-refactor-audit/inf-supply-choose-1117.md`・`.json`、取り込み後）を写し、そこに入らない範囲だけを新しく調べる。
「要る」と判定したものは IC-W1 の移動と同じ再ビルドの夜にまとめて直す（事前承認の型は `inf-supply-w1.md` 11-17 朝の追記と同じ）。「要らない」はそのまま残す。

## 8. IC-W1 に入れる費用の対策（`stage-ii/build-cost-plan.md`、ユーザー承認 11-17）

- **A3**：∞ の監査（レーン時代の `scripts/audit_infinity_*.lean` など）を、移動と同じ回に**領域ごとの監査**（Kerodon の章・HA・Models）に統合する。形は `scripts/make_area_audits.py`：領域の全モジュールを一度 import し、宣言ごとに公理・sorry・native_decide を一回ずつ（訪問済みを共有）。各レーンの `#check` の目印は「宣言名の存在の一覧」（生成物）に、禁止 import の規則は `scripts/refactor/audit_imports.py`＋`layers.json` に移す。**A4**：`env.constants` 全体を舐めず、モジュールの定数表を使う。
- **B1**：同じ章の小さい葉（中央値 70 行）を章のファイルにまとめる案を段 0 で出す（R8 の重複 275 群も同時に）。elaboration の drift に注意し、保存比較 v3b を通す。統合の単位と上限は段 0 で決めてから。
- **B4**：root の外にある監査用の 2,794 本と未使用の 60 本（BR8）を、root の閉包に揃えるか消す。

## 9. IC-1 の段 0 の承認（2026-11-17、ユーザー）

段 0 の紙（`report-infinity-consolidation.md`、be21fdc73：2,264 本・26 単位、import の追従 311 本、他の枝への影響 0、層の違反 172 のまま）を受けて。
1. **IC-1 の適用を承認**。条件：今夜の root の後に正式な宣言の採取（native 所有元・private・生成宣言・open 経由）と他の枝への影響の取り直しをし、影響が 30 ファイル以下なら §3 の事前承認でそのまま夜に適用してよい（超えたら止まって報告）。§2 の検査の順（静的 → 対象ビルド → v3b 未説明 0 → 引用・タグ → root → 全監査 → verify）。直せない移動は取り下げて報告。夜の暦は調整役が ③-a・⑥ の取り込みと重ならないように組む（適用の前に調整役に一行）。
2. **BR55 の「不明」356 件は使う段で直す**：全部を今読まない。表は `research/infinity-consolidation-w1/choose-additional*.{md,json}` のまま、台帳 BR55 から参照し、状態の列で管理する。あるレーンが指定構成との両立を要したら、`inf-supply-w1.md` 11-17 朝の事前承認の型で置き換える。文書の生成レーンの宣言索引ができたら、文献の項目の証明から届く候補を優先する並びにする。
3. **B1・B4 は IC-1 の移動の後、別の amendment で、試しの大きさから**：B1 は最初 4 本・400 行（上限 12 本・800 行、初回の夜は 10 群・80 本まで）、B4 は 1 節・50 本。保存比較で崩れた群は丸ごと取り下げる。

## 10. Archive は書き換えない（2026-11-17、BR56）

IC-W1 の移動・改名の追従は `SerrePositivity/Archive/` を対象にしない（ビルドしない場所を書き換え続けない）。Archive から戻すときに、改名表に沿って直す。Archive の import は移動表の「対象外の直接 importer」に数えない。


## 11. IC-1 の適用は昼から（2026-11-17 夕、ユーザー決定）

§9 の「夜に適用」を改める。宣言の採取と他の枝への影響の取り直しが済み、影響が 30 ファイル以下なら、昼から適用してよい（始める前に調整役に一行）。鍵は `--class bulk` のまま、昼は一回 3〜5 分の塊、夜は 30 分まで。検査は §2 の順（静的 → 対象ビルド → v3b 未説明 0 → 引用・タグ → root）。正式な全監査は調整役が取り込みで行うので、root が通ったら完了の報告をコミットして止まる。30 ファイル超・直せない移動が出たら止まって報告。

## 12. BS の drafts も型検査の対象外（2026-11-17 夕、ユーザー決定）

`formalization-plans/bhatt-scholze/drafts/` は本体ではなくビルドも監査もしない設計の紙なので、§10 の Archive と同じく、移動・改名の追従は**文字の置き換えだけ**を当て、型検査は求めない。IC-1 の停止（0edfe41f2）で見つかった `drafts/A1/CrystallineInput.lean` は、移動の前の環境でも 19 エラー（`EInfinityTheory`・`PerfectoidizationInterface` など、もう無い名前）で、IC-1 による不具合ではない。⑦ の追従の案（34 行の import、130 行の関手と制限の名前の 3 か所）を文字で当て、報告に「移動の前から 19 エラー、追従は文字の置き換えのみ」と記録する。drafts が今の本体の名前に合っていない件は BS の整理のレーンの段 0 で扱う。drafts は外部 importer の数（30 ファイルの条件）に数えない。

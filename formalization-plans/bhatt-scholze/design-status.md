# BS 設計段階の状態と要確認の一覧（2026-11-02 作成、2026-11-05 更新）

概要：BS の設計段階（ビルドなし、`drafts/` に骨組み）の到達点と、骨組みに残した「要確認」の分類。A0〜A1 の設計書・骨組みを一度見直した結果。
方針：要確認を五つに分ける：(A) 基盤の名前を探すだけ、(B) BS 側で決める設計の細部、(C) ∞ 側の窓に依存、(D) 論文の層の区切り 2b の後に
HA を読んでから、(E) 結晶側の黒箱。A・B は中身を書く段階の最初に片づけ、C・D は時期を待ち、E は独立の作業単位。
規約：状態の表は進捗報告の書式（一段目は全項目、進行中の親の下は二段目を全項目、一項目一行）。日付は絶対表記。
決定の一覧は各設計書（U・D・D-S・D-A1 番号）を正本とし、ここでは所在だけ示す。
使われ方：設計段階の進捗の正本。調整役への中間報告の元。中身を書く段階に入るときの作業一覧。

## 0. 新しいチャットへの引き継ぎ（2026-11-05、段階 II の開始時）

ユーザー決定（11-05）：BS は段階 II から新しいチャット（設計の Claude Code）に移る。BS-W11 は新しいチャットで始める。この節が入口。

### 0.1 目標と規則

- **目標**：E3（`SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean` の `exists_perfectoidizationInterfaceE3`）を、Bhatt–Scholze の原典の経路 A0〜A9 で消す（stage2 の A 案）。
- **ユーザーの規則**：「adhoc にやらないで、基本は論文通りに形式化したい。特に定義は変えないで、定理は特別な場合だけ証明する」。避けられない差は D 番号を付け、先に相談する（D 番号はユーザーが付ける）。設計判断は推奨を添えて出す。
- **終わりの条件（11-05 夜、ユーザー）**：sorry 0。a9-design §3 の「恒久的な引用」3 件（D68・G-A6-1a・G-A6-1b）も証明する（計画 A-7、経路は §2 の決定の表「改訂（11-05 夜）」）。許可一覧に sorry は入れない。**drafts の追従（A1/CrystallineInput・A1/HodgeTateComparison・A6/ArcSheafProperty）は調整役が行う（未）**。
- **役割**：Claude は設計・drafts・Codex 指示書・検収。**段階 II では BS 設計のチャットを置かず、段階 II の調整役のチャットがこの役を持つ（11-05 夜、ユーザー）**。Lean の本体のコーディングは Codex（指示書 `bhatt-scholze-codex-wN.md`、停止点で報告、経緯を書いて自己完結にする。ユーザーは Codex のチャットを替えるので）。
- **コミット**：main に直接、自分の範囲だけを **`git commit --only -- <paths>`**、その後 `git show --stat HEAD` で確認（11-04 に `git add && git commit` で他セッションの staged 削除を巻き込んだ。memory「main では commit --only」）。帰属行は `Co-Authored-By`。
- **ビルド**：drafts（`formalization-plans/bhatt-scholze/drafts/`、`SerrePositivity/` の外）はビルドしない。本体の単体ビルドは coordination.md §2-4a（`ps -axo command=` で他のビルド・verify がないこと、`scripts/refactor/with_build_lock.sh --wait 0`）。全ビルドは調整役の暦。
- **worktree**：BS の Codex の worktree は**一度に一つ**、`/Users/sugakubunka/Documents/LEAN_Projects.nosync/` の下（/tmp は再起動で消える）。こまめにブランチへコミット。CA の新規ディレクトリなど監査対象は sorry 0 になってから、調整役が取り込む。
- **import**：drafts は移動後の名前で書き、書いたら実在を確かめる（取り込み後に書いた旧名は機械書き換えの対象外）。改名表が回ったら追従する。
- **docstring**：日本語の 概要／方針／規約／使われ方（memory「Docstring style guide」）。

### 0.2 読む順

1. この節と §1 の状態表（各単位の行）。
2. `bhatt-scholze-stage2.md` §3（A 案の全体像）と `a9-design.md`（E3 の八欄と A0〜A8 の対応、§3 の引用表、§7 の import 順）。
3. 設計書 `a0-design.md`〜`a8-design.md`（単位ごと。段 2 で書く順は A2 → A1 → A3 → A4〜A7 → A5 の Prop 8.5 → A6 → A8）。`infinity-sheaves-design.md`（∞ 層 S1〜S8）。
4. **入口表 `foundation-entry-points.md`**：drafts が待っている基盤の宣言、担当、∞ への依頼（§4、§4.1 に S3 の経路と G9・G10 の型）、段 2 の点検表（§5）、履歴（§6）。
5. drafts：`drafts/README.md`（置き場所の表と「ファイル順序」の DAG）→ 各ファイルの冒頭 docstring。
6. 指示書：`bhatt-scholze-codex-w11.md`（次に出すもの）、完了例として `bhatt-scholze-codex-w10.md` と `report-codex-w10.md`。
7. Codex レビュー W9 の判定と扱い：§5 の表（`review-codex-w9.md` は必要なときだけ）。
8. 調整：`../coordination.md`（暦・待ち条件）、`../infinity-codex-g1.md`・`g2.md`（∞ の段 G）。
9. 勉強ノート：`exposition/ja/bs/`（章＝原典の節）。

### 0.2′ 11-10 の決定（ユーザー）：CAlg_R の界面（D71〜D73）

- **D71〜D73**（`calg-interface-design.md`）：BS は E∞ 代数の ∞ 圏を構造 `EInfinityTheory` を通してだけ使う。今の Barratt–Eccles の模型は実例の一つ。HA の方向で作る場合は別の実例を作り、Hinich Thm 4.1.1 などで比べる。実装は BS-W14（⑤a）。
- **整理の候補（11-10）**：BS-W15 の `Delta/DividedPower/RegularSequencePDUniversalTor` が `KST/DerivedBlowup/ScalarTensorView`（Mathlib だけを import する係数拡大とテンソルの表示比較の補題）を import している。主定理の閉包に KST のディレクトリが入るのを避けるため、このファイルを `CommutativeAlgebra/` へ移す（alias を残す）。KL-W1 の後の小さな整理で行う。
- **D74**（BS-W15 §3 の 2）：Ex 2.21・3.4 の普遍的な向き付き prism の Frobenius の平坦性は、原典どおり d 完全平坦の形で本体に置く（drafts の A1 の通常の平坦性の型は、A1 の界面への書き換えのときに見直す）。
- **記録の訂正（11-12 夜、§4 の見直し R4-2・R4-3）**：A0-3b（Lemma 3.7 (2)(3)）・A0-3d（Cor 3.12）・A0-4 の Tor 振幅は BS-W15 K4・W17 で本体に入った（`Prism/Bounded/CompleteFlatDiscrete`、`Prismatic/FlatTopologyPushout`・`FlatCechSheaf`・`FlatCechDescent`、`HomologicalAlgebra/CochainCompleteTorAmplitude`）。下の表の「未」は古い。a0-design の D22（位相を生成される最小の位相として定義する）は本体では採らず、原典どおり Cor 3.12 で site を示してから `flatCoverage` で位相を置いた。a1-design の Lemma 4.10「Prop 6.2 の系」は、本体の `bockstein_sq_zero` が Prop 6.2 を経由しない直接の証明（p=2 は δ による余境界、奇素数は cup 積の次数付き可換性）で示している。
- **記録の訂正（11-13、§7・§8・§10 の見直し R7-8・R8-11・R10-8）**：§1 の表の A3・A6-2・A8・A9 の行は古い。A3 の古典部分は BS-W15 K5（main 1d5a7113b）と BS-W17 H5（d6ecc3c58・9d8509776）で本体 `BhattScholze/Semiperfectoid/` などに入った（Lemma 7.7(1) `DiscreteDelta`、7.7(2)(3) `DiscretePrism`・`PrismRetract`、Lemma 7.8 `CategoryTheory/InitialOfRetraction`、Ex 7.9 `LciEnvelopeExistence` ほか `LciEnvelope*`、Prop 7.10 の T・S′ `RootRelation*`・`RootFamily*`・`InitialPrismPerfection`・`Cor73PrismComparison`。対応は a3-design §1 の表の後の追記）。A8 の perfd を使わない部品は BS-W13（11-10、main 1d9eb11ee・1c36c06c3）で本体に入った（`BhattScholze/Almost/` の AlmostConnectivity・AlmostTensor・AlmostTensorForward・AlmostGenerators・CompletedModuleTensor・FiniteEtaleComparison、`Perfectoidization/Derived/` の IntegralClosureCompletion・PerfectoidFilteredColimit・IntegralApproximation・IntegralClosureApproximation。a8-design §4）。G-A8-6 は BS-W11（`Perfectoidization/Derived/FiniteEtalePerfectoid`）。A6-2 の三つの引用は 11-05 夜の改訂で引用でなくなった（1a は ⑥ の BS17 で証明、1b は主経路から外し G-A6-1 は BS-W12 の経路 B、1c は本体 `ArcValuationMilnor`）。A9 の前提 W9-III-08 は BS-W10 作業 A（cc67ea88e）で解決済み。
- **D81（11-16、ユーザー決定）：CAlg は HA 流で作る。** E∞ 代数の ∞ 圏は HA の方向（∞-オペラッド・対称モノイダル ∞ 圏、CAlg(C)、HA 2〜3 章）で定義する。D75（BS の E∞ は BE の模型で供給、HA の方向は BS の経路から外す）を改める。きっかけは P⁰ を Lurie の構成（DAG XIII Constr 2.2.6）で正確に定義する目標（11-15、`research/p0-lurie/`）：P⁰ は CAlg(Mod_k) の上の Sym^p・Tate 構成で作るので、HA 2 章の対称モノイダル ∞ 圏が要る。未決（ユーザーと相談）：BE の模型を計算用の模型として整流（Hinich／Pavlov–Scholbach）で結ぶか、使わないか；界面 `EInfinityTheory`・D79・D80 の扱い；進行中の BE 固有の作業（⑤d の G12 の BE への適用、③-b の 3b-4 の実現の側、⑤a の M14）の扱い；基盤の作業の順序と担当。規模の目安は `research/einfinity-route/README.md` §6（A 約 83,000〜212,000 行、外挿）。
- **D81 の続き（11-16、ユーザー承認）：G12 のモナドの道は打ち切る。** ⑤d の報告 §131〜§132（afd5b5c3b）：残りは一般の ∞ モナドの理論で補正後 30,200〜58,400 行、BE への適用で 8,300〜16,300 行。5a-4（sifted の保存）は HA 3.2.3.1・Cor 3.2.3.2（極限 3.2.2.5、presentability 3.2.3.5）、S7 の単位の条件は HA 2.2.1.6〜2.2.1.9 のモノイダルな局所化の道に移す（どちらも HA 2 章の対称モノイダル D(A) が前提で、P⁰ と同じ基盤）。⑤d の枝 `math/bs-m15` の `InfinityCategories/HA/Monads/`（179 本・18,959 行）は消さず、main に取り込まず、後で HA 4.7 が要るときの参照として残す。⑤d は止めたまま、M15・D80 は D81 の下で決め直す。
- **D80（11-14、調整役）**：M15（descendability、E∞ の上の一般の R 加群）は BE の模型で作り、任意の `EInfinityTheory` への輸送は作らない。界面に加群の族の欄を足さない（BS-W16 報告 §61.4）。BS の利用側（A5 の descendability の部分）は E = `barrattEcclesTheory` に特殊化する。D75（BS の E∞ は BE の模型で供給）と A9 が具体的な E で組み立てることによる。BS-M15 §5。
- **D79（11-12 夜、ユーザー決定：原典どおり）**：界面の P⁰ を原典（DAG XIII Constr 2.2.6）と設計書（a4-design §2.2 (a)・G-A4-1）どおり **Sp 値**にする。`EInfinityTheory.powerOp0` を W_k := U_k ⋙ V_k の自己変換（V_k : D(k) → Sp は Eilenberg–MacLane の忘却）に、`powerOp0_zero`・`powerOp0_pos` をスペクトルのホモトピー群 π_n の主張（π_n V_k ≅ H^{-n} の自然な比較を通す）に直す。まず k = F_p に限る（Lemma 8.4 は E∞-F_p 代数）。旧型（D(k) 値の Frobenius 半線形な自然変換）は原典より強く、持ち上げの存在が未確定だった（W16 §62〜63）。V_k と native なスペクトルの圏は当面 ⑤a が V_{F_p} まで作り、一般の形は後で ∞ の基盤（③）に移す（K の再開でも使う）。
  - **D79 の改訂（11-13、ユーザー決定）**：M14 は May 案（BS-W16 報告 §96、指示書 §26）。界面の `powerOp0` は F_p に限り、ho(CAlg F_p) 上の可換群値関手の NatTrans（全整数 n の π_n＝H^{-n} の演算）にする。一般 k は F_p への制限で読む補助。coherent な Sp 値の P⁰（DAG XIII Constr 2.2.6 の形）と強い補助出力は補完へ。A4 の Lemma 8.4 に要る二重模型の実現上の Frobenius 比較は A4 の局所的な補題として M14 に含める（G10 の後）。見込みは新規 5,500〜9,950 行（全体 15,716〜20,166 行）、上限約 20,000 行。
- **D78（11-12）**：界面 `EInfinityTheory` に `coproduct_tensor_legs` を足す。`coproduct_tensor` の同じ全関手の同型が、`coprodWith_cocone` の二脚を、H⁰ で正規化した単位による二つの包含（HA 3.2.4.7）へ、ホモトピー圏で送る条件（W16 §13）。二点の離散な図式なので、余錐の移送はホモトピー圏の等式から一般の補題で得る。
- **未決の解消（11-12）**：W16 の E2 は経路 B（bar と実現、ユーザー決定）、sifted の一般部分は ③-b（IS-W2）。
- **後回しの項目（11-12 朝）**：(1) Prop 7.10 の S′ の単位の p 完全忠実平坦性（W17 §9、一般の qrsp の場合に要る。E3 は使わない）。(2) BS-D69 の一般の I の η の一般化（D69 の追記、E3 は D68 の ℤ_p の η で足りる）。どちらも使う場所が出たら範囲に入れる。
- **未決（11-11 夜、11-12 昼に決める）**：BS-W16 の E2。⑤a の紙の検討（report-codex-w16.md §21）で、E2 の二欄と native な余積錐の総計は経路 A（セル対）9,400〜12,000 行・経路 B（自由 bar と実現）9,400〜12,400 行、どちらも sifted の保存 S（2,300〜3,750 行）を含む。S の「厳密な Δᵒᵖ 図式の hocolim と native な錐の橋」「任意の coherent な図式への移送」は一般の ∞ 圏の道具で、③（G10 など）と共有できるかを確かめる。あわせて、界面の `coproduct_tensor` の型が `coprodWith_cocone` の二脚をテンソルの標準射へ送る条件を持たない点（A2 が要る）を、界面の欄の追加か A2 側の別の比較で扱う。
- **D77（11-11）**：Construction 6.1 の仮定。原典は「A/p の Frobenius が平坦」と書くが、Ex 3.4 が示すのは d 完全平坦だけで、証明が使うのは式 (6) の中央の射の忠実平坦性だけ。drafts の `Construction61Hypotheses` は原典どおり残し、本体の補題は d 完全平坦性と A/d の p 正則性を引数に取る（一般化）。普遍の場合は K2 の定理を直接入れ、drafts の `universal61` は使わない（BS-W17 §3）。
- **D76（11-11）**：drafts の Ex 7.9 の存在補題 `exists_lciEnvelope` に、原典どおり R の p 冪ねじれの有界性を足す（原典より強い主張だったため。利用者なし、E3 の経路は有界な場合だけ。BS-W15 §6）。
- **D75（11-11、ユーザー決定）：段階 II の BS は E∞ 代数を今の模型（Barratt–Eccles、`barrattEcclesTheory`）で供給する。HA の方向（∞-オペラッドで CAlg(D(R))、Hinich／Pavlov–Scholbach で整流）は BS の経路から外し、「HA の基盤」の課題として別に持つ。** 根拠は `research/einfinity-route/README.md` §6（A 約 83,000〜212,000 行、B 約 12,700〜33,000 行、較正後の上限 約 60,000。A の整流は ∞-monad・Barr–Beck がまだ 0 件の領域に乗る。B の成果は界面を通して A にほぼそのまま使える）。
  - BS-W16（⑤a）と ④（G12・P⁰・M15）は B で進める。G12 の経路（組合せ的モデル圏の局所化の表現可能性、HTT A.3.7.6 相当）は ④ の開始時に設計する。
  - 「HA の基盤」レーン（∞-オペラッド・対称モノイダル ∞ 圏、A の行 1〜2、約 12,000〜32,000 行）は、HA の確認が第 2〜4 章を終えた時点で範囲を決める。整流はその後の課題。
- 11-10 の Prisms の地図の更新：目標に必要な 105 項目のうち、本体（証明済み・特別な場合）59、本体に部品 8、drafts 29、E3 の界面 6、設計だけ 2、なし 1（`research/bs-coverage/`）。

### 0.3 現在地（11-07 の更新。下の 11-05 の記述は経緯として残す）

- **段階 II のレーン（11-07）**：⑤a BS 実装（BS-DOC1 完了 → BS-W11 進行中：A-2・B-2 は main に入った）、⑤b BS-D68（段 1 進行中）、⑥ スキーム論（BS17 の経路：2a′・2b・2d の一部は main に入った）。設計は調整役。
- **終わりの条件は sorry 0**（恒久の引用は 0 件）。D68 は直接証明、D69 は大きい模型で関手同型、結晶 site は最小限で作る（a1-design §10・§10.5・§11）。
- 本体に入った BS 段階 II のモジュールは `scripts/audit_bhatt_scholze_stage2.lean` で監査する。

### 0.3′ 現在地（11-05）

- **段 0（設計と骨組み）完了**：drafts 51 本・約 12,900 行。A0〜A9 に `True` の仮置きはない。Codex の drafts 作業 BS-D1〜D6 と S4 の篩比較（`report-codex-s4-sieve.md`）は終了、指摘 D1-01〜D5-07 は設計側で解決（§5）。
- **段 1（基盤を待たない古典的単位）**：BS-W10 は**終了**（作業 A：CompletedTensor から E3 依存を外し有限直積を直接証明、main cc67ea88e。作業 B：Lemma 10.12、main 4019014a1）。**次は BS-W11**（`bhatt-scholze-codex-w11.md`：根添加、Lemma 8.8 の前段と試験付値環、有限エタールの perfectoid 性、arc site の 1 圏部分）。**開始は ∞ F-2（名前空間の付け替え）の取り込みと改名表の配布の後**（調整役が知らせる）。開始時に改名表で W11 と drafts の名前を追従してから出す。
- **段 2 への橋**：IF-G1 第一区切り（G7・Core・G13・⊗ᴸ・G3・G8）は main に入り、drafts の仮名は本名にした（入口表 §6）。S4 は `drafts/Sheaves/SheafGenerators.lean` で型にし、残る穴は G14 と G8 の自然性の二つ。S3 の経路は (c) Quillen A に決定（入口表 §4.1）。論文の層の B4（Pair を Principal の反復に）は main に入り、BS は `pairCompletionH0Unit` への置き換えと heartbeat の引き上げ 2 件で対応済み。

### 0.3.1 11-07 の drafts の書き直し（調整役）

- **A1：D68 の改訂を反映**。黒箱 `crystalline_deRham_polynomial_Zp` と `CrystallineComparison` 系を削除し、`hodgeTate_of_deRham_cartier` を六段（Lemma 5.4 → 結晶の橋 → pd 包含 → pd de Rham の双複体 → Cartier → 生成元の照合）から示す骨組みにした（a1-design §10）。未使用の `deRham_iso_polynomial_crystalline` も削除。**恒久の引用は 0 件**。sorry の行は 180 → 203。
- **A0：型がなかった四つを追加**。新しいファイル `A0/FlatDescent.lean`（Lemma 3.7(2)(3)、固定基底の Cor 3.12 (a)〜(e)）と `A0/BaseChange.lean`（Lemma 4.22 の一般形、Lemma 4.20 の多項式代数の場合）。sorry +13。
- **要相談（ユーザーに尋ねる）**：
  1. D69 の代案：`deRham_iso_polynomial_modP` の型を「各 n の VertexIso と X ↦ X^p の自然性」に弱めると、関手同型の貼り合わせ（∞ 側の部品 (i)(ii)、a1-design §10.4）が要らなくなる。使う側（A5 `rootMap_modP_eq_deRham`）はそれで足りる。A1-5 の主張の型が変わる。
  2. Lemma 5.4 は、N が余単体的可換環の場合に限った（原典は任意の加群。定理の特別な場合）。
  3. 無限変数版 G-A1-15 が主経路に入る（B = ℤ_p{X}^∧ の mod p は変数が無限個）。
  4. ~~A1-5 の `wittPdBridge` に導来 Nakayama（G-A1-4）が残る。~~ 11-07：`wittPdBridge` は D69 の大きい模型の設計（a1-design §10.5）で削除。
  5. Lemma 3.7(2) で M に導来 (p,d) 完備を仮定した（原典の証明と直後の注意の読み方）。
  6. Lemma 4.20 は比較の写像を存在の形で述べた。Prop 6.2 (b) が η との両立を使うなら、指定した辺の形に直す。
- 後始末：Tor 振幅の定義が A1（HodgeTateComparison）と A0（BaseChange の `Derived.` 版）に重複。中身の段階で A0 の版に一本化する。
- **決定（11-07、ユーザー）**：要相談の 2（Lemma 5.4 を余単体的可換環の N に限る）と 5（Lemma 3.7(2) で導来 (p,d) 完備を仮定）は承認。1（D69 の代案）は採らず、**元のまま関手としての同型 `deRham_iso_polynomial_universal` を作る**。そのための部品は a1-design §10.4：(i) 選び方によらない模型と厳密に自然な zigzag（BS 側、プリズム側とド・ラーム側の両方）、(ii) `totEInfinityFunctor` と、厳密な自然変換から関手 ∞ 圏の辺を作る部品（∞ 側）、(iii) 成分ごとに可逆なら可逆（本体に既存）。
- **D69 の部品 (i) の設計（11-07、a1-design §10.5、drafts に型）**：厳密な関手性の原理は「対象は選んでよく、射は普遍性で一意に決まる持ち上げ」。C 上の小さい模型 `pdModel C n` は Poly(C) について厳密に関手的なので、大きい模型（要素すべてを変数にする）が要るのは A₀ と W の上だけ。Ω*_{Q/C} へは C 上の小さい模型で span（Tot D₀ ← Tot K → K⁰）。`wittComposite` は大きい zigzag を通る形に定義し直した。sorry +60（Shared 8→20、CrystallineInput 70→87、DeRhamComparisonPoly 28→59）。**要相談（ユーザーに尋ねる）**：(1) A2 の `PolyDeltaData` に「大きい模型の Tot との関手同型」の欄を足すか。(2) 大きい枠の J つき pd Čech 模型は原典にない（Constr 4.18 の考え方を結晶側に転用、D25 β の延長）。(3) 一般の J つき pd 包と「表示によらない」補題は Mathlib にない古典（Berthelot）。(4) D69 で使われなくなった `pdPolynomialComparison`・`PDPolynomialComparison`・`pdTotMap` を削除するか。(5) cutoff を Q ごとから共通にするか。
  **決定（11-07、ユーザー）**：(1) 欄を足す。(3) 承認。(4) 削除した。(5) 保留。(2) は説明の後に判断（原典の定義は変えず、Thm 6.4 の証明で結晶 site の関手性を使う所を大きい模型の厳密な関手性で置き換える。D25 の延長）。
- **方針変更（11-07、ユーザー）**：結晶 site も必要最小限で作る（D25 の改訂）。設計は a1-design §11、型は drafts/A1/CrystallineSite.lean（新規、40 宣言、sorry +35）。affine な big site（Stacks 07HM の CRIS(C/A)、Ber06 §III.4）、Zariski 位相、基底 (W, J, 標準 pd)、cutoff κ、RΓ_crys := RΓ(site, O_crys)。定理：(a) Čech–Alexander（pro 弱終対象）、(b) Poincaré 補題、(c) Thm 5.2 の多項式の場合、(d) 関手性。§10.5 の大きい模型と zigzag は「RΓ_crys を計算する定理」として残り、要相談 (2)（大きい模型は原典にない）は解消。D68 への影響なし。**要相談（§11.6、ユーザーに尋ねる）**：affine に限るか、位相（Zariski／chaotic）、(c) の比較写像の形、∞ 関手としての RΓ_crys を置くか、`pdCechNerveMap_quasiIso` の扱い、対象を p 冪零にするか p 進完備にするか。
  **決定（11-07、ユーザー）**：1 affine に限る。2 Zariski 位相（O_crys が層であることを定理に。重ければ chaotic に替える相談をする）。3 **Thm 5.2 は原典の η（b ↦ φ(b)、δ 変数つきの D^•）の写像が同型であるという形で述べる**（X ↦ X^p の写像は主張から外し、要るなら計算の補題に。理由：二つの橋の並立、Frobenius との両立、ほかでの使い回しで困らないように。η は D68 の `crystallineBridge` を一般の基底 (A, I, γ) に広げて作る）。4 ∞ 関手としての RΓ_crys は置かない。5 `pdCechNerveMap_quasiIso` は主張を残し証明を site 経由に差し替える。6 対象は原典どおり p 冪零。

### 0.4 ∞ に頼んでいて未着の項目

| 項目 | 内容 | 使う場所 | 依頼の所在 |
| --- | --- | --- | --- |
| G8 の自然性（四角形） | 集合値前層の射 φ について Map(Y ⋙ ⊗M, F) → Map(X ⋙ ⊗M, F) と `sectionsOf_map φ` が G8 の同値を通してホモトピー圏で可換。G1 版では言えないので**自然な別版** `tensorSpaceFunctor_setWeightHomNatural` で。先行分（指定錐版 `SetWeight.sectionsMap`、篩包含の二辺、別版）は段 F の verify の後に main へ | S4 `isLocalObject_sheafGeneratingEdges_iff`、S8-5 | IF-G2 の最初の項目 |
| G14 | presentable な E の小さい検出族（`IsDetectingFamily`：`PinchedInterval.postcompose (M i)` の QCat 同値で検出、添字 `Type u`）。`exists_limitDetectingPresheafModel` から導く | S4 `exists_detectingFamily` | IF-G2 §3（main 401c32777） |
| G9 の小補題 3 つ | left 側の nerve の Quillen A、`IsLeftCofinal` の ulift 保存、縮約の逆向き版（型は入口表 §4.1） | S3 `isLimitCone_iff_restrict_cech`（BS は comma の同一視と縮約を書く） | IF-G2 §4（main b715120a5） |
| G10 | 余単体的 A 加群の D(A) での Δ 上の極限は交代余面複体（型は入口表 §4.1） | A0 CechAlexander、Shared `totEInfinity_isLimitCone`、A1、A6 Prop 8.10 | IF-G2 §4 |
| G12 | `IsPresentable (CAlg_R A)`（HA 3.2.3.5） | `sheafification_exists_cAlg`、A2、A5 | IF-G2（最後、E2 レーンの範囲） |
| M14 | E∞-F_p 代数の冪作用 P⁰（φ_k 半線形、D5-03） | A4 Lemma 8.4、A3 G-A3-9 | 段 G、担当は A4 の中身の段階で決める |
| M15 | Mathew の descendability（Mod_R の thick ⊗-ideal、内部 Hom・完備テンソルを含む） | A5 Lemma 8.6・Prop 8.5 | 段 G、担当は A5 の中身の段階で決める |

### 0.5 未決の点

- BS-W11 の基準コミットと worktree（F-2 の後）。F-2 の改名表への追従。
- S3 の comma の同一視と縮約（1 圏）を書く時期：G2 の G9 が入ってから（drafts で書くか段 2 の指示書に入れるか）。
- `drafts/Sheaves/SpaceValued` の `is0Truncated_iff_pointwise`・`kanDiscretePresheafInclusion` は BS 側の証明（段 2）。
- M14・M15 の担当（E2 レーンか BS か）は、A4・A5 の中身を書く段階で調整役と決める。
- 中身の段階への持ち越し：A6/ArcSite の docstring の `FinitaryPreExtensive` → `FinitaryExtensive`（D5-06）、A0・A1 の旧 Mathlib 名 `CosimplicialObject.alternatingCofaceMapComplex`（D5-05）、A4 の `cAlgH0Algebra` → 基盤の `cAlgH0Ring`。
- ~~監査の許可一覧（恒久の引用 3：D68 の結晶入力、G-A6-1a・1b の arc 降下の引用。暫定 2）は段 3 で。~~ **11-05 夜に撤回**：段階 II の終わりの条件は sorry 0 で、許可一覧に sorry は入れない（三件とも証明する）。

## 1. 状態

**Codex レビュー W9（2026-11-02〜03）完了：条件付き妥当**（段 I〜III、12 論点すべて「妥当」、A9 は実施条件つき）。条件は W9-III-08 の実施（CompletedTensor の芯の分離・有限直積の
E3 非依存化、2a 後）と実ファイルでの到達性検査。致命は W9-I-01…39、W9-II-01…16、W9-III-01・04・08 の計 14 件で、すべて訂正または方針決定済み。sorry は 194 宣言（恒久的な引用 3）。
詳細は §5 と a9-design §8。

| 単位 | 設計書 | 骨組み（drafts） | 紙の検証 | 中身 |
| --- | --- | --- | --- | --- |
| ∞ 層 S1 層条件 | infinity-sheaves-design §1・§3 | Sheaves/SheafCondition | — | C（JoinCone.ulift、生成系で十分の補題） |
| ∞ 層 S2 Γ・RΓ | 同 | Sheaves/GlobalSections | — | C（層化の存在 S4 は入力） |
| ∞ 層 S3 脚注 10 | 同 §1 | Sheaves/CechConerveLimit | — | C（G9・G10） |
| ∞ 層 S4 層化の存在 | 同 §1 の 1〜4 | GlobalSections の `sheafification_exists` | — | C（G3・G4・G6・G8） |
| ∞ 層 S5 完全性 | 同 §1 の 5 | 未 | — | C（G7） |
| ∞ 層 S6 κ | 同 §5 | A0/PrismaticSite の `essentiallySmall` | 済（a0 §5.1 の 4） | B（構造の移送） |
| ∞ 層 S7 D(A) への適用 | 同 §4 G3 | 未 | — | C |
| A0-1 site・Not 4.16 | a0-design §2.1〜2.4・2.7 | A0/PrismaticSite（BS-D1 停止点 4：cutoff 不変性は HasEnvelopes 仮定で CechAlexander に、残る `True` は `prismaticCohomologyFrobenius` 1 件） | 済（κ） | A（4 件）・B（κ 不変性の形） |
| A0-2 Čech–Alexander | a0-design §2.8 | A0/CechAlexander（BS-D1 停止点 4 済：余積は標準頂点の脚 §2.8′、`cechNerveData`、Tot 比較、Rem 4.19 の模型と底変換） | 済（弱始性・余積） | A（1 件）・B（R の形、cechKernel、型合わせ） |
| A0-3a Def 2.42 | a0-design §2.5 | A0/PrismaticEnvelope | — | A（Koszul の名前） |
| A0-3c Prop 3.13 の定義と変数の場合 | a0-design §2.5 | A0/PrismaticEnvelope | 済（a0 §5.1 の 1・2） | A（完備テンソル）・B（閉包の定義） |
| A0-3b Lemma 3.7(2)(3) | a0-design §2.6 | 未 | 自由加群の場合は済（a0 §5.1 の 1） | D |
| A0-3d Cor 3.12 | a0-design §2.6 | PrismaticSite の `flatTopology_refine` のみ | 未（a0 §5 の 5・6） | D |
| A0-4 Lemma 4.22・4.20 | a0-design §2.9 | 未 | — | D |
| A1-1 de Rham・η^* | a1-design §2.1・2.2 | A1/HodgeTateMap、Shared/{CupProduct,Bockstein,DeRhamPolynomial}（BS-D4 停止点 3 済、11-03：`True` 0 件。`hodgeTateMap` は各次数の線形写像＋単位・積・微分の両立、Bockstein は係数 A の `regularBockstein`、D4-03・D4-05・D4-06） | — | B（R の形、線形性の述べ方、係数環）・A（忘却関手） |
| A1-4 Prop 6.2・Thm 6.3 | a1-design §2.4・2.5・§3 | A1/HodgeTateComparison（BS-D4 停止点 3 済：`True` 0 件。`universalOrientedPrismRing p`＋`CommRing`（D4-02）、α の Tor 振幅は mod p 通常 ≤ 1 と Koszul 版 3 に分離し利用側は有限性のみ（D4-04）） | 未（a1 §8 の 5〜7） | A（Flat の形）・D（G-A1-4・5・13） |
| A1-2 結晶側の対象 | a1-design §2.3 | A1/CrystallineInput（BS-D4 停止点 3 済：`True` 0 件。恒久的な引用は `crystalline_deRham_polynomial_Zp` 一件、G-A1-14/16/17 は証明予定） | 未（a1 §8 の 1・2） | E |
| A1-3 Lemma 5.4・Thm 5.2 β・Cartier・Cor 5.5 | a1-design §3 の 3〜6 | A1/CrystallineInput（BS-D4 停止点 3 済：`hodgeTate_of_deRham_cartier`、有限変数の Cartier） | 未（a1 §8 の 3・4） | E |
| A2-1 animated 代数（P_Σ）・離散環の埋め込み | a2-design §2.1 | A2/AnimatedAlgebra（BS-D4 停止点 1 済、11-03：`True` 0 件） | 未（a2 §7 の 1） | A（Yoneda の名前、集合値前層の離散埋め込み） |
| A2-2 Δ の Kan 延長・Frobenius・(1) | a2-design §2.2 | A2/DerivedPrismaticCohomology（BS-D4 停止点 1 済：`True` 0 件。`prismaticCohomologyCAlg`＝A5 の第 0 脚、`derivedPrismaticFrobenius`＝A4/A7 の Frobenius の行き先、要確認は G-A2-3・9 の CAlg 反射・G12・Shared の Tot・A0/S2 の関手性） | — | C（G-A2-3・4）、G-A1-11 |
| G-A1-11 CAlg 値の層・RΓ、模型の E∞ 構造 | a1-design G-A1-11、a2-design §2.2 | Sheaves/CAlgValued、Shared/CosimplicialEInfinity | — | C（G12、U の保存性、Barratt–Eccles の余鎖作用の形） |
| A2-3 HT filtration・cotangentWedge | a2-design §2.3 | A2/HodgeTateFiltration（BS-D4 停止点 1 済：`True` 0 件。gr は導来 p 完備化、D4-01） | 未（a2 §7 の 2） | C（G-A2-2） |
| G-A2-2 D(A) の t 構造・切り捨て | a2-design §3 | DerivedGeneral/Truncation | — | C（置き場所は調整役、BS が骨組み） |
| G-A2-3 (p,d) 完備化の ∞ 関手 | a2-design §3 | DerivedGeneral/CompletionFunctor | — | C・D（HA の名前は 2b 後） |
| A2-4 完備化不変性・(4)・(5) | a2-design §2.4 | A2/BaseChangeAndTensor（BS-D4 停止点 1 済：`True` 0 件。(4)(5)・D32、要確認は ScalarRestriction の随伴の単位） | 未（a2 §7 の 3・4） | C・D |
| A3-1 Lemma 7.8、Lemma 7.7(2)(3) | a3-design §2.1 | **11-13：古典部分は本体**（`CategoryTheory/InitialOfRetraction`、`Semiperfectoid/{PrismRetract,DiscretePrism}`、BS-W15 K5）。A3/DiscreteCase（BS-D4 停止点 2 済、11-03：`True` 0 件。評価射の δ 射性は p ねじれなしの標的、始対象はその充満部分圏、D36 (a)） | — | A（Mathlib の冪等完備・Under）、C（S2 の極限の脚） |
| A3-2 Lemma 7.7(1′)(1″) | a3-design §2.1 | **11-13：古典部分は本体**（`Semiperfectoid/DiscreteDelta`、BS-W15 K5）。A3/DiscreteCase（BS-D4 停止点 2 済：`True` 0 件。要確認 G-A3-9） | — | A（Rem 2.2 の δ 構造の名前） |
| A3-3 Ex 7.9 | a3-design §2.2 | **11-13：古典部分は本体**（`Semiperfectoid/LciEnvelopeExistence` ほか `LciEnvelope*`、G-A3-7 の古典部分 `LciEnvelopeInvertP*`、BS-W15 K5）。A3/LciAndQuasiregular（BS-D4 停止点 2 済：`True` 0 件。普遍例は任意の有界 P₀ と分類射を明示引数に、D4-02。G-A3-7 は証明予定） | 未（a3 §8 の 1〜3） | G-A3-7（p 反転の議論。**証明予定**の補題で恒久的な引用ではない、W9-III-12）、G-A3-1・2 |
| A3-4 qrsp・Prop 7.10・Cor 7.3 との接続 | a3-design §2.3 | **11-13：T・S′ の古典部分は本体**（`Semiperfectoid/{RootRelation*,RootFamily*,InitialPrismPerfection,Cor73PrismComparison}`、BS-W17 H5。S′ の単位の p 完全忠実平坦性は後回し、§0.2′）。A3/LciAndQuasiregular（BS-D4 停止点 2 済：`True` 0 件。qrsp は完備・perfectoid の全射商・有界 p 冪ねじれ・完備余接複体の平坦性の四条件 D39、Cor 7.3 の入口は非零・零環で分岐 W9-I-44。要確認：p 完備環の標準 ℤ_p 作用（主元完備化の一意延長、2b の HA/DerivedCompletion へ。A6 の `arcPadicIntMap` と同じ）） | 未（a3 §8 の 4〜6） | G-A3-3・4・8、RootEnvelope の対応表 |
| A4-1 Not 8.1・Def 8.2 | a4-design §2.1 | A4/Perfectoidization（BS-D2 停止点 1 済、11-03：`True` 0 件。塔は `cAlgRestrictScalars φ_A` の正の反復、Frobenius の成分は A2 待ちの仮置き `discreteDeltaFrobenius`、`perfectPrismRing` = A_inf(R) = W(PreTilt R)） | — | C（G-A4-2・3・4）、A（Thm 3.10 の prism の名前） |
| A4-3 E3 の perfd・unit・h0 | a4-design §2.3 | A4/InterfaceFields（BS-D2 停止点 1 済：`True` 0 件。界面の欄の型に合わせた） | — | A（`completionRing` の関手版、CAlg_R の H⁰ の環）、D（2b の改名） |
| A4-2 Lemma 8.4 | a4-design §2.2 | A4/Perfectoidization | 済（a4 §5 の P⁰ の筋） | G-A4-1、A（Lemma 2.34 の名前）、A3-2 |
| G-A4-1 E∞-F_p 代数の P⁰ | a4-design §3 | Shared/EInfinityPowerOperation | — | C（置き場所は `EInfinity/PowerOperation/`、M14。担当は A4 の中身の段階で。Barratt–Eccles の作用の型） |
| A4-4 Example 8.3 | a4-design §2.4 | A4/AfterComparison（BS-D2 停止点 1 済） | — | A5 の後（Prop 8.5 を使う）。A6 で要るか確認 |
| A5-1 完全 site・Lemma 4.8・比較写像・Prop 8.5 の主張と系・E3 の limitCone | a5-design §2 | A5/PerfectSiteComparison、A5/InterfaceLimitCone（BS-D3 停止点 1 済、11-03：PerfectSite の `True` 0 件。Lemma 4.8 は有界標的版、第 0 脚は A0/S2 の CAlg 値 RΓ の射影待ち、Čech データは `CechNerveDataLarge`／小さい版の使い分け）；PerfectSiteComparison も停止点 2 で済（Prop 8.5 は比較射の `IsIso`、系 4 は切り捨て単位の像の可逆性。要確認 3：G12、BS-D4 の離散 Frobenius、A2 の π₀） | — | A（`PerfectPrismHomLift`、Cor 7.3 の対象、`SmallModel`）、C（S2・S3）、D（A0-3d の制限 G-A5-5） |
| A5-2 semiperfectoid の場合・G-A5-17 | a5-design §3.4 | A5/SemiperfectoidCase（BS-D3 停止点 1 済：`True` 0 件、`universalPerfectoidRing` は Cor 7.3 の選択） | 未（a5 §8 の 5） | G-A5-10・11・17、A2-3、A3-4 |
| A5-4 弱始対象・filtered 余極限・降下の形式部分 | a5-design §3.1〜3.3 | A5/WeaklyInitialAndDescent | 未（a5 §8 の 1〜4） | G-A5-2・7・8・14 |
| A5-3 descendability・Lemma 8.6 | a5-design §2.4・§3.5 | Shared/Descendable（D3-04 の `IsDescendableOver`）、A5/StrongDescent（BS-D3 停止点 2 済、11-03：`True` 0 件。要確認 5：M15 の Mod_D、係数拡大（ScalarRestriction に追加、D3-05）、A1-5 の三つ） | 済（a5 §8 の 6 は W9 続き 6 の G-A5-6′ の計算、7 は W9 ○） | G-A5-1（置き場所 `EInfinity/Descendable/`、M15）・6・12・13・15（A1-5） |
| A6-1 arc site・cover-dense | a6-design §2.1 | A6/ArcSite（BS-D1 停止点 1 済、11-03：`True` 0 件。D1-01 sieve の圏、D1-02 K₁ ⊔ K_ext、S1-E は基盤待ち） | 済（a6 §9。cover-dense は前段 G-A6-11 つき、W9-II-16） | A（Mathlib `IsCoverDense`・`SmallModel`）、G-A6-3、G-A6-11（R₀ の perfectoid 性） |
| A6-3 集合の層の等式・perfd の有限積 | a6-design §3.2 の 1〜4 | A6/SheafOfSetsExcision（BS-D3 停止点 3 済、11-03：SheafOfSetsExcision の `True` 0 件。延長は比較同値の `.functor`（D3-06）、S8 の離散入口（D3-07）） | 未（a6 §8 の 5・6） | A（Mathlib `Sheaf`・`sheafEquiv`）、G-A6-2・9 |
| A6-2 Prop 8.10・三つの引用 | a6-design §2.2・§3.1 | A6/ArcSheafProperty（BS-D1 停止点 2 済、11-03：`True` 0 件。三引用、G-A6-1、tilt（D1-03 の `tiltRing`）、G-A6-4〜7、Prop 8.10 は増大交代和複体の完全性、O は `CAlg_R (ULift ℤ)` 値、O と Hom の有限積保存、Cor 8.11 は affPerfd_κ/S 上の可逆な辺） | 済（W9 続き 5・6。O は CAlg_ℤ 値、W9-II-22） | E′（G-A6-1a・1b `sorry`、1c は証明）。**11-13：11-05 夜の改訂で引用なし**（1a は ⑥ の BS17 で証明、1b は主経路から外し G-A6-1 は BS-W12 の経路 B、1c は本体 `ArcValuationMilnor`）、G-A6-4〜7 |
| A6-4 Cor 8.12・E3 の excision | a6-design §2.3・§3.2 の 5・6 | A6/Excision（BS-D3 停止点 3 済：Excision の `True` 0 件。Cor 8.12 は界面の IsPullbackSquare、証明は S8 `sectionsOf_pushout` の引き戻し述語待ち） | 未（a6 §8 の 4） | C（S8）、G-A6-10 |
| S8 空間値の層・局所性 | a6-design §2.4 | Sheaves/SpaceValued・Sheaves/SetSections（切断、11-05 分離）・Sheaves/SheafGenerators（S4） | — | C（G13・⊗ᴸ・G8 は IF-G1 で入った。残りは G8 の自然な別版・G14（IF-G2）） |
| A7-1 Def 8.2 の animated 版・(5) 相対版・Prop 8.13 | a7-design §2.1・§2.2 | A7/AnimatedDomain（G-A7-1、A5 より先）、A7/AnimatedPerfectoidization（BS-D2 停止点 2 済、11-03：`True` 0 件。Prop 8.13 は完備 CAlg の押し出しからの指定比較射の可逆性。A2 待ちの仮置き 5） | 済（W9 続き 6） | C（G-A7-1・2：P_Σ の押し出し・完備化）、G-A7-4 |
| A7-2 Cor 8.14・E3 の universal | a7-design §2.3 | A7/DiscreteCore（G-A7-5、A5 より先）、A7/UniversalProperty（BS-D2 停止点 2 済：F(η_S) = η_P を先に置き、自己テンソルの同値と単位の合成＝乗法） | 済（W9 続き 6。単位の整合性は G-A7-8） | A（`IsPerfectoidization`、`completionRing` の普遍性）、A5-2 の芯の共有 |
| A8-1 Prop 10.4 複体版・Lemma 10.5・J-almost の基本 | a8-design §2.1・§3.1 | A8/AlmostConnectivity（BS-D2 停止点 3 済、11-03：`True` 0 件。一般 J の核 K、D2-02 の底変換は完備テンソルの像） | 済（W9 第 3 部 ○、W9-III-03 の訂正。非有界での Prop 10.4 の接続は Codex 未。**11-13：BS-W13 で本体に証明**（`Almost/AlmostTensorForward`、Lemma 10.5 も）） | B5 の既存、A7 |
| A8-2 Thm 10.9 の J-almost 連結性 | a8-design §2.2・§3.2 | A8/AlmostPurityConnectivity（BS-D2 停止点 3 済：`True` 0 件）。**11-13**：部品 G-A8-3′・3″ は BS-W13 で本体（`Almost/FiniteEtaleComparison`、`Derived/IntegralClosureCompletion`）、組み立ては drafts | 修復済み（W9-III-01・02：有限表示有限に戻し、S′ の完備性は G-A8-3′、ArcOutside は整性つき G-A8-3″。修復計算は W9 第 3 部で ○） | A（Thm 7.14・aic エタールの名前）、A6-4、A7 |
| A8-3 Lemma 10.12 | a8-design §2.3・§3.4 | **本体に入った**（BS-W10 作業 B、main 4019014a1、11-05）：`CommutativeAlgebra/UniversalHomeomorphism/`（6 本）・`CommutativeAlgebra/EtaleStratification/`（30 本）、sorry 0。drafts/A8/Stratification は削除 | **済**（ビルド・shared 監査 PASS） | — |
| A8-4 Thm 10.11・E3 の integral | a8-design §2.4・§3.3 | A8/IntegralDiscreteness（**11-13**：部品 G-A8-8〜11 は BS-W13 で本体（`Derived/{PerfectoidFilteredColimit,IntegralApproximation,IntegralClosureApproximation,IntegralClosureCompletion}`）、G-A8-6 は BS-W11、組み立ては drafts。BS-D2 停止点 3 済：`True` 0 件。T・T̂・A_λ の型、Cor 8.12 は S → T̂、G-A8-8 は一般の整代数への帰着でだけ） | 修復済み（W9-III-04〜06：Cor 8.12 は S → T̂ = completionRing T に、近似は T への写像を備えた filtered 系、D70）。紙 3・4・7 の局所的接続は W9 ○、6 と filtered 余極限の全接続は Codex 未 | G-A8-6・8・9、A5・A7 |
| A9-1 界面の組み立て・E3 の消去 | a9-design | A9/Assembly | 八欄の対応は W9 第 3 部続き 2 で ○ | A4〜A8 の全欄。Inputs の書き換えは中身の段階。**前提：E3 非依存の import 順（W9-III-08、CompletedTensor の分割は 2a 後に調整役）**（11-13：BS-W10 作業 A、cc67ea88e で解決済み） |
| A1-5 Thm 6.4 の多項式・mod p | a1-design §9 | A1/DeRhamComparisonPoly（BS-D4 停止点 3 済：`True` 0 件。`deRham_iso_rootAlgebra_modP` → A5 の `rootMap_modP_eq_deRham`、`prismaticCohomology_lci_universal` → A3 の特殊化） | 未（a1 §9.5） | E（黒箱を de Rham 形に、D68）、D（Lemma 4.20、A0-4）、A1-4 |

骨組みの規模（**11-05**）：drafts 51 本、約 12,900 行。結論が `True` の名前つき宣言は 4（Shared の × のみ：`totEInfinity_cohomologyRing`、Descendable の `*_two_of_rhom` 2、`isDescendableOver_complete`）。A0〜A9 には仮置きなし。本体に入ったもの：BS-W10 作業 A（`BhattScholze/Perfectoid/FiniteProduct`、cc67ea88e）・作業 B（Lemma 10.12、4019014a1）。以下は 11-03 時点の記録：51 本、約 12,100 行（結論が `True` の名前つき宣言 53、Codex 集計）。BS-D1（49）・BS-D2（83）・BS-D3（88）・BS-D4（64＋`Type u := sorry` 10）で A0〜A9 の仮置きを具体的な型にした（報告 `report-codex-d1/2/3/4.md`、D1-01〜03・D2-01〜02・D3-01〜07・D4-01〜06 は設計側で解決）。**A0〜A9 に結論が `True` の仮置きは残っていない。** 残り 53 は基盤側（**BS-D6 後は 4**：DerivedGeneral 0、Shared 4（× 理由つき：ホモトピー環 1・内部 Hom 2・Mod_R の完備テンソル 1）、Sheaves 0。drafts は 51 本、約 12,721 行。Shared 28：Descendable 16・CosimplicialEInfinity 5・EInfinityPowerOperation 4・Bockstein 2・DeRhamPolynomial 1；DerivedGeneral 14：CompletionFunctor 5・Truncation 5・ScalarRestriction 4；Sheaves 11：SpaceValued 6・CAlgValued 3・CechConerveLimit 1・GlobalSections 1）→ W2b 後の段 G（BS が M12a・M13、∞ が G3・G4・G6）。

## 2. 要確認の分類

### (A) 基盤の名前を探すだけ（11-03 に grep で確認。ビルドなし）

| 箇所 | 探すもの | 結果（11-03） |
| --- | --- | --- |
| Shared/CosimplicialCupProduct:80 | CommRingCat の余単体的対象 → ModuleCat の忘却（`forget₂`） | Mathlib `forget₂ CommRingCat RingCat`・`forget₂ CommRingCat AddCommGrpCat`（Algebra/Category/{Ring,Grp}/Basic）。余単体的対象は `Functor.comp`（whiskering）。A 加群構造は (B) の決定どおり基底 A の作用を別に付ける |
| Sheaves/GlobalSections:84 | 関手 ∞ 圏 `(ihom K).obj E` の頂点 ↔ 射 `K ⟶ E` | `Core/Equivalence.lean` `functorVertex`、逆向きを含む同値は `Core/EquivalencePath.lean` `functorVertexEquiv : (X ⟶ Y) ≃ ((ihom X).obj Y) _⦋0⦌` |
| Sheaves/GlobalSections:115 | `IsReflectiveSubcategory` から反射関手を取り出す形 | `F1B/Localization/Reflective.lean`：`IsReflectiveSubcategory X P := Nonempty (ReflectiveSubcategory X P)`。構造 `ReflectiveSubcategory` を `Classical.choice` で取り出して関手を使う |
| Sheaves/GlobalSections:138 | E の辺の可逆性の述語 | `FunctorIso`（Core.lean で export。F1・HomotopyLimits・Derived・Stable で使用） |
| Sheaves/SheafCondition:98 | `uliftFunctor` と join の可換性（`JoinCone.ulift`） | `JoinCone` は F1・F1B・Derived・Stable；`uliftFunctor` の比較は `Stable/UniverseVertexIso.lean`・`Stable/UniverseHorns.lean`・`ModelBridge/HA/UniverseLiftAnodyne.lean`。join との可換性そのものは未発見（なければ新規、S1 の中身で） |
| A0/PrismaticSite:237 | `uliftFunctor.obj (nerve (SmallModel C)) ⟶ nerve C` | `SmallModel`・`equivSmallModel` は Mathlib（EssentiallySmall）。比較射は未発見：新規（nerve の関手性と `uliftFunctor` の単位） |
| A0/PrismaticSite:256 | D(A) の `⊗^L A/d` | `HA/DerivedQuotientBaseChange.lean` `derivedTensorQuotientModuleIso`・`derivedTensorQuotientAlgebraIso`、`HA/DerivedQuotientTensorAugmentation.lean`。D(A) の ∞ 版は Derived/ のテンソル（2b 後の名前） |
| A0/PrismaticSite:267 | φ_A に沿うスカラー制限 D(A) → D(A) | **訂正（11-03、BS-D2 の質問）**：`Derived/ScalarRestrictionNerve.lean` の `dgNerveRestrictScalarsIso` は dg 圏の Hom の係数制限の同型で、D(T) → D(S) の関手ではない。∞ 関手 f_* は未発見（底変換 f^* は `Derived/BaseChange.lean` の `derivedInfinityBaseChange`）。基盤待ちの宣言 `derivedInfinityRestrictScalars` を `drafts/DerivedGeneral/ScalarRestriction.lean`（M13）に置いた |
| A0/PrismaticEnvelope:52 | Koszul 複体のホモロジー | HA の Koszul 群：`KoszulLinearDuality.lean`（`koszulLinearDualHomologyIso`）、`DerivedQuotientKoszul.lean`、`AlgebraKoszul*.lean`、`BoundedTermKoszulAcyclic.lean`。名前は 2b の改名表の後に確定 |
| A0/PrismaticEnvelope:156 | 完備テンソル | `BhattScholze/Perfectoidization/CompletedTensor.lean`（分割後は芯、`completed-tensor-split.md`）、`HA/DerivedCompletion/{CompletedBaseChangeH0Coefficient,AlgebraBaseChangeTensorUnit}.lean` |
| A0/CechAlexander:88、Shared/DeRhamPolynomial:125 | 一変数の導来 p 完備化 H⁰ | `completionRing`（`BhattScholze/Perfectoidization/Derived/Interface.lean`）、`PDCompletionH0 p d := PairCompletionH0 R (p) d`（`HA/DerivedCompletion/PDCompletion.lean:29`） |
| A1/HodgeTateComparison:106 | Frobenius に沿う `Module.Flat` の述べ方 | 用例：`HA/Tor.lean`、`HA/PerfectResidueTensorRegular.lean`、`BhattScholze/Delta/DividedPower/PrincipalDP.lean`。Frobenius に沿う形は `RestrictScalars` か `Algebra` インスタンスで（既存の Frobenius 平坦性の宣言は未発見、A1 の中身で） |

### (B) BS 側で決める設計の細部（決定：2026-11-02）

| 箇所 | 決定 |
| --- | --- |
| R の具体形（A0/CechAlexander:114・197、A1/HodgeTateMap:39） | R := `MvPolynomial (Fin r) (A ⧸ P.ideal)` の一変数 p 進完備化の H⁰（E3 の `completionRing` と同じ道具）。A0 の `cechAlexanderAffine` と A1 の `affineAlgebra` を同じ定義にする。一般の集合 T 上も同じ |
| `cechKernel`（A0/CechAlexander:88）と閉包（A0/PrismaticEnvelope:98） | J := ker(B → H⁰ の一変数導来 p 完備化 (B ⧸ J₀B))。`of_closure` はこの核と J₀B の envelope が一致すること |
| `regularShortExact` の係数環（Shared/CosimplicialBockstein:82） | 係数は基底 A（A 加群として）。R 線形性は別に付ける |
| η^1 の線形性（Shared/DeRhamPolynomial:110） | H^0 の P 加群構造を η^0 で入れ、η^1 は P 線形写像 Ω^1 → H^1（H^1 は H^0 加群）として述べる |
| `cohomology` の関手性（Shared/CosimplicialCupProduct:121） | 余単体的環の射 f : X ⟶ Y に対し `cohomologyMap f i : cohomology X i → cohomology Y i`（環の射、cup 積を保つ） |
| `cechShape` と `structurePresheafDerived` の型合わせ（A0/CechAlexander:160〜175） | `cechNerveData` を `PrismOverSmall` の側で作り（`equivSmallModel` で移送）、S3 を `PrismaticSite` 上の前層 `structurePresheafDerived` に適用する |
| κ 不変性の形（A0/PrismaticSite:272） | κ₀ ≤ κ ≤ κ′ の site の包含関手 ι と、ι に沿う前層の制限で `derivedGlobalSections` を比較する同型（頂点の等号は主張しない） |

### (C) ∞ 側の窓に依存（infinity-sheaves-design §4・§9。W2b の後、担当未定）

G3（D(A) presentable）、G4（Fun の presentable 性）、G6（局所置換の存在）、G8（X ⊗ M と Yoneda）、G9（Čech 脈体の実現または Bousfield–Kan）、
G10（Tot ＝ 全複体）、`isSheaf_toGrothendieck_iff`（生成系で十分）、`JoinCone.ulift`（宇宙）、S5・S7。BS 側は骨組みのまま待つ。

### (D) 論文の層の区切り 2b の後（HA/DerivedCompletion を読んでから）

A0-3b（Lemma 3.7(2) 一般形・(3)）、A0-3d（Cor 3.12 (a)〜(e)。有限段の Amitsur は新規）、A0-4（Tor 振幅・Lemma 4.22・4.20）、
G-A1-4（導来 Nakayama）、G-A1-5（完全忠実平坦の保存性）、G-A1-13（底変換の合成）。改名表は調整役から。

### (E) 結晶側の黒箱と arc 降下の引用（独立の作業単位。いつでも書ける）

A1-2（D^•、η、Lemma 2.36 の変数の場合）、A1-3（Lemma 5.4、pd 包の Čech 脈体 ≃ de Rham 複体、Cartier、Cor 5.5）。
結論は `hodgeTate_iso_polynomial_Zp` 一つ。BS と独立な部分（余単体的ホモトピー、pd-Poincaré、Cartier）は `drafts/Shared/` に。

## 3. 決定の所在

| 番号 | 内容 | 正本 |
| --- | --- | --- |
| U1・U3・U4 | Type u と κ、向き付き有界基底、完備化は導来完備化の H⁰ | infinity-sheaves-design §0・§5、ノート D5・D16 |
| β（U2） | RΓ は層化と Γ（γ 案は不採用） | infinity-sheaves-design §0 |
| D-S1 | Čech 層（hypersheaf との差は離散な層で消える） | infinity-sheaves-design §2・§2.1、ノート D17 |
| D-S2〜D-S5 | κ、D(A) 値→CAlg 値、左完全性は安定性で、1 圏の位相データ | infinity-sheaves-design §6 |
| D19〜D24 | 向き付き、Def 2.42 の離散化、Prop 3.13 の範囲、生成位相、Čech 余脈体は添字で、Lemma 4.21 不要 | a0-design §4・§6 |
| Tot 非正規化、Čech (b)、HA は 2b の後 | | a0-design §6 |
| D25〜D30 | Thm 5.2 β、微分形式、模型の環構造、捻りなし、一般の r、E を作らない | a1-design §5・§7 |
| 順序 | A1-1 → A1-4 → A1-2 → A1-3、結晶は最小限 | a1-design §6 |
| D31〜D35 | P_Σ、完備化不変性、gr が (∧^i L)^∧ の定義、Poly の添字、CAlg_A 値 | a2-design §4・§6 |
| D36〜D40 | Lemma 7.7(1) は特別な場合だけ、Δ^init 不要、BR30 閉じる、qrsp は余接複体で、Prop 7.10 の範囲 | a3-design §4・§7 |
| D41〜D44 | Def 8.2 は p 完備な S に、perfd の欄は (S^∧)_perfd、φ_A^{n*}、Lemma 8.4 は内部で要る、P⁰ は BS が骨組み | a4-design §4・§6 |
| D45 改訂、D68・D69 | Prop 8.5 は導来 p 完備な animated S（site は π_0 S）で系 4 を述べる（決定 6、11-02）；結晶の黒箱は仕様つきの de Rham 形一つ＋G-A1-17；Thm 6.4 の帰着は A_0 上で原典の経路 | a5-design §5・§7.1、a1-design §9.3・§9.4 |
| D45〜D52 | S は導来 p 完備な animated（D45 改訂、系 4 を含む）、位相の順序、κ と Type u の一致（余積は Perfd_{S/} の (T₁ ⊗̂_S T₂)_perfd を Lemma 4.8 で移す、W9-II-06）、D48 取り下げ（G-A5-17 = G-A2-10）、descendable は Mat16 の定義、de Rham 入力は A1-5、S̃ は ω 段、Cor 7.3 との一致 | a5-design §5・§7 |
| D63〜D67 | Thm 10.9 は連結性だけ原典 (1)(2) で、n = 1 は Perfd_{S/} = Perfd_{S_red/}、Lemma 10.12 は原典の形、Prop 10.4 は必要な同値、E3 は S^∧ 経由 | a8-design §5・§7 |
| D68〜D69 | 結晶の黒箱は de Rham 形一つ、Thm 6.4 の帰着は Prop 6.2 の経路 | a1-design §9.3・§9.4 |
| D60〜D62、D15 | Def 8.2 の定義域を原典（animated）に戻す、基底 R 固定、Cor 8.14 は離散 S、環版 Prop 8.13 は後で系に（BR31） | a7-design §4・§6 |
| D20 訂正 | Def 2.42 の平坦性はホモロジーの底変換同型（高次の消滅ではない。Codex W9-I-01 の反例 (Z_p,(p))） | a0-design §2.5・§4 |
| D53〜D59 | arc site は affine（affCompl_κ ⊃ affPerfd_κ）、有限族、Cor 8.11 は affine 版を記録、三つの引用は別々に `sorry`、S8、S′ × S/I は有限積の保存で戻す、BM18 は affine 版 | a6-design §5・§7・§9・§10 |
| **改訂（11-05 夜、ユーザー）** D68・D56・D59、BS17 | 終わりの条件は sorry 0。(1) D68 改訂：結晶の黒箱を関手同型から外し、使う側が要る対象ごとの HT の命題 `HodgeTateIsoStatement` を Čech–Alexander 模型の mod p で直接証明（Lemma 5.4・pd Poincaré・BdJ・Cartier）。未使用の `deRham_iso_polynomial_crystalline` は外す。D69 側の `deRham_iso_polynomial_universal` の貼り合わせの高次整合性を確かめる。(2) D56・D59 改訂：一般形の `arcSheaf_of_vSheaf_of_valuationSquares` は主経路から外し、G-A6-1 `cech_exact_of_arcCover_perfect` を F = O の場合の BM18 Prop 4.8 として 1 圏で直接（Rydh・hypercomplete 性は使わない。置き換えの二点は紙で確認）。(3) BS17 Thm 4.1 (i) `cech_exact_of_vCover_perfect` は原典どおり（Cor 2.14・Thm 2.9・Lemma 2.6・Rydh Thm 3.12・BST13 Lemma 3.9）。土台は K と共有の「スキーム論の土台」（計画 §1.5）。E3 の型は変えない | [citations-survey-2026-11-05.md](citations-survey-2026-11-05.md)、a9-design §3 |

## 3.1 調整役からの返答（2026-11-02、main 26f1f4d94）

- Shared 3 本の置き場所：cup 積・Bockstein は `HomologicalAlgebra/Cosimplicial/`、de Rham は `CommutativeAlgebra/DeRham/`（新設、HA の第一層＝一般論）。
  移すのは 2b の後。名前は論文の層に予約してもらう。それまで drafts/Shared/ のまま。
- 2b の改名表は `BhattScholze/` に加えて `HomologicalAlgebra/DerivedCompletion/` の分も回る（(D) の読解に使う）。
- Sheaves の骨組みで使っている基盤の名前は実在を確認済み（nerve・ihom は Mathlib）。形の確認は W2b 後の窓の判断のとき。F1B・F2 の改名は
  W2b・W2c の改名表で回る。
- A2 の設計（P_Σ・左 Kan 延長・CAlg_R の API を読む）は進めてよい。読むだけでビルドなし。
- （main 600e578d7、M13）DerivedGeneral 2 本の置き場所は `InfinityCategories/Derived/`（一般の t 構造の定義を切り出すなら Stable/）。時期は段 G、
  W2b の後。CompletionFunctor は 2b の改名表を受けてから。それまで drafts/DerivedGeneral/ のまま。
- （main 431c40741、M14）G-A4-1（P⁰）の置き場所は `EInfinity/PowerOperation/`（新設、BarrattEccles・Operad の隣。Barratt–Eccles の作用の型はそこで確認）。
  時期は A4 の中身を書く段階まで不要、担当（E2 レーンか BS か）はそのとき決める。BS 固有の骨組みは Perfectoidization/Derived/ の隣の仮置きでよい。
- （main 86acd98db、M15）G-A5-1（descendability）の置き場所は `EInfinity/Descendable/`（新設。CAlg と D(A) の両方を使う。EInfinity は Derived を import 済み）。
  E∞ を使わない thick ⊗-ideal・index・安定性の部分は Derived/ へ下ろしてよい。時期・担当は M14 と同じ（段 G、A5 の中身を書く段階で決める）。
- （main 7b8b96286、M12e）S8 の置き場所：(1)(5)(6) は `Sheaves/SpaceValued/`、(2)(3) は `Sheaves/Discrete/`、(4) の一般部分（HTT 5.1.5.6、el(F) 上の極限）は
  M12b と同じ `F2/`。前提に G13（𝒮 の presentable 性）と S4 の非安定版を追加。時期・担当は M12 と同じ。
- （同）Prop 8.10 の引用 3 件の `sorry` 定理は drafts/ の間は問題なし。`SerrePositivity/` に入れるときに `scripts/make_area_audits.py` の許可一覧の更新が要る
  （そのとき調整役に知らせる）。
- （11-02）論文の層の **2a**（CA の perfectoid 部分を BS へ、CLMST の整理、Perfectoidization* 12 本の Perfectoid/ への統合）が 11-05 の全ビルドに向けて開始。
  **2a の取り込みまで BhattScholze/・CLMST/ の Lean には手を入れない**（drafts/ はそのまま）。取り込み後に改名表（BhattScholze/・CLMST/・prop247_ の宣言名）が回る。
  **2b**（HA/DerivedCompletion）は 11-06 の見込みで、その改名表も回る。Codex レビュー W9 は読むだけなので影響なし。
- （main 26f9f7fc5）Lemma 10.12（A8-3）の置き場所は `CommutativeAlgebra/UniversalHomeomorphism/`（普遍同相の一般論）と `CommutativeAlgebra/EtaleStratification/`
  （層別の本体）。どちらも 2a の後に新規ファイルだけで入れ、論文の層へ名前を予約。独立した Codex の単位、担当は 2a の後。A8-1・A8-2・A8-4 の仮置きも問題なし。

**調整役へ依頼（2026-11-03、W9-III-08、未返答）**：`BhattScholze/Perfectoidization/CompletedTensor.lean` は `Derived/IntegralExistence` 経由で `Inputs/PerfectoidizationInterface` を
import し、有限直積 `isIntegralPerfectoid_finPi` が E3 を実際に使う。E3 を消す組み立て（Inputs の証明を Assembly に置換）で循環するので、Fontaine による完備テンソルの芯
（`integralPerfectoid_completedTensor_pure_and_h0` まで）を E3 非依存のモジュール（仮称 `CompletedTensorCore`）へ切り出し、`Almost/Lemma103` の依存をそこへ向け、有限直積は
直接証明に替えたい。2a が Perfectoidization* を Perfectoid/ へ統合するので、**2a に含めるか 2a 直後の最初の作業**にしてほしい（BS は 2a まで BS の Lean を触らない）。
詳細は a9-design §7。**仕様書 `completed-tensor-split.md`（11-03）**：移す節・差し替える定理・利用側 9 本・直接証明の筋・到達性の確認片を記した。
  **返答（11-03、coordination.md 588f589f3）**：2a には入れない。**2a 取り込み直後（11-05）に BS-W10 作業 A として BS の Codex で**行う。BhattScholze/ と利用側の import 行（CLMST 5 本は import 行だけ）、単体 `lake build`、全ビルドは 2b（11-06）に便乗。
- **基盤 66 宣言の分担（11-03 提案 → 同日返答、coordination.md 588f589f3、計画 M12 の行）**：提案どおり。**BS が M12a（S1〜S3・S8）と M13（DerivedGeneral）を書く**、∞ が G3・G4・G6（必要なら G8・G9）。
  時期は W2b 後の段 G、新規ファイルのみ。∞ への依頼は W2b 取り込み後に調整役が起こす。Sheaves 層の `layers.json` 登録は調整役。
- （同返答）段 1（Lemma 10.12 ほか）は BS の Codex で。Lemma 10.12 は `CA/UniversalHomeomorphism/`・`CA/EtaleStratification/` へ。2a の合図と改名表は 11-05、2b の改名表は 11-06。
- （11-03、調整役）**DG-W3 の取り込み**で DG のモジュールを import していた BhattScholze/ などの import 行が機械的に書き換わった（宣言は不変。対応表は
  `scripts/refactor/targets/dg-w3-merge-plan.json`）。2a まで BhattScholze/・CLMST/ の Lean に手を入れない方針はそのまま。BS 側の確認：drafts の `public import`
  67 本のうち本体に存在しないものは `F2.Presentable.Basic` 一本だけで、これは DG-W3 の影響ではなく当初の推測名（git 履歴に存在しない）。`F2.Presentable` に直した
  （Sheaves/SpaceValued）。DG の名前は drafts から直接は import していない。

## 4. 次の作業（提案）

1. A1-5 の決定（a1-design §9.4）の反映。その後は中身の段階へ：調整役と暦（W2b・2b の後）、(A) の名前探し、A1-2/A1-3 の黒箱の骨組み。
2. （済）A6（excision の欄）、A7（universal の欄）、A8（integral の欄）、A9（界面の組み立て）の設計書と骨組みは 11-02 に完了。
3. (E) の骨組み（A1-2・A1-3）。
4. (A) は中身を書く段階の最初に、(C)・(D) は時期を待つ。G-A4-1（P⁰）は `EInfinity/PowerOperation/`（M14）、担当は A4 の中身の段階で。
5. （11-03、W9-III-08）2a 後：CompletedTensor の E3 非依存の芯への分割と有限直積の直接証明（調整役と時期を合わせる）。中身の段階の `lake build` の前に import の到達性で E3 非依存と drafts/README の DAG を確認する。
6. （11-03）W9 完了。中身の段階の順序：2a の取り込み → 5 → 2a・2b の改名表の反映（drafts の import 行） → (A) の名前探し（済、§2 (A)） → 骨組みを `SerrePositivity/` へ（drafts/README の DAG の順、単体 `lake build`）。
7. **（11-03 決定、ユーザー「全て ok」）段取り**：
   - 段 0（今〜2a、ビルドなし）：`completed-tensor-split.md`（済）、(A) の名前探し（済）、BS-W10 の指示書（`bhatt-scholze-codex-w10.md`、済。基準コミットは 2a 後に記入）。
     追加（11-03 午後）：G-A6-12 の骨組み `drafts/A6/PerfectoidFiniteProduct.lean`（直積・Fin r・有限族、ModP/Perfection/Witt の直積の同型と θ の両立）、
     `drafts/A5/RootAdjunction.lean` の主張を具体的な型に（延長性・完備性・濃度・関手性、`polyAlgebra`・`polyRootAlgebra` の perfectoid 性、`rootCover`）、
     `ArcSite` の cover-dense を Mathlib の `Functor.IsCoverDense` の型に、BS-W11 の下書き（`bhatt-scholze-codex-w11.md`：段 1 ③④）。
     11-03 夕（ユーザー決定）：残りの主張の具体化（A6/ArcSite・ArcSheafProperty、A8/Stratification、A0 の三本）は Codex の下書き作業 **BS-D1**（`bhatt-scholze-codex-d1.md`、
     ビルドなし、drafts と報告だけ）、ノート第 4・7 章の W9 との照合は BS 側で実施（済：04-site の方針の追記と Rem 4.6・D16 の行、07-semiperfectoid の Not 7.1・Lemma 7.7・Prop 7.10・要点）。
   - 段 1（2a 後、基盤を待たない古典的単位。担当は BS の Codex、こちらは検収。調整役了承 11-03）：① CompletedTensor 分割＋G-A6-12（**2a 直後 11-05、BS-W10 作業 A**。全ビルドは 2b に便乗）→ ② Lemma 10.12（A8-3）→
     ③ A5/RootAdjunction・G-A6-11（R₀）・G-A6-3/6（付値環）・G-A8-6（11-13：BS-W11 で済）・1c の初等補題 → ④ A6/ArcSite の 1 圏部分 → ⑤ A0 の site の定義と A0-3c。BS-W10 は ①②、W11 以降に ③〜⑤。
   - 段 2（W2b・段 G 後）：∞ 基盤 S1〜S8・DerivedGeneral・Shared → A2 → A4〜A7 の中身 → A5 の Prop 8.5。
   - 段 3：A8-4、A9 の組み立て、Inputs の証明の置換、監査の許可一覧（恒久 3＋暫定 2）。
   - 基盤 66 の分担（調整役了承 11-03、§3.1）：BS が M12a（S1〜S3・S8）と M13（DerivedGeneral）を書く、∞ が G3・G4・G6（必要なら G8・G9）。W2b 後の段 G、新規ファイルのみ。段 2 の BS 側の指示書（BS-W12 以降の見込み）はそのとき。

8. （11-03 夜、ユーザー「それで進めて」）2a までの追加作業：(a) **基盤の入口表** `foundation-entry-points.md`（基盤側 53 件の「使う側・担当・D5 での形」、A 側の要確認 → 入口、∞ レーンへの依頼案 §4、段 2 の点検表 §5）。
   見つかった穴：空間の ∞ 圏 𝒮 の名前がない（G13 と一緒に ∞ へ。**D5-07 で訂正：F1 に `SpaceInfinity` が既にあり、残るのは presentable 性と離散埋め込みだけ**）、導来テンソル ⊗^L の ∞ 関手がない（必須は M15 だけ）、S4・S5（層化の存在・完全性）の担当が分担に入っていない。調整役の回答（11-03、coordination.md 8ef332d45）：𝒮・G13 は ∞（名前の候補 `SpaceInfinity`、`IsPresentable 𝒮` は F2/）、⊗^L は ∞（β5 の一部、Derived/、M13 には含めない）、**S4・S5 は BS**（G4・G6・G8・G7 を ∞ が供給）。G12 と Core の小補題も ∞ の依頼に入れる。依頼書は W2b 取り込み後に調整役が起こす。BS-D5 の開始は了承。BS-D5 完了と依頼 7 の縮小（残り：離散埋め込みと 0 切り捨ての公開名の照合）は計画 M12 の行・coordination.md に反映済み（main 90def3697）。
   (b) **BS-D5**（`bhatt-scholze-codex-d5.md`、Codex、ビルドなし）：基盤側 53 件のうち型にできる 48 件程度を型に（×：`totEInfinity_cohomologyRing`、Descendable の RHom・完備版・`tensor` 欄）。停止点は DerivedGeneral → Shared → Sheaves。**停止点 1（DerivedGeneral）済・検収済み（da51e50f3、11-03）**：14 件、新設 `completeAt`・`completionReflection s`・`completion s`・CAlg 版・`completedBaseChange f s`・`truncationLE_step`・`discreteModuleEmbedding`・`cohomologyLayer`・`tStructure_{orthogonal,shift,decomposition}`・`cAlgH0Ring`・`cAlgRestrictScalars_h0_base`。残り 39（Shared 28・Sheaves 11）。**停止点 2（Shared）済・検収済み（161f826ee、11-03）**：23 件、新設 `totEInfinityFunctor`（`totEInfinity` は abbrev）・`totEInfinityCone`・`cohomologyEquivModuleHomology`・`cupBockstein`・`homotopyZeroRingEquiv`・`homotopyMap`・`powerOperationZero_primeField`・`AmitsurData`・`isDescendableOver_tensorMaps` ほか。× 5 件（`totEInfinity_cohomologyRing`、`*_two_of_rhom` 2、`*_complete` 2）＋`IsThickTensorIdeal.tensor` 欄は理由つきで残す。残り 16（Shared 5・Sheaves 11）。**停止点 3（Sheaves）済・検収済み、BS-D5 終了（bd0d4f14d、11-03）**：11 件＋`derivedGlobalSections_of_le` の ∃ の中身、新設 `PreservesFiniteProductsOnSite`・`isSheaf_extensive_iff_preservesFiniteProducts`（`FinitaryExtensive`）・`isSheaf_sup_iff`・`sheafificationFunctor`・`PresheafLarge`・`cechShapeLarge`・`exists_limitCone_of_cech_large`・`discretePresheaf`・`Is0Truncated`・`weightedSections` ほか。`space_isPresentable`（F2）が既にあり S8-1 の仮定を満たす。**BS-D5 合計 53 → 48 具体化、残り 5（Shared、× 理由つき）**。
   (c) ノート第 4・5・7・8・10 章に BS-D1〜D4 の決定と A1・A3・A6 の骨組みの宣言名を反映（第 5 章に「原典との差の評価」D68・D69・D27・D20 を追加）。
   (d) **∞ W2b の取り込み（3e27dda00、11-03）を確認**：drafts の変更は Sheaves/GlobalSections の import 1 行だけで、衝突解決（BS の追加行＋書き換え）は正しい。別に、11-02 の W2a 系コミット（d12e85d0e・9c38c984e・4d02ee532）で Core へ下りた 6 モジュールへの旧名 import が、11-03 の BS-D2・D3-02・D5 で 10 ファイル 12 行入っていた（書いた時点で既に古く、機械書き換えの対象外）。`Core.*` に直し、drafts の全 import の解決を確認（drafts/README の基準コミット表）。教訓：Codex の指示書に「import の実在を `ls` で確かめる」を加える。2a の取り込みと改名表は **11-04** 見込み（11-05 から前倒し）。調整役了解（11-03）：取り込み後に書かれた旧名は機械書き換えの対象外なので、**drafts は移動後の名前で書く運用**（Codex 指示書の規則に「import の実在を確かめる」を追加）。2a の改名表は **296 件**、2b は **11-05** 見込み。

9. （11-04）**段 G 停止点 1 への追従**（IF-G1 §4、main 7401c3588）：G4・G6 は既存名で済む（`functor_isPresentable`、`exists_bousfieldLocalEquivalenceReplacement`／`bousfield_isReflectiveSubcategory`）。⊗^L は `tensorWith M`（`Derived/Tensor/`、供給予定）、G13 は `discreteSpaceInclusion`・`Is0TruncatedSpace`（F1、供給予定）。BS 側の調整は **BS-D6**（`bhatt-scholze-codex-d6.md`、Codex、ビルドなし、停止点一つ）：Descendable の `tensor` 欄と `IsDescendable` の本体・離散底の完備版、S4 を `sheafification_of_generatingEdges`＋`exists_sheafGeneratingEdges`（G8 待ち）に二段化、S8 の `Is0Truncated` の点ごとの接続。供給予定の名前は `-- 要確認（IF-G1）` の仮名で使う。調整役了解（11-04）：G8 の「BS が要る形」は G7・Core・G13・⊗^L・G3 の後で**数日先**、供給名が F1/・Derived/Tensor/ に入ったら連絡が来る（そのとき drafts の仮名を実名に追従）。**BS-D6 済・検収済み（2074a8d9e、11-04）**：Descendable の `tensor` 欄・`IsDescendable` の本体・`IsThickCompleteTensorIdeal`・`IsDescendableComplete`・`isDescendable_complete`；S4 は `sheafification_of_generatingEdges`（既存の `functor_isPresentable`＋`bousfield_isReflectiveSubcategory` で証明済みの形）＋`exists_sheafGeneratingEdges`（G8 待ちの sorry）、空間値・CAlg 値も同じ二補題；S8 は `discretePresheaf_vertex`・`discretePresheafInclusion_edge`・`is0Truncated_iff_pointwise`。残る `True` は 4（Descendable の `*_two_of_rhom` 2・`isDescendableOver_complete`、`totEInfinity_cohomologyRing`）。∞ への要望（報告 §照合）：`discreteSpaceInclusion` は完全忠実性だけでなく、頂点が `setsToKan` の離散 Kan 複体に、辺が Kan 値図式の辺の評価に**厳密に等しい**計算式が要る；`Is0TruncatedSpace` は離散埋め込みの本質像であること。調整役了解（11-04）：この要望は IF-G1 §5 に回された（頂点・辺の計算式は `rfl` で、本質像の定義、`completion` と合成可能な自己関手）。G13 の仕様の確定（11-04）：`discreteSpaceInclusion` 自身の頂点・辺は `rfl`、前層を評価した `discretePresheaf_vertex`・`discretePresheafInclusion_edge` は ∞ が**定理**として供給。drafts を確認：二式はもともと命題の等式（定理と部分型の性質）として置かれ、`rfl`・`change`・`show` で定義的等号に頼る箇所はない。辺の式は `.edge`（一単体）どうしの等号なので端点の輸送も要らず、`rw`・`simp` で使える。条件は一つ：供給される定理が drafts と同じ構成 `kanDiagramCoherentNerve (P ⋙ setsToKan)` について述べられること（`setsToKan` を F1 に移すか、∞ 側の構成に drafts を合わせる）。調整役回答（11-04）：∞ 側が `setsToKan` を F1 の `discreteSpaceInclusion` の隣に置き（drafts の定義を写す）、二つの定理は `kanDiagramCoherentNerve (P ⋙ setsToKan)` について述べる。**F1 に入った連絡が来たら**、drafts の Sheaves/SpaceValued の `setsToKan` を削除して ∞ 側の名前に付け替え、仮名 `discreteSpaceInclusion`・`Is0TruncatedSpace` と二式の `sorry` も実名・供給定理に置き換える（tensorWith も同じ時に）。

10. （11-04）**2a 取り込み（590c4eff7）**：BhattScholze/・CLMST/ の編集再開。drafts の import は旧 `CommutativeAlgebra.IntegralPerfectoid`（削除、宣言は `CommutativeAlgebra/Perfectoid/Defs`）7 行と `CommutativeAlgebra.Koszul`（→ `Koszul.Basic`）3 行を追従し、全 import の解決を確認。宣言の改名 312 件のうち drafts に当たるのは `CLMST.perfectoidizationCone` → `BhattScholze.perfectoidizationCone` だけで、drafts の同名は別名前空間（`…Perfectoidization.Derived`）の独自定義なので変更不要。BS-W10 の基準を 590c4eff7 以降に、`completed-tensor-split.md` §0 に 2a 後の利用側（有限直積は 3 本、CLMST 1 本）を追記。作業 A が main に入ったら調整役へ知らせる（2b の全ビルドの前に取り込む）。
   - BS-W10 停止点 A-1 検収（11-04、報告 dc9d5120f、Lean は worktree `codex/bs-w10-a` に未コミット）：芯は CompletedTensor に残し（前半 5 節は文字列一致）、有限直積は `BhattScholze/Perfectoid/FiniteProduct.lean`、利用側 3 本と CLMST ConstantRank は import 1 行ずつ。E3 への到達は drafts 111 起点で `[]`。`isIntegralPerfectoid_finPi` は名前・引数順を保ち型検査済み、直接証明の sorry 10（直積の完備性・mod p・Perfection・Witt・PreTilt の同型、θ の両立、核の主性、二項・Fin r の perfectoid 性）。A-2 で埋めて直接 importer のビルド。
   - **BS-W10 作業 A 完了・main に取り込み（cc67ea88e、実装 fae7c9ca3、報告 0ce6df07b、11-04）**：sorry 0、`isIntegralPerfectoid_finPi` は空積を含めて E3 非依存の直接証明。CompletedTensor・FiniteProduct・drafts 111 起点のいずれからも E3 に到達しない（W9-III-08 の条件を満たし、A9 の前提が一つ外れた）。単体ビルド 11 本・126 秒、監査は BS が import と登録だけ・CLMST 差分なし。drafts/A6/PerfectoidFiniteProduct は削除。調整役へ通知（2b の全ビルドの前に取り込み済み）。次は作業 B（Lemma 10.12）。
   - **BS-W10 作業 B 停止点 B-1 検収（11-04、9a4437e34・報告 783d95509、ブランチ codex/bs-w10-b）**：`CommutativeAlgebra/UniversalHomeomorphism/Basic`（普遍同相＝整・Spec 全射・Spec 単射・剰余体の純非分離、標数 p の判定は `RingHom.ker f ≤ nilradical A`（nil、BS-D1）と元ごとの p 冪）と `CommutativeAlgebra/EtaleStratification/Stratification`（Lemma 10.12 の三結論：g が単位イデアル、各層の射が有限エタール∘普遍同相で後者は p 反転で全単射、各層で p は零か単元。層は (R/I)_red[1/g_i] → (S ⊗ …)_red、I を先に延長してから根基）。原典と違う定義・仮定なし、定義の穴 0、定理の sorry 11、単体ビルド 2 本 11 秒。drafts/A8/Stratification は削除。**調整役の条件**：sorry 0 になるまで main に入れない（CA の監査が sorry を拒否）。worktree が /tmp にあるので、こまめにブランチへコミット。
     取り込みの手順（調整役、11-04）：作業 B が sorry 0 になったら**取り込む前に調整役へ知らせる**（CA の新ディレクトリなので、調整役が監査の再生成と論文の層の B4 との衝突を確認してから main に入れる）。
   - 調整役（11-04）：作業 A の取り込みを確認し 2b の全ビルドを合図。2b が main に入ったら改名表（BhattScholze・HA/DerivedCompletion、**319 件**）が回る → drafts の import・宣言名を追従。段 1 は単体ビルドで進めてよい（2b の全ビルド中は鍵が空くまで待つ）。
   - **2b 取り込み（08a2997fd、11-04）**：drafts の import 5 行を追従（`DerivedCompletion.{Basic → ModuleComplete.Basic, CompletionH0Comparison → BoundedAboveCompletion, FinitePresentationComplete → ModuleComplete.Presentation, PairKoszulStage → Pair.Koszul, PrincipalKoszulRing → Principal.KoszulModel}`）、全 import の解決を確認。宣言の改名 23 件（削除 13）は drafts に当たらない。a3・a8 の設計書の旧パス 2 箇所も直した。BS-W10 作業 B は新規ディレクトリのみで import の影響なし。
   - **調整役の依頼（11-04、急がない）**：論文の層の段階 3（B4：Pair を Principal の反復に定義し直す）のため、BS で PairCompletionH0 を Koszul の H⁰ として開いて使う箇所を API 経由に。棚卸し：`unfold`・`simp [PairCompletionH0]` などの明示的な展開は 0。定義的等号に頼る箇所は **4 ファイル 8 箇所**で、どれも `koszulCompletionH0Unit R (pairKoszulCoordinates R (p : R) d) x` を PairCompletionH0（＝PDCompletionH0）の元として使う形：`Andre/Envelope/RootSource`（`exists_iteratedPDH0LinearEquiv`・`iteratedPDH0LinearEquiv_unit`、3）、`Semiperfectoid/RootEnvelope/RawCompletion`（3）、`Andre/Envelope/MonicSource`（1）、`Andre/PowerRootEnvelope/Unconditional/Source`（1）。他の利用（`pairCompletionCommRing`・`pairCompletionAlgebra`・`pairCompletionUnitRingHom`・`pairCompletionIteratedEquiv`・`pairCompletionH0_isModuleComplete_*`・`pairCompletion_algebraMap`・`pdCompletionUnit`）は既に API。drafts は API だけ。提案：HA 側に線形の単位 `pairCompletionH0Unit R f d : R →ₗ[R] PairCompletionH0 R f d`（今は `koszulCompletionH0Unit R (pairKoszulCoordinates R f d)` の abbrev）を置き、`pairCompletionH0_isCompleteModuleReflection` をこの名前で述べ直してもらう → BS の 8 箇所をその名前に置き換える（今は定義的に同じなので証明は不変、B4 で HA が定義を替えても BS は触らない）。
   - **段 G 第一区切り完了（11-04、math/g1、sorry・公理なし）**：G7・Core・G13・⊗ᴸ・G3・G8。`setsToKan`・`discreteSpaceInclusion` の頂点・辺は rfl、前層の比較定理は `kanDiagramCoherentNerve (P ⋙ setsToKan)` について、G8 は `sectionsOfDiagram` の指定極限錐に対する同値まで。**W2c の取り込みの後に main へ入る → そのとき drafts の仮名を本名に**（`setsToKan` の drafts 版を削除、`discreteSpaceInclusion`・`Is0TruncatedSpace`・`tensorWith` の要確認を外す、`discretePresheaf_vertex`・`discretePresheafInclusion_edge` の sorry を供給定理に、`exists_sheafGeneratingEdges` を G8 で）。
     質問への回答（11-04）：G8 の X についての自然性は**要る**（IF-G2 へ）。形：集合値前層の任意の射 φ : X ⟶ Y について、Map(Y ⋙ ⊗M, F) → Map(X ⋙ ⊗M, F) と Map(M, Γ(Y, F)) → Map(M, Γ(X, F))（`sectionsOf_map φ`）が G8 の同値を通して**空間のホモトピー圏で可換**。S4（篩の包含 S ↪ h_U で「W 局所 ⇔ 層」）と S8-5（任意の局所同値）で使う。合成に関する高次の整合性は不要。
   - **BS-W10 作業 B 停止点 B-2 検収（11-04、実装 b1bc9d7cb、報告 8220cbc47・0552427a2）**：`UniversalHomeomorphism/{Basic, PowerClosure}` の sorry 0・公理なし、B-1 で承認した主張は文字列で不変（底変換・合成・nil 核の全射・標数 p の判定の両方向・完全→被約の全単射・純非分離体拡大）。単体ビルド Basic 8.3 秒・PowerClosure 3.9 秒・Stratification 12.4 秒（B-3 の sorry 4 は残る）。次は B-3。
   - **11-04 16:00〜（19:30〜20:30 終了見込み）**：∞ W2c の下流ビルドと verify。この間は BS の小さなビルドも停止（編集は可）。終了後の順序：G1 の取り込み → B4 の全ビルド → BS-W10 作業 B の取り込み。
   - **B4 取り込み（3de4d3ba9、11-04 夜）**：Pair は Principal の反復で定義し直された（`PairCompletionH0`・`pairCompletionH0Unit` は API の後で irreducible）。BS の heartbeat 引き上げ 2 件（Perfectoidization 7c4e56d1b・PerfectionFaithful 23152a62c）は全ビルドで通過（102 秒・130 秒）。`pdCompletionUnit_apply` の右辺は `pairCompletionH0Unit`（RawCompletion が使う、BS 側も通過）。drafts の全 import は解決のまま。
   - **IF-G1 第一区切り取り込み（7bda72c3c、11-04 夜）**：drafts の仮名を本名に替えた（入口表 §6）。drafts の全 import は解決。残る sorry の理由を更新：`is0Truncated_iff_pointwise`（BS 側の証明）、`exists_sheafGeneratingEdges`（G8 の X についての自然性、IF-G2）、`kanDiscretePresheafInclusion`（BS 側の構成）。
     **IF-G2 停止点 1 の型（11-05、調整役承認）**：切断の辺 `SetWeight.sectionsMap φ F hX hY`（Γ(Y) → Γ(X)）、自然性 `SetWeight.tensorSpaceFunctor_setWeightHom_naturality`（ホモトピー圏の四角形）、篩の包含への特殊化。drafts の `sectionsOf_map` と照合：図式は同じ式（drafts の `sectionsOfDiagram` ＝ `SetWeight.diagram`、元の圏の射影は同一定数。drafts の非推奨の別名 `CategoryOfElements.π` を `Functor.Elements.π` に直した）、頂点は drafts の選んだ極限錐の頂点なので、`hX`・`hY` が錐（または HasLimit）なら `sectionsOf_map` の本体にそのまま使える。
       調整役（11-05）：`hX`・`hY` は指定した錐と極限性（`c : JoinCone`、`hc : IsLimitCone c`）の形、篩の包含への特殊化は `exists_sheafGeneratingEdges` で使う形で G2 に依頼済み。G2 が入ったら `sectionsOf_map` の本体と S4 の生成辺を閉じる。
       **S4 の型付け（11-05、BS、drafts/Sheaves/SheafGenerators.lean 新設）**：篩の圏の反対 ≌ `S.functor` の元の圏（射影は `sieveDiagram S`）、Γ(S, F) ＝ 制限図式の極限（`sectionsOf_sieve`）、Γ(h_U, F) → Γ(S, F) が可逆 ⇔ `restrictionCone F S` が極限錐（`isLimit_restrictionCone_iff_sectionsMap`）、層 ⇔ 全被覆篩でそれが可逆、検出族 `IsDetectingFamily`（F2 の生成系の名前は要確認）と生成辺 `sheafGeneratingEdges`（S ⊗ M_i → h_U ⊗ M_i）、「W 局所 ⇔ 層」は G8 の自然な別版待ちの sorry 一つに集約。`exists_sheafGeneratingEdges`・`sheafification_exists`・`sheafification_exists_spaces` はこのファイルへ移した（Γ を使うため SpaceValued の後）。
   - **BS-W10 作業 B 完了・main 取り込み済み（調整役、4019014a1、11-05 08:53）**：Lemma 10.12（A8-3）。`CommutativeAlgebra/UniversalHomeomorphism/`（6 本）と `CommutativeAlgebra/EtaleStratification/`（30 本）、計 36 モジュール・約 4,650 行、sorry・axiom・admit 0。単体ビルド 36 本すべて成功（160 秒）、shared 監査 641 → 677 モジュール・エラーなし。drafts/A8/Stratification は削除済み。**BS-W10 終了**。調整役の確認（11-05）：main で新規 36 モジュール・ルートのビルドと shared 監査がすべて PASS。
   - **BS-W11 の開始（調整役、11-05）**：今夜の F-2（名前空間の付け替え、4〜6 時間＋verify）の後、明朝 11-06 に main から worktree を切って開始（`LEAN_Projects.nosync/` の下に一つ）。F-2 の取り込みと改名表の配布の連絡を待ち、まず drafts と W11 の import・名前を追従。その後しばらく全ビルドなし、単体ビルドは coordination.md §2-4a の規則だけ。
     **変更（11-05）**：F-2 は前倒しで開始（夕方まで）。その間 BS のビルドは控える。BS-W11 は F-2 の取り込み後に worktree を切って開始（日付ではなく取り込みの連絡が合図）。改名表はそのとき回る。worktree /private/tmp/SerrePositivity-bs-w10 は削除（ブランチは残す）。
   - **S4 の篩比較を main に取り込み（6d72051be、11-05）**：drafts と報告のみ、BS ファイルだけを確認して merge。worktree /private/tmp/SerrePositivity-bs-s4 は削除。BS の worktree は 0 本。
       **S4 の篩比較（Codex、ブランチ `codex/bs-s4-sieve-comparison`、worktree /private/tmp/SerrePositivity-bs-s4、報告 `report-codex-s4-sieve.md`）**：drafts のみ（ビルドなし）。`drafts/Sheaves/SetSections.lean` を新設して切断（`sectionsOf` 系）を SpaceValued から移し（S4 が S8 に依存する循環を避ける）、`sectionsOf_map` を G2 の指定錐版 `sectionsMap` に、篩の元の圏の同値・`sectionsOf_sieve`・`restrictionCone` との接続を本文つきで記述（sorry 0、未ビルド）。main の SheafGenerators にマージ済み（`ec2957fa8`）、残る sorry は `exists_detectingFamily`（G14）と `isLocalObject_sheafGeneratingEdges_iff`（G2 の篩包含版自然性）。**取り込み**：drafts だけなので次の区切りで main に入れ、worktree を消す。
       worktree の規則（11-05、調整役の提案）：BS の Codex の worktree は一度に一つ、置き場所は LEAN_Projects.nosync/ の下（/tmp は再起動で消える）。bs-w10 は作業 B の取り込み後に消す。W10・W11 の指示書に追記済み。
       S3 の経路（Quillen A、G9 の三つの小補題、G10 は応用でだけ要る）は IF-G2 §4 に反映（main b715120a5）。
       `exists_detectingFamily` の型（`IsDetectingFamily`：ホモトピー圏の射の可逆性を `PinchedInterval.postcompose (M i)` の QCat 同値で検出、添字は `Type u`）を G2 に渡した（IF-G2 §3、main 401c32777）。G14 として既存の `exists_limitDetectingPresheafModel` から導く。F-2 の後に G2 が再開。
       G2 から（11-05）：G1 の `tensorSpaceFunctor_setWeightHom` は内部の比較が指定した同型と対応する保証がなく、自然性が導けない。G1 の定義は変えず、自然な比較で作った**同じ形の別版**を新規ファイルに置き、自然性は別版について述べる。BS の S4・S8-5 で G8 と自然性を使う箇所（drafts では `exists_sheafGeneratingEdges` の注記と `sectionsOf_map` の docstring）は、別版の名前に差し替える（名前は G2 の報告で）。
     **S3 の経路を決定（11-04 夜、BS）**：(c) Quillen A による余終性（効果的エピの実現・Bousfield–Kan は採らない）。BS が comma の同一視と縮約（1 圏）を書き、∞ に依頼するのは left 側の nerve の Quillen A・ulift での left cofinal の保存・縮約の逆向き版の 3 つ（入口表 §4.1 に型）。G10 は S3 に不要だが A0・Shared Tot・A1・A6 で要る（型も §4.1）。
     調整役（11-04 夜）：IF-G2 は 11-05 に、G8 の X についての自然性を最初の項目にして出す。入ったら S4 の `exists_sheafGeneratingEdges` を閉じる。
   - **∞ W2c 取り込み（c2979a262、11-04 夜）**：drafts の全 import は解決したまま（W2c は drafts に触れていない）。BS-W10 作業 B のビルド再開。G1 第一区切りは G1 レーンが main を取り込んで衝突を解いた後に main へ → そのとき仮名を本名に。
   - 調整役（11-04 午後）：BS-W10 作業 B の小さなビルド（CA の新規ファイルだけ）を再開してよい。鍵は W2c の round の合間に空く。**W2c の下流と verify（夕方〜夜）の間は止める**（調整役が知らせる）。
     調整役（11-04、IF-G1 §6、main 4dceee881）：IF-G2 の最初の項目（G12 より前）に。G1 第一区切りが main に入った後に出す。
     調整役（11-04）：論文の層に依頼済み（abbrev で置き、反射の補題をその名前で述べ直す）。main に入った連絡が来たら、8 箇所を置き換えて 4 ファイルと importer を単体ビルド（作業 B の合間）。
     **済（11-04、f654244bb）**：8 箇所を `pairCompletionH0Unit` に置き換え、4 モジュールの単体ビルドが通った（4,118 ジョブ）。調整役確認済み、論文の層は B4 に着手（全ビルドは ∞ W2c の後）。

## 5. Codex レビュー W9 の指摘と扱い（2026-11-02）

正本：`review-codex-w9.md`。指示書：`bhatt-scholze-codex-w9.md`。

| 指摘 | 重さ | 扱い |
| --- | --- | --- |
| W9-I-01 D20 の「高次の消滅」は偽（基底 (Z_p,(p)) の H₁ = F_p） | 致命 | **訂正済み**（a0-design §2.5・§4、drafts/A0/PrismaticEnvelope の `IsCompletelyRegularRel`）：HA 7.2.2.10 の平坦性（H₀ 平坦＋全次数の底変換同型）。変数の場合は満たす。下流は不変 |
| W9-I-02 `cechShape` の始域 | 要修正 | 訂正済み（持ち上げた N(Δ)） |
| W9-I-03 `derivedGlobalSections_of_le` の頂点の等号 | 要修正 | 訂正済み（可逆な辺で） |
| W9-I-04 S3 の宇宙（E3 の添字圏は大きい） | 要修正 | 記録（infinity-sheaves-design §12、骨組みに注記）。中身の段階で大きい添字圏の版を足す |
| W9-I-05 CAlg 値の層化と U の両立 | 要確認 | `forget_sheafify` を別の主張として置いた。S4 の非安定版（M12e の前提）の一部 |
| W9-I-06 `True` の置き場・A 代数構造 | 要修正 | `ringPresheafToCAlg` の入力を A 代数値関手に。`of_closure`・`prismaticEnvelope_baseChange_of_variables` は主張を文で追記。残りの `True` は中身の段階で型にする（drafts/README の規約） |
| W9-I-07 Γ の説明 | 軽微 | 訂正済み |
| W9-I-08 ノート・状態表の不整合 | 要修正 | 訂正済み（05 の Thm 6.4 行、index と 07 の BR30、本表 §4 の 2） |
| W9-I-09 変数変換後の対の等式に閉包が落ちている | 要修正 | 訂正済み（a0-design §5.1 の 2：(d, Z)^−、`of_closure` で結ぶ、A/d = 0 は別扱い） |
| W9-I-10 `flatTopology` の篩の置き場（op X）、refine の被覆先 | 要修正 | 訂正済み（drafts/A0/PrismaticSite） |
| W9-I-11 κ の許容条件（κ^{ℵ₀} = κ） | 要確認 | `IsAdmissibleCutoff` を追加し `flatTopology_refine` の仮定に（drafts/A0/PrismaticSite）。a0-design §2.7 は中身の段階で追従 |
| W9-I-12 `HasEnvelopes` に濃度の条件がない | 要確認 | `HasEnvelopes` に濃度 ≤ cutoff を追加（多項式 R では模型との一意同型で供給） |
| W9-I-13 PD Čech 脈体 D_0^• 自体を切断つきとする行の証明は誤り（H¹(D_0^•/p) ≠ 0） | 致命 | **訂正済み**（a1-design §3 の 6：j ≥ 1 の行 Ω^j_{D_0^•} の収縮 G-A1-14（Bhatt–de Jong Lemma 2.15–2.17）、j = 0 の行は収縮しない。retraction による (ii) の比較も撤回） |
| W9-I-14 pd 微分の明示 | 要修正 | 訂正済み（G-A1-7 を pd 微分加群・pd de Rham 複体に） |
| W9-I-15 D69：保存性だけでは比較射が作れない | 要確認 | **訂正済み**（a1-design §9.1・§9.3：原典 Thm 6.4 の ψ・W(A_0/d_0) の経路を A_0 上で行い（p ねじれなしは A_0 で成立）、完全 prism へ底変換。D69 の決定は差し替えた案で再提示） |
| W9-I-16 Lemma 5.4 の無限変数 | 要修正 | G-A1-15（filtered 余極限）を追加 |
| W9-I-17 a1-design 前半の Thm 6.4「不要」 | 軽微 | 訂正済み（§0・§6） |
| W9-I-18 δ 座標つき D^• に列の Poincaré 議論を直接当てられない（t^p が H⁰ に残る） | 致命 | **訂正済み**（a1-design §3 の 6 (ii)：追加座標の Čech 因子 E^• = Q^{⊗(•+1)} の収縮で D_0^• → D^• が擬同型、G-A1-16） |
| W9-I-19 J つきの比較は Z_p の黒箱と Lemma 4.20 だけでは出ない | 要確認 | 反映済み（G-A1-17 を A1-3 の独立補題に。黒箱は Z_p のまま一つ） |
| W9-I-20 D69 の最後の W → A_0/d_0 の底変換 | 要修正 | 訂正済み（a1-design §9.1 の 2 に係数の列を明記） |
| W9-I-21 Bockstein の β² = 0 の説明、π∘ι = 0、係数環 | 要修正 | 訂正済み（drafts/Shared/CosimplicialBockstein） |
| W9-I-22 de Rham の d は P^∧ 線形でない | 要修正 | 訂正済み（drafts/Shared/DeRhamPolynomial） |
| W9-I-23 `hodgeTate_iso`・`prismaticCohomology_baseChange'` の二重宣言 | 要修正 | 訂正済み（HodgeTateMap 側を述語に） |
| W9-I-24 CAlg の錐の指定（正規化模型、AW との比較） | 要確認 | 反映済み（drafts/Shared/CosimplicialEInfinity の方針） |
| W9-I-25 r = 1 → Lemma 4.10 → 一般 r の順序 | 要確認 | 反映済み（a1-design §3 の 2、HodgeTateComparison の方針） |
| W9-I-26 HT filtration・導来外冪を D(A) で Kan 延長すると完備性が失われる（Fil_0 ≠ R^∧） | 致命 | **訂正済み**（a2-design §2.3・D33：D(k)_{p-comp} 内の延長 LΛ_p ∘ Lan、exhaustive は完備圏で、G-A2-9；drafts/A2/HodgeTateFiltration） |
| W9-I-27 φ_{A*} は CAlg_A の全余極限を保たない | 要修正 | 訂正済み（sifted に。a2-design §2.2、DerivedPrismaticCohomology） |
| W9-I-28 切り捨ては dg 関手にならない；connective の名前が原典と逆 | 要修正 | 訂正済み（Truncation：相対圏の局所化または t 構造の随伴；`IsConnectiveAt` = D^{≤n}、`IsCoconnectiveAt` = D^{≥n} に入れ替え、A4 の参照も） |
| W9-I-29 animated 完備化と `completionRing` = H⁰ の区別 | 要確認 | 反映済み（a2-design §2.4・D32、BaseChangeAndTensor）。E3 との接続は perfd の段で Prop 8.5 系 4 が要る → **a5-design §7.1 の決定項目 6（Prop 8.5 を animated S で、D45 改訂）** |
| W9-I-30 E3 の `unit` は CAlg の関手射 | 要確認 | 反映済み（Fil_0 → Δ̄ を CAlg で：`hodgeTateUnitCAlg`、a2-design §2.3） |
| W9-I-31 `Poly` の k パラメータ | 要修正 | 訂正済み（AnimatedAlgebra） |
| W9-I-32 qrsp の定義に有界 p 冪ねじれがない（S = ∏ O_C/(p^n) が反例） | 致命 | **訂正済み**（a3-design §1・§2.3・D39、`IsQuasiregularSemiperfectoid.boundedTorsion`） |
| W9-I-33 Lemma 7.7 の仮定は Δ̄ の離散性；有界性は自動でない | 要修正 | 訂正済み（a3-design §2.1、`IsDiscreteHodgeTate` → `IsDiscretePrismatic`、`discretePrism` の `hbdd`） |
| W9-I-34 源の p ねじれなしでは δ 射が出ない；φ mod p は独立補題に | 要修正 | 反映済み（δ 射は p ねじれなしの標的に限定、G-A3-9 追加）。**D36 の射の範囲は (a) で決定（11-02）** |
| W9-I-35 Δ_{T/A} ≃ Δ_{T/A′} は A2 (4) ではない | 要修正 | 訂正済み（G-A5-17 を G-A2-10 として A2 の隣に前倒し、A3 §2.3・`regularSemiperfectoid_prismatic`） |
| W9-I-36 HT の多項式入口の値の圏、一般の k の余接複体 | 要修正 | 訂正済み（`hodgeTatePoly` を D(k) 値に、`cotangentWedgeGeneral` の注記） |
| W9-I-37 一般への帰着の順序（B の離散性を先に） | 要確認 | 反映済み（a3-design §2.2：B_univ ⊗̂ A の離散性を導来 Nakayama で、紙 7） |
| W9-I-38 無限 filtration の離散性の説明、gr¹ の shift、G-A2-5 | 要修正 | 訂正済み（a3-design §2.2：有界ねじれによる議論、gr¹ は次数 0、J と J̄ の区別；a2-design G-A2-5 は sifted） |
| W9-I-39 「B_univ は A_univ 上完全平坦」は偽（f = dY で f の乗法が零） | 致命 | **訂正済み**（a3-design §2.2 を原典 Ex 7.9 の順序に：B := E ⊗̂^L_U A（CAlg）を普遍の比較の底変換で Δ_{R/A} と同一視し、HT の離散性から B 離散・Tor 独立、δ 環の押し出しの普遍性で envelope と全 prism の中の始性。G-A3-10、骨組み `lciDerivedEnvelope*`） |
| W9-I-40 p ねじれなしへ制限後も全 prism の始性が結論に残る | 要修正 | 訂正済み（`exists_initial_of_discrete` は部分圏での始性。Ex 7.9・Prop 7.10 の全 prism の始性は envelope の普遍性から。A5 で要る Lemma 7.7(3) の δ 射は完全 prism への脚だけ） |
| W9-I-41 完備化後の離散性を Tor 独立と言い換えない | 要修正 | 訂正済み（a3-design §2.2 (iii)：H⁰ 比較 `derivedComplexCompletion_h0_map_isIso` で B ≃ H⁰ LΛ_I(E ⊗_U A)） |
| W9-I-42 非完全 δ 環の押し出しに `PerfectDeltaTensor` は使えない | 要修正 | 訂正済み（G-A3-10 (a)：W₂ への切断で通常の δ 押し出し、`existsUnique_deltaPDCompletionHom`） |
| W9-I-43 一般 qrsp の始性と T・S′ の始性を区別 | 要修正 | 訂正済み（公開する始性は T・S′ に絞る。`qrsp_initial` は別単位・E3 不要と注記） |
| W9-I-44 既存 Cor 7.3 入口へ渡すデータ | 要修正 | 訂正済み（a3-design §2.3：A′ = A_inf(R′)、r : A′ → S′、非単元・零環の分岐、`existsUnique_deltaPerfectionPDCompletionHom`。G-A3-8′） |
| W9-I-45 G-A3-9 は φ と E∞ 演算の比較を含む | 要確認 | 反映済み（G-A3-9 の仕様に追加。段 II で A4 の P⁰ と同時に検証） |
| W9-I-46 ノートの表記の同期 | 軽微 | ノート第 7 章（Lemma 7.7 の入口は Δ̄、Prop 7.10 の射は Δ̄ へ、RootEnvelope は完全化後の比較）を更新 |
| **段 I の総括（W9 続き 6）** | — | 新たな致命なし。段 II（A4〜A7）へ進む。残る要修正・要確認は上表のとおり反映済み（G-A3-9 の比較は段 II で） |
| **段 II 開始（W9 第 2 部）** | — | A4 の途中で停止、以下を反映 |
| W9-II-01 D42：φ_* と φ^* の同一視で塔の遷移射が型をもたない | 致命 | **訂正済み**（a4-design §2.1・D42・G-A4-3、`frobeniusTower`：原典どおり φ_{A*}^n の塔。D42 撤回） |
| W9-II-02 P⁰ と levelwise Frobenius の比較を p 重 cup 積で説明できない | 要修正 | 訂正済み（coherent な自然変換（Lurie の強さ）と Tot・実現への移送。a4-design §2.2 (a)・G-A4-1、EInfinityPowerOperation） |
| W9-II-03 D41 の説明が D32 だけ | 要修正 | 訂正済み（二段：animated D32 ＋ Prop 8.5 系 4） |
| W9-II-04 H⁰(Δ_perf) に A3 の離散 Δ 用定理を直接当てられない | 要修正 | 訂正済み（C/p ↪ H⁰(X/p) の単射、一般の Rem 2.2 = G-A4-8/G-A3-6、prism 性を直接組み立て） |
| W9-II-05 単位名とノートの coconnective 欄 | 軽微 | 訂正済み（InterfaceFields、ノート第 8 章） |
| W9-II-06 完全 site の余積を B ⊗̂_A B′ とすると S 構造射の一致が失われる（S = F_p[t] の反例） | 致命 | **訂正済み**（a5-design §2.1：Perfd_{S/} の余積 (T₁ ⊗̂_S T₂)_perfd（Cor 7.3 の普遍性）を Lemma 4.8 の圏同値で完全 site へ。flat 被覆の相対 Čech 項（G-A5-5）とは区別。`perfectSite_cechNerveData`） |
| W9-II-07 比較写像の脚に旧記法 φ_A^{n*} が残る | 要修正 | 訂正済み（f_n = φ_B^{-n} ∘ f : Res_φ^n Δ_S → B。a5-design §2.2、`perfectionComparisonLeg`（W9-III-15 で改名、PerfectSite）） |
| W9-II-08 D45 改訂と旧「離散のみ・系 4 なし」の併存 | 要修正 | 訂正済み（a5-design 冒頭・§0・§1・§6、骨組みの概要・規約、本表の D45〜D52 行） |
| W9-II-09 S̃ は完備 filtered 余極限を保たない（完備化で現れる元の Y 変数） | 致命 | **訂正済み**（a5-design §3.1 (iv′)・§3.2・D51・G-A5-18：S̃ は弱始対象用に限り、filtered 余極限は完備化前の代数的根添加 E(S_alg)^∧_p と「flat semiperfectoid 被覆の取り替えで Čech 計算不変」で。`rootClosure_filteredColimit` 撤回、`algebraicRootClosure*`） |
| W9-II-10 arc 被覆の骨組みが「忠実平坦」を「平坦かつ単射」に弱めている（F_p[t^{1/p^∞}] の反例で O の Čech 降下が破綻） | 致命 | **訂正済み**（`IsArcCoverFamily` を `e.FaithfullyFlat` に。原典 Def 8.7 どおり） |
| W9-II-11 G-A5-18 の「任意の flat semiperfectoid 被覆」は S3 だけでは出ない | 要確認 | 反映済み（E 被覆は Q(U) が弱始なので S3 で閉じる。一般形は別補題・E3 不要。a5-design §3.2・G-A5-18） |
| W9-II-12 Lemma 8.6 の RHom と完備性の接続 | 要確認 | **解消（W9 続き 6）**：任意の C 加群を係数とする (∗)（G-A5-13）と有限 Koszul 複体 K_A(p,e) の Postnikov filtration・双対可能性・Rlim で M ∈ D^{≤−1}。C を perfect と仮定しない。仕様を a5-design §3.5・G-A5-6′・G-A5-13、`rhom_baseChange_koszul_connection`・`squareZero_rhom_coconnective` に記録 |
| W9-II-13 `IsDescendable` の底が離散環に限られる | 要修正 | 反映済み（一般形 `IsDescendableOver`：対称モノイダル安定 ∞ 圏の可換代数対象を底に。a5-design §2.4） |
| W9-II-14 G-A5-11 の「次数 −1 集中」 | 要修正 | 訂正済み（次数 −1 以下。a5-design G-A5-11、SemiperfectoidCase） |
| W9-II-15 S・T・I が完備でも T/IT は導来 p 完備とは限らない（平方零拡大の反例、`ArcOutside` も成立） | 致命 | **訂正済み**（a6-design §2.3・G-A6-10・§8.7：S/I の部分だけ残し、T/IT は `completionRing` 経由の自然同型 F_U ≃ F_{completionRing U}、Γ(F_U, O) ≃ e3Perfd(U) で四角形を自然変換として移す。`Excision.lean`） |
| W9-II-16 全 p 完備環の affCompl_κ の cover-dense を、perfectoid 基底を仮定する A5-4 の `rootClosure_isSemiperfectoid` から導いている（ℤ_p から基底なしの根添加を始めると ℤ_p へ retraction、perfectoid 環から ℤ_p への環準同型はないので semiperfectoid でない） | 致命 | **訂正済み（2026-11-03）**：global な affCompl_κ は維持（Codex 推奨 (a)）し、前段 G-A6-11 を追加：R₀ := ℤ_p[p^{1/p^∞}]^∧、S₀ := completionRing(S ⊗_{ℤ_p} R₀) を R₀ 代数として A5-4 の根添加へ。arc 被覆の持ち上げは perfectoid な W（G-A6-3）を**先に**取り、R₀ → W・S₀ → W → `rootClosure_extends` → 普遍性の順（旧「S̃ → V に延びてから W」は順序が誤り）。a6-design §1・§2.1・§4・§7・§8.8・§9・§10、`ArcSite.lean`（`perfectoidBaseRing`・`baseExtension`・`exists_baseExtension_lift`・`exists_perfectoid_arcCover`）、ノート第 8 章。別案 (b)（固定 R 上の相対 site）は採らない。修復後の層の延長までの全接続は Codex 未確認 |
| W9-II-17 G-A6-1b の骨組みが `(F_p 代数)^op` と「連結部分」で、BM18 の共変 Ring_{F_p} → D(ℤ)^{≥0}（coconnective）と揃わない | 要修正 | 訂正済み（共変・H^i = 0 for i < 0 の規約を明示。affine 版 D59 の根拠として Zariski 降下と finitary 性の確認を記録。a6-design §4・D59、`arcSheaf_of_vSheaf_of_valuationSquares`） |
| W9-II-18 1a は被覆側も完全環であることを明記、1c は BS17 Lemma 6.3（完全付値環）の特殊化で Lemma 6.2 はその四角形ではない | 要修正 | 訂正済み（1a に B_i の完全性を追加。1c は `valuationRing_milnorSquare`（任意の付値環、初等補題：𝔭V_𝔭 = 𝔭）と引用 `valuationRing_milnorSquare_perfect`（[BS17, Lemma 6.3]）に分離。a6-design §4・D56） |
| W9-II-19 S′ × S/I への取り替え後の四角形は元の四角形と恒等四角形の文字どおりの積ではない | 軽微 | 訂正済み（(B × C) ×_{D × C} C ≃ B ×_D C、C → D × C は (g, id) として記述。a6-design §3.2(2)、`excision_of_excision_prod`） |
| W9-II-20 G-A6-5「tilt は d ねじれなし」は偽（R 標数 p なら d = p で像は 0）。正則なのは Witt 環上の d。W を交代和微分に当てる意味にもできない | 要修正 | 訂正済み（levelwise の W_n と V の短完全列で帰納、Rlim、各 Witt 環で正則な d の cofiber。a6-design §3.1(1)・G-A6-5、`witt_exact_of_perfect`） |
| W9-II-21 標数 p 版の arc 被覆は階数 ≤ 1 で試すが持ち上げの説明が階数 1 だけ。階数 0 と a = d mod p = 0 の分岐が要る | 要修正 | 訂正済み（四分岐：a 単元／階数 1 で a ≠ 0／階数 1 で a = 0 は V^♯ = V／階数 0 は V₁ = k[t^{1/p^∞}]^∧ へ忠実平坦に拡大。untilt の付値環性は [Česnavičius–Scholze, Prop 2.1.9] の証明と同じ（参照のみ）。a6-design §3.1(2)・§8.3・G-A6-6、`tilt_arcCoverFamily`・`untilt_rankOneValuationRing`） |
| W9-II-22 global な affPerfd_κ の対象には固定 R からの射がなく、O を CAlg_R 値とは書けない | 要修正 | 訂正済み（O は CAlg_ℤ 値。F_U の元の圏 Perfd_{U/} の上で R → U → T により CAlg_R 値に持ち上げ、極限・引き戻しは忘却が作るので E3 の型に戻せる。site は変えない。a6-design §2.2・§3.2(5)・§8.9、`ArcSheafProperty.lean`） |
| W9-II-23 Cor 8.14 の乗法との一致は単位の自然性だけでは出ない（S 上の一致まで） | 要修正 | 訂正済み（G-A7-8 単位の整合性 F(η_S) = η_P を A5 の極限の脚（f = η_S の脚 q = id_P）と比較の自然性から示し、Prop 8.13 の比較の二つの脚と押し出しの普遍性で e ∘ η_X = m。一意性の先取りなし。a7-design §2.3・§3・§7.3、`perfectoidization_map_unit_eq_unit`・`selfTensor_unit_eq_mul`） |
| W9-II-24 G-A7-5（A5 が使う）を A5 に依存する A7 の普遍性モジュールに置くと import が閉じない。G-A7-1 も同様 | 要修正 | 訂正済み（数学的循環ではなく配置。`drafts/A7/DiscreteCore.lean`（G-A7-5）と `drafts/A7/AnimatedDomain.lean`（G-A7-1）に切り出し、A5/SemiperfectoidCase・A5/PerfectSiteComparison が import。所有は A7 のまま。a7-design §5・§6、drafts/README） |
| W9-II-25 `IsCoverDense.sheafEquiv` は Mathlib の正確な名前でなく、包含は site の opposite で渡す | 軽微 | 訂正済み（`Functor.inducedTopology`、`Functor.sheafInducedTopologyEquivOfIsCoverDense`（= `Functor.IsDenseSubsite.sheafEquiv`、`Sites/DenseSubsite/{InducedTopology,Basic}.lean`）、包含 `affPerfdInclusion.op`、Set の `HasLimitsOfShape (StructuredArrow X G.op)`。a6-design §4 G-A6-8・§7・§10、`ArcSite.lean`・`SheafOfSetsExcision.lean`） |
| （W9 続き 6）W9-II-19 の補足：g : B → D のまま C → D × C = (g, id) は型違い | 軽微 | 訂正済み（商からの射 h : C → D と書き分け。a6-design §3.2(2)、`excision_of_excision_prod`） |
| W9-III-01 G-A8-3「導来 p 完備な環上の有限加群は導来 p 完備」は偽（R = ∏V、M = R/⊕V：p x_{k+1} = x_k、x_0 ≠ 0 で R[1/p] → M 非零；S = R × M は有限で D(e_0) 上自明な有限エタールだが非完備）。Cor 8.12 の前提の供給が崩れる | 致命 | **訂正済み（2026-11-03、Codex 推奨 (a)）**：Thm 10.9 の入力を原典どおり有限表示有限に戻す（脚注 19、既存 `isModuleComplete_of_finitePresentation`。E3 の始域は狭まらない：Thm 10.11 は有限表示有限に帰着）。S′ の完備性は構成固有の計算 G-A8-3′（有限個の e_j s_a で生成、R 被約で R̄ = R/ann(g) 完備、S′ ≅ g^N S′ ⊂ R̄^r、既存 `ModuleClosure`）。a8-design §2.2・§3.2(5)・§4・§7・§8.2、`AlmostPurityConnectivity.lean`（`finitePresentation_isModuleComplete`・`trivialCoverComparison_isModuleComplete`）。(b)（任意の有限 S を completionRing 経由で残す）は採らない |
| W9-III-02 局所化の同型だけでは `ArcOutside` は出ない（S = V = F_p[t^{1/p^∞}]^∧_t、S′ = V[1/t]、g = t で id が延びない）。界面の条件は g の像が非零であって可逆ではない | 要修正 | 訂正済み（G-A8-3″：整写像＋局所化の同型 ⇒ Frac(V) へ延長し整閉性で V へ。界面を弱めない。a8-design §3.2(4)・§4、`arcOutside_of_integral_of_localization_iso`、`perfectoidization_almostIso_of_localization_iso` の前提に整・完備を明示） |
| W9-III-03 「R/J = R/f_1 ⊗̂ ⋯（導来）」は偽（p ねじれなし R、f_1 = f_2 = p で H^{−1} = R/p） | 要修正 | 訂正済み（Q := ⊗̂^L R/(f_i)、π_0 Q = R/J、Prop 8.5 系 4 で Q_perfd ≃ (R/J)_perfd、Prop 8.13 の二段。生成元ごとの判定は維持。a8-design §3.1・G-A8-2、`isAlmostZero_iff_forall_gen`） |
| （W9 第 3 部の要確認）Thm 10.11 の整閉包 S′ に Cor 8.12 を当てる前提（整性・導来 p 完備性）の供給 | 要確認 | → W9-III-04 で致命と判明、下の行で修復 |
| W9-III-04 Thm 10.11 の整閉包 T は導来 p 完備とは限らない（V 値の p 進収束列の環 R（perfectoid）、g = (p^n)、S = R で、b = (n) は T の p 進 Cauchy 列の極限だが R 上整でない）。Cor 8.12 を直接当てられない | 致命 | **訂正済み（2026-11-03、Codex 推奨 (a)）**：T（代数的整閉包、原典どおり）と T̂ = completionRing T を分け、Cor 8.12 は S → T̂ に当てる（D70・G-A8-10：ArcOutside は W の p 完備性で T̂ へ延びる、T の p 冪ねじれは有界なので T̂ は離散で導来完備、e3Perfd(T) = T̂_perfd、商の比較は A6 §2.3 の自然同型）。生の T の完備性を一般補題にする案は不可。(b)（A6 側に系を追加）は採らない。a8-design §3.3(5)・§4・§5・§7・§8.7、`IntegralDiscreteness.lean`、ノート第 10 章 |
| W9-III-05 S → T の局所化は同型とは限らない（S = V[ε]/(ε²)、g = p。原典は arc 層の同型）ので G-A8-3″ を S に直接当てられない | 要修正 | 訂正済み（S → S_red → T ⊂ B と書き、ArcOutside は W 被約で S_red を通し Frac(W) と整閉性で。`integralClosureInLocalization_arcOutside`） |
| W9-III-06 「整閉包の有限生成部分代数」では有限表示性が出ない | 要修正 | 訂正済み（G-A8-11：T への写像を備えた有限表示有限 A_λ の filtered 系、A_λ[1/g_1] ≅ B、単射性を要求しない。`exists_finitePresentation_approximation_fixedLocalization`） |
| W9-III-07 Lemma 10.12 の骨組みの引数に Z_(p) 代数の仮定がない（q ≠ p の純非分離拡大で偽） | 要修正 | 訂正済み（`exists_finiteEtaleStratification` に `hZp : ∀ q, q.Prime → q ≠ p → IsUnit (q : R)` を追加） |
| W9-III-08 本体の実 import `CompletedTensor → IntegralExistence → Inputs`（有限直積 `isIntegralPerfectoid_finPi` が E3 を使用）により、A6・A8（Lemma103 経由）から Inputs へ到達し、Inputs の証明を Assembly に置き換えると循環 | 致命（配置） | **方針決定（2026-11-03、Codex 推奨 (a)）**：Fontaine の芯を E3 非依存のモジュールへ切り出し、Lemma103・A6・A8 の依存をそこへ、有限直積は直接証明（G-A6-12）。**実施は 2a 後**（BS は 2a まで BS の Lean を触らない。調整役へ依頼、§3.1）。drafts の import 行にコメント、a9-design §7（受入条件：Inputs への到達経路なし）、drafts/README「ファイル順序」 |
| W9-III-09 A1・A4・A5 で先行の定義と後段の定理が同居（DeRhamComparisonPoly↔HodgeTateComparison の黒箱、WeaklyInitialAndDescent の根添加と降下、PerfectSiteComparison の比較写像と Prop 8.5、InterfaceFields の `e3Perfd_eq_direct`、Perfectoidization の Example 8.3） | 要修正 | 訂正済み（新設 `A1/CrystallineInput`・`A5/RootAdjunction`・`A5/PerfectSite`・`A4/AfterComparison`、Lemma 8.6 の主張は StrongDescent に一本化、各 import コメントを更新。DAG は drafts/README「ファイル順序」と a9-design §7。所有単位は不変） |
| W9-III-10 almost 連結性の余極限保存は G-A8-8 からは出ず（A_λ の perfd が perfectoid とは未知）、非有界版 Prop 10.4 には忘却 U の完全忠実性・極限余極限保存が要る；一般 J と単項 `perfectoidIdeal` の API の区別 | 要修正 | 訂正済み（G-A8-1 の系 `isAlmostConnective_iff_completedTensor_connective`・`isAlmostConnective_completedFilteredColimit`、内部補題 `restrictScalars_perfectoidQuotient_fullyFaithful`；G-A8-8 は一般の整代数への帰着でだけ使う。a8-design §2.1・§3.3(5)・G-A8-1・G-A8-8・§8.7・8、`AlmostConnectivity.lean`・`IntegralDiscreteness.lean`） |
| W9-III-11 `truncationLE_isCoconnective`・`truncationLE_of_isCoconnective` の述語の向きが逆（τ^{≤n} は `IsConnectiveAt n`） | 要修正 | 訂正済み（`truncationLE_isConnective`・`truncationLE_of_isConnective` に改名・訂正。A2/HodgeTateFiltration の参照も） |
| W9-III-12 A9 の残存引用一覧が D68 前の形（`hodgeTate_iso_polynomial_Zp`）、G-A3-7 の「黒箱」の意味が曖昧、S8 の G13 が抜け | 要修正 | 訂正済み（a9-design §3 を「恒久的な引用」「証明予定」「基盤依存」の三欄に。黒箱は `crystalline_deRham_polynomial_Zp` 一件、1c と P⁰ は暫定、G-A3-7 は証明予定。a3-design §6、本表 A3-3 行） |
| W9-III-13 `nonempty_e3_of_cAlg` の hR は暗黙引数 | 軽微 | 訂正済み（`(hR := hR)`。`Assembly.lean`、a9-design §2） |
| W9-III-14 DiscreteCore が入力の A4 より前に並び、A5 の先行ファイルが後段の Čech データ・filtered 余極限補題を参照 | 要修正 | 訂正済み（README の順序：A7/DiscreteCore は A4/Perfectoidization の後；`prismaticPerfection_filteredColimit` を A4/Perfectoidization へ（A2 の sifted 余極限保存・塔・完備化の反射性だけ）；`perfUnder_cechNerveData` を A5/PerfectSite へ（既存 Cor 7.3 の普遍環から直接）。AfterComparison の利用側（A6・A8）と ArcSite の根添加の所在の import コメントも補った） |
| W9-III-15 同じ namespace に内容の異なる `perfectionLeg` が二つ | 要修正 | 訂正済み（A4 は `toPerfection`、A5 は `perfectionComparisonLeg`。利用箇所 InterfaceLimitCone・SemiperfectoidCase・UniversalProperty・a7-design を更新） |
| W9-III-16 ノート第 5 章に訂正前の「帰着は Prop 6.2 の経路」の D69 と、結晶側を「具体的に定義する」旧説明が残る；第 8 章「E3 での扱い」も | 要修正 | 訂正済み（05-hodge-tate の冒頭・§5 の概要・Thm 5.2/Cor 5.5 の後・項目表 2 行・要点、08-perfection「E3 での扱い」と Lemma 8.6 の行を D68（黒箱一件、Cartier で系、RΓ_crys は定義しない）・D69（普遍 A₀ 上で Thm 6.4 を証明して底変換）に揃えた） |
| W9-III-17 恒久的引用の表に証明予定の 1c と基盤側の P⁰ が同居 | 軽微 | 訂正済み（a9-design §3：最終引用は D68・G-A6-1a・1b の三件、1c は証明予定、P⁰ は基盤待ち（D43）。暫定の許可数（最大五）と最終引用数（三）を区別） |
| **W9 最終判定（第 3 部続き 3）** | — | 条件付き妥当。12 論点すべて妥当（A9 は W9-III-08 の実施条件つき）。D19〜D70 の三者照合 ○、κ ○、sorry 194 宣言（恒久的 3・証明予定 125・基盤待ち 66）。a9-design §8 |
| D1-01（BS-D1、Codex の下書き作業）S3 の `CechNerveData` は圏 𝒟 の絶対積のデータだが、arc site で要る Čech 項 S ⊗̂_R S は相対（R = S = F_p[t] の恒等被覆で絶対積 S ⊗̂_{ℤ_p} S と異なる） | 要修正 | 反映済み（11-03）：𝒟 := sieveCategory Q（Q は単射被覆の生成 sieve）の中で取る（U = f.op が弱終、冪は op R 上のファイバー積）。主張を (1) 生成 sieve ごとの Čech 同値 `isSheaf_generateSieve_iff_cech` と (2) 層判定 `isSheaf_arc_iff_cech`（coverage `arcCoverage`、`arcTopology_eq_toGrothendieck`）に分離。ArcSite・a6-design §2.2 |
| D1-02（BS-D1）有限族の coverage と一点族の coverage は同じ位相を生成しない（k × k → k の二つの射影：有限 arc 被覆だが生成 sieve は一点被覆を含まない）。任意の前層では一点 Čech 条件だけで層にならない（二点定数前層と零環の空族） | 要修正 | 反映済み（11-03）：`arcTopology_eq_toGrothendieck` を有限族版に、`arcTopology_eq_sup`（一点 ⊔ extensive）、`PreservesFiniteRingProducts`、S1-E `isSheaf_extensive_iff_preservesFiniteProducts`（基盤待ち）、`isSheaf_arc_iff_cech` を「有限積保存 ∧ 一点 Čech」に。O と Hom(T,−) は有限積を保つので Prop 8.10 の帰着は従来どおり。ArcSite、a6-design §2.2、infinity-sheaves-design §13 |
| D1-03（BS-D1）Mathlib `PreTilt O p` の環構造は `Fact (¬IsUnit (p : O))` を要求し、設計が含む零環（両因子が非零でも相対完備テンソルは零になり得る：F_p × F_p の二つの射影）と合わない | 要修正 | 反映済み（11-03）：零環を含む tilt `tiltRing`（G-A6-14。零環なら零環、非零なら `PreTilt`；p 完備で非零なら p は非単元）と関手性 `tiltMap`、`IsTiltGenerator`、G-A6-4 を `tiltRing` で具体的に。定義の変更ではない（原典の tilt は零環で零環）。ArcSheafProperty、a6-design §3.1・§4 |
| D2-01（BS-D2、Codex）`cAlgRestrictScalars_isColimitCone` は任意の環写像・任意の図式では偽（ℤ → F₂ に沿う制限は始対象を保たない；余積 ⊗_T は ⊗_S にならない） | 要修正 | 訂正済み（11-03）：CAlg 版は sifted 図式（`IsSiftedInfinity K`）に限定、同型に沿う制限は全余極限を保つ別補題 `_of_bijective`（A7 の完全 prism の φ_A）、D 版は全余極限で正しい。ScalarRestriction.lean |
| D2-02（BS-D2、Codex）`perfectoidIdeal_baseChange` の右辺：(JR′)_perfd は J_perfd R′ の通常の `Ideal.map` ではなく p 進閉包（Fayolle Prop 2.9）。閉包を外す補題はない | 要修正 | 訂正済み（11-03）：右辺を「完備テンソル J_perfd ⊗̂_R R′ の像＝ker(R′ → (R/J)_perfd ⊗̂ R′)＝J_perfd R′ の p 進閉包」で述べ、`Ideal.map` との一致の補題は**置かない**（有界ねじれだけでは偽：R = V⟨x_i^{1/p^∞}⟩、K = ker(R → V)、R′ = R⟨t^{1/p^∞}⟩ で Σ p^n x_n t^n が閉包にだけ入る。K 有限生成なら成り立つが J_perfd は一般に有限生成でない）。almost 零の反映は K′ ≅ K ⊗̂_R R′ で閉包に依らない。a8-design §3.1 |
| D3-01（BS-D3、Codex）比較の第 0 脚に指定した A3 の `prismMapOfDiscrete` は離散性を仮定して環準同型を返すが、A5 は仮定なしの CAlg_A の Frobenius 両立な射が要る | 要修正 | 回答（11-03）：Lemma 7.7(3) の一般形は RΓ の極限の射影（S2 `derivedGlobalSectionsCAlg` の対象 B での脚、Frobenius 両立は `structurePresheafFrobenius` の自然性）。A5 には「A0/S2 の CAlg 値 RΓ の射影待ち」の型つき仮置きを置く（A3 待ちではない）。a5-design §2.2 |
| D3-02（BS-D3、Codex）S3 の `CechNerveData` は `SmallCategory` 専用だが A5 の `PerfUnder_u p S` は大きい圏（対象 Type (u+1)、射 Type u） | 要修正 | 回答（11-03）：W9-I-04 で予告した大きい版を基盤側の draft に置いた（`CechNerveDataLarge`・`IsWeaklyTerminalLarge`・`isLimitCone_iff_restrict_cech_large`、Sheaves/CechConerveLimit）。A5 はこれを返す。infinity-sheaves-design §13 |
| D3-03（BS-D3、Codex）離散代数の埋め込みと `cAlgRestrictScalars` の標準比較（A5 の `discreteRestrictionIso`）は基盤側 | 要確認 | 反映済み（11-03）：一般形 `cAlgRestrictScalars_algebraEmbedding` を ScalarRestriction.lean に（基盤待ち）。A5 の版はその特別な場合 |
| D3-04（BS-D3、Codex）`IsDescendableOver` が引数のない `True` で、`IsDescendable A B` は離散底。Lemma 8.6 の底 Δ_T は離散でない | 要修正 | 入口を確定（11-03）：`IsDescendableOver A R B (f : SSet.Edge R B)`（R・B は CAlg_A の頂点、Mod_R(D(A)) の thick ⊗-ideal、基盤待ち M15）、`HasDescentIndexLEOver`、`isDescendableOver_iff_exists_index`、一般形の (a)〜(h)（押し出し・合成・テンソル・Tot・RHom 判定・Frobenius 余極限・完備版、基盤待ち）。Shared/Descendable.lean。A5 はこの API だけを使う |
| D3-05（BS-D3、Codex）StrongDescent の `prismScalarExtension`（A → C に沿う CAlg の係数拡大 ⊗^L_A C）は基盤側 | 要確認 | 反映済み（11-03）：`cAlgBaseChange f : CAlg_R S ⟶ CAlg_R T`、`cAlgRestrictScalars` との随伴、忘却との比較 `cAlgBaseChange_forget`（D 側は既存 `derivedInfinityBaseChange`）を ScalarRestriction.lean に（基盤待ち） |
| D3-06（BS-D3、Codex）`extendArcSheaf` の向き：`sheafInducedTopologyEquivOfIsCoverDense` は `Sheaf (inducedTopology) ≌ Sheaf K` なので延長は `.functor`、制限が `.inverse` | 軽微 | 確認（11-03）：そのとおり。指示書の「逆」は「制限の逆」の意味。a6-design G-A6-8 |
| D3-07（BS-D3、Codex）S8 の入口 `sectionsOf`・`localEquiv_of_sheafifyIso` が引数のない `True` | 要修正 | 入口を確定（11-03）：離散（集合値）の場合を型つきに——`IsLocalEquivSet J φ`（Mathlib `presheafToSheaf` で同型）、`presheafPushout`、`sectionsOfDiagram F O`（`F.Elements` の nerve の持ち上げと O の合成）、`sectionsOf F O h`（選んだ極限の頂点）、`sectionsOf_map`、`sectionsOf_representable`、`sections_localEquiv_iso`（`IsInvertibleEdge`）、`sectionsOf_eq_limit_elements`（元の圏と同値な D 上の極限）。∞ 側との橋（S8-1・2、`sectionsOf_pushout` の引き戻しの述語）は基盤待ち。Sheaves/SpaceValued |
| D4-01（BS-D4、Codex）Shared の `forms`・`completedForms` が k・変数型を引数に取らず、後者に加群構造がない。一般の k で H⁰ 完備化に置き換えると導来完備化の負次数を失う | 要修正 | 回答（11-03）：A2 は通常の `forms` を `discreteEmbedding` で D(k) に入れ DerivedGeneral の `completion`（LΛ_p）を施す；有界 p 冪ねじれ（有界 prism の A/d）でだけ H⁰ 版 `completedForms` と同定（`completedForms_eq_derivedCompletion_of_boundedTorsion`、基盤待ち）。Shared の `forms`・`completedForms` は k・T・p を明示引数に、`completedPoly`・加群構造を追加。a2-design §0′ |
| D4-02（BS-D4、Codex）A1 の `universalOrientedPrismRing : Type u := sorry` は p を引数に取らず `CommRing` もなく、A1 内の `(p := p)` と型が合わない | 要修正 | 回答（11-03）：A3 の普遍例は任意の有界向き付き prism A₀・有界性・d を保つ分類射を明示引数にして述べ、停止点 3（A1）で A1 の具体的な A₀ に特殊化し、A1 側の宣言は p を明示引数にして `CommRing` を付ける。a3-design §2.2 |
| D4-03（BS-D4、Codex）Shared の `Cosimplicial.cohomology`・`quotPow` は body が sorry で図式 X・C・元 d が引数に入らず、`regularShortExact` は `True` | 要修正 | 基盤側で確定（11-03）：`cohomology X n`（X 明示、`AddCommGroup`、Mathlib の `alternatingCofaceMapComplex` のホモロジーとの `cohomologyEquivHomology`）、`cohomologyMap`・`cohomologyMap_cup`、`quotPow C d hd_nat k′`、`toModules k C ι`（係数 k を固定、W9-I-21）、`regularShortExact … : CosimplicialShortExact`、`regularBockstein`、`bockstein_sq` を型つきに。A1 は Mathlib の homology を直接使う所では `cohomologyEquivHomology` で橋渡し |
| D4-04（BS-D4、Codex）a1-design §2.5 の「Constr 6.1 の α は c = 1」は A0 §2.9 の Koszul 版の述語と合わない（標的で α(d) = p·u なので Kos(D₀; p, α(d)) に H^{−2} = D₀/p が残り c = 2） | 要修正 | 訂正済み（11-03、二度目：全 K を量化すると K = A₀/(p,d) で H^{−3} ≠ 0 なので **c = 3**＝B/p の Tor 次元 ≤ 2 ＋ 標的 Koszul の余分な 1 段）：二つを分ける——α mod p の通常の Tor 振幅 ≤ 1（保存性・(6) の分解用）と、Koszul 版の (p,d) 完全 Tor 振幅 c = 3（Lemma 4.20・4.22 用。要るのは有限性だけ）。A0 §2.9 に Koszul 版と商の版のずれ（≤ r）を注記。a1-design §2.5 |
| D4-05（BS-D4、Codex）Shared の `deRhamComplex` が変数型 T を取らず、`completedForms` 上の連続微分・外積の宣言がない | 要修正 | 基盤側で確定（11-03）：`deRhamComplex k T`、`completedFormsUnit`、`completedWedge`（＋unit との両立）、`completedDeRhamD`（k 線形な連続微分、W9-I-22。unit との両立・d̂² = 0・Leibniz）、`completedDeRhamComplex k T p`。A1 はこれを CommMon (Complex k) にまとめ Barratt–Eccles の augmentation と `cAlgVertex` で E∞ 実現 |
| D4-06（BS-D4、Codex）Shared の `regularShortExact` は body が sorry で型に `hd_reg` が現れないので section 変数 `hd_reg` が引数に残らない（A1 の `htSequence`・`regularBockstein` が渡す） | 要修正 | 基盤側で修正（11-03）：`include hd_reg in` を付けて引数に残す（def の body 依存の自動包含に頼らない。D4-03 と同じ教訓：body が sorry の宣言は section 変数が落ちる） |
| D5-01（BS-D5、Codex）入口表 §1.2 の shift の式 `IsConnectiveAt n x ↔ IsConnectiveAt (n+1) (Σx)` は向きが逆（Σ = [1] は `derivedSuspensionShiftObjectIso`、cohomological 添字で H^i(Σx) = H^{i+1}(x)；X = A[−1]、n = 0 が反例） | 要修正 | 訂正（11-03）：`IsConnectiveAt n x ↔ IsConnectiveAt (n-1) (Σx)`。分解は標準の τ^{≤n}x → x → τ^{≥n+1}x の cofiber 四角形（安定なので fiber 四角形でもある）で述べる |
| D5-02（BS-D5、Codex）入口表 §1.2・§1.6 が加群 H^n(X)・Ω^i を `discreteEmbedding A` で D(A) に入れると書いたが、その始域は A 代数 `nerve (Under (CommRingCat.of A))` | 要修正 | 訂正（11-03）：加群は A2 `ordinaryFormsDiagram` と同じ `moduleSemifreeResolutionFunctor A` ＋ `closedNerveInclusion A (Semifree A)` で入れる。`discreteModuleEmbedding A : nerve (ModuleCat A) ⟶ derivedInfinityCategory A` を DerivedGeneral に新設して `truncation_cofiber`・`completedForms_eq_derivedCompletion_of_boundedTorsion` の両方で使う |
| D5-03（BS-D5、Codex）入口表 §1.8 の `powerOperationZero_natTrans : FunctorHom U U` は D(k) では成立しない：P⁰ は φ_k 半線形で、k = F_p[t]、B = k なら t ↦ t^p は k 線形でない | 要修正 | 訂正（11-03）：一般形は U ⇒ U ≫ `derivedInfinityRestrictScalars (frobenius k p)`（U(X) → φ_{k*} U(X)）、k = F_p で `frobenius = id` により自己変換に特殊化。離散成分 `powerOperationZero_eq_frobenius_tot` も B → φ_{k*}B として読む。EInfinityPowerOperation の docstring「k 線形ではない（φ_k 半線形）」と整合 |
| D5-04（BS-D5、Codex）Descendable の記録用補題 `isDescendable_of_faithfullyFlat`「忠実平坦 ⇒ descendable」は偽（Aoki, arXiv:2411.05995 の反例） | 要修正 | 訂正（11-03）：Mathew Prop 3.31 のとおり忠実平坦**かつ有限表示**の離散 A 代数に限定。A5 では使わない記録のみ |
| D5-05（BS-D5、Codex）Shared/CosimplicialCupProduct の `cohomologyEquivHomology`（D4-03 で型つきにした入口）が未定義名 `CosimplicialObject.alternatingCofaceMapComplex` を使う。Mathlib の実名は `AlgebraicTopology.alternatingCofaceMapComplex C`、CommRingCat → AddCommGrpCat の忘却は RingCat 経由の合成 | 要修正 | 許可（11-03）：名前・引数・主張を保って実名に直す（CupProduct・Bockstein の両方）。教訓：ビルドしない drafts では Mathlib 名の誤りが型つき宣言にも残る。(A) の名前探しの対象に Shared の Mathlib 名を加える。同じ誤名は A 側にも残る（A0/CechAlexander:259 の方針欄、A1/HodgeTateMap:74、A1/CrystallineInput:179・234・237）：BS-D5 の対象外、中身の段階で A1 を直す |
| D5-06（BS-D5、Codex）S1-E（extensive coverage の層 ⇔ 有限積を保つ）を A6 の docstring と設計書は `FinitaryPreExtensive` で述べていたが、Mathlib の `isSheaf_iff_preservesFiniteProducts` は余積の非交叉性も含む `FinitaryExtensive` を仮定する。前者だけでは偽：二元順序圏 0 < 1 の被覆 {1→1, 1→1} の層条件から F(1) ≃ F(1)² は出ない | 要修正 | 訂正（11-03）：一般補題は `FinitaryExtensive` で述べる（Sheaves/SheafCondition）。A6 の affine な site（κ-small の p 完備環・perfectoid 環の反対圏）では余積＝環の直積で、非交叉性は二つの射影の引き戻しが零環であること（零環を site に含める、D1-03 と同じ扱い）。A6/ArcSite:272・312 の docstring は中身の段階で直す。infinity-sheaves-design §13 を訂正 |
| D5-07（BS-D5、Codex）入口表 §1.12・§4 の「空間の ∞ 圏 𝒮 の名前がリポジトリにない」は誤り：`InfinityCategories/F1/Categories/CatInfinity.lean` に `SpaceInfinity : SSet.{u+1} := SimplicialNerve KanObject` と `spaceInfinity_quasicategory` がある（Kerodon 3.1.6.1） | 訂正 | 訂正（11-03）：SpaceValued はこの実体を参照、要確認は `IsPresentable SpaceInfinity`（G13）と `Type u` → 𝒮 の離散埋め込みだけ。∞ レーンへの依頼 7 はこの二つに縮む（調整役へ伝達） |
| （決定 11-02）D36 の射の範囲 (a) | — | 記録済み（a3-design §7.1）。Lemma 7.7(3) の δ 射は p ねじれなしの標的、始性はその部分圏；Ex 7.9・Prop 7.10 の全 prism の始性は envelope の普遍性から |
| （決定 11-02）D68 (a)・D69 (a)・決定 6 (a) | — | 記録済み。A5 の骨組みの定義域（`S : Type u` → `CompleteAnimatedAlgebra`）の書き換えは中身の段階で。animated 版の主張 `perfectionComparison_isIso_animated`・系 4 `perfectoidization_piZero` を A5-1 に追加 |

既存の作業ツリーの差分（`exposition/ja/infinity*` ほか 43 件）は他セッションのもので、BS のレビューの受入条件は「新たな差分が報告ファイルだけ」と読む。


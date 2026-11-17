# Codex 作業指示書 BS-W11（下書き）：段 1 の古典的単位 ③④——根添加・R₀・付値環・有限エタール・Milnor 四角形・arc site の 1 圏部分

作成：2026-11-03（BS 作業チャット、下書き）。宛先：Codex。**BS-W10 の後に開始**（基準コミットは開始時に記入：main `________`）。
design-status §4 の 7 の段 1 ③④。基盤（∞ 側・HA の 2b 後の名前）を待たない古典的可換環論だけを集めた。前提・ビルドの規則・禁止事項は BS-W10 §0・§3 と同じ。

## 1. 作業 A：根添加の構成（drafts/A5/RootAdjunction.lean → Perfectoidization/Derived/RootAdjunction）

主張は 11-03 に具体化済み（`rootAdjunctionStep`・`rootClosure` とその延長性・完備性・濃度・関手性、`algebraicRootClosure` と mod p の Frobenius 全射、
`polyAlgebra`・`polyRootAlgebra`（perfectoid）・`rootCover`）。
- 完備化は `PrincipalCompletionH0 _ p`（HA/DerivedCompletion/PrincipalKoszulRing。2b で名前が変わるので改名表を見る）。
- `polyRootAlgebra_isIntegralPerfectoid` は既存の一変数 `CompatibleRootPerfectoid`（Semiperfectoid/）の多変数版。既存の証明の構造を写す。
- `algebraicRootClosure_filteredColimit` の主張の形（`CategoryTheory.Limits` の colimit との比較）を決めてから書く。
- **停止点 A-1**：定義と全主張が型検査を通った時点。**A-2**：延長性・完備性・perfectoid 性まで。濃度評価は後回し可（理由付き sorry）。

## 2. 作業 B：Lemma 8.8 の前段と試験付値環（drafts/A6/ArcSite.lean の G-A6-11・G-A6-3、drafts/A6/ArcSheafProperty.lean の G-A6-6）

- G-A6-11：R₀ = ℤ_p[p^{1/p^∞}]^∧ の perfectoid 性（Codex W9 続き 6 の筋：W(F_p[t^{1/p^∞}]^∧_t)/([t] − p) との同型、または `isIntegralPerfectoid_of_compatible_p_roots`
  （p 正則なので使える））、`baseExtension` = completionRing(S ⊗_{ℤ_p} R₀) と濃度、`exists_baseExtension_lift`。
- G-A6-3：p 完備な階数 1 の付値環 V は perfectoid な p 完備階数 1 付値環 W に忠実平坦に埋まる（絶対整閉包の p 完備化、付値の延長）。W の中の p の両立する p 冪根。
  Mathlib の `ValuationRing`・`IsIntegralClosure`・付値の整拡大への延長（要確認：名前）を使う。
- G-A6-6：階数 1 の付値環の tilt・untilt（a = d mod p の四分岐は a6-design §3.1(2)）、untilt の付値環性（Česnavičius–Scholze Prop 2.1.9 の証明と同じ計算）。
- 1c：`valuationRing_milnorSquare`（任意の付値環、𝔭V_𝔭 = 𝔭 から）と、その特殊化 `valuationRing_milnorSquare_perfect`（引用 [BS17, Lemma 6.3] を証明で置き換える）。
- **停止点 B-1**：主張の型。**B-2**：R₀・G-A6-11・1c まで。**B-3**：付値環の tilt・untilt まで。

## 3. 作業 C：有限エタール代数の perfectoid 性（G-A8-6、drafts/A8/IntegralDiscreteness.lean の `isIntegralPerfectoid_of_finiteEtale`）

完全 prism (A,(d)) の商 R 上の有限エタール代数 T は、完備対 (A,(p,d)) に沿って有限エタール A 代数へ持ち上がり、mod p は完全環上の有限エタール環で完全、Frobenius を
持ち上げて完全 δ 環、d の正則性と (p,d) 完備性は有限エタール性（有限射影加群）から保たれ、Thm 3.10 で商は perfectoid（Codex W9 続き 2 の筋）。
Mathlib の `Algebra.Etale`・`Module.Finite`・有限射影加群・エタールの持ち上げ（`Algebra.FormallyEtale` の lift）を使う。
- **停止点 C-1**：型。**C-2**：証明。

## 4. 作業 D：arc site の 1 圏部分（drafts/A6/ArcSite.lean の残り）

`AffCompl`・`AffPerfd`（`CommRingCat` の充満部分圏の `SmallModel`、濃度 ≤ κ）、`IsArcCoverFamily`（既に具体的）、`arcTopology`（sInf）、coverage（底変換・合成・有限積）、
`isSheaf_arc_iff_cech`（S1 の生成系の補題を待つ部分は理由付き sorry）、`exists_perfectoid_arcCover`（作業 A・B の結果から）、`affPerfdInclusion_isCoverDense`
（Mathlib `Functor.IsCoverDense`、型は具体化済み）、`arcTopologyPerfd`（`inducedTopology`）。
- **停止点 D-1**：型。**D-2**：cover-dense まで。

## 5. 報告

BS-W10 §4 と同じ形で `report-codex-w11.md` に追記。各停止点で `git status --short` が作業範囲だけであること、ビルドの実測、残る sorry と理由。

## 開始の条件（11-05、調整役）

- F-2（名前空間の付け替え）の取り込みと改名表の配布の後に、main から worktree を切って始める（F-2 は 11-05 に前倒しで開始。合図は取り込みの連絡）。開始時に F-2 の改名表で本指示書と drafts の名前を確かめる。
- 当面全ビルドはないので、単体ビルドは coordination.md §2-4a（`ps` の確認と `with_build_lock --wait 0`）だけでよい。

## worktree の規則（11-05、調整役の提案）

- worktree は一度に一つ。作業 B が main に入ったら `bs-w10` の worktree は `git worktree remove` で消す（ブランチは残す）。
- 新しい worktree は `/private/tmp/` ではなく `/Users/sugakubunka/Documents/LEAN_Projects.nosync/` の下に作る（例：`../SerrePositivity-bs-w11`）。/tmp は再起動で消える。
- 停止点の間もこまめにブランチへコミットする。

## 6. 追記（2026-11-05 夜、段階 II の調整役）：開始の確定と段階 II の規則

段階 II では BS 設計のチャットを置かず、**指示・検収・取り込みはすべて段階 II の調整役**が行う。本指示書はこの追記で確定する（表題の「下書き」は読み替え）。正本は [段階 II の計画](../../stage-ii-plan-draft.md) §1.0 と [coordination.md](../../coordination.md) §2。

1. **開始**：基準は main `9f591b5a5` 以降（F-2 と片付けを含む）。worktree `../SerrePositivity-bs-impl`（`LEAN_Projects.nosync/` の下）、枝 `math/bs-impl`。`source ~/.zshenv` の後に `lake env | grep LAKE_ARTIFACT_CACHE` で確かめ、`lake build SerrePositivity.BhattScholze` で温める。BS-W10 の worktree は残っていない（11-05 確認、worktree は main だけ）。
2. **名前の確認（11-05、調整役）**：本指示書の名前は main に実在する。`PrincipalCompletionH0`（`HomologicalAlgebra/DerivedCompletion/`）、`CompatibleRootPerfectoid`（`BhattScholze/PerfectoidIdeal/Cover`・`Semiperfectoid/`）、`isIntegralPerfectoid_of_compatible_p_roots`（`CommutativeAlgebra/RootTower/Perfectoid`）。`valuationRing_milnorSquare` は新しく作る名前。F-2 の改名表 `scripts/refactor/targets/f-namespace-map.json` で名前空間が変わった宣言は新しい名前を使う（deprecated alias は使わない）。drafts の旧名の使用は 0。
3. **drafts の移し方（計画 §1.0）**：drafts のファイル（`drafts/A5/RootAdjunction.lean` 18 か所、`A6/ArcSite.lean` 25、`A6/ArcSheafProperty.lean` 68、`A8/IntegralDiscreteness.lean` 21 の sorry）を、決まった置き場所（`drafts/README.md` の表）へ**新規ファイルとして**移しながら sorry を証明に置き換える。**本体のファイルに sorry を残さない**。§1・§4 の「理由付き sorry」は段階 II では使わない：濃度評価や S1 の生成系を待つ `isSheaf_arc_iff_cech` のように今は閉じられない宣言は、drafts に残す（本体に移すのは sorry 0 で閉じた宣言だけ）。ファイルを分ける必要があれば、drafts 側を「移したもの」と「残るもの」に分けてよい。移し終えた drafts のファイルは消す。
4. **E3 非依存**：新しいファイルとその import から `BhattScholze/Inputs/PerfectoidizationInterface` に届かないこと（drafts/README「ファイル順序」の規則。BS-W10 作業 A で解消済み）。監査で `sorryAx` が出たら E3 への依存を疑う。
5. **停止点**：§1〜§4 の停止点で報告する（`report-codex-w11.md` に追記し、`math/bs-impl` にコミット）。**取り込み**は調整役が A-2・B-2・B-3・C-2・D-2 の各停止点で行う（sorry 0 のファイルだけ）。新規モジュールは入口（`BhattScholze.lean`・`CommutativeAlgebra.lean` など）と監査（`scripts/audit_bhatt_scholze*.lean`）に登録し、監査を単独で流す。
6. **条件付きの事前承認**：型の停止点（A-1・B-1・C-1・D-1）は、主張が drafts の型と同じなら報告して待たずに証明へ進んでよい。型を変える必要があれば止める（原典どおりの定義を変えない。避けられない差は D 番号でユーザーに相談するので、報告に書く）。証明の停止点は「対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない」なら次の作業へ進んでよい。
7. **ビルド**：小さなビルドだけ（`ps -axo command= | grep '[l]ake build'` が空で、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build …` で鍵が取れること）。main の作業木では作業しない。

## 7. 追記（2026-11-07、調整役）：⑤a のこの後の予定

BS-W11 の後、⑤a は次の順で進む（指示書は調整役が順に出す。今は読むだけでよい）。

1. **BS-W12（BM18 の経路 B）**：完全環の arc 被覆で構造層の Čech 複体が完全（G-A6-1 `cech_exact_of_arcCover_perfect`、BS 著者版 Prop 8.10 の証明の中の主張）を、可換環論で直接示す。部品 B1〜B6（Čech の完全性の API、付値環の Milnor 列と完全代数、付値環の性質、超積、A → ∏ W_t が v 被覆、組み立て。`bhatt-scholze/notes/citations-survey-2026-11-05.md` §2）。作業 B の付値環（G-A6-3・G-A6-6・1c）を使う。最後の組み立て B6 は ⑥ の BS17 Thm 4.1 (i) を待つ。
2. **BS-W13（A8-1・A8-2）**：§10 の古典的な部分。A8-1 は J_perfd を一般の J に（Def 10.1）、Lemma 10.3 の一般の J、Prop 10.4 の複体版、Lemma 10.5（drafts/A8/AlmostConnectivity）。A8-2 は Thm 10.9 の J-almost 連結性の部分（drafts/A8/AlmostPurityConnectivity）。どちらも本体の Derived・André・semiperfectoid だけを使い、∞ の供給も E3 も待たない。作業 C（G-A8-6、有限エタールの perfectoid 性）が A8 の前段。

これで、論文の §10 の目標に必要な項目は Thm 10.11（E3 の integral の欄。導来の perfectoid 化と Cor 8.12 を待つ）以外が埋まる。

作業 A〜D の中で、後の BS-W12・BS-W13 で使う形（付値環の補題、有限エタールの perfectoid 性）は、使う側を意識した一般性で置く。

## 8. 追記（2026-11-07 15 時、調整役）：濃度の評価と忠実平坦性の扱い

drafts の `exists_perfectoid_arcCover`（drafts/A6/ArcSite.lean、BS 著者版 Lemma 8.8）は、arc site を κ-small に保つため、主張に濃度の上界 #T ≤ (#S + ℵ₀)^ℵ₀ を含む。§1 の「濃度評価は後回し可」で drafts に残した次の二つは、**作業 D で Lemma 8.8 を閉じる前に閉じる**（作業 D の最初の段として扱う）：

1. `rootClosure_cardinal_le`（作業 A）
2. `baseExtension_cardinal_le`（作業 B）

`baseExtensionUnit_pCompletelyFaithfullyFlat`（一般の S での忠実平坦性、作業 B）は、Lemma 8.8 の証明（arc 被覆であること）が使うかを作業 D の型の停止点 D-1 で確かめる。使うなら作業 D で閉じ、使わないなら drafts に残して理由を報告に書く。

濃度の評価が予想以上に重い場合（基数の算術で詰まる場合）は、止めて報告する。

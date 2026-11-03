# drafts：BS の設計段階の Lean の骨組み（ビルドしない）

概要：E3 を消す道筋（stage2 の A 案）の設計段階で書く Lean の骨組み。主張の型と `sorry` の証明だけで、**ビルド・`lake env lean`・監査を
一切行わない**（coordination.md §1 の BS の行、2026-11-02）。`SerrePositivity/` の外にあるので root からも監査からも届かない。
方針：各ファイルは、将来置かれる場所のモジュール名を先頭のコメントに書く（例：`SerrePositivity.InfinityCategories.Sheaves.SheafCondition`）。
import 行は現時点の main の名前で書く（基準コミットは下の表）。論文の層の整理（2a・2b）や ∞ の束で名前が変わったら、調整役から回る
旧→新の対応表で直す（`scripts/move_module.py` が自動で直すこともある）。
規約：docstring は README の Conventions（概要／方針／規約／使われ方）。宣言名は内容の名前（原典の番号は docstring に）。
`sorry` には理由を一行添える（「S3 の補題を待つ」「2b の後に HA を読んでから」など）。新しい `axiom` は置かない。
使われ方：中身を書く段階（暦に載せてから）で、該当するファイルを `SerrePositivity/` の下の決まった場所へ移し、単体の `lake build` で確かめる。
設計書は [infinity-sheaves-design.md](../infinity-sheaves-design.md)・[a0-design.md](../a0-design.md)。

| ディレクトリ | 将来の置き場所（調整役の決定、main d9254e8b0） | 設計書の単位 |
| --- | --- | --- |
| `Sheaves/` | `SerrePositivity/InfinityCategories/Sheaves/`（層の順序 StablePresentable < Sheaves < ModelBridge。最初のファイルで `scripts/refactor/layers.json` に登録） | S1〜S6 |
| `DerivedSheaves/` | `SerrePositivity/InfinityCategories/Derived/Sheaves/` | S7（D(A) への適用） |
| `A0/` | `SerrePositivity/BhattScholze/Prismatic/`（仮） | A0-1〜A0-4 |
| `A1/` | `SerrePositivity/BhattScholze/Prismatic/`（仮） | A1-1〜A1-4 |
| `A2/` | `SerrePositivity/BhattScholze/Prismatic/Derived/`（仮） | A2-1〜A2-4 |
| `A3/` | `SerrePositivity/BhattScholze/Prismatic/Derived/`（仮） | A3-1〜A3-4 |
| `A4/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（既存の Interface.lean の隣。E3 の欄の構成なので Prismatic/ ではなく Perfectoidization/。調整役了承、main 431c40741） | A4-1〜A4-4 |
| `A5/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（A4 と同じ仮置き） | A5-1〜A5-4 |
| `A6/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（A4 と同じ仮置き。arc site は BS 固有の扱い）。Prop 8.10 の引用 3 件の `sorry` 定理は drafts/ の間は問題なし。`SerrePositivity/` に入れるときは `scripts/make_area_audits.py` の許可一覧の更新が要る（調整役に知らせる、main 7b8b96286） | A6-1〜A6-4 |
| `A7/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（A4 と同じ仮置き）。`AnimatedDomain.lean`（G-A7-1）・`DiscreteCore.lean`（G-A7-5）は A5 が import する共有部分で A5 より先に置く（W9-II-24）。所有は A7 | A7-1〜A7-2 |
| `A1/CrystallineInput`・`A4/AfterComparison`・`A5/RootAdjunction`・`A5/PerfectSite` | 各 A 番号の置き場所と同じ。W9-III-09 で先行の定義と後段の定理を分けた（下の「ファイル順序」） | A1-3／A1-5、A4-3／A4-4、A5-4、A5-1 |
| `A8/` | A8-1・A8-2 は `SerrePositivity/BhattScholze/Almost/`（既存の almost の隣）、A8-4 は `Perfectoidization/Derived/`（調整役了承、main 26f9f7fc5）。A8-3（Lemma 10.12）は `CommutativeAlgebra/UniversalHomeomorphism/`（普遍同相の一般論）と `CommutativeAlgebra/EtaleStratification/`（層別の本体）に、2a の後に新規ファイルだけで入れる（論文の層へ名前を予約）。独立した Codex の単位、担当は 2a の後。それまで drafts/A8/ のまま | A8-1〜A8-4 |
| `A9/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（組み立て）と Inputs/PerfectoidizationInterface.lean の証明の置き換え（中身の段階、暦に載せてから） | A9-1 |
| `Sheaves/SpaceValued` | S8（調整役の決定、main 7b8b96286、infinity-foundation-plan.md の M12e）：(1) 空間の層化・(5) 局所性・(6) 元の圏上の極限は `InfinityCategories/Sheaves/SpaceValued/`、(2) 離散の層化＝1 圏・(3) 単射に沿う押し出しは `Sheaves/Discrete/`、(4) の一般部分（HTT 5.1.5.6 の極限保存延長、el(F) 上の極限）は M12b と同じ `F2/`。前提に G13（𝒮 の presentable 性）と S4 の非安定版。時期・担当は M12 と同じ。それまで drafts/Sheaves/ のまま | S8 |
| `Shared/Descendable` | `SerrePositivity/EInfinity/Descendable/`（新設。CAlg と D(A) の両方を使う。調整役の決定、main 86acd98db、infinity-foundation-plan.md の M15）。E∞ を使わない thick ⊗-ideal・index・安定性の部分は Derived/ へ下ろしてよい。時期・担当は M14 と同じ（段 G、A5 の中身を書く段階）。それまで drafts/Shared/ のまま | G-A5-1 |
| `DerivedGeneral/` | `SerrePositivity/InfinityCategories/Derived/`（調整役の決定、main 600e578d7、infinity-foundation-plan.md の M13。Derived は HA を import 済みなので PDCompletion への依存は可。一般の t 構造の定義を切り出すなら Stable/）。時期は段 G、W2b の後。CompletionFunctor は 2b の改名表を受けてから。それまで drafts/DerivedGeneral/ のまま | G-A2-2・G-A2-3 |
| `Shared/` | 共有層（調整役の決定、main 26f1f4d94）：cup 積・Bockstein は `HomologicalAlgebra/Cosimplicial/`、de Rham は `CommutativeAlgebra/DeRham/`（いずれも新設、HA の第一層＝一般論の扱い）。移すのは 2b の後。名前は論文の層に予約してもらう。それまで drafts/Shared/ のまま | G-A1-1・2・9 ほか |
| `Shared/EInfinityPowerOperation` | `SerrePositivity/EInfinity/PowerOperation/`（新設、BarrattEccles・Operad の隣。調整役の決定、main 431c40741、infinity-foundation-plan.md の M14）。Barratt–Eccles の作用の型はそこで確認。時期は A4 の中身を書く段階、担当（E2 レーンか BS か）はそのとき決める。それまで drafts/Shared/ のまま | G-A4-1 |

| 基準コミット | 日付 | 内容 |
| --- | --- | --- |
| 972bb7f53 | 2026-11-02 | 最初の骨組み（S1・S2）。InfinityCategories の名前はこの時点の main |

## ファイル順序（W9-III-08・09、2026-11-03）

**E3 非依存の規則**：drafts と、それらが import する本体のモジュールから `Inputs/PerfectoidizationInterface` へ到達してはならない（Inputs の証明を Assembly に置き換えると循環する）。
現行の本体では `Perfectoidization/CompletedTensor` → `Derived/IntegralExistence` → `Inputs` の経路があり（有限直積 `isIntegralPerfectoid_finPi` が E3 を使う）、
A6/ArcSite・A6/ArcSheafProperty・A8/AlmostConnectivity（Lemma103 経由）がこれに当たる。2a 後に Fontaine の芯を E3 非依存のモジュールへ切り出す（a9-design §7、調整役へ依頼）。

**drafts 内の順序**（→ は「先に置く」。同じ A 番号でも定義を先行ファイルへ、後段の定理を後に）：
1. Sheaves/・DerivedGeneral/・Shared/ → A0 → A1/CrystallineInput → A1/{HodgeTateMap,HodgeTateComparison} → A2 → A3
2. A7/AnimatedDomain（A5 より先）
3. A4/Perfectoidization（`prismaticPerfection_filteredColimit` もここ：A2 の sifted 余極限保存・塔の余極限・完備化の反射性だけで示す、W9-III-14）→ **A7/DiscreteCore（A4 の後、A5 より先）** → A4/InterfaceFields（定義。Prop 8.5 を使わない）
4. A5/RootAdjunction（定義のみ）、A5/PerfectSite（site・比較写像・Čech データ `perfUnder_cechNerveData`：既存 Cor 7.3 の普遍環から直接、W9-III-14）→ A5/SemiperfectoidCase → A1/DeRhamComparisonPoly（A1-5。RootAdjunction・HodgeTateComparison を使う）→ A5/StrongDescent
   → A5/WeaklyInitialAndDescent → A5/PerfectSiteComparison（Prop 8.5 と系。A5 の最後）→ A5/InterfaceLimitCone
5. A4/AfterComparison（`e3Perfd_eq_direct`・Example 8.3）
6. A6/ArcSite → ArcSheafProperty → SheafOfSetsExcision → Excision；A7/AnimatedPerfectoidization → UniversalProperty（A6 と A7 は互いに独立）；A8/AlmostConnectivity → AlmostPurityConnectivity、A8/Stratification（独立に先行可）→ A8/IntegralDiscreteness → A9/Assembly
基盤・A0〜A3 の内部順序（Codex W9 第 3 部続き 3 の表）：Sheaves/SheafCondition → GlobalSections・CechConerveLimit → CAlgValued・SpaceValued；Shared/CosimplicialCupProduct → CosimplicialBockstein、DeRhamPolynomial、CosimplicialEInfinity（CAlgValued・CechConerveLimit の後）→ EInfinityPowerOperation、Descendable；A0/PrismaticSite → PrismaticEnvelope → CechAlexander；A2/AnimatedAlgebra → DerivedPrismaticCohomology → HodgeTateFiltration → BaseChangeAndTensor；A3/DiscreteCase → LciAndQuasiregular。
中身の段階で `lake build` の前に、import の到達性（`scripts/` の道具）でこの DAG と E3 非依存を確認する。

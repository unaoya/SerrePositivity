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
| `A0/` | `SerrePositivity/BhattScholze/Prismatic/`（仮）。PrismaticSite（A0-1）・PrismaticEnvelope（A0-3a・3c）・CechAlexander（A0-2）・FlatDescent（A0-3b・3d、11-07 新設）・BaseChange（A0-4、11-07 新設）。FlatDescent の `IsCompletelyFlatObject` と BaseChange の `HasFiniteCompleteTorAmplitude`・Lemma 4.22 は名前空間 `InfinityCategories.Derived` の純代数で、`InfinityCategories/Derived/`（M13 の隣）へ移す候補（調整役の判断待ち） | A0-1〜A0-4 |
| `A1/` | `SerrePositivity/BhattScholze/Prismatic/`（仮）。**11-07（D68 改訂）**：結晶の黒箱 `crystalline_deRham_polynomial_Zp` を削除し、`hodgeTate_iso_polynomial_Zp` を CrystallineInput の六段（Lemma 5.4・C^•/p → D^•/p ← D_0^•/p・pd Poincaré と BdJ・Cartier・生成元の照合、mod p）で証明する骨組みに。恒久の引用なし（a1-design §10）。**11-07（§10.5、D69 は関手の同型のまま）**：DeRhamComparisonPoly の `deRham_iso_polynomial_universal` を、大きい模型（`bigCechAlexander`・`wittBigPdModel`、Q^∧ の元すべてを変数にする枠）と C 上の小さい模型の厳密な自然変換の zigzag `bigZigzagIso` で組む骨組みに（`wittComposite` はその成分に定義し直し、旧 `WittComparisonLegs`・`wittPdBridge` は削除）。一般の J つき pd 包・枠の pd Čech 脈体・表示によらない補題・C 上の de Rham の関手同型 `pdDeRhamFunctorIso` は CrystallineInput、∞ 側の部品（厳密な自然変換の辺・余単体的 cdga の Tot・Tot と係数制限）は Shared/CosimplicialEInfinity の末尾。**11-07（a1-design §11、D25 改訂）**：`CrystallineSite`（新設）に結晶 site の最小限（affine な big site `CrysOver`・Zariski 位相・O_crys・`crystallineCohomology`、(a) Čech–Alexander `crystallineCechIso`・(b) Poincaré 補題・(c) Thm 5.2 の多項式の場合・(d) 関手性）。先頭の S3 の pro 版（`exists_limitCone_of_proCech`）は中身の段階で Sheaves/CechConerveLimit へ | A1-1〜A1-6 |
| `A2/` | `SerrePositivity/BhattScholze/Prismatic/Derived/`（仮） | A2-1〜A2-4 |
| `A3/` | `SerrePositivity/BhattScholze/Prismatic/Derived/`（仮） | A3-1〜A3-4 |
| `A4/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（既存の Interface.lean の隣。E3 の欄の構成なので Prismatic/ ではなく Perfectoidization/。調整役了承、main 431c40741） | A4-1〜A4-4 |
| `A5/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（A4 と同じ仮置き） | A5-1〜A5-4 |
| `A6/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（A4 と同じ仮置き。arc site は BS 固有の扱い）。Prop 8.10 の引用 3 件の `sorry` 定理は drafts/ の間は問題なし。`SerrePositivity/` に入れるときは `scripts/make_area_audits.py` の許可一覧の更新が要る（調整役に知らせる、main 7b8b96286） | A6-1〜A6-4 |
| `A7/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（A4 と同じ仮置き）。`AnimatedDomain.lean`（G-A7-1）・`DiscreteCore.lean`（G-A7-5）は A5 が import する共有部分で A5 より先に置く（W9-II-24）。所有は A7 | A7-1〜A7-2 |
| `A1/CrystallineSite`（11-07 新設） | A1 と同じ（仮に `BhattScholze/Crystalline/Site`、調整役の判断待ち）。CrystallineInput の後、HodgeTateComparison・DeRhamComparisonPoly の前 | A1-6 |
| `A1/CrystallineInput`・`A4/AfterComparison`・`A5/RootAdjunction`・`A5/PerfectSite` | 各 A 番号の置き場所と同じ。W9-III-09 で先行の定義と後段の定理を分けた（下の「ファイル順序」）。CrystallineInput は HodgeTateMap の後、HodgeTateComparison の前（11-07：η⁰・η¹・`HodgeTateIsoStatement` を使う） | A1-2／A1-3／A1-5、A4-3／A4-4、A5-4、A5-1 |
| ~~`A6/PerfectoidFiniteProduct`~~ | **本体に入った（11-04、BS-W10 作業 A、main cc67ea88e）**：`SerrePositivity/BhattScholze/Perfectoid/FiniteProduct.lean`。drafts からは削除 | G-A6-12 |
| `A8/` | A8-1・A8-2 は `SerrePositivity/BhattScholze/Almost/`（既存の almost の隣）、A8-4 は `Perfectoidization/Derived/`（調整役了承、main 26f9f7fc5）。A8-3（Lemma 10.12）は `CommutativeAlgebra/UniversalHomeomorphism/`（普遍同相の一般論）と `CommutativeAlgebra/EtaleStratification/`（層別の本体）に、2a の後に新規ファイルだけで入れる（論文の層へ名前を予約）。独立した Codex の単位、担当は 2a の後。それまで drafts/A8/ のまま。**11-13 追記**：A8-3 は BS-W10 作業 B で本体に入り（main 4019014a1）、drafts/A8/Stratification は削除。BS-W13（main 1d9eb11ee・1c36c06c3）で A8-1 の Prop 10.4 複体版・Lemma 10.5 などは `BhattScholze/Almost/`（AlmostConnectivity・AlmostTensor・AlmostTensorForward・AlmostGenerators・CompletedModuleTensor・FiniteEtaleComparison）、A8-4 の部品は `Perfectoidization/Derived/`（IntegralClosureCompletion・PerfectoidFilteredColimit・IntegralApproximation・IntegralClosureApproximation）に入った。drafts/A8 に残るのは AlmostConnectivity（底変換での反映など）・AlmostPurityConnectivity・IntegralDiscreteness と、接続の型の W13AssemblyInputs | A8-1〜A8-4 |
| `A9/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（組み立て）と Inputs/PerfectoidizationInterface.lean の証明の置き換え（中身の段階、暦に載せてから） | A9-1 |
| `Sheaves/SetSections` | `SerrePositivity/InfinityCategories/Sheaves/SetSections`。S4・S8 共通の BS 側ラッパーと比較：指定錐版の切断、表現可能重み、篩の添字圏、`restrictionCone` との接続。F2 の一般 API の配置は変更しない。証明本文は未ビルド | S4・S8 |
| `Sheaves/SheafGenerators` | `SerrePositivity/InfinityCategories/Sheaves/Sheafification`（S4、M12a、BS）。11-05 新設：篩の元の圏と制限図式、Γ(h_U, F) → Γ(S, F) と `restrictionCone` の接続、検出族と生成辺 S ⊗ M → h_U ⊗ M、層化の存在（GlobalSections・SpaceValued から移した）。G8 の自然な別版（IF-G2）待ち | S4 |
| `Sheaves/SpaceValued` | S8（調整役の決定、main 7b8b96286、infinity-foundation-plan.md の M12e）：(1) 空間の層化・(5) 局所性・(6) 元の圏上の極限は `InfinityCategories/Sheaves/SpaceValued/`、(2) 離散の層化＝1 圏・(3) 単射に沿う押し出しは `Sheaves/Discrete/`、(4) の一般部分（HTT 5.1.5.6 の極限保存延長、el(F) 上の極限）は M12b と同じ `F2/`。前提に G13（𝒮 の presentable 性）と S4 の非安定版。時期・担当は M12 と同じ。それまで drafts/Sheaves/ のまま | S8 |
| `Shared/Descendable` | `SerrePositivity/EInfinity/Descendable/`（新設。CAlg と D(A) の両方を使う。調整役の決定、main 86acd98db、infinity-foundation-plan.md の M15）。E∞ を使わない thick ⊗-ideal・index・安定性の部分は Derived/ へ下ろしてよい。時期・担当は M14 と同じ（段 G、A5 の中身を書く段階）。それまで drafts/Shared/ のまま | G-A5-1 |
| `DerivedGeneral/`（Truncation・CompletionFunctor・ScalarRestriction（11-03 追加：係数制限の ∞ 関手 f_*、基盤待ち）） | `SerrePositivity/InfinityCategories/Derived/`（調整役の決定、main 600e578d7、infinity-foundation-plan.md の M13。Derived は HA を import 済みなので PDCompletion への依存は可。一般の t 構造の定義を切り出すなら Stable/）。時期は段 G、W2b の後。CompletionFunctor は 2b の改名表を受けてから。それまで drafts/DerivedGeneral/ のまま | G-A2-2・G-A2-3 |
| `Shared/` | 共有層（調整役の決定、main 26f1f4d94）：cup 積・Bockstein は `HomologicalAlgebra/Cosimplicial/`、de Rham は `CommutativeAlgebra/DeRham/`（いずれも新設、HA の第一層＝一般論の扱い）。移すのは 2b の後。名前は論文の層に予約してもらう。それまで drafts/Shared/ のまま | G-A1-1・2・9 ほか |
| `Shared/EInfinityPowerOperation` | `SerrePositivity/EInfinity/PowerOperation/`（新設、BarrattEccles・Operad の隣。調整役の決定、main 431c40741、infinity-foundation-plan.md の M14）。Barratt–Eccles の作用の型はそこで確認。時期は A4 の中身を書く段階、担当（E2 レーンか BS か）はそのとき決める。それまで drafts/Shared/ のまま | G-A4-1 |

| 基準コミット | 日付 | 内容 |
| --- | --- | --- |
| 972bb7f53 | 2026-11-02 | 最初の骨組み（S1・S2）。InfinityCategories の名前はこの時点の main |
| cc67ea88e | 2026-11-04 | BS-W10 作業 A：CompletedTensor から E3 依存を外し、有限直積を `BhattScholze/Perfectoid/FiniteProduct`（E3 非依存の直接証明、sorry なし）へ。drafts/A6/PerfectoidFiniteProduct を削除。drafts 111 起点から E3 に到達しない |
| b2ef94226 | 2026-11-07 | A0 の区分 D（2b が main に入った後）：A0/FlatDescent（Lemma 3.7(2)(3)、Cor 3.12）・A0/BaseChange（Tor 振幅、Lemma 4.22、Lemma 4.20 の多項式代数の場合）を新設。HA/DerivedCompletion は 2b 後の main の名前 |
| 3e27dda00 | 2026-11-03 | ∞ W2b の取り込み。drafts の import 行は調整役が機械的に書き換え（対応表 `scripts/refactor/targets/w2b-r37.json`・`w2b-r38.json`・`w2b-r73.json`・`w2b-section18-placement.json`）、Sheaves/GlobalSections の衝突は BS の追加行と書き換えの両方を残す。BS 側で追加確認：11-02 に Core へ下りた 6 モジュール（`Stable.{TrivialFibrationCocone,UniverseSquareHom,FiniteShapes,PushoutShape}`、`F2.FilteredExchange.FilteredInfinity`、`F2.CatInfinity.NativeConeLeg`）への旧名 import が 11-03 の BS-D2・D3-02・D5 で 10 ファイル 12 行入っていた（機械書き換えの対象外）ので `Core.*` に直した。全 import の解決を確認。`F2.IsFilteredInfinity` の名前空間は Core でも `F2` のまま |

## ファイル順序（W9-III-08・09、2026-11-03）

**E3 非依存の規則**：drafts と、それらが import する本体のモジュールから `Inputs/PerfectoidizationInterface` へ到達してはならない（Inputs の証明を Assembly に置き換えると循環する）。
現行の本体では `Perfectoidization/CompletedTensor` → `Derived/IntegralExistence` → `Inputs` の経路があり（有限直積 `isIntegralPerfectoid_finPi` が E3 を使う）、
A6/ArcSite・A6/ArcSheafProperty・A8/AlmostConnectivity（Lemma103 経由）がこれに当たる。2a 後に Fontaine の芯を E3 非依存のモジュールへ切り出す（a9-design §7、調整役へ依頼）。

**drafts 内の順序**（→ は「先に置く」。同じ A 番号でも定義を先行ファイルへ、後段の定理を後に）：
0. ~~A6/PerfectoidFiniteProduct~~（本体 `BhattScholze/Perfectoid/FiniteProduct` に入った、11-04）
1. Sheaves/・DerivedGeneral/・Shared/ → A0 → A2/{AnimatedAlgebra,DerivedPrismaticCohomology} → A1/HodgeTateMap → A1/CrystallineInput → A1/CrystallineSite → A1/HodgeTateComparison → A2 の残り（HodgeTateFiltration・BaseChangeAndTensor）→ A3
   （11-07 訂正：HodgeTateMap は A2/DerivedPrismaticCohomology の `polyCosimplicialAlgebra` を、CrystallineInput は HodgeTateMap の `htRings`・`reducedModel`・η⁰・η¹・`HodgeTateIsoStatement`・`formVars` を使う）
   （11-07、a1-design §11：CrystallineSite は CrystallineInput の `pdCechNerve`・`pdModel_iso_pdCechNerve`・`pdDeRhamFunctorIso`・`formsVertex`・`deltaCopies`・`pdDeltaModel`・`crystallineBridge`（(c) の η との関係 `crystallineBridge_eq_eta`）、A0/PrismaticEnvelope の `completedFreeDelta`・`completedFreeDeltaBase`、A2 の `coefficientPresentable`・`polyCosimplicialAlgebra`・`prismaticCohomologyCAlg_eq_totEInfinity`、A0/PrismaticSite の `cutoff`、Sheaves の S2・S3・CAlgValued、DerivedGeneral/ScalarRestriction の `cAlgRestrictScalars` を使う。どれもこの順の前にある。DeRhamComparisonPoly の各対象での可逆性の証明の筋が CrystallineSite を使う）
   （11-07、a1-design §10.5：CrystallineInput は Shared/CosimplicialEInfinity の `strictShapeNerve`・`strictNatTransFunctorIso`・`totCDGAFunctor` を、DeRhamComparisonPoly は A0/CechAlexander の `cechAlexander`・`hasEnvelopes_of_polynomial` と A2 の `polyCosimplicialAlgebra`・`polyCompletion` も使う。どれも既にこの順の前にある）
2. A7/AnimatedDomain（A5 より先）
3. A4/Perfectoidization（`prismaticPerfection_filteredColimit` もここ：A2 の sifted 余極限保存・塔の余極限・完備化の反射性だけで示す、W9-III-14）→ **A7/DiscreteCore（A4 の後、A5 より先）** → A4/InterfaceFields（定義。Prop 8.5 を使わない）
4. A5/RootAdjunction（定義のみ）、A5/PerfectSite（site・比較写像・Čech データ `perfUnder_cechNerveData`：既存 Cor 7.3 の普遍環から直接、W9-III-14）→ A5/SemiperfectoidCase → A1/DeRhamComparisonPoly（A1-5。RootAdjunction・HodgeTateComparison を使う）→ A5/StrongDescent
   → A5/WeaklyInitialAndDescent → A5/PerfectSiteComparison（Prop 8.5 と系。A5 の最後）→ A5/InterfaceLimitCone
5. A4/AfterComparison（`e3Perfd_eq_direct`・Example 8.3）
6. A6/ArcSite → ArcSheafProperty → SheafOfSetsExcision → Excision；A7/AnimatedPerfectoidization → UniversalProperty（A6 と A7 は互いに独立）；A8/AlmostConnectivity → AlmostPurityConnectivity、A8/Stratification（独立に先行可。11-13：本体に入り削除）→ A8/IntegralDiscreteness → A9/Assembly（11-13：A8/W13AssemblyInputs は本体だけを import する接続の型で、AlmostPurityConnectivity・IntegralDiscreteness の前）
基盤・A0〜A3 の内部順序（Codex W9 第 3 部続き 3 の表）：Sheaves/SheafCondition → SetSections・GlobalSections・CechConerveLimit → SheafGenerators・SpaceValued → CAlgValued；Shared/CosimplicialCupProduct、DeRhamPolynomial（古典的な Bockstein は本体の `HomologicalAlgebra/Cosimplicial/BocksteinClass`）、CosimplicialEInfinity（CAlgValued・CechConerveLimit の後。11-07：末尾の係数制限の節が DerivedGeneral/ScalarRestriction を使うのでその後）→ EInfinityPowerOperation、Descendable；A0/PrismaticSite → PrismaticEnvelope → FlatDescent → CechAlexander → BaseChange（FlatDescent は Envelope を使わないが、Prop 3.13(1) の一般形で Envelope が Lemma 3.7(2) を使うならこの順。`flatTopology_refine` は中身の段階で FlatDescent の後へ）；A2/AnimatedAlgebra → DerivedPrismaticCohomology → HodgeTateFiltration → BaseChangeAndTensor；A3/DiscreteCase → LciAndQuasiregular。
中身の段階で `lake build` の前に、import の到達性（`scripts/` の道具）でこの DAG と E3 非依存を確認する。

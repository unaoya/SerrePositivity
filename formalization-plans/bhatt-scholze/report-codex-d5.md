# BS-D5 基盤側 drafts の報告

## 第 1 部　停止点 1・DerivedGeneral

開始基準は main `dc77a84dd`。入口表 §1.1〜§1.3 の 14 件を具体化した。開始基準で結論が `True` だった宣言を一件と数え、分割・補助宣言は重ねて数えていない。

| ファイル | 件数 | 具体化した宣言 |
| --- | ---: | --- |
| `CompletionFunctor.lean` | 5 | `completion_isReflective`、`completion_tensor_koszul`、`completion_exact`、`complete_colimit`、`completedBaseChange` |
| `Truncation.lean` | 5 | `truncationLE_counit`、`truncation_cofiber`、`tStructure_axioms`（直交性・shift・分解に分割）、`truncationLE_of_isConnective`、`derived_nakayama` |
| `ScalarRestriction.lean` | 4 | `derivedInfinityBaseChange_restrictScalars_adjunction`、`cAlgBaseChange_restrictScalars_adjunction`、`derivedInfinityRestrictScalars_completion`、`cAlgRestrictScalars_h0` |

### 定義と新設した入口

* **CompletionFunctor**　`completeAt a x` は A2 と同じ主元の `IsComplete`、`IsDerivedComplete A s x` は有限集合 `s` の各元での完備性。既存の `completeSubcomplex` と `completion` に `s` を渡す。新設は `completeAt`、`completionReflection`、`completionUnit`、`cAlgCompleteSubcomplex`、`cAlgCompletionReflection`、`cAlgCompletion`、`cAlgCompletionUnit`。二つの反射は随伴を含み、単位にはその `.unitHom` を使う。`complete_colimit` の結論の圏は完備部分圏。`completion_tensor_koszul` は生成元の列と `Set.range a = ↑s` を受け、単位を代表する辺の鎖写像を `koszulFunctor` で写したホモロジー射の `IsIso` を述べる。
* **Truncation**　新設は `componentEdge`、`truncationLE_counit_h`、`truncationLE_step`、`truncationLE_step_counit`、`discreteModuleEmbedding`、`cohomologyLayer`、`tStructure_orthogonal`、`tStructure_shift`、`tStructure_decomposition`。切り捨ての隣接射と余単位の合成を指定し、その射の cofiber を Hⁿ(X)[−n] と比較する。コホモロジーには一般基盤の `derivedInfinityHomology`・`derivedInfinityHomologyMap` を使う。BS 界面の `H` と同じ導来同値・ホモロジー関手である。`derived_nakayama` の入力は `s`、その列表示、完備性、semifree 代表の `koszulComplexOn` の全ホモロジーの消滅。
* **ScalarRestriction**　二つの随伴と完備化比較は、単位や比較射を取り出せるデータを返す。新設は `cAlgH0Ring`、その `CommRing`・`Algebra S` インスタンス、`cAlgRestrictScalars_h0_base`。A4 と同じ cofibrant 代表の実際の H⁰、`homologyCommRing`、`homologyAlgebra` を使った。最後の補題は H⁰ の環同型と基底環の構造射の可換性を指定する。

### A 側の呼び出しと渡す引数

行番号は A 側の開始基準。実コードで呼び出している場合と、証明の穴・説明から今後接続する場合を区別した。

| A 側 | 基盤の入口と接続 |
| --- | --- |
| A2/DerivedPrismaticCohomology:58,63,70–74、A2/HodgeTateFiltration:52,58,60 | A2 の `completeAt` は基盤と同じ引数順。主元なら `completionReflection k {p}`、二元なら `cAlgCompletionReflection A {p,d}` の左随伴・単位を使う。二元集合での所属と A2 の連言の同値で部分圏を対応させる。 |
| A1/CrystallineInput:130、A1/DeRhamComparisonPoly:44–50、A1/HodgeTateComparison:220–225 | A1 が A2 の `completeAt` を使う箇所。`primeAlgReflection` は `cAlgCompletionReflection k {p}`、`moduleReflection` は `completionReflection A {p,d}` の特殊化。 |
| A2/BaseChangeAndTensor:25,83–86,98–104 | `completedBaseChange f s` は D(A) → D(B) の `derivedInfinityBaseChange f ≫ completion B (s.image f)`。A2 での同名参照は説明のみ。`completedPrismBaseChange` の実コードは CAlg の包含・`cAlgBaseChange f.toRingHom`・標的の反射を合成する。`perfectBaseComparison` の証明では `(cAlgBaseChange_restrictScalars_adjunction f.toRingHom).unitHom` を使う。 |
| A2/HodgeTateFiltration:91,97–101,138–151 | `truncationLE A i` は従来どおり。`hodgeTatePoly_bounded` では `truncationLE_of_isConnective A n x hx` の余単位の可逆性から頂点同型を得る。`hodgeTateTower` の穴から `truncationLE_step A i`・`truncationLE_counit A i` と合成式を使う。`truncation_cofiber A n x` が隣接段の比較。 |
| A4/Perfectoidization:155,202–211 | `reflectCompleteCAlg` は CAlg 反射の第 1 射。`restrictFrobeniusTowerColimit` は既存の `cAlgRestrictScalars_isColimitCone_of_bijective`（完全基底の Frobenius）。`restrictFrobeniusCompletion` の台は `derivedInfinityRestrictScalars_completion φ I J h`、ここで I = J = {p,d}、h は φ(I) と J の生成イデアルの根基の等号。CAlg の比較は忘却との両立と完備反射の普遍性で持ち上げる。 |
| A4/Perfectoidization:252,266–272 | 三件目の `restrictH0Equiv f x` は `cAlgRestrictScalars_h0 f x`、`restrictH0Equiv_base` は `cAlgRestrictScalars_h0_base f x`。A4 の `cAlgH0Algebra` は構造射も束ねた `A_R A`。台の環と代数構造を基盤から取れる。 |
| A5/StrongDescent:126–128 | `prismScalarExtension q` が選ぶ左随伴の証人は `cAlgBaseChange q` と `cAlgBaseChange_restrictScalars_adjunction q`。忘却後の比較は既存の `cAlgBaseChange_forget q`。 |
| A5/SemiperfectoidCase:150–158、A5/StrongDescent:111–121 | `derived_nakayama A s a ha x hx hKos` は消滅判定。前者の d 進の場合は一元の列。後者の上界判定では Koszul の filtration と完備性も使う。いずれも証明の方針からの参照。 |

`cAlgH0Algebra` の型や引数は今回変えていない。中身の段階で環の台を読み替える箇所は A4/Perfectoidization:252,260,267,271–272,277,306,322,336、A4/InterfaceFields:199,206,233、A5/SemiperfectoidCase:176,206、A7/DiscreteCore:55–56,69、A7/UniversalProperty:47、A8/IntegralDiscreteness:113,128,327。上記以外の 14 件の旧名への直接呼び出しは A0〜A9 で見つからなかった。

### 入口表の訂正・要確認・検査

* **D5-01**（`761bf6a19`）　`derivedSuspensionShiftObjectIso` により Σ = [1]。したがって ΣX の上界は n−1。τ^{≤n}X → X の cofiber は τ^{≥n+1}X で、同じ正方形が pullback にもなる。
* **D5-02**（`f7cfe33e5`）　`discreteEmbedding` の始域は通常の A 代数。加群の埋め込みを `nerveMap (moduleSemifreeResolutionFunctor A) ≫ closedNerveInclusion A (Semifree A)` で定義した。停止点 2 の完備微分形式にもこの入口を使える。shift は hD(A) 上の `loopFunctor`／`suspensionFunctor` を対象に反復している。
* 今回の未確定名・× として残した宣言は 0 件。反射・切り捨て・係数制限の証明は M13／M13-CAlg 待ち。draft 同士の import は従来どおり、取り込み先が決まるまで依存先をコメントで指定した。
* コメントを除いて開始基準と照合し、DerivedGeneral の結論 `True` は 14 → 0。drafts 全体では 53 → 39（Shared 28、Sheaves 11）。実 import のパス、括弧、新規 axiom がないこと、`git diff --check` を確認した。ビルド・Lean の型検査は行っていない。

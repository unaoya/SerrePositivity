# SC-W1 停止点 2a — BS17 Thm 4.1 (i) の affine・構造層の場合

2026-11-07。作業基点は main の `b5c6cbff2`。対象は G-A6-1a の有限 affine 族。以下は固定済みの Lean API の照合と紙の証明案で、各段の Lean 検証は今後行う。

## 1. 引き継ぎとの差分と準備

- `4adf352c` から基点まで、`KST/SchemeLemmas/` と `KST/Descent/GenericFiniteFlattening.lean` に入った数学の追加はゼロ。前者の 6 ファイルで `f00bad23f` と `7242dc7f7` が import を更新した。現行パスは `CommutativeAlgebra.Adic.Completion.Tensor`、`CommutativeAlgebra.Adic.Completion.Algebra`、`CommutativeAlgebra.HilbertSamuel.Graded.Subquotient`。ルートはすでに `SerrePositivity.KST.SchemeLemmas` を import している。
- F-2 の `scripts/refactor/targets/f-namespace-map.json` の `rows` に、上記二箇所の移名はない。表が対象とする ∞ 側の宣言への依存も今回の経路には置かない。以下の L7 名は現行の宣言名。
- `math/scheme` と専用 worktree を作成。依存パッケージは専用 worktree に複製し、成果物キャッシュを共有した。 `LAKE_ARTIFACT_CACHE=true`、`LAKE_RESTORE_ARTIFACTS=true`、`LAKE_CACHE_DIR=~/.cache/lake` を確認。鍵経由の `lake build SerrePositivity.KST.SchemeLemmas` は成功（3708 jobs）。単独の `lake env lean scripts/audit_kst_scheme_lemmas.lean` は成功（2003 宣言、標準三公理のみ）。
- Mathlib の照合は lock 済みの `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。以下の不足はソース照合による。段 2a で追加した Lean 宣言はゼロ。

| 現行の入口 | 使える範囲と次の一歩 |
| --- | --- |
| `KST.SchemeLemmas.GenericFreePolynomialQuotient.exists_nonzero_free_polynomial_quotient_localization`（宣言の namespace は `SerrePositivity.KST.SchemeLemmas`） | 整域上の多項式商の局所化が自由。任意の有限型代数へ移すには商と局所化・テンソルの比較が要る。2b の最初の保存単位。 |
| `KST.Descent.GenericFiniteFlattening` の `exists_nonzero_away_free_of_finite` と `KST.SchemeLemmas.NoetherianFiniteModuleFlattening` の `exists_noetherian_finite_flattening_center` | 基底環上で有限な加群に適用できる。今回の射のアフィンチャート環は基底上有限型で、基底加群としての有限性は一般には得られない。 |
| `KST/SchemeLemmas/SplitAlgebraFreeOpenBlowup.lean` の `exists_fg_center_boundaryFreeOpenPullbacks_of_projective` | 実分裂の代わりに基底上の射影性を渡せる。05FS から射影性の入力を供給し、0810・0811 の自由部分と台の次元帰納へ接続する。 |
| `SchemeBlowup.lean`、`FlatStrictTransform.lean`、`StrictTransformDomination.lean` | blowup、中心外同型、strict transform、admissible blowup の合成を再利用できる。`exists_domination_of_flat_schematicallyDense_strictTransform` は稠密開上の同型と平坦な strict transform を仮定する 081T の末尾。BS17 Lemma 2.6 に直接要る出力は、固有全射を平坦化した strict transform とその全射性。 |

## 2. 段 2b・2d — 平坦化と BS17 Lemma 2.6

1. **一般平坦性。** 051R の有限型代数の場合から、被約 Noether 基底の各既約成分の一般点近傍で平坦な開を取る。成分間の交わりを除き、有限アフィン被覆に共通な稠密開に縮める。同じ操作を補集合の被約閉部分スキームで反復すると有限の平坦層化が得られる。05FS はこれとは別に、平坦有限表示代数の射影性を作るために使う。既存の局所化・完備化・忠実平坦降下を 05FS の残りの帰納と接続する。[051R](https://stacks.math.columbia.edu/tag/051R)・[05FS](https://stacks.math.columbia.edu/tag/05FS)・[平坦層化](https://stacks.math.columbia.edu/tag/0H3Z)
2. **必要な平坦化の出力。** 有限型 `𝔽ₚ` 上の被約基底、有限表示の分離射、稠密な準コンパクト開 U 上で平坦、という入力で U-admissible blowup と平坦な strict transform を作る。一般有限型加群への帰納は証明の内部で要る。0815 の相対正規化（38.3.2）、strict transform と有限押し出しの比較、0810・0811 の自由化、一般点で自由な部分を抜いた余核の台の次元降下、局所で得た中心の大域化が残る。Noether 基底では strict transform の有限表示性は固有射または有限型射と Noether 性から従う。中心の補集合と U の整合、blowup 後も U が稠密であることを出力に含める。081T の modification 支配の完成はこの出力の依存から外せる。[0810](https://stacks.math.columbia.edu/tag/0810)・[0811](https://stacks.math.columbia.edu/tag/0811)・[0815](https://stacks.math.columbia.edu/tag/0815)・[081T](https://stacks.math.columbia.edu/tag/081T)
3. **固有全射から帰納レベル。** 有限型 `𝔽ₚ` 基底で次元帰納。まず被約化する。次元 0 では各有限体上の非空なファイバーから有限拡大上の点を選び、それらの直和を有限忠実平坦な細分にする。正次元では 1・2 を適用。blowup の射は固有で稠密な U を像に含むので全射。blowup の任意の点に U 内の一般化を取り、基底変換された固有全射でその特殊化を持ち上げると strict transform が全射になる。この射は閉部分スキームを介する固有射で、2 の平坦性により proper fppf。補集合 Z の次元は下がり、例外部分 E → Z へ帰納を適用できる。レベルの証人は基底変換できる。今回の判定には有限型 `𝔽ₚ` 上でのレベルで足りる。任意の qcqs 版には有限表示の固有全射のモデル化がさらに要る。[BS17 §2](https://arxiv.org/pdf/1507.06490#page=5)・[Rydh §3](https://arxiv.org/pdf/0710.2488)

## 3. 段 2e・2f — Gabber の四角形

### Mathlib の足場

| 部品 | 固定版にあるもの | 今回追加する範囲 |
| --- | --- | --- |
| 準連接層と層コホモロジー | `AlgebraicGeometry/Modules/{Sheaf,Tilde}` の `Scheme.Modules`、`tilde`、`tildeEquiv`、`isQuasicoherent_iff_isIso_fromTilde`。 `CategoryTheory/Sites/SheafCohomology/` の一般のコホモロジー、完全列、Čech 複体 | 準連接層の affine 消滅、分離 qc スキームの有限 affine Čech 計算、係数の短完全列、閉埋め込み・平坦制限・Frobenius と両立する比較。Čech 複体の定義とコホモロジーの計算は別の仕事。 |
| 固有射と有限性 | `AlgebraicGeometry/Morphisms/{Proper,Finite,Flat,QuasiFinite}`、`ValuativeCriterion`、`ProjectiveSpectrum/Proper`。環論の Rees 代数と Noether 性 | 固有射のコホモロジーの有限性、コホモロジー版 Artin–Rees、Stein 分解の既成定理は確認できなかった。下記の H⁰ の案なら Stein 分解を独立に構築する必要がない。 |
| 完全化 | `PerfectRing` と `RingTheory/Perfection.lean` の `Perfection` | ここで要るのは **順極限** `A → A → ⋯`。Mathlib の `Perfection` は Frobenius の逆極限。順極限の普遍性、完全性、有限積・テンソル・局所化との比較を整備する。 |
| 二重複体 | `CechNerve`、`AlternatingFaceMapComplex`、`HomologicalBicomplex`、`TotalComplex`、`SheafCohomology/Cech` | 第一象限の行・列ごとの擬同型を Tot に渡す補題、分裂増大の縮約、混合 Čech の比較。 |

### 紙の証明

- affine 基底 Y = Spec A、閉部分 Z = Spec(A/I)、固有全射 X → Y、Y − Z 上の同型、Eₙ = X ×ᵧ Spec(A/Iⁿ) とする。有限 affine Čech は有限交叉が affine なので、係数の短完全列・局所化・直和を項別に扱える。通常のコホモロジーの有限性は射影の場合の標準開被覆・捻り層・有限生成加群から始める。任意の固有射へ拡張する場合は Chow の補題と台の帰納が別途要る。今回の帰納四角形で使う X → Y は blowup のファイバー冪で、射影の場合で足りる。これは 2e の範囲を狭める提案であり、固有射の一般形も実装対象とする場合は工数を別に取る。[Stacks 02O6](https://stacks.math.columbia.edu/tag/02O6)
- 02O7 の入力は `𝒪_X` に対する 30.20.4 (1),(3)。`⊕ Iⁿ𝒪_X` の相対 Spec は Rees 基底へ変換した X の閉部分スキーム。そこでコホモロジー有限性を使うと `⊕ Hⁱ(X,Iⁿ𝒪_X)` が Rees 環上有限。斉次生成元の次数の上界と長完全列から、制限の核の `I^(n−c)Hⁱ` への包含、および十分大きい m に対する `Hⁱ(Eₘ) → Hⁱ(Eₙ)` の像の安定化を得る。逆極限を取った形式関数定理までは使わない。[Stacks 02O7](https://stacks.math.columbia.edu/tag/02O7)
- **正次数。** `Hⁱ(X,𝒪_X)` は有限で、D(I) に制限すると零だから I の一様な冪で消える。十分大きい n で (1) から `Hⁱ(X) → Hⁱ(Eₙ)` は単射。 `pᵉ ≥ n` なら Eₙ の Frobenius の e 回反復は E₁ を経由するので、E₁ への制限の核は Frobenius 順極限で消える。逆向きは、E₁ 上の類を Frobenius で Eₘ へ移し、(3) によりその Eₙ への制限を X 上の類で持ち上げる。したがって正次数の完全化後の制限は同型。[BST13 v3 Lemma 3.9 (1)](https://arxiv.org/pdf/1307.3763v3#page=13)
- **H⁰ の短縮案。** B = Γ(X,𝒪_X)、D = Γ(E₁,𝒪) と置く。(3) を n=1 に用いると、D の元の十分高い Frobenius 冪は B から来る。逆に b ∈ ker(B → D) なら、`pᵉ ≥ n > c` で b の `pᵉ` 乗は Eₙ で零、(1) から IB に属する。従って `(B/IB)^perf ≅ D^perf`。B は A 上有限、`B/A`（A の像による余核）は D(I) で零なのである n について `IⁿB ⊂ im(A)`。 `A → B` の核は全射性から冪零元のみ。B と A/I の完全化の元が B/IB 上で一致したら、同一 Frobenius 段にそろえて A/I 側を A に持ち上げる。B 側との差は追加の Frobenius 後に IB に入り、さらに冪を上げると `IⁿB` に入る。これで差も A から持ち上がり、`0 → A^perf → B^perf ⊕ (A/I)^perf → D^perf → 0` が完全。Stein 分解・Kollár の商を経由せず、BST13 v3 (2) の結論を (1),(3) の評価で得る提案。任意の普遍同相の完全化の定理はこの H⁰ の計算には不要。判定の nilimmersion では affine の冪零元が Frobenius 順極限で消えることを使う。[BST13 v3 Lemma 3.8–3.9 と Remark 3.10](https://arxiv.org/pdf/1307.3763v3#page=12)
- 以上を restriction の差を取る写像にまとめる。H⁰ の短完全列と正次数の同型を長完全列に入れれば、`C(Y) → Cone(C(X) ⊕ C(Z) → C(E))[-1]` は擬同型。ここで C は次節の同じ前層複体を用いる。単にコホモロジー群が同型という記録だけでは、Čech の全次数にわたる図式に使えない。[BS17 Lemma 4.6 (i)](https://arxiv.org/pdf/1507.06490#page=16)

## 4. 段 2g — v 被覆の細分・近似

- affine の付値試験は draft と同じく任意の階数の付値整域と忠実平坦な拡大で書く。局所な単射の付値環準同型は捩れなしで平坦かつ閉点を持ち上げるので忠実平坦。逆向きには最大イデアルの収縮と単射性を使う。固有全射の付値試験は、一般ファイバーの点から分数体拡大を取り、付値を延長して固有射の付値判定を使う。Mathlib の `IsProper.eq_valuativeCriterion` と `ValuativeCriterion.Existence.of_specializingMap` 周辺の特殊化・付値環 API を再利用できる。定義、基底変換、合成、細分を別補題にする。[BS17 Def 2.1](https://arxiv.org/pdf/1507.06490#page=4)・[Rydh Cor 2.9](https://arxiv.org/pdf/0710.2488)
- Rydh 3.12 の出力は「開被覆の後に固有全射」。判定の証明には 3.10 の「fppf の後に固有全射」で十分。3.12 そのものへ進むなら準切断と準有限射の有限化も必要。さらに Noether 基底の 3.6 だけから任意の affine 基底の Lemma 2.12 を引くと循環する。BS17 は先に任意 affine 基底の 3.12 を適用し、細分のデータを有限段へ降ろしている。[Rydh §3](https://arxiv.org/pdf/0710.2488)・[BS17 Lemma 2.12](https://arxiv.org/pdf/1507.06490#page=9)・[Stacks 38.35.3](https://stacks.math.columbia.edu/tag/0EUZ)
- **必要な細分を Noether 平坦化から作る案。** 有限表示の affine v 被覆 X → Y を有限型 `𝔽ₚ` の affine モデル X₀ → Y₀ に降ろす。この段ではモデルが v 被覆であるとは仮定しない。Y₀ を被約閉部分の有限列で層化し、各差 Uᵢ 上で X₀ が平坦となるようにする。各 Uᵢ は対応する被約閉部分 Sᵢ で稠密に取る。各 Sᵢ で 2d を適用し、射影 blowup Tᵢ → Sᵢ と平坦有限表示の strict transform Qᵢ → Tᵢ を得る。
- Y へ引き戻した Tᵢ の中で、Uᵢ の逆像のスキーム論的閉包 Cᵢ を取る。この取り直しにより、非平坦な基底変換で稠密性が失われる場合も扱える。Cᵢ の任意の点には Uᵢ 上の一般化がある。付値環でこの特殊化を実現し、元の v 被覆で持ち上げる。持ち上げた付値環は整域なので、その一般点が strict transform に入れば全体が入る。従って Cᵢ は Qᵢ の引き戻しの像（開集合）に含まれる。Cᵢ の Y への固有な像は Uᵢ の Y 上の逆像を含み、i 全体で Y を覆う。
- Cᵢ の定義イデアルを有限型の部分イデアルで近似する。像の開集合の補集合は準コンパクトなので、Cᵢ を含み、なお Qᵢ の像に入る有限表示閉部分 T′ᵢ を取れる。有限個の T′ᵢ の直和 T′ → Y は射影全射、Q ×ₜ T′ → T′ は fppf、合成は X を経由する。T′ の閉埋め込みの有限個のデータをモデルへ降ろす。射影全射と fppf の全射性は、閉補集合または構成可能な非像の極限判定で有限段へ降りる。Mathlib の `Scheme.Hom.isConstructible_image` と構成可能位相を再利用候補にする。これで有限型 `𝔽ₚ` 上の v 被覆モデルを得る。有限表示でない affine 射は、まず基底上の有限表示代数の filtered colimit にする。各因子は元の被覆により細分されるので v 被覆。この二段階で Lemma 2.12 に必要な系を得る。上の閉包・有限型イデアル近似・モデルへの降下が実装上の検証点。非 Noether 版の平坦化や TIC を展開する場合との比較はここで行う。[Stacks 38.34.1](https://stacks.math.columbia.edu/tag/0ETQ)・[有限型部分加群による近似](https://stacks.math.columbia.edu/tag/086M)
- **既存の近似 API。** `AffineTransitionLimit` に `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`、`Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`、`Scheme.OpenCover.exists_of_isCofiltered_of_finite`、`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`、`nonempty_isColimit_Γ_mapCocone`、`exists_mem_of_isClosed_of_nonempty` がある。これらは固定された図式に対する射・有限開被覆・等式・切断の降下の足場。有限表示スキーム全体のモデル化や v 被覆性の降下そのものは別の補題。 `SpreadingOut` の `spread_out_of_isGermInjective` は点でのデータを近傍へ広げる定理で、基底の余フィルター系を取る Noether 近似とは役割が違う。

## 5. 段 2g・2h — 全次数の判定と affine への出口

**複体で可能。** 第一象限の Tot を使えば ∞ 圏を経由せずに今回の §2 の判定を示せる。以下の C の候補と比較を最初の実装の区切りにする。

1. **厳密に関手的なモデル。** 固定した `𝔽ₚ` 上の qc 分離スキームの fppf サイト上で、加法層 𝒪 の一つの入射分解 J を取る。Mathlib の `AlgebraicGeometry/Sites/Fpqc.lean` に `Scheme.fppfPrecoverage`、`Scheme.fppfTopology` と subcanonical 性があり、制限サイトとアフィン直線で表現される 𝒪 の加法層をつなぐ。Frobenius はこの分解の鎖写像として持ち上げ、各 X で `C(X) = colim_F J(X)` とする。一つの分解を評価するので、X に関する Čech の余単体恒等式は鎖写像として成立する。各入射層の被覆 Čech は、被覆の自由加群層の増大複体が層として局所分裂して完全であることから完全。Tot と正確な filtered colimit を使い C の fppf 降下を得る。
2. **C の計算。** affine fppf 族では有限積による忠実平坦環準同型の Amitsur 複体を使う。忠実平坦基底変換で増大が分裂する。`Module.FaithfullyFlat.lTensor_exact_iff_exact` などを使い、項を通常のテンソル冪と比較する。これで affine の正次数の消滅を示すには、コホモロジー類を消す有限 affine fppf 被覆を選び、低次数の消滅から帰納して Čech 二重複体を比較する。分離 qc では有限 affine 開被覆とその交叉で C を計算できるため、通常の準連接層の Čech 計算と Frobenius 順極限に比較できる。特に affine では自然な `A^perf[0] → C(Spec A)` が擬同型。この比較を使って §3 の四角形を C の鎖写像の四角形にする。
3. **細分と合成。** `D(f)` を `C(Y) → Tot C(X_•/Y)` が擬同型とし、任意の基底変換で成立する場合を普遍降下とする。h = g ∘ f に対し、Z 上の二つの Čech 脈体の積 `X_Z^{a+1} ×_Z Y_Z^{b+1}` を使う。X の各冪の上で g の引き戻しには切断がある。h が普遍降下ならもう一方向でも列ごとの擬同型を得て、g の降下が従う。逆に g と Y 上での h の引き戻しが普遍降下なら、同じ比較で h の降下が従う。f が普遍降下なら、h の Y への引き戻しは f で細分されるのでこれを適用できる。すべての比較を基底変換後にも使う。被覆を一つ細分しただけで任意の前層の Čech 完全性が移る、という主張は使わない。
4. **帰納四角形。** affine 基底上でレベルの帰納を行う。非 affine 基底は有限 affine 開被覆による fppf 局所判定に帰着する。nilimmersion と proper fppf の因子は処理済み。残る X → Y の各 Čech ファイバー冪にも §3 の四角形を適用し、例外部分は E → Z の Čech ファイバー冪となる。各次数の mapping fiber を Tot に通す。帰納仮定により下辺 Z の増大が擬同型だから、上辺 X の増大も擬同型。これで BS17 Lemma 2.10 と Thm 2.9 のうち必要な方向が出る。
5. **近似と完全環。** §4 の有限段の affine 被覆に適用。各 Čech 項は有限テンソル冪なので filtered colimit と両立する。完全化も順極限であり、増大複体の完全性は項ごとの正確な filtered colimit に移る。第一象限の各全次数には有限個の成分しかないため、無限の積と filtered colimit の交換は要らない。これが Cor 2.14–2.15 の今回の代用。Prop 4.5 のうち、完全環のテンソル冪に対する比較だけを使う。完全化は完全環への左随伴で、テンソル積上で両因子の Frobenius の逆が基底と両立する。有限積も完全。Lemma 3.4 の平坦性を独立に供給するなら、完全化した B を `colim_n (A^perf ⊗_{A,n} B)` として平坦性を出し、Spec の同相から忠実性を得る。上記の fppf 計算では普通の Amitsur に Frobenius 順極限を取るため、この比較を先に一般スキームで証明する必要はない。[BS17 §2–4](https://arxiv.org/pdf/1507.06490)
6. **draft との照合。** `B = ∏ Bᵢ` とし、`Spec B` の有限余積と付値整域の連結性で有限族の付値試験を一射に移す。幾何側は零環を含むので `ZMod p` 代数として扱い、零環上でも p 乗写像を定義する。Lean の `[CharP A p]` は p が素数なら A の非自明性を含意する（`CharP.nontrivial_of_char_ne_one`）。したがって draft の型へは `CharP`・`PerfectRing` から特殊化する。空の族で被覆なら基底は空で、幾何側で処理できる。 `Arrow.augmentedCechConerve` の余面をテンソル冪への単位の挿入に比較し、`AugmentedRingCechExact` の単射性、次数 0、全正次数へ変換する。最終出力は [ArcSheafProperty.lean の G-A6-1a](../../bhatt-scholze/drafts/A6/ArcSheafProperty.lean#L108) を閉じられる型にする。

## 6. 停止点で決めることと規模

- **配置の境界。** 2d の再利用候補は `KST/SchemeLemmas/` にある。現規則では `AlgebraicGeometry/` は KST を import できず、そのままでは 2g の判定を無条件の 2h に接続できない。一般の複体判定を `AlgebraicGeometry/` に置くことはできる。無条件の 2h まで同じ層で閉じるには、調整役が必要な blowup・strict transform・平坦化の依存閉包を下層へ移す保存比較の束を決めるか、明示的な接続モジュールの置き場を決める必要がある。段 2b で得る K 非依存の新しい環論は低い層に置く方針がこの問題を小さくする。
- **実装範囲の提案。** 2d は Noether 基底上の平坦化と proper fppf 細分まで。2e はまず射影射、2f は Stein 分解を外した H⁰ の証明、2g は Rydh 3.12 のうち Lemma 2.12 と判定に必要な fppf・固有全射の細分まで。一般の固有射の有限性、Stein 分解、開被覆を返す完全版 3.12 も成果物に含める場合は、この経路の外側の工数として別に扱う。
- **粗い見積もり。** 既存 L7 を使う前提で、2b は 10–25 時間。2d は旧見積もりの 24–60 時間を下限側の目安とし、相対正規化・中心の大域化の不足で増える可能性がある。追加 Lean は 2e で 0.8–2.5 万行（射影版の有限性と Rees）、2f で 0.2–0.7 万行、2g で 1–4 万行（付値・近似・サイトの複体を含む）、2h で 0.1–0.4 万行。これは依存層の不足を含めた概算で実測値ではない。任意の固有射・完全版 Rydh まで含む場合は別積算。最大の不確実性は射影コホモロジーの有限性と、細分データのモデル化。
- **次の保存単位。** 051R の多項式商と局所化／基底変換の比較を先に実装し、有限型代数の一般自由性に移す。並行する実装判断は上記の配置と 2e・2g の範囲。

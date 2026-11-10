# BS-W15 段 0 報告（停止点 0）

2026-11-10。⑤c、`math/bs-classical`、基準 `d39908253`。本体・drafts の型を静的に照合した。原典は著者版（当 worktree に PDF がないため、指定 PDF を隣の main worktree から読み取りのみ）。以下の型は紙上の案。行数は証明と docstring を含む概算。

## K1 — r 元の分冪包（Lemma 2.36・2.38、Cor 2.39）

- **既存**。 `Delta/DividedPower/PDivision` の `pDivisionFactorialSubring_eq_raw_range`、`pDivisionFactorialDelta`、`pDivisionFactorialIdealDividedPowers` は任意の族。階乗部分環の標的への普遍性 `existsUnique_pDivisionFactorialDPMorphism` は標的の p 正則性を使う。 `PrincipalDP` の `principalDPPresentation_p_mul_injective`、`principalDPFactorialEquiv`、`principalDPBaseChangeUniversalEquiv` は一元。 `FreeDPBasis`・`FreeDPBaseChange` に自由分冪代数の基底と底変換、`Delta/Division/Family`・`BaseChange` に生の δ 除算の族と押し出しがある。 `Andre/Envelope/PDivision` の `deltaPDivisionRaw_p_mul_injective` は一元で、`pDivisionFactorialSubring_eq_raw_range` だけでは生の包の単射性は出ない。
- **⑤b の既存特殊例**。 `CrystallineAffineDivision.crystallineAffineFrobeniusDivision_primeRegular` は有限個の頂点差の完備自由 δ 環における p 正則性を既に示す。 `crystallineRawPDFactor`・`CrystallineRawPDSplit` は未完備の分冪因子との照合、`PDCompletedCech` は完備模型。これらを再実装せず、共通の一般論を下に置く。 `items.csv` の 2.36 の「r=1 だけ」はこの特殊例については古い。 `pdEnvelope_eq_frobeniusDivision` は a1-design 上の予定名で、現行 drafts に同名の型は見当たらない。
- **型案**。 `P_r := ℤ_(p)[X_i]`、`G_r := Γ_{ℤ_(p)}(⊕ᵢ ℤ_(p)eᵢ)`（(X_i ↦ γ_1(e_i))）、`D(B,f) := B ⊗[P_r] G_r`（(X_i ↦ f_i)、(i : Fin r)）。B が p 正則、`IsKoszulResolution (fun i ↦ f̄ i)` on B/p の下で、(i) `∀ n, Subsingleton (TorAlg … (n+1) …)`（B と G_r の高次 Tor）、(ii) D(B,f) の p 正則性、(iii) (D(B,f)) が ((f_i)) の分冪包（係数と各分冪を保つ普遍性）、(iv) `B' ⊗[B] D(B,f) ≃ₐ[B'] D(B', f')`。表示環の底変換は任意の環射について示し、分冪包との照合に B′ 側の同じ仮定を使う。 (i) のために Koszul 複体で (γ_1(e_i)-f_i) を解像し、mod p の分冪基底を (P_r/p/(X_i^p)) 上の自由基底にまとめる。Koszul 正則性の冪への移行を使い、mod p と p 反転の計算を合わせる。分冪包の普遍性は p ねじれのある標的にも述べる。分冪基底の積と分冪の恒等式で表示関係を処理する。
- **δ 側の型案**。 `A{φ(f)/p}` は既存の `DeltaAdjoinDivision D (p : A) (fun i ↦ D.frobeniusLift (f i))`。自由 δ 座標 (f=X) で生の包の p 正則性と (D(A,X) ≃ₐ[A] A{φ(X)/p}) を先に閉じる。 `freeDeltaFrobenius_isCompletelyFaithfullyFlat`、`crystallinePrimeRegular_of_isPushout`、局所化、分冪基底を使い、原典の ℤ_(p) と ⑤b が使う ℤ_p の両方を得る。任意の A へ (X_i ↦ f_i) の押し出しを取り、Lemma 2.38 の計算を適用する。Cor 2.39 は A/p 上の正則列を仮定し、δ 構造と有限 δ 表示（r 変数・r 個の δ 関係）を同時に与える。
- **置き場所・規模**。 `Delta/DividedPower/{RegularSequencePD,FrobeniusDivisionPD}.lean` と必要なら Koszul の小補題。3〜5 ファイル、約 800〜1,500 行。順序は自由変数の未完備版 → 一般 r 元 → 底変換・完備模型への適用。⑤b への受け渡しは生の包の同型とその標準脚。 `CrystallineSite` の `pdDeltaCechNerve`・`etaBridge`、`DeRhamComparisonPoly` の比較に使える。 `CrystallineInput.exists_completedPDEnvelope` の任意の基底分冪イデアル・任意の K に対する存在は別の主張であり、K1 の正則列の定理から直接は出ない。

## K2 — 普遍 distinguished 環と向き付き prism（Ex 2.21・3.4）

- **既存と型案**。 `FreeDeltaRing`、`DeltaStructure.localization`、`frobeniusDenominators` と `deltaPDCompletionStructure` を使う。 `drafts/A1/HodgeTateComparison` の `universalDistinguishedRing`、`distinguishedDelta`、`rawOrientation` と `universalOrientedPrismRing := PDCompletionH0 …` の模型を採る。Ex 2.21 の普遍性は p 局所な δ 環 D と distinguished な x について `∃! f : U₀ →+* D, IsDeltaHom … f ∧ f d₀ = x`。Ex 3.4 は draft と同型の `universalOrientedPrism`、`universalOrientedPrism_bounded`、`universalOrientedPrism_hom`（生成元を指定した一意な prism 射）。(p,d) の正則性に加え (U/d) の p 正則性を明示し、`universal61` に供給する。
- **証明と型の差**。自由座標で (p,d) の正則性を確認し、局所化と二元の完備化で保つ。完備性・写像は `pdCompletionH0_self_complete_p`・`_d` と `existsUnique_deltaPDCompletionHom`、(p ∈ (d,φ(d))) は δ(d) の単元性から得る。原典の Frobenius は (U/p) 上で **d 完全平坦**。型案は Frobenius で制限した加群について `IsCompletelyFlat (Ideal.span {d̄}) …`。 `FreeDeltaFrobeniusFlat` の剰余自由性を局所化し、Frobenius が (d̄ ↦ d̄^p) とすることを使って d 進完備化へ移す。draft の `universalOrientedPrism_frobenius_flat : FrobeniusFlatModP …` は通常の `Module.Flat` という強い型。Construction 6.1 で必要な完全平坦性との接続は承認事項。A1 の型は⑤c で編集しない。
- **置き場所・規模**。 `Delta/Distinguished/Universal.lean` と `Prism/Basic/UniversalOriented.lean`（必要なら Frobenius を分離）。2〜3 ファイル、約 450〜850 行。

## K3 — 相対完全正則性と δ 押し出しの Koszul 計算（Def 2.42、Rem 2.37）

- **既存と型案**。 `koszulComplex`、`KoszulIdealAction`、`KoszulBaseChangeNaturality`、`Koszul/Resolution` を使う。 `drafts/A0/PrismaticEnvelope.IsCompletelyRegularRel` と `drafts/A1/HodgeTateComparison.FlatKoszulComparison` は同じ D20 の条件。一般の有限生成列 (a) と追加の有限列 (x) について、`H₀(K(B;a,x))` が `H₀(K(A;a))` 上平坦、かつ全 j で標準射 (H_j(K(A;a)) ⊗_{H₀(K(A;a))} H₀(K(B;a,x)) → H_j(K(B;a,x))) が全単射。係数環への作用は Koszul の零ホモトピーから降ろす。完全正則性の定義には B の導来完備性も入れ、prism 用の `IsCompletelyRegularRel P x` は (a=(p,d)) に特殊化する。結晶 prism では基底の (H_1) が非零なので、正次数の消滅で定義すると D20 に反する。
- **Rem 2.37 の型案**。自由 δ 環の r 元の押し出しの二脚 (y_i↦φ(x_i))、(y_i↦p z_i) に対し、高次の `TorAlg` の消滅と H₀ の生の商への同定を述べる。有限段の Koszul 解像では (δ^k(y_i-pz_i)) を各座標の初期区間で取り、三角変数変換で通常の多項式解像を得る。Frobenius 底変換後は mod p の平坦性と p 反転での解像から全段の非零次数消滅へ進み、有限段の余極限で全 δ 関係を扱う。既存の `deltaPDivisionFirstRelation_pair_isKoszulResolution` は一成分の最初の関係と p の組。K1 と共有する冪・Tor の補題は段 1 で必要なものから作る。 `Koszul/Powers` の弱正則列向け結果だけでは一般環上の Koszul 正則列を覆えない。
- **置き場所・規模**。 `CommutativeAlgebra/KoszulRegular/{Powers,Relative}.lean`、`Prismatic/CompletelyRegular.lean`、`Delta/DividedPower/FrobeniusDivisionKoszul.lean` を候補にする。3〜5 ファイル、約 500〜1,000 行（K1 との共有分を除く）。

## K4 — 完全平坦性・平坦サイト・envelope（Lemma 3.7(2)(3)、Cor 3.12、Prop 3.13(2)、Ex 3.14）

- **3.7(2)(3)**。 `Prism/Bounded/Completeness.boundedPrism_pair_isAdicComplete` は (1)。 `CompletedFlatBoundedTorsion`・`CompletedFlatBoundedComparison`・`CompletedFlatRegularModule` と `CompletelyFlat` に加群の比較がある。 `FlatDescent.isDiscrete_of_completelyFlat_boundedPrism` の入力を通常の `DerivedCategory (ModuleCat A)`（またはその鎖複体模型）にし、導来完備かつ (M ⊗^L A/(p,d)) が平坦な加群の次数 0 集中、(H^0) の古典完備性、各 d 冪の正則性と (H^0/d^n) の有界 p 冪ねじれを示す。任意の複体に適用するため、既存の加群版に加えて (M⊗^L A/d^n) の離散性と d 進の塔の比較が要る。 (3) の `exists_boundedPrism_of_completelyFlat` は draft の型を採り、逆向きは `Hom.span_map_generator` と完全平坦性の定義。候補は `Prism/Bounded/CompletelyFlat.lean` と通常の導来圏の補題。
- **3.12**。本体の `PrismOver`・`IsAdmissibleCutoff` を使い、A0 設計どおり固定基底・濃度 cutoff 上で述べる。 `PrismOver.IsFaithfullyFlat`、`isFaithfullyFlat_of_isIso`、`IsFaithfullyFlat.comp`、`exists_isPushout_isFaithfullyFlat`、`flatTopology_refine`、`structurePresheaf_isSheaf` と剰余版は A0 の型を採る。押し出しは `PDCompletionH0 (B' ⊗[B] C) …`。K5 と共有する通常の δ テンソルの普遍性をここで先行し、完備化の普遍性と (2)(3) で押し出しを作る。 `Perfectoidization/CompletedTensor` の完全 prism 向け結果は部品の参照先。 `structurePresheafDerived_isLimit_singleton` の古典部分は「各完全忠実平坦な f の増大付き完備 Čech 余脈体の交代余面複体が全次数で完全」。各 ((p^n,d^n)) 商上で通常の Amitsur の収縮を忠実平坦性で降ろし、全射の塔から Milnor で戻す。剰余版は (B/d) と d 正則性を使う。 `Prismatic/{FlatPushout,FlatSite,AmitsurDescent}.lean` が候補。∞ 層と RΓ への接続は草稿側。
- **3.13(2) と 3.14**。本体の `IsPrismaticEnvelope`・`IsPrismaticEnvelope.unique`・`envelopeClosure` と `exists_prismaticEnvelope_of_variables` は使用可能。 `drafts/A0/PrismaticEnvelope.prismaticEnvelope_baseChange_of_variables` の型を最初に閉じ、一般形は完全平坦な δ-A 代数 B と envelope C、任意の有界 prism 射 (A→A') に対し、B′・C′ を各完備底変換、J′ を延長イデアルとし、可換な標準脚と `IsPrismaticEnvelope P' … J' … Q' η'` を返す。K3 の完全正則性は一般の存在を得るときの仮定。Ex 3.14 は (B₀→R) が全射、(B₀) が ((p,d)) 完全 smooth、R が (A/d) 上 p 完全 smooth、(B₀→B) が完全平坦という原典の仮定から、(J=ker(B→H⁰(R ⊗̂^L_{B₀} B))) の局所完全正則性と envelope の存在を返す案。通常の剰余上で smooth な全射の核を局所正則列で表し、完全平坦性と K3 で持ち上げる。一般の存在は変数模型だけでは出ず、局所正則列の δ 除算の完全平坦性と貼り合わせが要る。 `Prismatic/{EnvelopeBaseChange,SmoothEnvelope}.lean` 等が候補。 `drafts/A0/BaseChange` の Tot・cohomology の宣言は後段の利用側。
- **規模**。全体で 7〜12 ファイル、約 2,200〜4,200 行。最も不確かな見積もりは Ex 3.14 の完全 smooth から局所正則列を得る部分と一般の存在。変数版の型を保ち、一般化は別の定理にする。

## K5 — 離散 δ 構造・冪等分裂・lci envelope（Lemma 7.7・7.8、Ex 7.9）

- **7.7 の古典部分**。 `DeltaStructure.existsUnique_of_frobeniusLift`、`isDeltaHom_of_map_frobeniusLift`、`comapEquiv` を再利用。 `DiscreteCase.deltaStructure_of_discrete_pTorsionFree` に対応する古典型は、通常の p 正則な A 代数 C、基底と可換で mod p が p 乗の `φ : C →+* C` に対し、φ を持ち上げ基底を δ 射にする `∃! D : DeltaStructure p C, …`。 `deltaStructure_of_envelopeIso` は環同型・Frobenius・基底の可換性から δ を移送する同型版。評価脚については、基底・剰余・Frobenius と可換な自然な環射族から p 正則な標的への δ 射族を得る（D36）。 `discreteFrobenius_mod_p`・`prismMapOfDiscrete` が実際の Δ からこの入力を供給する部分は A2/G-A3-9 と G10 を使う草稿。単なる弱始性（各標的への射の存在）だけでは 7.8 は適用できない。
- **7.8**。 `DiscreteCase.initial_of_retraction_idempotent` の `F : C ⥤ Under X` と `F ⋙ Under.forget X = 𝟭 C` から F(X) の冪等射とその分裂である始対象を得る型を採る。 `prismOver_isIdempotentComplete` は像の δ 構造、完備性・正則性・有界性の retract への移行、剰余と R の脚、濃度を示す。p 正則な充満部分圏にも適用し、自然な評価族を入力とする `exists_initial_of_discrete` の古典部分を得る。一般圏論は `CategoryTheory/InitialOfRetraction.lean`、prism の適用は `Semiperfectoid/DiscretePrism.lean` を候補にする。
- **7.9 の envelope**。 `LciAndQuasiregular.IsKoszulRegularModGenerator`、`BoundedPTorsion`、`IsLciEnvelope` を入口とする。 `exists_lciEnvelope` の型を保ち、別に (R=A/(d,f)) の有界 p 冪ねじれの下で候補が有界で `PrismOver P R κ` の始対象になる形（必要な濃度仮定つき）を検討する。K2 の普遍基底 U₀ 上の完備自由 δ 環 (U=U₀\{f_i\}^∧) と変数 envelope E は `CompletedFreeDeltaFlat`・`VariableEnvelope` を使い、候補は `PDCompletionH0 (E ⊗[U] A) …`。 `lciTensorDelta`・`lciTensorDelta_map_iff` は通常のテンソル積に W₂ の切断を貼る型を採用（K4 と共有）。候補の環と普遍性を先に構成し、d 正則性と有界性を Koszul の比較で別に証明する。 `RootEnvelope/RawCompletion`・`PerfectPrism` に類似の完備化・正則性の証明があるが、完全基底や根の族の仮定は一般の lci に持ち込まない。A3 設計が候補の正則性に使う Δ の離散性の代わりに、通常の鎖複体でどの比較を証明するかは段 4 の難所。
- **G-A3-7 の切り出し**。現 draft `lci_envelope_surjective_invert_p_universal` は標的が実際の Δ̄ なので、その型のままでは A2 と G10 に依存する。古典部分は普遍変数の場合の比較先を通常の p 完備なフィルター付き環 C とし、(E/d → C) の分裂単射と、p 反転後の閉像、(gr¹) による稠密生成から `Function.Surjective` on ( (E/d)[1/p] → C[1/p]) を得る型。差商 (f_i/d) が (\bar f_i) の余法線類に写る計算は a3-design §8 の (D\tilde t=f_i-dz) を通常の bar/Čech 模型で行う。閉性は連続な retraction から、稠密性は有限段の生成と完備化から示す。実際の Δ̄ が必要なフィルトレーションと評価を持つこと、その比較でこの古典計算が使えることは drafts に残す。この分割と、`exists_lciEnvelope` の一般の型を Δ の離散性なしで閉じる経路は確認事項。
- **置き場所・規模**。 `Delta/Basic/Tensor.lean`（K4 と共有）、`Semiperfectoid/{DiscretePrism,LciEnvelope,LciEnvelopeInvertP}.lean` 等。4〜7 ファイル、約 1,100〜2,400 行。G-A3-7 の模型計算と一般の候補の正則性の見積もりには幅がある。

## ⑤b との照合と停止点

- ⑤b `math/bs-d68` は調査中に `7792e3499` から `b1dd16939` に進んだ。共通祖先 `a24fae02a` からの枝差分と⑤b worktree の未コミット差分を確認した。中心は pd 微分・de Rham 双複体・Cartier・Bockstein（`FreeDPDerivation`、`FreeDPIntegral`、`PDDeRham*`、`DeRham/Cartier*`）および A1 の `CrystallineInput`・`HodgeTateMap`。未コミットの `FinitePolynomialCartier` 等も含め、上記の新規候補パス、A0（`CechAlexander` を除く）、A3 とのファイル重複は現時点でない。
- 数学上の接点は K1 の自由座標・分冪模型。取り込み済みの ⑤b の特殊例を参照し、一般定理は ⑤c、A1 の比較・結晶サイト側への接続は ⑤b の持ち分。枝の取り込みはこの段では不要。
- 検収事項は K1 の一般 r 元の型と受け渡し順、K2 の Frobenius の型の差、K4 の通常の導来圏／Čech の型、K5 の G-A3-7 の切り出し。既存 draft の型変更が必要な箇所は停止して調整する。段 0 では報告のみ。ビルド・監査・Lean ファイルの編集は未実施。承認後に段 1（K1）。

## 段 1 の中間記録（2026-11-10）

- `math/bs-classical` に main `903ec3a0e` を fast-forward した。
- 本体に新規 7 モジュールを追加した。 `PrimeLocalIntegers`、`FrobeniusDivisionPD`、`TruncatedPolynomialBasis`、`Powers` は `3139c7f27`、`PrincipalReduction` は `259c41a97`、`RegularSequencePD` と `FreeDPModPBlocks` は `b21c5c0c2`。自由 δ 座標での生の除算の p 正則性、分冪表示と標的への評価・任意係数への底変換、標数 p での切断多項式環上の自由性、有限 Koszul 正則列の冪と主元の補題を得た。
- 7 モジュールの鍵付き対象ビルドと公開 39 宣言の監査を通過。公理は標準三公理（`propext`、`Classical.choice`、`Quot.sound`）のみで、`#print sorries` は 0。⑤b の `math/bs-d68`（`1fda57035`）との枝差分に候補パスの重複はなく、本体と草稿の 14 モジュールの推移的 import 314 件に ∞ 圏・E3 への依存はない。
- 一般列の分冪包との同定、高次 Tor の消滅、Frobenius 除算・完備化との照合が残る。証明候補 7 モジュールと監査案は `drafts/A0/W15K1/`。直近で `PrimeLocalFlat` の整数からのスカラー塔、`RegularSequencePDFactorial` の分冪写像の計算、`RegularSequencePDKoszul` の評価商の証明を修正し、次回の鍵付き検証でこの順に確認する。
- 修正後の再検証は共有ビルドロックの 30 分待機が満了した。停止点 1 の検収条件は未達で、段 2 は未着手。

## 段 1 の再開（2026-11-10）

- ⑤b の停止点 3 を含む main `09047a87e` を `4f729b6d7` で取り込んだ。D69 §3.4（main `07d9d2117`）に沿い、具体的な正則列の分冪包・Frobenius 除算を⑤cで扱い、任意の J つき分冪包・枠とサイトへの適用は⑤bの持ち分。自由分冪基底・底変換と結晶側の押し出しの p 正則性を既存宣言から使う。
- `PrimeLocalFlat`、`RegularSequencePDFactorial`、`RegularSequencePDKoszul` の対象ビルドと公開 10 宣言の監査を通過。これらは局所整数上の平坦性、階乗部分環の分冪包としての普遍性、標数 p での関係列の Koszul 正則性を与える。評価商には既存の `Section2.stage0BaseEquiv` を使った。
- `RegularSequencePDPrimeRegular` と `RegularSequencePDTor` の対象ビルドと公開 5 宣言の監査を通過。分冪表示の p 正則性、係数多項式環上の通常の押し出しと高次 Tor 消滅を得た。原典の多項式環への底変換と Frobenius 除算・完備化との同型は再検証中。

## 停止点 1（K1、2026-11-10）

- **Lemma 2.36**。 `freeCoordinateFrobeniusDivision_primeRegular` は自由多変数の生の Frobenius 除算の p 正則性を示す。`freeCoordinateFrobeniusDivisionPDEquiv` がその分冪表示との係数上の標準同型。既存の自由 δ 環と⑤bの結晶側の押し出しの正則性を使った。
- **Lemma 2.38**。 `dpFamilyUniversalTensorEquiv` と `dpFamilyUniversalTor_subsingleton` は、原典の多項式環上の通常の押し出しと高次 Tor の消滅。Tor の係数には ℤ₍ₚ₎ の `ULift` を用いた。`dpFamilyPresentation_primeRegular`、`dpFamilyFactorialEquiv`、`existsUnique_dpFamilyFactorialDPMorphism` が p 正則性と分冪包の普遍性を与える。`dpFamilyBaseChangeEquiv_generator` が任意の係数への底変換で標準分冪を追跡する。
- **Corollary 2.39**。 `frobeniusDivisionDPEnvelopeEquiv`、`frobeniusDivision_primeRegular`、`dpFamilyDelta_algebraMap` が正則列に沿う生の δ 除算、p 正則性、係数環の δ 射を与える。有限 δ 表示は既存の `DeltaAdjoinDivision` を使う。`frobeniusDivisionPDCompletionEquiv_base` が導来 p 完備化の H⁰ で係数脚との可換性を与える。D69 §3.4 の任意の J つき分冪包と枠・サイトへの適用は⑤bの持ち分。
- **検収**。本体の新規 14 モジュールの対象ビルドに成功し、公開 65 宣言を監査した。標準三公理のみ、`sorry` 0。推移的 import 324 件を照合し、∞ 圏・E3 への依存はない。既存の Lean ファイル・宣言と A1 の型は維持した。監査案は `drafts/A0/W15K1/AuditK1.lean`。段 2 は未着手。

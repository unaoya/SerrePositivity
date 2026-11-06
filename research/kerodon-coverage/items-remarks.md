### c00

122 項目すべてを判定し、出力の件数が入力と一致することを確かめた。範囲は 1.1.0.1〜1.4.3.7 で、ほとんどが Mathlib にある。
- 入力の text の切り出しが崩れている：参照だけの項目（例 1.1.3.8・1.1.3.11・1.2.1.13・1.1.6.9）では、最初の言及箇所が取られている。sub/*.html から「種類 番号 .」の見出しの所を取り直して照合した（out/st00.py）。
- 既存の表になかった、自前の見つけもの：
  - SerrePositivity/CategoryTheory/Simplex/GenRelEquivalence.lean の equivalence（SimplexCategoryGenRel ≌ SimplexCategory、sorry なし）。1.1.2.14 に当たり、Mathlib にはない。
  - InfinityCategories/Kan/PiZeroConstant.lean の discrete・component・homEquiv。1.2.1.18・1.2.1.19 に当たる（π₀ と定数単体的集合の普遍性）。
  - InfinityCategories/Derived/BoundaryFaceGluing.lean。1.1.4.13 の像の記述に当たる。
  - KST/Comparison/BarSegal.lean の monoidWordSimplex。1.3.2.5 の B_n M ≅ M^n に当たる。
- 1.2.5.10 の自前の宣言は、自前の商 KanHomotopyZero の上の主張。Mathlib の SSet.π₀ と同じものかは確かめていない。
- Mathlib の @[kerodon] 属性はこの範囲の tag には付いていない。
- 判定した宣言のファイルを grep した範囲では sorry はない。Archive/ に該当するものはなかった。
- 主な空白：
  - 連結成分の直和分解と π₀ の積保存（Mathlib の TODO）
  - Sing と単体群が Kan 複体であること
  - 次元 ≤1 の単体的集合と有向グラフの圏同値
  - Mon → Set_Δ
  - 自由な圏の特徴付け
  - |S| と π₀ の比較
- 記録の方法：出力は指示の Write ツールではなく、python のスクリプト out/gen00.py から書いた。場所は許された out/ の下。

### c01

入力の 128 項目はすべて判定し、出力の件数も 128 で一致しています。ファイルは Write ツールではなく python スクリプト（scratchpad/kerodon/gen_c01.py）で書きました。

範囲ごとの結果：
- 1.4.4〜1.4.5：主に Mathlib の Quasicategory₂ / HomotopyCategory₂ / Edge.CompStruct.comp_unique でカバーされています。自前の homotopyCategoryBridge が、これを hoFunctor につないでいます。
- 1.4.6：自前の IsInvertibleEdge と kanComplex_ho_isGroupoid（OuterHornConverse.lean）があります。
- 1.5.4：すべて Mathlib にあります。ただし「weakly saturated」をひとまとめにした定義はないので、1.5.4.13 は partial にしました。
- 2.1：Mathlib に非単位的（nonunital）なモノイダル圏・関手がないため、none が大半です。
- 2.2：Mathlib が強い範囲です。ただし conjugate、strictly unital な双圏、twisting cochain、双圏の hC、2-groupoid、core は none です。

InfinityCategories の外にあった宣言：
- KST/SConstruction/STrivialFibration.lean の ihomMap_trivialKanFibration（1.5.5.7）
- KST/Fibration/CoreFactorization.lean の exists_extension_of_innerAnodyne（1.5.6.7）
- HomotopicalAlgebra/Simplicial/MonoRightLiftingContraction.lean の exists_section と exists_vertical_contraction（1.5.5.5）
- HomotopicalAlgebra/Simplicial/Generators.lean の boundaryGenerators_leftClass（1.5.5.14）

使った自前の宣言のファイルには、grep の範囲で sorry も axiom もありません。Archive/ からは何も使っていません。

その他：
- Mathlib には @[kerodon TAG] の属性が 16 件あります。ところが入力の tag 欄は、2.2.8.2 と 2.2.8.9 が同じ 00AL になっていて、2.2.8.24 の 009Q も Mathlib では IsLocallyGroupoid（2.2.8.5 相当）に付いています。入力の tag は不正確なようです。
- 番号のずれ：IsContractibleKan の docstring が「Kerodon §3.5」を引いていますが、現行は 1.5.5.8 です。
- 本文が抽出で欠けている項目（1.4.5.7、2.2.8.9 など）は、引用元から内容を推定したので confidence を low にしました。
- partial のうち空白といえる所：
  - 1.5.5.6 の一般の pullback-power 版
  - 1.5.5.11 の向き（自前にあるのは逆向きだけ）
  - 1.5.6.1 の逆向き
  - 1.5.7.1 と 1.5.7.3 の一般のグラフ（あるのは ℕ の直線グラフの場合だけ）
  - 1.5.7.9 の strict Segal ⇒ nerve

### c02

All 124 items of chunk c02 (Kerodon 2.3.1.1 to 2.5.7.17) are judged, and the output count matches the input. The JSON file was written by a Python script, not the Write tool. The script is kept at scratchpad/kerodon/gen_c02.py, outside out/. Nothing in the repository was touched.

Findings:
(1) 2.3 (Duskin nerve) is entirely none. The only trace is a TODO in Mathlib Bicategory/Functor/StrictlyUnitary.lean.
(2) There is no left adjoint Path[-] to the homotopy coherent nerve (none in 2.4.4). As a result, 2.4.5.8 to 2.4.5.10 are stated in this repo from the side of horns mapping into N^hc(C), so they are partial. 2.4.5.1 and 2.4.5.12 are own, and Coherent/ has no sorry (by grep).
(3) 2.4.6 (homotopy category and homotopy bicategory of a simplicial category) is essentially missing. For 2.4.6.9 there is only one direction: homotopic morphisms get the same class, via coherentEdge_homMk_eq_of_homotopy in EInfinity/Hammock/CoherentComponents.lean. This is outside InfinityCategories.
(4) For Coxeter (2.4.7), Mathlib has only CoxeterSystem and length. There are no braid groups.
(5) Most of 2.5.0 and 2.5.1 is in Mathlib. Mathlib's normalized Moore complex is Kerodon's second construction (2.5.6.15, the kernel construction). There is no quotient C/D (2.5.5.5 to 2.5.5.7 and part of 2.5.6.21 are partial or none). Dold–Kan in Mathlib covers only ℕ-graded complexes, so the right adjoint K from ℤ-graded Ch(ℤ) is absent.
(6) The shuffle product (2.5.7) is in KST/ProExcision, outside InfinityCategories. The EZ quasi-isomorphism 2.5.7.14 has only the homotopy 𝟙 ≃ AW ≫ shuffle. The other composite, shuffle ≫ AW, was not found. Associativity and unit hold only in special cases: simplicial rings in InfinityCategories/Derived/ and the Barratt–Eccles setting in EInfinity/.
(7) The dg side (2.5.2 to 2.5.4) is own, but it is Ch(A)-enriched over a commutative ring A with cochain conventions. The 2.5.3.x docstrings cite HA, not Kerodon numbers.
(8) Archive/ had no hits. Some item texts are truncated (2.4.3.5, 2.4.4.10, 2.5.1.13, 2.5.4.10, 2.5.6.17), so their judgments are inferred and carry med or low confidence.

### c03

入力の 120 項目をすべて判定し、出力の件数も 120 で一致した。対象は 2.5.8〜3.2.8。

**出どころ**
- 2.5.8 の Alexander–Whitney は InfinityCategories ではなく、ほかの場所にある。
  - 本体：KST/ProExcision（AlexanderWhitney.lean、AWChainMap.lean、NormalizedAlexanderWhitney.lean、EZHomotopy.lean、NormalizedEZHomotopy.lean）。
  - 単体集合の鎖の AW 対角（余結合・余単位・退化単体の消去）：EInfinity/AlexanderWhitney。
- 3.1.1〜3.1.3 の大半と 3.1.5.2、3.2.1.1/3.2.1.3、3.2.2.5 は Mathlib にある。
- 3.1.3.6、3.1.3.14、3.1.7.14 などは HomotopyLimits・KST/SConstruction・EInfinity/FrameHom に散らばっている。

**欠けているもの**
- EZ の後に AW をとると恒等、という等式（2.5.8.9）がない。逆向き（AW の後に shuffle をとると恒等とホモトピック）だけがあるので、AW の擬同型（2.5.8.11）は一部扱いにした。
- 3.1.4 の covering map は丸ごとない。
- π₁ の π₀(fiber) への作用（3.2.5.5、3.2.6.5、3.2.6.7）がない。
- nullhomotopic の定義（3.2.4.5）と 3.2.4.11〜3.2.4.15 がない。
- hKan・hKan_* が圏として定義されていない。
- Z[X] の鎖の比較（3.1.7.18）がない。

**定義の違い**
- IsSimplicialHomotopyEquivalence は一段のホモトピーの存在で定義している。Kerodon は Fun の同じ連結成分で定義する。
- IsContractibleKan は境界の充填（点への trivial fibration）で定義している。
- KanHomotopyGroup X n は π_{n+1} を表し、添字が一つずれる。
- π_n は Mathlib の PtSimplex の相対ホモトピー類で、Δ^n/∂Δ^n からの点つき類ではない。

**引用番号のずれ**
- IsContractibleKan の docstring が「Kerodon §3.5」を引いている。
- BoundaryLift の docstring は Construction 3.2.5.1 と書いているが、現行版では Definition 3.2.5.1。
- 入口 DoldKanComparison.lean の docstring「∞ 圏の同値の証明は残る」は古い。

**sorry**
- 関連するディレクトリのソースを grep した範囲では見つからなかった。ヒットしたのは README だけ。

**判定の確度**
- 本文の抜粋が途中で切れていた項目（3.1.2.10、3.1.8.2、3.1.8.12、3.2.4.14、3.2.5.4）は、内容を推測して判定した。confidence は low か med にしてある。

### c04

All 125 items are judged; the output count matches the input. The existing survey (coverage-ch1-3.md) marks 3.3.4–3.4.5 almost entirely "none", but KST/Comparison covers much of it. That directory has 352 files and was missed because the survey only searched InfinityCategories.

What KST/Comparison has:
- Ex and the last vertex map: ρ_X: X→Ex(X) is proved anodyne (exUnitAt_anodyne, after Moss 2020), and Sd preserves anodyne maps (subdivision_map_anodyne). Ex preserves Kan fibrations (ex_map_rlp).
- Ex∞ is defined, with: it is a Kan complex, it preserves fibrations, ρ∞ is anodyne, the WHE iff (3.3.6.8), and preservation of finite limits.
- Right properness (pullback_localized_isIso, 3.3.7.4).
- A homotopy pullback predicate IsHomotopyPullback (one leg replaced by a Kan fibration through a fixed functorial anodyne factorization). It comes with independence of the factorization, symmetry, pasting and cancellation, invariance, and the fibrant criterion.
- The double mapping cylinder (in InfinityCategories/Kan) with its collapse and invariance (3.4.2.2, 3.4.2.13–15).
- A Mather first cube type result (spanPushout_vertex_homotopyPullback = 3.4.4.3).
- X^+ modelled as freeDegeneracies (rows made discrete, then fat realization), with the counit a WHE (3.4.5.4).
- In KST/SConstruction, Quillen A for simplicial products (simplicialProductQuillenA → 3.4.2.17).

There is no predicate for homotopy pushout squares, so most of 3.4.2 and 3.4.3 is "none". Also absent: semisimplicial sets as a category, connectivity (3.5.1–3.5.2, except Mathlib's SSet.IsConnected for n=1), and topological excision and van Kampen (3.4.6–3.4.7).

Weak equivalences in KST are stated as "invertible in the anodyne localization anodyneQ". This is a different formulation from IsWeakHomotopyEquivalence in F1B.

3.3.7.7 (2)⇒(1) exists only in HomotopicalAlgebra/Simplicial/ModelCompatibility under a [ModelCategory SSet] hypothesis, which cannot be discharged, so it is "partial".

On Mathlib's side, 3.3.2.1, 3.3.2.5 and 3.3.3.2–3.3.3.4 are covered by Subdivision.lean (sd, ex, the adjunction) and NonemptyFiniteChains. Braced corresponds only to the stronger condition Nonsingular.

Grep finds no sorry in the matched files. For 3.3.2.3, 3.3.6.7, 3.3.6.9, 3.4.1.13 and 3.5.2.7 the extracted text is missing in the input. I inferred their content from neighbouring text and cached pages and gave them low or med confidence.

Kerodon citations are almost absent here (citedBy is 0 for all items). The KST docstrings cite Segal 1974 and Moss 2020 instead, so Kerodon-number grep does not find these items.

### c05

c05 の 124 項目を全部判定し、出力も 124 件で入力と一致した。c05 は 3.5.3〜3.6.6 と 4.1.1〜4.1.2 の範囲で、citedBy はすべて空だった。探索は SerrePositivity 全体（KST、HomotopicalAlgebra、Spectra、Stable、Archive を含む）と Mathlib を rg で行った。Archive では該当する宣言は見つからなかった。

（1）coskeleton（3.5.3）は Mathlib にある。SimplicialObject.IsCoskeletal（右 Kan 拡張として定義）、cosk・coskAdj・反射性、nerve の 2-coskeletal 性。ただし Kerodon の Def 3.5.3.1（境界からの延長の形）との同値、Fun(K,X)、Kan 複体の cosk（3.5.3.23）はない。

（2）次のものは自前にも Mathlib にもない。
- 弱 coskeleton（3.5.4）
- n-groupoid（3.5.5）
- 基本 n-groupoid（3.5.6）
- truncated Kan 複体（3.5.7）
- Postnikov 塔（3.5.8）
- truncated 射（3.5.9）

関連して見つかったものは次の三つで、いずれも一部か関連の注記にとどまる。
- discrete_kan（離散単体的集合は Kan）
- groupoidNerve_kanComplex（亜群の nerve は Kan）
- F1/Categories/DiscreteSpace の Is0TruncatedSpace。n=0 だけで、𝒮 の対象として「離散空間と同値」と定義している。3.5.7.1 は partial とした。

（3）3.6 は位相空間との比較の節で、ほぼ空白。あるものは次のとおり。
- Mathlib の SSet.Finite（有限 ⇒ finitely presentable の向きだけ）
- 自前の finiteInternalHom_preservesFilteredColimits（3.6.1.10 は own）
- HomotopicalAlgebra/Topological の weakHomotopyEquivalences（π_n の全単射で定義していて、Kerodon の「Sing(f) が弱同値」の形との同値はない）
- Mathlib の IsCoveringMap.liftHomotopy（3.6.6.11 の特別な場合）

自前の単体的集合の弱同値は |f| で定義している。Kan 複体を経由する定義との比較（3.6.4.3）はない。Kan–Quillen は ModelBridge/Inputs/KanQuillen.lean にある sorry の引用。

（4）4.1.1〜4.1.2 は次の判定。
- 内ファイブレーションの定義（Def 4.1.1.1）は both：定義は Mathlib、自前は使う側。
- 4.1.1.10 は partial：⇒ は Mathlib の quasicategory_of_innerFibration、⇐ は薄い圏の nerve のときだけ（自前の thinNerve_innerFibration）。
- 一般の N(F) が内ファイブレーションであること（4.1.1.11）は証明されていない。Stable/FinitePosetLeftKanExtension はこれを仮定として要求している。
- 充満部分圏は fullSubcomplexOnVertices で、構成と quasicategory 性まである。充満性の述語と一意性はない。

（5）次の 5 項目は入力の text が参照の断片で切れていて、主張が読めなかった。3.5.3.10・3.5.6.17・3.5.7.16・3.5.7.17・3.5.3.18／3.5.4.19。3.5.3.18 は記法として扱った。それ以外は confidence を low とし、note に推測と書いた。3.5.3.10 は nerve の 2-coskeletal 性と推測して mathlib・low にした。

### c06

c06 は 4.1.3.1〜4.4.2.15 の 123 項目です。出力の件数は入力と一致しています。ファイルは Write ツールではなく、scratchpad の out/gen06.py から python で書きました。

既存の判定（coverage-ch4.md）と違った点:
- Prop 4.3.3.24（inner fibration の join）は既存の判定では「一般形なし」でしたが、F1B/Joins/JoinMapInnerFibration.lean:25 の joinMap_innerFibration にあります。

空白:
- 4.1.5・4.2.2・4.2.3（covering と fibration in groupoids）、4.3.4（位相空間の join）、4.4.1（isofibration）はほぼ全部ありません。Mathlib にもありません。
- 4.3.7 は中盤（4.3.7.3〜7、4.3.7.9、4.3.7.15〜16、4.3.7.18〜19）が抜けています。抜けているのは、Kan 複体や left fibration の slice が Kan fibration になることと、相対的な trivial 版です。

片側だけある項目（partial にしました）:
- 4.3.6.12：slice 側の制限の right fibration 性（sliceOverRestrict_rightFibration_of_mono）は Archive/InfinityCategories/FilteredExchange にしかありません。
- 4.3.6.13・4.3.7.13：coslice 側だけです。
- 4.4.2.14：left fibration 版の (2)⇒(1) がありません。
- 4.4.2.15：dual の right fibration 版だけです。

番号のずれ（citedBy の箇所）:
- Core/Join.lean は join の構成に §4.3.5 を引いています（正しくは §4.3.3）。
- 4.3.3.24 の citedBy（IntervalCutDetection）と 4.4.1.11 の citedBy（leftFibration_liftInvertibleEdge_target）は内容が違います。
- 4.2.5.1 の docstring は §5.3.1 を引いています。

本文が欠けている項目:
- 4.3.3.11 と 4.3.5.17 は入力の本文が欠けているので、内容を推測して探しました（confidence は low）。

sorry と Archive:
- 主な宣言の .lean ファイルを grep した範囲では sorry は見つかりませんでした。
- Archive 内の宣言を挙げたのは 4.3.6.12 の 1 件だけです。

### c07

The chunk covers 4.4.3–4.5.7, 120 items, and the output has all 120. I checked that every cited declaration sits at its file:line. A grep found no sorry in any file cited.

Corrections to the existing coverage-ch4.md:
- 4.5.1.1 (hQCat) does exist: HomotopyQCat at InfinityCategories/F1/Categories/HomotopyQCat.lean:33. The table says it was not built.
- 4.5.1.23 (the homotopy bicategory) is in Mathlib: SSet.QCat.strictBicategory at Mathlib/AlgebraicTopology/Quasicategory/StrictBicategory.lean:70. The project itself has only the 2-cells (FunctorIso).

Found outside InfinityCategories, all in KST:
- 4.4.3.17 and 4.4.3.18: kanSourceCoreMap (KST/SConstruction/KanSourceCoreMap).
- 4.4.3.6: core inclusion is an inner fibration and an isofibration (KST/LocalizingInvariants/CoreInclusionEquivalenceLifting).
- kanCoreIso (KST/SConstruction/CoreSimplicial).

Possible citation-number drift:
- isPrecompositionEquivalence_of_pushout_gluing cites 4.5.5.9, but its content matches 4.5.5.14.
- The 4.5.1.5 citations in Core/Equivalence.lean (FunctorIso.postcomp and others) are about composing equivalences, so they may be off by a number.

Conventions behind the judgments:
- An isofibration is always stated as EquivalenceLifting, i.e. in the 4.5.6.5 form. Equivalence with the 4.4.1 form is equivalenceLifting_iff_inner_and_invertibleTargetLifting.
- A categorical equivalence is defined as IsPrecompositionEquivalence, the 4.5.4.8(2) form.

Large gaps:
- There is no definition of categorical pullback square or categorical pushout square, so most of 4.5.3.8–4.5.3.30 and 4.5.5 is "none". The Cat∞ limit-cone formulation (qCatPullbackInfinityCone_isLimit) and the gluing lemmas for strict pushouts are recorded as "partial".
- Minimal ∞-categories (4.5.2) and isofibrant diagrams (4.5.7) are entirely absent.

Several results hold only for quasicategories or left fibrations (4.5.3.35, 4.5.4.11, 4.5.6.18, 4.5.6.20); these are "partial".

### c08

All 124 items are judged and the count matches the input (124). The chunk covers 4.5.8, 4.6.1 to 4.6.8 and 4.7.1 to 4.7.4. Nothing here is in Mathlib. Mathlib's ExponentiableMorphism (the locally-cartesian-closed sense) and CategoryTheory.IsSubterminal (the ordinary-category version) are different notions and are noted in the file. None of the cited files contain sorry (checked by grep). Nothing found is in Archive/.

The existing survey (coverage-ch4.md) missed several items:
(1) Construction 4.6.1.1, Hom_C(X,Y), does exist: `intervalMappingSpace` in F1/MappingSpaces/IntervalMappingSpace.lean. The same folder also has Prop 4.6.1.10 and 4.6.1.11 (PreFiberKan.lean).
(2) Prop 4.6.5.10 (the pinch inclusions are equivalences) exists: RightIntervalEquivalence.lean and MappingSpaceModelEquivalence.lean.
(3) Def 4.6.4.1 (oriented fiber product) exists as `laxPullback` in F2/CatInfinity/LaxPullback.lean, introduced for Tamme. Cor 4.6.4.3 also holds there.
(4) Several results on Phi and the coherent nerve are present: 4.6.7.21, 4.6.7.23, 4.6.7.24 and 4.6.7.25 (F1/Coherent/Resolution*).

Results stated with the right-pinched mapping space instead of the left one are judged own:
- 4.6.7.5
- 4.6.7.16
- 4.6.1.14

Two citation-number problems:
- The 'Proposition 4.7.3.6' citation in Core/Terminal.lean:79 and :146 has the wrong number. The content matches Prop 4.7.3.11; it is already listed in the README.
- 4.6.6.7, 4.6.4.19 and 4.6.7.16 have the wrong kind label (e.g. Proposition instead of Lemma). The numbers are right.

The general theory is missing in these places:
- 4.7.1, 4.7.2 and 4.7.4: no notion of truncated, subterminal or discrete objects.
- 4.6.8: no composition maps on mapping spaces, no unitality or associativity, no enriched homotopy category. Only the composition correspondence with one edge fixed exists.
- 4.6.3: no general categorical mapping cylinder.
- 4.6.6: no two-sided slice.

### c09

This chunk covers 4.7.5 to 4.8.8, 132 items, and the output has all 132. Most items are "none" because the base definitions are missing in every directory searched (InfinityCategories, KST, HomotopicalAlgebra, CategoryTheory, EInfinity, Derived, Archive): no ∞-categorical monomorphism or subobject, no truncation or local truncation, no n-category, no homotopy n-category, no full, faithful, n-full or n-faithful functor, and no categorical connectivity. Mathlib has only the 1-category versions (Mono, Subobject, Full, Faithful, essImage) and coskeletality, which only says nerves are 2-coskeletal.

What exists is the fully-faithful / essentially-surjective layer. Own: 4.8.1.1, 4.8.1.3, 4.8.1.7, 4.8.3.1, 4.8.3.5 and 4.8.3.9; 4.8.3.5 is IsFullyFaithful.reflects_isInvertibleEdge. Mathlib: 4.8.0.1, via Functor.IsEquivalence. Partial items are mostly the n=0 (fully faithful) case of a general n-faithful result:
- 4.8.4.1: only (1)⇔(2).
- 4.8.4.13: n=0 only, both directions, through boundary lifting.
- 4.8.4.15: IsFullyFaithful.postcompose.
- 4.8.4.17: coslices, only for inclusions of iso-closed full subcomplexes.
- 4.8.4.9: part (1) only, via coherentNerveMap_isFullyFaithful_iff.
- 4.8.1.11 and 4.8.4.4: replaced by the full subcomplex spanned by the vertex image.

Number mismatches:
- The Lean docstrings citing "Proposition 4.8.4.5" (Core/FullyFaithfulBoundary, Core/FullyFaithfulBaseChange) state the n=0 case of 4.8.4.13 (fully faithful ⇔ boundary lifting), not 4.8.4.5, which is about n-full.
- KST/Spectra cites 4.8.4.1 for π-isomorphisms of Kan complexes; that is Whitehead-type content, so the number is off.

No sorry was found by grep in the main files involved (Core/FullyFaithful*, EquivalenceFullyFaithful, FunctorEdgePointwise, FullyFaithfulPostcomposition, NerveFullyFaithful, MappingSpacePositiveBoundary). Nothing relevant was in Archive.

### c10

This chunk has 124 items, all judged; the output count matches the input. Sections 4.9.1-4.9.3 (ordinals, cardinals, small sets) are almost all in Mathlib: Ordinal, InitialSeg, Order.cof, IsRegular, IsInaccessible, cantor, wellOrderExtension. Mathlib defines cofinality as a cardinal and defines inaccessible as regular plus strong limit, so both differ in form from Kerodon's definitions. The exponential cofinality ecf (4.9.3.16) exists in neither Mathlib nor SerrePositivity, so every item that depends on it (4.9.3.20, 4.9.4.18/19, 4.9.5.11, 4.9.8.11, etc.) is none. From 4.9.4 on, SerrePositivity's own versions mostly assume a regular cardinal (isKappaSmall_prod, isKappaSmall_join) or use the universe form u+1/u (HasSmallKanModel, IsLocallySmall, HasEssentiallySmallFibers); these are marked partial. Most results of 4.9.5-4.9.8 are absent. In 5.1, the definitions of (co)cartesian edges and fibrations, 5.1.1.9, 5.1.1.14 (coslice side), 5.1.2.4, 5.1.4.15 and the composition statements are own, and many are proved only on the cocartesian side. Locally cartesian notions (all of 5.1.3 and 5.1.5) and the slice cartesian fibration (5.1.4.18/20) are missing. Lean docstrings that cite 5.1.2.2, 5.1.3.2, 5.1.4.2/4/8/9 and 5.1.5.3 refer to HTT numbers, not Kerodon, so they are not citation drift. No sorry was found by grep in the main files involved (F1/Fibrations, F1/Cocartesian, F1/Universe, Core/FilteredExchange, LocallySmall). No Archive hits. A helper script gen_c10.py was also left in out/.

### c11

c11 は Kerodon 5.1.6〜5.3.4 の 124 項目です。全件を判定し、出力の件数も 124 で一致しました。

判定の内訳
- 中心的な構成と命題はおおむね自前でそろっています（主に InfinityCategories/F1・F1B）。
  - relative join（5.2.3）、transport とその合成（5.2.2・5.2.5）、Prop 5.2.4.5（写像円柱との比較）
  - strict transport（5.3.1.5・5.3.1.7）、homotopy colimit＝simplicialReplacement（5.3.2）、weighted nerve（5.3.3）、scaffold（5.3.4）
- 片側の場合だけのものが多く、partial にしました。
  - 双対の left・cocartesian 側だけ、底が Δ¹ だけ、同じ底（F̄=id）だけ、のどれかです。
  - 例：Thm 5.1.6.1、Cor 5.1.6.4・5.1.7.16（left fibration の iff だけ）、Thm 5.2.1.1（left fibration の内部 Hom だけ）、Thm 5.2.4.1（十分条件の向きだけ）。
- 次の 5 つはまとまって none です。
  - 5.1.7（inner fibration の同値）：名前つきの定義がありません。left fibration について相対逆が存在するという補題 exists_relativeFunctorInverse_of_precompositionEquivalence だけがあります。
  - left covering map（5.2.0・5.2.7、5.3.4.20）
  - contravariant transport（5.2.2.15・5.2.2.18、5.2.5.7）
  - enriched homotopy transport（5.2.8.6〜5.2.8.12）
  - weighted nerve の左随伴（5.3.3.23〜5.3.3.26）

InfinityCategories の外で見つけたもの
- KST/ に二つあります。
  - KST/Fibration/StrictTransportPostToLeftFibration.lean：5.3.1.9 の一部
  - KST/SConstruction/DoubleCoconeUniversality.lean の ihom_pre_innerFibration：5.2.1.1 の補助
- Mathlib から使ったもの
  - Functor.Elements（5.2.6.1・5.2.6.2）
  - Under.mapFunctor（5.3.1.1）
  - FiberedCategory の IsCocartesian・Fiber（5.2.2.1・5.2.2.2 は partial：Mathlib に cocartesian fibration の型クラスと f_! 関手がありません）
  - IsCoveringMap（5.2.7.1 は分類定理がないので none）
- Archive/ には該当するものが見つかりませんでした。

sorry と axiom
- 使った宣言のディレクトリ（F1・F1B・Core・HomotopyLimits・Kan・KST/Fibration・F2/Tensor）を grep した範囲では、sorry も axiom もありませんでした。

入力と番号について
- 次の 3 件は、入力の text が導入文の断片でした。番号から Kerodon の内容を推測して照合したので、confidence は low か med です：5.3.2.17、5.3.3.19、5.3.4.19。
- 5.2.3.15 も text は導入文ですが、主張（C ⋆_D D → Δ¹ が cocartesian）が分かるので照合できました。
- 5.2.3.18：docstring に「Corollary」と書かれた箇所があります（現行の版では Example）。

補助ファイル
- out/gen11.py（生成スクリプト）、out/c11-brief.txt（項目の一覧）、out/lk11.sh（検索の補助）は scratchpad の out/ に置いた作業用のファイルです。

### c12

c12 の範囲は 5.3.5〜5.6.1 で 123 項目、出力も 123 件で一致を確認した。95 件ある none の大半は次の三つ。5.4 と 5.5.4 の ∞-bicategory（README で意図的に導入しない方針）、5.3.8 の minimal fibration、5.5.5 の QC_Obj。InfinityCategories の外も探した。KST に N^hc(Kan_*) が PointedKanInfinity（KST/SConstruction/PointedKanEnrichedObjects.lean:51）としてあるが、Prop 5.5.2.8 の 𝒮_* との比較の同値はない。Mathlib の Bicategory/Grothendieck.lean は 5.6.1.1・.3・.5・.12 に当たる。FiberedCategory/Grothendieck.lean は Cor 5.6.1.17 の反変側の半分だけを与える。cocartesian の分類（5.3.5.6・5.3.5.11・5.3.5.12、5.6.0.2）の宣言は F1/Cocartesian/ にある。ここは休止中の集約 F1/Cocartesian.lean からしか import されず、main の F1.lean には入らないので note に書いた。調べたディレクトリのソースを grep した範囲では sorry はなかった。既存の coverage では 5.3.6 が「Prop 5.3.6.7・5.3.6.10 は未確認」だった。実際は Lemma 5.3.6.5 が CocartesianScaffold.overPullback_isPrecompositionEquivalence（F1B/CocartesianScaffold/ArbitraryBaseChange.lean:23）としてある。相対指数 Fun(C/B, D) はない。5.3.5.7 と 5.3.6.11 は抽出文が 500 字で切れていて、Kerodon の主張の全体を読めていない。5.3.5.7 は scaffold ⇒ 圏同値の向きだけと判定したが、確信度は med。

### c13

All 125 input items are judged; the output count matches the input (125). The range is 5.6.2 to 6.2.3. No sorry turned up in any file cited, checked by grep only.

(1) In 5.6.2 to 5.6.9 the QC-valued (cocartesian) side has nothing. Most entries are "partial" because only the left-fibration, S-valued analogue exists: leftUnstraightening, LeftTransportRepresentation, transportWitnessSpace and related declarations under F1/Transport and F1/Universe. 5.6.7.5 (cocartesian implies isofibration) exists only for a quasicategory base, as cocartesianFibration_kanEquivalenceLifting. It sits in the paused F1/Cocartesian tree, which main does not import.

(2) The 93 citations of 5.6.2.5 point to fiber content, which corresponds to Example 5.6.2.19 in the current numbering, so that is a numbering drift. The 34 citations of 5.6.5.15 and the 35 of 5.6.9.1 point to proof components.

(3) 6.1 is mostly Mathlib: Bicategory.Adjunction, homEquiv₁/₂, conjugateEquiv, compUnit/compCounit, ExactPairing. Mathlib's ExactPairing and HasRightDual use the opposite left/right convention from Kerodon. 6.1.2.9 (an adjunction exists with unit η iff every adjunct map built from η is bijective) is our own bicategory_exists_adjunction_unit_iff in F1B/Adjunction/UnitHomCriterion.lean, which the existing survey had not counted.

(4) In 6.2.2 to 6.2.3, ReflectiveSubcategory is defined as a left adjoint to the inclusion, so Kerodon's reflection-based definition and 6.2.2.19 are only partly matched. Several statements are proved under HomotopyLimits/ rather than InfinityCategories/F1B, for example reflective_isIso_map_iff_localHom (6.2.2.16) and reflective_isLocal_iff_invertedEdges (6.2.3.10). Localizing collections (6.2.3.11 to 6.2.3.16) and n-truncated objects (6.2.1.21, 6.2.2.13 and 6.2.2.14) have no definitions at all.

(5) KST, HomotopicalAlgebra and Archive turned up nothing relevant to this chunk. The local equivalences in HomotopicalAlgebra/Localization are model-category notions, not ∞-categorical ones.

### c14

c14 は 6.2.4〜7.1.4 の 120 項目。全件を判定し、件数が一致することを確かめた（own 18・mathlib 5・partial 31・none 66）。

- 6.3.2.1（局所化の存在）は KST/LocalizingInvariants/LocalizationResolution.lean:37 の exists_quasicategory_localization にある。構成は Q（Δ³ の商）ではなく walkingEquivalence を貼り付けるもので、これも KST にある（InverseAttachment*）。このため 6.3.2.7/8 は none、6.3.2.9 は partial とした。C[W^{-1}]（KST/GeneralLocalization の edgeLocalization）は選択で決めているだけで、関手的ではない。そのため 6.3.2.11 は partial。
- 6.3.1.21 は Derived/Localization/GroupoidCompletion にある。示されているのは「全辺の局所化の行き先は Kan 複体」という向きだけで、partial。6.3.6.4/6.3.6.5 には F1/Transport/LocalizationAllBases の transportSimplexFirstVertexMap_isLocalization が近い。ただし first vertex の規約で、universally localizing ではない。いずれも partial。
- 6.2.4・6.2.5・6.2.7・6.3.4・6.3.5（universally localizing）・7.1.2（power、dg）は、宣言が一つも見つからなかった。
- 7.1 の述語は、K を固定した版を持たない。Lean 側は HasSmallLimits・PreservesSmallLimits という小さい形状全部の版だけなので、7.1.1.15・7.1.4.4・7.1.4.19・7.1.4.31・7.1.4.35 は partial とした。
- 7.1.4.22 は F2/Compact/ConservativeLimitReflection の isLimitCone_of_conservative_image がほぼそのまま。7.1.4.28 は両向きともある。
- Mathlib のタグのずれ：Nonsingular.lean:73 の nerve(poset) が nonsingular というインスタンスに @[kerodon 02MT] が付いている。02MT は今の版では 6.3.6.17（有限 poset からの universally localizing 写像）のタグ。SSet.Nonsingular の定義の 02MG も、Kerodon の今のタグ 04JV とは一致しない。
- sorry：引いた宣言のファイルとその周辺のディレクトリを grep し、証明本体にある sorry は見つからなかった。ヒットは F2/Presentable/Localization/All.lean の 1 件だけで、docstring の中の文字列。
- F1B/Localization/DwyerKan.lean は空の骨組み。DwyerKan/ 配下（約 619 ファイル）は、ここでは根拠に使っていない。
- citedBy が付いているのは 6.2.6.5・6.3.1.1・6.3.1.9・6.3.1.13 だけで、どれも内容と一致した。

### c15

c15 covers 7.1.5–7.3.1 (122 items, all present). The c15 output file is the only file written. The repo was only read.

Judgement rule:
- Extra assumptions that only restrict the model are marked own, with a note: U is an inner fibration, the index B is a quasicategory, or the statement is given in boundary-lifting form (InitialBoundaryLifting).
- Statements restricted to a smaller class are marked partial: left fibration instead of cocartesian, finite colimits only, the nerve of a 1-category, or only one direction.

Findings:
1. The core of relative initial objects and relative colimits (7.1.5.17/19/21, 7.1.6.13/16) and pointwise colimits in functor categories (7.1.8.x) is mostly own. Some declarations sit in KST/: the colimit side of 7.1.8 (KST/SConstruction/FunctorPointwise*, RelativeInitialExtension), the adjunction from a section (KST/LocalizingInvariants/RelativeInitialAdjunction), and relativeInitialVertexIso (KST/SConstruction).
2. IsPointwiseColimitCone and isColimitCone_of_pointwise are defined twice: in KST/SConstruction and in InfinityCategories/Core (or F1B)/FilteredExchange.
3. The 7.1.9 oriented fiber product appears as laxPullback in F2/CatInfinity. Its results also assume that F1 preserves the colimit on the ev1 side, so they are marked partial.
4. Several 7.2 results live outside F1B/Cofinality:
   - adjoint ⇒ cofinal, only for a 1-categorical adjunction: EInfinity/FrameHom.
   - products of cofinal maps, right side only: HomotopyLimits/CofinalTensor.
   - cofinality of the diagonal: Stable/Filtered.
   - the colimit side of 7.2.2.3: F2/Ind/CofinalCoconeRestriction.
   - limits and cofinality: Derived/CofinalLimitTransfer.
5. Nothing found for:
   - 7.1.5.13–15: coreflective localization (only the strict-section special case exists).
   - 7.1.7.4/5: left fibrations creating colimits.
   - 7.1.7.9 onward: edgewise colimits (the Edgewise* files in Archive/ are unrelated).
   - 7.1.8.4/6: Fubini.
   - 7.1.10: colimits in ∞-categories of sections.
   - 7.2.1.10–13, 7.2.1.16–18, 7.2.1.22: localization, filtered colimits, categorical equivalence. Mathlib has only the 1-categorical Final analogues (final_of_natIso, final_iff_comp_equivalence, final_of_adjunction), used as decls for the partial items 7.2.1.13/21/23, 7.2.2.8 and 7.2.3.7.
   - 7.3.1.14–16 and 7.3.1.18.
6. Citation-number drift:
   - The decl cited as 7.1.8.5 (isLimitCone_of_pointwise) is the dual of 7.1.8.15.
   - The decl cited as 7.2.1.15 (exists_leftAnodyne_leftFibration_factorization) is a different result. The real counterpart is isLeftCofinal_iff_exists_anodyne_trivialKan_factorization.
7. A grep found no sorry in any file cited.
8. Some items are low confidence because their Kerodon text was cut off in the chunk: 7.1.6.19, 7.1.9.2, 7.2.2.14, 7.3.1.16 and 7.3.1.18.

### c16

This chunk covers 122 items, §7.3.2 to 7.4.3; the output has all 122 (checked by count). Nothing was found in Mathlib: it only has 1-categorical Kan extensions. The repo's sorry/axiom grep over F1B/KanExtension, HomotopyLimits, F1, F1B/Fibrations and the other files cited came back empty.

Where own coverage is:
- Almost all of it is in InfinityCategories/F1B/KanExtension (255 files).
- §7.3.2–7.3.6 are well covered: definitions, existence 7.3.5.1/2/5/8, Hom universality 7.3.6.1, 7.3.6.7, 7.3.6.9, the restriction theorems 7.3.6.14/15, and the relative join over a cocartesian δ in 7.3.4.5–7.
- Many statements are split into one-directional lemmas rather than stated as one iff (7.3.2.7, 7.3.4.2–4, 7.3.5.5), so I marked several of these partial.
- The absolute "left Kan extended at C" has no named predicate; it appears as the hypothesis ∀ c, IsColimitCone (leftKanCanonicalCocone δ F c).

What is missing:
- §7.3.7 (Kan extensions in functor ∞-categories), §7.3.8 (transitivity, Fubini) and §7.3.9 (relative colimits for cocartesian fibrations) are absent entirely.
- Also absent: the coreflective and initial-object criteria (7.3.3.11–14, 7.3.5.9–11), the restriction-functor adjoint 7.3.6.3/4, n-truncated objects (7.3.8.7; there is no truncated definition at all), and most of §7.4.2.

Finds outside F1B/KanExtension (not under that heading in coverage-ch7):
- 7.4.3.4 is HomotopyLimits/BousfieldKanCoherentColimit (bousfieldKanCoherentCocone_isColimit, cited as HTT 4.2.4.1).
- 7.4.1.22/23 are F1/Yoneda/RepresentablePresheafLimitDetection and YonedaEvaluationLimits (C^op form, cited as HTT 5.1.3.2).
- 7.4.1.18 is Derived/LeftTransportConeRestriction (LeftTransportRepresentation.coneRestriction_iff).
- KST, EInfinity and Derived only apply these results (DG Verdier, Barratt–Eccles right Kan extensions); none of them states the general theory. Nothing from Archive was used.

Citation numbers:
- 7.4.1.6 has 312 citations, but most are blanket citations on helper lemmas such as AssociativeJoinSimplex; the matching content is coherentDiagramSectionsCone_isLimit in F1/Coherent/SpaceSmallLimits.
- Several files cite "Lemma 7.3.4.5–6" as one range, so 7.3.4.6 has no citation of its own.
- 7.3.6.1, 7.3.6.7 and 7.3.6.9 match their content.

Items whose excerpt is too short to judge (7.3.6.5, 7.3.8.14, 7.3.9.5, 7.4.1.2, 7.4.2.4) are marked low confidence.

### c17

c17 は 7.4.4 から 7.6.2 までの 121 項目で、全件を判定した（件数は assert で一致を確かめた）。
(1) 7.4.4〜7.4.6（QC の極限・余極限、diffraction・refraction）：QC では引き戻しの場合だけある（catPullbackCone_isLimit、qCatPullbackInfinityCone_isLimit）。𝒮 版の類似はある（coherentDiagramSectionsCone_isLimit、coherentDiagramTotalCocone_isColimit）が、QC の主張の特別な場合ではないので、余極限側は none、極限側は partial とした。
(2) 7.5.1・7.5.4 は中身がある。own は 7.5.1.1、7.5.1.2、7.5.2.1、7.5.4.5（kanCone_isLimit_iff_bousfieldKanComparison、F2/Presentable にある）、7.5.4.6（strictCoherentCone_isLimit_iff_*）。isofibrant の定義と置換（7.5.3）、categorical limit/colimit diagram（7.5.5・7.5.8）、holim・hocolim diagram の述語はない。
(3) InfinityCategories の外で見つけたもの：KST/Comparison/HomotopyPullback.lean の IsHomotopyPullback と KST/Fibration/KanCommSqLimit.lean の kanCommSqCone_isLimit（7.5.4.13 の一方向）、KST/Descent の HasHomotopyLimitDescent（基点付き・π_* 版の holim diagram、7.5.4.1）、HomotopicalAlgebra/Diagram の射影モデル構造と hocolim（7.5.6）。HomotopicalAlgebra の結果は [ModelCategory C] を仮定する。SSet に使うときは kanQuillenModel（ModelBridge/Inputs/KanQuillen、sorry 付きの Hovey 引用）を通るので、note に書いた。Archive にあったのは kanDiagramCoherentNerve の旧版だけで、判定には使っていない。
(4) 7.6：own は IsPullbackSquare・IsPushoutSquare の定義だけ。貼り合わせは絶対版だけで 7.6.2.40 の相対版はなく、7.6.2.42 は片方の向きだけ。∞ 圏の truncated 射、monomorphism、対角射、f^*、積の hKan 豊穣の定義はどれもない。Mathlib には 1 圏版がある（diagonal、Over.pullback、hasFiniteProducts_of_has_binary_and_terminal）が、主張が違うので mathlib とは判定せず、note に書いた。
(5) 照合は grep の範囲で行った。関係するファイル（HomotopyLimits、F2/CatInfinity、Stable、HomotopicalAlgebra/Diagram、KST/Comparison）に sorry はなかった。Kerodon の抜粋が短く内容を推定した項目（7.5.3.3、7.5.6.12、7.6.1.13）は low にした。

### c18

All 136 items are judged, and the output count matches the input (136). Scope: 7.6.3 to 7.7.7 and 8.1.0 to 8.1.2.

Where the own declarations are:
- 7.6.3 (pullbacks): HomotopyLimits/RepresentableLimitEquivalence and F2/CatInfinity/CatPullback*.
- 7.6.5 (towers): SpaceTowers and F2/Ind/FilteredKanCocone.
- 7.6.6 (completeness): HasSmallLimits and its relatives in F2/Presentable.
- 8.1 (twisted arrows): F1/TwistedArrow.
- 7.6.4 (equalizers) and 7.7 (descent, universal colimits, Mather cube, LCC, disjoint coproducts) have no ∞-categorical versions at all.

How Mathlib is counted:
- Where Mathlib has only the 1-category version (IsUniversalColimit, IsVanKampenColimit, NatTrans.Equifibered, CoproductDisjoint, equalizer/Fork, ExponentiableMorphism, hasFiniteLimits_of_hasEqualizers_and_finite_products), I marked the item partial and wrote this in the note.
- The only mathlib verdict is 7.7.3.1, which is a statement about ordinary categories.

Partial points worth knowing:
- 7.6.3.1, 7.6.3.10 and 7.6.3.14 hold only for strict cones, or require one leg to be a fibration.
- 8.1.2.1 covers only the identity morphism.
- 8.1.2.16 has only one direction: fully faithful ⟹ the comparison is an equivalence.
- 8.1.1.13 is not a single declaration. It follows by combining twistedArrowProjection_leftFibration with leftFibration_fibration_of_kanComplex.

Other notes:
- No grep hits for sorry in any of the files I cite.
- No Archive hits.
- Everything under KST/Descent is scheme descent and unrelated to 7.7.
- Watch the name KappaContinuousFunctorInfinity: it is about preserving κ-filtered colimits, not κ-continuity (7.6.6.7).
- The text is cut off for 8.1.2.11, 8.1.2.21 and 8.1.2.23, so those verdicts are guesses (low confidence).
- Lean docstrings cite only the 8.1.1.x numbers in this range, and they match the content.

### c19

Chunk c19 covers Kerodon 8.1.3 to 8.3.4. All 122 input items are in the output file (122 in, 122 out). None of these items is cited by any Lean docstring (nCited is 0 for all).

- **8.1 (cospans) and 8.2 (couplings): almost everything is none.** Neither SerrePositivity nor Mathlib has the Cospan construction, couplings, Beck-Chevalley fibrations or the Duskin nerve (Mathlib only lists the Duskin nerve as a TODO). Searching outside InfinityCategories found nothing either: KST, HomotopicalAlgebra and DG have only HasTwoOutOfThreeProperty instances, and the cospan hits in Archive/FilteredExchange are diagram names that have nothing to do with this construction.
- **Three partial entries are only 1-categorical analogues in Mathlib:**
  - 8.1.3.12: Mathlib's span bicategory `SpanBicat`, applied to C^op, gives the bicategory of cospans.
  - 8.1.6.5: the hypotheses of `SpanBicat` are the dual of pushout-compatibility.
  - 8.1.7.8: `MorphismProperty.HasOfPostcompProperty` is the 1-category version of the left two-out-of-three property.
- **8.3.0–8.3.1:**
  - 8.3.0.1 and 8.3.1.1 are in Mathlib (`Coyoneda.fullyFaithful`, `coyonedaEquiv`).
  - 8.3.1.2 (the ∞-category of spaces) is `SpaceInfinity`.
  - 8.3.1.3 is `yonedaPresheafEvaluation_isQCatEquivalence`. It is stated for presheaves, not in Kerodon's covariant form, and only for small quasicategories.
- **8.3.3:**
  - 8.3.3.13 (Yoneda is fully faithful) is `yonedaInfinityMap_isFullyFaithful` and `coyonedaInfinityMap_isFullyFaithful`, for small C only.
  - 8.3.3.14 (limits are detected by the Hom functors) is `isLimitCone_iff_covariantRepresentableInfinity`, `yonedaInfinityMap_isLimit` and `coyonedaInfinityMap_reflects_isLimit`.
  - The Hom-functor (8.3.3.1 and 8.3.3.2) exists only as a concrete construction: the classifying diagram of Tw(C) → C^op × C (`twistedArrowHomInfinity`). There is no abstract "is a Hom-functor" predicate, and no uniqueness result.
- **The general profunctor theory is absent:** universal vertices, representable and balanced profunctors, and their classification and universal property. What exists is representability of a single functor (`IsRepresentableSmallSpaceFunctor`) and adjunctions characterized by Hom representability (`exists_leftAdjoint_iff_covariantHom_representable`). I judged 8.3.4.2, 8.3.4.4 and 8.3.4.9 partial on that basis.
- **Size conditions:** where Kerodon uses κ-small spaces (8.3.3.5, 8.3.3.12, 8.3.3.15), the Lean code handles size with universes, so I marked those partial.
- **Sorry:** I grepped F1/Yoneda, F1/MappingSpaces, F2/Presentable and the HomotopyLimits/CoYoneda* files. The only occurrence of the word `sorry` is in a docstring in F2/Presentable/Localization/All.lean, so none of the cited declarations shows a sorry in its source. I did not run an axiom audit.

### c20

Chunk c20 covers Kerodon 8.3.5 through 8.5.5, 127 items. All 127 are written, which I checked by counting. No item in this chunk has a docstring citation (nCited 0 for all), so every match was found by searching on content. 8.5 (idempotents) is the strongest part: the own declarations are under InfinityCategories/{Core,F1,F1B,F2}/Idempotent and F2/Compact/ColimitRetractions. Matching statements were found for 8.5.1.12, 8.5.1.22, 8.5.1.30, 8.5.1.31, 8.5.3.1, 8.5.3.5, 8.5.3.10–12, 8.5.4.1, 8.5.4.11, 8.5.4.13, 8.5.4.14, 8.5.4.26, 8.5.5.1, 8.5.5.4 and 8.5.5.5. A grep found no sorry in any of those directories. The model of Ret is WalkingSplit = Karoubi(WalkingIdem), and R is WeakShape (Δ² with the long edge collapsed). Not found in 8.5: the sequential (Spine[Z]) criterion 8.5.4.15–20, oriented and homotopy fiber products and limits in QC (8.5.4.25, 8.5.4.27–29, 8.5.5.9), the QC^ic left adjoint, κ-smallness, truncated and cocartesian retracts, and filtered colimits (8.5.1.35). In Mathlib, 8.5.2 (1-categorical idempotents) is covered by Idempotents/Basic.lean, mostly as whole-category statements; 8.4.1.1 by Functor.IsDense; 8.5.1.7 only in its 1-categorical form (isomorphisms are stable under retracts). In 8.4 there is no general cocompletion or 𝕂-cocompletion theory (8.4.0.1, 8.4.6–8.4.9 are missing). What exists is the presheaf density colimit, the Yoneda left Kan extension, and the Ind, P_Σ and idempotent-completion special cases, so those items are partial. 8.3.5 and 8.3.7 are missing. For 8.3.6, only the one-variable comparison of the enriched Hom is there (F1/Coherent/RepresentableHom*). The search found nothing relevant outside InfinityCategories (KST, HomotopicalAlgebra, Archive, etc.): the hits there are 1-categorical or DG-specific applications. The output was generated by a script (scratchpad/kerodon/gen20.py) instead of the Write tool.

### c21

c21 は 8.5.6〜8.6.7 の 126 項目で、全項目を判定し、件数が入力と一致することを確かめた。citedBy はどの項目でも空で、Lean の docstring にこの範囲の Kerodon 番号は一つも出てこない。冪等の理論は InfinityCategories の F1/F1B/F2/Core 下の Idempotent にあり、HTT 4.4.5・5.1.4 の番号で引かれている。ファイルを grep した範囲では sorry はない。

- 一部（partial）になったもの：
  - IsIdempotentCompletion の普遍性・cofinal 性・右 fibration に沿う底変換・反転・終対象の保存から、8.5.6.11/13/15/17/18/20。8.5.6.18 は実質的に主張そのものだが、inner fibration の仮定が追加されている。
  - weakDiagram_strongSplitting_exists（弱い retract 図式の延長）から 8.5.7.10 と 8.5.8.4。
  - nonemptyStrongSplitting_iff_hasLimit から 8.5.7.12（Spine[ℤ] 図式ではなく N(Idem) 図式の極限の形）。
  - 分裂図式の錐が極限になることから 8.5.7.16、trivial Kan fibration から 8.5.7.19（low）、CoherentIdempotent から 8.5.7.3、弱い retract 図式と StrongSplitting から 8.5.7.8、QCat/CatInfinity から 8.6.7.4（Kerodon 5.5.3.1 として）。
- 自前（own）は 8.5.7.15 の 1 件。Ret を WalkingSplit = Karoubi(WalkingIdem) として持っている。
- Mathlib は 8.5.7.1 の 1 件。単体的円周 SSet.S1 がある。
- なし（none）になったもの：Morita 同値の定義、homotopy idempotent、weakly split、Spine[ℤ]、部分冪等 N_{≤n}(Idem)、Thompson 群と Thompson 亜群、フィルター余極限と冪等完備性、8.6 の全体（共役 fibration、双対 fibration、E^≍、反転関手 σ）。Tw はあるが、8.6 の構成には使われていない。
- 名前が紛らわしいもの：DifferentialGraded/Morita は DG の Morita で、別の概念。Mathlib の Data/Dyadic は二進有理数だけで、Thompson 群の材料にはならない。
- Archive/ には該当する宣言がなかった。

### c22

131 項目すべてを判定（入力と出力の件数は一致）。

- 8.6.8〜8.7.7（反変輸送表現・coend・fiberwise cocompletion・flat inner fibration）：ほぼすべて「なし」。例外は 2 件で、どちらも「一部」。
  - 8.6.8.17：QC そのものは CatInfinity として F1/Categories/CatInfinity.lean にある。
  - 8.6.9.5：Mathlib の coend は通常の圏のものだけ。
- 9.1（filtered）：中身があるのはここに集中している。主な宣言は Core/Filtered/FilteredInfinity・FilteredEquivalence と Stable/Filtered/*、F1/Filtered、F2/Ind。逆向きのない片方向だけの結果が多い。
  - 9.1.1.18 と 9.1.5.7 の逆向き（coslice 判定・対角判定による同値）は Archive/InfinityCategories/FilteredExchange/FilteredDiagonalCriterion.lean にだけある。
  - 9.1.1.20（Kan 複体では filtered ⇔ 可縮）は Archive/.../FilteredKanContractibility.lean にだけある。own と判定し、note に Archive のみと書いた。
  - main（現行コード）には cofiltered のクラスがない。代わりに Derived/FiniteConeOpposite.lean の op 版を使っている。
  - weakly right cofinal、9.1.2 の局所判定、9.1.3.2（left fibration の全空間：filtered ⇔ 弱可縮）は見つからなかった。
- 9.1.5.1 と 9.1.5.9 はどちらも「filtered ⇒ 極限と交換」の向きだけ。9.1.5.9 は poset 形状に限る。
- citedBy の番号は、Archive の対角判定（filtered 版）を 9.1.1.18 に付けている。内容は 9.1.5.7 の (1)⇔(2) に近い。
- 見た宣言のファイルを grep したが sorry はなかった。
- 本文の取り出しが切れている項目（9.1.2.5、9.1.3.4、8.7.3.3 など）は内容の照合が弱いので、confidence を low にした。

### c23

All 124 items (9.1.6.1 to 9.2.8.11) are judged; output count matches input. No item had citedBy hints (nCited=0 for all), so every match comes from grep plus reading the statements. None of the cited files contain sorry.

Corrections to the existing coverage-ch8-10.md:
(1) 9.1.7.5 (the ⊴/◁ relation on regular cardinals): Mathlib has `Cardinal.SharplyLT` (Mathlib/CategoryTheory/Presentable/SharplyLT/Basic.lean), with `tfae`, `trans` and `of_pow_lt`. It covers the strict relation ◁ only; the non-strict ⊴ is not defined anywhere. So 9.1.7.8 is mathlib, and 9.1.7.9 and 9.1.7.13 are partial.
(2) 9.1.7.1 (a small simplicial subset sits inside a small ∞-subcategory) is own: `hasCardinalLT_innerHornClosure` in Core/InnerHornClosureCardinal.lean.
(3) 9.1.8.2 and 9.1.8.4 are own, using the same codiscrete-product / terminal-subcomplex construction as Kerodon (F2/Ind/CodiscreteProductCofinal, SmallCodiscreteConeRange, TerminalCarrierCofinal).
(4) 9.2.2.26 and 9.2.2.28 are own: `Compact.preservesKappaFilteredColimits_of_poset` shows that preserving colimits over κ-directed posets is enough.
(5) 9.1.6.7, 9.1.6.8, 9.1.6.12 and 9.1.6.13 (projective cofibrations of diagrams) are partial, from HomotopicalAlgebra/Diagram/Projective*. That is a projective model structure for a general cofibrantly generated model category. Applying it to SSet needs a `ModelCategory SSet` instance, which the main path lacks (ModelBridge/Inputs/KanQuillen.lean has a sorry).
(6) Archive/ has a different filteredness criterion: `isKappaFiltered_iff_constantDiagram_rightCofinal`. It does not match 9.1.8.11.

Extraction problems: for 9.1.7.8, 9.1.7.12, 9.1.8.7, 9.2.5.24, 9.2.5.25, 9.2.7.4 and 9.2.8.11, the text field is cut off or is the proof of a neighbouring item. These have confidence low, and the note says what the statement was assumed to be.

Overall shape: the λ-unbounded parts of 9.2 (compactness, finitary functors, closure under finite colimits) are covered. Nothing covers the (κ,λ)-indexed theory (9.2.1.3, 9.2.2.6, 9.2.5.12 and dependents), sequential cocompleteness (9.2.3), filtered colimits inside QC (9.1.9), the finiteness notions for Kan complexes and ∞-categories (9.2.6, 9.2.7), or the converse directions of the cofinal-poset characterizations (9.1.8.1, 9.1.8.8).

### c24

This chunk covers Kerodon 9.2.9 through 9.4.2: 121 items. All 121 were judged and written, and the count and kinds match the input. No item in the chunk is cited by any Lean docstring (citedBy is empty for all), so every match was found by content.

The own work all sits in InfinityCategories/F2/{Ind,Compact,Presentable}. No sorry or axiom turned up there in a grep, and nothing relevant was found in KST, HomotopicalAlgebra or Archive.

There is a structural reason so many items are partial:
- The project has only the concrete model Ind_κ, built as IndInfinity κ C (C small, values in universe u+1). It defines no abstract predicate "f exhibits D as an Ind completion", and no two-cardinal Ind_κ^λ.
- So Kerodon statements in (κ,λ) form are partial ("only the case λ=∞"). Statements made for Ind_κ alone (9.3.2.9, 9.3.2.10, 9.3.4.5) are own.

Where the main results are:
- Recognition theorem: indComparisonEquivalence and exists_indComparison.
- Ind ↔ flat presheaves: isIndVertex_iff_hasKappaFilteredElements.
- Compact objects ≃ Idem(C): compactIndYoneda_isIdempotentCompletion.
- Accessible ⇔ Ind equivalence: isKappaAccessible_iff_indEquivalence.

Gaps:
- 9.3.5 (left exactness of functors between ∞-categories) does not exist in the project. Mathlib's 1-category versions (RepresentablyFlat, preservesFiniteLimits_iff_flat, Ind.leftExactFunctorEquivalence, isIndObject_iff_preservesFiniteLimits, Ind.yoneda coflat and preserving finite colimits) were all marked partial with a note.
- Also absent:
  - Pro completion
  - relative Ind (9.3.3.13 onward)
  - the Ind functor on QC
  - transitivity (9.3.6)
  - final objects of Ind (9.3.7)
  - QC = Ind(QC_fin)
  - (κ,λ)-cocomplete fibrations (9.2.9)
  - compact functors as a named definition
- Lazard's theorem is in neither the project nor Mathlib.

Kerodon's "compactly generated" (9.4.1.1, 9.4.1.5) does not require the compact objects to form a small subcategory. The project's IsKappaAccessible does require that, so I marked them partial.

Several Kerodon texts are cut off (9.2.9.16, 9.3.3.7, 9.3.4.14, 9.3.4.15, 9.3.4.20, 9.3.4.21, 9.3.4.23, 9.3.5.8). Their judgments rest on a guess and are marked low.

gen_c24.py, the script that generates the JSON, is in the same out/ directory.

### c25

All 120 items are judged; the counts were checked against the input. None of the items in this chunk has a citedBy entry, so every match was found by searching for content. Every match is in InfinityCategories/F2/Presentable or F2/Compact. Nothing relevant turned up in KST, Archive or the other trees. HomotopicalAlgebra/Smith has 1-categorical accessibility results built on Mathlib, and Mathlib has CategoryTheory.Presentable; neither is ∞-categorical, so I did not count them. 9.5.0.1 is the only Mathlib item (CompleteLattice).

Findings:
(1) There is no predicate for "(κ,λ)-compactly generated". Only IsKappaAccessible exists, defined in the HTT style; isKappaAccessible_iff_indEquivalence proves the Ind_κ form. As a result, 9.4.3–9.4.6 is mostly none, and the accessible special cases are recorded as partial.
(2) The adjoint functor theorem 9.5.2.1 has no conditions (exists_rightAdjoint_iff_preservesSmallColimits and exists_leftAdjoint_iff_accessible_preservesLimits). Grep finds no sorry in AdjointFunctorTheorem.lean. 9.5.2.3 is partial because the Lean statement assumes C is presentable, while Kerodon only needs accessible. The proof itself only uses accessibility.
(3) 9.5.4.6, the presentable pullback: pullback_isPresentable_of_accessiblePullback takes the general accessible-pullback statement as a hypothesis. Substituting pullback_isAccessible removes that hypothesis, but there is no single public lemma for the result.
(4) Not found: truncated finite spaces (9.4.3), compactly generated fibrations (9.4.6), accessibly embedded subcategories, edgewise accessible fibrations, presentable fibrations, slices and oriented fiber products, Pr^L limits, and the global duality Pr^L^op ≃ Pr^R (only the pairwise version presentableAdjointFunctorEquivalence exists).
(5) Several items are hard to judge because the 500-character excerpt is cut off, among them 9.4.7.22–25 and 9.4.8.11/18, so I gave them low confidence.
I also left the helper script gen25.py, used to generate the file, in the same out/ directory.

### c26

c26 は 9.5.5〜9.7.1 の 127 項目で、出力も 127 件（件数の一致を確かめた）。この範囲は Lean の docstring からの引用が 0 件なので、照合はすべて内容で行った。

- own は 2 件。
  - 9.5.7.1（Bousfield 局所化の存在）：`bousfield_isReflectiveSubcategory`・`bousfieldLocalObjects_isPresentable`（F2/Presentable/Localization/BousfieldReflection.lean）。
  - 9.6.9.18（強飽和の定義）：`IsStronglySaturatedEdgeSetOfShapes`（HomotopyLimits/Presentable/LocalStrongSaturation.lean:29、HTT 5.5.4.5 の形）。
- partial は 17 件。
  - 9.5.5.x：κ-presentable を一つの定義にしたものはない。濃度を変えられるのは cardinal-change bound を満たす μ だけで、presentable の特徴づけも ⇒ 向きだけ。
  - 9.5.6〜9.5.7：Bousfield 局所化関手と「Bousfield 局所化」を名前の付いた定義にしたものはない。9.5.7.5 は (2)⇒(1) だけ。9.5.7.2 は全関手を標的とする IsLocalization の形でしかない。
  - 9.6.9.23・9.6.9.25：強飽和閉包が局所同値と一致する片側だけで、分類の全単射はない。
  - 9.7.1.x：一般の相対余完備化はない。あるのは Ind_κ と P_Σ の場合（`indKappaContinuousRestriction_isQCatEquivalence`、`sigmaSiftedContinuousRestriction_isQCatEquivalence`、`sigma_preservesSmallColimits_iff_yoneda_of_cocomplete`）だけ。
- mathlib は 1 件：9.6.0.3（1 圏の弱分解系、`MorphismProperty.IsWeakFactorizationSystem`）。
- 9.6 の ∞ 圏の部分（超限合成・弱局所対象・small object argument・持ち上げ・直交性・分解系）は全部 none。
  - 1 圏の類似は note に書いた。Mathlib の TransfiniteComposition・SmallObject・HasLiftingProperty・ObjectProperty.isLocal・OrthogonalReflection と、SerrePositivity の HomotopicalAlgebra/Smith にある。
  - 規則どおり、1 圏の類似は status に数えていない。
- 9.5.5 の Ind_κ^λ・κ-cocompletion 系（9.5.5.5〜.14、.18、.19）と Fun^cocont の presentable 性（9.5.5.16）は none。functor_isPresentable は全関手の圏についての結果。
- 9.5.5.15 は抜粋が途中で切れていて主張が読めないので、low とした。
- sorry：引いた F2/Presentable・HomotopyLimits・F1B/Localization・F2/Ind のファイルを grep したが、本体に sorry はなかった。Archive/ のコードは使っていない。
- KST・DerivedGeometry の HomotopyOrthogonal 系は、複体の 1 圏の話で該当しないと判断した。

### c27

130 項目すべてを判定した（入力 130 件、出力 130 件）。どの項目も citedBy は 0 件だった。

- **9.7.2（sifted）**：F2/Presentable/ に自前の版がある。ファイルの置き場所は F2 だが、名前空間は HomotopyLimits。
  - IsSiftedInfinity は、Kerodon 9.7.2.8 の同値な形（非空で、二項対角が right cofinal）で定義している。HTT 5.5.8.1 の形。
  - 弱可縮性（9.7.2.7）、Δ^op が sifted であること（9.7.2.10）、余積をもてば sifted（9.7.2.9）は自前にある。
  - 9.7.2.12 は、sifted なら空間の積が余極限と交換する、という向きだけがある。
  - Mathlib の IsSifted（1 圏）は、9.7.2.5・6・12 の 1 圏版として partial に記した。
  - grep の範囲では sorry は見つからなかった。
- **9.7.3〜9.7.8**：Lurie のテンソル積、locally truncated、idempotent ∞ 圏は、自前にも Mathlib にもない。tensor_isPresentable は二項直積の presentable 性で、テンソル積とは別物。
- **10.1**：∞ 圏の単体的・半単体的対象、Čech nerve、skeleton・coskeleton、split、décalage は、自前に一つもない。
  - 自前にあるのは、P_Σ の文脈の HasSmallGeometricRealizations と PreservesSmallGeometricRealizations だけ。
  - Mathlib には 1 圏の版が多くある：SimplicialObject(.Augmented)、AugmentedSimplexCategory、SemiSimplexCategory、Arrow.augmentedCechNerve・cechNerveAdjunction、sk・cosk・IsCoskeletal、ExtraDegeneracy。これらはすべて partial（1 圏の版のみ）として記した。
  - Mathlib の Splitting は Dold–Kan 型の分解なので、Kerodon の split とは違う。Kerodon の split に近いのは ExtraDegeneracy。
- Archive・KST・Derived を探しても、該当するものはなかった。
- テキストが途中で切れている項目は推定で判定し、confidence を low か med にした（9.7.2.9・9.7.2.10・10.1.6.7 など）。

### c28

c28 は Kerodon 10.2（正則 ∞ 圏）の全 66 項目です。ファイルの項目数は 66 件で、入力と一致しています。SerrePositivity 全体（KST・HomotopicalAlgebra・Spectra・Inputs を含め、Archive は除外）を探しましたが、10.2 のどの項目に当たる宣言もありませんでした。調べた対象は、∞ 圏の sieve、quotient morphism、像、universal quotient、正則 ∞ 圏です。名前に sieve を含む宣言は F2/Tensor/SetSections* にありますが、これは 1 圏の Mathlib Sieve を使ったもので、10.2.1 の単体的集合の sieve とは別物です。

Mathlib にあるのは 1 圏の 2 項目です。
- 10.2.0.2：RegularEpi（RegularMono.lean:307）。核対の余等化子の形との同値は regularEpiOfKernelPair（:451）と regularEpiOfEffectiveEpi（:509）にあります。
- 10.2.0.6：CategoryTheory.Regular（RegularCategory/Basic.lean:52）。定義の形が違い、Kerodon の「像の存在」は hasStrongEpiMonoFactorisations として証明されています。

「一部」は 10.2.4.9 の 1 件です。Mathlib には epi_iff_surjective と RegularEpi.ofSplitEpi がありますが、universal quotient としての同値は明示されていません。

ほかに気づいたこと：
- 10.2.1.29 と 10.2.2.17 は入力の text が切れていて、中身を確認できませんでした（10.2.1.29 は confidence low）。
- citedBy は全項目で空で、Lean の docstring は 10.2 の番号を一度も引いていません。
- 既存の coverage-ch8-10.md の判定（10.2 は 0/0/5 で全部なし）と合っています。
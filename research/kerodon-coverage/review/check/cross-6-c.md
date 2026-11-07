# 第6章の交差抜き取り検査（research/kerodon-review-c）

- 対象は main の `dc3ebc8ab`。依頼に従い第4〜6章を選んだ。既存の同名の抜き取り報告と区別するため、ファイル名に `-c` を付けた。
- 乱数の種は `0x81e593fc`。Python 3.14.7 の `random.Random(seed).sample` で、章を 4→5→6、区分を own・both・mathlib の合算→none の順に処理した。各母集団は項目番号の数値順、各区分は重複なしの20件。
- 元表の status と引用で抽出・型の取得を行い、Kerodon 本文、段1・段1′と章別 kernel evidence の型、Lean ソースから判定した。元表の reason は判定に使っていない。
- none では (a) 元の citations.csv と Lean docstring の該当番号・同小節の引用、(b) 宣言名と型の語索引を原方向・双対・普通圏の語で検索、(c) 同小節の own・both の引用ファイルと同じディレクトリの宣言を検索した。近傍は起点がなければ mathlib・partial、同小節の引用、候補の順で補った。候補の採否は各行の型・ソースとの照合による。
- 差は status の変更で数えた。§8.1 に従い、特例・一方向・強い仮定・複数結論の一部が直接確認できる場合を partial とした。

| 元の区分 | 母集団 | 抽出 | 差 | 差の割合 |
|---|---:|---:|---:|---:|
| own・both・mathlib | 31 | 20 | 0 | 0% |
| none | 52 | 20 | 3 | 15% |

## own・both・mathlib

| Kerodon | 元の status | 照合結果 | 仮定・結論と確認した宣言 |
|---|---|---|---|
| [6.1.0.2](https://kerodon.net/tag/02CC) | mathlib | mathlib | 仮定：普通圏間の二つの関手（一致）。結論：Adjunction.CoreUnitCounit と mkOfUnitCounit は自然変換の単位・余単位と二つの成分三角恒等式を包装する（一致）。 `CategoryTheory.Adjunction` (Mathlib/CategoryTheory/Adjunction/Basic.lean:108), `CategoryTheory.Adjunction.mkOfUnitCounit` (Mathlib/CategoryTheory/Adjunction/Basic.lean:460) |
| [6.1.2.8](https://kerodon.net/tag/02CX) | mathlib | mathlib | 仮定：bicategory、単位候補・余単位候補、左三角（一致）。結論：右 zigzag の冪等式が一致し、片側逆がある場合は Hom 圏でその逆による消去から恒等式が従う（一致）。 `CategoryTheory.Bicategory.rightZigzag_idempotent_of_left_triangle` (Mathlib/CategoryTheory/Bicategory/Adjunction/Basic.lean:73) |
| [6.1.2.9](https://kerodon.net/tag/02CY) | own | own | 仮定：任意の bicategory と固定した η（一致）。結論：全ての T,c,d に対する Hom 写像の全単射と指定単位の随伴の存在は iff。Bicategory.Adjunction.homEquiv₂ の順写像は η のみに依存し、g=r、h=id で逆写像を左 unitor の逆に評価すると余単位を復元するので、同じ η に対する余単位は一意（一致）。 `SerrePositivity.InfinityCategories.bicategory_exists_adjunction_unit_iff` (SerrePositivity/InfinityCategories/F1B/Adjunction/UnitHomCriterion.lean:114), `SerrePositivity.InfinityCategories.bicategoryAdjunctionOfUnitHomBijective` (SerrePositivity/InfinityCategories/F1B/Adjunction/UnitHomCriterion.lean:93) |
| [6.1.2.10](https://kerodon.net/tag/02CZ) | own | own | 仮定：任意の bicategory と固定した η（一致）。結論：指定の η を単位とする随伴の存在が、全パラメータの Hom 全単射条件と同値（一致）。 `SerrePositivity.InfinityCategories.bicategory_exists_adjunction_unit_iff` (SerrePositivity/InfinityCategories/F1B/Adjunction/UnitHomCriterion.lean:114) |
| [6.1.3.1](https://kerodon.net/tag/02D5) | mathlib | mathlib | 仮定：η が随伴の単位（一致）。結論：homEquiv₂ を g=id に取ることと homEquiv₁ の逆を該当する h=id に取ることにより、左右の unitor を介して二つの単位による全単射を得る（一致）。 `CategoryTheory.Bicategory.Adjunction.homEquiv₂` (Mathlib/CategoryTheory/Bicategory/Adjunction/Mate.lean:91), `CategoryTheory.Bicategory.Adjunction.homEquiv₁` (Mathlib/CategoryTheory/Bicategory/Adjunction/Mate.lean:64) |
| [6.1.3.2](https://kerodon.net/tag/02D6) | mathlib | mathlib | 仮定：ε が随伴の余単位（一致）。結論：homEquiv₁ と homEquiv₂ の逆を恒等 1-射で特殊化し、unitor を介して二つの余単位による全単射を得る（一致）。 `CategoryTheory.Bicategory.Adjunction.homEquiv₁` (Mathlib/CategoryTheory/Bicategory/Adjunction/Mate.lean:64), `CategoryTheory.Bicategory.Adjunction.homEquiv₂` (Mathlib/CategoryTheory/Bicategory/Adjunction/Mate.lean:91) |
| [6.1.4.2](https://kerodon.net/tag/02DF) | mathlib | mathlib | 仮定：f と指定の g が可逆な単位候補と余単位候補を持つ（一致）。結論：mkOfAdjointifyCounit が g を保つ Equivalence を作り adj が f⊣g を与える。対称な Equivalence で g⊣f（一致）。 `CategoryTheory.Bicategory.Equivalence.mkOfAdjointifyCounit` (Mathlib/CategoryTheory/Bicategory/Adjunction/Basic.lean:276), `CategoryTheory.Bicategory.Equivalence.adj` (Mathlib/CategoryTheory/Bicategory/Adjunction/Basic.lean:285) |
| [6.1.5.4](https://kerodon.net/tag/02DS) | mathlib | mathlib | 仮定：二つの単位が随伴を与える（一致）。結論：Adjunction.comp の compUnit が whiskering と associator による指定の単位の縮約で、その随伴を構成する（一致）。 `CategoryTheory.Bicategory.Adjunction.comp` (Mathlib/CategoryTheory/Bicategory/Adjunction/Basic.lean:161) |
| [6.1.5.5](https://kerodon.net/tag/02DT) | mathlib | mathlib | 仮定：二組の随伴（一致）。結論：前向き関手を順方向、右随伴を逆順に合成した随伴（一致）。 `CategoryTheory.Bicategory.Adjunction.comp` (Mathlib/CategoryTheory/Bicategory/Adjunction/Basic.lean:161) |
| [6.1.5.9](https://kerodon.net/tag/02DX) | mathlib | mathlib | 仮定：二組の単位と余単位を持つ随伴（一致）。結論：Adjunction.comp の単位 compUnit と余単位 compCounit はそれぞれ本文の pasting であり両三角を満たす（一致）。 `CategoryTheory.Bicategory.Adjunction.comp` (Mathlib/CategoryTheory/Bicategory/Adjunction/Basic.lean:161) |
| [6.2.1.1](https://kerodon.net/tag/02EK) | own | own | 仮定：準圏間の F,G と単位・余単位の homotopy class（一致）。結論：h Fun で両 zigzag の恒等式を要求し QCatAdjunction を得る。QCatAdjunction の三角の射影で条件を回収（一致）。 `SerrePositivity.InfinityCategories.QCatAdjunction.mkOfHomTriangles` (SerrePositivity/InfinityCategories/F1B/Adjunction/Adjunction.lean:191), `SerrePositivity.InfinityCategories.QCatAdjunction` (SerrePositivity/InfinityCategories/F1B/Adjunction/Adjunction.lean:38), `SerrePositivity.InfinityCategories.QCatAdjunction.left_triangle_hom` (SerrePositivity/InfinityCategories/F1B/Adjunction/Adjunction.lean:272) |
| [6.2.1.2](https://kerodon.net/tag/02EL) | own | own | 仮定：準圏間の F,G（一致）。結論：QCatAdjunction は単位・余単位と二三角のデータ。Nonempty で存在を表し、単位からの定義と余単位からの定義は同じデータを指定する（一致）。 `SerrePositivity.InfinityCategories.QCatAdjunction` (SerrePositivity/InfinityCategories/F1B/Adjunction/Adjunction.lean:38), `SerrePositivity.InfinityCategories.QCatAdjunction.unitHom` (SerrePositivity/InfinityCategories/F1B/Adjunction/Adjunction.lean:239) |
| [6.2.1.4](https://kerodon.net/tag/02EN) | own | own | 仮定：F,G と二自然変換の homotopy class（一致）。結論：qcatHomFunctor と qcatCellEquiv が h₂ の 2-射と h Fun の射を同定し、mkOfHomTriangles と三角の射影が両向きを与える（一致）。 `SerrePositivity.InfinityCategories.QCatAdjunction` (SerrePositivity/InfinityCategories/F1B/Adjunction/Adjunction.lean:38), `SerrePositivity.InfinityCategories.qcatHomFunctor` (SerrePositivity/InfinityCategories/F1B/Adjunction/Adjunction.lean:47), `SerrePositivity.InfinityCategories.qcatCellEquiv` (SerrePositivity/InfinityCategories/F1B/Adjunction/Adjunction.lean:63) |
| [6.2.1.15](https://kerodon.net/tag/02EZ) | own | own | 仮定：準圏間の F,G に QCatAdjunction（一致）。結論：toHoAdjunction の左右はそれぞれ hF,hG（一致）。 `SerrePositivity.InfinityCategories.QCatAdjunction.toHoAdjunction` (SerrePositivity/InfinityCategories/F1B/Adjunction/HomotopyCategory.lean:85), `SerrePositivity.InfinityCategories.QCatAdjunction.hoHomEquiv` (SerrePositivity/InfinityCategories/F1B/Adjunction/HomotopyCategory.lean:78) |
| [6.2.3.10](https://kerodon.net/tag/06TB) | own | own | 仮定：準圏の ReflectiveSubcategory と reflector が逆にする辺（一致）。結論：reflective_isLocal_iff_invertedEdges と isLocal_iff_essentialImage の合成で W-local と反射部分圏の対象に同型が同値。replete の場合は述語が一致（一致）。 `SerrePositivity.InfinityCategories.HomotopyLimits.reflective_isLocal_iff_invertedEdges` (SerrePositivity/InfinityCategories/HomotopyLimits/ReflectiveInvertedHom.lean:59), `SerrePositivity.InfinityCategories.ReflectiveSubcategory.isLocal_iff_essentialImage` (SerrePositivity/InfinityCategories/F1B/Localization/ReflectiveLocalObjects.lean:77), `SerrePositivity.InfinityCategories.HomotopyLimits.reflective_localEquivalences_eq` (SerrePositivity/InfinityCategories/HomotopyLimits/ReflectiveInvertedHom.lean:124) |
| [6.2.6.4](https://kerodon.net/tag/02FW) | mathlib | mathlib | 仮定：普通圏間の G（一致）。結論：isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top の leftAdjointObjIsDefined は G を通じた Hom(X,-) の IsCorepresentable を表すので対象毎の余表現可能性と右随伴性が同値（一致）。 `CategoryTheory.Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top` (Mathlib/CategoryTheory/Adjunction/PartialAdjoint.lean:142) |
| [6.3.0.1](https://kerodon.net/tag/01M5) | mathlib | mathlib | 仮定：普通圏の F と MorphismProperty W、任意の固定終域 E（一致）。結論：StrictUniversalPropertyFixedTarget の inverts、lift、fac、uniq が指定の前合成の全単射を表す。全ての E に課すのが本文の strict localization（一致）。 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget` (Mathlib/CategoryTheory/Localization/Predicate.lean:75) |
| [6.3.1.1](https://kerodon.net/tag/01MF) | own | own | 仮定：単体集合 C、辺集合 W、準圏 E（一致）。結論：invertingFunctors は W を可逆に送る関手の充満部分単体集合で、準圏性も確認（一致）。 `SerrePositivity.InfinityCategories.invertingFunctors` (SerrePositivity/InfinityCategories/F1B/Localization/Localization.lean:57), `SerrePositivity.InfinityCategories.invertingFunctors_quasicategory` (SerrePositivity/InfinityCategories/F1B/Localization/Localization.lean:63) |
| [6.3.1.23](https://kerodon.net/tag/02LT) | own | own | 仮定：F が W に関する局所化で W' の各辺の像が退化（宣言は可逆で足りるので弱い）。結論：W⊆W∪W'⊆invertedEdges F を用いて同じ F が W∪W' に関する局所化（一致）。 `SerrePositivity.InfinityCategories.IsLocalization.of_subset_invertedEdges` (SerrePositivity/InfinityCategories/F1B/Localization/Saturation.lean:23) |
| [6.3.2.1](https://kerodon.net/tag/01N0) | own | own | 仮定：任意の単体集合と辺集合（一致）。結論：準圏を終域とする IsLocalization の存在（一致）。 `SerrePositivity.KST.LocalizingInvariants.exists_quasicategory_localization` (SerrePositivity/KST/LocalizingInvariants/LocalizationResolution.lean:37), `SerrePositivity.KST.LocalizingInvariants.inverseAttachment_isLocalization` (SerrePositivity/KST/LocalizingInvariants/InverseAttachmentUniversal.lean:28) |

## none

### [6.2.1.21](https://kerodon.net/tag/06T9) · `none → none`

随伴の Hom 比較にはホモトピー類版と写像空間版がある。任意の整数 n について G の対象の n-truncated 性を結論する型を確認できない。

- (a) `6.2.1.21` と `6.2.1`、`Kerodon`。直接 0 件、同小節 99 件。参照例 `SerrePositivity/InfinityCategories/F1B/Adjunction/Adjunction.lean:6`, `SerrePositivity/InfinityCategories/F1B/Adjunction/Adjunction.lean:10`。
- (b) `right adjoint truncated objects / preserves n truncation / mapping space adjunction`。双対の語 `adjoint adjunction left mapping objects preserves space truncated truncation`。普通圏の語 `adjoint adjunction mapping objects preserves right space truncated truncation`。確認した候補 `QCatAdjunction.hoHomEquiv` (`SerrePositivity/InfinityCategories/F1B/Adjunction/HomotopyCategory.lean:78`), `QCatAdjunction.pinchedEquivalenceIntervalIso` (`SerrePositivity/InfinityCategories/F1B/MappingSpaces/PinchedEquivalenceClasses.lean:73`)。
- (c) 同小節の own・bothを起点に (b) の語で `SerrePositivity/InfinityCategories/F1B/Adjunction` を検索。対象の宣言見出し 409 件。

### [6.2.2.14](https://kerodon.net/tag/05Q7) · `none → none`

一般の反射部分圏と局所同値の性質。h≤n、局所 (n−1)-切断準圏の部分圏、κ-small 版の反射は候補の型に現れない。

- (a) `6.2.2.14` と `6.2.2`、`Kerodon`。直接 0 件、同小節 6 件。参照例 `SerrePositivity/InfinityCategories/F1B/Localization/Reflective.lean:6`, `SerrePositivity/InfinityCategories/F1B/Localization/Reflective.lean:10`。
- (b) `homotopy n category reflection / local truncation reflective QC / truncated quasicategory localization`。双対の語 `category homotopy localization qc quasicategory reflection reflective truncated truncation`。普通圏の語 `category homotopy localization qc quasicategory reflection reflective truncated truncation`。確認した候補 `ReflectiveSubcategory` (`SerrePositivity/InfinityCategories/F1B/Localization/Reflective.lean:26`), `reflective_localEquivalences_eq` (`SerrePositivity/InfinityCategories/HomotopyLimits/ReflectiveInvertedHom.lean:124`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Presentable`, `SerrePositivity/InfinityCategories/F1B/Adjunction`, `SerrePositivity/InfinityCategories/F1B/Localization`, `SerrePositivity/InfinityCategories/F2/Presentable`, `SerrePositivity/InfinityCategories/HomotopyLimits`, `SerrePositivity/InfinityCategories/HomotopyLimits/Presentable` を検索。対象の宣言見出し 7996 件。

### [6.2.2.18](https://kerodon.net/tag/04JE) · `none → none`

反射の随伴と普通圏 Over の忘却随伴は異なる。固定図式 q を保って反射が slice に降りる宣言は確認できない。

- (a) `6.2.2.18` と `6.2.2`、`Kerodon`。直接 0 件、同小節 6 件。参照例 `SerrePositivity/InfinityCategories/F1B/Localization/Reflective.lean:6`, `SerrePositivity/InfinityCategories/F1B/Localization/Reflective.lean:10`。
- (b) `reflective slice over diagram / reflector restrict over / coreflective coslice`。双対の語 `coreflective coslice diagram reflective reflector restrict slice under`。普通圏の語 `coreflective coslice diagram over reflective reflector restrict slice`。確認した候補 `ReflectiveSubcategory` (`SerrePositivity/InfinityCategories/F1B/Localization/Reflective.lean:26`), `reflectorAdjunction` (`Mathlib/CategoryTheory/Adjunction/Reflective.lean:51`), `forgetAdjStar` (`Mathlib/CategoryTheory/Comma/Over/Pullback.lean:160`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Presentable`, `SerrePositivity/InfinityCategories/F1B/Adjunction`, `SerrePositivity/InfinityCategories/F1B/Localization`, `SerrePositivity/InfinityCategories/F2/Presentable`, `SerrePositivity/InfinityCategories/HomotopyLimits`, `SerrePositivity/InfinityCategories/HomotopyLimits/Presentable` を検索。対象の宣言見出し 7996 件。

### [6.2.2.28](https://kerodon.net/tag/03UZ) · `none → partial`（partial_kind: `component`）

同値 F の逆を右随伴とする toAdjunction と、逆同値の isFullyFaithful により (2) を得る。普通圏の逆向きの類似定理は左右両方の全忠実性を要求する。高次で (1),(2) から関手全体の同値を結論する型は未確認。

- (a) `6.2.2.28` と `6.2.2`、`Kerodon`。直接 0 件、同小節 6 件。参照例 `SerrePositivity/InfinityCategories/F1B/Localization/Reflective.lean:6`, `SerrePositivity/InfinityCategories/F1B/Localization/Reflective.lean:10`。
- (b) `conservative fully faithful right adjoint equivalence / reflects isomorphisms unit / QCatAdjunction equivalence`。双対の語 `adjoint adjunction cat conservative equivalence faithful fully isomorphisms left reflects unit`。普通圏の語 `adjoint adjunction cat conservative equivalence faithful fully isomorphisms reflects right unit`。確認した候補 `QCatEquivalence.toAdjunction` (`SerrePositivity/InfinityCategories/F1B/QCatEquivalenceAdjunction.lean:34`), `QCatEquivalence.symm` (`SerrePositivity/InfinityCategories/Core/Equivalence.lean:139`), `QCatEquivalence.isFullyFaithful` (`SerrePositivity/InfinityCategories/Core/EquivalenceFullyFaithful.lean:40`), `Functor.isEquivalence_of_isRightAdjoint` (`Mathlib/CategoryTheory/Adjunction/Basic.lean:704`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Presentable`, `SerrePositivity/InfinityCategories/F1B/Adjunction`, `SerrePositivity/InfinityCategories/F1B/Localization`, `SerrePositivity/InfinityCategories/F2/Presentable`, `SerrePositivity/InfinityCategories/HomotopyLimits`, `SerrePositivity/InfinityCategories/HomotopyLimits/Presentable` を検索。対象の宣言見出し 7996 件。

### [6.2.4.1](https://kerodon.net/tag/05Z1) · `none → none`

既に指定された局所同値集合の可逆辺包含・消去は確認。候補集合 W に弱い消去と各対象の lift を課して反射を構成し W を同定する結論を得ない。

- (a) `6.2.4.1` と `6.2.4`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `local equivalences existence reflection two out of three / localization orthogonal reflection / reflector class saturated`。双対の語 `equivalences existence localization orthogonal out reflection reflector saturated three two`。普通圏の語 `equivalences existence lifting llp localization out reflection reflector rlp saturated three two`。確認した候補 `localEquivalences_compStruct_cancel_right` (`SerrePositivity/InfinityCategories/HomotopyLimits/Presentable/LocalEquivalenceTriangles.lean:62`), `localEquivalences_mem_of_isInvertibleEdge` (`SerrePositivity/InfinityCategories/HomotopyLimits/Presentable/LocalEquivalenceTriangles.lean:33`), `reflective_localEquivalences_eq` (`SerrePositivity/InfinityCategories/HomotopyLimits/ReflectiveInvertedHom.lean:124`)。
- (c) 候補を起点に (b) の語で `SerrePositivity/InfinityCategories/HomotopyLimits`, `SerrePositivity/InfinityCategories/HomotopyLimits/Presentable` を検索。対象の宣言見出し 5210 件。

### [6.2.4.5](https://kerodon.net/tag/05Z6) · `none → none`

反射と輸送は別々に定義される。cartesian 輸送による反射部分圏の保存から全空間に反射を構成する型は未確認。

- (a) `6.2.4.5` と `6.2.4`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `fiberwise reflective subcategory cartesian fibration / reflector transport preserves / Grothendieck fiber adjunction`。双対の語 `adjunction cocartesian fiber fiberwise fibration grothendieck preserves reflective reflector subcategory transport`。普通圏の語 `adjunction fiber fiberwise fibre grothendieck lifting preserves pullback reflective reflector subcategory transport`。確認した候補 `ReflectiveSubcategory` (`SerrePositivity/InfinityCategories/F1B/Localization/Reflective.lean:26`), `homotopyTransport` (`SerrePositivity/InfinityCategories/F1/Transport/HomotopyTransport.lean:30`), `reflectorAdjunction` (`Mathlib/CategoryTheory/Adjunction/Reflective.lean:51`)。
- (c) 候補を起点に (b) の語で `Mathlib/CategoryTheory/Adjunction`, `SerrePositivity/InfinityCategories/F1/Transport`, `SerrePositivity/InfinityCategories/F1B/Localization` を検索。対象の宣言見出し 1437 件。

### [6.2.4.9](https://kerodon.net/tag/05ZA) · `none → none`

始域射影の inner 性と、反射が既にある場合の局所化。左 fibration の仮定から二つの引戻しの反射、および指定の三条件を得る型ではない。

- (a) `6.2.4.9` と `6.2.4`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `oriented pullback reflective subcategory / homotopy pullback left fibration reflector / comma local equivalence`。双対の語 `comma equivalence fibration homotopy oriented pushout reflective reflector right subcategory`。普通圏の語 `comma equivalence homotopy left lifting oriented pullback reflective reflector subcategory`。確認した候補 `unitCommaSource_innerFibration` (`SerrePositivity/InfinityCategories/F1B/Adjunction/UnitComma.lean:77`), `isLocalization` (`SerrePositivity/InfinityCategories/F1B/Localization/ReflectiveLocalization.lean:118`)。
- (c) 候補を起点に (b) の語で `Mathlib/Algebra/Polynomial`, `Mathlib/CategoryTheory/Localization`, `Mathlib/RingTheory`, `Mathlib/RingTheory/DedekindDomain`, `Mathlib/RingTheory/Localization`, `Mathlib/RingTheory/MvPolynomial`, `SerrePositivity/InfinityCategories/F1B/Adjunction`, `SerrePositivity/InfinityCategories/F1B/Localization` を検索。対象の宣言見出し 6135 件。

### [6.2.5.1](https://kerodon.net/tag/02FK) · `none → none`

大域の辺の充填性と相対 coslice 制限の判定。Δ¹ の端のファイバーへの (co)reflection と cartesian 辺の iff は未確認。

- (a) `6.2.5.1` と `6.2.5`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `cartesian edge reflection interval / coreflection cocartesian fiber endpoint / over delta one`。双対の語 `cartesian cocartesian coreflection delta edge endpoint fiber interval one reflection under`。普通圏の語 `cocartesian coreflection delta edge endpoint fiber fibre interval one over pullback reflection`。確認した候補 `isCartesianEdge_of_rightFibration` (`SerrePositivity/InfinityCategories/F1/Fibrations/CartesianEdge.lean:44`), `relativeCosliceRestriction_source_of_isCocartesianEdge` (`SerrePositivity/InfinityCategories/F1/Cocartesian/SourceRestriction.lean:42`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/HomotopyLimits`, `SerrePositivity/InfinityCategories/ModelBridge` を検索。対象の宣言見出し 5928 件。

### [6.2.5.5](https://kerodon.net/tag/06MB) · `none → none`

大域的輸送の指定と随伴の h への降下。局所 lift の両条件を結び、同一の底辺で e_!⊣e^* を返す型はない。

- (a) `6.2.5.5` と `6.2.5`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `locally cocartesian cartesian transport adjunction / adjoint transport fibration / push pull mates`。双対の語 `adjoint adjunction cartesian cocartesian fibration locally mates pull push transport`。普通圏の語 `adjoint adjunction cocartesian lifting locally mates pull pullback push transport`。確認した候補 `homotopyTransport_map_isTransport` (`SerrePositivity/InfinityCategories/F1/Transport/HomotopyTransport.lean:68`), `QCatAdjunction.toHoAdjunction` (`SerrePositivity/InfinityCategories/F1B/Adjunction/HomotopyCategory.lean:85`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/HomotopyLimits`, `SerrePositivity/InfinityCategories/ModelBridge` を検索。対象の宣言見出し 5928 件。

### [6.2.7.6](https://kerodon.net/tag/03XJ) · `none → partial`（partial_kind: `special`）

C が Kan の場合、可逆辺は全辺なので短射の全体を選べる。core は全辺を可逆と要求するこの場合の部分複体。任意の短射クラス S を入力として頂点全て、辺は S という部分複体を得る宣言は未確認。

- (a) `6.2.7.6` と `6.2.7`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `short morphism subcomplex all edges / edge spanned subcomplex / quasicategory core`。双対の語 `core edge edges morphism quasicategory short spanned subcomplex`。普通圏の語 `core edge edges morphism quasicategory short spanned subcomplex`。確認した候補 `quasicategoryCore` (`SerrePositivity/InfinityCategories/F1/Categories/QuasicategoryCore.lean:23`), `invertedEdges` (`SerrePositivity/InfinityCategories/F1B/Localization/Localization.lean:28`)。
- (c) 候補を起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Categories`, `SerrePositivity/InfinityCategories/F1B/Localization` を検索。対象の宣言見出し 497 件。

### [6.2.7.12](https://kerodon.net/tag/03XQ) · `none → none`

経路の長さと可逆辺の部分複体はある。指定辺 f を長辺とする短射の合成の最小値や長さ 0,1 の判定は確認できない。

- (a) `6.2.7.12` と `6.2.7`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `short morphism minimal length / spine factorization / quiver path length`。双対の語 `factorization length minimal morphism path quiver short spine`。普通圏の語 `factorization length minimal morphism path quiver short spine`。確認した候補 `length` (`Mathlib/Combinatorics/Quiver/Path.lean:63`), `quasicategoryCore` (`SerrePositivity/InfinityCategories/F1/Categories/QuasicategoryCore.lean:23`)。
- (c) 候補を起点に (b) の語で `Mathlib/Algebra`, `Mathlib/Algebra/FreeMonoid`, `Mathlib/Algebra/Order/Interval`, `Mathlib/Combinatorics/Enumerative`, `Mathlib/Combinatorics/Quiver`, `Mathlib/Combinatorics/SimpleGraph/Walk`, `Mathlib/Control`, `Mathlib/Data/List`, `Mathlib/Data/Seq`, `Mathlib/Data/Vector`, `Mathlib/Data/WSeq`, `Mathlib/GroupTheory/Coxeter`, `Mathlib/GroupTheory/FreeGroup`, `Mathlib/MeasureTheory/Measure`, `Mathlib/RingTheory`, `Mathlib/Tactic/ClickSuggestions`, `SerrePositivity/EInfinity/TableReduction`, `SerrePositivity/HomotopicalAlgebra/Rectification/Simplicial`, `SerrePositivity/InfinityCategories/F1/Categories` を検索。対象の宣言見出し 12422 件。

### [6.2.7.14](https://kerodon.net/tag/03XT) · `none → none`

最後の頂点と全辺可逆の条件はある。各 q から最後までが S に入る最小 p、面での不等式、退化での p または p+1 は確認できない。

- (a) `6.2.7.14` と `6.2.7`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `short simplex priority face degeneracy / terminal vertex edge short / filtration last vertex`。双対の語 `degeneracy edge face filtration initial last priority short simplex vertex`。普通圏の語 `degeneracy edge face filtration last priority short simplex terminal vertex`。確認した候補 `quasicategoryCore` (`SerrePositivity/InfinityCategories/F1/Categories/QuasicategoryCore.lean:23`), `simplexLastVertex` (`SerrePositivity/InfinityCategories/Core/TerminalExtension.lean:23`)。
- (c) 候補を起点に (b) の語で `SerrePositivity/InfinityCategories/Core`, `SerrePositivity/InfinityCategories/Derived/Localization`, `SerrePositivity/InfinityCategories/F1/Categories` を検索。対象の宣言見出し 2792 件。

### [6.3.2.7](https://kerodon.net/tag/05ZJ) · `none → none`

逆辺を付加する局所化、標準単体の transport 模型の局所化を確認。Δ³ の二辺 02,13 を同時に潰す指定商の点への圏論的同値は確認できない。

- (a) `6.3.2.7` と `6.3.2`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `tetrahedron collapse two edges categorical equivalence / delta three quotient diagonal / inverse attachment collapse`。双対の語 `attachment categorical collapse delta diagonal edges equivalence inverse quotient tetrahedron three two`。普通圏の語 `attachment categorical collapse delta diagonal edges effective epi equivalence inverse regular tetrahedron three two`。確認した候補 `inverseAttachment_isLocalization` (`SerrePositivity/KST/LocalizingInvariants/InverseAttachmentUniversal.lean:28`), `transportSimplexFirstVertexMap_standard_isLocalization` (`SerrePositivity/InfinityCategories/F1/Transport/StandardLocalization.lean:113`)。
- (c) 同小節の own・bothを起点に (b) の語で `SerrePositivity/KST/LocalizingInvariants` を検索。対象の宣言見出し 8788 件。

### [6.3.4.1](https://kerodon.net/tag/038U) · `none → none`

初頂点写像の指定局所化と局所化済みの射への辺追加。底の局所化と各ファイバーの局所化から全空間を導く型はない。

- (a) `6.3.4.1` と `6.3.4`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `cocartesian fiberwise localization base / Grothendieck localization total / fiber and horizontal edge class`。双対の語 `base cartesian edge fiber fiberwise grothendieck horizontal localization total`。普通圏の語 `base cocartesian edge fiber fiberwise fibre grothendieck horizontal localization total`。確認した候補 `transportSimplexFirstVertexMap_isLocalization` (`SerrePositivity/InfinityCategories/F1/Transport/LocalizationAllBases.lean:23`), `IsLocalization.of_subset_invertedEdges` (`SerrePositivity/InfinityCategories/F1B/Localization/Saturation.lean:23`)。
- (c) 候補を起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Transport`, `SerrePositivity/InfinityCategories/F1B/Localization` を検索。対象の宣言見出し 1063 件。

### [6.3.4.2](https://kerodon.net/tag/02LW) · `none → none`

特定 transport 模型の局所化と押出しに沿うその組立て。各ファイバーで局所化する任意の cocartesian 辺保存射に対する貼合せはない。

- (a) `6.3.4.2` と `6.3.4`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `fiberwise localization fixed base / cocartesian localization total space / localized relative functor`。双対の語 `base cartesian fiberwise fixed functor localization localized relative space total`。普通圏の語 `base cocartesian fiberwise fixed functor localization localized relative space total`。確認した候補 `transportSimplexFirstVertexMap_isLocalization_of_isPushout` (`SerrePositivity/InfinityCategories/F1/Transport/LocalizationPushout.lean:20`), `transportSimplexFirstVertexMap_isLocalization` (`SerrePositivity/InfinityCategories/F1/Transport/LocalizationAllBases.lean:23`)。
- (c) 候補を起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Transport` を検索。対象の宣言見出し 938 件。

### [6.3.4.3](https://kerodon.net/tag/02LY) · `none → none`

指定の初頂点写像は局所化で、別の補題は coslice の特定ファイバーの可縮性。全ファイバーが弱可縮である cocartesian fibration と退化像の全辺という組で同時に一致する型は未確認。

- (a) `6.3.4.3` と `6.3.4`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `contractible fibers cocartesian localization / vertical edges localization / transport simplex first vertex`。双対の語 `cartesian contractible edges fibers first localization simplex transport vertex vertical`。普通圏の語 `cocartesian contractible edges fibers first localization simplex transport vertex vertical`。確認した候補 `transportSimplexFirstVertexMap_isLocalization` (`SerrePositivity/InfinityCategories/F1/Transport/LocalizationAllBases.lean:23`), `cosliceFiberProjection_terminalFiber_isContractibleKan` (`SerrePositivity/InfinityCategories/Core/CosliceFiberProjection.lean:92`)。
- (c) 候補を起点に (b) の語で `SerrePositivity/InfinityCategories/Core`, `SerrePositivity/InfinityCategories/F1/Transport` を検索。対象の宣言見出し 3278 件。

### [6.3.4.6](https://kerodon.net/tag/02LV) · `none → partial`（partial_kind: `special`）

普通圏で W が恒等射を含み、F が普通圏の局所化も与える場合、第二因子に F、第一因子に恒等射のクラスに関する恒等局所化を取れる。任意の単体集合 K と、K 成分が退化した辺だけを指定する高次の命題は確認できない。

- (a) `6.3.4.6` と `6.3.4`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `product localization with identities / tensor localization edge set / cartesian closed precomposition`。双対の語 `closed cocartesian coproduct edge identities localization postcomposition set tensor`。普通圏の語 `closed edge identities localization precomposition product pullback set tensor`。確認した候補 `SupClosed.prod` (`Mathlib/Order/SupClosed.lean:100`), `invertingFunctors` (`SerrePositivity/InfinityCategories/F1B/Localization/Localization.lean:57`)。
- (c) 候補を起点に (b) の語で `Mathlib/Algebra/Algebra`, `Mathlib/Algebra/Algebra/Subalgebra`, `Mathlib/Algebra/BigOperators`, `Mathlib/Algebra/BigOperators/Finsupp`, `Mathlib/Algebra/BigOperators/Group/Finset`, `Mathlib/Algebra/BigOperators/Group/Multiset`, `Mathlib/Algebra/FiniteSupport`, `Mathlib/Algebra/Group`, `Mathlib/Algebra/Group/Pointwise/Set`, `Mathlib/Algebra/Group/Subgroup`, `Mathlib/Algebra/Group/Submonoid`, `Mathlib/Algebra/Group/Subsemigroup`, `Mathlib/Algebra/Lie`, `Mathlib/Algebra/Lie/Basis`, `Mathlib/Algebra/Module`, `Mathlib/Algebra/Polynomial`, `Mathlib/Algebra/Regular`, `Mathlib/Algebra/Ring`, `Mathlib/Algebra/Ring/Subring`, `Mathlib/Algebra/Ring/Subsemiring`, `Mathlib/Algebra/Star`, `Mathlib/AlgebraicTopology/SimplicialSet`, `Mathlib/Analysis/Analytic`, `Mathlib/Analysis/Calculus`, `Mathlib/Analysis/Calculus/TangentCone`, `Mathlib/Analysis/Convex`, `Mathlib/Analysis/InnerProductSpace`, `Mathlib/Analysis/Meromorphic`, `Mathlib/Basic`, `Mathlib/Basic/Finite`, `Mathlib/CategoryTheory`, `Mathlib/CategoryTheory/Bicategory`, `Mathlib/CategoryTheory/Discrete`, `Mathlib/CategoryTheory/Limits/Shapes`, `Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts`, `Mathlib/CategoryTheory/Localization`, `Mathlib/CategoryTheory/MorphismProperty`, `Mathlib/CategoryTheory/Products`, `Mathlib/Combinatorics`, `Mathlib/Combinatorics/Additive/AP/Three`, `Mathlib/Combinatorics/Enumerative`, `Mathlib/Computability/Primrec`, `Mathlib/Data`, `Mathlib/Data/Analysis`, `Mathlib/Data/DFinsupp`, `Mathlib/Data/Fin/Tuple`, `Mathlib/Data/Finset`, `Mathlib/Data/Ordmap`, `Mathlib/Data/PNat`, `Mathlib/Data/Set`, `Mathlib/Data/Set/Pairwise`, `Mathlib/Geometry/Convex`, `Mathlib/Geometry/Convex/Cone/Face`, `Mathlib/Geometry/Manifold`, `Mathlib/Geometry/Manifold/Algebra`, `Mathlib/Geometry/Manifold/IsManifold`, `Mathlib/Geometry/Manifold/MFDeriv`, `Mathlib/GroupTheory`, `Mathlib/GroupTheory/Congruence`, `Mathlib/GroupTheory/FreeGroup`, `Mathlib/GroupTheory/GroupAction`, `Mathlib/Lean`, `Mathlib/LinearAlgebra`, `Mathlib/LinearAlgebra/AffineSpace`, `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace`, `Mathlib/LinearAlgebra/Alternating`, `Mathlib/LinearAlgebra/Basis`, `Mathlib/LinearAlgebra/Multilinear`, `Mathlib/LinearAlgebra/QuadraticForm`, `Mathlib/LinearAlgebra/SModEq`, `Mathlib/LinearAlgebra/Span`, `Mathlib/Logic/Equiv`, `Mathlib/Logic/Function`, `Mathlib/MeasureTheory`, `Mathlib/MeasureTheory/Constructions/Polish`, `Mathlib/MeasureTheory/Function/LpSeminorm`, `Mathlib/MeasureTheory/MeasurableSpace`, `Mathlib/MeasureTheory/Measure`, `Mathlib/MeasureTheory/VectorMeasure`, `Mathlib/NumberTheory/ModularForms`, `Mathlib/Order`, `Mathlib/Order/Bounds`, `Mathlib/Order/Filter`, `Mathlib/Order/Filter/Bases`, `Mathlib/Order/Hom`, `Mathlib/Order/ScottContinuity`, `Mathlib/Order/Setoid`, `Mathlib/Order/UpperLower`, `Mathlib/Probability/Kernel/Composition`, `Mathlib/RepresentationTheory`, `Mathlib/RingTheory`, `Mathlib/RingTheory/Adjoin`, `Mathlib/RingTheory/DividedPowers`, `Mathlib/RingTheory/Finiteness`, `Mathlib/RingTheory/Ideal`, `Mathlib/RingTheory/Ideal/AssociatedPrime`, `Mathlib/RingTheory/IntegralClosure/Algebra`, `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure`, `Mathlib/RingTheory/MvPolynomial`, `Mathlib/RingTheory/NonUnitalSubring`, `Mathlib/RingTheory/NonUnitalSubsemiring`, `Mathlib/RingTheory/UniqueFactorizationDomain`, `Mathlib/SetTheory/Cardinal`, `Mathlib/SetTheory/ZFC`, `Mathlib/Topology`, `Mathlib/Topology/Algebra`, `Mathlib/Topology/Algebra/InfiniteSum`, `Mathlib/Topology/Algebra/Module/Alternating`, `Mathlib/Topology/Algebra/Module/ContinuousLinearMap`, `Mathlib/Topology/Algebra/Module/Multilinear`, `Mathlib/Topology/Bornology`, `Mathlib/Topology/Compactness`, `Mathlib/Topology/Connected`, `Mathlib/Topology/Constructions`, `Mathlib/Topology/FiberBundle`, `Mathlib/Topology/Homeomorph`, `Mathlib/Topology/Homotopy`, `Mathlib/Topology/Metrizable`, `Mathlib/Topology/OpenPartialHomeomorph`, `Mathlib/Topology/UniformSpace`, `Mathlib/Topology/UniformSpace/Ultra`, `Mathlib/Topology/VectorBundle`, `SerrePositivity/InfinityCategories/F1B/Localization`, `SerrePositivity/Spectra/Pointed` を検索。対象の宣言見出し 73054 件。

### [6.3.5.13](https://kerodon.net/tag/02M9) · `none → none`

逐次余極限の補題は特定の transport 初頂点射の IsLocalization を与える。一般の任意の引戻しに対する universally localizing 性の filtered colimit 閉性は確認できない。

- (a) `6.3.5.13` と `6.3.5`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `universally localizing filtered colimits arrow / localization sequential colimit / universal base change`。双対の語 `arrow base change filtered limit limits localization localizing sequential universal universally`。普通圏の語 `arrow base change colimit colimits filtered localization localizing sequential universal universally`。確認した候補 `transportSimplexFirstVertexMap_isLocalization_of_sequential_colimit` (`SerrePositivity/InfinityCategories/F1/Transport/LocalizationSequential.lean:41`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Transport`, `SerrePositivity/InfinityCategories/F1B/Localization` を検索。対象の宣言見出し 1063 件。

### [6.3.5.14](https://kerodon.net/tag/02MA) · `none → none`

候補は特定の transport 初頂点射の押出しで IsLocalization を返す。一般の三つの universally localizing 射を貼った後の全基底変更に対する結論は確認できない。

- (a) `6.3.5.14` と `6.3.5`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `universally localizing pushout monomorphism / localization glued pushout / base change transport localization`。双対の語 `base change glued localization localizing monomorphism pullback transport universally`。普通圏の語 `base change glued localization localizing monomorphism pushout transport universally`。確認した候補 `transportSimplexFirstVertexMap_isLocalization_of_isPushout` (`SerrePositivity/InfinityCategories/F1/Transport/LocalizationPushout.lean:20`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Transport`, `SerrePositivity/InfinityCategories/F1B/Localization` を検索。対象の宣言見出し 1063 件。

### [6.3.6.15](https://kerodon.net/tag/02MR) · `none → none`

単射による部分対象と同型への移送。一般の極限を扱うには任意積の nonsingular 性も必要で、その宣言は確認できない。

- (a) `6.3.6.15` と `6.3.6`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `nonsingular simplicial sets limit / nondegenerate simplex product / Nonsingular mono`。双対の語 `colimit coproduct epi nondegenerate nonsingular sets simplex simplicial`。普通圏の語 `limit mono nondegenerate nonsingular product sets simplex simplicial`。確認した候補 `Nonsingular.of_mono` (`Mathlib/AlgebraicTopology/SimplicialSet/Nonsingular.lean:58`), `Nonsingular.of_iso` (`Mathlib/AlgebraicTopology/SimplicialSet/Nonsingular.lean:67`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/AlgebraicTopology/SimplicialSet`, `SerrePositivity/InfinityCategories/F1/Transport`, `SerrePositivity/KST/Comparison` を検索。対象の宣言見出し 3563 件。

## 照合に使った kernel 型

段1・段1′と対象章の kernel evidence にある型。表示用に空白を整えた。

### 6.1.0.2

```lean
@CategoryTheory.Adjunction.{u_1, u_2, u_3, u_4} : {C : Type u_3} → [inst : CategoryTheory.Category.{u_1, u_3} C] → {D : Type u_4} → [inst_1 : CategoryTheory.Category.{u_2, u_4} D] → @CategoryTheory.Functor.{u_1, u_2, u_3, u_4} C inst D inst_1 → @CategoryTheory.Functor.{u_2, u_1, u_4, u_3} D inst_1 C inst → Type (max (max (max u_3 u_4) u_1) u_2)
@CategoryTheory.Adjunction.mkOfUnitCounit.{u_1, u_2, u_3, u_4} : {C : Type u_3} → [inst : CategoryTheory.Category.{u_1, u_3} C] → {D : Type u_4} → [inst_1 : CategoryTheory.Category.{u_2, u_4} D] → {F : @CategoryTheory.Functor.{u_1, u_2, u_3, u_4} C inst D inst_1} → {G : @CategoryTheory.Functor.{u_2, u_1, u_4, u_3} D inst_1 C inst} → @CategoryTheory.Adjunction.CoreUnitCounit.{u_1, u_2, u_3, u_4} C inst D inst_1 F G → @CategoryTheory.Adjunction.{u_1, u_2, u_3, u_4} C inst D inst_1 F G
```

### 6.1.2.8

```lean
@CategoryTheory.Bicategory.rightZigzag_idempotent_of_left_triangle.{u_1, u_2, u_3} : ∀ {B : Type u_3} [inst : CategoryTheory.Bicategory.{u_1, u_2, u_3} B] {a b : B} {f : Quiver.Hom.{u_2, u_3} a b} {g : Quiver.Hom.{u_2, u_3} b a} (η : Quiver.Hom.{u_1, u_2} (CategoryTheory.CategoryStruct.id.{u_2, u_3} a) (CategoryTheory.CategoryStruct.comp.{u_2, u_3} f g)) (ε : Quiver.Hom.{u_1, u_2} (CategoryTheory.CategoryStruct.comp.{u_2, u_3} g f) (CategoryTheory.CategoryStruct.id.{u_2, u_3} b)), Eq.{u_1 + 1} (CategoryTheory.Bicategory.leftZigzag.{u_1, u_2, u_3} η ε) (CategoryTheory.CategoryStruct.comp.{u_1, u_2} (CategoryTheory.Iso.hom.{u_1, u_2} (CategoryTheory.Bicategory.leftUnitor.{u_1, u_2, u_3} f)) (CategoryTheory.Iso.inv.{u_1, u_2} (CategoryTheory.Bicategory.rightUnitor.{u_1, u_2, u_3} f))) → Eq.{u_1 + 1} (CategoryTheory.bicategoricalComp.{u_1, u_2, u_3} (CategoryTheory.Bicategory.rightZigzag.{u_1, u_2, u_3} η ε) (CategoryTheory.Bicategory.rightZigzag.{u_1, u_2, u_3} η ε)) (CategoryTheory.Bicategory.rightZigzag.{u_1, u_2, u_3} η ε)
```

### 6.1.2.9

```lean
@SerrePositivity.InfinityCategories.bicategory_exists_adjunction_unit_iff.{u_1, u_2, u_3} : ∀ {B : Type u_1} [inst : CategoryTheory.Bicategory.{u_3, u_2, u_1} B] {b c : B} {l : Quiver.Hom.{u_2, u_1} b c} {r : Quiver.Hom.{u_2, u_1} c b} (η : Quiver.Hom.{u_3, u_2} (CategoryTheory.CategoryStruct.id.{u_2, u_1} b) (CategoryTheory.CategoryStruct.comp.{u_2, u_1} l r)), (∃ a, Eq.{u_3 + 1} (CategoryTheory.Bicategory.Adjunction.unit.{u_3, u_2, u_1} a) η) ↔ ∀ {a : B} (g : Quiver.Hom.{u_2, u_1} a b) (h : Quiver.Hom.{u_2, u_1} a c), Function.Bijective.{u_3 + 1, u_3 + 1} (SerrePositivity.InfinityCategories.bicategoryUnitHomMap.{u_1, u_2, u_3} η g h)
@SerrePositivity.InfinityCategories.bicategoryAdjunctionOfUnitHomBijective.{u_1, u_2, u_3} : {B : Type u_1} → [inst : CategoryTheory.Bicategory.{u_3, u_2, u_1} B] → {b c : B} → {l : Quiver.Hom.{u_2, u_1} b c} → {r : Quiver.Hom.{u_2, u_1} c b} → (η : Quiver.Hom.{u_3, u_2} (CategoryTheory.CategoryStruct.id.{u_2, u_1} b) (CategoryTheory.CategoryStruct.comp.{u_2, u_1} l r)) → (∀ {a : B} (g : Quiver.Hom.{u_2, u_1} a b) (h : Quiver.Hom.{u_2, u_1} a c), Function.Bijective.{u_3 + 1, u_3 + 1} (SerrePositivity.InfinityCategories.bicategoryUnitHomMap.{u_1, u_2, u_3} η g h)) → CategoryTheory.Bicategory.Adjunction.{u_3, u_2, u_1} l r
```

### 6.1.2.10

```lean
@SerrePositivity.InfinityCategories.bicategory_exists_adjunction_unit_iff.{u_1, u_2, u_3} : ∀ {B : Type u_1} [inst : CategoryTheory.Bicategory.{u_3, u_2, u_1} B] {b c : B} {l : Quiver.Hom.{u_2, u_1} b c} {r : Quiver.Hom.{u_2, u_1} c b} (η : Quiver.Hom.{u_3, u_2} (CategoryTheory.CategoryStruct.id.{u_2, u_1} b) (CategoryTheory.CategoryStruct.comp.{u_2, u_1} l r)), (∃ a, Eq.{u_3 + 1} (CategoryTheory.Bicategory.Adjunction.unit.{u_3, u_2, u_1} a) η) ↔ ∀ {a : B} (g : Quiver.Hom.{u_2, u_1} a b) (h : Quiver.Hom.{u_2, u_1} a c), Function.Bijective.{u_3 + 1, u_3 + 1} (SerrePositivity.InfinityCategories.bicategoryUnitHomMap.{u_1, u_2, u_3} η g h)
```

### 6.1.3.1

```lean
@CategoryTheory.Bicategory.Adjunction.homEquiv₂.{u_1, u_2, u_3} : {B : Type u_3} → [inst : CategoryTheory.Bicategory.{u_1, u_2, u_3} B] → {a b c : B} → {l : Quiver.Hom.{u_2, u_3} b c} → {r : Quiver.Hom.{u_2, u_3} c b} → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} l r → {g : Quiver.Hom.{u_2, u_3} a b} → {h : Quiver.Hom.{u_2, u_3} a c} → Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_2} (CategoryTheory.CategoryStruct.comp.{u_2, u_3} g l) h) (Quiver.Hom.{u_1, u_2} g (CategoryTheory.CategoryStruct.comp.{u_2, u_3} h r))
@CategoryTheory.Bicategory.Adjunction.homEquiv₁.{u_1, u_2, u_3} : {B : Type u_3} → [inst : CategoryTheory.Bicategory.{u_1, u_2, u_3} B] → {b c d : B} → {l : Quiver.Hom.{u_2, u_3} b c} → {r : Quiver.Hom.{u_2, u_3} c b} → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} l r → {g : Quiver.Hom.{u_2, u_3} b d} → {h : Quiver.Hom.{u_2, u_3} c d} → Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_2} g (CategoryTheory.CategoryStruct.comp.{u_2, u_3} l h)) (Quiver.Hom.{u_1, u_2} (CategoryTheory.CategoryStruct.comp.{u_2, u_3} r g) h)
```

### 6.1.3.2

```lean
@CategoryTheory.Bicategory.Adjunction.homEquiv₁.{u_1, u_2, u_3} : {B : Type u_3} → [inst : CategoryTheory.Bicategory.{u_1, u_2, u_3} B] → {b c d : B} → {l : Quiver.Hom.{u_2, u_3} b c} → {r : Quiver.Hom.{u_2, u_3} c b} → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} l r → {g : Quiver.Hom.{u_2, u_3} b d} → {h : Quiver.Hom.{u_2, u_3} c d} → Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_2} g (CategoryTheory.CategoryStruct.comp.{u_2, u_3} l h)) (Quiver.Hom.{u_1, u_2} (CategoryTheory.CategoryStruct.comp.{u_2, u_3} r g) h)
@CategoryTheory.Bicategory.Adjunction.homEquiv₂.{u_1, u_2, u_3} : {B : Type u_3} → [inst : CategoryTheory.Bicategory.{u_1, u_2, u_3} B] → {a b c : B} → {l : Quiver.Hom.{u_2, u_3} b c} → {r : Quiver.Hom.{u_2, u_3} c b} → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} l r → {g : Quiver.Hom.{u_2, u_3} a b} → {h : Quiver.Hom.{u_2, u_3} a c} → Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_2} (CategoryTheory.CategoryStruct.comp.{u_2, u_3} g l) h) (Quiver.Hom.{u_1, u_2} g (CategoryTheory.CategoryStruct.comp.{u_2, u_3} h r))
```

### 6.1.4.2

```lean
@CategoryTheory.Bicategory.Equivalence.mkOfAdjointifyCounit.{u_1, u_2, u_3} : {B : Type u_3} → [inst : CategoryTheory.Bicategory.{u_1, u_2, u_3} B] → {a b : B} → {f : Quiver.Hom.{u_2, u_3} a b} → {g : Quiver.Hom.{u_2, u_3} b a} → CategoryTheory.Iso.{u_1, u_2} (CategoryTheory.CategoryStruct.id.{u_2, u_3} a) (CategoryTheory.CategoryStruct.comp.{u_2, u_3} f g) → CategoryTheory.Iso.{u_1, u_2} (CategoryTheory.CategoryStruct.comp.{u_2, u_3} g f) (CategoryTheory.CategoryStruct.id.{u_2, u_3} b) → CategoryTheory.Bicategory.Equivalence.{u_1, u_2, u_3} a b
@CategoryTheory.Bicategory.Equivalence.adj.{u_1, u_2, u_3} : {B : Type u_3} → [inst : CategoryTheory.Bicategory.{u_1, u_2, u_3} B] → {a b : B} → (e : CategoryTheory.Bicategory.Equivalence.{u_1, u_2, u_3} a b) → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} (CategoryTheory.Bicategory.Equivalence.hom.{u_1, u_2, u_3} e) (CategoryTheory.Bicategory.Equivalence.inv.{u_1, u_2, u_3} e)
```

### 6.1.5.4

```lean
@CategoryTheory.Bicategory.Adjunction.comp.{u_1, u_2, u_3} : {B : Type u_3} → [inst : CategoryTheory.Bicategory.{u_1, u_2, u_3} B] → {a b c : B} → {f₁ : Quiver.Hom.{u_2, u_3} a b} → {g₁ : Quiver.Hom.{u_2, u_3} b a} → {f₂ : Quiver.Hom.{u_2, u_3} b c} → {g₂ : Quiver.Hom.{u_2, u_3} c b} → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} f₁ g₁ → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} f₂ g₂ → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} (CategoryTheory.CategoryStruct.comp.{u_2, u_3} f₁ f₂) (CategoryTheory.CategoryStruct.comp.{u_2, u_3} g₂ g₁)
```

### 6.1.5.5

```lean
@CategoryTheory.Bicategory.Adjunction.comp.{u_1, u_2, u_3} : {B : Type u_3} → [inst : CategoryTheory.Bicategory.{u_1, u_2, u_3} B] → {a b c : B} → {f₁ : Quiver.Hom.{u_2, u_3} a b} → {g₁ : Quiver.Hom.{u_2, u_3} b a} → {f₂ : Quiver.Hom.{u_2, u_3} b c} → {g₂ : Quiver.Hom.{u_2, u_3} c b} → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} f₁ g₁ → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} f₂ g₂ → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} (CategoryTheory.CategoryStruct.comp.{u_2, u_3} f₁ f₂) (CategoryTheory.CategoryStruct.comp.{u_2, u_3} g₂ g₁)
```

### 6.1.5.9

```lean
@CategoryTheory.Bicategory.Adjunction.comp.{u_1, u_2, u_3} : {B : Type u_3} → [inst : CategoryTheory.Bicategory.{u_1, u_2, u_3} B] → {a b c : B} → {f₁ : Quiver.Hom.{u_2, u_3} a b} → {g₁ : Quiver.Hom.{u_2, u_3} b a} → {f₂ : Quiver.Hom.{u_2, u_3} b c} → {g₂ : Quiver.Hom.{u_2, u_3} c b} → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} f₁ g₁ → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} f₂ g₂ → CategoryTheory.Bicategory.Adjunction.{u_1, u_2, u_3} (CategoryTheory.CategoryStruct.comp.{u_2, u_3} f₁ f₂) (CategoryTheory.CategoryStruct.comp.{u_2, u_3} g₂ g₁)
```

### 6.2.1.1

```lean
@SerrePositivity.InfinityCategories.QCatAdjunction.mkOfHomTriangles.{u_1} : {X Y : SSet.{u_1}} → [inst : SSet.Quasicategory.{u_1} X] → [inst_1 : SSet.Quasicategory.{u_1} Y] → {F : Quiver.Hom.{u_1, u_1 + 1} X Y} → {G : Quiver.Hom.{u_1, u_1 + 1} Y X} → (η : Quiver.Hom.{u_1, u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.qcatOf.{u_1} X)) (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.qcatMap.{u_1} F) (SerrePositivity.InfinityCategories.qcatMap.{u_1} G))) → (ε : Quiver.Hom.{u_1, u_1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.qcatMap.{u_1} G) (SerrePositivity.InfinityCategories.qcatMap.{u_1} F)) (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.qcatOf.{u_1} Y))) → Eq.{u_1 + 1} (CategoryTheory.Functor.map.{u_1, u_1, u_1, u_1} (SerrePositivity.InfinityCategories.qcatHomFunctor.{u_1} X Y) (CategoryTheory.Bicategory.leftZigzag.{u_1, u_1, u_1 + 1} η ε)) (CategoryTheory.Functor.map.{u_1, u_1, u_1, u_1} (SerrePositivity.InfinityCategories.qcatHomFunctor.{u_1} X Y) (CategoryTheory.CategoryStruct.comp.{u_1, u_1} (CategoryTheory.Iso.hom.{u_1, u_1} (CategoryTheory.Bicategory.leftUnitor.{u_1, u_1, u_1 + 1} (SerrePositivity.InfinityCategories.qcatMap.{u_1} F))) (CategoryTheory.Iso.inv.{u_1, u_1} (CategoryTheory.Bicategory.rightUnitor.{u_1, u_1, u_1 + 1} (SerrePositivity.InfinityCategories.qcatMap.{u_1} F))))) → Eq.{u_1 + 1} (CategoryTheory.Functor.map.{u_1, u_1, u_1, u_1} (SerrePositivity.InfinityCategories.qcatHomFunctor.{u_1} Y X) (CategoryTheory.Bicategory.rightZigzag.{u_1, u_1, u_1 + 1} η ε)) (CategoryTheory.Functor.map.{u_1, u_1, u_1, u_1} (SerrePositivity.InfinityCategories.qcatHomFunctor.{u_1} Y X) (CategoryTheory.CategoryStruct.comp.{u_1, u_1} (CategoryTheory.Iso.hom.{u_1, u_1} (CategoryTheory.Bicategory.rightUnitor.{u_1, u_1, u_1 + 1} (SerrePositivity.InfinityCategories.qcatMap.{u_1} G))) (CategoryTheory.Iso.inv.{u_1, u_1} (CategoryTheory.Bicategory.leftUnitor.{u_1, u_1, u_1 + 1} (SerrePositivity.InfinityCategories.qcatMap.{u_1} G))))) → SerrePositivity.InfinityCategories.QCatAdjunction.{u_1} F G
@SerrePositivity.InfinityCategories.QCatAdjunction.{u_1} : {X Y : SSet.{u_1}} → [SSet.Quasicategory.{u_1} X] → [SSet.Quasicategory.{u_1} Y] → Quiver.Hom.{u_1, u_1 + 1} X Y → Quiver.Hom.{u_1, u_1 + 1} Y X → Type u_1
@SerrePositivity.InfinityCategories.QCatAdjunction.left_triangle_hom.{u_1} : ∀ {X Y : SSet.{u_1}} [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SSet.Quasicategory.{u_1} Y] {F : Quiver.Hom.{u_1, u_1 + 1} X Y} {G : Quiver.Hom.{u_1, u_1 + 1} Y X} (a : SerrePositivity.InfinityCategories.QCatAdjunction.{u_1} F G), Eq.{u_1 + 1} (CategoryTheory.Functor.map.{u_1, u_1, u_1, u_1} (SerrePositivity.InfinityCategories.qcatHomFunctor.{u_1} X Y) (CategoryTheory.Bicategory.leftZigzag.{u_1, u_1, u_1 + 1} (CategoryTheory.Bicategory.Adjunction.unit.{u_1, u_1, u_1 + 1} a) (CategoryTheory.Bicategory.Adjunction.counit.{u_1, u_1, u_1 + 1} a))) (CategoryTheory.Functor.map.{u_1, u_1, u_1, u_1} (SerrePositivity.InfinityCategories.qcatHomFunctor.{u_1} X Y) (CategoryTheory.CategoryStruct.comp.{u_1, u_1} (CategoryTheory.Iso.hom.{u_1, u_1} (CategoryTheory.Bicategory.leftUnitor.{u_1, u_1, u_1 + 1} (SerrePositivity.InfinityCategories.qcatMap.{u_1} F))) (CategoryTheory.Iso.inv.{u_1, u_1} (CategoryTheory.Bicategory.rightUnitor.{u_1, u_1, u_1 + 1} (SerrePositivity.InfinityCategories.qcatMap.{u_1} F)))))
```

### 6.2.1.2

```lean
@SerrePositivity.InfinityCategories.QCatAdjunction.{u_1} : {X Y : SSet.{u_1}} → [SSet.Quasicategory.{u_1} X] → [SSet.Quasicategory.{u_1} Y] → Quiver.Hom.{u_1, u_1 + 1} X Y → Quiver.Hom.{u_1, u_1 + 1} Y X → Type u_1
@SerrePositivity.InfinityCategories.QCatAdjunction.unitHom.{u_1} : {X Y : SSet.{u_1}} → [inst : SSet.Quasicategory.{u_1} X] → [inst_1 : SSet.Quasicategory.{u_1} Y] → {F : Quiver.Hom.{u_1, u_1 + 1} X Y} → {G : Quiver.Hom.{u_1, u_1 + 1} Y X} → SerrePositivity.InfinityCategories.QCatAdjunction.{u_1} F G → Quiver.Hom.{u_1, u_1} (SSet.HomotopyCategory.mk.{u_1} (SerrePositivity.InfinityCategories.functorVertex.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} X))) (SSet.HomotopyCategory.mk.{u_1} (SerrePositivity.InfinityCategories.functorVertex.{u_1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} F G)))
```

### 6.2.1.4

```lean
@SerrePositivity.InfinityCategories.QCatAdjunction.{u_1} : {X Y : SSet.{u_1}} → [SSet.Quasicategory.{u_1} X] → [SSet.Quasicategory.{u_1} Y] → Quiver.Hom.{u_1, u_1 + 1} X Y → Quiver.Hom.{u_1, u_1 + 1} Y X → Type u_1
SerrePositivity.InfinityCategories.qcatHomFunctor.{u_1} : (X Y : SSet.{u_1}) → [inst : SSet.Quasicategory.{u_1} X] → [inst_1 : SSet.Quasicategory.{u_1} Y] → CategoryTheory.Functor.{u_1, u_1, u_1, u_1} (Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.qcatOf.{u_1} X) (SerrePositivity.InfinityCategories.qcatOf.{u_1} Y)) ↑(CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} (X ⟹ Y))
@SerrePositivity.InfinityCategories.qcatCellEquiv.{u_1} : {X Y : SSet.{u_1}} → [inst : SSet.Quasicategory.{u_1} X] → [inst_1 : SSet.Quasicategory.{u_1} Y] → (F G : Quiver.Hom.{u_1, u_1 + 1} X Y) → Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_1} (SerrePositivity.InfinityCategories.qcatMap.{u_1} F) (SerrePositivity.InfinityCategories.qcatMap.{u_1} G)) (Quiver.Hom.{u_1, u_1} (SSet.HomotopyCategory.mk.{u_1} (SerrePositivity.InfinityCategories.functorVertex.{u_1} F)) (SSet.HomotopyCategory.mk.{u_1} (SerrePositivity.InfinityCategories.functorVertex.{u_1} G)))
```

### 6.2.1.15

```lean
@SerrePositivity.InfinityCategories.QCatAdjunction.toHoAdjunction.{u_1} : {X Y : SSet.{u_1}} → [inst : SSet.Quasicategory.{u_1} X] → [inst_1 : SSet.Quasicategory.{u_1} Y] → {F : Quiver.Hom.{u_1, u_1 + 1} X Y} → {G : Quiver.Hom.{u_1, u_1 + 1} Y X} → SerrePositivity.InfinityCategories.QCatAdjunction.{u_1} F G → CategoryTheory.Adjunction.{u_1, u_1, u_1, u_1} (CategoryTheory.Cat.Hom.toFunctor.{u_1, u_1} (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} F)) (CategoryTheory.Cat.Hom.toFunctor.{u_1, u_1} (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} G))
@SerrePositivity.InfinityCategories.QCatAdjunction.hoHomEquiv.{u_1} : {X Y : SSet.{u_1}} → [inst : SSet.Quasicategory.{u_1} X] → [inst_1 : SSet.Quasicategory.{u_1} Y] → {F : Quiver.Hom.{u_1, u_1 + 1} X Y} → {G : Quiver.Hom.{u_1, u_1 + 1} Y X} → SerrePositivity.InfinityCategories.QCatAdjunction.{u_1} F G → (x : ↑(CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} X)) → (y : ↑(CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} Y)) → Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_1} (CategoryTheory.Functor.obj.{u_1, u_1, u_1, u_1} (CategoryTheory.Cat.Hom.toFunctor.{u_1, u_1} (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} F)) x) y) (Quiver.Hom.{u_1, u_1} x (CategoryTheory.Functor.obj.{u_1, u_1, u_1, u_1} (CategoryTheory.Cat.Hom.toFunctor.{u_1, u_1} (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.hoFunctor.{u_1} G)) y))
```

### 6.2.3.10

```lean
@SerrePositivity.InfinityCategories.HomotopyLimits.reflective_isLocal_iff_invertedEdges.{u_1} : ∀ {X : SSet.{u_1}} [inst : SSet.Quasicategory.{u_1} X] {P : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → Prop} (r : SerrePositivity.InfinityCategories.ReflectiveSubcategory.{u_1} X P) (z : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })), SerrePositivity.InfinityCategories.ReflectiveSubcategory.IsLocal.{u_1} r z ↔ SerrePositivity.InfinityCategories.HomotopyLimits.IsLocalObject.{u_1} (SerrePositivity.InfinityCategories.invertedEdges.{u_1} (SerrePositivity.InfinityCategories.ReflectiveSubcategory.reflector.{u_1} r)) z
@SerrePositivity.InfinityCategories.ReflectiveSubcategory.isLocal_iff_essentialImage.{u_1} : ∀ {X : SSet.{u_1}} [inst : SSet.Quasicategory.{u_1} X] {P : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → Prop} (r : SerrePositivity.InfinityCategories.ReflectiveSubcategory.{u_1} X P) (x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })), SerrePositivity.InfinityCategories.ReflectiveSubcategory.IsLocal.{u_1} r x ↔ ∃ y, Nonempty.{u_1 + 1} (SerrePositivity.InfinityCategories.VertexIso.{u_1} (↑y) x)
@SerrePositivity.InfinityCategories.HomotopyLimits.reflective_localEquivalences_eq.{u_1} : ∀ {X : SSet.{u_1}} [inst : SSet.Quasicategory.{u_1} X] {P : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → Prop} (r : SerrePositivity.InfinityCategories.ReflectiveSubcategory.{u_1} X P), Eq.{u_1 + 1} (SerrePositivity.InfinityCategories.HomotopyLimits.localEquivalences.{u_1} (SerrePositivity.InfinityCategories.invertedEdges.{u_1} (SerrePositivity.InfinityCategories.ReflectiveSubcategory.reflector.{u_1} r))) (SerrePositivity.InfinityCategories.invertedEdges.{u_1} (SerrePositivity.InfinityCategories.ReflectiveSubcategory.reflector.{u_1} r))
```

### 6.2.6.4

```lean
@CategoryTheory.Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top.{u_1, u_2, u_3, u_4} : ∀ {C : Type u_3} [inst : CategoryTheory.Category.{u_1, u_3} C] {D : Type u_4} [inst_1 : CategoryTheory.Category.{u_2, u_4} D] (F : CategoryTheory.Functor.{u_2, u_1, u_4, u_3} D C), CategoryTheory.Functor.IsRightAdjoint.{u_1, u_2, u_3, u_4} F ↔ Eq.{u_3 + 1} (CategoryTheory.Functor.leftAdjointObjIsDefined.{u_1, u_2, u_3, u_4} F) Top.top.{u_3}
```

### 6.3.0.1

```lean
@CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.{u_1, u_2, u_3, u_4, u_5, u_6} : {C : Type u_2} → {D : Type u_4} → [inst : CategoryTheory.Category.{u_1, u_2} C] → [inst_1 : CategoryTheory.Category.{u_3, u_4} D] → CategoryTheory.Functor.{u_1, u_3, u_2, u_4} C D → CategoryTheory.MorphismProperty.{u_1, u_2} C → (E : Type u_6) → [CategoryTheory.Category.{u_5, u_6} E] → Type (max (max (max (max (max u_2 u_4) u_6) u_1) u_3) u_5)
```

### 6.3.1.1

```lean
SerrePositivity.InfinityCategories.invertingFunctors.{u_1} : (X E : SSet.{u_1}) → Set.{u_1} (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 1 })) → SSet.Subcomplex.{u_1} (X ⟹ E)
SerrePositivity.InfinityCategories.invertingFunctors_quasicategory.{u_1} : ∀ (X E : SSet.{u_1}) [SSet.Quasicategory.{u_1} E] (W : Set.{u_1} (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 1 }))), SSet.Quasicategory.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SerrePositivity.InfinityCategories.invertingFunctors.{u_1} X E W))
```

### 6.3.1.23

```lean
@SerrePositivity.InfinityCategories.IsLocalization.of_subset_invertedEdges.{u_1} : ∀ {X D : SSet.{u_1}} {F : Quiver.Hom.{u_1, u_1 + 1} X D} {W W' : Set.{u_1} (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 1 }))}, SerrePositivity.InfinityCategories.IsLocalization.{u_1} F W → W ⊆ W' → W' ⊆ SerrePositivity.InfinityCategories.invertedEdges.{u_1} F → SerrePositivity.InfinityCategories.IsLocalization.{u_1} F W'
```

### 6.3.2.1

```lean
SerrePositivity.KST.LocalizingInvariants.exists_quasicategory_localization.{u_1} : ∀ (X : SSet.{u_1}) (W : Set.{u_1} (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 1 }))), ∃ Q F, SSet.Quasicategory.{u_1} Q ∧ SerrePositivity.InfinityCategories.IsLocalization.{u_1} F W
SerrePositivity.KST.LocalizingInvariants.inverseAttachment_isLocalization.{u_1} : ∀ (X : SSet.{u_1}) (W : Set.{u_1} (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 1 }))), SerrePositivity.InfinityCategories.IsLocalization.{u_1} (SerrePositivity.KST.LocalizingInvariants.inverseAttachmentInclusion.{u_1} X W) W
```

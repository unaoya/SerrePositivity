# Ch 10 交差の抜き取り検査（§8.4）

- 検査日 2026-11-10。対象は -c のやり直しを取り込んだ `0d9e86356` の表。作業枝に §8.4 を含む `e3c1c6c0e` を取り込んだ。
- 乱数の種 `0x0d9e8635`。Python の `random.Random` を一つ使い、第7章から第10章まで章順に処理。各章の番号を整数の組として昇順に並べ、完全対応、partial、none の順に `sample` で重複なく抽出した。上限は 20、10、10 件。
- 抽出後は番号と Kerodon 本文を作業用一覧に出し、-c の status・理由・引用欄を伏せた。原対応表の名前候補と、番号・小節の引用、概念名・双対・特例から探し、共有ロック下で採用候補の `#check` と `#print axioms` を実行した。
- 独立照合を確定した時点のメモの SHA-256 は `d2e01835e1491569e80e5a50f9b5cab4c1f2c5ca64c56ab12071bbaa7343dc5a`。その後、差のある各行で -c の宣言と理由を読み直した。
- partial は §8.1 の四分類で判定。比較後に表の status と異なる場合を「比較後の差」と数えた。

| 抽出群 | 母数 | 抽出 | 独立照合の差 | 比較後の差 | 比較後の差の割合 |
| --- | ---: | ---: | ---: | ---: | ---: |
| own・both・mathlib | 2 | 2 | 0 | 0 | 0.0% |
| partial | 49 | 10 | 0 | 0 | 0.0% |
| none | 93 | 10 | 5 | 5 | 50.0% |

完全対応群の比較後の差は §8.4 の停止基準以下。

## 独立照合で差があった行の比較

| Kerodon | -c | 独立 | 比較後 | partial_kind | 比較後に採る判定 | 根拠 |
| --- | --- | --- | --- | --- | --- | --- |
| [10.1.2.13](https://kerodon.net/tag/04RN) | none | partial | partial | component | 独立判定 | -c が述べるとおり、単射だけからなる増大部分圏の専用宣言は確認できない。ただし `WithInitial.map SemiSimplexCategory.toSimplexCategory` は、半単体圏への初期対象の付加と増大単体圏への比較関手を直接与える。初期対象を付加する構成が原文に明記された成分。左 cone の同定は残る。 |
| [10.2.1.1](https://kerodon.net/tag/04U0) | none | partial | partial | component | 独立判定 | 固定対象への射の族を取る通常圏の `Sieve` は対象が異なる。一方 `RightFibration` は任意の単体集合の射に適用でき、同じ部分単体集合の包含に適用した述語が原文の右ファイブレーション条件そのもの。sieve として束ねる宣言は確認できない。 |
| [10.2.1.8](https://kerodon.net/tag/04U7) | none | partial | partial | component | 独立判定 | `rightFibration_innerFibration` と `SSet.quasicategory_of_innerFibration` は原文と同じ包含に適用でき、内ファイブレーションの instance を介して「始域が準圏」を直接与える。-c が探した replete・充満部分圏としての結論はこれらの型にない。 |
| [10.2.3.23](https://kerodon.net/tag/04XS) | none | partial | partial | special | 独立判定 | -c の理由にある strong epi の定義とは別に、`regularOfIsPushoutFstOfRegular` は同じ形の押し出しの左辺の regular epi 性を右辺へ移す。通常圏で引き戻しがあれば、Kerodon 10.2.2.7 により quotient 性は kernel pair の余等化子条件と一致するため、この特例が直接対応する。像を持つ準圏一般への拡張は残る。 |
| [10.2.4.6](https://kerodon.net/tag/04Y1) | none | partial | partial | special | 独立判定 | 正則圏で全 regular epi の安定性を仮定する宣言とは別に、`universally_isStableUnderBaseChange (MorphismProperty.regularEpi C)` は通常圏で、全引き戻しが regular epi であるという同じ射の条件を引き戻し後にも与える。引き戻しを持つ通常圏では Kerodon 10.2.4.7 の普遍商射の判定と対応する。 |

## own・both・mathlib

| Kerodon | -c | 独立 | 独立 partial_kind | 比較後 | 比較後 partial_kind | 独立照合での仮定・結論 | 型を確認した宣言 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| [10.1.1.10](https://kerodon.net/tag/04R0) | mathlib | mathlib | — | mathlib | — | 有限非空順序集合と単調写像の SimplexCategory に初期対象 star を付加する。star は空順序集合で、そこから出る写像は一意、非空順序集合からそこへの写像はない。 | `AugmentedSimplexCategory`（`Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Basic.lean:33`）、`CategoryTheory.WithInitial.starInitial`（`Mathlib/CategoryTheory/WithTerminal/Basic.lean:636`） |
| [10.2.0.2](https://kerodon.net/tag/04TP) | mathlib | mathlib | — | mathlib | — | 通常圏の射 f と f 自身との引き戻し。kernel pair の余等化子から RegularEpi を作れ、逆に IsRegularEpi と同じ kernel pair からその余等化子の普遍性を取り出せる。 | `CategoryTheory.IsRegularEpi`（`Mathlib/CategoryTheory/Limits/Shapes/RegularMono.lean:345`）、`CategoryTheory.regularEpiOfKernelPair`（`Mathlib/CategoryTheory/Limits/Shapes/RegularMono.lean:451`）、`CategoryTheory.IsKernelPair.toCoequalizer'`（`Mathlib/CategoryTheory/Limits/Shapes/KernelPair.lean:167`） |

## partial

| Kerodon | -c | 独立 | 独立 partial_kind | 比較後 | 比較後 partial_kind | 独立照合での仮定・結論 | 型を確認した宣言 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| [10.1.1.3](https://kerodon.net/tag/04QT) | partial | partial | component | partial | component | 同じ Δᵒᵖ の nerve からの図式に対し HasSmallGeometricRealizations は余極限の存在を要求する。IsColimitCone はその余錐の条件。指定された X がその実現であるという専用の述語は確認できなかった。 | [`SerrePositivity.InfinityCategories.F2.Presentable.HasSmallGeometricRealizations`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/CoproductRealizationConditions.lean#L31)、[`SerrePositivity.InfinityCategories.IsColimitCone`](../../../../SerrePositivity/InfinityCategories/Core/Cocone.lean#L38) |
| [10.1.2.1](https://kerodon.net/tag/04R9) | partial | partial | component | partial | component | 原文の Δ_inj を、各 [n] と狭義単調写像で持つ。これを nerve または反対の nerve にして関手を取る (co)semisimplicial object 専用の定義は確認できなかった。 | `SemiSimplexCategory`（`Mathlib/AlgebraicTopology/SimplexCategory/SemiSimplexCategory.lean:31`）、`SemiSimplexCategory.homEquiv`（`Mathlib/AlgebraicTopology/SimplexCategory/SemiSimplexCategory.lean:54`） |
| [10.1.3.18](https://kerodon.net/tag/05GM) | partial | partial | component | partial | component | 通常圏では、n 切断から左 Kan 延長して n-skeletal な対象を指定できる。任意の u を入力にとり、さらに m≤n の u_m が同型である条件を束ねた述語は確認できなかった。 | `CategoryTheory.SimplicialObject.sk`（`Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean:297`）、`CategoryTheory.Functor.IsLeftKanExtension`（`Mathlib/CategoryTheory/Functor/KanExtension/Basic.lean:171`） |
| [10.1.3.23](https://kerodon.net/tag/05GS) | partial | partial | special | partial | special | 通常圏では指定の点ごとの左 Kan 延長などを仮定すると sk と余単位が取れ、充満忠実な包含に沿う随伴の単位が同型。よって余単位は n 切断上で同型。準圏で押し出しだけを仮定する版は確認できなかった。 | `CategoryTheory.SimplicialObject.sk`（`Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean:297`）、`CategoryTheory.SimplicialObject.skAdj`（`Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean:320`）、`CategoryTheory.SimplicialObject.Truncated.sk_coreflective`（`Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean:351`） |
| [10.1.4.8](https://kerodon.net/tag/04T3) | partial | partial | component | partial | component | 通常圏と有限積の仮定で、原文が右随伴の対象値として挙げる非増大 Čech nerve を返す。cechNerveAdjunction は増大対象の toArrow の随伴であり、この評価関手への随伴の宣言は確認できなかった。 | `CategoryTheory.cechNerveTerminalFrom`（`Mathlib/AlgebraicTopology/CechNerve.lean:327`） |
| [10.1.5.5](https://kerodon.net/tag/04T8) | partial | partial | special | partial | special | 通常圏の f に必要な有限 wide pullback があれば増大 Čech nerve を構成する。圏全体に有限 wide pullback があれば Arrow C 上の関手となる。 | `CategoryTheory.Arrow.augmentedCechNerve`（`Mathlib/AlgebraicTopology/CechNerve.lean:72`）、`CategoryTheory.SimplicialObject.augmentedCechNerve`（`Mathlib/AlgebraicTopology/CechNerve.lean:106`） |
| [10.1.6.3](https://kerodon.net/tag/04S9) | partial | partial | component | partial | component | 通常圏で 10.1.6.4 の h₋₁ と hₙ、および面関係と i>0 の退化関係をデータに持つ。i=0 の退化関係と Δ_min からの延長関手はこの構造体のフィールドにない。 | `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy`（`Mathlib/AlgebraicTopology/ExtraDegeneracy.lean:74`） |
| [10.1.6.11](https://kerodon.net/tag/04SK) | partial | partial | component | partial | component | 増大を持つ通常圏の対象に対して、その非増大部分の hₙ (n≥0) と面・退化関係の一部を持つ。非増大対象だけを入力に取る Δ_min に沿う延長は確認できなかった。 | `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy`（`Mathlib/AlgebraicTopology/ExtraDegeneracy.lean:74`） |
| [10.2.3.10](https://kerodon.net/tag/04XC) | partial | partial | special | partial | special | 通常圏では quotient の kernel pair 余等化子から EffectiveEpi、StrongEpi が従う。強エピの持ち上げは各 mono に対して存在し、一意性は mono の消去性。準圏での写像空間の直交性は確認できなかった。 | `CategoryTheory.effectiveEpi_of_kernelPair`（`Mathlib/CategoryTheory/Limits/Shapes/RegularMono.lean:483`）、`CategoryTheory.strongEpi_of_effectiveEpi`（`Mathlib/CategoryTheory/EffectiveEpi/Basic.lean:105`）、`CategoryTheory.StrongEpi.llp`（`Mathlib/CategoryTheory/Limits/Shapes/StrongEpi.lean:55`） |
| [10.2.3.11](https://kerodon.net/tag/04XD) | partial | partial | special | partial | special | 通常圏で任意のモノ分解に対する image の lift を使うと包含が得られる。逆に包含が与えるモノ間の射を像への分解射と合成して因子分解を得る。 | `CategoryTheory.Limits.IsImage`（`Mathlib/CategoryTheory/Limits/Shapes/Images.lean:193`）、`CategoryTheory.Subobject.mk_le_mk_of_comm`（`Mathlib/CategoryTheory/Subobject/Basic.lean:237`）、`CategoryTheory.Subobject.ofMkLEMk`（`Mathlib/CategoryTheory/Subobject/Basic.lean:339`）、`CategoryTheory.Subobject.ofMkLEMk_comp`（`Mathlib/CategoryTheory/Subobject/Basic.lean:349`） |

## none

| Kerodon | -c | 独立 | 独立 partial_kind | 比較後 | 比較後 partial_kind | 独立照合での仮定・結論 | 型を確認した宣言 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| [10.1.2.2](https://kerodon.net/tag/04RA) | none | none | — | none | — | SemiSimplexCategory の ⦋n⦌ₛ は添字側の対象だけを表す。(co)semisimplicial object を [n] で評価する原文の記法は、通常圏と準圏の評価、および双対の記法を検索しても見つからなかった。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [10.1.2.13](https://kerodon.net/tag/04RN) | none | partial | component | partial | component | WithInitial を Δ_inj に適用して [-1] を付加した圏と、その包含の WithInitial.map を取れる。増大単体圏の狭義単調写像との同定や、準圏としての左 cone との同定は確認できなかった。 | `CategoryTheory.WithInitial.starInitial`（`Mathlib/CategoryTheory/WithTerminal/Basic.lean:636`）、`CategoryTheory.WithInitial.map`（`Mathlib/CategoryTheory/WithTerminal/Basic.lean:533`）、`SemiSimplexCategory.toSimplexCategory`（`Mathlib/AlgebraicTopology/SimplexCategory/SemiSimplexCategory.lean:74`） |
| [10.1.5.1](https://kerodon.net/tag/04T4) | none | none | — | none | — | Over Y に値を持つ非増大 Čech nerve への条件として、任意の増大対象に適用できる述語を探索。Arrow.augmentedCechNerve は一つの射から標準対象を構成し、任意に与えた増大対象に対する原文の定義は置かない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [10.1.5.21](https://kerodon.net/tag/05HL) | none | none | — | none | — | 増大・半単体版、n=-1 と n=0、通常圏の matching object と face cube を検索。Mathlib の isCoskeletal_iff_isIso は非増大対象の同じ次数での Kan 随伴の単位との比較で、(n−1) から n への判定や指定の face cube は含まない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [10.1.6.15](https://kerodon.net/tag/04TL) | none | none | — | none | — | 通常圏と split epi の場合に Arrow.AugmentedCechNerve.extraDegeneracy を確認したが、結論は余退化のデータ。ExtraDegeneracy.homotopy は単体的ホモトピーを返す。いずれも元の増大余錐の IsColimit は型に含まない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [10.2.1.1](https://kerodon.net/tag/04U0) | none | partial | component | partial | component | 原文の sieve の包含が満たす lifting 条件を任意の単体集合の射について定義する。単体部分集合を束ねた sieve の宣言は確認できなかった。 | [`SerrePositivity.InfinityCategories.RightFibration`](../../../../SerrePositivity/InfinityCategories/Core/RightFibration.lean#L41) |
| [10.2.1.8](https://kerodon.net/tag/04U7) | none | partial | component | partial | component | 同じ包含の右ファイブレーション性から、準圏への内ファイブレーションとして始域が準圏だと直接出せる。充満・replete を得る宣言は確認できなかった。 | [`SerrePositivity.InfinityCategories.rightFibration_innerFibration`](../../../../SerrePositivity/InfinityCategories/Core/RightFibration.lean#L55)、`SSet.quasicategory_of_innerFibration`（`Mathlib/AlgebraicTopology/Quasicategory/InnerFibration.lean:94`） |
| [10.2.3.23](https://kerodon.net/tag/04XS) | none | partial | special | partial | special | 通常圏の押し出しで左辺が regular epi なら右辺が regular epi。引き戻しの存在する通常圏では kernel pair の余等化子という原文の quotient 条件に対応する。 | `CategoryTheory.regularOfIsPushoutFstOfRegular`（`Mathlib/CategoryTheory/Limits/Shapes/RegularMono.lean:591`） |
| [10.2.3.24](https://kerodon.net/tag/04XT) | none | none | — | none | — | 通常圏の regular/effective epi、および image を持つ準圏で retract 閉性を検索。llp_isStableUnderRetracts は射クラスの持ち上げ性についてで、quotient への対応をこの宣言は与えない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [10.2.4.6](https://kerodon.net/tag/04Y1) | none | partial | special | partial | special | 通常圏で P を regular epi とし、P.universally は任意の引き戻しが regular epi となる射クラス。この同じクラスを引き戻しが保存する。準圏の quotient は型に含まれない。 | `CategoryTheory.MorphismProperty.universally`（`Mathlib/CategoryTheory/MorphismProperty/Limits.lean:855`）、`CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange`（`Mathlib/CategoryTheory/MorphismProperty/Limits.lean:872`）、`CategoryTheory.MorphismProperty.regularEpi`（`Mathlib/CategoryTheory/Limits/Shapes/RegularMono.lean:350`） |

## 独立照合の kernel 出力

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.HasSmallGeometricRealizations</summary>

```lean
SerrePositivity.InfinityCategories.F2.Presentable.HasSmallGeometricRealizations.{u_1} : SSet.{u_1 + 1} → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.IsColimitCone</summary>

```lean
@SerrePositivity.InfinityCategories.IsColimitCone.{u_1} : {K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} → SerrePositivity.InfinityCategories.JoinCocone.{u_1} p → Prop
```

</details>

<details>
<summary>AugmentedSimplexCategory</summary>

```lean
AugmentedSimplexCategory : Type
```

</details>

<details>
<summary>CategoryTheory.WithInitial.starInitial</summary>

```lean
@CategoryTheory.WithInitial.starInitial.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    CategoryTheory.Limits.IsInitial.{u_1, u_2} CategoryTheory.WithInitial.star.{u_2}
```

</details>

<details>
<summary>SemiSimplexCategory</summary>

```lean
SemiSimplexCategory : Type
```

</details>

<details>
<summary>SemiSimplexCategory.homEquiv</summary>

```lean
@SemiSimplexCategory.homEquiv : {n m : SemiSimplexCategory} →
  Equiv.{1, 1} (Quiver.Hom.{0, 0} n m)
    (OrderEmbedding.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} n.len 1)) (Fin (HAdd.hAdd.{0, 0, 0} m.len 1)))
```

</details>

<details>
<summary>CategoryTheory.WithInitial.map</summary>

```lean
@CategoryTheory.WithInitial.map.{u_1, u_2, u_3,
    u_4} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    {D : Type u_4} →
      [inst_1 : CategoryTheory.Category.{u_3, u_4} D] →
        CategoryTheory.Functor.{u_1, u_3, u_2, u_4} C D →
          CategoryTheory.Functor.{u_1, u_3, u_2, u_4} (CategoryTheory.WithInitial.{u_2} C)
            (CategoryTheory.WithInitial.{u_4} D)
```

</details>

<details>
<summary>SemiSimplexCategory.toSimplexCategory</summary>

```lean
SemiSimplexCategory.toSimplexCategory : CategoryTheory.Functor.{0, 0, 0, 0} SemiSimplexCategory SimplexCategory
```

</details>

<details>
<summary>CategoryTheory.SimplicialObject.sk</summary>

```lean
@CategoryTheory.SimplicialObject.sk.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    (n : ℕ) →
      [∀ (F : CategoryTheory.Functor.{0, u_1, 0, u_2} (Opposite.{1} (SimplexCategory.Truncated n)) C),
            CategoryTheory.Functor.HasLeftKanExtension.{0, 0, u_1, u_2, 0, 0}
              (CategoryTheory.Functor.op.{0, 0, 0, 0} (SimplexCategory.Truncated.inclusion n)) F] →
        CategoryTheory.Functor.{u_1, u_1, max u_2 u_1, max u_2 u_1} (CategoryTheory.SimplicialObject.{u_1, u_2} C)
          (CategoryTheory.SimplicialObject.{u_1, u_2} C)
```

</details>

<details>
<summary>CategoryTheory.Functor.IsLeftKanExtension</summary>

```lean
@CategoryTheory.Functor.IsLeftKanExtension.{u_1, u_2, u_3, u_4, u_5,
    u_6} : {C : Type u_2} →
  {H : Type u_4} →
    {D : Type u_6} →
      [inst : CategoryTheory.Category.{u_1, u_2} C] →
        [inst_1 : CategoryTheory.Category.{u_3, u_4} H] →
          [inst_2 : CategoryTheory.Category.{u_5, u_6} D] →
            (F' : CategoryTheory.Functor.{u_5, u_3, u_6, u_4} D H) →
              {L : CategoryTheory.Functor.{u_1, u_5, u_2, u_6} C D} →
                {F : CategoryTheory.Functor.{u_1, u_3, u_2, u_4} C H} →
                  Quiver.Hom.{max u_2 u_3, max (max (max u_2 u_4) u_1) u_3} F
                      (CategoryTheory.Functor.comp.{u_1, u_5, u_3, u_2, u_6, u_4} L F') →
                    Prop
```

</details>

<details>
<summary>CategoryTheory.SimplicialObject.skAdj</summary>

```lean
@CategoryTheory.SimplicialObject.skAdj.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    (n : ℕ) →
      [inst_1 :
          ∀ (F : CategoryTheory.Functor.{0, u_1, 0, u_2} (Opposite.{1} (SimplexCategory.Truncated n)) C),
            CategoryTheory.Functor.HasLeftKanExtension.{0, 0, u_1, u_2, 0, 0}
              (CategoryTheory.Functor.op.{0, 0, 0, 0} (SimplexCategory.Truncated.inclusion n)) F] →
        CategoryTheory.Adjunction.{u_1, u_1, max u_2 u_1, max u_2 u_1}
          (CategoryTheory.SimplicialObject.Truncated.sk.{u_1, u_2} n)
          (CategoryTheory.SimplicialObject.truncation.{u_1, u_2} n)
```

</details>

<details>
<summary>CategoryTheory.SimplicialObject.Truncated.sk_coreflective</summary>

```lean
@CategoryTheory.SimplicialObject.Truncated.sk_coreflective.{u_1,
    u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] (n : ℕ)
  [inst_1 :
    ∀ (F : CategoryTheory.Functor.{0, u_1, 0, u_2} (Opposite.{1} (SimplexCategory.Truncated n)) C),
      CategoryTheory.Functor.HasLeftKanExtension.{0, 0, u_1, u_2, 0, 0}
        (CategoryTheory.Functor.op.{0, 0, 0, 0} (SimplexCategory.Truncated.inclusion n)) F]
  [∀ (F : CategoryTheory.Functor.{0, u_1, 0, u_2} (Opposite.{1} (SimplexCategory.Truncated n)) C),
      CategoryTheory.Functor.HasPointwiseLeftKanExtension.{0, 0, 0, 0, u_1, u_2}
        (CategoryTheory.Functor.op.{0, 0, 0, 0} (SimplexCategory.Truncated.inclusion n)) F],
  CategoryTheory.IsIso.{max u_2 u_1, max u_2 u_1}
    (CategoryTheory.Adjunction.unit.{u_1, u_1, max u_2 u_1, max u_2 u_1}
      (CategoryTheory.SimplicialObject.skAdj.{u_1, u_2} n))
```

</details>

<details>
<summary>CategoryTheory.cechNerveTerminalFrom</summary>

```lean
@CategoryTheory.cechNerveTerminalFrom.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    [CategoryTheory.Limits.HasFiniteProducts.{u_1, u_2} C] → C → CategoryTheory.SimplicialObject.{u_1, u_2} C
```

</details>

<details>
<summary>CategoryTheory.Arrow.augmentedCechNerve</summary>

```lean
@CategoryTheory.Arrow.augmentedCechNerve.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    (f : CategoryTheory.Arrow.{u_1, u_2} C) →
      [∀ (n : ℕ),
            CategoryTheory.Limits.HasWidePullback.{0, u_1, u_2} (CategoryTheory.Arrow.right.{u_1, u_2} f)
              (fun x => CategoryTheory.Arrow.left.{u_1, u_2} f) fun x => CategoryTheory.Arrow.hom.{u_1, u_2} f] →
        CategoryTheory.SimplicialObject.Augmented.{u_1, u_2} C
```

</details>

<details>
<summary>CategoryTheory.SimplicialObject.augmentedCechNerve</summary>

```lean
@CategoryTheory.SimplicialObject.augmentedCechNerve.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    [∀ (n : ℕ) (f : CategoryTheory.Arrow.{u_1, u_2} C),
          CategoryTheory.Limits.HasWidePullback.{0, u_1, u_2} (CategoryTheory.Arrow.right.{u_1, u_2} f)
            (fun x => CategoryTheory.Arrow.left.{u_1, u_2} f) fun x => CategoryTheory.Arrow.hom.{u_1, u_2} f] →
      CategoryTheory.Functor.{u_1, u_1, max u_2 u_1, max u_2 u_1} (CategoryTheory.Arrow.{u_1, u_2} C)
        (CategoryTheory.SimplicialObject.Augmented.{u_1, u_2} C)
```

</details>

<details>
<summary>CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy</summary>

```lean
@CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] → CategoryTheory.SimplicialObject.Augmented.{u_1, u_2} C → Type u_1
```

</details>

<details>
<summary>CategoryTheory.IsRegularEpi</summary>

```lean
@CategoryTheory.IsRegularEpi.{u_1,
    u_2} : {C : Type u_2} → [inst : CategoryTheory.Category.{u_1, u_2} C] → {X Y : C} → Quiver.Hom.{u_1, u_2} X Y → Prop
```

</details>

<details>
<summary>CategoryTheory.regularEpiOfKernelPair</summary>

```lean
@CategoryTheory.regularEpiOfKernelPair.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    {B X : C} →
      (f : Quiver.Hom.{u_1, u_2} X B) →
        [inst_1 : CategoryTheory.Limits.HasPullback.{u_1, u_2} f f] →
          CategoryTheory.Limits.IsColimit.{0, u_1, 0, u_2} (CategoryTheory.Limits.Cofork.ofπ.{u_1, u_2} f ⋯) →
            CategoryTheory.RegularEpi.{u_1, u_2} f
```

</details>

<details>
<summary>CategoryTheory.IsKernelPair.toCoequalizer'</summary>

```lean
@CategoryTheory.IsKernelPair.toCoequalizer'.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    {R X Y : C} →
      {f : Quiver.Hom.{u_1, u_2} X Y} →
        {a b : Quiver.Hom.{u_1, u_2} R X} →
          (k : CategoryTheory.IsKernelPair.{u_1, u_2} f a b) →
            [CategoryTheory.IsRegularEpi.{u_1, u_2} f] →
              CategoryTheory.Limits.IsColimit.{0, u_1, 0, u_2} (CategoryTheory.Limits.Cofork.ofπ.{u_1, u_2} f ⋯)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.RightFibration</summary>

```lean
@SerrePositivity.InfinityCategories.RightFibration.{u_1} : {X Y : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} X Y → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.rightFibration_innerFibration</summary>

```lean
@SerrePositivity.InfinityCategories.rightFibration_innerFibration.{u_1} : ∀ {X Y : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} X Y) [SerrePositivity.InfinityCategories.RightFibration.{u_1} p],
  SSet.InnerFibration.{u_1} p
```

</details>

<details>
<summary>SSet.quasicategory_of_innerFibration</summary>

```lean
@SSet.quasicategory_of_innerFibration.{u_1} : ∀ {X Y : SSet.{u_1}} (p : Quiver.Hom.{u_1, u_1 + 1} X Y)
  [SSet.InnerFibration.{u_1} p] [hY : SSet.Quasicategory.{u_1} Y], SSet.Quasicategory.{u_1} X
```

</details>

<details>
<summary>CategoryTheory.effectiveEpi_of_kernelPair</summary>

```lean
@CategoryTheory.effectiveEpi_of_kernelPair.{u_1,
    u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] {B X : C} (f : Quiver.Hom.{u_1, u_2} X B)
  [inst_1 : CategoryTheory.Limits.HasPullback.{u_1, u_2} f f]
  (hc : CategoryTheory.Limits.IsColimit.{0, u_1, 0, u_2} (CategoryTheory.Limits.Cofork.ofπ.{u_1, u_2} f ⋯)),
  CategoryTheory.EffectiveEpi.{u_1, u_2} f
```

</details>

<details>
<summary>CategoryTheory.strongEpi_of_effectiveEpi</summary>

```lean
@CategoryTheory.strongEpi_of_effectiveEpi.{u_1,
    u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] {X Y : C} (f : Quiver.Hom.{u_1, u_2} X Y)
  [CategoryTheory.EffectiveEpi.{u_1, u_2} f], CategoryTheory.StrongEpi.{u_1, u_2} f
```

</details>

<details>
<summary>CategoryTheory.StrongEpi.llp</summary>

```lean
@CategoryTheory.StrongEpi.llp.{u_1,
    u_2} : ∀ {C : Type u_2} {inst : CategoryTheory.Category.{u_1, u_2} C} {P Q : C} {f : Quiver.Hom.{u_1, u_2} P Q}
  [self : CategoryTheory.StrongEpi.{u_1, u_2} f] ⦃X Y : C⦄ (z : Quiver.Hom.{u_1, u_2} X Y)
  [CategoryTheory.Mono.{u_1, u_2} z], CategoryTheory.HasLiftingProperty.{u_1, u_2} f z
```

</details>

<details>
<summary>CategoryTheory.Limits.IsImage</summary>

```lean
@CategoryTheory.Limits.IsImage.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    {X Y : C} →
      {f : Quiver.Hom.{u_1, u_2} X Y} → CategoryTheory.Limits.MonoFactorisation.{u_1, u_2} f → Type (max u_2 u_1)
```

</details>

<details>
<summary>CategoryTheory.Subobject.mk_le_mk_of_comm</summary>

```lean
@CategoryTheory.Subobject.mk_le_mk_of_comm.{u_1,
    u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] {B A₁ A₂ : C}
  {f₁ : Quiver.Hom.{u_1, u_2} A₁ B} {f₂ : Quiver.Hom.{u_1, u_2} A₂ B} [inst_1 : CategoryTheory.Mono.{u_1, u_2} f₁]
  [inst_2 : CategoryTheory.Mono.{u_1, u_2} f₂] (g : Quiver.Hom.{u_1, u_2} A₁ A₂),
  Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_2} g f₂) f₁ →
    LE.le.{max u_2 u_1} (CategoryTheory.Subobject.mk.{u_1, u_2} f₁) (CategoryTheory.Subobject.mk.{u_1, u_2} f₂)
```

</details>

<details>
<summary>CategoryTheory.Subobject.ofMkLEMk</summary>

```lean
@CategoryTheory.Subobject.ofMkLEMk.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    {B A₁ A₂ : C} →
      (f : Quiver.Hom.{u_1, u_2} A₁ B) →
        (g : Quiver.Hom.{u_1, u_2} A₂ B) →
          [inst_1 : CategoryTheory.Mono.{u_1, u_2} f] →
            [inst_2 : CategoryTheory.Mono.{u_1, u_2} g] →
              LE.le.{max u_2 u_1} (CategoryTheory.Subobject.mk.{u_1, u_2} f)
                  (CategoryTheory.Subobject.mk.{u_1, u_2} g) →
                Quiver.Hom.{u_1, u_2} A₁ A₂
```

</details>

<details>
<summary>CategoryTheory.Subobject.ofMkLEMk_comp</summary>

```lean
@CategoryTheory.Subobject.ofMkLEMk_comp.{u_1,
    u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] {B A₁ A₂ : C} {f : Quiver.Hom.{u_1, u_2} A₁ B}
  {g : Quiver.Hom.{u_1, u_2} A₂ B} [inst_1 : CategoryTheory.Mono.{u_1, u_2} f]
  [inst_2 : CategoryTheory.Mono.{u_1, u_2} g]
  (h : LE.le.{max u_2 u_1} (CategoryTheory.Subobject.mk.{u_1, u_2} f) (CategoryTheory.Subobject.mk.{u_1, u_2} g)),
  Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_2} (CategoryTheory.Subobject.ofMkLEMk.{u_1, u_2} f g h) g) f
```

</details>

<details>
<summary>CategoryTheory.regularOfIsPushoutFstOfRegular</summary>

```lean
@CategoryTheory.regularOfIsPushoutFstOfRegular.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    {P Q R S : C} →
      {f : Quiver.Hom.{u_1, u_2} P Q} →
        {g : Quiver.Hom.{u_1, u_2} P R} →
          {h : Quiver.Hom.{u_1, u_2} Q S} →
            {k : Quiver.Hom.{u_1, u_2} R S} →
              CategoryTheory.RegularEpi.{u_1, u_2} f →
                (comm :
                    Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_2} f h)
                      (CategoryTheory.CategoryStruct.comp.{u_1, u_2} g k)) →
                  CategoryTheory.Limits.IsColimit.{0, u_1, 0, u_2}
                      (CategoryTheory.Limits.PushoutCocone.mk.{u_1, u_2} h k comm) →
                    CategoryTheory.RegularEpi.{u_1, u_2} k
```

</details>

<details>
<summary>CategoryTheory.MorphismProperty.universally</summary>

```lean
@CategoryTheory.MorphismProperty.universally.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    CategoryTheory.MorphismProperty.{u_1, u_2} C → CategoryTheory.MorphismProperty.{u_1, u_2} C
```

</details>

<details>
<summary>CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange</summary>

```lean
@CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange.{u_1,
    u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C]
  (P : CategoryTheory.MorphismProperty.{u_1, u_2} C),
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange.{u_1, u_2}
    (CategoryTheory.MorphismProperty.universally.{u_1, u_2} P)
```

</details>

<details>
<summary>CategoryTheory.MorphismProperty.regularEpi</summary>

```lean
CategoryTheory.MorphismProperty.regularEpi.{u_1,
  u_2} : (C : Type u_2) → [inst : CategoryTheory.Category.{u_1, u_2} C] → CategoryTheory.MorphismProperty.{u_1, u_2} C
```

</details>

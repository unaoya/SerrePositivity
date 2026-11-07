# Ch 10 交差の抜き取り検査（§7.3）

対象は `research/kerodon-review-c` の `cfd899d46d1d22b08b3f808f5d10b889ac3ab13c`。Ch 4〜6 のやり直しをコミットしてから、原文と型・ソースを別に照合した。元の判定の reason は照合に使わなかった。

乱数の種は `SerrePositivity-Kerodon-2026-11-07-b-7.3`。種、章番号、群（`positive` または `none`）、項目番号を NUL で区切った UTF-8 文字列の SHA-256 を計算し、群ごとに昇順の先頭20件を選んだ。20件未満の群は全件を検査した。

| 群 | 母集団 | 抽出 | 判定の差 | 率 |
| --- | ---: | ---: | ---: | ---: |
| own・both・mathlib | 2 | 2 | 0 | 0.0% |
| none | 93 | 20 | 2 | 10.0% |

1割を超えた群はない。

## 項目別の照合

- [10.1.1.10](https://kerodon.net/tag/04R0) `mathlib`。通常圏の対象は空の順序集合と各 [n]、射は単調写像。AugmentedSimplexCategory は SimplexCategory に空の始対象を付加し、非空同士の射を保つ。仮定・結論とも一致。 `Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Basic.lean:33`
- [10.2.0.2](https://kerodon.net/tag/04TP) `mathlib`。通常圏と f の核対の引き戻しが必要。regularEpiOfKernelPair は核対が余等化子なら RegularEpi を与える。逆は IsRegularEpi→EffectiveEpi→核対の余等化子の型を使える。 `Mathlib/CategoryTheory/Limits/Shapes/RegularMono.lean:451`
- [10.1.2.16](https://kerodon.net/tag/04RR) `none`。増強半単体対象を Xₙ、双対を Xⁿ と書く規約。SemiSimplexCategory と AugmentedSimplexCategory の定義を比較したが、増強された半単体とその双対のこの表記を宣言していない。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/AlgebraicTopology/SimplexCategory/SemiSimplexCategory.lean:31`
- [10.1.3.2](https://kerodon.net/tag/05G5) `none → partial`。定値図式と関手同型な f が全ての辺を可逆に写す補題は (1)⇒(2) に適用できる。逆向きと [0] からの左 Kan 拡張・Hom 比較の同値は別途必要。 番号の直接引用 0 件、同小節の近接引用 0 件。 `SerrePositivity/InfinityCategories/F1B/FunctorIsoConstantEdges.lean:41`
- [10.1.3.16](https://kerodon.net/tag/05GK) `none`。n-skeletal から一段下げる退化立方体の余極限判定。SSet の skeleton と Reedy の latching 対象はあるが、任意の ∞ 圏の単体対象の退化立方体とのこの比較は未確認。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/AlgebraicTopology/SimplicialSet/Skeleton.lean`
- [10.1.5.18](https://kerodon.net/tag/05HH) `none`。部分集合 P([k]) と増強された半単体圏の [k] 上の slice を同型とする構成。SemiSimplexCategory の Hom は順序埋め込みだが、空の埋め込みを含む slice 同型は未確認。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/AlgebraicTopology/SimplexCategory/SemiSimplexCategory.lean:45`
- [10.1.5.21](https://kerodon.net/tag/05HL) `none`。n-coskeletal な増強（半）単体対象の face cube が極限なら (n−1)-coskeletal となる双方向。通常の coskeleton の右随伴は段階判定と face cube の極限を結ばない。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/AlgebraicTopology/SimplicialObject/Coskeletal.lean`
- [10.1.6.1](https://kerodon.net/tag/04S7) `none`。零を保存する単調射だけを持つ Δ_min の定義。SimplexCategory の Hom にその制約はなく、WithInitial は空の対象を付加する別の構成。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean`
- [10.1.6.22](https://kerodon.net/tag/04SN) `none`。[0] を左に連結して得る増強 decalage とその制限。AugmentedSimplexCategory のモノイダル構造は連結を与えるが、Δ_min への因子化と nerve 上の二つの前合成を束ねた型は未確認。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Monoidal.lean`
- [10.2.1.6](https://kerodon.net/tag/04U5) `none`。部分複体 C′ が sieve であることと、充満かつ各辺について標的から始域への所属閉性の同値。Mathlib Sieve の対象は固定対象への射の族。fullSubcomplexOnVertices にその始域閉性はない。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/CategoryTheory/Sites/Sieves.lean`
- [10.2.1.8](https://kerodon.net/tag/04U7) `none`。∞ 圏の sieve が同値で閉じた充満部分圏になる。KST の DG replete 部分圏は DG の指定対象性質による構成で、任意の sieve からは作らない。 番号の直接引用 0 件、同小節の近接引用 0 件。 `SerrePositivity/InfinityCategories/Derived/DGRepleteYoneda.lean`
- [10.2.1.13](https://kerodon.net/tag/04UB) `none`。hC の sieve と C の sieve の nerve 上の引き戻しによる全単射。通常の Sieve.pullback は単一の対象への射に沿う制限であり、hC からのこの分類ではない。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/CategoryTheory/Sites/Sieves.lean`
- [10.2.2.11](https://kerodon.net/tag/04WT) `none`。∞ 圏同値が quotient morphism を保存・反映。通常圏の RegularEpi.ofArrowIso は同じ圏内の矢印同型による移送。原文の指定の sieve による quotient との比較は未確認。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/CategoryTheory/Limits/Shapes/RegularMono.lean:332`
- [10.2.2.14](https://kerodon.net/tag/04WW) `none`。slice 内の辺の像が quotient ならその辺も quotient。Over の pullback 随伴は異なる底の通常の slice 間の関手で、任意図式の ∞ slice の商射を反映しない。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/CategoryTheory/Comma/Over/Pullback.lean`
- [10.2.3.24](https://kerodon.net/tag/04XT) `none`。像のある ∞ 圏で quotient が arrow 圏の retract に閉じる。MorphismProperty の epi の retract 安定性は通常圏で、幾何実現による quotient を扱わない。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/CategoryTheory/MorphismProperty/Retract.lean:48`
- [10.2.4.1](https://kerodon.net/tag/04XW) `none`。単一の辺で生成した sieve の忘却関手が全 slice に左 Kan 延長される定義。Sieve.effectiveEpimorphic_singleton は通常圏の一つの余錐の余極限を比較する。universally と組み合わせても、生成 sieve の全 slice の左 Kan 拡張と同一視する型は未確認。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/CategoryTheory/Sites/EffectiveEpimorphic.lean:160`
- [10.2.4.6](https://kerodon.net/tag/04Y1) `none → partial`。通常圏の射の性質 P に対し、全ての引き戻しで P となる universally P は引き戻しに安定。P を EffectiveEpi とした通常圏版を得る。原文の ∞ 圏の密な生成 sieve との比較は未確認。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/CategoryTheory/MorphismProperty/Limits.lean:872`
- [10.2.4.10](https://kerodon.net/tag/04Y6) `none`。任意の底変換後も Čech nerve が幾何実現となることと普遍商射の同値。extraDegeneracy は通常圏の split epi の Čech nerve の追加退化で、任意の射の普遍余極限との比較を述べない。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/AlgebraicTopology/ExtraDegeneracy.lean:367`
- [10.2.4.14](https://kerodon.net/tag/04YA) `none`。普遍商射全体の arrow 圏での retract 安定性。universally_isStableUnderBaseChange の安定性は pullback で、retract についての結論ではない。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/CategoryTheory/MorphismProperty/Limits.lean:872`
- [10.2.5.6](https://kerodon.net/tag/04YN) `none`。空間の ∞ 圏の正則性。Mathlib の Regular は通常圏の有限極限・核対の余等化子・正則 epi の引き戻しを要求する。SpaceInfinity に対する原文の像と普遍商射の型は未確認。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/CategoryTheory/RegularCategory/Basic.lean:52`
- [10.2.5.17](https://kerodon.net/tag/04YY) `none`。有限極限と幾何実現を保つ F が quotient を保つ。regularEpiOfPreserves は通常圏で EffectiveEpi の保存を既に仮定するため、原文の仮定からその保存を導く型ではない。 番号の直接引用 0 件、同小節の近接引用 0 件。 `Mathlib/CategoryTheory/EffectiveEpi/Preserves.lean:119`
- [10.2.5.20](https://kerodon.net/tag/04Z1) `none`。正則 ∞ 圏の左完全な反射から反射先の正則性と F の正則性を得る主張。通常圏の Regular と Reflective、および反射的 ∞ 部分圏の構成には両結論を組み合わせた型がない。 番号の直接引用 0 件、同小節の近接引用 0 件。 `SerrePositivity/InfinityCategories/F1B/Localization/Reflective.lean:26`

## 追加の kernel 出力

`SerrePositivity/InfinityCategories/F1B/FunctorIsoConstantEdges.lean:41`

```lean
@SerrePositivity.InfinityCategories.functorIso_const_map_isInvertible.{u_1} : ∀ {K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {f : Quiver.Hom.{u_1, u_1 + 1} K X}
  (x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }))
  (e : SerrePositivity.InfinityCategories.FunctorIso.{u_1} f (SSet.const.{u_1} x))
  {a b : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} K (Opposite.op.{1} { len := 0 })}
  (d : SSet.Truncated.Edge.{u_1} a b),
  SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1}
    (SSet.Truncated.Edge.map.{u_1} d
      (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} (SSet.truncation.{u_1} 2) f))
```

`Mathlib/CategoryTheory/MorphismProperty/Limits.lean:855`

```lean
@CategoryTheory.MorphismProperty.universally.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    CategoryTheory.MorphismProperty.{u_1, u_2} C → CategoryTheory.MorphismProperty.{u_1, u_2} C
```

`Mathlib/CategoryTheory/MorphismProperty/Limits.lean:872`

```lean
@CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange.{u_1,
    u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C]
  (P : CategoryTheory.MorphismProperty.{u_1, u_2} C),
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange.{u_1, u_2}
    (CategoryTheory.MorphismProperty.universally.{u_1, u_2} P)
```

`Mathlib/CategoryTheory/Sites/EffectiveEpimorphic.lean:160`

```lean
@CategoryTheory.Sieve.effectiveEpimorphic_singleton.{u_1,
    u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] {X Y : C} (f : Quiver.Hom.{u_1, u_2} Y X),
  CategoryTheory.Presieve.EffectiveEpimorphic.{u_1, u_2} (CategoryTheory.Presieve.singleton.{u_1, u_2} f) ↔
    CategoryTheory.EffectiveEpi.{u_1, u_2} f
```

該当モジュールの既存キャッシュを使い、共有ロックの下で `#check` と `#print axioms` を実行した。追加候補で標準3公理以外は検出しなかった。

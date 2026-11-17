# BS-M15（⑤d）作業報告 — M10 の cone、外枠の停止、停止時の紙（§43〜§70、2026-11-14〜11-15）

元の報告：[report-codex-m15.md](../../bhatt-scholze/reports/report-codex-m15.md)

## 43. M10 の同じ通常単体と高次 cochain の接合（11-14）

§42 の途中報告後も元の目標を継続する。
同じ全要素列の先端に元の probe を前置し、後続頂点は元の通常加群 frame 対象とする。
元の末尾単調写像は ComplexLimits の既存 `coneTailOrderHom` を再利用し、
その後の同じ通常図式を `closedNerveSimplex` で元の全通常 dg 加群の dg nerve へ送る。

この同じ通常単体と、§41 の選択した高次 cochain を接合した `SimplexData` を作った。
先端を含む成分には同じ次数の `k.negOnePow` と同じ最大元への型移送を適用する。
先端を含まない成分は元の通常単体の同じ成分とする。
`withoutFirst`・濃度・最大元の各有限集合補題は既存 ComplexLimits のものを再利用し、
それらのファイルは変更していない。

ここで得たものは元の全 cone の**データ**であり、HA の全方程式を持つ `Simplex` や
全 cone/prism とはまだ主張しない。方程式を引数の仮定に加えていない。
本節も M10 の同じ比較の係数移送・通常成分との貼り合わせと証明の分割で、一次 ID は追加しない。
全宣言の型は以下のとおり。

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeObj {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    Fin (n + 2) → RightModule A (dgAlgebraCategory A ((assocForget A).obj X))

lemma strictRawModuleTensorConeObj_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorConeObj A X P Q c 0 =
      ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)

lemma strictRawModuleTensorConeObj_succ {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 1)) :
    strictRawModuleTensorConeObj A X P Q c i.succ =
      ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i))

lemma strictRawModuleTensorConeObj_ne_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    strictRawModuleTensorConeObj A X P Q c i =
      ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (coneTailOrderHom n i)))

def strictRawModuleTensorConeOrdinarySimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 1)

lemma strictRawModuleTensorConeOrdinarySimplex_obj {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 2)) :
    (strictRawModuleTensorConeOrdinarySimplex A X P Q c).obj i =
      ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (coneTailOrderHom n i)))

def strictRawModuleTensorConeData {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    SimplexData A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 1)
```

対象ビルドと小さい監査の結果は §43.1 に記録した。
元の全 HA 方程式・全作用素での自然性、元の全屋根と同じ K の Hom 射への照合は引き続き必要。
M10 の完全忠実性・指定 fiber・一般の native な辺と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 43.1 検証と実測

RawModuleTensorConeData の通常の対象ビルドは成功した。
新しい公開宣言 7 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は一ファイル 119 行、公開宣言 7 本。
§41.1 の累計に加え、検証済み累計は 84 ファイル・8,619 行・明示宣言 452 本
（private 4 本）。200 行を超える証明はない。一次 ID は追加していない。
§42 の 8,500 行の途中報告後も実装を継続した。

同じ全通常成分と符号つき高次 cochain の接合データ・元の端点の型の移送を検証した。
次は元の混合/通常成分の式、単射制限、全 HA 方程式と全作用素自然性を検証する。
完全な cone/prism、同じ屋根と K の実 Hom 射の照合、その同値性・完全忠実性、
指定 fiber・一般の native な辺と全族はまだ未完。
M11 以降と G12 の元の目標、17,000 行の外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 44. M10 の同じ cone の通常成分と全二点の HA 方程式（11-14）

§43 の同じ生データの通常成分・混合成分を、元の通常単体と符号つき選択 cochain へ戻す
異種等号を保持する。始点を除く面の全成分を同じ通常単体へ照合し、既存の一般の
`SimplexData.equation_image_of_pullback` によって、始点を含まない**任意の有限部分集合**の
全 HA 方程式を元のデータへ戻す。

一点を選ぶ元の最上位 cochain は、同じ線形単体の微分方程式から閉零元である。
元の最大元への型の移送は同じ微分と整合する。その閉性を元の混合辺へ移し、
通常の辺は元の面で検証することで、同じ cone データの**全ての二点集合**の HA 方程式を得る。
次数が零になることは元の濃度二の条件から導く。

これは M10 の同じ構成の成分式・通常成分との貼り合わせ・係数移送と証明の分割である。
一次 ID は追加しない。先端を含む三点以上の集合の方程式、全 cone/prism の全作用素自然性、
元の屋根と K の Hom 射の全高次比較はまだ未完。
全宣言の型は以下のとおり。

`RawModuleTensorConeComponents`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_ordinary {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeOrdinarySimplex A X P Q c).toSimplexData.hom I a b k hI ha hb hk)

lemma strictRawModuleTensorConeData_hom_mixed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk)
      (k.negOnePow • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c (withoutFirst I) k
        (withoutFirst_nonempty hI h0) (by have := card_withoutFirst I h0; omega))
```

`RawModuleTensorConeTail`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_tail {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorConeData A X P Q c).pullback (Fin.succOrderEmb (n + 1)).toOrderHom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      (c ⋙ strictRawModuleTensorElementDiagram A X P Q)).toSimplexData
```

`RawModuleTensorConeTailEquation`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_equation_without_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (h0 : (0 : Fin (n + 2)) ∉ I) :
    (strictRawModuleTensorConeData A X P Q c).Equation I
```

`RawModuleTensorSelectedClosed`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochain_closed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    differential A (strictRawModuleTensorElementSelectedCochain A X P Q c J 0 hJ (by omega)) = 0

lemma strictRawModuleTensorElementSelectedCochainAtMax_closed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    differential A (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J 0 hJ (by omega)) =
      0
```

`RawModuleTensorConePairEquation`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_equation_pair {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (hc : I.card = 2) :
    (strictRawModuleTensorConeData A X P Q c).Equation I
```

対象ビルドと小さい監査の確定結果・実測は §44.1 に記録した。
M10 の完全忠実性・指定 fiber・一般の native な辺と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 44.1 検証と実測

RawModuleTensorConeComponents・RawModuleTensorConeTail・RawModuleTensorConeTailEquation・
RawModuleTensorSelectedClosed・RawModuleTensorConePairEquation の通常の対象ビルドは成功した。
新しい公開宣言 7 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は五ファイル、それぞれ 45・51・35・55・55 行、計 241 行、公開宣言 7 本。
§43.1 の累計に加え、検証済み累計は 89 ファイル・8,860 行・明示宣言 459 本
（private 4 本）。200 行を超える証明はない。一次 ID は追加していない。

元の接合データの両成分の式、始点を除く面の全成分一致、始点を含まない任意集合の方程式、
一点選択 cochain の閉性と元の型移送、全二点集合の方程式まで検証した。
残る正次混合成分・全 cone/prism・同じ屋根と K の Hom 射への照合、完全忠実性、
指定 fiber・一般の native な辺と全族、M11 以降と G12 の元の目標は未完。

**一覧：済み 10／全体 43（うち追加 1）**。


## 45. M10 の選択 cochain の像と同じ全 cone データの単射制限（11-14）

§44 の通常成分と二点の方程式に続き、任意終端への制限で元の方程式を戻すため、
同じ全 cone データと始点つき単射 pullback の一致を検証する。

まず、元の選択 cochain を濃度の等式と明示次数で表し直し、元の表示に厳密に戻す。
既存の有限集合の列挙 `normalizedTensorElementSelectionOfCard` と、その終端・像の法則を
再利用する。同じ列の最上位 cochain であることから、順序埋め込みの像を選んだ成分と
制限列の元の成分を異種等号で照合し、元の次数符号の作用も保持する。
frame 射の後合成の単射性を仮定して逆推論するものではない。

同じ cone の全対象は、始点つき単射の制限と厳密に一致する。
通常零次成分を元の frame 射の閉零元へ戻し、高次の通常成分は元の閉 nerve の消滅式で零とする。
混合成分は同じ選択 cochain の像の式を使い、通常零次成分は同じ元の辺を、
高次通常成分は同じ零成分を比較する。これらの全成分を従属関数の外延性でまとめ、
全 `SimplexData` の単射 pullback と元の制限列のデータの一致を得る。

本節は M10 の同じ構成の係数移送・再添字・成分の貼り合わせと証明の分割であり、
一次 ID は追加しない。全作用素のうち非単射の全 cone データの整合性と、
始点を含む三点以上の集合の HA 方程式は引き続き別に検証する。
全宣言の型は以下のとおり。

`RawModuleTensorSelectedCard`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementSelectedCochainAtMaxOfCard {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℕ) (hc : J.card = r + 1) :
    GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (J.max' hJ)))) k

lemma strictRawModuleTensorElementSelectedCochainAtMax_eq_ofCard {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk =
      strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c J k hJ hk (J.card - 1)
        (by have := Finset.card_pos.mpr hJ; omega)

lemma strictRawModuleTensorElementSelectedCochainAtMaxOfCard_congr {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r s : ℕ) (hrs : r = s) (hr : J.card = r + 1) (hs : J.card = s + 1) :
    strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c J k hJ hk r hr =
      strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c J k hJ hk s hs

lemma strictRawModuleTensorElementSelectedCochainAtMaxOfCard_raw {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℕ) (hc : J.card = r + 1) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c J k hJ hk r hc)
      ((strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map
          (normalizedTensorElementSelectionOfCard J r hc)).toFunctor ⋙ c)).val.component
            Finset.univ k Finset.univ_nonempty
            (by simpa only [Finset.card_univ, Fintype.card_fin, ← hc] using hk))
```

`RawModuleTensorSelectedCardImage`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMaxOfCard_image {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℕ) (hc : J.card = r + 1) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c (J.image e) k (hJ.image e)
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hk) r
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hc))
      (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
        J k hJ hk r hc)
```

`RawModuleTensorSelectedImageReindex`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_image_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c (J.image e) k (hJ.image e)
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hk))
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
        J k hJ hk)

lemma strictRawModuleTensorElementSelectedCochainAtMax_image_reindex_smul {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (r : ℤˣ) :
    HEq (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c (J.image e) k (hJ.image e)
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hk))
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
        J k hJ hk)
```

`RawModuleTensorConePrependObjects`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_obj_prepend {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (i : Fin (m + 2)) :
    (strictRawModuleTensorConeData A X P Q c).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom i) =
      (strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map
          (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).obj i
```

`RawModuleTensorConeOrdinaryClosed`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_ordinary_closed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) (hab : a ≤ b) :
    HEq ((strictRawModuleTensorConeData A X P Q c).hom I a b 0 hI ha hb hk)
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementDiagram A X P Q).map
          (c.map (homOfLE ((coneTailOrderHom n).monotone hab))))).val
```

`RawModuleTensorConeOrdinaryZero`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_ordinary_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) (hc : I.card ≠ 2) :
    (strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk = 0
```

`RawModuleTensorConeOrdinaryPullbackZero`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_ordinary_zero {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1))
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom)).hom I a b 0 hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).hom
          I a b 0 hI ha hb hk)
```

`RawModuleTensorConeMixedPullback`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_mixed {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1))
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).hom
          I a b k hI ha hb hk)
```

`RawModuleTensorConeOrdinaryPullback`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_ordinary {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1))
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).hom
          I a b k hI ha hb hk)
```

`RawModuleTensorConeInjectivePullback`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_injective {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) :
    (strictRawModuleTensorConeData A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) =
      strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)
```

対象ビルド・小さい監査の結果と実測は §45.1 に記録した。
M10 の元の屋根と同じ K の実 Hom 射への全高次照合、同値性・完全忠実性、指定 fiber、
一般の native な辺と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 45.1 検証と実測

RawModuleTensorSelectedCard・RawModuleTensorSelectedCardImage・RawModuleTensorSelectedImageReindex・
RawModuleTensorConePrependObjects・RawModuleTensorConeOrdinaryClosed・RawModuleTensorConeOrdinaryZero・
RawModuleTensorConeOrdinaryPullbackZero・RawModuleTensorConeMixedPullback・
RawModuleTensorConeOrdinaryPullback・RawModuleTensorConeInjectivePullback の通常の対象ビルドは成功した。
新しい公開宣言 14 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は十ファイル、それぞれ 66・61・69・35・35・46・69・77・64・60 行、
計 582 行、公開宣言 14 本。§44.1 の累計に加え、検証済み累計は
99 ファイル・9,442 行・明示宣言 473 本（private 4 本）。
200 行を超える証明はない。一次 ID は追加していない。

同じ選択 cochain の濃度による表示・元の表示との厳密一致・像の選択との異種等号・
元の次数符号の作用、全 cone データの対象と混合/通常成分の単射制限、
全データの単射 pullback 一致を検証した。
元の通常辺を閉零射へ戻す段でも、同じ加群射を保持している。
frame 射の作用の単射性は使っていない。

次は先端と終端を含む三点以上の集合の微分・全削除和・最後の切断合成を、
同じ全普遍線形 cochain の方程式へ照合する。一般の dg 閉後合成の全次数式
`dgClosedPostcomposition_f` は既存の `eHomWhiskerLeft` の成分式そのものであり、
複体専用の `homPostcompose` の再構成は不要と確認した。
その後、単射制限によって任意の終端の集合へ戻し、非単射作用素との全整合性を検証する。

全 HA 方程式・全 cone/prism・同じ屋根と K の実 Hom 射への照合、その同値性・完全忠実性、
指定 fiber・一般の native な辺と全族はまだ未完。
M11 以降と G12 の元の目標、17,000 行の外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 46. M10 の全 HA 方程式と元の実 cone 単体（11-14）

§45 の同じ接合データについて、先端と終端を含む任意の有限部分集合の HA 方程式を閉じる。
まず同じ選択 cochain を元の末尾射で送った像を回収し、終端まで届く選択は
同じ元の普遍 cochain の成分そのものであることを、同じ次数符号の作用まで照合する。
これにより混合成分とその微分を元の線形成分・同じ微分方程式の右辺へ戻す。

同じ通常側の切断集合が二点でないときは、元の通常高次成分が零なので切断合成は零になる。
元の全非線形和の支持を最後から二番目の内部点に絞り、最後の実切断合成を計算する。
閉零射の実合成は既存の一般 dg 閉後合成の全次数式 `dgClosedPostcomposition_f` により
同じ `eHomWhiskerLeft` の成分へ戻す。元の Hom end の後合成と符号作用を保ち、
同じ最後の削除成分を回収する。

全内部削除和へこの最後の切断成分を足すと、元の全普遍線形 cochain の右辺になる。
符号つき同じ微分の式と照合して、終端を含む全ての集合の方程式を得る。
任意終端の集合は、元の昇順選択列と §45 の同じ単射 pullback を使って戻す。
ここで一般の dg 単体データについて、指定集合の方程式だけを同じ単射に沿って移す証明を
私有補題に分割した。方程式を仮定した外部の Setup や追加公理は導入しない。

結果として元の `strictRawModuleTensorConeData` は**全有限部分集合・全次数の HA 方程式**を持つ。
同じデータとその方程式から `Simplex` を作り、元のデータとの厳密な一致、
全単射制限の一致、始点を除く面と元の全通常単体の一致を保持する。
非単射を含む全作用素への自然性と大域 cone/prism の束ねは次に検証する。

本節も M10 の同じ構成の微分・合成・符号・係数移送・成分の貼り合わせと証明の分割で、
一次 ID は追加しない。全宣言の型は以下のとおり。

`ClosedPostcomposition.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma modulePostcompose_graded (M : ModuleCategory A D) {P Q : ModuleCategory A D}
    (f : P ⟶ Q) (k : ℤ)
    (v : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) k) :
    compose A (closedHomEquiv A (RightModule A D) _ _ f).val v (add_zero k) =
      (eHomWhiskerLeft (Complex A) M f).f k v
```

`RawModuleTensorSelectedAtMaxImage.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_image {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementDiagram A X P Q).map
      (c.map (homOfLE (Fin.le_last (J.max' hJ)))))).f k
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) =
    (strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk
```

`RawModuleTensorSelectedTerminal.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_terminal {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hm : J.max' hJ = Fin.last n) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk)
      ((strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk)

lemma strictRawModuleTensorElementSelectedCochainAtMax_terminal_smul {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hm : J.max' hJ = Fin.last n) (r : ℤˣ) :
    HEq (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk)
      (r • (strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk)
```

`RawModuleTensorConeMixedLast.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk)
      (k.negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        (withoutFirst I) k (withoutFirst_nonempty hI h0)
        (by have := card_withoutFirst I h0; omega))

lemma strictRawModuleTensorConeData_d_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq (differential A ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk))
      (k.negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.rhs
        (withoutFirst I) k (by have := card_withoutFirst I h0; omega))
```

`RawModuleTensorConeErasedLast.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_erased_succ_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1))
    (h0 : 0 ∈ I) (j : Fin (n + 1)) (hj : j.succ ∈ I) (hjb : j.succ < b)
    (hJ : ((withoutFirst I).erase j).Nonempty)
    (hkJ : k + 1 = 1 - (((withoutFirst I).erase j).card : ℤ)) :
    HEq ((strictRawModuleTensorConeData A X P Q c).homOrZero (I.erase j.succ) a b (k + 1))
      ((k + 1).negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        ((withoutFirst I).erase j) (k + 1) hJ hkJ)
```

`RawModuleTensorConeLinearBoundary.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_linearBoundary_reindex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ)
    (ha0 : a = 0) (hbl : b = Fin.last (n + 1)) :
    (strictRawModuleTensorConeData A X P Q c).linearBoundary I a b k =
      ∑ j : withoutFirst I, if j.val < Fin.last n then
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (withoutFirst I) j.val •
          (strictRawModuleTensorConeData A X P Q c).homOrZero (I.erase j.val.succ) a b (k + 1)
        else 0

lemma strictRawModuleTensorConeData_linearBoundary_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (hbl : b = Fin.last (n + 1))
    (h0 : 0 ∈ I) (hJ : 2 ≤ (withoutFirst I).card)
    (hkJ : k = 1 - ((withoutFirst I).card : ℤ)) :
    HEq ((strictRawModuleTensorConeData A X P Q c).linearBoundary I a b k)
      (∑ j : withoutFirst I, if j.val < Fin.last n then
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (withoutFirst I) j.val • ((k + 1).negOnePow •
          (strictRawModuleTensorElementLinear A X P Q c).val.component
            ((withoutFirst I).erase j.val) (k + 1)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ _ j.property)
            (by have := Finset.card_erase_add_one j.property; omega)) else 0)
```

`RawModuleTensorSelectedComposition.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_compose {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℤˣ) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (J.max' hJ)))))).val
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) (add_zero k) =
    r • (strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk
```

`RawModuleTensorConeTerminalComposition.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_terminal_compose_mixed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (L R : Finset (Fin (n + 2))) (a j b : Fin (n + 2)) (k : ℤ)
    (hL : 2 ≤ L.card) (ha : a = L.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL))
    (hj : j = L.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL)) (hk : k = 2 - (L.card : ℤ))
    (ha0 : a = 0) (h0 : 0 ∈ L) (hR : 2 ≤ R.card)
    (hjR : j = R.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR)) (hb : b = R.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR))
    (hkR : (0 : ℤ) = 2 - (R.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    HEq (compose A ((strictRawModuleTensorConeData A X P Q c).hom R j b 0 hR hjR hb hkR)
      ((strictRawModuleTensorConeData A X P Q c).hom L a j k hL ha hj hk) (add_zero k))
      (k.negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        (withoutFirst L) k (withoutFirst_nonempty hL h0)
        (by have := card_withoutFirst L h0; omega))
```

`RawModuleTensorConePenultimateValue.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_cutCompose_penultimate_value {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) (ha0 : a = 0)
    (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq ((strictRawModuleTensorConeData A X P Q c).cutCompose I a b k (penultimate I hI))
      ((k + 1).negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        (withoutFirst (I.filter (· ≤ penultimate I hI))) (k + 1)
        (withoutFirst_nonempty
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two (a := a) (by rw [ha]; exact I.min'_mem _) (penultimate_mem I hI)
            (by rw [ha]; exact min_lt_penultimate I hI hc))
          (Finset.mem_filter.mpr ⟨h0, Fin.zero_le _⟩))
        (by have hsplit := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card (penultimate_mem I hI)
            have hr := (right_card_two_iff_penultimate I hI _ (penultimate_mem I hI)
              (penultimate_lt_max I hI)).mpr rfl
            have hw := card_withoutFirst (I.filter (· ≤ penultimate I hI))
              (Finset.mem_filter.mpr ⟨h0, Fin.zero_le _⟩)
            have hsZ := congrArg (fun t : ℕ => (t : ℤ)) hsplit
            have hwZ := congrArg (fun t : ℕ => (t : ℤ)) hw
            rw [hr] at hsZ
            push_cast at hsZ hwZ
            have harith : ∀ i l w t : ℤ, t = 2 - i → l + 2 = i + 1 →
                l = w + 1 → t + 1 = 1 - w := by intros; omega
            exact harith _ _ _ _ hk hsZ hwZ))
```

`RawModuleTensorConeTerminalCut.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_terminal_cut_component {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) (ha0 : a = 0)
    (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I)
    (hJ : ((withoutFirst I).erase (Fin.last n)).Nonempty)
    (hkJ : k + 1 = 1 - (((withoutFirst I).erase (Fin.last n)).card : ℤ)) :
    HEq ((strictRawModuleTensorConeData A X P Q c).cutCompose I a b k (penultimate I hI))
      ((k + 1).negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.component
        ((withoutFirst I).erase (Fin.last n)) (k + 1) hJ hkJ)
```

`RawModuleTensorConeNonedgeCut.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_term_of_nonedge_cut {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 2)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) (hc : (I.filter (j ≤ ·)).card ≠ 2) :
    (strictRawModuleTensorConeData A X P Q c).term I a b k hI ha hb hk j hj haj hjb =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • (strictRawModuleTensorConeData A X P Q c).homOrZero (I.erase j) a b (k + 1)
```

`RawModuleTensorConeCutSupport.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_cutCompose_of_nonedge {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 2)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) (hc : (I.filter (j ≤ ·)).card ≠ 2) :
    (strictRawModuleTensorConeData A X P Q c).cutCompose I a b k j = 0

lemma strictRawModuleTensorConeData_cutCompose_of_ne_penultimate {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 2)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) (hne : j ≠ penultimate I hI) :
    (strictRawModuleTensorConeData A X P Q c).cutCompose I a b k j = 0
```

`RawModuleTensorConeQuadratic.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_quadratic_single {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) :
    (strictRawModuleTensorConeData A X P Q c).quadraticBoundary I a b k =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (penultimate I hI) •
      (strictRawModuleTensorConeData A X P Q c).cutCompose I a b k (penultimate I hI)
```

`RawModuleTensorConeRhsReduction.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_rhs_reduced {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) :
    (strictRawModuleTensorConeData A X P Q c).rhs I a b k hI ha hb hk =
    (strictRawModuleTensorConeData A X P Q c).linearBoundary I a b k +
      (strictRawModuleTensorConeData A X P Q c).cutCompose I a b k (penultimate I hI)
```

`RawModuleTensorConeRhsMixedLast.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_rhs_mixed_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) (ha0 : a = 0)
    (hbl : b = Fin.last (n + 1)) (h0 : 0 ∈ I) :
    HEq ((strictRawModuleTensorConeData A X P Q c).rhs I a b k hI ha hb hk)
      (k.negOnePow • (strictRawModuleTensorElementLinear A X P Q c).val.rhs
        (withoutFirst I) k (by have := card_withoutFirst I h0; omega))
```

`RawModuleTensorConeLastEquation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_equation_of_last_mem {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (hlast : Fin.last (n + 1) ∈ I) :
    (strictRawModuleTensorConeData A X P Q c).Equation I
```

`RawModuleTensorConeEquation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma rawModuleSimplexData_equation_image_of_pullback {m n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) n) (α : Fin (m + 1) →o Fin (n + 1))
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) m) (h : s.pullback α = t)
    (J : Finset (Fin (m + 1))) (hi : Set.InjOn α (J : Set (Fin (m + 1))))
    (ht : t.Equation J) : s.Equation (J.image α)

lemma strictRawModuleTensorConeData_equation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) : (strictRawModuleTensorConeData A X P Q c).Equation I
```

`RawModuleTensorConeSimplex.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeSimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 1)

lemma strictRawModuleTensorConeSimplex_data {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorConeSimplex A X P Q c).toSimplexData = strictRawModuleTensorConeData A X P Q c

lemma strictRawModuleTensorConeSimplex_pullback_injective {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) :
    (strictRawModuleTensorConeSimplex A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) =
      strictRawModuleTensorConeSimplex A X P Q
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)

lemma strictRawModuleTensorConeSimplex_tail {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorConeSimplex A X P Q c).pullback (Fin.succOrderEmb (n + 1)).toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q)
```

通常の対象ビルドは成功した。小さい監査の確定結果と実測は §46.1 に記録した。
同じ屋根と K の実 Hom 射への全高次照合、その同値性・完全忠実性、指定 fiber、
一般の native な辺と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 46.1 検証と実測

ClosedPostcomposition と RawModuleTensorSelectedAtMaxImage・SelectedTerminal・ConeMixedLast・
ConeErasedLast・ConeLinearBoundary・SelectedComposition・ConeTerminalComposition・
ConePenultimateValue・ConeTerminalCut・ConeNonedgeCut・ConeCutSupport・ConeQuadratic・
ConeRhsReduction・ConeRhsMixedLast・ConeLastEquation・ConeEquation・ConeSimplex
（省略した接頭辞はすべて RawModuleTensor）の通常の対象ビルドは成功した。
新しい公開宣言 25 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は十八ファイル。上記順で 35・45・59・67・61・84・42・75・93・48・45・52・44・38・
76・43・83・50 行、計 1,040 行、明示宣言 26 本（private 1 本）。
§45.1 の累計に加え、検証済み累計は 117 ファイル・10,482 行・明示宣言 499 本
（private 5 本）。現作業木の M15 所有ソースの合計も同じ 117 ファイル・10,482 行と確認した。
200 行を超える証明はない。一次 ID は追加していない。

元の実 cone の全 HA 方程式、同じデータを持つ実単体、全単射制限と元の全通常末尾面の一致を
検証した。非線形切断和の支持・次数・元の閉射との合成・全削除和の最後の成分と符号は、
同じ dg Hom end の線形成分へ戻して検証している。
先端・終端の型移送を明示し、比較射や方程式の存在を引数に仮定していない。

次は、非単射再添字での元の最上位 cochain の零と通常成分の元の制限を使い、
全 cone 単体の**全作用素**自然性を検証する。その後に同じ元の全 cone/prism を束ねる。
同じ屋根と K の実 Hom 射への全高次照合、その同値性・完全忠実性、指定 fiber、
一般の native な辺と全族はまだ未完。M11 以降と G12 の元の目標、17,000 行の外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 47. M10 の全作用素自然性と同じ大域 cone・prism（11-14）

§46 の同じ実 cone 単体について、選択集合上で単射な任意作用素の像と、
元の制限列の選択 cochain を明示濃度の列挙で照合する。
非単射のときは作用素の実 epi-mono 像分解を使う。全射部分は終端を保つため、
元の非単射成分式の後合成が恒等作用になり、同じ最上位 cochain の零を得る。
恒等作用以外の後合成を取り消すことや、その単射性の仮定は使わない。
元の選択 cochain と同じ混合 cone 成分の零へ、最大元の型の移送を保って戻す。

混合成分の単射/非単射分岐と、元の通常末尾面の全自然性をまとめる。
通常側では潰れた辺の単位分岐も元の閉 nerve の自然性で保持する。
従属関数の外延性により全 `SimplexData` の任意作用素の pullback を一致させ、
同じ実 `Simplex` の**非単射を含む全作用素**自然性を得る。

この同じ全単体族を、元の probe の指定点の下の coslice 写像へ束ねる。
点と nerve の join から元の全通常 dg 加群 nerve への大域 cone を構成し、
先端・全通常図式・任意の元の単体への制限を厳密に回収する。
通常図式の nerve には、元の局所化源と同じ ULiftHom 関手と同じ
`strictRawModuleDGSource` を使う。別の台の模型へ変えていない。

同じ join-cylinder 比較で大域 prism へ移し、両端を元の先端の定値図式と
同じ全通常図式に戻す。同じ区間因子の交換を私有の一般補題へ分け、
Lean の展開上限を増やさず元の全区間ホモトピーを構成する。
さらにその同じ全辺を全関手圏の射として保持する。パラメータを対象ごとの π₀ へ落とさない。

本節は M10 の同じ構成の全再添字・退化・係数移送・端点・貼り合わせの法則と証明の分割で、
一次 ID は追加しない。同じ源の解像度を後合成して §39 の屋根へ照合する段と、
同じ K の Hom 誘導射の同値性・完全忠実性は引き続き必要。
全宣言の型は以下のとおり。

`RawModuleTensorSelectedCardInjOn`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMaxOfCard_image_of_injOn {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) (r : ℕ) (hc : J.card = r + 1) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q c
      (J.image θ.toOrderHom) k (hJ.image θ.toOrderHom)
      (by rw [Finset.card_image_of_injOn hi]; exact hk) r
      (by rw [Finset.card_image_of_injOn hi]; exact hc))
      (strictRawModuleTensorElementSelectedCochainAtMaxOfCard A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        J k hJ hk r hc)
```

`RawModuleTensorSelectedInjOn`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_image_reindex_of_injOn {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    HEq (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c
      (J.image θ.toOrderHom) k (hJ.image θ.toOrderHom)
      (by rw [Finset.card_image_of_injOn hi]; exact hk))
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        J k hJ hk)

lemma strictRawModuleTensorElementSelectedCochainAtMax_image_reindex_of_injOn_smul {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1)))
    (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) (r : ℤˣ) :
    HEq (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c
      (J.image θ.toOrderHom) k (hJ.image θ.toOrderHom)
      (by rw [Finset.card_image_of_injOn hi]; exact hk))
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        J k hJ hk)
```

`RawModuleTensorConeMixedInjOn`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_mixed_of_injOn {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I)
    (hθ : Set.InjOn θ.toOrderHom ((withoutFirst I) : Set (Fin (m + 1)))) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom
          I a b k hI ha hb hk)
```

`RawModuleTensorSurjectiveTop`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementLinear_top_surjective_noninjective {m n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (hs : Function.Surjective θ.toOrderHom)
    (hn : ¬Function.Injective θ.toOrderHom) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (m + 1))).card : ℤ)) :
    (strictRawModuleTensorElementLinear A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component
        Finset.univ k Finset.univ_nonempty hk = 0
```

`RawModuleTensorNoninjectiveTop`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementLinear_top_noninjective {m n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (hn : ¬Function.Injective θ.toOrderHom) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (m + 1))).card : ℤ)) :
    (strictRawModuleTensorElementLinear A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component
        Finset.univ k Finset.univ_nonempty hk = 0
```

`RawModuleTensorSelectedNoninjective`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_reindex_noninjective {m n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (J : Finset (Fin (m + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hn : ¬Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    strictRawModuleTensorElementSelectedCochainAtMax A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) J k hJ hk = 0
```

`RawModuleTensorConeDegenerateMixed`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_hom_mixed_reindex_noninjective {m n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I)
    (hn : ¬Set.InjOn θ.toOrderHom ((withoutFirst I) : Set (Fin (m + 1)))) :
    (strictRawModuleTensorConeData A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom I a b k hI ha hb hk = 0
```

`RawModuleTensorConeDegeneratePullback`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_obj_prepend_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 2)) :
    (strictRawModuleTensorConeData A X P Q c).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i) =
      (strictRawModuleTensorConeData A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).obj i

lemma strictRawModuleTensorConeData_pullback_hom_mixed_not_inj {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I)
    (hn : ¬Set.InjOn θ.toOrderHom ((withoutFirst I) : Set (Fin (m + 1)))) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom
        I a b k hI ha hb hk)
```

`RawModuleTensorConeTailMap`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_tail_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    ((strictRawModuleTensorConeData A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).pullback
      (Fin.succOrderEmb (m + 1)).toOrderHom =
      (strictRawModuleTensorConeData A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).pullback
        (Fin.succOrderEmb (m + 1)).toOrderHom
```

`RawModuleTensorConeOrdinaryMap`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_hom_ordinary_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq (((strictRawModuleTensorConeData A X P Q c).pullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorConeData A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom
        I a b k hI ha hb hk)
```

`RawModuleTensorConeMap`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (strictRawModuleTensorConeData A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) =
      strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
```

`RawModuleTensorConeSimplexMap`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeSimplex_pullback_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (strictRawModuleTensorConeSimplex A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) =
      strictRawModuleTensorConeSimplex A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
```

`RawModuleTensorConeUnderSimplex`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConePoint : (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))

lemma strictRawModuleTensorConePoint_vertex :
    (strictRawModuleTensorConePoint A X P).app (Opposite.op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))

lemma strictRawModuleTensorConeSimplex_vertex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).map
      (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (strictRawModuleTensorConeSimplex A X P Q c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))

def strictRawModuleTensorConeUnderSimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (strictRawModuleTensorConePoint A X P)) _⦋n⦌

lemma strictRawModuleTensorConeSimplex_naturality {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    strictRawModuleTensorConeSimplex A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).map (SimplexCategory.mkHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).op (strictRawModuleTensorConeSimplex A X P Q c)
```

`RawModuleTensorConeUnderMap`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeUnderMap : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (strictRawModuleTensorConePoint A X P)

lemma strictRawModuleTensorConeUnderMap_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorConeUnderMap A X P Q).app (Opposite.op ⦋n⦌) c =
      strictRawModuleTensorConeUnderSimplex A X P Q c
```

`RawModuleTensorConeProjection`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementNerveDiagram :
    nerve (strictRawModuleTensorElementIndex A X P Q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))

lemma strictRawModuleTensorElementNerveDiagram_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorElementNerveDiagram A X P Q).app (Opposite.op ⦋n⦌) c =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q)

lemma strictRawModuleTensorConeUnderMap_projection :
    strictRawModuleTensorConeUnderMap A X P Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (strictRawModuleTensorConePoint A X P) =
      strictRawModuleTensorElementNerveDiagram A X P Q
```

`RawModuleTensorConeJoin`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeJoin :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))

lemma strictRawModuleTensorConeJoin_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorConeJoin A X P Q = strictRawModuleTensorConePoint A X P

lemma strictRawModuleTensorConeJoin_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorConeJoin A X P Q = strictRawModuleTensorElementNerveDiagram A X P Q

lemma strictRawModuleTensorConeJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (SSet.yonedaEquiv.symm c) ≫
      strictRawModuleTensorConeJoin A X P Q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))))).symm
          (strictRawModuleTensorConeSimplex A X P Q c)
```

`RawModuleTensorConePrism`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConePrism : (Δ[1] : SSet.{u + 1}) ⊗
    nerve (strictRawModuleTensorElementIndex A X P Q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))

lemma strictRawModuleTensorConePrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorConePrism A X P Q =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))

lemma strictRawModuleTensorConePrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorConePrism A X P Q = strictRawModuleTensorElementNerveDiagram A X P Q
```

`RawModuleTensorConeFamily`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma conePrismEndpointZero {K T : SSet.{u + 1}}
    (p : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ T) :
    SSet.ι₀ (X := K) ≫ ((β_ K (Δ[1] : SSet.{u + 1})).hom ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ p

private lemma conePrismEndpointOne {K T : SSet.{u + 1}}
    (p : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ T) :
    SSet.ι₁ (X := K) ≫ ((β_ K (Δ[1] : SSet.{u + 1})).hom ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ p

def strictRawModuleTensorConeHomotopy :
    SSet.Homotopy (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))))
      (strictRawModuleTensorElementNerveDiagram A X P Q)

def strictRawModuleTensorConeFamilyHom :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))))
      (strictRawModuleTensorElementNerveDiagram A X P Q)
```

対象ビルド・小さい監査の結果と実測は §47.1 に記録した。
M10 の指定 fiber・一般の native な辺と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 47.1 検証と実測

RawModuleTensorSelectedCardInjOn・SelectedInjOn・ConeMixedInjOn・SurjectiveTop・NoninjectiveTop・
SelectedNoninjective・ConeDegenerateMixed・ConeDegeneratePullback・ConeTailMap・ConeOrdinaryMap・
ConeMap・ConeSimplexMap・ConeUnderSimplex・ConeUnderMap・ConeProjection・ConeJoin・ConePrism・ConeFamily
（省略した接頭辞はすべて RawModuleTensor）の通常の対象ビルドは成功した。
新しい公開宣言 33 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は十八ファイル。上記順で 63・74・79・50・57・82・53・62・42・86・67・31・67・49・
58・49・67・62 行、計 1,098 行、明示宣言 35 本（private 2 本）。
§46.1 の累計に加え、検証済み累計は 135 ファイル・11,580 行・明示宣言 534 本
（private 7 本）。現作業木の M15 所有ソースの合計も同じ 135 ファイル・11,580 行と確認した。
200 行を超える証明はない。一次 ID は追加していない。

元の全 cone 単体の全作用素自然性、同じ先端下の大域 coslice、同じ join cone、
同じ通常図式と任意単体への制限、両端を保つ大域 prism、同じ全区間ホモトピーと
全関手圏の射まで検証した。区間因子の交換は両端の等式補題へ分け、
200,000 heartbeat の上限を増やしていない。前節の実 cone 単体の同じ HA 方程式を使っている。

次は同じ `moduleResolution` の後合成で元の `strictRawModuleSource` へ送り、
同じ通常図式の全等式と指定端点を保って §39 の全実評価屋根へ比較する。
同じ augmentation の全逆と同じ評価の元の三角形、および元の K の実 Hom 誘導射との
全高次照合は引き続き必要。この段階を K の完全忠実性には数えない。
M10 の指定 fiber・一般の native な辺と全族、M11 以降と G12 の元の目標、
17,000 行の外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 48. M10 の同じ解像度による全 cone 像と元の恒等 augmentation 像（11-14）

§47 の同じ全区間族を、既存の同じ `moduleResolution` で後合成した。
元の ULiftHom 表示・同じ dg 源の全合成式によって、全通常図式の像を
`strictRawModuleDiagramSource` と厳密に一致させる。元の通常源の指定頂点の式も保持し、
同じ定値端点へ等式で移送する。この移送の前後で実ホモトピー写像は元の全写像の後合成
そのものであることを別の等式として保持し、全関手圏の同じ射を構成した。

元の全 augmentation の自然性を Yoneda 同値で評価し、普遍 Hom 族の augmentation 像を
元の零次像の定値族へ戻す。同じ Dold–Kan と pinched Hom の座標を使う。
その零次像は次の同じ元のデータで較正する。

- 既存の `moduleParamUncurry_closed` と逆転置の単射性から、単位パラメータに関する元の
  閉射の転置式を回収する。元の左単位比較の転置は同じ恒等閉射の単位パラメータとなる。
- 元の全 augmentation の転置は、同じ AW 余単位の後の元の恒等閉射である。
  AW 余単位と既存の単体収縮の順射の一致、同じ零次生成元での値を使って、
  転置の零次直接値を元の恒等閉 cochain へ戻す。
- 同じ Γ 零次直接評価の単射性と、標準恒等頂点の同じ直接評価を比較して、
  元の augmentation Γ 頂点を同じ標準恒等頂点へ一致させる。
  同じ標準/Γ/pinched 比較で送ると、元の恒等閉 pinched 辺を回収する。

これは smart 切断の**元の閉零元の一致**であり、H⁰ の商の一致で代用していない。
別の単位・自己同型・解像度を選んでいない。
同じ全要素列の終端パラメータでこの全恒等族を前合成し、元の全普遍族と
同じ augmentation の合成が、全次数で元の恒等閉辺の定値族になることを保持した。
同じ恒等単体で評価した各実 pinched 単体の式も保持する。

本節は M10 の同じ構成の単位・余単位・自然性・係数移送・同じ写像の貼り合わせと
証明の分割であり、一次 ID は追加しない。
この実係数の恒等式を、大域 cone と元の通常 augmentation 円柱の**全合成三角形**へ
接続する段は引き続き必要。全係数の恒等式だけからその全三角形を宣言していない。
全宣言の型は以下のとおり。

`TensorAugmentationFamily.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleTensorHomRepresentable_augmentation (P : ModuleCategory A D) (n : SimplexCategory) :
    moduleTensorHomRepresentable A D P P n ((moduleTensorSimplicesAugmentation A D P).app n) =
      SSet.const ((moduleTensorSimplicesAugmentation A D P).app ⦋0⦌)

def moduleTensorAugmentationDoldKanVertex (P : ModuleCategory A D) :
    (((moduleDoldKanHomBifunctor A D).obj (op P)).obj P) _⦋0⦌

lemma moduleTensorHomDoldKanSimplex_augmentation (P : ModuleCategory A D) (n : SimplexCategory) :
    moduleTensorHomDoldKanSimplex A D P P n ((moduleTensorSimplicesAugmentation A D P).app n) =
      SSet.const (moduleTensorAugmentationDoldKanVertex A D P)

private lemma tensorUlift_map_const {K L : SSet.{u}} (z : L _⦋0⦌) :
    SSet.uliftFunctor.{max (u + 1) v, u}.map (SSet.const (X := K) z) =
      SSet.const (ULift.up z)

def moduleTensorAugmentationPinchedVertex (P : ModuleCategory A D) :
    (PinchedHom.pinchedHom A (RightModule A D)
      (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P)) _⦋0⦌

lemma moduleTensorHomPinchedSimplex_augmentation (P : ModuleCategory A D) (n : SimplexCategory) :
    moduleTensorHomPinchedSimplex A D P P n ((moduleTensorSimplicesAugmentation A D P).app n) =
      SSet.const (moduleTensorAugmentationPinchedVertex A D P)

lemma moduleTensorUniversalPinchedSimplex_augmentation (P : ModuleCategory A D)
    (n : SimplexCategory) :
    moduleTensorUniversalPinchedSimplex A D P n ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P
        ((moduleTensorSimplicesAugmentation A D P).app n)) =
    SSet.const (moduleTensorAugmentationPinchedVertex A D P)
```

`TensorAugmentationCurry.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleParamCurry_closed {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleParamCurry A D ((moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom ≫ f) =
      ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f

lemma moduleParamCurry_unit (P : ModuleCategory A D) :
    moduleParamCurry A D (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) P)).hom =
      ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := P) (Y := P) (𝟙 P)

lemma moduleTensorAugmentation_curry (P : ModuleCategory A D) (n : SimplexCategory) :
    moduleParamCurry A D ((moduleTensorSimplicesAugmentation A D P).app n) =
      AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n) ≫
        ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := P) (Y := P) (𝟙 P)

lemma moduleTensorAugmentation_curry_zero (P : ModuleCategory A D) :
    (moduleParamCurry A D ((moduleTensorSimplicesAugmentation A D P).app ⦋0⦌)).f 0
      (normalizedSimplexZeroGenerator A) =
    (closedHomEquiv A (RightModule A D) P P (𝟙 P)).val

lemma moduleTensorAugmentation_gamma_zero_raw (P : ModuleCategory A D) :
    truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
      embeddingDownNat_eq_upIntLE_zero rfl
      (moduleHom A D (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P))
      ((gammaDegreeZeroIso ((moduleHom A D (ForgetEnrichment.to (Complex A) P)
        (ForgetEnrichment.to (Complex A) P)).truncLE'
          (ComplexShape.embeddingUpIntLE 0))).hom (moduleTensorAugmentationDoldKanVertex A D P)) =
    (closedHomEquiv A (RightModule A D) P P (𝟙 P)).val
```

`TensorAugmentationIdentity.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleIdentityDoldKanVertex (P : ModuleCategory A D) :
    (((moduleDoldKanHomBifunctor A D).obj (op P)).obj P) _⦋0⦌

lemma moduleIdentityDoldKanVertex_raw (P : ModuleCategory A D) :
    truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
      embeddingDownNat_eq_upIntLE_zero rfl
      (moduleHom A D (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P))
      ((gammaDegreeZeroIso (connectiveHomComplex (R := A) (D := RightModule A D)
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P))).hom
          (moduleIdentityDoldKanVertex A D P)) =
    (closedHomEquiv A (RightModule A D) P P (𝟙 P)).val

lemma moduleTensorAugmentation_gamma_zero_eq (P : ModuleCategory A D) :
    moduleTensorAugmentationDoldKanVertex A D P = moduleIdentityDoldKanVertex A D P

lemma moduleIdentityDoldKanVertex_pinched (P : ModuleCategory A D) :
    (moduleDoldKanPinchedIso A D P P).hom.app (op ⦋0⦌) (ULift.up (moduleIdentityDoldKanVertex A D P)) =
      pinchedClosedVertex A (RightModule A D) (𝟙 P)

lemma moduleTensorAugmentationVertex_identity (P : ModuleCategory A D) :
    moduleTensorAugmentationPinchedVertex A D P =
      pinchedClosedVertex A (RightModule A D) (𝟙 P)

lemma moduleTensorUniversalPinchedSimplex_augmentation_identity (P : ModuleCategory A D)
    (n : SimplexCategory) :
    moduleTensorUniversalPinchedSimplex A D P n ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P
        ((moduleTensorSimplicesAugmentation A D P).app n)) =
    SSet.const (pinchedClosedVertex A (RightModule A D) (𝟙 P))
```

`RawModuleTensorConeSource.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma coneHomotopyTransport_h {K T : SSet.{u + 1}} {f g f' g' : K ⟶ T}
    (hf : f = f') (hg : g = g') (H : SSet.Homotopy f g) :
    ((congrArg₂ (fun a b => SSet.Homotopy a b) hf hg).mp H).h = H.h

def strictRawModuleTensorConeMappedHomotopy {C : SSet.{u + 1}}
    (F : dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) ⟶ C) :
    SSet.Homotopy
      (SSet.const (F.app (op ⦋0⦌)
        ((dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm
          (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))))
      (strictRawModuleTensorElementNerveDiagram A X P Q ≫ F)

lemma strictRawModuleTensorConeMappedHomotopy_h {C : SSet.{u + 1}}
    (F : dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) ⟶ C) :
    (strictRawModuleTensorConeMappedHomotopy A X P Q F).h =
      (strictRawModuleTensorConeHomotopy A X P Q).h ≫ F

lemma strictRawModuleTensorElementNerveDiagram_source :
    strictRawModuleTensorElementNerveDiagram A X P Q ≫
      moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)) =
    strictRawModuleDiagramSource A X (strictRawModuleTensorElementDiagram A X P Q)

lemma strictRawModuleTensorConeSource_vertex :
    (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))).app (op ⦋0⦌)
      ((dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))) =
    (strictRawModuleSource A X).app (op ⦋0⦌)
      (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj
        ((strictRawModuleProbeFunctor A X).obj P)))

def strictRawModuleTensorConeSourceHomotopy :
    SSet.Homotopy
      (SSet.const ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj
          ((strictRawModuleProbeFunctor A X).obj P)))))
      (strictRawModuleDiagramSource A X (strictRawModuleTensorElementDiagram A X P Q))

lemma strictRawModuleTensorConeSourceHomotopy_h :
    (strictRawModuleTensorConeSourceHomotopy A X P Q).h =
      (strictRawModuleTensorConeHomotopy A X P Q).h ≫
        moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))

def strictRawModuleTensorConeSourceFamilyHom :
    FunctorHom
      (SSet.const ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj
          ((strictRawModuleProbeFunctor A X).obj P)))))
      (strictRawModuleDiagramSource A X (strictRawModuleTensorElementDiagram A X P Q))
```

`RawModuleTensorConeAugmentation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementPinchedFamily_augmentation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorElementPinchedFamily A X P Q c ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (Fin.last n)))) =
    SSet.const (moduleTensorAugmentationPinchedVertex A
      (dgAlgebraCategory A ((assocForget A).obj X)) ((strictRawModuleProbeFunctor A X).obj P))

lemma strictRawModuleTensorElementPinchedSimplex_augmentation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (Fin.last n))))).app
        (op ⦋n⦌) (strictRawModuleTensorElementPinchedSimplex A X P Q c) =
    (PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))).map
        (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (moduleTensorAugmentationPinchedVertex A (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P))

lemma strictRawModuleTensorElementPinchedFamily_augmentation_identity {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorElementPinchedFamily A X P Q c ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (Fin.last n)))) =
    SSet.const (pinchedClosedVertex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (𝟙 ((strictRawModuleProbeFunctor A X).obj P)))

lemma strictRawModuleTensorElementPinchedSimplex_augmentation_identity {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (Fin.last n))))).app
        (op ⦋n⦌) (strictRawModuleTensorElementPinchedSimplex A X P Q c) =
    (PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))).map
        (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (pinchedClosedVertex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (𝟙 ((strictRawModuleProbeFunctor A X).obj P)))
```

通常の対象ビルドは成功した。小さい監査の確定結果と実測は §48.1 に記録した。
同じ全実評価屋根・K の Hom 誘導射との全高次照合、その同値性・完全忠実性、
M10 の指定 fiber・一般の native な辺と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 48.1 検証と実測

TensorAugmentationFamily・TensorAugmentationCurry・TensorAugmentationIdentity・
RawModuleTensorConeSource・RawModuleTensorConeAugmentation の通常の対象ビルドは成功した。
新しい公開宣言 28 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は五ファイル、上記順で 95・89・116・131・108 行、計 539 行、
明示宣言 30 本（private 2 本）。§47.1 の累計に加え、検証済み累計は
140 ファイル・12,119 行・明示宣言 564 本（private 9 本）。
現作業木の M15 所有ソースの合計も同じ 140 ファイル・12,119 行と確認した。
200 行を超える証明はない。一次 ID は追加していない。

同じ全 cone の元の導来源への後合成・全図式の等式・指定端点・実ホモトピー写像の保持、
同じ普遍 Hom 族の全 augmentation 像の定値化、元の単位パラメータ閉射と転置の式、
同じ零次生成元と Γ の単射な直接評価による元の恒等閉辺への較正、
元の全要素列・全次数の同じ恒等定数族と全実単体の式まで検証した。
元の augmentation 像を任意の自己同型として置く代用はしていない。

次は、同じ恒等係数を使う全二重 cone と元の通常 augmentation 円柱を比較し、
同じ全関手圏における合成三角形と全 augmentation 逆の一致を閉じる。
この同じ全三角形を仮定として追加せずに構成する。
同じ全実評価屋根・元の K の Hom 誘導射への全高次照合、その同値性・完全忠実性、
指定 fiber・一般の native な辺と全族はまだ未完。
M11 以降と G12 の元の目標、17,000 行の外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## §49 同じ全 cone の元の augmentation と全次数の厳密な両立

§48 の全 pinched 族の恒等像を同じ全線形表示へ送り、任意の有限部分集合の
成分の augmentation 像を回収した。二点以上の部分集合では元の非単射 pullback
成分が零となり、一点では元の恒等閉辺の cochain をそのまま回収する。
同じ選択列の最後から元の最大点への型移送と後合成を両立させた。

同じ元の全 cone の各対象の augmentation は、先端では元の恒等射、通常の
対象では元の frame augmentation である。各成分の擬同型性と全単体作用素の
再添字式を確認する。混合成分は元の符号つき選択 cochain の像であり、
通常の零次辺は元の augmentation の自然性で照合する。この二つを合わせ、
任意の有限部分集合 I、元の端点 a,b と整数次数 k に対して、
augmentation と元の cone の斉次成分の合成が同じ始点 augmentation の
closedNerveHom となる式を実装した。

この同じ条件の記録が ModuleSimplexAugmentation であり、
strictRawModuleTensorConeSimplexAugmentation は元の cone 単体に同じ実射と
今回の全合成則を代入して作る。右 cone の存在や全三角形を仮定する記録ではない。
各成分の元の加群擬同型性も同じ既存の各成分の証明から回収する。

以下は M10 の既存構成の係数移送・自然性・合成の法則と証明の分割であり、
新しい一次 ID は追加しない。全二重 cone、元の通常 augmentation 円柱との
比較と全関手圏での三角形そのものはここではまだ主張しない。
対象ビルドと新規公開宣言の小さい監査は §50.1 のとおり成功した。

**一覧：済み 10／全体 43（うち追加 1）**。

`SimplexAugmentation.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

structure ModuleSimplexAugmentation {n : ℕ} (s : Simplex A (RightModule A D) n)
    (M : ModuleCategory A D) where
  app : ∀ i, ForgetEnrichment.of (Complex A) (s.obj i) ⟶ M
  hom_naturality : ∀ (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
      (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
      (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)),
      compose A (closedHomEquiv A (RightModule A D) _ _ (app b)).val
        (s.hom I a b k hI ha hb hk) (add_zero k) = closedNerveHom (app a) k

def ModuleSimplexAugmentation.cycle {n : ℕ} {s : Simplex A (RightModule A D) n}
    {M : ModuleCategory A D} (η : ModuleSimplexAugmentation A D s M) (i : Fin (n + 1)) :
    zeroCycles (homObject A (RightModule A D) (s.obj i) (ForgetEnrichment.to (Complex A) M))

lemma ModuleSimplexAugmentation.cycle_closed {n : ℕ} {s : Simplex A (RightModule A D) n}
    {M : ModuleCategory A D} (η : ModuleSimplexAugmentation A D s M) (i : Fin (n + 1)) :
    differential A (ModuleSimplexAugmentation.cycle A D η i).val = 0
```

`RawModuleTensorLinearAugmentation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementLinear_augmentation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (E := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (x := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (x' := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (Fin.last n))))
      (strictRawModuleTensorElementLinear A X P Q c) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).toOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (𝟙 ((strictRawModuleProbeFunctor A X).obj P))))

lemma strictRawModuleTensorElementLinear_augmentation_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : 2 ≤ J.card) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (Fin.last n)))).f k
      ((strictRawModuleTensorElementLinear A X P Q c).val.component J k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) hk) = 0
```

`RawModuleTensorLinearAugmentationVertex.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementLinear_augmentation_vertex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app
      (c.obj (Fin.last n)))).f 0
      ((strictRawModuleTensorElementLinear A X P Q c).val.component J 0 hJ (by omega)) =
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (𝟙 ((strictRawModuleProbeFunctor A X).obj P))).val
```

`RawModuleTensorSelectedAugmentation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_augmentation_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hc : 2 ≤ J.card) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (J.max' hJ)))).f k
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) = 0

lemma strictRawModuleTensorElementSelectedCochainAtMax_augmentation_smul_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hc : 2 ≤ J.card) (r : ℤˣ) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (J.max' hJ)))).f k
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) = 0

lemma strictRawModuleTensorElementSelectedCochainAtMax_augmentation_compose_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hc : 2 ≤ J.card) (r : ℤˣ) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (J.max' hJ)))).val
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) (add_zero k) = 0
```

`RawModuleTensorSelectedAugmentationVertex.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_augmentation_vertex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (J.max' hJ)))).f 0
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J 0 hJ (by omega)) =
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (𝟙 ((strictRawModuleProbeFunctor A X).obj P))).val

lemma strictRawModuleTensorElementSelectedCochainAtMax_augmentation_compose_vertex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (hJ : J.Nonempty) (hc : J.card = 1) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (J.max' hJ)))).val
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J 0 hJ (by omega)) (add_zero 0) =
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (𝟙 ((strictRawModuleProbeFunctor A X).obj P))).val
```

`RawModuleTensorConeAugmentationAt.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeAugmentationAt {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 2)) :
    ForgetEnrichment.of (Complex A) ((strictRawModuleTensorConeData A X P Q c).obj i) ⟶ ((strictRawModuleProbeFunctor A X).obj P)

lemma strictRawModuleTensorConeAugmentationAt_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorConeAugmentationAt A X P Q c 0 = 𝟙 ((strictRawModuleProbeFunctor A X).obj P)

lemma strictRawModuleTensorConeAugmentationAt_succ {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 1)) :
    strictRawModuleTensorConeAugmentationAt A X P Q c i.succ =
      (strictRawModuleTensorElementAugmentation A X P Q).app (c.obj i)

lemma strictRawModuleTensorConeAugmentationAt_postcompose_mixed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq ((eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) ((strictRawModuleTensorConeData A X P Q c).obj a))
      (strictRawModuleTensorConeAugmentationAt A X P Q c b)).f k
        ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk))
      ((eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app
        (c.obj ((withoutFirst I).max' (withoutFirst_nonempty hI h0))))).f k
        (k.negOnePow • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c (withoutFirst I) k
          (withoutFirst_nonempty hI h0) (by have := card_withoutFirst I h0; omega)))

lemma strictRawModuleTensorConeAugmentationAt_quasiIso {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 2)) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) (strictRawModuleTensorConeAugmentationAt A X P Q c i)

lemma strictRawModuleTensorConeAugmentationAt_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 2)) :
    HEq (strictRawModuleTensorConeAugmentationAt A X P Q c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i))
      (strictRawModuleTensorConeAugmentationAt A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) i)
```

`RawModuleTensorConeAugmentationPositive.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeAugmentationAt_compose_of_card_ge_three {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c b)).val
      ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk) (add_zero k) = 0
```

`RawModuleTensorConeAugmentationEdge.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeAugmentationAt_compose_mixed_pair {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq (compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c b)).val
      ((strictRawModuleTensorConeData A X P Q c).hom I a b 0 hI ha hb hk) (add_zero 0))
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (𝟙 ((strictRawModuleProbeFunctor A X).obj P))).val
```

`RawModuleTensorConeAugmentationOrdinary.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeAugmentationAt_compose_ordinary_pair {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c b)).val
      ((strictRawModuleTensorConeData A X P Q c).hom I a b 0 hI ha hb hk) (add_zero 0) =
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c a)).val
```

`RawModuleTensorConeAugmentationCompatibility.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeAugmentationAt_compose_pair {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c b)).val
      ((strictRawModuleTensorConeData A X P Q c).hom I a b 0 hI ha hb hk) (add_zero 0) =
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c a)).val

lemma strictRawModuleTensorConeAugmentationAt_compose {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c b)).val
      ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk) (add_zero k) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q c a) k
```

`RawModuleTensorConeSimplexAugmentation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeSimplexAugmentation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    ModuleSimplexAugmentation A (dgAlgebraCategory A ((assocForget A).obj X))
      (strictRawModuleTensorConeSimplex A X P Q c) ((strictRawModuleProbeFunctor A X).obj P)

lemma strictRawModuleTensorConeSimplexAugmentation_app_weak {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 2)) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleTensorConeSimplexAugmentation A X P Q c).app i)
```


## §50 同じ実 augmentation による全加群二重 cone 単体

§49 の同じ全合成則を入力にして、同じ dg 加群単体へ指定終端を追加する
実右 cone の全 HA 方程式を実装した。前面には元の単体をそのまま使い、
終端への成分には元の閉 augmentation を使う。終端を含まない集合は
元の前面の HA 方程式へ戻し、終端を含む集合では閉性と同じ全合成則により
各内部項の削除項・合成項を相殺する。任意の有限部分集合と整数次数を保つ。

strictRawModuleTensorDoubleConeSimplex は、§49 の元の全 cone 単体と実 augmentation
を同じ右 cone へ代入した実単体である。前面が元の cone 単体であり、
終端が同じ元の probe である式まで実装した。右 cone や全 HA 方程式を
存在仮定として置いていない。任意の E への輸送も追加しない。

これは M10 の同じ全三角形に用いる既存の cone 構成と、その前面・終端の法則の
証明分割であり、一次 ID は追加しない。全二重 cone の全単体作用素に対する
自然性、slice での全 prism と元の通常 augmentation 円柱との比較、
同じ導来源への後合成による全三角形、元の augmentation 逆と評価屋根の照合は
まだ未完である。§49 と合わせた対象ビルド・新規公開宣言だけの監査は、
§50.1 のとおり同じ一つの impl 整理券で成功した。

**一覧：済み 10／全体 43（うち追加 1）**。

`RightConeClosed.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeData_differential_last {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    differential A ((moduleRightConeData A D η).hom I a b k hI ha hb hk) = 0
```

`RightConeComponents.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeData_hom_ordinary {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b ≠ Fin.last (n + 1)) :
    HEq ((moduleRightConeData A D η).hom I a b k hI ha hb hk)
      ((s.toSimplexData.pullback (Fin.last n).predAboveOrderHom).hom I a b k hI ha hb hk)

lemma moduleRightConeData_hom_last {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    HEq ((moduleRightConeData A D η).hom I a b k hI ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (η.app ((Fin.last n).predAboveOrderHom a)) k)
```

`RightConeData.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleRightConeObj {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n) (M : ModuleCategory A D)
    (i : Fin (n + 2)) : RightModule A D

lemma moduleRightConeObj_last {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n) (M : ModuleCategory A D) :
    moduleRightConeObj A D s M (Fin.last (n + 1)) = (ForgetEnrichment.to (Complex A) M)

lemma moduleRightConeObj_ne_last {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n) (M : ModuleCategory A D)
    (i : Fin (n + 2)) (hi : i ≠ Fin.last (n + 1)) :
    moduleRightConeObj A D s M i = s.obj ((Fin.last n).predAboveOrderHom i)

lemma moduleRightConeObj_castSucc {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n) (M : ModuleCategory A D)
    (i : Fin (n + 1)) : moduleRightConeObj A D s M i.castSucc = s.obj i

def moduleRightConeData {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) (n + 1)
```

`RightConeFront.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeData_front {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) :
    (moduleRightConeData A D η).pullback Fin.castSuccOrderEmb.toOrderHom = s.toSimplexData
```

`RightConeFrontEquation.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeData_equation_without_last {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) (I : Finset (Fin (n + 2)))
    (hl : Fin.last (n + 1) ∉ I) : (moduleRightConeData A D η).Equation I
```

`RightConeNaturality.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeIndex_recover {n : ℕ} (i : Fin (n + 2))
    (hi : i ≠ Fin.last (n + 1)) :
    ((Fin.last n).predAboveOrderHom i).castSucc = i

lemma moduleRightConeIndex_injOn {n : ℕ} (I : Finset (Fin (n + 2)))
    (b : Fin (n + 2)) (hI : 2 ≤ I.card) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hbl : b ≠ Fin.last (n + 1)) :
    Set.InjOn (Fin.last n).predAboveOrderHom (I : Set (Fin (n + 2)))

lemma moduleRightConeData_front_compose {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b ≠ Fin.last (n + 1)) :
    compose A (closedHomEquiv A (RightModule A D) _ _ (η.app ((Fin.last n).predAboveOrderHom b))).val
      ((s.toSimplexData.pullback (Fin.last n).predAboveOrderHom).hom I a b k hI ha hb hk)
      (add_zero k) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (η.app ((Fin.last n).predAboveOrderHom a)) k
```

`RightConeSimplex.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeData_equation_last {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) (I : Finset (Fin (n + 2)))
    (hl : Fin.last (n + 1) ∈ I) : (moduleRightConeData A D η).Equation I

def moduleRightConeSimplex {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) (n + 1)

lemma moduleRightConeSimplex_data {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) :
    (moduleRightConeSimplex A D η).toSimplexData = moduleRightConeData A D η

lemma moduleRightConeSimplex_front {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M) :
    (moduleRightConeSimplex A D η).pullback Fin.castSuccOrderEmb.toOrderHom = s
```

`RightConeTerminalComposition.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeData_terminal_compose {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1))
    (j : Fin (n + 2)) (hj : j ∈ I) (haj : a < j) (hjb : j < b)
    (hrc : (I.filter (j ≤ ·)).card = 2) :
    HEq (compose A
      ((moduleRightConeData A D η).hom (I.filter (j ≤ ·)) j b
        (2 - ((I.filter (j ≤ ·)).card : ℤ))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj (by rw [hb]; exact I.max'_mem _) hjb)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max (by rw [hb]; exact I.isGreatest_max' _) hjb.le _)
        rfl)
      ((moduleRightConeData A D η).hom (I.filter (· ≤ j)) a j
        (2 - ((I.filter (· ≤ j)).card : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two (by rw [ha]; exact I.min'_mem _) hj haj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min (by rw [ha]; exact I.isLeast_min' _) haj.le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl)
      (show (2 - ((I.filter (· ≤ j)).card : ℤ)) +
        (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 by
          have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (η.app ((Fin.last n).predAboveOrderHom a))
        (2 - ((I.filter (· ≤ j)).card : ℤ)))
```

`RightConeTerminalTerm.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeData_term_last {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1))
    (j : Fin (n + 2)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    (moduleRightConeData A D η).term I a b k hI ha hb hk j hj haj hjb = 0
```

`RightConeTerminalZero.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleRightConeData_hom_last_zero {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) n} {M : ModuleCategory A D}
    (η : ModuleSimplexAugmentation A D s M)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1)) (hk0 : k ≠ 0) :
    (moduleRightConeData A D η).hom I a b k hI ha hb hk = 0
```

`RawModuleTensorDoubleConeSimplex.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorDoubleConeSimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 2)

lemma strictRawModuleTensorDoubleConeSimplex_front {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).pullback Fin.castSuccOrderEmb.toOrderHom =
      strictRawModuleTensorConeSimplex A X P Q c

lemma strictRawModuleTensorDoubleConeSimplex_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).obj (Fin.last (n + 2)) =
      ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
```


### 50.1 検証と実測

RawModuleTensorDoubleConeSimplex の通常の対象ビルドは成功した。
この対象が §49・§50 の新しい全二十二ファイルを import する。
新規公開宣言 47 本の依存公理監査も成功し、すべて
propext・Classical.choice・Quot.sound の範囲である。
引用属性の新規追加はなく、引用出力は 0 本。impl 鍵・待ち 3600 秒、
gtimeout 280 秒の同じ一つの実行で対象ビルドと小さい監査を行い、
プロセスの終了値 0 を確認した。root ビルドや大きい監査は実行していない。

| 区分 | 新規 Lean ファイル | 行数 | 明示宣言 |
| --- | ---: | ---: | ---: |
| §49 の全 augmentation・型の記録と実代入 | 11 | 664 | 24 |
| §50 の右 cone・同じ実二重 cone | 11 | 579 | 23 |
| 今回の追加 | 22 | 1,243 | 47 |

private の新規宣言は 0 本。§48.1 の累計に加え、検証済み累計は
162 ファイル・13,362 行・明示宣言 611 本（private 9 本）。
現作業木の M15 所有ソースを再計数し、同じ値と確認した。
17,000 行の外枠まで残り 3,638 行である。
今回、200 行を超える証明はない。一次 ID は追加していない。

元の実 augmentation の全次数の合成則と各成分の擬同型性、
全再添字の各成分の移送、元の実 cone 単体への同じデータの代入、
同じ右 cone の全 HA 方程式・前面の厳密な一致、
同じ実二重 cone の前面と元の終端まで検証した。
通常辺の証明では、依存する式全体への始点の置換を有限添字の帰納法へ変更し、
全次数のまとめでは、Hom end を展開する書き換えを元の等式の直接の合成へ変更した。
200,000 heartbeat の既定上限は増やしていない。

次は、この同じ全二重 cone の全単体作用素に対する自然性、
元の全 slice prism と同じ通常 augmentation 円柱との比較を作る。
同じ導来源へ後合成した全三角形、元の全 augmentation 逆・評価屋根との一致、
元の K の全 Hom 誘導射の照合・同値性・完全忠実性、指定 fiber と native な辺・全族は
まだ未完である。M11 以降と G12 の元の目標、17,000 行の外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## §51 同じ二重 cone の全自然性と slice 普遍評価の大域三角形

§50 の同じ実二重 cone を、退化を含む全単体作用素に対して自然にした。
終端を避ける成分は元の前面の全等式から回収し、終端を含む成分は
選択した集合上の単射と非単射で分ける。作用素全体の単射性は要求しない。
非単射の場合、終端の二点辺は潰れないので部分集合の要素数が二以外であり、
元の非零次数の閉 augmentation 成分と同じ零を両側で比較する。
型移送は元の対象の等式と異種等号を明記して行う。

同じ二重 cone の先端と終端を結ぶ実一単体は、元の probe の恒等閉射の
定値通常単体と厳密に一致する。これを使い、同じ終端上の slice における
最初の頂点を元の恒等錐そのものへ同定し、元の全要素圏の nerve 上で
同じ slice 図式・二重 join・全区間 prism を構成する。
その前面・終端・全元単体への制限と元の全 cone への射影を保持する。

同じ slice 図式の普遍評価から全ホモトピーを構成し、実写像 h が
元の rightMappingSpacePrism と同じ sliceOverUncurry による写像である式を残す。
全 prism の始端が元の恒等錐、終端が同じ全 slice 図式、射影が元の cone prism
である式を使い、全関手圏で元の cone 族と同じ slice 評価族の合成が恒等となる
三角形を実装した。点ごとの射の類の一致だけには置き換えない。

この時点の評価族は、元の通常 augmentation 円柱との一致をまだ主張しない。
同じ元の導来源への後合成、元の全 augmentation 逆との比較と
元の評価屋根、K の Hom 誘導射の同値性・完全忠実性、指定 fiber・native な全族は
まだ未完である。M10 の同じ既存構成の自然性・係数移送・合成の法則と
証明分割であり、一次 ID は追加しない。
対象ビルドと新規公開宣言の小さい監査は §51.1 のとおり成功した。

**一覧：済み 10／全体 43（うち追加 1）**。

`RawModuleTensorDoubleConeEndEdge.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeSimplex_end_edge {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).pullback (doubleConeEndEdgeOrderHom n) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex ((Functor.const (Fin 2)).obj ((strictRawModuleProbeFunctor A X).obj P))
```

`RawModuleTensorDoubleConeFrontMap.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeSimplex_obj_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 3)) :
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).obj (doubleConeOrderHom θ i) =
      (strictRawModuleTensorDoubleConeSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).obj i

lemma strictRawModuleTensorDoubleConeSimplex_pullback_front {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    ((strictRawModuleTensorDoubleConeSimplex A X P Q c).pullback (doubleConeOrderHom θ)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      (strictRawModuleTensorDoubleConeSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).pullback
        Fin.castSuccOrderEmb.toOrderHom
```

`RawModuleTensorDoubleConeJoin.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorDoubleConeJoin :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q))) Δ[0] ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))

lemma strictRawModuleTensorDoubleConeJoin_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q))) Δ[0] ≫
      strictRawModuleTensorDoubleConeJoin A X P Q = strictRawModuleTensorConeJoin A X P Q

lemma strictRawModuleTensorDoubleConeJoin_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q))) Δ[0] ≫
      strictRawModuleTensorDoubleConeJoin A X P Q = strictRawModuleTensorConePoint A X P

lemma strictRawModuleTensorDoubleConeJoin_endpoints :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)))
      (𝟙 Δ[0]) ≫ strictRawModuleTensorDoubleConeJoin A X P Q =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))

lemma strictRawModuleTensorDoubleConeJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (SSet.yonedaEquiv.symm c)) (𝟙 Δ[0]) ≫
      strictRawModuleTensorDoubleConeJoin A X P Q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom (𝟙 Δ[0]) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 0).hom ≫
          (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))))).symm
            (strictRawModuleTensorDoubleConeSimplex A X P Q c)
```

`RawModuleTensorDoubleConeMap.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeData_pullback_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).toSimplexData.pullback (doubleConeOrderHom θ) =
      (strictRawModuleTensorDoubleConeSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).toSimplexData

lemma strictRawModuleTensorDoubleConeSimplex_pullback_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).pullback (doubleConeOrderHom θ) =
      strictRawModuleTensorDoubleConeSimplex A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
```

`RawModuleTensorDoubleConeOverDiagram.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorIdentityOverPoint_vertex :
    (strictRawModuleTensorIdentityOverPoint A X P).app (Opposite.op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))

def strictRawModuleTensorDoubleConeOverDiagram : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P)

lemma strictRawModuleTensorDoubleConeOverJoin_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorDoubleConeOverJoin A X P Q = strictRawModuleTensorDoubleConeOverDiagram A X P Q

lemma strictRawModuleTensorDoubleConeOverDiagram_projection :
    strictRawModuleTensorDoubleConeOverDiagram A X P Q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (strictRawModuleTensorConePoint A X P) =
        strictRawModuleTensorElementNerveDiagram A X P Q
```

`RawModuleTensorDoubleConeOverFirst.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeOverSimplex_first_vertex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P)).map
      (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
      (strictRawModuleTensorDoubleConeOverSimplex A X P Q c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))
```

`RawModuleTensorDoubleConeOverJoin.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorDoubleConeOverJoin :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P)

lemma strictRawModuleTensorDoubleConeOverJoin_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorDoubleConeOverJoin A X P Q = strictRawModuleTensorIdentityOverPoint A X P

lemma strictRawModuleTensorDoubleConeOverJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (SSet.yonedaEquiv.symm c) ≫
      strictRawModuleTensorDoubleConeOverJoin A X P Q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P))).symm
          (strictRawModuleTensorDoubleConeOverSimplex A X P Q c)
```

`RawModuleTensorDoubleConeOverNaturality.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeOverSimplex_naturality {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    strictRawModuleTensorDoubleConeOverSimplex A X P Q ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P)).map
        (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom)).op
        (strictRawModuleTensorDoubleConeOverSimplex A X P Q c)

lemma strictRawModuleTensorDoubleConeOverSimplex_projection {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (strictRawModuleTensorConePoint A X P)).app (Opposite.op ⦋n + 1⦌)
      (strictRawModuleTensorDoubleConeOverSimplex A X P Q c) = strictRawModuleTensorConeSimplex A X P Q c
```

`RawModuleTensorDoubleConeOverProjection.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeOverJoin_projection :
    strictRawModuleTensorDoubleConeOverJoin A X P Q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (strictRawModuleTensorConePoint A X P) = strictRawModuleTensorConeJoin A X P Q
```

`RawModuleTensorDoubleConeOverSimplex.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeSimplex_last_vertex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).map
      (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ (Fin.last (n + 2))).op
      (strictRawModuleTensorDoubleConeSimplex A X P Q c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))

def strictRawModuleTensorDoubleConeOverSimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P)) _⦋n + 1⦌
```

`RawModuleTensorDoubleConeSliceEvaluation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma sliceEvaluationEndpointZero {K T : SSet.{u + 1}} (z : T _⦋0⦌)
    (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z))
    (f : K ⟶ T)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z) = f) :
    SSet.ι₀ (X := K) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z) a).h = f

private lemma sliceEvaluationEndpointOne {K T : SSet.{u + 1}} (z : T _⦋0⦌)
    (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) :
    SSet.ι₁ (X := K) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofSliceEvaluationHomotopy z) a).h = SSet.const z

def strictRawModuleTensorDoubleConeSliceEvaluationHomotopy :
    SSet.Homotopy (strictRawModuleTensorElementNerveDiagram A X P Q)
      (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))))

lemma strictRawModuleTensorDoubleConeSliceEvaluationHomotopy_h :
    (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy A X P Q).h =
      (β_ (nerve (strictRawModuleTensorElementIndex A X P Q)) (Δ[1] : SSet.{u + 1})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (strictRawModuleTensorDoubleConeOverDiagram A X P Q)

def strictRawModuleTensorDoubleConeSliceEvaluationHom :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (strictRawModuleTensorElementNerveDiagram A X P Q)
      (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))))
```

`RawModuleTensorDoubleConeSlicePrism.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorDoubleConeSlicePrism : (Δ[1] : SSet.{u + 1}) ⊗
    nerve (strictRawModuleTensorElementIndex A X P Q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P)

lemma strictRawModuleTensorDoubleConeSlicePrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorDoubleConeSlicePrism A X P Q =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))))

lemma strictRawModuleTensorDoubleConeSlicePrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorDoubleConeSlicePrism A X P Q = strictRawModuleTensorDoubleConeOverDiagram A X P Q
```

`RawModuleTensorDoubleConeSlicePrismProjection.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeSlicePrism_projection :
    strictRawModuleTensorDoubleConeSlicePrism A X P Q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (strictRawModuleTensorConePoint A X P) = strictRawModuleTensorConePrism A X P Q
```

`RawModuleTensorDoubleConeSliceTriangle.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma sliceTriangleFromPrism {K T : SSet.{u + 1}} (z : T _⦋0⦌)
    {f : K ⟶ T} (l : SSet.Homotopy (SSet.const z) f)
    (t : SSet.Homotopy f (SSet.const z))
    (a : K ⟶ sliceOver (SSet.yonedaEquiv.symm z))
    (p : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ sliceOver (SSet.yonedaEquiv.symm z))
    (hb : prismEndpoint 0 K ≫ p = SSet.const (sliceIdentityCone z))
    (ht : prismEndpoint 1 K ≫ p = a)
    (hl : (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ p ≫
      sliceOverProjection (SSet.yonedaEquiv.symm z) = l.h)
    (he : t.h = (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ rightMappingSpacePrism K ≫
      sliceOverUncurry a) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy t) =
      𝟙 (SSet.HomotopyCategory.mk (functorVertex (SSet.const (X := K) z)))

lemma strictRawModuleTensorDoubleConeSliceEvaluation_triangle :
    strictRawModuleTensorConeFamilyHom A X P Q ≫ strictRawModuleTensorDoubleConeSliceEvaluationHom A X P Q =
      𝟙 (SSet.HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := nerve (strictRawModuleTensorElementIndex A X P Q))
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))))))
```

`RawModuleTensorDoubleConeTerminalInjOn.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeSimplex_pullback_hom_terminal_injOn {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 3))) (a b : Fin (m + 3)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (m + 2))
    (hi : Set.InjOn (doubleConeOrderHom θ) (I : Set (Fin (m + 3)))) :
    HEq (((strictRawModuleTensorDoubleConeSimplex A X P Q c).toSimplexData.pullback
      (doubleConeOrderHom θ)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorDoubleConeSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom I a b k hI ha hb hk)
```

`RawModuleTensorDoubleConeTerminalNoninjective.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeSimplex_pullback_hom_terminal_not_inj {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (I : Finset (Fin (m + 3))) (a b : Fin (m + 3)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (m + 2))
    (hn : ¬Set.InjOn (doubleConeOrderHom θ) (I : Set (Fin (m + 3)))) :
    HEq (((strictRawModuleTensorDoubleConeSimplex A X P Q c).toSimplexData.pullback
      (doubleConeOrderHom θ)).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorDoubleConeSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).hom I a b k hI ha hb hk)
```

`RawModuleTensorDoubleConeTerminalValue.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeAugmentationClosed_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 2)) (k : ℤ) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i)) k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q
          ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) i) k)

lemma strictRawModuleTensorDoubleConeTerminalValue_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 3)) (k : ℤ) (hi : i ≠ Fin.last (m + 2)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q c
        ((Fin.last (n + 1)).predAboveOrderHom (doubleConeOrderHom θ i))) k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q
          ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
          ((Fin.last (m + 1)).predAboveOrderHom i)) k)
```

`RawModuleTensorDoubleConeUnderOverMap.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorDoubleConeUnderOverMap : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (strictRawModuleTensorIdentityOverPoint A X P)

lemma strictRawModuleTensorDoubleConeUnderOverMap_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorDoubleConeUnderOverMap A X P Q).app (Opposite.op ⦋n⦌) c =
      strictRawModuleTensorDoubleConeUnderOverSimplex A X P Q c
```

`RawModuleTensorDoubleConeUnderOverSimplex.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorIdentityOverPoint : (Δ[0] : SSet.{u + 1}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P)

lemma strictRawModuleTensorIdentityOverPoint_projection :
    strictRawModuleTensorIdentityOverPoint A X P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (strictRawModuleTensorConePoint A X P) =
      strictRawModuleTensorConePoint A X P

def strictRawModuleTensorDoubleConeUnderOverSimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (strictRawModuleTensorIdentityOverPoint A X P)) _⦋n⦌
```

`ConstantClosedSimplex.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (M : ModuleCategory A D)

lemma moduleConstantClosedNerveSimplex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      ((Functor.const (Fin (n + 1))).obj M) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex
      (ForgetEnrichment.to (Complex A) M)).pullback (OrderHom.const _ (0 : Fin 1))

lemma moduleConstantClosedNerveSimplex_yoneda (n : ℕ) :
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A D))).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
        ((Functor.const (Fin (n + 1))).obj M)) =
    SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A D)).symm
      (ForgetEnrichment.to (Complex A) M))
```

`FrontComponentComparison.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleSimplexData_hom_heq_of_front_eq {m : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) (m + 1))
    (hfront : s.pullback Fin.castSuccOrderEmb.toOrderHom =
      t.pullback Fin.castSuccOrderEmb.toOrderHom)
    (I : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b ≠ Fin.last (m + 1)) :
    HEq (s.hom I a b k hI ha hb hk) (t.hom I a b k hI ha hb hk)
```


### 51.1 検証と実測

RawModuleTensorDoubleConeSliceTriangle の通常の対象ビルドは成功した。
新規二十一ファイルの公開宣言 43 本の依存公理監査も成功し、すべて
propext・Classical.choice・Quot.sound の範囲である。引用属性の新規追加はなく、
引用出力は 0 本。impl 鍵・待ち 3600 秒・gtimeout 280 秒の同じ一つの実行で
対象ビルドと小さい監査を行い、プロセスの終了値 0 を確認した。
root ビルドや大きい監査は実行していない。

新規 Lean は 21 ファイル・1,194 行・明示宣言 46 本（private 3 本）。
§50.1 の累計に加え、検証済み累計は 183 ファイル・14,556 行・
明示宣言 657 本（private 12 本）。現作業木の M15 所有ソースも再計数し、
同じ値と確認した。17,000 行の外枠まで残り 2,444 行。
今回、200 行を超える証明はない。一次 ID は追加していない。

元の全単体作用素の自然性、元の恒等閉辺との全一単体の一致、
同じ全 slice 図式・二重 join と全区間 prism の両端・射影・全元単体への制限、
普遍評価の元の全ホモトピーの実写像 h、その同じ評価族と元の cone 族の
全関手圏における合成三角形まで検証した。
端点と三角形の証明は一般の SSet における同じ既存の式へ分割し、
元の具体的な実 prism と端点・射影の法則を代入した。
実ホモトピー写像を別のものに取り替えず、200,000 heartbeat の既定上限も増やしていない。

生成操作の初回は、自動承認レビューが⑤aの既存ファイルの書換えと判定して拒否した。
処理は実行されていない。既存ファイルの差分ゼロを確認したうえで、
読み取り元と新規書込み先を分離し、存在しない新規 Modules ファイルだけを
出力先とする処理で作成した。作成の前後とコミット前に保護対象の差分ゼロを確認した。
既存の EInfinity Lean ファイルへの変更はない。

次は、同じ全 slice 評価族を元の通常 augmentation 円柱に全パラメータで照合し、
同じ元の導来源へ後合成する。元の全 augmentation 逆・評価屋根、
元の K の全 Hom 誘導射の同値性・完全忠実性、指定 fiber・native な辺と全族は
まだ未完である。M11 以降と G12 の元の目標、17,000 行の外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## §52 元の全 augmentation 円柱・同じ逆・実評価屋根との比較

元の全要素圏と Hom 持ち上げ先を、同じ宇宙の通常圏として使う。
同じ frame 図式に元の augmentation を後合成した通常余錐を構成し、
既存の通常余錐の有限列表示から、同じ終端を持つ元の加群の列を作る。
対象と全射は元の frame 射・augmentation の型移送付きの式へ回収する。
この列の閉単体と、§50 の同じ実二重 cone の末尾単体を全次数で照合した。

同じ通常余錐の全 join を元の dg 源へ送り、各標準単体への制限を同じ終端付き列へ
同定する。元の全 slice 図式を uncurry した写像は、この同じ通常余錐の join に等しい。
既存の通常余錐の全 prism 比較により、同じ指定された実分解 moduleResolution を
後合成した slice 評価の実写像 h は、元の通常 augmentation の全自然変換円柱の
実写像 h と一致する。全パラメータの等式を保ち、点ごとの射の類の一致に切り下げない。

この同じ全実写像の等式を、両端も記録する Arrow の一致へ移す。
§51 の同じ全三角形を同じ実分解へ後合成し、元の全 augmentation 同型の逆の一意性から、
元の cone 族の像を同じ augmentation 逆へ同定する。
元の cone の端点移送が実写像 h を保持する既存の式を使い、
strictRawModuleTensorConeSourceFamilyHom 自身の逆との Arrow 比較と同型性を導く。
同じ元の全評価を後合成し、元の全実屋根と定値端点へ移した同じ実屋根の Arrow 比較を行う。

これらは M10 の同じ既存構成の自然性・係数移送・合成・逆の法則と証明分割であり、
一次 ID は追加しない。元の K の全 Hom 誘導射との照合、その同値性・完全忠実性、
指定 fiber・native な辺と全族、および M11 以降と G12 は未完である。
対象ビルドと新規公開宣言の小さい監査は §52.1 のとおり成功した。

**一覧：済み 10／全体 43（うち追加 1）**。

`RawModuleTensorConeSourceInverse.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma postcompTriangle {K S T : SSet.{u + 1}} {U V : K ⟶ S}
    (F : S ⟶ T) (l : SSet.Homotopy U V) (r : SSet.Homotopy V U)
    (h : Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy r) = 𝟙 _) :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp l F)) ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp r F)) = 𝟙 _

private lemma inverseArrowEq {C : Type*} [Category* C] {x y x' y' : C}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] (h : Arrow.mk f = Arrow.mk g) :
    Arrow.mk (inv f) = Arrow.mk (inv g)

private lemma isIsoOfArrowEq {C : Type*} [Category* C] {x y x' y' : C}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso g] (h : Arrow.mk f = Arrow.mk g) : IsIso f

private lemma leftInverse_eq_inv {C : Type*} [Category* C] {x y : C}
    (c : x ⟶ y) (e : y ⟶ x) [IsIso e] (h : c ≫ e = 𝟙 x) : c = inv e

lemma strictRawModuleTensorDoubleConeSliceEvaluation_source_arrow :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp
        (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy A X P Q)
        (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)))))) =
    Arrow.mk (strictRawModuleTensorElementSourceAugmentationIso A X P Q).hom

lemma strictRawModuleTensorConePostSource_inverse_arrow :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp
        (strictRawModuleTensorConeHomotopy A X P Q)
        (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)))))) =
    Arrow.mk (strictRawModuleTensorElementSourceAugmentationIso A X P Q).inv

lemma strictRawModuleTensorConeSourceFamilyHom_inverse_arrow :
    Arrow.mk (strictRawModuleTensorConeSourceFamilyHom A X P Q) =
      Arrow.mk (strictRawModuleTensorElementSourceAugmentationIso A X P Q).inv

lemma strictRawModuleTensorConeSourceFamilyHom_isIso :
    IsIso (strictRawModuleTensorConeSourceFamilyHom A X P Q)
```

`RawModuleTensorConeSourceRoof.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma arrowPostcompEq {C : Type*} [Category* C] {x x' y z : C}
    (f : x ⟶ y) (g : x' ⟶ y) (h : Arrow.mk f = Arrow.mk g) (b : y ⟶ z) :
    Arrow.mk (f ≫ b) = Arrow.mk (g ≫ b)

private lemma arrowTransportEq {C : Type*} [Category* C] {x y x' y' : C}
    (hx : x = x') (hy : y = y') (f : x ⟶ y) :
    Arrow.mk (eqToHom hx.symm ≫ f ≫ eqToHom hy) = Arrow.mk f

lemma strictRawModuleTensorConeSourceEvaluation_arrow :
    Arrow.mk (strictRawModuleTensorConeSourceFamilyHom A X P Q ≫
      strictRawModuleTensorElementSourceEvaluation A X P Q) =
    Arrow.mk (strictRawModuleTensorElementSourceRoof A X P Q)

lemma strictRawModuleTensorElementSourceRoofFamily_arrow :
    Arrow.mk (strictRawModuleTensorElementSourceRoofFamily A X P Q) =
      Arrow.mk (strictRawModuleTensorElementSourceRoof A X P Q)

lemma strictRawModuleTensorConeSourceEvaluation_family_arrow :
    Arrow.mk (strictRawModuleTensorConeSourceFamilyHom A X P Q ≫
      strictRawModuleTensorElementSourceEvaluation A X P Q) =
    Arrow.mk (strictRawModuleTensorElementSourceRoofFamily A X P Q)
```

`RawModuleTensorDoubleConeAugmentationComparison.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeOverDiagram_uncurry :
    sliceOverUncurry (strictRawModuleTensorDoubleConeOverDiagram A X P Q) =
      strictRawModuleTensorElementAugmentationJoin A X P Q

lemma strictRawModuleTensorDoubleConeSliceEvaluationHomotopy_h_source :
    (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy A X P Q).h ≫
      moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)) =
    (strictRawModuleDiagramNatTransHomotopy A X
      (strictRawModuleTensorElementAugmentation A X P Q)).h
```

`RawModuleTensorDoubleConeOverColumn.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeOverDiagram_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    ((strictRawModuleTensorDoubleConeOverDiagram A X P Q).app (Opposite.op ⦋n⦌) c).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))))).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
          (strictRawModuleTensorElementAugmentedColumn A X P Q c))
```

`RawModuleTensorDoubleConeTailComparison.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeTail_eq_closed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorDoubleConeTail A X P Q c =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (strictRawModuleTensorElementAugmentedColumn A X P Q c)
```

`RawModuleTensorDoubleConeTailFront.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementAugmentedColumn_front {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    Fin.castSuccOrderEmb.toOrderHom.monotone.functor ⋙
      strictRawModuleTensorElementAugmentedColumn A X P Q c =
      c ⋙ strictRawModuleTensorElementDiagram A X P Q

lemma strictRawModuleTensorElementAugmentedColumn_closed_front {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      (strictRawModuleTensorElementAugmentedColumn A X P Q c)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q)

def strictRawModuleTensorDoubleConeTail {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 1)

lemma strictRawModuleTensorDoubleConeTail_front {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorDoubleConeTail A X P Q c).pullback Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q)
```

`RawModuleTensorDoubleConeTailTerminal.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeTail_hom_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    HEq ((strictRawModuleTensorDoubleConeTail A X P Q c).hom I a b k hI ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (A := A) (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) ((strictRawModuleTensorElementAugmentation A X P Q).app
        (c.obj ((Fin.last n).predAboveOrderHom a))) k)
```

`RawModuleTensorElementAugmentationJoin.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma ordinaryCoconeRestriction {I C : Type (u + 1)}
    [Category.{u + 1} I] [Category.{u + 1} C] {F : I ⥤ C}
    (c : CategoryTheory.Limits.Cocone F) {n : ℕ} (Γ : ComposableArrows I n)
    {T : SSet.{u + 1}} (G : nerve C ⟶ T) :
    joinMap (SSet.yonedaEquiv.symm Γ) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      ((nerveCoconeEquiv c).val ≫ G) =
      (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
        (G.app (Opposite.op ⦋n + 1⦌) (diagram c Γ))

def strictRawModuleTensorElementAugmentationJoin :
    join (nerve (strictRawModuleTensorElementIndex A X P Q)) (Δ[0] : SSet.{u + 1}) ⟶
      dgModuleNerve A (dgAlgebraCategory A ((assocForget A).obj X))

lemma strictRawModuleTensorElementAugmentationJoin_inr :
    joinInr (nerve (strictRawModuleTensorElementIndex A X P Q)) (Δ[0] : SSet.{u + 1}) ≫
      strictRawModuleTensorElementAugmentationJoin A X P Q = strictRawModuleTensorConePoint A X P

lemma strictRawModuleTensorElementAugmentationJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    joinMap (SSet.yonedaEquiv.symm c) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      strictRawModuleTensorElementAugmentationJoin A X P Q =
    (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
      (closedNerveSimplex (strictRawModuleTensorElementAugmentedColumn A X P Q c))

lemma strictRawModuleTensorElementAugmentationJoin_prism_source :
    (β_ (nerve (strictRawModuleTensorElementIndex A X P Q)) (Δ[1] : SSet.{u + 1})).hom ≫
      rightMappingSpacePrism _ ≫ strictRawModuleTensorElementAugmentationJoin A X P Q ≫
        moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)) =
      (strictRawModuleDiagramNatTransHomotopy A X
        (strictRawModuleTensorElementAugmentation A X P Q)).h
```

`RawModuleTensorElementAugmentedColumn.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementAugmentationCocone :
    Cocone (strictRawModuleTensorElementDiagram A X P Q ⋙
      ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X))

def strictRawModuleTensorElementAugmentedColumn {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    ComposableArrows (strictRawModuleCategory A X) (n + 1)

lemma strictRawModuleTensorElementAugmentedColumn_obj_castSucc {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 1)) :
    (strictRawModuleTensorElementAugmentedColumn A X P Q c).obj i.castSucc =
      (strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i)

lemma strictRawModuleTensorElementAugmentedColumn_obj_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorElementAugmentedColumn A X P Q c).obj (Fin.last (n + 1)) =
      (strictRawModuleProbeFunctor A X).obj P
```

`RawModuleTensorElementAugmentedColumnMaps.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma downMap_heq {C : Type (u + 1)} [Category.{u} C]
    {x y x' y' : ULiftHom.{u + 1} C} (hx : x = x') (hy : y = y')
    (f : x ⟶ y) (g : x' ⟶ y') (hf : HEq f g) :
    HEq (ULiftHom.down.{u, u + 1, u + 1}.map f)
      (ULiftHom.down.{u, u + 1, u + 1}.map g)

lemma strictRawModuleTensorElementAugmentedColumn_map_cast_cast {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    HEq ((strictRawModuleTensorElementAugmentedColumn A X P Q c).map
      (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij)))
      ((strictRawModuleTensorElementDiagram A X P Q).map (c.map (homOfLE hij)))

lemma strictRawModuleTensorElementAugmentedColumn_map_cast_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 1)) :
    HEq ((strictRawModuleTensorElementAugmentedColumn A X P Q c).map
      (homOfLE (Fin.le_last i.castSucc)))
      ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj i))
```

`RawModuleTensorElementAugmentedColumnTerminal.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma closedHom_heq {P Q P' Q' : ModuleCategory A (dgAlgebraCategory A ((assocForget A).obj X))} (hP : P = P') (hQ : Q = Q')
    (f : P ⟶ Q) (g : P' ⟶ Q') (hf : HEq f g) (k : ℤ) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (A := A) (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) f k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (A := A) (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) g k)

lemma strictRawModuleTensorElementAugmentedColumn_hom_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (strictRawModuleTensorElementAugmentedColumn A X P Q c)).hom I a b k hI ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (A := A) (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) ((strictRawModuleTensorElementAugmentation A X P Q).app
        (c.obj ((Fin.last n).predAboveOrderHom a))) k)
```


### 52.1 検証と実測

RawModuleTensorConeSourceRoof の通常の対象ビルドは成功した。
新規十一ファイルの公開宣言 27 本の依存公理監査も成功し、すべて
propext・Classical.choice・Quot.sound の範囲である。引用属性の新規追加はなく、
引用出力は 0 本。impl 鍵・待ち 3600 秒・gtimeout 280 秒の同じ一つの実行で
対象ビルドと小さい監査を行い、プロセスの終了値 0 を確認した。
root ビルドや大きい監査は実行していない。

新規 Lean は 11 ファイル・756 行・明示宣言 36 本（private 9 本）。
§51.1 の累計に加え、検証済み累計は 194 ファイル・15,312 行・
明示宣言 693 本（private 21 本）。現作業木の M15 所有ソースも再計数し、
同じ値と確認した。17,000 行の外枠まで残り 1,688 行。
今回、200 行を超える証明はない。一次 ID は追加していない。
既存 EInfinity Lean ファイルの変更もないことをコミット前に確認した。

同じ通常余錐の元の対象・全射、同じ終端付き列の閉単体と二重 cone の末尾面の
全 cochain の一致、同じ全余錐 join の標準単体への制限、全 slice 図式の uncurry の一致、
同じ元の指定導来源における slice 評価の実写像 h と通常 augmentation 円柱の
実写像 h の厳密な一致まで検証した。元の通常円柱を別の自己同型で置き換えていない。

さらに、元の全 augmentation 同型の順射への Arrow 比較、同じ全三角形の後合成、
逆の一意性による元の cone 族の augmentation 逆への Arrow 比較と同型性、
同じ元の評価を後合成した実屋根の Arrow 比較、同じ元の定値端点への移送まで検証した。
実写像の等式と全パラメータの構成を保持し、点ごとの射の類だけで代用していない。
名前空間・probe・Hom 持ち上げの宇宙を明示し、通常余錐の制限と三角形の後合成は
一般の既存法則へ証明を分割した。200,000 heartbeat の既定上限は増やしていない。

次は、この同じ元の実屋根を元の全 pinched 族・K の実 Hom 誘導射と照合する。
その同値性・完全忠実性、指定 fiber・native な辺と全族を含む M10 はまだ未完であり、
M11 以降と G12 の元の目標も未完である。17,000 行の外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## §53 元の全 pinched 族と全選択係数の評価

M10 の同じ元の加群 frame Hom の要素圏から、終端 augmentation と同じ二変数
Dold–Kan・pinched 同型を通る大域写像を作った。標準単体の恒等射での値は
元の frame 射そのものであり、その元の pinched 族の評価と厳密に一致する。
選択した最大点での cochain を元の評価で送ると、同じ大域 pinched 単体の
全有限部分集合・全整数次数の成分になる。符号を伴う斉次合成の式も照合した。
点の射の類や H⁰ の比較に置き換えていない。

加えて、元の Hom end の外延性により、加群の dg 単体データの各対象での評価が
全 HA 方程式を満たすなら元のデータも同じ方程式を満たすことを証明した。
これは M10 の既存の構成の評価法則・証明の分割であり、新しい一次 ID は足さない。
以下は今回の全宣言の型である。

`RawModuleTensorElementParameter.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementLiftMap : strictRawModuleTensorElementIndex A X P Q ⥤
    ULiftHom.{u + 1} (((((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q).Elements)ᵒᵖ)

def strictRawModuleTensorElementLiftNerveMap : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    nerve (ULiftHom.{u + 1} (((((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q).Elements)ᵒᵖ))

def strictRawModuleTensorElementParameterMap : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    SSet.uliftFunctor.{u + 1, u}.obj (((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q)

def strictRawModuleTensorPinchedIso :
    SSet.uliftFunctor.{u + 1, u}.obj (((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q) ≅
      PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
        (ForgetEnrichment.to (Complex A) Q)

def strictRawModuleTensorElementPinchedMap : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) Q)

lemma strictRawModuleTensorElementParameterMap_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorElementParameterMap A X P Q).app (op ⦋n⦌) c =
      ULift.up (((strictRawModuleProbeTensorFrame A X).obj P).map
        (strictRawModuleTensorElementTerminalParameter A X P Q c) ≫
          (strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))

lemma strictRawModuleTensorHomPinchedSimplex_id_eval (n : ℕ)
    (g : ((strictRawModuleProbeTensorFrame A X).obj P).obj ⦋n⦌ ⟶ Q) :
    (moduleTensorHomPinchedSimplex A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleProbeFunctor A X).obj P) Q ⦋n⦌ g).app (op ⦋n⦌)
      (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) =
      (strictRawModuleTensorPinchedIso A X P Q).hom.app (op ⦋n⦌) (ULift.up g)
```

`RawModuleTensorElementPinchedEvaluation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementPinchedMap_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorElementPinchedMap A X P Q).app (op ⦋n⦌) c =
    (pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n))))).app (op ⦋n⦌)
      (strictRawModuleTensorElementPinchedSimplex A X P Q c)
```

`RawModuleTensorSelectedEvaluation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementSelectedCochainAtMax_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (J.max' hJ)))).f k
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) =
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))).f k
      ((strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk)

lemma strictRawModuleTensorElementLinear_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (E := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (x := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (x' := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n))))
      (strictRawModuleTensorElementLinear A X P Q c) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((strictRawModuleTensorElementPinchedMap A X P Q).app (Opposite.op ⦋n⦌) c)

lemma strictRawModuleTensorElementSelectedCochainAtMax_evaluation_pinched {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (J.max' hJ)))).f k
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      ((strictRawModuleTensorElementPinchedMap A X P Q).app (Opposite.op ⦋n⦌) c)).val.component
        J k hJ hk

lemma strictRawModuleTensorElementSelectedCochainAtMax_evaluation_compose {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℤˣ) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (J.max' hJ)))).val
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) (add_zero k) =
    r • (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      ((strictRawModuleTensorElementPinchedMap A X P Q).app (Opposite.op ⦋n⦌) c)).val.component
        J k hJ hk
```

`SimplexEquationEvaluation.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleSimplexData_equation_of_evaluation {n : ℕ}
    (s : SimplexData A (RightModule A D) n) (I : Finset (Fin (n + 1)))
    (h : ∀ x : D, (s.map (moduleEvaluationDG A D x)).Equation I) : s.Equation I
```


### 53.1 検証と実測

RawModuleTensorSelectedEvaluation と SimplexEquationEvaluation の対象ビルドは成功した
（終了値 0）。新規公開宣言 13 本の小さい依存公理監査も終了値 0 で成功し、
依存公理は propext・Classical.choice・Quot.sound のみ。新規引用属性はなく、
引用出力は 0 本。いずれも impl 鍵・待ち 3600 秒・gtimeout 280 秒で実行した。
大きい監査や root ビルドはしていない。

新規 Lean は 4 ファイル・244 行・明示宣言 13 本（private 0 本）。
所有ソースの累計は 198 ファイル・15,556 行・明示宣言 706 本（private 21 本）。
17,000 行の外枠まで残り 1,444 行。200 行を超える証明はなく、一次 ID の追加はない。
既存 EInfinity ソースの変更はない。既定 heartbeat 上限も増やしていない。

この評価式だけでは元の三相全三角形と K の実 Hom 誘導射の比較は完了しない。
M10 の完全忠実性・指定 fiber・native な辺と全族、M11 以降および G12 は未完である。
次は同じ全三相データの評価比較を進める。外枠は維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## §54 同じ加群対象族上の全単体の評価による外延性

§53 の全 HA 方程式の反映に続き、同じ加群対象族上の全単体データの等式を
各対象での評価から戻す法則を作った。元の加群対象族の等式を明示的な入力とする。
評価先の複体だけから加群の作用を同定する仮定は置かない。対象の同一視の後に、
元の Hom end の各斉次成分に外延性を適用する。実 dg 単体についても同じ法則を束ねた。
これらは M10 の評価・貼り合わせの証明の分割であり、一次 ID は増やさない。

`SimplexEvaluationExt.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleSimplexData_ext_of_evaluation {n : ℕ}
    (s t : SimplexData A (RightModule A D) n) (ho : s.obj = t.obj)
    (h : ∀ x : D, s.map (moduleEvaluationDG A D x) =
      t.map (moduleEvaluationDG A D x)) : s = t

lemma moduleSimplex_ext_of_evaluation {n : ℕ}
    (s t : Simplex A (RightModule A D) n) (ho : s.obj = t.obj)
    (h : ∀ x : D, s.toSimplexData.map (moduleEvaluationDG A D x) =
      t.toSimplexData.map (moduleEvaluationDG A D x)) : s = t
```


### 54.1 検証と実測

SimplexEvaluationExt の対象ビルドは終了値 0 で成功した。
新規公開宣言二本の小さい監査も終了値 0 で成功し、依存公理は
propext・Classical.choice・Quot.sound の範囲。引用属性の追加はなく引用出力は 0 本。
いずれも impl 鍵・待ち 3600 秒・gtimeout 280 秒の対象だけの実行である。
大きい監査や root ビルドは行っていない。

新規 Lean は一ファイル・52 行・明示宣言二本（private 0 本）。
所有ソースを再計数した累計は 199 ファイル・15,608 行・明示宣言 708 本
（private 21 本）。外枠 17,000 行まで残り 1,392 行。
200 行を超える証明や一次 ID の追加はない。既存 EInfinity ソースの変更もない。

全評価から全 cochain の等式と HA 方程式を戻す道具は通ったが、
元の三相データの全評価比較自体はまだ残る。M10、M11 以降、G12 は未完である。
次は元の frame 評価と既存の複体側の同じ三相データを比較する。

**一覧：済み 10／全体 43（うち追加 1）**。


## §55 全 frame Hom と全要素図式の評価

M10 の元の全加群 frame Hom から各対象での複体の全 frame Hom への写像を作り、
同じ Dold–Kan 同型と主 Hom end の評価との可換性を証明した。
複体側の frame は P(x)⊗N(Δⁿ)、加群 frame の評価は N(Δⁿ)⊗P(x) であるため、
両者を定義上等しいとは扱わない。転置の比較から、全単体での実射が
符号付き交換の後に元の加群射を評価した射に一致することを証明した。
その符号付き交換を全作用素に自然な frame 同型へ束ねた。

同じ全 Hom 評価に要素圏関手を作用させ、元の加群の全要素図式を複体の全要素図式へ
送った。次数射影に同じ frame 同型を前合成した全図式の自然同型と、
同じ元の二つの評価自然変換を結ぶ厳密な可換式を証明した。
評価後の定値関手の同定も元の constComp 同型で明示する。
いずれも既存の構成の評価・係数移送・自然性の法則であり、一次 ID の追加はない。

`RawModuleTensorElementEvaluationIndex.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementEvaluationIndex
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    strictRawModuleTensorElementIndex A X P Q ⥤
      normalizedTensorElementIndex A
        ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
        ((moduleEvaluation A _ x).obj Q)

def strictRawModuleTensorElementEvaluationDiagramIso
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    strictRawModuleTensorElementEvaluationIndex A X P Q x ⋙
      normalizedTensorElementDiagram A
        ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
        ((moduleEvaluation A _ x).obj Q) ≅
      strictRawModuleTensorElementDiagram A X P Q ⋙ moduleEvaluation A _ x

lemma strictRawModuleTensorElementEvaluationDiagramIso_evaluation
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    (strictRawModuleTensorElementEvaluationDiagramIso A X P Q x).hom ≫
      CategoryTheory.Functor.whiskerRight
        (strictRawModuleTensorElementEvaluation A X P Q) (moduleEvaluation A _ x) ≫
      (Functor.constComp (strictRawModuleTensorElementIndex A X P Q) Q
        (moduleEvaluation A _ x)).hom =
      CategoryTheory.Functor.whiskerLeft
        (strictRawModuleTensorElementEvaluationIndex A X P Q x)
        (normalizedTensorElementEvaluation A
          ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
          ((moduleEvaluation A _ x).obj Q))
```

`TensorFrameEvaluation.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleTensorEvaluationFrameIso (P : ModuleCategory A D) (x : D) :
    normalizedSimplexTensor A ((moduleEvaluation A D x).obj P) ≅
      ((moduleTensorSimplicesFunctor A D).obj P) ⋙ moduleEvaluation A D x

lemma moduleTensorEvaluationHomMap_frame (P Q : ModuleCategory A D) (x : D)
    (n : SimplexCategory)
    (f : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ Q) :
    (moduleTensorEvaluationHomMap A D P Q x).app (op n) f =
      (moduleTensorEvaluationFrameIso A D P x).hom.app n ≫
        (moduleEvaluation A D x).map f
```

`TensorHomEvaluation.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleTensorEvaluationHomMap (P Q : ModuleCategory A D) (x : D) :
    (cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P)).obj Q ⟶
      (cosimplicialHom (normalizedSimplexTensor A ((moduleEvaluation A D x).obj P))).obj
        ((moduleEvaluation A D x).obj Q)

lemma moduleTensorHomDoldKanIso_evaluation (P Q : ModuleCategory A D) (x : D) :
    (moduleTensorHomDoldKanIso A D P Q).hom ≫
      (truncatedDoldKanFunctor A).map
        (moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
          (ForgetEnrichment.to (Complex A) Q) x) =
      moduleTensorEvaluationHomMap A D P Q x ≫
        (normalizedSimplexTensorHomIso A ((moduleEvaluation A D x).obj P)
          ((moduleEvaluation A D x).obj Q)).hom

lemma moduleTensorEvaluationHomMap_transpose (P Q : ModuleCategory A D) (x : D)
    (n : SimplexCategory)
    (f : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ Q) :
    normalizedSimplexTensorHomEquiv A ((moduleEvaluation A D x).obj P)
      ((moduleEvaluation A D x).obj Q) n
      ((moduleTensorEvaluationHomMap A D P Q x).app (op n) f) =
    normalizedSimplexHomEquiv A _ n (curryRight ((moduleEvaluation A D x).map f))
```

`TensorHomEvaluationValue.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleTensorEvaluationHomMap_app (P Q : ModuleCategory A D) (x : D)
    (n : SimplexCategory)
    (f : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ Q) :
    (moduleTensorEvaluationHomMap A D P Q x).app (op n) f =
      (signedSwap ((moduleEvaluation A D x).obj P)
        ((BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n))).hom ≫
          (moduleEvaluation A D x).map f
```


### 55.1 検証と実測

TensorHomEvaluationValue、TensorFrameEvaluation、RawModuleTensorElementEvaluationIndex の
対象ビルドは終了値 0 で成功した。新規公開宣言九本は四本・二本・三本の小さい監査に分け、
いずれも終了値 0。依存公理は propext・Classical.choice・Quot.sound のみで、
新規引用属性・引用出力は 0 本。すべて impl 鍵・待ち 3600 秒・gtimeout 280 秒で実行した。
root ビルドや大きい監査、heartbeat 上限の変更はしていない。

今回の検証済み Lean は四ファイル・233 行・明示宣言九本（private 0 本）。
§54.1 に加え、検証済み累計は 203 ファイル・15,841 行・明示宣言 717 本
（private 21 本）。外枠まで残り 1,159 行。
200 行を超える証明や一次 ID の追加はない。既存 EInfinity ソースは変更していない。

次の augmentation 評価法則を TensorFrameAugmentationEvaluation.lean の新規下書きとして
実装中であり、この検証済み累計にはまだ含めていない。下書きは 37 行で、
現作業木全体は 15,878 行、外枠まで残り 1,122 行である。

元の全要素圏と実評価射の比較は通ったが、元の全三相単体・三角形と K の実 Hom 射の
比較は未完である。複体側の triangle 系列の実測は 40 ファイル・2,541 行であり、
単純移植では残りの外枠に入らない。評価による再利用を進めているが、未証明の比較を
仮定にして済ませない。M10・M11 以降・G12 は未完、外枠 17,000 行は維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## §56 同じ符号付き frame 同型を通した元の augmentation の評価

同じ全 frame 同型の後に元の加群 augmentation を評価した射は、
元の AW 余単位を右因子にテンソルし、元の右単位子を合成した射に一致する。
元の AW 余単位の評価式、符号付き交換の自然性と単位子の法則を使う。
別の augmentation で置き換えた等式にはしない。

これは既存構成の係数移送・貼り合わせの法則であり、一次 ID は追加しない。
複体側の normalizedSimplexCochainContraction の順射との一致はまだこの主張には含めない。
その照合を済ませてから、既存の複体の三角形の再利用へ進む。

`TensorFrameAugmentationEvaluation.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleTensorEvaluationFrameIso_augmentation (P : ModuleCategory A D) (x : D)
    (n : SimplexCategory) :
    (moduleTensorEvaluationFrameIso A D P x).hom.app n ≫
      (moduleEvaluation A D x).map ((moduleTensorSimplicesAugmentation A D P).app n) =
    (𝟙 ((moduleEvaluation A D x).obj P) ⊗ₘ
      AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n)) ≫
        (ρ_ ((moduleEvaluation A D x).obj P)).hom
```


### 56.1 検証と実測

TensorFrameAugmentationEvaluation の対象ビルドと新規公開宣言一本の小さい依存公理監査は、
同じ impl 鍵・待ち 3600 秒・gtimeout 280 秒の実行で終了値 0。
依存公理は propext・Classical.choice・Quot.sound の範囲であり、
新規引用属性・引用出力は 0 本。大きい監査・root ビルド・heartbeat の変更はない。

新規 Lean は一ファイル・37 行・明示宣言一本（private 0 本）。
§55.1 の下書きは検証済みとなり、所有ソース全体を再計数した累計は
204 ファイル・15,878 行・明示宣言 718 本（private 21 本）。
外枠 17,000 行まで残り 1,122 行。200 行を超える証明や一次 ID の追加はない。
既存 EInfinity ソースの変更もない。

元の augmentation の評価の等式は通ったが、複体の指定収縮の順射との比較と
全三相単体の比較はまだ残る。M10・M11 以降・G12 は未完であり、目標を縮めない。

**一覧：済み 10／全体 43（うち追加 1）**。


## §57 指定収縮と元の AW 余単位、全要素屋根の左脚の一致

複体側の指定された単体鎖収縮の順射は、元の AW augmentation と厳密に一致する。
single₀ への鎖写像を零次で比較し、全頂点に対する値を使った。
具体的には、P∞ の次数零は恒等であり、正規化生成元を Moore 包含で送ると
元の自由生成元になる。その後の追加退化の augmentation と一点上の自由加群の同型は
その生成元を 1 に送る。指定された実射を別のホモトピー同値に置き換えていない。

同じ等式を元の次数延長と single の同型に沿って送り、指定コチェイン収縮の順射も
元の AW コチェイン余単位に一致することを証明した。これを §56 の評価式に合成し、
元の加群 frame augmentation と複体側の指定 augmentation が、
同じ符号付き frame 同型を通して可換になることを示した。
さらに元の全要素図式の同型を通して、元の augmentation 自然変換の可換式を束ねた。
§55 の評価自然変換の可換式と合わせ、同じ元の全評価屋根の両脚の比較が通った。

これらは同じ構成の係数移送・自然性・貼り合わせの法則であり、一次 ID の追加はない。
以下は今回の全宣言の型である。

`RawModuleTensorElementAugmentationEvaluation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementEvaluationDiagramIso_augmentation
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    (strictRawModuleTensorElementEvaluationDiagramIso A X P Q x).hom ≫
      CategoryTheory.Functor.whiskerRight
        (strictRawModuleTensorElementAugmentation A X P Q) (moduleEvaluation A _ x) ≫
      (Functor.constComp (strictRawModuleTensorElementIndex A X P Q)
        ((strictRawModuleProbeFunctor A X).obj P) (moduleEvaluation A _ x)).hom =
      CategoryTheory.Functor.whiskerLeft
        (strictRawModuleTensorElementEvaluationIndex A X P Q x)
        (normalizedTensorElementAugmentation A
          ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
          ((moduleEvaluation A _ x).obj Q))
```

`NormalizedAugmentationComparison.lean`：

```lean
variable (A : Type u) [CommRing A]

lemma normalizedSimplexChainContraction_hom_counit (n : SimplexCategory) :
    (normalizedSimplexChainContraction A n).hom = counit A (SSet.stdSimplex.obj n)

lemma normalizedSimplexCochainContraction_hom_counit (n : SimplexCategory) :
    (normalizedSimplexCochainContraction A n).hom =
      cochainCounit A (SSet.stdSimplex.obj n)
```

`TensorFrameOriginalAugmentation.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleTensorEvaluationFrameIso_original_augmentation (P : ModuleCategory A D) (x : D)
    (n : SimplexCategory) :
    (moduleTensorEvaluationFrameIso A D P x).hom.app n ≫
      (moduleEvaluation A D x).map ((moduleTensorSimplicesAugmentation A D P).app n) =
    (normalizedSimplexTensorAugmentation A ((moduleEvaluation A D x).obj P)).app n
```


### 57.1 検証と実測

NormalizedAugmentationComparison と RawModuleTensorElementAugmentationEvaluation の
対象ビルドは終了値 0 で成功した。新規公開宣言四本は二本ずつの小さい監査に分け、
いずれも終了値 0。依存公理は propext・Classical.choice・Quot.sound の範囲であり、
新規引用属性・引用出力は 0 本。すべて impl 鍵・待ち 3600 秒・gtimeout 280 秒で行った。
root ビルド・大きい監査・heartbeat の上限変更はない。

新規 Lean は三ファイル・149 行・明示宣言四本（private 0 本）。
所有ソース全体を再計数した累計は 207 ファイル・16,027 行・明示宣言 722 本
（private 21 本）。外枠 17,000 行まで残り 973 行。
200 行を超える証明や一次 ID の追加、既存 EInfinity ソースの変更はない。

次の全単体比較で必要な閉零同型による対象表示の移送は、既存の
DifferentialGraded/Functor/DGClosedIsoConjugation.lean の dgFunctorClosedConjugate と
DifferentialGraded/Functor/Closed.lean の inducedDGFunctorClosedConjugate が
全 Hom 複体・単位・合成を保持して実装していることを確認した。
この既存の部品の利用を先に調べ、全三相データの比較へ進む。

今回、同じ元の全屋根の両脚を比較したが、全三相単体・三角形の一致と
K の実 Hom 誘導射の完全忠実性はまだ証明していない。
M10・M11 以降・G12 は未完であり、外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## §58 元の全単体の閉零同型による対象表示の移送

M10 の三相単体の評価に必要な対象表示の移送は、既存の inducedDGCategory・
inducedDGEvaluation と dgFunctorClosedConjugate を使って構成した。
元の単体を頂点番号のラベル上へ移し、同じ全 Hom 複体に対する既存の共役 dg 関手で送る。
頂点番号から元の対象への写像の単射性を仮定しない。
移送した実単体の全 HA 方程式は既存の dg 関手による単体の像の構成で保持する。
全 cochain の値は、元の二つの閉零同型による全 Hom 複体の前後合成と一致する。

これは既存構成の対象表示・係数移送の法則であり、新しい一次 ID は追加しない。
全三相データの評価比較自体を仮定した構成でも、H⁰ の同型での移送でもない。

`SimplexClosedTransport.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

def simplexVertexLabels {n : ℕ} (s : Simplex A D n) :
    letI := inducedDGCategory A s.obj
    Simplex A (Fin (n + 1)) n

def simplexClosedTransport {n : ℕ} (s : Simplex A D n) (b : Fin (n + 1) → D)
    (e : ∀ i, ForgetEnrichment.of (Complex A) (s.obj i) ≅
      ForgetEnrichment.of (Complex A) (b i)) : Simplex A D n

lemma simplexClosedTransport_obj {n : ℕ} (s : Simplex A D n)
    (b : Fin (n + 1) → D)
    (e : ∀ i, ForgetEnrichment.of (Complex A) (s.obj i) ≅
      ForgetEnrichment.of (Complex A) (b i)) (i : Fin (n + 1)) :
    (simplexClosedTransport A D s b e).obj i = b i

lemma simplexClosedTransport_hom {n : ℕ} (s : Simplex A D n)
    (b : Fin (n + 1) → D)
    (e : ∀ i, ForgetEnrichment.of (Complex A) (s.obj i) ≅
      ForgetEnrichment.of (Complex A) (b i))
    (I : Finset (Fin (n + 1))) (a c : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hc : c = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (simplexClosedTransport A D s b e).hom I a c k hI ha hc hk =
      (enrichedClosedIsoConjugation (Complex A) (e a) (e c)).f k
        (s.hom I a c k hI ha hc hk)
```

### 58.1 検証と実測

SimplexClosedTransport の対象ビルドと新規公開宣言四本の小さい監査は、
同じ impl 鍵・待ち 3600 秒・gtimeout 280 秒で終了値 0。
依存公理は propext・Classical.choice・Quot.sound のみ。新規引用属性・引用出力は 0 本。
root ビルド・大きい監査・heartbeat 上限の変更はない。

新規 Lean は一ファイル・70 行・明示宣言四本（private 0 本）。
検証済み累計は 208 ファイル・16,097 行・明示宣言 726 本（private 21 本）。
17,000 行の外枠まで残り 903 行。200 行を超える証明や一次 ID の追加はなく、
既存 EInfinity ソースも変更していない。

次は同じ三相データの対象・実 cochain を作り、この対象表示の移送を全評価で使う。
全三角形・K の実 Hom 誘導射の完全忠実性、M10・M11 以降・G12 はまだ未完である。

**一覧：済み 10／全体 43（うち追加 1）**。


## §59 元の評価列と実三相単体データ

同じ元の評価自然変換を通常余錐にし、元の各全単体列に終端 Q を付けた評価列を作った。
そこからの通常閉 nerve 単体、元の実 cone 単体と元の大域 pinched 単体を、
同じ三相時刻で引き戻した。各相が対象族と一致する等式を使い、同じ元の全 cochain を
貼り合わせた実 SimplexData を作った。全有限部分集合・任意整数次数を保持し、
端点の等式による cast を明示する。

これは M10 の既存の全三角形の貼り合わせの一段であり、一次 ID は足さない。
貼り合わせたデータの HA 方程式はまだ未証明であり、Simplex として出力していない。
各三部品が実単体であることだけから、貼り合わせたデータも単体だとは主張しない。

`RawModuleTensorElementEvaluatedColumn.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementEvaluationCocone :
    Cocone (strictRawModuleTensorElementDiagram A X P Q ⋙
      ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X))

def strictRawModuleTensorElementEvaluatedColumn {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    ComposableArrows (strictRawModuleCategory A X) (n + 1)

lemma strictRawModuleTensorElementEvaluatedColumn_obj_castSucc {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 1)) :
    (strictRawModuleTensorElementEvaluatedColumn A X P Q c).obj i.castSucc =
      (strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i)

lemma strictRawModuleTensorElementEvaluatedColumn_obj_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorElementEvaluatedColumn A X P Q c).obj (Fin.last (n + 1)) =
      Q
```

`RawModuleTensorTriangleData.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorTriangleData {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) n
```

`RawModuleTensorTrianglePieces.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorTriangleObj {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) : RightModule A (dgAlgebraCategory A ((assocForget A).obj X))

def strictRawModuleTensorTriangleFront {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) n

def strictRawModuleTensorTriangleBack {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) n

def strictRawModuleTensorTrianglePinched {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) n

lemma strictRawModuleTensorTriangleFront_obj {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i ≠ 2) :
    (strictRawModuleTensorTriangleFront A X P Q c τ).obj i =
      strictRawModuleTensorTriangleObj A X P Q c τ i

lemma strictRawModuleTensorTriangleBack_obj {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i ≠ 0) :
    (strictRawModuleTensorTriangleBack A X P Q c τ).obj i =
      strictRawModuleTensorTriangleObj A X P Q c τ i

lemma strictRawModuleTensorTrianglePinched_obj_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i = 0) :
    (strictRawModuleTensorTrianglePinched A X P Q c τ).obj i =
      strictRawModuleTensorTriangleObj A X P Q c τ i

lemma strictRawModuleTensorTrianglePinched_obj_two {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i = 2) :
    (strictRawModuleTensorTrianglePinched A X P Q c τ).obj i =
      strictRawModuleTensorTriangleObj A X P Q c τ i
```

### 59.1 検証と実測

RawModuleTensorTrianglePieces と RawModuleTensorTriangleData の対象ビルド、および新規公開宣言
13 本の小さい監査は終了値 0 で成功した。依存公理は propext・Classical.choice・Quot.sound
の範囲。新規引用属性・引用出力は 0 本。impl 鍵・待ち 3600 秒・gtimeout 280 秒を使った。
大きい監査・root ビルド・heartbeat 上限の変更はない。

新規検証済み Lean は三ファイル・199 行・明示宣言 13 本（private 0 本）。
検証済み累計は 211 ファイル・16,296 行・明示宣言 739 本（private 21 本）。
外枠 17,000 行まで残り 704 行。200 行を超える証明や一次 ID の追加はない。
既存の EInfinity ソース（参照した複体側のファイルも含む）は変更していない。

次の対象評価比較 RawModuleTensorTriangleEvaluationObjects.lean は 51 行の新規下書きで、
現作業木の所有ソース全体は 16,347 行、外枠まで残り 653 行。

次は同じ実三相データの全評価比較と HA 方程式を進める。
M10・M11 以降・G12 はまだ未完であり、外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## §60 同じ三相対象の全評価と複体側の実単体の表示移送

元の三相加群対象の各対象での評価と、複体側の指定された三相対象を結ぶ閉零同型を
作った。元の全列・全三相時刻・全頂点で定義し、両端には恒等、中央には §55 の
同じ符号付き frame 同型を使う。別の中間対象・同値を選び直さない。

この同じ対象同型で、既存の複体側の指定された実三相単体全体を表示移送した。
§58 の全単体の移送を使うため、全有限部分集合・全整数次数の cochain と全 HA 方程式を
保持している。これは既存構成の係数移送であり、一次 ID は追加しない。

この移送した実単体が、元の加群の三相データを評価したデータと一致することは、
まだ証明していない。その等式を前提として加えたり、元の加群側の HA 方程式が
済んだと扱ったりしない。以下は今回の全宣言の型。

`RawModuleTensorTriangleEvaluationObjects.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorTriangleEvaluationObjIso {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3)
    (x : dgAlgebraCategory A ((assocForget A).obj X)) (i : Fin (n + 1)) :
    (complexToClosed A).obj (normalizedTensorTriangleObj A
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q)
      (c ⋙ strictRawModuleTensorElementEvaluationIndex A X P Q x) τ i) ≅
    (complexToClosed A).obj ((moduleEvaluationDG A _ x).obj
      (strictRawModuleTensorTriangleObj A X P Q c τ i))
```

`RawModuleTensorTriangleEvaluationReference.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorTriangleEvaluationReference {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3)
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex
      A (Complex A) n
```


### 60.1 検証と実測

RawModuleTensorTriangleEvaluationObjects と RawModuleTensorTriangleEvaluationReference の
対象ビルドは終了値 0 で成功した。新規公開宣言二本の小さい監査も終了値 0。
依存公理は propext・Classical.choice・Quot.sound のみで、引用属性の新規追加・引用出力は 0 本。
impl 鍵・待ち 3600 秒・gtimeout 280 秒で対象だけを実行した。
大きい監査・root ビルド・heartbeat の上限変更はない。

新規 Lean は二ファイル・90 行・明示宣言二本（private 0 本）。
所有ソース全体を再計数した累計は 213 ファイル・16,386 行・明示宣言 741 本
（private 21 本）。外枠 17,000 行まで残り 614 行。
§59.1 の対象評価比較の下書きも検証済みになった。
200 行を超える証明や一次 ID の追加、既存 EInfinity ソースの変更はない。

複体側の実単体を元の評価対象の表示へ戻す全構成まで通ったが、
元の加群側三相データの全評価 cochain との等式は未証明である。
元の加群側の全 HA 方程式、全三角形・K の実 Hom 誘導射の比較を未完として残す。
M10・M11 以降・G12 の元の目標は維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## §61 元の全終端パラメータ族・大域 pinched 族の実評価

同じ全 frame Hom の評価と、元の Dold–Kan・pinched 座標の可換式を証明した。
元の主 Hom end の評価鎖写像に、既存の任意 Hom 鎖写像への自然性を適用する。
BE の底の対象型は Type 0 なので、元の全加群 dg 圏と複体 dg 圏の宇宙表示を
同じ u+1 に保った。係数環・実 Hom 鎖写像の端点を明示する。

元の全要素圏の評価関手を同じ全 nerve の写像にし、元の全終端パラメータ族と
全 Hom 評価が可換であることを証明した。元の終端作用素における自然性の式を
元の最終評価射で評価する。全自然変換の等式であり、点ごとの射の類の比較ではない。

これらを合成し、元の大域 pinched 族を主 Hom end で評価すると、同じ評価要素圏関手を
通した複体側の元の大域 pinched 族に厳密に一致することを証明した。
全パラメータ・全次数・全作用素を保持する。三相データの pinched 成分の比較に使う。
既存構成の評価・自然性・貼り合わせの法則であり、一次 ID は追加しない。

具体的な評価自然変換の自然性証明の展開が既定 heartbeat に達したため、
同じ式を任意の単体集合の自然変換についての private 補題へ分割した。
診断用の一時ログは除去済みであり、上限を増やしていない。
以下は private の証明分割も含む今回の全宣言の型である。

`RawModuleTensorElementParameterEvaluation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorEvaluationHomMap
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    (((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q) ⟶
      (cosimplicialHom (normalizedSimplexTensor A
        ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P)))).obj
        ((moduleEvaluation A _ x).obj Q)

def strictRawModuleTensorElementEvaluationIndexNerveMap
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
      nerve (normalizedTensorElementIndex A
        ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
        ((moduleEvaluation A _ x).obj Q))

private lemma sset_naturality_apply {F G : SSet.{u}} (α : F ⟶ G)
    {n m : SimplexCategory} (θ : n ⟶ m) (g : F.obj (op m)) :
    α.app (op n) (F.map θ.op g) = G.map θ.op (α.app (op m) g)

lemma strictRawModuleTensorElementParameterMap_evaluation
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    strictRawModuleTensorElementParameterMap A X P Q ≫
      SSet.uliftFunctor.{u + 1, u}.map
        (strictRawModuleTensorEvaluationHomMap A X P Q x) =
    strictRawModuleTensorElementEvaluationIndexNerveMap A X P Q x ≫
      normalizedTensorElementParameterMap A
        ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
        ((moduleEvaluation A _ x).obj Q)
```

`RawModuleTensorElementPinchedEvaluationMap.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementPinchedMap_evaluation
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    strictRawModuleTensorElementPinchedMap A X P Q ≫
      pinchedHomChainMap (moduleHomπ A _
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
        (ForgetEnrichment.to (Complex A) Q) x) =
    strictRawModuleTensorElementEvaluationIndexNerveMap A X P Q x ≫
      normalizedTensorElementPinchedMap A
        ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
        ((moduleEvaluation A _ x).obj Q)
```

`TensorPinchedEvaluation.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type) [DGCategory A D] [Small.{u} D]

lemma moduleTensorHomPinchedIso_evaluation (P Q : ModuleCategory A D) (x : D) :
    SSet.uliftFunctor.{u + 1, u}.map (moduleTensorEvaluationHomMap A D P Q x) ≫
      (normalizedTensorPinchedIso A ((moduleEvaluation A D x).obj P)
        ((moduleEvaluation A D x).obj Q)).hom =
    SSet.uliftFunctor.{u + 1, u}.map (moduleTensorHomDoldKanIso A D P Q).hom ≫
      (moduleDoldKanPinchedIso A D P Q).hom ≫
        pinchedHomChainMap (moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
          (ForgetEnrichment.to (Complex A) Q) x)
```


### 61.1 検証と実測

TensorPinchedEvaluation と RawModuleTensorElementPinchedEvaluationMap の対象ビルドは
終了値 0 で成功した。新規公開宣言五本の小さい監査も終了値 0。
依存公理は propext・Classical.choice・Quot.sound のみで、引用属性の新規追加・引用出力は 0 本。
impl 鍵・待ち 3600 秒・gtimeout 280 秒で対象だけを実行した。
root ビルド・大きい監査・heartbeat 上限の変更はない。

新規 Lean は三ファイル・180 行・明示宣言六本（private 一本）。
所有ソース全体を再計数した累計は 216 ファイル・16,566 行・明示宣言 747 本
（private 22 本）。17,000 行の外枠まで残り 434 行。
200 行を超える証明や一次 ID の追加はなく、既存 EInfinity ソースの変更もない。

元の大域 pinched 族の評価は全写像として通ったが、元の三相データ全体の評価の一致は
未証明である。cone 成分の係数移送と前後の同型の比較、全三角形の自然性と
K の実 Hom 誘導射の完全忠実性もまだ残る。
M10・M11 以降・G12 は未完であり、目標と外枠を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## §62 元の実 pinched 単体と三相 pinched 分岐の全評価

§61 の元の大域族の等式を各全単体列で評価し、元の実 pinched 単体の等式と、
同じ全線形表示の等式を回収した。全線形表示は全有限部分集合・全整数次数の
係数の族であり、零次元・H⁰ の比較には落としていない。

さらに既存の dgFunctorPinchedChainMap_val を使い、元の Hom 鎖写像で送った実単体の値が
同じ dg 評価関手で送った元の実単体に一致することを回収した。
同じ三相の単調作用素の引き戻し自然性を合成し、三相 pinched 分岐の全データの
dg 評価は複体側の同じ指定分岐の全データに厳密に一致することを証明した。
退化を含む全単調作用素と全 cochain を保持する。
既存構成の評価・係数移送・自然性の法則であり、一次 ID は追加しない。

`RawModuleTensorElementPinchedEvaluationValues.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementPinchedMap_evaluation_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    pinchedHomChainMapSimplex (moduleHomπ A _
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) Q) x)
      ((strictRawModuleTensorElementPinchedMap A X P Q).app (op ⦋n⦌) c) =
    (normalizedTensorElementPinchedMap A
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q)).app (op ⦋n⦌)
      (c ⋙ strictRawModuleTensorElementEvaluationIndex A X P Q x)

lemma strictRawModuleTensorElementPinchedMap_linear_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    pinchedLinearSimplexMap (moduleHomπ A _
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) Q) x)
      (PinchedHom.toLinearSimplex
        ((strictRawModuleTensorElementPinchedMap A X P Q).app (op ⦋n⦌) c)) =
    PinchedHom.toLinearSimplex ((normalizedTensorElementPinchedMap A
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q)).app (op ⦋n⦌)
      (c ⋙ strictRawModuleTensorElementEvaluationIndex A X P Q x))
```

`RawModuleTensorTrianglePinchedEvaluation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementPinchedMap_simplex_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    ((strictRawModuleTensorElementPinchedMap A X P Q).app (op ⦋n⦌) c).val.map
      (moduleEvaluationDG A _ x) =
    ((normalizedTensorElementPinchedMap A
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q)).app (op ⦋n⦌)
      (c ⋙ strictRawModuleTensorElementEvaluationIndex A X P Q x)).val

lemma strictRawModuleTensorTrianglePinched_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3)
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    (strictRawModuleTensorTrianglePinched A X P Q c τ).toSimplexData.map
      (moduleEvaluationDG A _ x) =
    (normalizedTensorTrianglePinched A
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q)
      (c ⋙ strictRawModuleTensorElementEvaluationIndex A X P Q x) τ).toSimplexData
```


### 62.1 検証と実測

RawModuleTensorElementPinchedEvaluationValues と RawModuleTensorTrianglePinchedEvaluation の
対象ビルドは終了値 0 で成功した。新規公開宣言四本の小さい監査も終了値 0。
依存公理は propext・Classical.choice・Quot.sound の範囲で、引用属性の新規追加・引用出力は 0 本。
impl 鍵・待ち 3600 秒・gtimeout 280 秒で対象だけを実行した。
大きい監査・root ビルド・heartbeat 上限の変更はない。

新規 Lean は二ファイル・131 行・明示宣言四本（private 0 本）。
所有ソース全体を再計数した累計は 218 ファイル・16,697 行・明示宣言 751 本
（private 22 本）。外枠 17,000 行まで残り 303 行。
200 行を超える証明や一次 ID の追加、既存 EInfinity ソースの変更はない。

三相 pinched 分岐の全評価は通ったが、三相データ全体・cone 側の係数移送、
全三角形の自然性と K の実 Hom 誘導射の完全忠実性はまだ残る。
M10・M11 以降・G12 は未完として、外枠を維持して進める。

**一覧：済み 10／全体 43（うち追加 1）**。


## §63 三相データの分岐別 cochain と通常二相の全 HA

元の評価列の全射を、元の frame 射と元の評価射へ戻す全異種等式を証明した。
三相データの各 cochain は、元の三つの引き戻し単体の cochain と分岐別に一致する。
評価列の前面は元の frame 図式そのものであり、閉 nerve 単体の前面も同じである。
これを元の cone の末尾面と合わせ、中央相の二表示の全 cochain が一致すると示した。

以上の全成分・全切断の比較を既存の局所方程式移送に渡し、零相を含まない部分集合、
または二相を含まない部分集合の全 HA 方程式を元の三相データについて証明した。
全三相を混ぜる部分集合の方程式は、この主張には含まない。
これらは既存構成の貼り合わせ・係数移送の法則であり、一次 ID の追加はない。

`RawModuleTensorElementEvaluatedColumnMaps.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma downMap_heq {C : Type (u + 1)} [Category.{u} C]
    {x y x' y' : ULiftHom.{u + 1} C} (hx : x = x') (hy : y = y')
    (f : x ⟶ y) (g : x' ⟶ y') (hf : HEq f g) :
    HEq (ULiftHom.down.{u, u + 1, u + 1}.map f)
      (ULiftHom.down.{u, u + 1, u + 1}.map g)

lemma strictRawModuleTensorElementEvaluatedColumn_map_cast_cast {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    HEq ((strictRawModuleTensorElementEvaluatedColumn A X P Q c).map
      (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij)))
      ((strictRawModuleTensorElementDiagram A X P Q).map (c.map (homOfLE hij)))

lemma strictRawModuleTensorElementEvaluatedColumn_map_cast_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 1)) :
    HEq ((strictRawModuleTensorElementEvaluatedColumn A X P Q c).map
      (homOfLE (Fin.le_last i.castSucc)))
      ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj i))
```

`RawModuleTensorTriangleComponents.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorTriangleData_hom_front {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbt : τ b ≠ 2) :
    HEq ((strictRawModuleTensorTriangleData A X P Q c τ).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorTriangleFront A X P Q c τ).hom I a b k hI ha hb hk)

lemma strictRawModuleTensorTriangleData_hom_back {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbt : τ b = 2) (haz : τ a ≠ 0) :
    HEq ((strictRawModuleTensorTriangleData A X P Q c τ).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorTriangleBack A X P Q c τ).hom I a b k hI ha hb hk)

lemma strictRawModuleTensorTriangleData_hom_pinched {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbt : τ b = 2) (haz : τ a = 0) :
    HEq ((strictRawModuleTensorTriangleData A X P Q c τ).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorTrianglePinched A X P Q c τ).hom I a b k hI ha hb hk)
```

`RawModuleTensorTriangleMiddle.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementEvaluatedColumn_front {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    Fin.castSuccOrderEmb.toOrderHom.monotone.functor ⋙
      strictRawModuleTensorElementEvaluatedColumn A X P Q c =
      c ⋙ strictRawModuleTensorElementDiagram A X P Q

lemma strictRawModuleTensorElementEvaluatedColumn_closed_front {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      (strictRawModuleTensorElementEvaluatedColumn A X P Q c)).pullback
      Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ strictRawModuleTensorElementDiagram A X P Q)

lemma strictRawModuleTensorTriangleFront_Back_hom {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (h0 : ∀ i ∈ I, τ i ≠ 0) (h2 : ∀ i ∈ I, τ i ≠ 2) :
    HEq ((strictRawModuleTensorTriangleFront A X P Q c τ).hom I a b k hI ha hb hk)
      ((strictRawModuleTensorTriangleBack A X P Q c τ).hom I a b k hI ha hb hk)
```

`RawModuleTensorTriangleOrdinaryEquation.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorTriangleData_equation_front {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (h2 : ∀ i ∈ I, τ i ≠ 2) : (strictRawModuleTensorTriangleData A X P Q c τ).Equation I

lemma strictRawModuleTensorTriangleData_equation_back {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (h0 : ∀ i ∈ I, τ i ≠ 0) : (strictRawModuleTensorTriangleData A X P Q c τ).Equation I
```

### 63.1 検証と実測

RawModuleTensorTriangleOrdinaryEquation の対象ビルドは終了値 0 で成功した。
新規公開宣言十本の小さい監査も終了値 0。依存公理は propext・Classical.choice・Quot.sound
の範囲で、引用属性の新規追加・引用出力は 0 本。
impl 鍵・待ち 3600 秒・gtimeout 280 秒で対象だけを実行した。
大きい監査・root ビルド・heartbeat の上限変更はない。

新規 Lean は四ファイル・239 行・明示宣言 11 本（private 一本）。
所有ソース全体を再計数した検証済み累計は 222 ファイル・16,936 行・明示宣言 762 本
（private 23 本）。17,000 行の外枠まで残り 64 行。
200 行を超える証明や一次 ID の追加、既存 EInfinity ソースの変更はない。

**一覧：済み 10／全体 43（うち追加 1）**。

## §64 外枠の境界で Lean 追加を停止

BS-M15 §5 の外枠 17,000 行と lane-goals-2026-11-14.md の共通規則の
「外枠に届くとき」で止まる条件を適用する。
次に予定する一まとまりは、定値相の重なりの全 cochain と、中央相を含まない集合の
全 HA 方程式である。参照元の NormalizedTensorTriangleConstantOverlap.lean は 71 行、
NormalizedTensorTrianglePinchedEquation.lean は 55 行で、合わせて 126 行ある。
同じ対象・全 cochain・全切断の比較を保つこの次の移植単位は、BE の型引数を加える前でも
残り 64 行に入らない。ここで新しい Lean ファイル・宣言の追加を止める。
行数を圧縮して外枠を広げたり、主張を弱めて残りへ押し込んだりしない。

M10 は未完である。三相データ全体の HA 方程式と全作用素への自然性、同じ全三角形の
構成と K の実 Hom 誘導射との比較・完全忠実性、一般底の全 native な加群族への接続が残る。
M11–M42 の相対テンソル、指数・降下、RHom、完備反射・完備テンソル・完備版の降下も未完。
M19 の共通の厚さの芯はあるが、M19 の完了としては数えていない。
N01 は追加済み・完了の一件であり、M01–M09 と合わせて済み十件である。
M15 が未完なので完成停止点 1 には達しておらず、G12 に移っていない。

外枠や一次一覧を自分で再設定しない。以後の Lean 実装は調整役の外枠・範囲の指示待ちとし、
指定された代わりの紙の作業を §65 に行う。目標を完了扱いにはしない。

**一覧：済み 10／全体 43（うち追加 1）**。

## §65 停止時の紙：A5 Lemma 8.6 と Shared/Descendable の受け渡し差

読み取り対象は drafts/Shared/Descendable.lean、drafts/A5/StrongDescent.lean と
WeaklyInitialAndDescent.lean。drafts は編集せず、ビルドしていない。
以下は §1 の M01–M42 と現在の本体を照合した受け渡しの差で、新しい Lean の構成や
一次 ID の追加ではない。まだない API を実装済みとして A5 に渡さない。

### 65.1 底と全族の入口

Shared の IsDescendableOver は `(E.CAlg A)` の任意の頂点 R・B と native な辺 f を取る。
StrongDescent の deltaRootEdge・perfRootEdge も、この型の実辺である。
D80 に従い、利用側は E = barrattEcclesTheory に特殊化する。
ただし、この特殊化だけでは現在の strictModuleInfinity A X への接続は済まない。
現在の本体の入口 X は `(operad A).Algebra` の厳密対象であり、厳密底上の安定な dg 加群の
準圏と台の忘却、厳密射の拡大・制限・全随伴まではある。
任意の BE CAlg 頂点と全辺・全高次単体に対して、同じ fiber と transport を持つ族を渡すのが
未完の M10 である。A5 の辺を勝手に厳密射へ読み替える接続にはしない。

### 65.2 定義・指数・台の忘却

Shared:59 の古い IsThickTensorIdeal は D(A) に固定されている。
本体の EInfinity/Modules/ThickTensorIdeal.lean は共通の IsThick を継承し、
任意の指定された安定準圏 C と全 tensorWith 関手を引数に取る。
A5 の一般底の定義はこれを C = Mod_R、tensorWith = M11 の同じ相対テンソルで使う必要がある。
厳密底上の stable 性はあるが、一般底の全族・相対テンソルとの結合はまだ渡せない。
IsDescendableOver と HasDescentIndexLEOver の現状の sorry は、M20–M21 の実定義・定理へ
接続する対象であり、仮定や True として残して済ませない。
fiber は Mod_R で指定単位 R→B の fiber、指数射はその相対テンソル冪から同じ単位への射である。
D(A) の忘却後だけの fiber・テンソルでこの型を代用しない。

### 65.3 RHom と Lemma 8.6 の一変数段階

StrongDescent:93 の fiberSquareRHom は、元の f と任意の D(A) 頂点 L から D(A) の頂点を返す。
受け渡しは §1 の M31–M35 の同じ型である：

```lean
-- §1 M34 の予定型の再掲。ここは未実装の受け渡し型。
fiberSquareRHom (f : SSet.Edge R B) (L : V D) : V D :=
  U_R (moduleRHomObj R (fiberPower f 2) (moduleFromBase R L))
-- §1 M35。Shared の True を置き換える実質的主張。
DLE (-1) (fiberSquareRHom f (unitComplex A)) → Idx f 2
```

moduleFromBase R L は同じ R⊗_A L の全関手であり、L の平坦性を要求しない。
Shared:202 の hasDescentIndexLEOver_two_of_rhom : True はこの M35 の代わりにはならない。
StrongDescent:265 の rootMap_descendable_one は、まさに deltaRootEdge の指数 ≤2 を要求する。
台を取った RHom の零次比較は M33 の全自然な加法同型を経由して同じ指数射の零性へ戻す。
M31–M35 は未完なので現在の本体からこの入力は供給できない。

StrongDescent:153 の rhom_baseChange_koszul_connection は任意の離散係数 L の評価、
有限 Koszul 複体とその有限 Postnikov 各段、導来完備性を使う。
M15 は全随伴・RHom・台の比較・完備反射と完備テンソルを渡す。
個々の Koszul・Nakayama の証明と「By completeness」の具体的な塔の議論は、承認済みの
分担どおり A5 に残す。任意の L について RHom とテンソルの交換を無条件に追加しない。

### 65.4 完備版、Frobenius、同じ Amitsur 錐

Lemma 8.6 の対象は完備な R・B である。Shared:213 の完備版 True を、M36–M39 の
加群の完備反射・同じ完備相対テンソル・完備圏での定義と指数判定に置き換える必要がある。
これらは未実装であり、通常圏における定義をそのまま完備圏の定義とは扱えない。
§1 の M39 は台の完備性を入力に通常の指数から完備版へ送る向きであり、逆向きは要求していない。

perfRootEdge の段階には Shared:205 の射の圏の ℕ 図式と同じ余極限錐、元の指数の上界 n から
2*n への M40–M41 の比較が必要。変数の個数と指数の上界を同一視しない。
StrongDescent の一変数から多変数への帰着には M26–M27 と完備版の同じテンソルが必要である。

Shared:179 の AmitsurData は diagram・base・zero・leg・term を持つ実データであり、
Shared:195 の主張はその同じ aug の極限性である。
WeaklyInitialAndDescent:301 の rootCover の錐も、directPerfectionFunctor で送った同じ錐を要求する。
M28–M30・M42 はこの指定図式と全脚を保って渡す。有限部分 Tot の retract を得たことだけで
無限 Tot の極限性に置き換えない。これらの API はいずれも未完である。

### 65.5 現在渡せる範囲

本体から現在渡せるのは、厳密 BE 底での加群準圏・安定性・台の忘却・正則加群、
厳密射の native な拡大・制限と全随伴・恒等合成の比較、および共通の thick の芯である。
A5 の Lemma 8.6 の descendability 判定・RHom・完備版・降下を完成させる入力はまだ渡せない。
任意 E の輸送、A5 の個々の Koszul・Nakayama の証明、drafts の改変は行っていない。
この紙の照合後も M15・G12 の元の目標は未完で、外枠の指示待ちである。

**一覧：済み 10／全体 43（うち追加 1）**。

## §66 BS-M15 §6：厳密表示の調査結果（11-15、紙のみ）

**結論：四つの利用対象すべてが、現在の宣言から厳密 BE 図式の像として与えられる、とは確認できない。**
通常の環の射・図式には厳密な BE の像を作る既存経路がある。しかし A5 が使うのは
それらに prismatic コホモロジー、Frobenius の余極限、完備化を施した辺・図式であり、
その全関手を同じ厳密 BE 図式の像と結ぶ比較は、現在の指定データに含まれていない。
AmitsurData はそもそも任意の native な増大図式を入力する構造体である。
これは厳密表示の数学的不可能性を述べる結論ではなく、現時点の供給・証明の境界である。

調査基準は自枝 7f6cf9595 と main 530cc801e（BS-M15 §6）である。
⑤a の worktree（HEAD 0a1a56e13）と③-b の worktree（HEAD 57705f223）は読み取りだけ行った。
main の §6 は git show で読み、merge はしていない。Lean・drafts・他レーンのファイルは変更しない。
宣言の形は最新 main の drafts も git show で再確認した。以下の行番号は自枝の参照時の番号で、
main では名前空間整理等で移動している。宣言名を照合の主キーとする。
main では perfectPrism の係数・prism が Semiperfectoid.ainfClassical* を使い、
completeCAlgInclusion は prismCompleteInclusion の略記になっている。
これは係数と包含の供給の更新であり、以下の使用図式の StrictPresentation の供給ではない。
以下の型は**紙上の出力仕様**であり、新しい Lean 宣言・instance を追加した記録ではない。

### 66.1 「像として与えられる」の検収条件

略記を固定する。

```lean
Alg := (operad A).Algebra
B   := CAlg_R A
q   := algebraCAlgSource A       -- nerve Alg ⟶ B、既存
C X := strictModuleInfinity A X -- 既存、X : Alg
```

一つの strict な環射を見つけるだけでなく、次の全図式の比較を必要とする。

```lean
-- K は通常の小さい圏。universe の up/down は指定添字比較を入れて読む。
StrictPresentation (D : nerve K ⟶ B) :=
  Σ F : K ⥤ Alg, FunctorIso (nerveMap F ≫ q) D

-- 一辺は K = WalkingArrow。比較は Δ[1] 上の全関手の同型。
-- f.edge と (nerve.edgeMk g).map q の両端も、この同じ比較の成分で結ぶ。
```

頂点別の VertexIso だけではこの出力に達しない。rootCover では K の増大を含む
WithInitial K 上の全関手を比較し、元の vertex・全脚を同じ比較で移送する。
Amitsur では AugmentedSimplexCategory 全体、Frobenius では ℕ の全図式と
指定遷移辺を比較する。添字の up/down 同型もその比較に含める。
元の余極限・極限性を使う場合には、その同じ増大錐・余錐の比較がさらに必要である。

### 66.2 四つの利用対象の出所と判定

| 対象 | drafts の実際の構成 | 確認できる厳密な入力 | prismatic な BE 出力の判定 |
|---|---|---|---|
| deltaRootEdge | A5/StrongDescent:53 polynomialRootArrow を :57 deltaRootEdge で discreteDeltaFunctor に送る | polyAlgebraToRoot の通常環射から Under の射を作る形。Under の可換性の証明は draft の sorry | **未供給**。使用する一辺への制限の StrictPresentation は、その宣言に含まれない |
| perfRootEdge | StrongDescent:60。上と同じ通常環射を directPerfectionFunctor へ送る | 同じ入力の通常射 | **未供給**。completePerfectionFunctor・Frobenius 塔・完備化の厳密図式と全比較がない |
| AmitsurData.diagram | Shared/Descendable:179 の diagram フィールド。任意の増大形状から E.CAlg A への写像 | 厳密表示はフィールドで要求されていない | **一般には入力として与えられていない**。A5 に使う一つの実図式について別途全比較が必要 |
| rootCover の錐 | A5/WeaklyInitialAndDescent:266 rootCoverArrow、:270 rootCoverCech、:273 rootCoverShape、:278 rootCoverAugmentedCone、:304 directPerfectionFunctor による mapJoinCone | 完備化した通常の環の cosimplicial 図式の形。shape の自然性と全増大錐は draft の sorry | **入力の環図式の形は厳密**。A5 が結論で使う prismatic な錐の厳密表示は未供給 |

「draft の sorry」はその箇所が現在検証済みでないことを示す。通常環の型で書かれたデータと、
証明済みの厳密 BE 出力を同一視しない。

### 66.3 既存本体が実際に与える経路

DiscreteAlgebra.lean:33 の discreteAlgebraFunctor は
CommAlgCat A ⥤ Alg という**実際の通常関手**である。
CAlgDiscreteEmbedding.lean:27 の discreteCAlgEmbedding は定義どおり
nerveMap (discreteAlgebraFunctor A) ≫ q。
CAlgDiscreteDerivedComparison.lean:26 の discreteCAlgUnderEmbedding はさらに
commAlgCatEquivUnder の逆関手の nerve を前合成する。
Theory.lean:35 の barrattEcclesCore.discrete は、この同じ Under 版である。
従って、与えられた通常の A 代数図式 D₀ : K ⥤ Under (CommRingCat.of A) については、

```lean
F₀ := D₀ ⋙ (commAlgCatEquivUnder (CommRingCat.of A)).inverse ⋙ discreteAlgebraFunctor A
nerveMap F₀ ≫ q
```

が指定された離散 BE 図式を表す。rootCover の係数を A = perfectPrismRing p R にするときは、
元の R 代数構造に perfectPrismTheta : A →+* R を前合成してこの経路を使える。
これで rootCover の**離散代数としての**図式や
prismatic site の構造環の図式を扱える。Δ や Δ_perf の図式とは異なる。

A4/Perfectoidization:128 の discreteDeltaFunctor は、係数環の同定の nerve の後で
A2 の derivedPrismaticCohomologyDiscrete と completeCAlgInclusion を合成する。
A2/DerivedPrismaticCohomology:271 の離散版は discreteToAnimated ≫ derivedPrismaticCohomology。
:226 の導来版は、∞ 圏の siftedLan で選んだ拡張である。
PolyDeltaData は ∞ 関手、obj_eq と評価の比較を持つが、通常関手 Poly ⥤ Alg と
その像との全 FunctorIso をフィールドに持たない。
多項式値についての :140 prismaticCohomologyCAlg_eq_totEInfinity も VertexIso の存在であり、
discreteDeltaFunctor 全体の StrictPresentation ではない。

A4:348 の directPerfectionFunctor は :344 completePerfectionFunctor に
completeCAlgInclusion を後合成する。completePerfectionFunctor 自体は draft の sorry で、
関手圏での Frobenius 塔の余極限と反射を要求している。
restrictionSequence:111 も native な後続辺を指定して高次合成を選ぶ構成であり、
通常関手 ℕ ⥤ Alg の宣言ではない。A2 の frobeniusExtension:253 も native な関手圏の辺。
従って、Frobenius の頂点を一つずつ厳密表示しても perfRootEdge の全比較はまだ得られない。

### 66.4 既存の比較・Tot が解決する部分と残る部分

CAlgAlgebraSource.lean の q は既存の cofibrant 置換と cAlgLocalizationSource の合成である。
CAlgCoefficientSourceComparison.lean の cAlgLocalizationSource_algebraIso と
algebraCAlgSource_descendIso は、源ですでに構成した関手の比較を降ろす部品として使える。
任意の D : nerve K ⟶ B に通常関手 F : K ⥤ Alg を割り当てる出力ではない。

③-b の StrictDiagramTotalizationComparison.lean の strictBETotVertex と
StrictDiagramTotNativeConeAt.lean の strictBETotNativeConeAt も読んだ。
入力は F : AsSmall SimplexCategory ⥤ Alg であり、同じ framedLimitFunctor の対象と
その指定 native 錐を出す。これは**厳密図式をすでに持つ場合**の有用な再利用先である。
A2 の Kan 延長や A4 の完備余極限の全関手を、そのような F の像へ戻す宣言ではない。
⑤a の May 系列の部分構成も A2/A4 の上記全関手比較を供給する宣言としては確認できなかった。
他レーンの未マージの構成は、現在の自枝の検証済み依存としては数えない。

### 66.5 厳密ルートを選ぶなら先に必要な証人

使用する図式について次の証人を**構成して証明する**必要がある。
仮定の欄に足して M15 の完了にしない。A_R R 全体の ∞ 関手を一つの通常関手へ
厳密化する出力は十分条件だが、今回の特殊な定理のための最小条件ではない。

```lean
-- P0: 使用する一辺ごとの表示。I₁ := Fin 2 の通常の順序圏。
-- Eδ n, Eperf n は N(I₁)≅Δ[1] で元の二辺を引き戻した同じ図式。
Fdelta (n : ℕ) : I₁ ⥤ Alg
edelta (n : ℕ) : FunctorIso (nerveMap (Fdelta n) ≫ q) (Eδ n)
Fperf (n : ℕ) : I₁ ⥤ Alg
eperf (n : ℕ) : FunctorIso (nerveMap (Fperf n) ≫ q) (Eperf n)
-- BE は barrattEcclesTheory に固定する紙上の略記。

-- P1: A5 で実際に使用する Amitsur 図式 d_use の増大までの表示。
Fam : AugmentedSimplexCategory ⥤ Alg
eam : FunctorIso (nerveMap Fam ≫ q) d_use.diagram
-- d_use.base, zero, leg, term を同じ比較で移送。

-- P2: 指定 rootCover の全増大錐の表示。
Fcover : WithInitial SimplexCategory ⥤ Alg
ecover : FunctorIso (nerveMap Fcover ≫ q) rootCoverAugmentedPrismaticDiagram
-- 右辺は directPerfectionFunctor で送った元の rootCoverAugmentedCone の全写像。

-- P3: 同じ指定 Frobenius Arrow 列の全表示。
Fseq : (ℕ × I₁) ⥤ Alg
eSeq : FunctorIso (nerveMap Fseq ≫ q) uncurriedSpecifiedFrobeniusArrowSequence
-- 同じ cAlgRestrictScalars、指定遷移辺と余極限余錐を比較する。
```

加えて、A5 の一変数から多変数への帰着と底変換で**使う**有限図式を、同じ辺と
その同じ合成で表示する。個々の辺の表示だけから、その正方形・高次の全図式の表示へは進めない。
一般の AmitsurData 全体、すべての通常形状の図式の厳密化は要求しない。

q の係数環は perfectPrismRing p R。添字 up/down と join/WithInitial の既存比較を挿入する。
現在の named な構成からはこの使用図式の証人を取り出せない。
その供給を先に行うなら、以下 §67 の条件付き厳密ルートを選択できる。
それを供給しない場合、§68 の M10 全族ルートが一般の入口を満たす案である。

## §67 厳密表示が供給される場合の残り：型つきの条件付き案

この節は §66.5 の証人が供給された場合に限る。現在その条件が成立したとは報告しない。
新しい ID を実装一覧へ追加したり、Lean 再開の承認と扱ったりしない。
略記 C_X := strictModuleInfinity A X、U_X := strictModuleUnderlying A X、
1_X := strictModuleUnit A X。X,Y,Z は Alg、g : X ⟶ Y は厳密射。
以下は §1 の M11–M42 を厳密な底・厳密な射へ制限した出力型である。
実際に示す適用は §66.5 の辺・正方形・増大図式・Frobenius 列とその必要な係数変更とする。

### 67.1 一般の定義と特殊な適用の分離

原典どおり、任意の安定対称モノイダル ∞ 圏 C で
Desc_C(B) := thickTensorIdealGenerated C tensorWith B one_C を定義する。
strict な場合だけを定義に組み込むのではなく、この一般定義を C_X に適用する。
一般 native な R の全族 R ↦ Mod_R をこれで構成したとは言わない。
全 R・全 f の IsDescendableOver の解釈まで先に求めるなら、定義の一般性だけでは M10 を省略できない。
A5 の指定辺に対する解釈には §66.5 の全比較と、それに沿う同じ単位・fiber・tensor の比較を要求する。

```lean
-- 一般定義。tensorWith と one は C の実対称モノイダル構造から取る。
Desc_C (B : V C) : Prop := thickTensorIdealGenerated C tensorWith B one_C
-- 厳密底での指定辺の解釈。Y を g に沿って X-加群へ制限する。
DescS (g : X ⟶ Y) : Prop := Desc_(C_X) (strictRestrict g (one_Y))
IdxS (g : X ⟶ Y) (n : ℕ) : Prop := IsZeroHom (epsilonS g n)
-- epsilonS は以下で実際に構成する指数射。ホモロジーの数値で定義しない。
```

### 67.2 出力型の一覧（各行は元の M 項目の制限）

| 元の項目 | 厳密ルートで構成・証明する型 |
|---|---|
| M11–M14 | tensorS X : C_X ⊗ C_X ⟶ C_X とその実 SymmetricModuleTensor 構造、単位 1_X、全結合子・対称性・両単位子、∀M, IsExactFunctor (tensorSWith X M) |
| M15 | strictExtend g の実対称モノイダル構造、指定された導来 pushout 正方形 Q の像に対する全関手底変換同型 |
| M16–M18 | unitS g : Edge 1_X ((strictRestrict g).app _ 1_Y)、FS g : V C_X、同じ unitS の fiber 錐の極限性、powerS g n : V C_X、epsilonS g n : Hom_(h C_X) (powerS g n) 1_X、単位底での元の fiber・冪・射との同定 |
| M19–M22 | 共通 IsThick と同じ tensorS での一般定義、DescS g ↔ ∃n, IdxS g n、単位底特殊化 |
| M23–M27 | 指定導来 pushout の辺での DescS/IdxS の保存、厳密合成 g≫h に対する保存、使用する二辺の相対テンソルの保存 |
| M28–M30 | strict な増大図式 Dbar : AugmentedSimplexCategory ⥤ Alg の像について moduleAmitsurS Dbar M : augmentedShape ⟶ C_X、IdxS g n → IsLimitCone (moduleAmitsurSAug Dbar M)、同じ d.aug の IsLimitCone |
| M31–M33 | rhomS X : C_Xᵒᵖ ⊗ C_X ⟶ C_X、QCatAdjunction (tensorSWith X M) (rhomSWith X M)、Hom_(h C_X) M N ≃+ H⁰(U_X(rhomSObj X M N)) |
| M34–M35 | fromBaseS X : D(A) ⟶ C_X、fiberSquareRHomS g L := U_X(rhomSObj X (powerS g 2) (fromBaseS X L))、DLE(-1)(fiberSquareRHomS g (unitComplex A)) → IdxS g 2 |
| M36–M39 | completeS X s、completionS X s と包含への実 QCatAdjunction、完備 tensor/単位の実対称構造、完備圏の厚いテンソルイデアルによる定義・指数判定、台が完備な指定辺の通常指数から完備指数への保存 |
| M40–M41 | 同じ厳密 ℕ×WalkingArrow 図式の像と指定余極限錐 c に対する (∀j, IdxS g_j n) → IdxS g_colim (2*n)、完備 Arrow 圏の同じ錐での完備版 |
| M42 | 使用する完備な増大図式の同じ全脚を持つ錐について DescCompS g → IsLimitCone (moduleAmitsurCompSAug Dbar M)、M=1_X の元の CAlg 錐との比較 |

補足の型を明示する。

```lean
-- fromBaseS は A 上の係数の拡大。L の平坦性は要求しない。
fiberSquareRHomS (g : X ⟶ Y) (L : V (derivedInfinityCategory A)) :
  V (derivedInfinityCategory A)

-- s : Finset A。completeS は U_X の台が s 完備な頂点の充満部分準圏。
completionS X s : C_X ⟶ completeS X s
QCatAdjunction (completionS X s) (completeSInclusion X s)
completeTensorS X s M N := completionS X s (tensorSObj X M.val N.val)

-- 二相の strict な正方形でも通常の pushout で済ませない。
-- hQ は q の像が指定された導来 pushout 錐であることの検証対象。
(hQ : IsColimitCone (mapJoinCocone q strictPushoutCocone)) →
  IdxS g n → IdxS gBaseChanged n
```

tensorS は単なる結合的 dg 代数 assocForget X の普通のテンソルではない。
X の E∞ 構造に由来する相対対称モノイダル構造と全高次の比較を作る必要がある。
任意の可換環上の BE 代数を strict 可換 dg 代数に置換する前提は入れない。
単位・拡大・U・指数射の向きは §1 と同じものを保つ。
相対内部 Hom・完備反射を存在する instance として引数に置く出力にはしない。
個々の Koszul・Nakayama の証明は A5 に残す。

### 67.3 補正つきの見込み（追加 Lean 行、条件付き）

旧 §42 の残り見積りを「素の作業量」の基準に取り、型付きの全係数・単位・余単位・
native な辺・Hom end の照合、完備反射の実構成を別途加重する。
§69 の実測に従い、一律の無補正値や完成済み N01 の再加算は使わない。

| 残りの束 | 素の基準 | 今回の係数（下端／上端） | 補正後 |
|---|---:|---:|---:|
| M11–M15 相対対称 tensor・底変換 | 1,800–2,800 | 2.5／4 | 4,500–11,200 |
| M16–M20 fiber・指数射・thick の接続 | 450–850 | 2／3 | 900–2,550 |
| M21–M27 指数判定・保存 | 900–1,500 | 2.5／4 | 2,250–6,000 |
| M28–M30 同じ Amitsur 塔・無限 Tot | 600–1,000 | 3／5 | 1,800–5,000 |
| M31–M35 全 RHom・評価・二乗指数判定 | 500–800 | 2.5／4 | 1,250–3,200 |
| M36–M42 実完備反射・完備 tensor・完備降下 | 700–1,200 | 3／5 | 2,100–6,000 |
| A5 の指定辺・図式との全比較の使用 | 300–700 | 2／3 | 600–2,100 |
| **合計** | **5,250–8,850** | | **13,400–36,050** |

これは §66.5 の厳密表示が**すでに証明されている場合**の追加量であり、その証人を作る費用は含まない。
現状でこの値だけを外枠に足して strict ルートが実行可能とは結論しない。
現在値との合計は 30,336–52,986 行、計画上の丸めは **31,000–53,000 行**。
余分な native 全族を省ける可能性はあるが、相対 tensor・RHom・完備化自体の実構成は残る。
厳密表示の橋の費用は、A2/A4 の実模型が供給される前にはこの区間に押し込めない。

## §68 厳密表示が供給されない現状での M10 全族の残り

これは元の M10 の**検収束への分割**であり、新しい一次 ID の追加ではない。
略記 L_X := localizationNerve (strictRawModuleRelativeCategory A X)、K_X := strictRawModuleComparison A X、
T₀ := moduleTotalInfinity A、p₀ := moduleTotalProjection A、
b_X := q.app _ (nerveVertex X)。
Fib π b は Δ[0] の頂点 b に沿う π の strict pullback。π が実 cocartesian fibration である模型で使う。
source・unit・U の比較には、元の resolution と指定成分を使う。

### 68.1 型つきの未完検収一覧

```lean
-- F1: 元の実三相データを閉じる。I_XPQ は元の全 frame 要素圏。
triangle_XPQ : (Δ[2] ⊗ nerve I_XPQ) ⟶ dgNerve A (RightModule A D_X)
-- 全 i : Fin 3 の標準面 face i : Δ[1] ⟶ Δ[2] について
(face i ⊗ₘ 𝟙 _) ≫ triangle_XPQ = specifiedTriangleBoundary_XPQ i
-- 指定三面は元の cone 円柱、元の評価円柱、元の pinched 族の interval 表示。
-- 全面・退化の自然性と同じ実 .h を保つ。全三相 HA の証明を構成に含む。

-- F2: 同じ K_X の全 Hom 誘導射の同値性と圏同値。
∀ P Q, IsSimplicialHomotopyEquivalence (strictRawModuleProbeComparisonPinchedMap A X P Q)
IsFullyFaithful K_X
IsQCatEquivalence K_X
-- 最初の P,Q は元の probe。全頂点への ES と Hom の全自然な移送も証明する。

-- F3: 局所化後の元の固定底を全圏の指定 fiber と同定する。
-- κ_X は既存の固定底包含から同じ全圏へ誘導する写像。
κ_X : L_X ⟶ Fib π b_X
IsQCatEquivalence κ_X
-- K_X と κ_X の両比較で同じ元の正則加群と U_X を同定する。

-- F4: 生の p₀ がそのまま inner fibration とは仮定せず、必要なら実際に模型を作る。
moduleNativeFamily :
  Σ (T : SSet.{u+1}), { π : T ⟶ B // CocartesianFibration π }
qTotal : T₀ ⟶ moduleNativeFamily.1
IsQCatEquivalence qTotal
FunctorIso (qTotal ≫ moduleNativeFamily.2.val) p₀
-- 単にこの構造を引数の Setup/instance にしない。

-- F5: 元の全厳密射と全比較を底の局所化へ降ろす。
transport_π ((nerve.edgeMk g).map q) : Fib π b_X ⟶ Fib π b_Y
FunctorIso (κ_X ≫ transport_π ((nerve.edgeMk g).map q)) (extendLocal g ≫ κ_Y)
-- extendLocal は同じ L_X→L_Y の derived 拡大。K を通すと既存 strictExtend g。
-- 擬同型の底では transport が実同値。全 Δ[n] 上の合成・退化の比較を構成する。

-- F6: 元の全族を指定 fiber の表示と U・単位付きで検収する。
e_X : Fib π b_X ⟶ C_X
IsQCatEquivalence e_X
FunctorIso (κ_X ≫ e_X) K_X
FunctorIso (transport_π ((nerve.edgeMk g).map q) ≫ e_Y) (e_X ≫ strictExtend g)
-- さらに family 上の U の全関手、指定単位、単位・余単位の元の成分の比較。
```

ここで transport_π は cocartesian lift の実構成による全輸送であり、h 上の一射の選択ではない。
strictRawModuleRestrictionPseudofunctor、strictRawModuleTotal、strictRawModuleTotalRelative と p₀ は
既存。通常の cartesian lift や projection があることだけから、F3–F5 の ∞ 局所化後の
fiber・cocartesian 性は結論しない。既存の一般の cocartesian 分類・fiber・局所化の部品を
先に照合して使う。③系の一般理論を⑤dで作り直す費用は、下の見積りの基準外であり、
追加の一般定理が必要と判明したら別に止まって報告する。

### 68.2 M10 の補正つき見込み（現在からの追加量）

| 検収束 | 現在の実装から残る素の作業量 | 補正係数（下端／上端） | 補正後 |
|---|---:|---:|---:|
| F1 全三角形・残る係数移送と全自然性 | 1,200–2,000 | 2.5／3 | 3,000–6,000 |
| F2 同じ K の Hom 射・完全忠実性 | 600–1,000 | 2.5／3 | 1,500–3,000 |
| F3 局所化後の全圏の指定 fiber | 500–900 | 3／3 | 1,500–2,700 |
| F4 実 cocartesian 模型と元の全圏との比較 | 900–1,500 | 3／4 | 2,700–6,000 |
| F5 底の局所化、全輸送・合成・高次単体 | 800–1,400 | 3／4 | 2,400–5,600 |
| F6 同じ U・正則加群・全族の最終照合 | 300–600 | 2.5／3 | 750–1,800 |
| **M10 残り合計** | **4,300–7,400** | | **11,850–25,100** |

計画の丸めは **M10 だけで追加 12,000–25,500 行**。
現在の 16,936 行を合わせると 28,786–42,036 行、丸めて **29,000–42,500 行**。
これは M10 が閉じるまでの量であり、M11–M42 と G12 を含まない。
§42 の M10 残り 1,500–3,000 行は撤回し、この区間へ更新する。
F1 で既存複体側の全 triangle を再利用できても、F3–F6 の全族の検収は別に残る。

## §69 数字の補正の根拠・範囲・判断材料

1. §5.1 で M01–M09 の主出力が済んだ時点は 1,549 行。
   以後 §63.1 までに 16,936−1,549 = **15,387 行**を追加した。
   この中に追加 N01 の **693 行**を含む。N01 を除いても **14,694 行**で、
   M10 の経路はまだ完了していない。旧 M06–M10 全体の上端 1,800 行に対しても約 **8.16 倍**ある。
   これは M06–M10 の個別の正確な費用比ではなく、旧上端の規模判断が外れた下限を示す比較である。
2. §42 の 8,500 行時点で M10 の残りを 1,500–3,000 行とした後、さらに
   **8,436 行**を使っても全族は未完だった。旧上端の **2.812 倍超**が実際に必要となった。
   この事実から、今後の全高次・Hom end・局所化後の fiber の未経験部分を係数 1 のままにしない。
3. ただし全費用に一律 8.16 倍は掛けない。N01 は既存の実モデル転送の再利用により
   旧 1,000–2,200 行に対して 693 行で済み、しかも完成済みなので再加算しない。
   既に通った全三角形の普通二相・pinched 評価・単体の共役なども残量に二重計上しない。
4. §67 は比較的局所的な fiber・thick を 2–3、相対 tensor・指数・RHom を 2.5–4、
   まだ実構成していない無限塔・完備反射を 3–5 として積算した。
   §68 の未知の全族・局所化後 fiber は旧上端の外れを踏まえて概ね 3–4、
   既存の明示 triangle・K の比較の残りは 2.5–3 とした。
   これらは形式的な定理や統計的な保証区間ではなく、作業計画のための補正・留保である。
5. M10 全族ルートの後にも §67 と同じ実相対 tensor・指数・RHom・完備版が残る。
   概算の単純和は **追加 25,250–61,150 行**、現在分込み **42,186–78,086 行**。
   計画上は **追加 26,000–62,000 行、総量 43,000–79,000 行**程度を判断材料とする。
   strict 使用図式の比較費用を native 適用の比較へ読み替えた粗い全体幅であり、
   承認済みの外枠や「この上端で必ず完成する」という約束にはしない。
   特に一般理論の不足を発見した場合や、A2/A4 の境界が変わる場合は見直す。

判断の分岐は次のとおりである。

- A2/A4 から §66.5 の**全関手・全増大の厳密表示**を供給できるなら、M10 の全族を後回しにして
  §67 の厳密ルートを採る余地がある。その場合も一般の厚いテンソルイデアルの定義を保つ。
- 現在の宣言のままでは、その厳密表示を入力として取り出せない。
  §68 の M10 全族ルートを続けるか、使用図式だけの厳密表示を A2/A4 の作業として先に追加するかを
  調整役が選ぶ必要がある。点ごとの模型の選択だけで strict ルートに切り替えない。
- strict 図式の限界に閉じた既存 G10 の部品を、一般の図式の厳密化定理として使わない。
  A5 の個々の Koszul・Nakayama の証明はこのどちらの見積りにも含めず、担当を維持する。

## §70 紙の検収・今回の差分

BS-M15 §6 の三点に対し、§66 が入力の出所と厳密性の判定、§67 が条件が成立した場合の
残りの型と見込み、§68–§69 が現状で必要な M10 全族の型と補正つき見込みである。
AmitsurData の任意入力と A5 の特定の実図式を分け、draft の sorry と検証済み本体の経路を区別した。
「厳密表示がない」という調査結果を、数学的な厳密化不可能性や新しい仮定として使わない。

変更は本報告の追記だけ。Lean・drafts・main・他レーンのファイルは変更せず、
ビルド・監査・鍵の取得は行っていない。紙上の型はコンパイル済みと表示しない。
検証済み Lean は前回の **222 ファイル・16,936 行・762 明示宣言（private 23）**のまま。
M15 の Lean 停止を維持し、外枠・範囲の決定を待つ。G12 は開始していない。

**一覧：済み 10／全体 43（うち追加 1）**。


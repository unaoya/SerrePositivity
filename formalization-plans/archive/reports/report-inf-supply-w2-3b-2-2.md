# IS-W2 の報告（report-inf-supply-w2.md） — 3b-2 後半（B02〜停止点 2b、B4 を含む）（§113〜§160、2026-11-14）

元の報告：[report-inf-supply-w2.md](../../stage-ii/inf-supply-b/report-inf-supply-w2.md)

## 113. 11-14の再開承認とBE忘却の無条件版の確認

### 113.1 IS-W2 §16

ユーザー承認とmainの指示書§16を読み取り、3b-2をB02から再開した。外枠は **20,000行**、一覧B01〜B08・C01〜C07・D01〜D08と§14の数え方は維持する。B・Cの完了を停止点**2a**として報告し、承認を待たずDへ進む。D完了は停止点**2b**（3b-2完成）。B完了時に、その実測とAの見込みに対する増分の比率も参考にC・Dを再見積もりして止まらず報告する。

前回の外枠による中間停止は解除した。mainは凍結中なのでmerge・変更・ビルドをせず、自分の枝だけで検証とコミットを続ける。対象ビルドと新規分だけの小さな監査を用いる。

### 113.2 §112の補足：FreeProbeUnitTransportConditionは本体で証明済み

調整役の11-14の連絡を受け、実ファイルを読み直して確認した。

- `EInfinity/BarrattEccles/FreeProbeUnitLocalTransport.lean`の`freeProbeUnitTransportCondition`は、`derivedFreeProbeUnitIntervalMap_transportIso`を使って`FreeProbeUnitTransportCondition A`を証明している。
- `FreeProbeDerivedFreeForget.lean`の`cAlgFreeForgetDerivedAdjunction`は、その定理を`cAlgFreeForgetDerivedAdjunctionOfTransport`へ渡した無条件の随伴。
- 同ファイルの`cAlgForgetDerived_mapJoinCone_isLimit`と`cAlgForgetDerived_hasLimit_postcomp`は、その定理を条件付き版へ代入した無条件版。§112の条件付き版だけの確認を、未供給の障害とは扱わない。

3b-4ではこの**無条件版**を再利用する。BEの実例の`forget_preservesLimits`にも供給済みとの連絡を受領した。既存の`FramedLimit*`や`CAlgUnderlyingDerivedComparison`の再構成は行わない。

これによりBE側の指定native極限錐が得られた後のU像の極限性は、追加のtransport仮定なしで上記定理へ接続できる。一方、元のstrict BE模型計算の指定錐をそのnative錐へ全高次単体とともに接続する工程と、実現側のU保存は、この極限保存定理だけで済ませない。G10（B02以降）の進行順は変えない。


## 114. B02再開後：実AW合成の同じ自由逆随伴を全次数で評価

### 114.1 進捗と型

§16の承認に従いB02を再開した。実標準DK Homへの射を、既存の自由加群・Moore正規化随伴の**同じ合成**で戻す。その逆随伴を指定Moore射影生成元で評価すると、実Γの同じ射影と余単位による評価に一致することを示した。これを指定標準DK同型へ適用し、正次数は元の最上位成分、零次数はcyclesからの包含で元の最上位成分を回収する。

実`standardComposition`に適用した逆随伴について、零次数・全正次数で元の`awTerm`の全切断点の和になる式を閉じた。後の射gを第一因子、前の射fを第二因子とし、元のbraidingと標準合成の順を保持する。これはB02の同じ生成元・成分照合の証明分割（§14）であり、独立した前提計算や照合の枠を追加しない。B02前提計算3/3、照合全体3/3のまま。

下記はDiagramComparison名前空間。一般の式は`{R : Type u}`・`[CommRing R]`、標準Homの式はさらに`{D : Type v}`・`[DGCategory R D]`を固定する。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedFreeHomProjectedEvaluation`

```lean
def freeMooreChainsAdjunction :
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (ModuleCat R)).obj
      (ModuleCat.free R) ⋙ normalizedMooreComplex (ModuleCat R)) ⊣
    ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat R) ℕ ⥤ SimplicialObject (ModuleCat R)) ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat R) (Type u)).obj
        (forget (ModuleCat R)))
```

```lean
theorem normalizedFreeHomEquiv_symm_projected_eval (S : SSet.{u})
    (K : ChainComplex (ModuleCat R) ℕ)
    (f : S ⟶ (Abelian.DoldKan.Γ.obj K) ⋙ forget (ModuleCat R)) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n⦌)) :
    (((freeMooreChainsAdjunction (R := R)).homEquiv S K).symm f).f n
      ((DoldKan.PInftyToNormalizedMooreComplex (S ⋙ ModuleCat.free R)).f n
        (ModuleCat.freeMk s)) =
    ((DoldKan.PInftyToNormalizedMooreComplex (Abelian.DoldKan.Γ.obj K)).f n ≫
      (Abelian.DoldKan.equivalence.counitIso.hom.app K).f n) (f.app _ s)
```

```lean
def standardDoldKanSpaceMap (x y : D) :
    standardHomSpace (R := R) x y ⟶
      (Abelian.DoldKan.Γ.obj (connectiveHomComplex (R := R) x y)) ⋙
        forget (ModuleCat R)
```

```lean
theorem normalizedFreeStandardHom_positive_eval (S : SSet.{u}) (x y : D)
    (f : S ⟶ standardHomSpace (R := R) x y) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n + 1⦌)) :
    let g : (normalizedMooreComplex (ModuleCat R)).obj (S ⋙ ModuleCat.free R) ⟶
        connectiveHomComplex (R := R) x y
```

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedFreeAWProjectedEvaluation`

```lean
def normalizedFreeStandardHom (S : SSet.{u}) (x y : D)
    (f : S ⟶ standardHomSpace (R := R) x y) :
    (normalizedMooreComplex (ModuleCat R)).obj (S ⋙ ModuleCat.free R) ⟶
      connectiveHomComplex (R := R) x y
```

```lean
theorem normalizedFreeStandardAW_positive_eval (S T : SSet.{u}) (x y z : D)
    (g : S ⟶ standardHomSpace (R := R) y z)
    (f : T ⟶ standardHomSpace (R := R) x y) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n + 1⦌)) (t : T.obj (Opposite.op ⦋n + 1⦌)) :
    let h
```

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedFreeHomZeroEvaluation`

```lean
theorem mooreProjection_zero_eq (W : SimplicialObject (ModuleCat R)) :
    (DoldKan.PInftyToNormalizedMooreComplex W).f 0 = (mooreDegreeZeroIso W).inv
```

```lean
theorem normalizedFreeHomEquiv_symm_zero_eval (S : SSet.{u})
    (K : ChainComplex (ModuleCat R) ℕ)
    (f : S ⟶ (Abelian.DoldKan.Γ.obj K) ⋙ forget (ModuleCat R))
    (s : S.obj (Opposite.op ⦋0⦌)) :
    (((freeMooreChainsAdjunction (R := R)).homEquiv S K).symm f).f 0
      ((mooreDegreeZeroIso (S ⋙ ModuleCat.free R)).inv (ModuleCat.freeMk s)) =
    (gammaDegreeZeroIso K).hom (f.app _ s)
```

```lean
theorem normalizedFreeStandardHom_zero_eval (S : SSet.{u}) (x y : D)
    (f : S ⟶ standardHomSpace (R := R) x y) (s : S.obj (Opposite.op ⦋0⦌)) :
    (homObject R D x y).iCycles 0
      ((connectiveHomComplex_zeroIso (R := R) x y).hom
        ((normalizedFreeStandardHom S x y f).f 0
          ((mooreDegreeZeroIso (S ⋙ ModuleCat.free R)).inv (ModuleCat.freeMk s)))) =
    standardTopEval (R := R) x y 0 (f.app _ s)
```

```lean
theorem normalizedFreeStandardAW_zero_eval (S T : SSet.{u}) (x y z : D)
    (g : S ⟶ standardHomSpace (R := R) y z)
    (f : T ⟶ standardHomSpace (R := R) x y)
    (s : S.obj (Opposite.op ⦋0⦌)) (t : T.obj (Opposite.op ⦋0⦌)) :
    let h
```

### 114.2 検収と登録

コード **`a34bfb003`**（1本117行）・**`8b0cc2644`**（2本157行）、計 **3本274行**。

- 鍵付き対象ビルド127：**4,081 jobs・終了コード0**、新規監査`/private/tmp/AuditISW2G10B02FreeProjected.lean`は **6宣言・標準三公理のみ**。
- 最終ソースの鍵付き対象ビルド129：**4,097 jobs・終了コード0**、新規監査`/private/tmp/AuditISW2G10B02FreeAWZero.lean`は **9宣言（4・5）・標準三公理のみ**。

ログは`/private/tmp/isw2-build127.log`・`/private/tmp/isw2-build129.log`。共有鍵は返却済み。大きな監査・rootビルドは実行していない。再利用する零次数DK公式の成果物が枝になかったので、その依存は上記対象ビルドで補った。

深いΓの型照合が既定の200,000 heartbeatに達した箇所は、同じ随伴と忘却射の型を固定し、合成の適用だけを明示して解消した。計算上限は上げず、既存宣言・⑤a・入口・公式監査・mainを変更していない。新公理・sorryなし。

累計 **234モジュール・14,113行・2,130宣言**。対象一覧は`/private/tmp/isw2-g10-twohundredthirtyfour-modules.txt`。新しい外枠20,000行まで残り5,887行。登録対象は114.1の3本。

### 114.3 次の接続

B02は未完。今回の実合成の逆随伴の切断和を、A09の同じ自由鎖AWと指定tensor–Hom随伴の切断点ごとの式へ接続する。sourceのMoore射影を一般のAWと可換と仮定するのではなく、同じ生成元評価の後で比較し、包含と射影のsplit則を使う経路を検討している。

`FreeTensorCoefficientGeneratorValues.lean`は、最後の切断の既存係数計算を任意の二次数へ分割する検査中の下書き。上のコミット・行数・監査には含めない。B03〜B08・C・Dも未完であり、今回の区切りは停止点2a・2bの完了報告ではない。Bが完了した時点でC・Dの見込みを実測に基づいて出し直す。


## 115. B02の途中：自由鎖AWの任意切断と全切断和の計算

### 115.1 同じ成分照合の分割と型

§114の実合成側の全切断和へ接続するため、A05aで検証した最後の切断の係数計算を、同じ既存構成の任意の二次数・任意の切断点へ分割した。指定係数比較が二因子のMoore射影生成元の純テンソルを、元の負次数延長の純テンソルへ送ることを、既存の斉次包含・係数移送・自由生成元の式から示した。

その式を既存AWの各切断成分へ代入し、対応する前面・後面の射影生成元のテンソルとなる式を閉じた。さらに既存`alexanderWhitneyApp`の有限和の定義から、同じ全切断和の式を得た。始域のMoore射影を勝手に消去せず、整数線形化からの元の成分に対して述べている。

下記はDiagramComparison名前空間、`{A : Type u}`・`[CommRing A]`を固定する。B02の同じ係数・成分計算の証明分割（§14）であり、独立した前提計算や照合の追加ではない。B02前提計算3/3、照合全体3/3はそのまま。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeTensorCoefficientGeneratorValues`

```lean
def freeNegativeGenerator (X : SSet.{u}) (n : ℕ) (x : X.obj (Opposite.op ⦋n⦌)) :
    (freeNegativeChains (A := A) X).X (-(n : ℤ))
```

```lean
theorem freeTensorCoefficient_projection_value
    (φ : simplicialRingCoefficient.{u} →+* A) (X Y : SSet.{u})
    (i j n : ℕ) (h : i + j = n)
    (x : X.obj (Opposite.op ⦋i⦌)) (y : Y.obj (Opposite.op ⦋j⦌)) :
    let F
```

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductAWCutValues`

```lean
theorem freeProductAlexanderWhitney_cut_value
    (φ : simplicialRingCoefficient.{u} →+* A) (X Y : SSet.{u})
    (n : ℕ) (c : Fin (n + 1))
    (x : X.obj (Opposite.op ⦋n⦌)) (y : Y.obj (Opposite.op ⦋n⦌)) :
    let F
```

```lean
theorem freeProductAlexanderWhitney_sum_value
    (φ : simplicialRingCoefficient.{u} →+* A) (X Y : SSet.{u})
    (n : ℕ)
    (x : X.obj (Opposite.op ⦋n⦌)) (y : Y.obj (Opposite.op ⦋n⦌)) :
    let F
```

### 115.2 検収と登録

コード **`13d1ecc09`**（2本209行）。依存順に結合した個別検査`/private/tmp/isw2-free-aw-cut3.log`は終了コード0。鍵付き対象ビルド`/private/tmp/isw2-build130.log`は **4,014 jobs・終了コード0**。新規分のみの監査`/private/tmp/AuditISW2G10B02FreeAWCuts.lean`は **10宣言（7・3）・標準三公理のみ**。共有鍵は返却済み。

累計 **236モジュール・14,322行・2,140宣言**。一覧は`/private/tmp/isw2-g10-twohundredthirtysix-modules.txt`。外枠20,000行まで残り5,678行。新公理・sorryなし。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。大きな監査は実行していない。登録対象は115.1の2本。

### 115.3 残り

B02は未完。今回の自由鎖AW側の切断和と、§114の実豊穣合成の逆随伴の切断和を、指定tensor–HomとHom–Totの成分・符号を介して同じ射として照合する。`HomTotalHomogeneousComposition.lean`は、試験対象の次数零の鎖射に限らず任意次数の合成について同じ積射影の成分を合わせる検査中の下書きであり、この検収と累計には含めない。

B03〜B08・C・Dは未完。停止点2a・2bの完了報告ではない。B完了時のC・Dの再見積もりは、Bの実測が揃った所で行う。


## 116. B02の途中：Hom–Tot成分の任意次数合成

### 116.1 同じ成分照合の型

元の`homTotalComponent`は、試験対象の次数零の鎖射だけでなく、**任意の整数次数p・qの斉次射の合成**を、同じ積射影による成分で保つことを示した。微分閉性や有界性を追加していない。B02の全Hom単体の成分照合の分割（§14）であり、独立した前提計算・照合の枠を追加しない。B02前提計算3/3、照合全体3/3のまま。

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalHomogeneousComposition`。
名前空間はHA.DerivedCategoryModels.CosimplicialTotalization、`{A : Type u}`・`[CommRing A]`を固定する。

```lean
theorem homTotalComponent_homogeneous_comp {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q : ℤ) (n : ℕ)
    (f : Homogeneous P Q p) (g : Homogeneous Q ((productTotalFunctor A).obj X) q) :
    homTotalComponent P X (p + q) n (f.comp g rfl) =
      f.comp (homTotalComponent Q X q n g) (by omega)
```

### 116.2 検収と登録

コード **`950678940`**（1本46行）。個別検査`/private/tmp/isw2-homtotal-homogeneous8.log`は終了コード0。依存するcochain成分の等しい整数添字の移送は、既存の成分式を使い、合同を一段ずつ取り整数等式の所でomegaを適用して閉じた。計算上限は変更していない。

鍵付き対象ビルド`/private/tmp/isw2-build131.log`は **2,287 jobs・終了コード0**。新規分だけの監査`/private/tmp/AuditISW2G10B02HomTotalComposition.lean`は **2宣言・標準三公理のみ**。共有鍵は返却済み。大きな監査・rootビルドは実行していない。

累計 **237モジュール・14,368行・2,142宣言**。一覧は`/private/tmp/isw2-g10-twohundredthirtyseven-modules.txt`、外枠20,000行まで残り5,632行。再開後の追加は6本529行・27宣言。新公理・sorryなし。既存宣言・⑤a・入口・公式監査・mainの変更なし。登録対象は116.1の1本。未検証下書きは残っていない。

### 116.3 残り

B02は未完。実AWの逆随伴の切断和（§114）、自由鎖AWの各切断と全切断和（§115）、Hom–Totの任意次数合成（本節）を、同じ指定重みとtensor–Homの符号付き成分に接続して最終の射の等式を閉じる。これらの部分公式を、B02の最終等式やB03〜B08のnative極限性の代用にしない。

C・Dも未完。停止点2a・2bの検収ではない。新しい外枠と一覧の中で継続し、B完了時にC・Dを実測に基づいて再見積もりする。BE忘却の無条件版の確認は§113.2に記録済み。


## 117. B02の途中：元のHom–Tot/BK比較の全行を指定標準重み射で表示

### 117.1 同じ比較の因子分解と型

元のMoore包含・over/bar鎖同型の逆射・先頭頂点の標準重み比較を、`normalizedBKStandardWeightMap`にまとめた。元の`normalizedBousfieldKanHomComparison`が、この同じ射の前合成と既存の符号つきend–Hom同型の合成に**厳密に等しい**ことを証明した。

指定標準重みへの逆比較の各成分を、同じ自由単位Yoneda評価の逆射で同定した。積射影の自然性で任意の鎖重みからの前合成へ移し、元の`homTotalNatIso_hom_component`を代入して、元の`homToNormalizedBousfieldKan`の**任意整数次数q・全鎖次数n**での行表示を得た。指定射と元の積成分・符号を保持する。

以下はHA.DerivedCategoryModels.CosimplicialTotalization名前空間。係数環は`A : Type u`・`[CommRing A]`（各宣言によりAは暗黙／明示）。B02の同じ成分照合の証明分割（§14）であり、独立した前提計算・照合を追加しない。B02前提計算3/3・照合全体3/3のまま。

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BKWeightComparisonComponents`

```lean
theorem barWeightEndTotalComparison_app_standard (X : CosimplicialObject (Complex A)) :
    barWeightEndTotalComparison.app X =
      (standardWeightEndTotalIso X).inv ≫
        (linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map
          ((alternatingFaceMapComplex _).map
            (SimplicialRealization.barStandardWeightComparison (ModuleCat.of A A))).op
```

```lean
theorem barToBousfieldKanWeightEndComparison_app (X : CosimplicialObject (Complex A)) :
    barToBousfieldKanWeightEndComparison.app X =
      (linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map
        (barDoubleOppositeOverChainIso SimplexCategory (ModuleCat.of A A)).inv.op
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKStandardWeight`

```lean
def normalizedBKStandardWeightMap :
    normalizedBousfieldKanWeight (A := A) ⟶
      (alternatingFaceMapComplex _).obj (standardSimplexWeight (ModuleCat.of A A))
```

```lean
theorem normalizedBousfieldKanHomComparison_standardWeight
    (X : CosimplicialObject (Complex A)) :
    normalizedBousfieldKanHomComparison X =
      (standardWeightEndTotalIso X).inv ≫
        (linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map
          (normalizedBKStandardWeightMap A).op ≫
        (weightEndHomIso A normalizedBousfieldKanWeight (doubleOppositeDiagram X)).hom
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightTotalInverseEvaluation`

```lean
theorem standardWeightEndCochainIso_inv_f (X : CosimplicialObject (Complex A)) (n : ℕ) :
    (standardWeightEndCochainIso X).inv.f n =
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app (doubleOppositeDiagram X)).inv
```

```lean
theorem standardWeightEndTotalIso_inv_component
    (X : CosimplicialObject (Complex A)) (n : ℕ) (q : ℤ) :
    (standardWeightEndTotalIso X).inv.f q ≫
      CochainProductTotal.componentπ
        ((linearWeightEndCochainFunctor A (doubleOppositeDiagram X)).obj
          (Opposite.op ((alternatingFaceMapComplex _).obj
            (standardSimplexWeight (ModuleCat.of A A))))) n q =
    componentπ X n q ≫
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram X)).inv.f (q - n)
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightHomRows`

```lean
theorem standardWeightHomComparison_rows
    (K : ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℕ)
    (g : K ⟶ (alternatingFaceMapComplex _).obj (standardSimplexWeight (ModuleCat.of A A)))
    (X : CosimplicialObject (Complex A)) (q : ℤ)
    (z : ((productTotalFunctor A).obj X).X q) (n : ℕ) :
    extendedChainHomRows K
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram X)) q
      ((weightEndHomIso A K (doubleOppositeDiagram X)).hom.f q
        (((linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map g.op).f q
          ((standardWeightEndTotalIso X).inv.f q z))) n =
    weightEndHomSign n q • (g.f n ≫
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram X)).inv.f (q - n) (componentπ X n q z))
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomToNormalizedBKRows`

```lean
theorem homToNormalizedBousfieldKan_rows (P : Complex A)
    (X : CosimplicialObject (Complex A)) (q : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) q) (n : ℕ) :
    extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) q
      ((homToNormalizedBousfieldKan P X).f q f) n =
    weightEndHomSign n q • ((normalizedBKStandardWeightMap A).f n ≫
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))).inv.f (q - n)
        (homTotalComponent P X q n f))
```

### 117.2 検収と登録

コード **`98cae95ee`**（5本267行）。結合検査`/private/tmp/isw2-hom-bk-rows2.log`は終了コード0。最初の一括展開ではkernelの既定の計算上限に達したため、既存の前向き射の定理による対象成分を小補題に分けてから関手の合成則を適用した。計算上限を上げていない。

- 鍵付き対象ビルド132：**2,541 jobs・終了コード0**、監査`/private/tmp/AuditISW2G10B02StandardWeight.lean`は **10宣言（2・8）・標準三公理のみ**。
- 鍵付き対象ビルド133：**2,560 jobs・終了コード0**、監査`/private/tmp/AuditISW2G10B02HomBKRows.lean`は **5宣言（2・1・2）・標準三公理のみ**。

ログ`/private/tmp/isw2-build132.log`・`/private/tmp/isw2-build133.log`。共有鍵は返却済み。累計 **242モジュール・14,635行・2,157宣言**。新公理・sorryなし。既存宣言・⑤a・入口・公式監査・mainの変更なし。大きな監査・rootビルドなし。登録対象は117.1の5本。

## 118. B02の途中：指定BK比較の任意次数合成とKoszul符号

### 118.1 同じ行の合成計算と型

斉次射f（閉性を要求しない）の前合成を、元のHom図式の**次数ごとの加群図式**の自然変換にした。cochain合成の線形性・次数零の図式射との結合則だけを使い、これを鎖射だとは主張していない。既存の自由Yoneda後合成則と同じ同型の逆射則から、同じ逆評価がこの前合成と可換なことを示した。

これと§116のHom–Totの任意次数合成、§117の指定行表示を合わせ、元の`homToNormalizedBousfieldKan`の各行の合成に現れる符号が **(-1)^(np)** であることを証明した。符号は同じ`weightEndHomSign`の式から計算し、選び直していない。

以下も同じ名前空間、`{A : Type u}`・`[CommRing A]`。B02の同じ全パラメータ成分計算の分割（§14）。前提計算3/3・照合3/3の枠を追加しない。

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomDiagramDegreePrecompose`

```lean
def homDiagramDegreePrecompose {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q r : ℤ) (h : p + q = r)
    (f : Homogeneous P Q p) :
    doubleOppositeDiagram ((homDiagramFunctor Q).obj X) ⋙
        HomologicalComplex.eval (ModuleCat A) (.up ℤ) q ⟶
      doubleOppositeDiagram ((homDiagramFunctor P).obj X) ⋙
        HomologicalComplex.eval (ModuleCat A) (.up ℤ) r where
  app j
```

```lean
theorem freeUnitWeightEnd_inv_degree_precompose {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q r : ℤ) (h : p + q = r)
    (f : Homogeneous P Q p) (n : ℕ) (z : Homogeneous Q (X.obj ⦋n⦌) q) :
    ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram ((homDiagramFunctor Q).obj X))).inv.f q z ≫
      homDiagramDegreePrecompose X p q r h f =
    ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))).inv.f r (f.comp z h)
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomToNormalizedBKComposition`

```lean
theorem homToNormalizedBousfieldKan_rows_comp {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q : ℤ) (n : ℕ)
    (f : Homogeneous P Q p) (g : Homogeneous Q ((productTotalFunctor A).obj X) q) :
    extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) (p + q)
      ((homToNormalizedBousfieldKan P X).f (p + q) (f.comp g rfl)) n =
    ((n : ℤ) * p).negOnePow •
      (extendedChainHomRows normalizedBousfieldKanWeight
        ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
          (doubleOppositeDiagram ((homDiagramFunctor Q).obj X))) q
        ((homToNormalizedBousfieldKan Q X).f q g) n ≫
      homDiagramDegreePrecompose X p (q - n) (p + q - n) (by omega) f)
```

### 118.2 検収と登録

コード **`c2beef461`**（2本136行）。結合検査`/private/tmp/isw2-bk-hom-composition.log`は終了コード0。鍵付き対象ビルド`/private/tmp/isw2-build134.log`は **2,562 jobs・終了コード0**。新規分だけの監査`/private/tmp/AuditISW2G10B02HomBKComposition.lean`は **10宣言（7・3）・標準三公理のみ**。共有鍵は返却済み。

累計 **244モジュール・14,771行・2,167宣言**、外枠20,000行まで残り5,229行。対象一覧は`/private/tmp/isw2-g10-twohundredfortyfour-modules.txt`。新公理・sorryなし。既存宣言・⑤a・入口・公式監査・mainの変更なし。大きな監査・rootビルドなし。登録対象は118.1の2本。

### 118.3 残り

B02は未完。今回の指定Hom/BK行の合成と同じKoszul符号を、既に検証したAWの両切断和・指定tensor–Homへ接続して、元の単体的比較射の等式を閉じる。`NormalizedSimplexFreeAdjunction.lean`はA09の標準単体パラメータ側の随伴を同じ恒等生成元で照合する検査中の下書きであり、今回の検収・累計には含めない。

B03〜B08・C・Dも未完。停止点2a・2bの検収ではない。B完了時にC・Dを実測に基づいて再見積もりし、止まらずに進める。


## 119. B02の途中：元の錐代表との行の合成と標準単体の自由随伴

### 119.1 型と接続

A09の標準単体パラメータの`normalizedSimplexHomEquiv`が、同じ自由鎖随伴の恒等単体の生成元での評価に一致することを示した。二つの零延長・smart切断Hom同値は、同じ逆写像の式で照合した。自由加群・DK・切断の随伴や生成元を選び直していない。

元の`normalizedBousfieldKanRepresentative`のcochainが、同じ`homToNormalizedBousfieldKan`に移した元の閉元そのものであることも確認した。任意次数の行の合成則を指定終次数rで述べてから後の射を恒等射に特殊化し、元の錐代表の**同じcochain行**への前合成の式を得た。零次数の行の終次数`0-n`を無断で`-n`と同一視するのではなく、元の型を保持する。

以下の型は各モジュールの既存名前空間。係数環は`A : Type u`・`[CommRing A]`（暗黙／明示は各宣言のとおり）。既存の随伴・合成の法則と同じB02の証明分割。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexFreeAdjunction`

```lean
theorem normalizedSimplexHomEquiv_freeAdjunction (H : Complex A) (n : SimplexCategory)
    (f : (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj n) ⟶ H) :
    ((freeNegativeChainsAdjunction A).homEquiv
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) H f).app (Opposite.op n)
      (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 n))) =
    normalizedSimplexHomEquiv A H n f
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeComposition`

```lean
theorem homToNormalizedBousfieldKan_rows_comp_of_degree {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q r : ℤ) (h : p + q = r) (n : ℕ)
    (f : Homogeneous P Q p) (g : Homogeneous Q ((productTotalFunctor A).obj X) q) :
    extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) r
      ((homToNormalizedBousfieldKan P X).f r (f.comp g h)) n =
    ((n : ℤ) * p).negOnePow •
      (extendedChainHomRows normalizedBousfieldKanWeight
        ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
          (doubleOppositeDiagram ((homDiagramFunctor Q).obj X))) q
        ((homToNormalizedBousfieldKan Q X).f q g) n ≫
      homDiagramDegreePrecompose X p (q - n) (r - n) (by omega) f)
```

```lean
theorem normalizedBousfieldKanRepresentative_cochain (P : Complex A)
    (X : CosimplicialObject (Complex A)) (f : P ⟶ (productTotalFunctor A).obj X) :
    Cochain.ofHom (normalizedBousfieldKanRepresentative P X f) =
      (homToNormalizedBousfieldKan P X).f 0 (Cochain.ofHom f)
```

```lean
theorem homToNormalizedBousfieldKan_rows_cone (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ) :
    extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
      ((homToNormalizedBousfieldKan P X).f p f) n =
    ((n : ℤ) * p).negOnePow •
      (extendedChainHomRows normalizedBousfieldKanWeight
        ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
          (doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X)))
        0 (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) n ≫
      homDiagramDegreePrecompose X p (0 - n) (p - n) (by omega) f)
```

### 119.2 検収と登録

コード **`afb2a7c53`**（2本147行：70・77）。個別検査`/private/tmp/isw2-simplex-free-adjunction3.log`・`/private/tmp/isw2-bk-cone-composition3.log`は終了コード0。鍵付き対象ビルド`/private/tmp/isw2-build135.log`は **2,899 jobs・終了コード0**。新規分のみの監査`/private/tmp/AuditISW2G10B02ConeSimplex.lean`は **11宣言（5・6）・標準三公理のみ**。共有鍵は返却済み。

累計 **246モジュール・14,918行・2,178宣言**。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。新公理・sorryなし。大きな監査なし。登録対象は119.1の2本。

## 120. B02の途中：tensor–Hom符号の消去と実dg合成の成分

### 120.1 型と意味

元の指定BK行の任意次数合成の符号`(-1)^(np)`と、tensor逆転置の同じ重み次数に現れる符号`(-1)^((-n)p)`を合わせ、積が1になることを示した。結果は、元の錐代表のcochain行と任意のHomパラメータの**実dg合成`compose`**である。複体の`enrichedComposition`の既存成分式で、通常順の合成とcochain合成も同じ値として計算した。

これは一般の符号つき成分の式で、試験パラメータの閉性や有界性を仮定していない。B02の各AW切断の照合に使う既存構成の合成則。指定単体的射全体の一致は、まだこの一つの成分式で置き換えない。

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKTensorRow`

```lean
theorem homToNormalizedBousfieldKan_tensor_row (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ)
    (j : SimplexCategoryᵒᵖᵒᵖ) (x : ((normalizedBousfieldKanWeight (A := A)).X n).obj j) :
    let η := extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X)))
      0 (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) n
    let χ := extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
      ((homToNormalizedBousfieldKan P X).f p f) n
    ((-(n : ℤ)) * p).negOnePow • χ.app j x =
      compose A (D := Complex A) (p := p) (q := 0 - n) (n := p - n)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j) (η.app j x) f (by omega)
```

### 120.2 検収と登録

コード **`6c03058df`**（1本75行）。個別検査`/private/tmp/isw2-bk-tensor-row2.log`は終了コード0。最終ソースの鍵付き対象ビルド`/private/tmp/isw2-build136.log`は **2,564 jobs・終了コード0**。新規分のみの監査`/private/tmp/AuditISW2G10B02TensorRow.lean`は **2宣言・標準三公理のみ**。共有鍵は返却済み。

累計 **247モジュール・14,993行・2,180宣言**。一覧は`/private/tmp/isw2-g10-twohundredfortyseven-modules.txt`。外枠20,000行まで残り5,007行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。新公理・sorryなし。大きな監査・rootビルドなし。登録対象は120.1の1本。未検証下書きはない。

B02の最終の単体的射の等式、B03〜B08・C・Dは未完。次は同じパラメータ随伴・成分式を、A09の重み付き切断Hom同型と実合成の全切断和へ組み込み、反転・添字移送を含む元の比較射の等式へ戻す。

## 121. 11-14の一覧の新しい数え方の適用

調整役の連絡とmainの`coordination.md` §2の追記を読み取り確認した。既存の構成の法則（単位・余単位・自然性・係数移送・合成則・貼り合わせ）と証明分割には本数の枠を置かず、型を報告に書く。200行を超えるものは行数も記録する。本報告では引き続き各検収のファイル行数も併記する。

これまでの「前提計算3/3」「照合3/3」は当時の検収の記録として残すが、**今後の停止判定には使わない**。既存の合成を名前で固定した定義や、指定射の成分評価を分割した今回の補題を、新しい独立の構成の導入とは扱わない。既存構成の法則ではない新しい構成・定理、承認済みまとまりの外、外枠に届く所では停止して報告する。B01〜B08・C01〜C07・D01〜D08と停止点2a・2b、外枠20,000行は維持する。

mainは凍結中なので、追記の確認は読み取りだけとしmergeしていない。自分の枝で作業とコミットを続け、鍵は`--wait 3600`でビルド・小監査の間だけ持つ。


## 122. B02の途中：全標準単体の自由随伴評価と図式逆転置

A09の元の比較を、同じAW前合成の自由鎖随伴へ戻す式を全標準単体で証明した。頂点だけの同定ではなく、元のYoneda射・宇宙同型・指定自由随伴を保持している。図式tensor–Homの逆射についても、各点の斉次tensor上のKoszul符号を元の逆転置の成分則で計算した。いずれも既存構成の余単位・評価・合成則で、11-14の新しい数え方に従う。B02の指定単体的射全体の等式は未完。

### 122.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LiftedStandardSimplexHomEvaluation`（60行）

```lean
theorem liftedStandardSimplexHomIso_hom_apply (Z : SSet.{u}) (n : SimplexCategory)
    (f : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⟶ Z) :
    (liftedStandardSimplexHomIso Z).hom.app (Opposite.op n) f =
      f.app (Opposite.op n) (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 n)))

theorem normalizedSimplexHomEquiv_via_freeAdjunction (A : Type u) [CommRing A]
    (H : Complex A) (n : SimplexCategory)
    (f : (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj n) ⟶ H) :
    (liftedStandardSimplexHomIso ((truncatedDoldKanFunctor A).obj H)).hom.app (Opposite.op n)
      ((freeNegativeChainsAdjunction A).homEquiv
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) H f) =
    normalizedSimplexHomEquiv A H n f

theorem liftedStandardSimplexHomIso_yoneda (Z : SSet.{u}) (n : SimplexCategory)
    (f : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⟶ Z) :
    liftedStandardSimplexIso.{u}.hom.app n ≫
      SSet.yonedaEquiv.symm ((liftedStandardSimplexHomIso Z).hom.app (Opposite.op n) f) =
    f

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductSectionsHomEvaluation`（61行）

```lean
theorem weightedFreeChainsAdjunction_uncurry (W : J ⥤ SSet.{u})
    (Y : SSet.{u}) (Q : J ⥤ Complex A)
    (f : freeNegativeChainsDiagram (A := A) (W ⊗ (Functor.const J).obj Y) ⟶ Q) :
    weightedSectionsUncurry
      (((weightedSectionsAdjunction W).comp (freeNegativeChainsDiagramAdjunction A J)).homEquiv
        Y Q f) =
    (freeNegativeChainsDiagramAdjunction A J).homEquiv (W ⊗ (Functor.const J).obj Y) Q f

theorem freeProductSectionsHomIso_uncurry (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (n : SimplexCategory) (f : (freeProductFrame A W (liftedStandardSimplexParameter J)).obj n ⟶ Q) :
    weightedSectionsUncurry
      (liftedStandardSimplexIso.{u}.hom.app n ≫ SSet.yonedaEquiv.symm
        ((freeProductSectionsHomIso A W Q).hom.app (Opposite.op n) f)) =
    (freeNegativeChainsDiagramAdjunction A J).homEquiv
      (W ⊗ (Functor.const J).obj
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n))) Q f

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedWeightSectionEvaluation`（56行）

```lean
theorem normalizedWeightSectionMap_hom_uncurry (W : J ⥤ SSet.{u})
    (Q : J ⥤ Complex A) (φ : simplicialRingCoefficient.{u} →+* A) (n : SimplexCategory)
    (f : (freeTensorFrame A W (liftedStandardSimplexParameter J)).obj n ⟶ Q) :
    weightedSectionsUncurry
      (liftedStandardSimplexIso.{u}.hom.app n ≫ SSet.yonedaEquiv.symm
        ((normalizedWeightSectionMap A W Q φ).app (Opposite.op n)
          ((freeTensorDiagramHomIso.{u,u} A Q W).hom.app (Opposite.op n) f))) =
    (freeNegativeChainsDiagramAdjunction A J).homEquiv
      (W ⊗ (Functor.const J).obj
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n))) Q
      (freeProductDiagramAW φ W ((liftedStandardSimplexParameter J).obj n) ≫ f)

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorHomComponents`（40行）

```lean
theorem diagramTensorLinearHomEquiv_symm_app
    (f : T ⟶ linearHomComplex A ((E).obj P) ((E).obj Q)) (j : J) :
    ((diagramTensorLinearHomEquiv P Q T).symm f).app j =
      (tensorHomEquiv (P.obj j) T (Q.obj j)).symm
        ((diagramHomFamilyOfHom P Q T f).val j)

theorem diagramTensorLinearHomEquiv_symm_component
    (f : T ⟶ linearHomComplex A ((E).obj P) ((E).obj Q)) (j : J)
    (i q n : ℤ) (hn : i + q = n) (y : (P.obj j).X i) (x : T.X q) :
    (((diagramTensorLinearHomEquiv P Q T).symm f).app j).f n
      (HomologicalComplex.ιTensorObj (P.obj j) T i q n hn (y ⊗ₜ[A] x)) =
      (i * q).negOnePow • (diagramCochainAt P Q (f.f q x) j).v i n hn y

```

### 122.2 検収と残り

コード **`18d19ebf0`**。鍵付き対象ビルド `/private/tmp/isw2-build137.log` は **2,645 jobs・終了コード0**。新規4本のみの監査 `/private/tmp/AuditISW2G10B02SectionEvaluation.lean` は **9宣言（3・3・1・2）、標準三公理のみ**。共有鍵は返却済み。個別検査の図式逆転置も終了コード0。

新規4本217行、累計 **251モジュール・15,210行・2,189宣言**。一覧 `/private/tmp/isw2-g10-twohundredfiftyone-modules.txt`。既存宣言・⑤a・入口・公式監査・mainは変更していない。計算上限を上げず、sorry・新公理0。rootビルド・大きな監査なし。B02、B03〜B08、C、Dは引き続き未完。次は同じtensorパラメータの逆射を各点で展開し、実dg合成の各AW切断和と照合する。

## 123. B02の途中：同じΓパラメータ像の逆転置成分

指定自由tensor Hom同型の逆射を各点で元の図式逆転置へ戻した。標準単体の自由tensor比較は各点の恒等射であり、同じ実Γの射の像を正規化標準単体Hom同値で戻すと元の複体射の後合成となる。この二つの式から、A09へ渡す全パラメータ像の斉次tensor成分を、元の複体射の各次数の作用で計算した。既存構成の自然性・評価・合成則で、新しい数学のまとまりを足していない。

型推論の途中で、恒等tensor則に対象を射として誤って渡したため時間切れが出た。正しい既存則 `tensorHom_id` と `id_whiskerRight` に直し、対象・次数を明記して解消した。計算上限は変更していない。

### 123.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexInverseNaturality`（34行）

```lean
theorem normalizedSimplexHomEquiv_symm_map {K L : Complex A}
    (g : K ⟶ L) (n : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj K).obj (Opposite.op n)) :
    (normalizedSimplexHomEquiv A L n).symm
      (((truncatedDoldKanFunctor A).map g).app (Opposite.op n) α) =
      (normalizedSimplexHomEquiv A K n).symm α ≫ g

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeTensorHomInverseEvaluation`（102行）

```lean
theorem freeTensorStandardSimplexIso_hom_app (W : J ⥤ SSet.{u})
    (n : SimplexCategory) (j : J) :
    ((freeTensorStandardSimplexIso A J W).hom.app n).app j = 𝟙 _

theorem freeTensorDiagramHomIso_inv_app (W : J ⥤ SSet.{u})
    (Q : J ⥤ Complex A) (n : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj
      (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
        ((E).obj Q))).obj (Opposite.op n)) (j : J) :
    ((freeTensorDiagramHomIso A Q W).inv.app (Opposite.op n) α).app j =
      ((diagramTensorLinearHomEquiv (freeNegativeChainsDiagram (A := A) W) Q
        ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
          (SSet.stdSimplex.obj n))).symm
        ((normalizedSimplexHomEquiv A
          (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
            ((E).obj Q)) n).symm α)).app j

theorem freeTensorDiagramHomIso_inv_component (W : J ⥤ SSet.{u})
    (Q : J ⥤ Complex A) (m : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj
      (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
        ((E).obj Q))).obj (Opposite.op m)) (j : J)
    (i q n : ℤ) (hn : i + q = n)
    (y : ((freeNegativeChainsDiagram (A := A) W).obj j).X i)
    (x : ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj m)).X q) :
    (((freeTensorDiagramHomIso A Q W).inv.app (Opposite.op m) α).app j).f n
      (HomologicalComplex.ιTensorObj
        ((freeNegativeChainsDiagram (A := A) W).obj j)
        ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
          (SSet.stdSimplex.obj m)) i q n hn (y ⊗ₜ[A] x)) =
      (i * q).negOnePow •
        (diagramCochainAt (freeNegativeChainsDiagram (A := A) W) Q
          (((normalizedSimplexHomEquiv A
            (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
              ((E).obj Q)) m).symm α).f q x) j).v i n hn y

theorem freeTensorDiagramHomIso_inv_map_component (W : J ⥤ SSet.{u})
    (Q : J ⥤ Complex A) (K : Complex A)
    (g : K ⟶ linearHomComplex A ((E).obj
      (freeNegativeChainsDiagram (A := A) W)) ((E).obj Q))
    (m : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj K).obj (Opposite.op m))
    (j : J) (i q n : ℤ) (hn : i + q = n)
    (y : ((freeNegativeChainsDiagram (A := A) W).obj j).X i)
    (x : ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj m)).X q) :
    (((freeTensorDiagramHomIso A Q W).inv.app (Opposite.op m)
      (((truncatedDoldKanFunctor A).map g).app (Opposite.op m) α)).app j).f n
      (HomologicalComplex.ιTensorObj
        ((freeNegativeChainsDiagram (A := A) W).obj j)
        ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
          (SSet.stdSimplex.obj m)) i q n hn (y ⊗ₜ[A] x)) =
      (i * q).negOnePow •
        (diagramCochainAt (freeNegativeChainsDiagram (A := A) W) Q
          (g.f q (((normalizedSimplexHomEquiv A K m).symm α).f q x)) j).v i n hn y

```

### 123.2 検収と残り

コード **`c055f145c`**（2本136行）。結合個別検査 `/private/tmp/isw2-free-tensor-map-combined.log` は終了コード0。最終ソースの鍵付き対象ビルド `/private/tmp/isw2-build138.log` は **2,567 jobs・終了コード0**。新規分だけの監査 `/private/tmp/AuditISW2G10B02InverseParameter.lean` は **5宣言（1・4）、標準三公理のみ**。鍵は `--wait 3600`、一枚の整理券、実行1,700秒上限で使用し、返却済み。

累計 **253モジュール・15,346行・2,194宣言**。外枠20,000行まで残り4,654行。一覧 `/private/tmp/isw2-g10-twohundredfiftythree-modules.txt`。既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0、大きな監査・rootビルドなし。未検証下書きはない。

B02の全単体的射の等式、B03〜B08・C・Dは未完。次は今回の逆転置成分と§120の実dg合成成分を、§115のAW全切断和で照合する。Moore射影を無条件に消すことはせず、元の射影・包含と係数比較を保持する。停止点2a・2bの仕様と一覧は弱めない。

## 124. B02の途中：実標準AW合成の負次数逆随伴を全次数で評価

自由負次数鎖の指定逆随伴を、同じMoore逆随伴の延長とsmart切断包含の合成に分割した。射影生成元の評価は同じΓのMoore射影と余単位を通して計算した。切断包含は、境界外では元の項同型、零次数では既存のcycles包含として保持した。これを元の標準DK同型の成分式に適用し、**自由負次数逆随伴の全次数の生成元像が実標準Homの最上位成分**であることを証明した。

実AW合成への適用では、正次数・零次数を統一して同じ全切断和が得られる。これは§114のMoore側の評価を、今回必要な元の負次数複体の射へ輸送したもの。B02の証明分割と既存構成の合成・評価則であり、別の比較射や新しい数学のまとまりを導入していない。

### 124.1 登録対象・行数・型

`SerrePositivity.HomologicalAlgebra.ComplexLimits.TruncationInclusionComponents`（47行）

```lean
theorem truncLEToRestriction_nonboundary (H : Complex A)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncLE]
    {n : ℕ} {i : ℤ} (hi : e.f n = i) (hn : ¬ e.BoundaryLE n) :
    (H.truncLE'ToRestriction e).f n ≫ (H.restrictionXIso e hi).hom =
      (H.truncLE'XIso e hi hn).hom

theorem extendedTruncationInclusion_nonboundary (H : Complex A)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncLE]
    {n : ℕ} {i : ℤ} (hi : e.f n = i) (hn : ¬ e.BoundaryLE n) :
    ((H.truncLE' e).extendXIso e hi).inv ≫
      ((H.truncLEIso e).inv ≫ HomologicalComplex.ιTruncLE H e).f i =
      (H.truncLE'XIso e hi hn).hom

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeNegativeHomDecomposition`（114行）

```lean
theorem freeNegativeChainsAdjunction_symm_moore (S : SSet.{u}) (H : Complex A)
    (f : S ⟶ (truncatedDoldKanFunctor A).obj H) :
    ((freeNegativeChainsAdjunction A).homEquiv S H).symm f =
      ((negativeExtendTruncationAdjunction (ModuleCat A)).homEquiv
        ((normalizedMooreComplex (ModuleCat A)).obj (S ⋙ ModuleCat.free A)) H).symm
        (((freeMooreChainsAdjunction (R := A)).homEquiv S
          (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).symm f)

theorem negativeExtendTruncationAdjunction_symm_inclusion
    (L : ChainComplex (ModuleCat A) ℕ) (H : Complex A)
    (g : L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0)) :
    ((negativeExtendTruncationAdjunction (ModuleCat A)).homEquiv L H).symm g =
      extendMap g ComplexShape.embeddingDownNat ≫
        truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
          embeddingDownNat_eq_upIntLE_zero H

theorem freeNegativeChainsAdjunction_symm_inclusion (S : SSet.{u}) (H : Complex A)
    (f : S ⟶ (truncatedDoldKanFunctor A).obj H) :
    ((freeNegativeChainsAdjunction A).homEquiv S H).symm f =
      extendMap (((freeMooreChainsAdjunction (R := A)).homEquiv S
        (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).symm f)
          ComplexShape.embeddingDownNat ≫
        truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
          embeddingDownNat_eq_upIntLE_zero H

theorem freeNegativeChainsAdjunction_symm_generator_eval (S : SSet.{u}) (H : Complex A)
    (f : S ⟶ (truncatedDoldKanFunctor A).obj H) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n⦌)) :
    (((freeNegativeChainsAdjunction A).homEquiv S H).symm f).f (-(n : ℤ))
      (freeNegativeGenerator S n s) =
      (((H.truncLE' (ComplexShape.embeddingUpIntLE 0)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
          embeddingDownNat_eq_upIntLE_zero H).f (-(n : ℤ)))
        (((DoldKan.PInftyToNormalizedMooreComplex
          (Abelian.DoldKan.Γ.obj (H.truncLE' (ComplexShape.embeddingUpIntLE 0)))).f n ≫
          (Abelian.DoldKan.equivalence.counitIso.hom.app
            (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).f n)
              (f.app (Opposite.op ⦋n⦌) s))

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeNegativeStandardHomEvaluation`（92行）

```lean
theorem connectiveHom_negative_inclusion (x y : D) (n : ℕ) :
    (((homObject R D x y).truncLE' (ComplexShape.embeddingUpIntLE 0)).extendXIso
      ComplexShape.embeddingDownNat (i := n + 1) (i' := -(n + 1 : ℤ)) (by simp)).inv ≫
      (truncationExtendedInclusionOfShape R ComplexShape.embeddingDownNat
        embeddingDownNat_eq_upIntLE_zero (homObject R D x y)).f (-(n + 1 : ℤ)) =
      (connectiveHomComplex_positiveIso (R := R) x y n).hom

theorem freeNegativeStandardHom_generator_eval (S : SSet.{u}) (x y : D)
    (f : S ⟶ standardHomSpace (R := R) x y) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n⦌)) :
    (((freeNegativeChainsAdjunction R).homEquiv S (homObject R D x y)).symm
      (f ≫ standardDoldKanSpaceMap x y)).f (-(n : ℤ))
        (freeNegativeGenerator S n s) =
      standardTopEval (R := R) x y n (f.app _ s)

theorem freeNegativeStandardAW_generator_eval (S T : SSet.{u}) (x y z : D)
    (g : S ⟶ standardHomSpace (R := R) y z)
    (f : T ⟶ standardHomSpace (R := R) x y) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n⦌)) (t : T.obj (Opposite.op ⦋n⦌)) :
    let h := (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := R) x y z
    (((freeNegativeChainsAdjunction R).homEquiv (S ⊗ T) (homObject R D x z)).symm
      (h ≫ standardDoldKanSpaceMap x z)).f (-(n : ℤ))
        (freeNegativeGenerator (S ⊗ T) n (s, t)) =
      ∑ c : (Finset.univ : Finset (Fin (n + 1))),
        awTerm (g.app _ s).val (f.app _ t).val Finset.univ c (-(n : ℤ)) (by simp)

```

### 124.2 検収と残り

コード **`2b2d1f50c`**（新規3本253行）。結合個別検査 `/private/tmp/isw2-negative-standard-aw-combined.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build139.log` は **4,164 jobs・終了コード0**。新規分だけの監査 `/private/tmp/AuditISW2G10B02NegativeStandard.lean` は **15宣言（2・8・5）、標準三公理のみ**。共有鍵は `--wait 3600`・一枚の整理券・実行1,700秒上限で使用し、返却済み。

累計 **256モジュール・15,599行・2,209宣言**。一覧 `/private/tmp/isw2-g10-twohundredfiftysix-modules.txt`。外枠まで残り4,401行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。

B02、B03〜B08・C・Dは未完。次の照合は、raw AWの各成分の等式を先に示し、**元のMoore包含を前合成して**正規化側の等式へ制限する。包含→射影の合成が恒等である指定分裂則を使い、P∞がAWと可換という未証明の仮定は置かない。

## 125. B02の途中：raw AW成分等式のMoore制限

raw AWの成分の等式を、元のMoore包含の前合成で正規化AWへ制限する式を証明した。係数移送は既存の加法関手と指定Moore比較で行い、包含→射影が恒等となる分裂則を使う。さらに同じ式を元の負次数AWに適用し、指定延長項同型と係数tensor同型を保持した成分の式へ戻した。**AWとP∞の可換性を仮定する必要はない**。B02に含まれる二つの既存射の照合の証明分割・合成則である。

### 125.1 登録対象・行数・型

`SerrePositivity.HomologicalAlgebra.MappedNormalizedAWRestriction`（61行）

```lean
theorem mappedNormalizedAlexanderWhitney_f_eq_of_raw (n : ℕ) (T : B)
    (t : F.obj ((chainIntegerTensor ((normalizedMooreComplex _).obj C)
      ((normalizedMooreComplex _).obj D)).X n) ⟶ T)
    (h : ((normalizedMooreComplex B).obj (simplicialIntegerTensor C D ⋙ F)).X n ⟶ T)
    (hraw : F.map ((alexanderWhitney C D).f n ≫
        (chainIntegerTensorMap (PInftyToNormalizedMooreComplex C)
          (PInftyToNormalizedMooreComplex D)).f n) ≫ t =
      F.map ((PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D)).f n) ≫
        (normalizedMooreMapIso F (simplicialIntegerTensor C D)).hom.f n ≫ h) :
    (mappedNormalizedAlexanderWhitney F C D).f n ≫ t = h

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeAWRestriction`（65行）

```lean
theorem negativeCoefficientAlexanderWhitney_f_eq_of_raw (n : ℕ) (T : ModuleCat A)
    (t : (HomologicalComplex.tensorObj
      (((normalizedMooreComplex (ModuleCat A)).obj (C ⋙ integerCoefficientExtension φ)).extend
        ComplexShape.embeddingDownNat)
      (((normalizedMooreComplex (ModuleCat A)).obj (D ⋙ integerCoefficientExtension φ)).extend
        ComplexShape.embeddingDownNat)).X (-(n : ℤ)) ⟶ T)
    (h : ((normalizedMooreComplex (ModuleCat A)).obj
      (simplicialIntegerTensor C D ⋙ integerCoefficientExtension φ)).X n ⟶ T)
    (hraw : (integerCoefficientExtension φ).map ((alexanderWhitney C D).f n ≫
        (chainIntegerTensorMap (PInftyToNormalizedMooreComplex C)
          (PInftyToNormalizedMooreComplex D)).f n) ≫
        ((((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
          (chainIntegerTensor ((normalizedMooreComplex _).obj C)
            ((normalizedMooreComplex _).obj D))).extendXIso ComplexShape.embeddingDownNat
              (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (negativeMooreTensorCoefficientIso φ C D).hom.f (-(n : ℤ)) ≫ t =
      (integerCoefficientExtension φ).map
        ((PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D)).f n) ≫
        (normalizedMooreMapIso (integerCoefficientExtension φ)
          (simplicialIntegerTensor C D)).hom.f n ≫ h) :
    (((normalizedMooreComplex (ModuleCat A)).obj
      (simplicialIntegerTensor C D ⋙ integerCoefficientExtension φ)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
      (negativeCoefficientAlexanderWhitney φ C D).f (-(n : ℤ)) ≫ t = h

```

### 125.2 検収と残り

コード **`e6a651b2e`**（新規2本126行）。結合個別検査 `/private/tmp/isw2-negative-aw-restrict-combined.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build140.log` は **2,239 jobs・終了コード0**。新規分だけの監査 `/private/tmp/AuditISW2G10B02AWRestriction.lean` は **3宣言（2・1）、標準三公理のみ**。共有鍵は返却済み。

累計 **258モジュール・15,725行・2,212宣言**。一覧 `/private/tmp/isw2-g10-twohundredfiftyeight-modules.txt`。既存宣言・⑤a・入口・公式監査・mainの変更なし。計算上限を上げず、sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。B02の最終等式とB03〜B08・C・Dは未完。

次は標準単体Homの逆同値を同じ自由随伴へ戻し、§124の最上位評価をA09のパラメータに直接適用する。raw成分の照合の仮定そのものは、§115の全切断和と§120の実dg合成成分を使って別途閉じる必要があり、今回の制限則だけでB02を完了とは数えない。

## 126. B02の途中：元の標準単体パラメータを指定自由随伴へ戻す

正規化標準単体Hom同値の逆射を、同じ持ち上げ標準単体Hom同型の逆射と自由鎖随伴の逆射の合成に同定した。元の実標準Homから来る全パラメータについて、その逆射の各射影生成元の像が実標準Homの最上位成分になることを、§124の全次数評価へ接続した。これでA09側のパラメータを試験頂点だけでなく全標準単体で扱える。

重いHom対象で逆射則を直接elaborateすると200,000 heartbeatの上限に達したため、同じ逆射則を任意の台単体集合で一つの部分補題に固定して解消した。新しい数学ではなく同じ証明の分割であり、計算上限を上げていない。

### 126.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexInverseAdjunction`（73行）

```lean
theorem normalizedSimplexHomEquiv_symm_freeAdjunction (H : Complex A)
    (n : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj H).obj (Opposite.op n)) :
    (normalizedSimplexHomEquiv A H n).symm α =
      ((freeNegativeChainsAdjunction A).homEquiv
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) H).symm
        ((liftedStandardSimplexHomIso ((truncatedDoldKanFunctor A).obj H)).inv.app
          (Opposite.op n) α)

theorem liftedStandardSimplexHomIso_inv_hom_apply (Z : SSet.{u}) (m : SimplexCategory)
    (t : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m) ⟶ Z) :
    (liftedStandardSimplexHomIso Z).inv.app (Opposite.op m)
      ((liftedStandardSimplexHomIso Z).hom.app (Opposite.op m) t) = t

theorem normalizedSimplexHomEquiv_symm_standard_generator
    {D : Type v} [DGCategory A D] (x y : D) (m : SimplexCategory)
    (f : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m) ⟶
      standardHomSpace (R := A) x y) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)).obj
      (Opposite.op ⦋n⦌)) :
    ((normalizedSimplexHomEquiv A (homObject A D x y) m).symm
      ((liftedStandardSimplexHomIso
        ((truncatedDoldKanFunctor A).obj (homObject A D x y))).hom.app (Opposite.op m)
          (f ≫ standardDoldKanSpaceMap x y))).f (-(n : ℤ))
            (freeNegativeGenerator
              ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) n s) =
      standardTopEval (R := A) x y n (f.app _ s)

```

### 126.2 検収と残り

コード **`3f092fcc9`**（1本73行）。個別検査 `/private/tmp/isw2-simplex-inverse-adjunction3.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build141.log` は **4,197 jobs・終了コード0**。新規分だけの監査 `/private/tmp/AuditISW2G10B02SimplexInverse.lean` は **3宣言・標準三公理のみ**。共有鍵は返却済み。

累計 **259モジュール・15,798行・2,215宣言**。一覧 `/private/tmp/isw2-g10-twohundredfiftynine-modules.txt`。外枠20,000行まで残り4,202行。既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0、大きな監査・rootビルドなし。未検証下書きはない。

B02の全体等式とB03〜B08・C・Dは未完で、Dまでの目標は維持する。次の具体的な接続は以下。

1. 実標準Homの前面・後面への引き戻しの最上位成分を、`awTerm`の接頭・接尾集合の成分へ合わせる（`standardPullback_val`・`pullback_component_of_inj`・`awFront`・`awBack`の既存評価則）。
2. §123の自由tensor逆射成分、§120の実dg合成成分、今回のパラメータ評価を§115のraw AW全切断和で照合する。
3. raw等式を§125の指定Moore包含による制限へ渡し、元の正規化側の複体射を同定する。
4. 指定自由随伴とweighted uncurryの単射性で元の全単体的射へ戻し、既存の反転・添字移送の等式を使ってB02を閉じる。

これらはB02の指定された二つの既存比較の照合の内訳であり、raw等式や最後の輸送を検証済みとは数えない。

## 127. B02の途中：AW前面・後面の各切断と全切断和の照合

指定`awFront`・`awBack`の単射性、全頂点の像、接頭・接尾集合の濃度を計算した。既存の単射引き戻しの評価則から、前面・後面の最上位成分を同じ接頭・接尾集合の成分に同定し、既存の異種等号の合成則で`awTerm`がこれらの通常順合成であることを証明した。

各切断のtensor像がこの実合成と一致するという条件を置けば、§115のraw自由AWの全切断和と§124の実標準AWの逆随伴評価が一致する貼り合わせ則も証明した。**切断条件自体はまだ閉じていない**。これをB02の無条件の全体等式の代わりにはしない。すべて既存構成の評価・合成・貼り合わせの法則、または同じ照合の証明分割であり、新しい数学のまとまりは追加していない。

### 127.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.AWCutFaces`（152行）

```lean
theorem awFront_injective (n : ℕ) (c : Fin (n + 1)) :
    Function.Injective (awFront n c).toOrderHom

theorem awBack_injective (n : ℕ) (c : Fin (n + 1)) :
    Function.Injective (awBack n c).toOrderHom

theorem awFront_univ_image (n : ℕ) (c : Fin (n + 1)) :
    (Finset.univ : Finset (Fin (c.val + 1))).image (awFront n c).toOrderHom =
      Finset.univ.filter (· ≤ c)

theorem awBack_univ_image (n : ℕ) (c : Fin (n + 1)) :
    (Finset.univ : Finset (Fin (n - c.val + 1))).image (awBack n c).toOrderHom =
      Finset.univ.filter (c ≤ ·)

theorem awFront_filter_card (n : ℕ) (c : Fin (n + 1)) :
    (Finset.univ.filter (· ≤ c)).card = c.val + 1

theorem awBack_filter_card (n : ℕ) (c : Fin (n + 1)) :
    (Finset.univ.filter (c ≤ ·)).card = n - c.val + 1

theorem standardTopEval_awFront {n : ℕ} (f : StandardSimplex R x y n)
    (c : Fin (n + 1)) :
    standardTopEval (R := R) x y c.val (standardPullback (awFront n c).toOrderHom f) =
      f.val.component (Finset.univ.filter (· ≤ c)) (-(c.val : ℤ))
        (AWIndex.left_nonempty (Finset.mem_univ c))
        (by rw [awFront_filter_card]; simp)

theorem standardTopEval_awBack {n : ℕ} (f : StandardSimplex R x y n)
    (c : Fin (n + 1)) :
    standardTopEval (R := R) x y (n - c.val) (standardPullback (awBack n c).toOrderHom f) =
      f.val.component (Finset.univ.filter (c ≤ ·)) (-((n - c.val : ℕ) : ℤ))
        (AWIndex.right_nonempty (Finset.mem_univ c))
        (by rw [awBack_filter_card]; simp)

theorem awTerm_univ_top_faces {x y z : D} {n : ℕ}
    (g : StandardSimplex R y z n) (f : StandardSimplex R x y n) (c : Fin (n + 1)) :
    awTerm g.val f.val Finset.univ ⟨c, Finset.mem_univ c⟩ (-(n : ℤ)) (by simp) =
      compose R (p := -((n - c.val : ℕ) : ℤ)) (q := -(c.val : ℤ)) (n := -(n : ℤ))
        (standardTopEval (R := R) y z c.val (standardPullback (awFront n c).toOrderHom g))
        (standardTopEval (R := R) x y (n - c.val)
          (standardPullback (awBack n c).toOrderHom f))
        (by have := c.isLt; omega)

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeAWStandardCutComparison`（76行）

```lean
theorem freeProductAW_standard_raw_value
    (φ : simplicialRingCoefficient.{u} →+* A) (W Y : SSet.{u}) (x y z : D)
    (g : W ⟶ standardHomSpace (R := A) y z)
    (f : Y ⟶ standardHomSpace (R := A) x y)
    (t : freeNegativeChains (A := A) W ⊗ freeNegativeChains (A := A) Y ⟶
      homObject A D x z) (n : ℕ)
    (w : W.obj (Opposite.op ⦋n⦌)) (a : Y.obj (Opposite.op ⦋n⦌))
    (hcut : ∀ c : Fin (n + 1),
      t.f (-(n : ℤ))
        (ιTensorObj (freeNegativeChains (A := A) W) (freeNegativeChains (A := A) Y)
          (-(c.val : ℤ)) (-((n - c.val : ℕ) : ℤ)) (-(n : ℤ))
          (by have := awDegrees n c; omega)
          (freeNegativeGenerator W c.val (W.map (awFront n c).op w) ⊗ₜ[A]
            freeNegativeGenerator Y (n - c.val) (Y.map (awBack n c).op a))) =
        compose A (p := -((n - c.val : ℕ) : ℤ)) (q := -(c.val : ℤ)) (n := -(n : ℤ))
          (standardTopEval (R := A) y z c.val
            (standardPullback (awFront n c).toOrderHom (g.app _ w)))
          (standardTopEval (R := A) x y (n - c.val)
            (standardPullback (awBack n c).toOrderHom (f.app _ a)))
          (by have := c.isLt; omega)) :
    let F := integerCoefficientExtension φ
    let C := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace W)
    let E := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)
    let h := (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := A) x y z
    t.f (-(n : ℤ))
      ((F.map (alexanderWhitneyApp (linearizedSpace W) (linearizedSpace Y) n ≫
        (chainIntegerTensorMap
          (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace W))
          (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace Y))).f n) ≫
        (((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor C E)).extendXIso
          ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (negativeMooreTensorCoefficientIso φ (linearizedSpace W) (linearizedSpace Y)).hom.f
          (-(n : ℤ)) ≫
        (tensorIso (integerCoefficientFreeChainsIso φ W)
          (integerCoefficientFreeChainsIso φ Y)).hom.f (-(n : ℤ)))
        (coefficientUnit φ (integerTensor ((linearizedSpace W).obj (Opposite.op ⦋n⦌))
          ((linearizedSpace Y).obj (Opposite.op ⦋n⦌)))
            (integerGenerator w ⊗ₜ[ℤ] integerGenerator a))) =
      (((freeNegativeChainsAdjunction A).homEquiv (W ⊗ Y) (homObject A D x z)).symm
        (h ≫ standardDoldKanSpaceMap x z)).f (-(n : ℤ))
          (freeNegativeGenerator (W ⊗ Y) n (w, a))

```

### 127.2 検収と残り

コード **`bb6f33eb2`**（新規2本228行）。結合個別検査 `/private/tmp/isw2-aw-standard-cut-combined.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build142.log` は **4,167 jobs・終了コード0**。新規分だけの監査 `/private/tmp/AuditISW2G10B02AWCuts.lean` は **16宣言（13・3）、標準三公理のみ**。鍵は返却済み。

累計 **261モジュール・16,026行・2,231宣言**。一覧 `/private/tmp/isw2-g10-twohundredsixtyone-modules.txt`。外枠まで残り3,974行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。B02、B03〜B08・C・Dは未完。

次は指定重み比較の逆射とMoore反転による前合成を、既存BK行のtensor合成則へ運ぶ。零延長した鎖複体の行表示の始域射自然性で同じ前合成を扱い、§120の実dg合成式を保持する。

## 128. 11-14のレーン目標と一覧の進捗表示

mainの `formalization-plans/stage-ii/lane-goals-2026-11-14.md` の共通規則と③-bを読み取り確認した。mainは凍結中でmergeしていない。B02〜B08、C01〜C07、D01〜D08を順に進め、B完了時にC・Dを再見積もり、B・C完了を停止点2a、D完了を停止点2bとする。2bの後に3b-4の段0（§38.2の1・2）を紙で出し、そこで止まる。既存FramedLimit*・CAlgUnderlyingDerivedComparison・無条件のcAlgForgetDerived_mapJoinCone_isLimitを再利用する。B4の指示が来たら先に従う。

一覧：済み 14／全体 36（うち追加 1）

数える単位は§73のA01〜A12（12項目）、B01〜B08（8）、C01〜C07（7）、D01〜D08（8）、承認追加A05a（1）。A01の二宣言など同じ親IDの複数の宣言は一つの項目にまとめる。A01〜A12とA05a、B01が済み。B02の途中の評価・自然性・合成・貼り合わせの法則と証明分割は分母にも分子にも加えない。B02〜B08・C・Dの22項目は未完。

外枠20,000行、実測16,026行（§127）、計算上限・既存宣言・⑤a・入口・公式監査・mainを変えない規則は維持する。次の対象ビルドから `--class impl --wait 3600` を明記する。

## 129. B02の途中：指定重みの始域射へBK合成則を運ぶ

一覧：済み 14／全体 36（うち追加 1）

零延長した鎖複体からの斉次射の行表示が、同じ始域射による前合成と可換であることを証明した。これにより元のBK行の合成則とtensor符号消去則を任意の指定重み始域射へ運べる。右辺の錐代表も同じ始域射を前合成したもので、別の錐や同値を選んでいない。B02の指定係数比較・Moore反転を通すための既存自然性・合成則で、ID付き一覧の追加ではない。

### 129.1 登録対象・行数・型

`SerrePositivity.HomologicalAlgebra.ExtendedChainHomSourceMap`（28行）

```lean
theorem extendedChainHomRows_precomp (L K : ChainComplex C ℕ) (H : CochainComplex C ℤ)
    (σ : L.extend ComplexShape.embeddingDownNat ⟶ K.extend ComplexShape.embeddingDownNat)
    (q : ℤ) (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q) (n : ℕ) :
    extendedChainHomRows L H q ((Cochain.ofHom σ).comp z (zero_add q)) n =
      (negativeChainRowIso L n).inv ≫ σ.f (-(n : ℤ)) ≫
        (negativeChainRowIso K n).hom ≫ extendedChainHomRows K H q z n

```

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKSourceComposition`（65行）

```lean
theorem homToNormalizedBousfieldKan_rows_source_cone (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ) :
    extendedChainHomRows L ((E).obj (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
      ((Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)) n =
      ((n : ℤ) * p).negOnePow •
        (extendedChainHomRows L
          ((E).obj (doubleOppositeDiagram
            ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X))) 0
          ((Cochain.ofHom σ).comp
            (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) (zero_add 0)) n ≫
          homDiagramDegreePrecompose X p (0 - n) (p - n) (by omega) f)

theorem homToNormalizedBousfieldKan_tensor_source_row (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ)
    (j : SimplexCategoryᵒᵖᵒᵖ) (x : (L.X n).obj j) :
    let η := extendedChainHomRows L
      ((E).obj (doubleOppositeDiagram
        ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X))) 0
      ((Cochain.ofHom σ).comp
        (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) (zero_add 0)) n
    let χ := extendedChainHomRows L
      ((E).obj (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
      ((Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)) n
    ((-(n : ℤ)) * p).negOnePow • χ.app j x =
      compose A (D := Complex A) (p := p) (q := 0 - n) (n := p - n)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j) (η.app j x) f (by omega)

```

### 129.2 検収と残り

コード **`9c2a7c160`**（新規2本93行）。結合個別検査 `/private/tmp/isw2-bk-source-composition-combined2.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build143.log` は **2,566 jobs・終了コード0**。新規分のみの監査 `/private/tmp/AuditISW2G10B02BKSourceComposition.lean` は **4宣言（1・3）、標準三公理のみ**。鍵は `--class impl --wait 3600` でビルド・監査の間だけ使用し返却済み。

累計 **263モジュール・16,119行・2,235宣言**。一覧 `/private/tmp/isw2-g10-twohundredsixtythree-modules.txt`。外枠まで残り3,881行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0、rootビルド・大きな監査なし。未検証下書きはない。

B02の全体等式とB03〜B08・C・Dは未完。次はA12の実際の反転・係数重み移送のHom成分を、同じ二つの重み射の合成による前合成とAsSmall制限に明示的に分解する。

## 130. B02の途中：A12の実際の全次数の始域移送を評価

一覧：済み 14／全体 36（うち追加 1）

A12で使う `reflectedNormalizedBKSmallHomIso` の順射と `normalizedBKReverseHomotopyEquiv` の順射の全次数成分を、**同じ係数重み同型の逆射とMoore反転の合成によるcochain前合成**、続く指定 `AsSmall` 制限に厳密に同定した。別の同値を選んでいない。自由Moore重みの指定同型を前合成すると、その図式交換同型が相殺され、元の逆係数重み射だけが残る式も証明した。これにより§129のBK行の始域移送則へ渡す射が、実際のA12の射であることを明示できる。

元のHom対象の非公開な余積の別名をまたぐrewriteと自動合同変形では既定heartbeatに達したため、反転のHom成分を先に一つの等式に固定し、明示的な `congrArg` で前合成・AsSmall制限へ運ぶ証明に分割した。計算上限を上げていない。これらはB02内の既存構成の評価・合成則と同じ証明の分割で、ID付き一覧の追加ではない。

### 130.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.HomSourceCochainEvaluation`（48行）

```lean
theorem intervalHomPrePost_id_apply {P P' Q : CochainComplex C ℤ}
    (σ : P' ⟶ P) (p : ℤ) (z : Cochain P Q p) :
    (intervalHomPrePost A σ (𝟙 Q)).f p z =
      (Cochain.ofHom σ).comp z (zero_add p)

theorem linearHomSourceIso_hom_apply {P P' : CochainComplex C ℤ}
    (e : P ≅ P') (Q : CochainComplex C ℤ) (p : ℤ) (z : Cochain P Q p) :
    (linearHomSourceIso A e Q).hom.f p z =
      (Cochain.ofHom e.inv).comp z (zero_add p) :=
  intervalHomPrePost_id_apply A e.inv p z

/-- 二つの閉零次始域射の前合成は同じ合成射の前合成。 -/
theorem zeroSourcePrecomp_comp {P P' P'' Q : CochainComplex C ℤ}
    (a : P'' ⟶ P') (b : P' ⟶ P) (p : ℤ) (z : Cochain P Q p) :
    (Cochain.ofHom a).comp ((Cochain.ofHom b).comp z (zero_add p)) (zero_add p) =
      (Cochain.ofHom (a ≫ b)).comp z (zero_add p)

theorem zeroSourcePrecomp_comp {P P' P'' Q : CochainComplex C ℤ}
    (a : P'' ⟶ P') (b : P' ⟶ P) (p : ℤ) (z : Cochain P Q p) :
    (Cochain.ofHom a).comp ((Cochain.ofHom b).comp z (zero_add p)) (zero_add p) =
      (Cochain.ofHom (a ≫ b)).comp z (zero_add p)

```

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKSourceEvaluation`（66行）

```lean
theorem reflectedNormalizedBKSmallHomIso_hom_apply (X : CosimplicialObject (Complex A))
    (p : ℤ) (z : (reflectedNormalizedBKHom X).X p) :
    (reflectedNormalizedBKSmallHomIso A X).hom.f p z =
      asSmallHomCochainEquiv A (SimplexCategoryᵒᵖᵒᵖ)
        ((E).obj (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})))
        ((E).obj (doubleOppositeDiagram X)) p
        ((Cochain.ofHom (normalizedLinearWeightDiagramIso A V).inv).comp z (zero_add p))

theorem reflectedNormalizedBKSmallHomIso_reverse_apply (X : CosimplicialObject (Complex A))
    (p : ℤ) (z : (normalizedBousfieldKanHom X).X p) :
    (reflectedNormalizedBKSmallHomIso A X).hom.f p
      ((normalizedBKReverseHomotopyEquiv X).hom.f p z) =
      asSmallHomCochainEquiv A (SimplexCategoryᵒᵖᵒᵖ)
        ((E).obj (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})))
        ((E).obj (doubleOppositeDiagram X)) p
        ((Cochain.ofHom ((normalizedLinearWeightDiagramIso A V).inv ≫
          extendMap (normalizedMooreReverse.app
            (linearizedSimplicialWeight A bousfieldKanSetWeight))
            ComplexShape.embeddingDownNat)).comp z (zero_add p))

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightInverseSource`（39行）

```lean
theorem freeLinearWeightDiagramIso_inverse_source :
    (freeLinearWeightDiagramIso A W).hom ≫ (normalizedLinearWeightDiagramIso A W).inv =
      (normalizedLinearWeightFreeIso A W.flip).inv

theorem freeLinearWeightDiagramIso_inverse_precomp
    {P Q : CochainComplex (J ⥤ ModuleCat A) ℤ}
    (τ : (((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W.flip)).extend
      ComplexShape.embeddingDownNat) ⟶ P) (p : ℤ) (z : Cochain P Q p) :
    (Cochain.ofHom (freeLinearWeightDiagramIso A W).hom).comp
      ((Cochain.ofHom ((normalizedLinearWeightDiagramIso A W).inv ≫ τ)).comp z
        (zero_add p)) (zero_add p) =
      (Cochain.ofHom ((normalizedLinearWeightFreeIso A W.flip).inv ≫ τ)).comp z
        (zero_add p)

```

### 130.2 検収と残り

コード **`d448f63e4`**（新規3本153行）。結合個別検査 `/private/tmp/isw2-reflected-bk-source-inverse-combined2.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build144.log` は **4,540 jobs・終了コード0**。新規分のみの監査 `/private/tmp/AuditISW2G10B02ReflectedSource.lean` は **8宣言（3・2・3）、標準三公理のみ**。共有鍵は `--class impl --wait 3600` でビルド・監査の間だけ使用し返却済み。

累計 **266モジュール・16,272行・2,243宣言**。一覧 `/private/tmp/isw2-g10-twohundredsixtysix-modules.txt`。外枠20,000行まで残り3,728行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0、rootビルド・大きな監査なし。未検証下書きはない。

B02は引き続き未完。次は、今回明示した同じ始域射を§129の行合成則へ代入し、自由重みの点ごとのMoore・延長・図式交換を通して、§127の各切断条件を閉じる。パラメータ側は§126の実標準Hom最上位評価、実AW側は§127の前面・後面の式を使う。その後、raw成分等式を§125のMoore制限と§122の指定自由随伴・uncurryへ渡し、反転・添字輸送後の全単体的射のB02等式へ戻す。B03〜B08・C・Dは未完、3b-4段0はG10完成後に出す。

## 131. B02の途中：実A12の自由重みの任意の元でのtensor合成式

一覧：済み 14／全体 36（うち追加 1）

A12の実際の逆係数重み射とMoore反転を合成した同じ始域射を、§129のBK行の合成則へ代入した。指定自由重み同型の逆射で元を戻し、負次数項同型と自由重み同型の両逆を相殺することにより、**自由重みの任意の元**についてtensor符号が消えて元の錐代表との実dg合成となることを示した。したがってAW切断の射影自由生成元を直接代入できる。

閉零次cochainの点ごとの成分を異種等号で評価し、右辺を元の実複体射 `σ ≫ normalizedBousfieldKanConeRepresentative X` の成分に直した。さらに終次数を任意の `r`、条件 `p-n=r` で合わせた版を別名に置いた。型を弱めず、同じ自由重み成分式を分割したもの。

指定同型の両逆を直接使う計算を採用したため、点ごとのMoore比較を更に展開する補助ファイルは最終ソースに加えていない。成分の型移送とAW合成則への適用では、計算上限を上げず、対象・全次数を明記し、共通の閉零次成分評価と終次数の輸送を別宣言に分けて検査した。いずれも既存構成の評価・合成則または同じ証明の分割であり、ID付き項目の追加ではない。

### 131.1 登録対象・行数・型

`SerrePositivity.HomologicalAlgebra.ExtendedChainHomIsoEvaluation`（32行）

```lean
theorem extendedChainHomRows_iso_evaluation (L : ChainComplex C ℕ)
    (P H : CochainComplex C ℤ) (e : L.extend ComplexShape.embeddingDownNat ≅ P)
    (q : ℤ) (z : Cochain P H q) (n : ℕ) :
    e.inv.f (-(n : ℤ)) ≫ (negativeChainRowIso L n).hom ≫
      extendedChainHomRows L H q
        ((Cochain.ofHom e.hom).comp z (zero_add q)) n =
      z.v (-(n : ℤ)) (q - n) (by omega)

```

`SerrePositivity.HomologicalAlgebra.CochainOfHomPointEvaluation`（34行）

```lean
theorem cochainOfHom_v_app_heq {F G : CochainComplex (J ⥤ ModuleCat A) ℤ}
    (a : F ⟶ G) (i j : ℤ) (h : i + 0 = j) (k : J) (x : (F.X i).obj k) :
    HEq (((Cochain.ofHom a).v i j h).app k x) ((a.f i).app k x)

theorem cochainOfHom_comp_v_app_heq {F G H : CochainComplex (J ⥤ ModuleCat A) ℤ}
    (a : F ⟶ G) (b : G ⟶ H) (i j : ℤ) (h : i + 0 = j) (k : J)
    (x : (F.X i).obj k) :
    HEq ((((Cochain.ofHom a).comp (Cochain.ofHom b) (zero_add 0)).v i j h).app k x)
      (((a ≫ b).f i).app k x)

```

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeTensorRow`（134行）

```lean
theorem reflectedBKFreeHom_tensor_row (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ)
    (j : SimplexCategoryᵒᵖᵒᵖ)
    (w : (((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0}))).X (-(n : ℤ))).obj j) :
    let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat
    let η := (Cochain.ofHom σ).comp
      (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) (zero_add 0)
    let χ := (Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)
    ((-(n : ℤ)) * p).negOnePow • ((χ.v (-(n : ℤ)) (p - n) (by omega)).app j) w =
      compose A (D := Complex A) (p := p) (q := 0 - n) (n := p - n)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j)
        (((η.v (-(n : ℤ)) (0 - n) (by omega)).app j) w) f (by omega)

theorem reflectedBKFreeHom_tensor_component (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ) (n : ℕ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p)
    (j : SimplexCategoryᵒᵖᵒᵖ)
    (w : (((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0}))).X (-(n : ℤ))).obj j) :
    let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat
    let χ := (Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)
    ((-(n : ℤ)) * p).negOnePow • ((χ.v (-(n : ℤ)) (p - n) (by omega)).app j) w =
      compose A (D := Complex A) (p := p) (q := -(n : ℤ)) (n := p - n)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j)
        ((((σ ≫ normalizedBousfieldKanConeRepresentative X).f (-(n : ℤ))).app j) w)
        f (by omega)

theorem reflectedBKFreeHom_tensor_component_of_degree (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ) (n : ℕ) (r : ℤ) (hr : p - n = r)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p)
    (j : SimplexCategoryᵒᵖᵒᵖ)
    (w : (((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0}))).X (-(n : ℤ))).obj j) :
    let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat
    let χ := (Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)
    ((-(n : ℤ)) * p).negOnePow • ((χ.v (-(n : ℤ)) r (by omega)).app j) w =
      compose A (D := Complex A) (p := p) (q := -(n : ℤ)) (n := r)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j)
        ((((σ ≫ normalizedBousfieldKanConeRepresentative X).f (-(n : ℤ))).app j) w)
        f (by omega)

```

### 131.2 検収と残り

コード **`6d7d1217b`**（新規3本200行）。最終ソースの結合個別検査 `/private/tmp/isw2-reflected-bk-free-tensor-iso-combined5.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build145.log` は **4,563 jobs・終了コード0**。新規分のみの監査 `/private/tmp/AuditISW2G10B02FreeTensorRow.lean` は **13宣言（2・2・9）、標準三公理のみ**。共有鍵は `--class impl --wait 3600` でビルド・監査の間だけ使用し返却済み。

累計 **269モジュール・16,472行・2,256宣言**。一覧 `/private/tmp/isw2-g10-twohundredsixtynine-modules.txt`。外枠20,000行まで残り3,528行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。

B02はまだ未完。次は元の `reversedWeightPointwiseBousfieldKanCone X` を、同じ自由鎖随伴による `σ ≫ r` の像に厳密に同定する。§108の `normalizedLinearWeightHomEquiv_freeDiagram` を元の錐代表に適用し、係数重み同型の両逆を相殺する。これにより今回の右辺を実標準Homの最上位成分へ合わせる。その後、パラメータ側の§126、各切断の§127と全切断和、§125のMoore制限、指定自由随伴・uncurryを通して、元のB02の全単体的射の等式へ戻す。B03〜B08・C・D、G10後の3b-4段0は未完。

## 132. B02の途中：元の反転BK錐入力の逆随伴と最上位成分

一覧：済み 14／全体 36（うち追加 1）

元の `reversedWeightPointwiseBousfieldKanCone X` が、指定係数重み同型の逆射と同じ反転錐代表の自由鎖随伴像であることを、既存の全図式の線形重みHom比較から証明した。自由随伴で逆に戻すと、同じ `σ ≫ normalizedBousfieldKanConeRepresentative X` の像となり、各点・各複体次数で実代表の成分に一致する。さらに元の反転錐入力を同じ標準DK同型で実標準Homへ戻した最上位成分を、同じ実代表の射影自由生成元の像に同定した。全次数（零次数を含む）の式で、錐入力・DK同型を選び直していない。

パラメータ側では、指定持ち上げ標準単体Hom評価の後合成自然性とYonedaパラメータの単位評価を証明した。同じ元の射の全単体の像をそのまま与える。いずれもB02の既存構成の評価・自然性・合成則または同じ証明の分割で、ID付き項目の追加ではない。

### 132.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeConeAdjunction`（113行）

```lean
theorem reversedWeightPointwiseBousfieldKanCone_freeAdjunction
    (X : CosimplicialObject (Complex A)) :
    reversedWeightPointwiseBousfieldKanCone X =
      (freeNegativeChainsDiagramAdjunction A (SimplexCategoryᵒᵖᵒᵖ)).homEquiv
        (V ⋙ SSet.uliftFunctor.{u,0})
        (complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X))
        ((functorComplexExchangeUnitIso (SimplexCategoryᵒᵖᵒᵖ) (ModuleCat A) (.up ℤ)).hom.app
            (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})) ≫
          complexOfFunctorsToFunctorToComplex.map
            ((normalizedLinearWeightDiagramIso A V).inv ≫
              reflectedBousfieldKanConeRepresentative X))

theorem reflectedBousfieldKanConeRepresentative_source (X : CosimplicialObject (Complex A)) :
    reflectedBousfieldKanConeRepresentative X =
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat ≫ normalizedBousfieldKanConeRepresentative X

theorem reversedWeightPointwiseBousfieldKanCone_free_inverse
    (X : CosimplicialObject (Complex A)) :
    ((freeNegativeChainsDiagramAdjunction A (SimplexCategoryᵒᵖᵒᵖ)).homEquiv
      (V ⋙ SSet.uliftFunctor.{u,0})
      (complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X))).symm
      (reversedWeightPointwiseBousfieldKanCone X) =
      (functorComplexExchangeUnitIso (SimplexCategoryᵒᵖᵒᵖ) (ModuleCat A) (.up ℤ)).hom.app
          (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})) ≫
        complexOfFunctorsToFunctorToComplex.map
          (((normalizedLinearWeightDiagramIso A V).inv ≫
            extendMap (normalizedMooreReverse.app
              (linearizedSimplicialWeight A bousfieldKanSetWeight))
                ComplexShape.embeddingDownNat) ≫ normalizedBousfieldKanConeRepresentative X)

theorem reversedWeightPointwiseBousfieldKanCone_free_inverse_app_f
    (X : CosimplicialObject (Complex A)) (j : SimplexCategoryᵒᵖᵒᵖ) (i : ℤ) :
    ((((freeNegativeChainsDiagramAdjunction A (SimplexCategoryᵒᵖᵒᵖ)).homEquiv
      (V ⋙ SSet.uliftFunctor.{u,0})
      (complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X))).symm
      (reversedWeightPointwiseBousfieldKanCone X)).app j).f i =
      ((((normalizedLinearWeightDiagramIso A V).inv ≫
        extendMap (normalizedMooreReverse.app
          (linearizedSimplicialWeight A bousfieldKanSetWeight)) ComplexShape.embeddingDownNat) ≫
          normalizedBousfieldKanConeRepresentative X).f i).app j

theorem freeNegativeChainsDiagramAdjunction_symm_app {J : Type*} [Category* J]
    (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (f : W ⟶ Q ⋙ SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A) (j : J) :
    (((freeNegativeChainsDiagramAdjunction A J).homEquiv W Q).symm f).app j =
      ((freeNegativeChainsAdjunction A).homEquiv (W.obj j) (Q.obj j)).symm (f.app j)

theorem reversedWeightPointwiseBousfieldKanCone_point_inverse_f
    (X : CosimplicialObject (Complex A)) (j : SimplexCategoryᵒᵖᵒᵖ) (i : ℤ) :
    (((freeNegativeChainsAdjunction A).homEquiv
      ((V ⋙ SSet.uliftFunctor.{u,0}).obj j)
      ((complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X)).obj j)).symm
      ((reversedWeightPointwiseBousfieldKanCone X).app j)).f i =
      ((((normalizedLinearWeightDiagramIso A V).inv ≫
        extendMap (normalizedMooreReverse.app
          (linearizedSimplicialWeight A bousfieldKanSetWeight)) ComplexShape.embeddingDownNat) ≫
          normalizedBousfieldKanConeRepresentative X).f i).app j

```

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeConeTopEvaluation`（59行）

```lean
theorem reflectedBKFreeCone_generator_top (X : CosimplicialObject (Complex A))
    (j : SimplexCategoryᵒᵖᵒᵖ) (n : ℕ)
    (s : ((V ⋙ SSet.uliftFunctor.{u,0}).obj j).obj (Opposite.op ⦋n⦌)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj j
    let g := (reversedWeightPointwiseBousfieldKanCone X).app j ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    (((((normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat) ≫ normalizedBousfieldKanConeRepresentative X).f
          (-(n : ℤ))).app j) (freeNegativeGenerator ((V ⋙ SSet.uliftFunctor.{u,0}).obj j) n s) =
      standardTopEval (R := A) T Q n (g.app _ s)

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LiftedStandardSimplexParameterEvaluation`（48行）

```lean
theorem liftedStandardSimplexHomIso_postcomp {Z Z' : SSet.{u}} (f : Z ⟶ Z')
    (n : SimplexCategory)
    (t : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⟶ Z) :
    (liftedStandardSimplexHomIso Z').hom.app (Opposite.op n) (t ≫ f) =
      f.app (Opposite.op n) ((liftedStandardSimplexHomIso Z).hom.app (Opposite.op n) t)

theorem liftedStandardSimplexHomIso_yoneda_apply (Z : SSet.{u}) (n : SimplexCategory)
    (α : Z.obj (Opposite.op n)) :
    (liftedStandardSimplexHomIso Z).hom.app (Opposite.op n)
      (liftedStandardSimplexIso.{u}.hom.app n ≫ SSet.yonedaEquiv.symm α) = α

theorem liftedStandardSimplexHomIso_yoneda_postcomp {Z Z' : SSet.{u}} (f : Z ⟶ Z')
    (n : SimplexCategory) (α : Z.obj (Opposite.op n)) :
    (liftedStandardSimplexHomIso Z').hom.app (Opposite.op n)
      ((liftedStandardSimplexIso.{u}.hom.app n ≫ SSet.yonedaEquiv.symm α) ≫ f) =
        f.app (Opposite.op n) α

```

### 132.2 検収と残り

コード **`c5cb92cb3`**（新規3本220行）。錐の結合個別検査 `/private/tmp/isw2-reflected-bk-cone-top-combined2.log`、パラメータの個別検査 `/private/tmp/isw2-lifted-simplex-parameter2.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build146.log` は **4,695 jobs・終了コード0**。新規分のみの監査 `/private/tmp/AuditISW2G10B02FreeConeTop.lean` は **10宣言（6・1・3）、標準三公理のみ**。共有鍵は `--class impl --wait 3600` でビルド・監査の間だけ使用し返却済み。

累計 **272モジュール・16,692行・2,266宣言**。一覧 `/private/tmp/isw2-g10-twohundredseventytwo-modules.txt`。外枠まで残り3,308行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。

B02の最終等式とB03〜B08・C・D、G10後の3b-4段0は未完。次はA09の実際のtensor逆射の成分へ、§131の実A12の成分式をAsSmall制限とともに代入する。錐側の今回の最上位評価とパラメータ側の§126・今回のYoneda評価を合わせ、§127の各切断条件と全切断和へ進む。

## 133. B02の途中：実A09 tensor逆射とA12の像の成分

一覧：済み 14／全体 36（うち追加 1）

A09の指定 `freeTensorDiagramHomIso` の逆射へ、実際のHom–Tot比較・Moore反転・指定自由重みHom同型を合成したA12の複体射のΓ像を入れた。全標準単体パラメータ、任意の自由重みの元、任意のパラメータ次数について、そのtensor成分が元の `σ ≫ normalizedBousfieldKanConeRepresentative X` とパラメータcochainの実dg合成になることを証明した。逆転置の符号、AsSmall制限、指定始域射は元のものを保持している。切断条件を仮定していない。

これはB02内の指定射の成分照合で、既存構成の評価・自然性・合成則を合わせた証明分割であり、ID付き項目の追加ではない。

### 133.1 登録対象・型

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeTensorComparison`（90行）

```lean
theorem reflectedBKFreeTensor_inverse_component (P : Complex A)
    (X : CosimplicialObject (Complex A)) (m : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj
      (homComplex A P ((productTotalFunctor A).obj X))).obj (Opposite.op m))
    (n : ℕ) (p r : ℤ) (hr : p - n = r)
    (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ))
    (w : ((freeNegativeChainsDiagram (A := A)
      (reflectedNormalizedBKSmallWeight A)).obj j).X (-(n : ℤ)))
    (x : ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj m)).X p) :
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let t := (freeTensorDiagramHomIso A (normalizedBKSmallDiagram A Y)
      (reflectedNormalizedBKSmallWeight A)).inv.app (Opposite.op m)
        (((truncatedDoldKanFunctor A).map γ).app (Opposite.op m) α)
    let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat
    (t.app j).f r (ιTensorObj
      ((freeNegativeChainsDiagram (A := A) (reflectedNormalizedBKSmallWeight A)).obj j)
      ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
        (SSet.stdSimplex.obj m)) (-(n : ℤ)) p r (by omega) (w ⊗ₜ[A] x)) =
      compose A (D := Complex A) (p := p) (q := -(n : ℤ)) (n := r)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj (AsSmall.down.obj j))
        ((((σ ≫ normalizedBousfieldKanConeRepresentative X).f (-(n : ℤ))).app
          (AsSmall.down.obj j)) w)
        (((normalizedSimplexHomEquiv A (homComplex A P ((productTotalFunctor A).obj X)) m).symm
          α).f p x) (by omega)
```

### 133.2 検収と残り

コード **`00c9e5357`**（1本90行）。個別検査 `/private/tmp/isw2-reflected-bk-free-tensor-comparison2.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build147.log` は **4,573 jobs・終了コード0**。新規分のみの監査 `/private/tmp/AuditISW2G10B02TensorComparison.lean` は **3宣言・標準三公理のみ**。共有鍵は `--class impl --wait 3600` でビルド・監査の間だけ使用し返却済み。

累計 **273モジュール・16,782行・2,269宣言**。一覧 `/private/tmp/isw2-g10-twohundredseventythree-modules.txt`。外枠まで残り3,218行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。

次は自由生成元の前面・後面をこの式に代入し、§132の錐の最上位評価、§126・§132のパラメータ評価、§127のAW各切断成分を合わせる。B02の全体等式とB03〜B08・C・D、G10後の3b-4段0は未完。

## 134. B02の途中：実比較射のAW各切断条件を無条件に閉じる

一覧：済み 14／全体 36（うち追加 1）

元の実標準Hom単体のDK像をA12の指定複体射のΓ像へ送り、A09の実tensor逆射で戻したものについて、**任意の切断点の前面・後面の射影自由生成元の値が、同じ実標準AWの切断項に一致**することを証明した。重みの全単体、元の実標準Homの全標準単体パラメータ、全切断点を含み、切断条件を仮定していない。

実標準Homへの元の射の自然性を前面・後面で評価する法則と、元の実標準Hom単体のDK像の逆正規化Hom同値を全生成元で評価する法則に分割した。§133の無条件のtensor成分、§132の錐の最上位成分、§127の標準AW切断の式を合成して、以前の貼り合わせ則の各切断条件を今回の実射について閉じた。既存構成の評価・自然性・合成則または同じ証明の分割で、ID付き項目の追加ではない。

### 134.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardHomParameterNaturality`（29行）

```lean
theorem standardHomParameter_map {S : SSet.{u}}
    (f : S ⟶ standardHomSpace (R := A) x y) {m n : SimplexCategory}
    (θ : m ⟶ n) (s : S.obj (Opposite.op n)) :
    f.app (Opposite.op m) (S.map θ.op s) =
      standardPullback θ.toOrderHom (f.app (Opposite.op n) s)

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexNativeParameterEvaluation`（42行）

```lean
theorem normalizedSimplexHomEquiv_native_generator (x y : D) (m : SimplexCategory)
    (α : (standardHomSpace (R := A) x y).obj (Opposite.op m)) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)).obj
      (Opposite.op ⦋n⦌)) :
    ((normalizedSimplexHomEquiv A (homObject A D x y) m).symm
      ((standardDoldKanSpaceMap x y).app (Opposite.op m) α)).f (-(n : ℤ))
        (freeNegativeGenerator
          ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) n s) =
      standardTopEval (R := A) x y n
        (((liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α).app
          (Opposite.op ⦋n⦌)) s)

```

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeTensorCut`（85行）

```lean
theorem reflectedBKFreeTensor_inverse_cut (P : Complex A)
    (X : CosimplicialObject (Complex A)) (m : SimplexCategory)
    (α : (standardHomSpace (R := A) P ((productTotalFunctor A).obj X)).obj (Opposite.op m))
    (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (N : ℕ) (c : Fin (N + 1))
    (s : ((reflectedNormalizedBKSmallWeight A).obj j).obj (Opposite.op ⦋N⦌))
    (a : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)).obj
      (Opposite.op ⦋N⦌)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
    let S := (reflectedNormalizedBKSmallWeight A).obj j
    let B := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)
    let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    let f := liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let t := (freeTensorDiagramHomIso A (normalizedBKSmallDiagram A Y)
      (reflectedNormalizedBKSmallWeight A)).inv.app (Opposite.op m)
        (((truncatedDoldKanFunctor A).map γ).app (Opposite.op m)
          ((standardDoldKanSpaceMap (R := A) P T).app (Opposite.op m) α))
    (t.app j).f (-(N : ℤ)) (ιTensorObj (freeNegativeChains (A := A) S)
      (freeNegativeChains (A := A) B) (-(c.val : ℤ)) (-((N - c.val : ℕ) : ℤ)) (-(N : ℤ))
      (by have := awDegrees N c; omega)
      (freeNegativeGenerator S c.val (S.map (awFront N c).op s) ⊗ₜ[A]
        freeNegativeGenerator B (N - c.val) (B.map (awBack N c).op a))) =
      awTerm (g.app _ s).val (f.app _ a).val Finset.univ ⟨c, Finset.mem_univ c⟩
        (-(N : ℤ)) (by simp)

```

### 134.2 検収と残り

コード **`f39770010`**（新規3本156行）。結合個別検査 `/private/tmp/isw2-reflected-bk-cut-combined.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build148.log` は **4,725 jobs・終了コード0**。新規分のみの監査 `/private/tmp/AuditISW2G10B02TensorCut.lean` は **5宣言（1・1・3）、標準三公理のみ**。共有鍵は `--class impl --wait 3600` でビルド・監査の間だけ使用し返却済み。

累計 **276モジュール・16,938行・2,274宣言**。一覧 `/private/tmp/isw2-g10-twohundredseventysix-modules.txt`。外枠まで残り3,062行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。

B02の全体等式は引き続き未完。残る主接続は、各切断の有限和をraw係数写像の等式にまとめ、係数移送した積の自由化比較が同じMoore射影生成元を保つ式を使って、§125のMoore包含による制限へ渡すこと。その後に同じ自由随伴・uncurryで全単体的射を戻し、反転・添字の指定輸送を合わせる。B03〜B08・C・DとG10後の3b-4段0は未完。


## 135. B4前の係数単位・積のMoore射影の照合（2026-11-14）

一覧：済み 14／全体 36（うち追加 1）

B02の係数移送の法則と証明分割。新しい数学・構成の追加なし。指定された正のMoore次数を保ち、同じ積の自由化同型が射影生成元を送る式を確認する。

### 135.1 `CoefficientUnitNaturality`（52行）

```lean
theorem coefficientUnit_map_value {M N : ModuleCat.{u} ℤ} (f : M ⟶ N) (x : M) :
    (integerCoefficientExtension φ).map f (coefficientUnit φ M x) =
      coefficientUnit φ N (f x)

theorem coefficientUnit_hom_ext (M : ModuleCat.{u} ℤ) (N : ModuleCat.{u} A)
    (f g : (integerCoefficientExtension φ).obj M ⟶ N)
    (h : ∀ x : M, f (coefficientUnit φ M x) = g (coefficientUnit φ M x)) : f = g

theorem coefficientUnit_integerTensor_hom_ext (X Y : Type u) (N : ModuleCat.{u} A)
    (f g : (integerCoefficientExtension φ).obj
      (integerTensor (integerLinearization.obj X) (integerLinearization.obj Y)) ⟶ N)
    (h : ∀ x y, f (coefficientUnit φ _ (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)) =
      g (coefficientUnit φ _ (integerGenerator x ⊗ₜ[ℤ] integerGenerator y))) : f = g

```

### 135.2 `ProductChainsCoefficientProjection`（126行）

```lean
theorem productChainsCoefficient_projection (X Y : SSet.{u}) :
    let F := integerCoefficientExtension φ
    let S := simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y)
    let e := Functor.isoWhiskerRight (linearizedTensorIso X Y) F ≪≫
      integerCoefficientSimplicialFreeIso φ (X ⊗ Y)
    (F.mapHomologicalComplex (.down ℕ)).map (PInftyToNormalizedMooreComplex S) ≫
      normalizedMooreMapHom F S ≫ (normalizedMooreComplex (ModuleCat A)).map e.hom =
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app S ≫
        (alternatingFaceMapComplex (ModuleCat A)).map e.hom ≫
          PInftyToNormalizedMooreComplex ((X ⊗ Y) ⋙ ModuleCat.free A)

theorem productChainsCoefficient_degree (X Y : SSet.{u}) (r : ℕ) :
    let F := integerCoefficientExtension φ
    let S := simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y)
    let e := Functor.isoWhiskerRight (linearizedTensorIso X Y) F ≪≫
      integerCoefficientSimplicialFreeIso φ (X ⊗ Y)
    F.map ((PInftyToNormalizedMooreComplex S).f r) ≫ (normalizedMooreMapHom F S).f r ≫
      (((normalizedMooreComplex (ModuleCat A)).obj (S ⋙ F)).extendXIso
        ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv ≫
      (integerCoefficientProductChainsIso φ X Y).hom.f (-(r : ℤ)) =
      e.hom.app (Opposite.op ⦋r⦌) ≫
        (PInftyToNormalizedMooreComplex ((X ⊗ Y) ⋙ ModuleCat.free A)).f r ≫
        (((normalizedMooreComplex (ModuleCat A)).obj ((X ⊗ Y) ⋙ ModuleCat.free A)).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv

theorem productChainsCoefficient_simplicial_generator (X Y : SSet.{u}) (r : ℕ)
    (x : X.obj (Opposite.op ⦋r⦌)) (y : Y.obj (Opposite.op ⦋r⦌)) :
    let F := integerCoefficientExtension φ
    let e := Functor.isoWhiskerRight (linearizedTensorIso X Y) F ≪≫
      integerCoefficientSimplicialFreeIso φ (X ⊗ Y)
    e.hom.app (Opposite.op ⦋r⦌)
      (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋r⦌))
        ((linearizedSpace Y).obj (Opposite.op ⦋r⦌)))
          (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)) = ModuleCat.freeMk (x, y)

theorem productChainsCoefficient_generator_value (X Y : SSet.{u}) (r : ℕ)
    (x : X.obj (Opposite.op ⦋r⦌)) (y : Y.obj (Opposite.op ⦋r⦌)) :
    let F := integerCoefficientExtension φ
    let S := simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y)
    ((integerCoefficientProductChainsIso φ X Y).hom.f (-(r : ℤ)))
      ((((normalizedMooreComplex (ModuleCat A)).obj (S ⋙ F)).extendXIso
        ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
          ((normalizedMooreMapHom F S).f r
            (F.map ((PInftyToNormalizedMooreComplex S).f r)
              (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋r⦌))
                ((linearizedSpace Y).obj (Opposite.op ⦋r⦌)))
                  (integerGenerator x ⊗ₜ[ℤ] integerGenerator y))))) =
      freeNegativeGenerator (X ⊗ Y) r (x, y)

```

### 135.3 検収

コード `76453fce1`。鍵付き対象ビルド149は4,015 jobs・終了コード0。新規分だけの監査は7宣言（3・4）、標準三公理のみ。累計278モジュール・17,116行・2,281宣言。個別結合検査も警告のみで完了。計算上限の変更、sorry・新公理、既存宣言の変更なし。B02は未完。B4の指示を優先し、原ソースを保存して改名前の参照採取に移る。


## 136. B4：採取後の open 方針の保留で停止（2026-11-14 昼）

一覧：済み 14／全体 36（うち追加 1）

### 136.1 固定した原ソースと採取

B4の指示を優先。検証済み2本を `76453fce1`、型・検収を `b4916a73d` にコミットしてから、mainを取り込む前の自worktreeで参照を採取した。基準 `c5c4436c0` 以後の追加・変更Lean（drafts除外）は **278本**。作業木はクリーンで、未検証Lean下書きなし。原ソースを `/private/tmp/isw2-b4/original-sources.tar.gz`、対象全体を同ディレクトリの `files.json` に保存した。

mainの `bulk_namespace.py collect/rewrite` と B3配布表を使った。鍵は `--class impl --wait 3600`、各採取組は `gtimeout --kill-after=3s 280` で制限。最初の8本ずつ二組、その後は独立した8本ずつ四組を一つの鍵の中で採取。索引と原ソースの全バイト一致の検査を維持。整理券は常に一つ。採取順だけを入れ替え、全278本の集合が一致することを検査した。

**48本の採取が完了**（`before-00`〜`before-05`、全て `files.json` あり）。プレビューは最初の二組16本が保留0・ソース差分0。その次の8本のプレビューで下記1件の保留が出たため、ドライバは終了コード1で停止した。後続の採取や残りのプレビューには進んでいない。鍵は返却済み。最初の逐次ドライバは二組目の採取完了後、停止状態から終了して組単位のドライバに切り替えた。このドライバ切り替えの終了137と、保留による終了1は区別している。

### 136.2 保留の内容

対象：`SerrePositivity/InfinityCategories/Project/DerivedCategories/DiagramComparison/DiagramTensorDoldKan.lean` **20行**（UTF-8 byte 1131〜1215）。

```lean
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
```

`review.json` の理由：

```text
explicit opens policy needed for a renamed namespace
```

採取したopenは単純open、解決先は上記と同じ完全名の一つ。配布表の全体 `opens` およびこのモジュールの `module_opens` には、この名前の方針がない。一方、配布表には既存モジュール `SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneStandardHom` に限った同じopenを同名のまま保つ方針が既にある。新規利用側へ同じ方針を使ってよいかを自分で推定せず、指示どおり停止した。共有の道具・配布表・Leanソースの手修正はしていない。

再現資料を `evidence/inf-supply-b/is-w2-b4-20261114/` に保存した：対象全体 `files.json`、保留 `review.json`、該当ファイルの採取元込み索引 `blocked-before-index.json.gz`、固定コミット・件数・配布表ハッシュ等 `summary.json`。他の索引・プレビュー・各採取ログは `/private/tmp/isw2-b4/` に保持している。

### 136.3 再開条件と現在地

**main未取り込み、プレビュー未反映、B4未完了**。指示の「保留が出たら止まって報告」に従い、B4後の対象ビルド・監査はまだ実行していない。原ソースは `b4916a73d` のまま。修正版のopen方針／道具を受け取ったら、同じ移動前ソースとその索引で再プレビューし、未採取分を採取する。保留0と差分確認の後に mainを取り込み、importをmodule-mapで追従し、自分の新規モジュールの対象ビルド・小さい監査を行う。

G10はB02未完、B03〜B08・C・Dも未完。累計278モジュール・17,116行・2,281宣言、外枠まで2,884行。B4が済んだ後に /goal を再開する。B4で計算上限・型・既存宣言・⑤a・入口・公式監査・mainの変更なし。新たなLean数学・構成の追加なし。


## 137. B4完了：承認された恒等open、main取り込み、対象ビルド・小さい監査（2026-11-14 午後）

一覧：済み 14／全体 36（うち追加 1）

### 137.1 open の承認と全体照合

調整役の11-14午後の指示（citation-attributes.md §14追記）に従い、二つの確認済み名前空間 `…Project.HomotopyDiagramComparison.CosimplicialHom` と `…Project.DerivedCategories.DiagramComparison` のopenを同名のまま保持した。配布された元の表は保存し、一時の表の `opens` に承認された二つの恒等方針だけを追加した。共有の道具・配布表の変更なし。再プレビューで§136の保留を解消した。

main取り込み前の同じ枝ソースで、**全278本**（drafts除外）の参照採取・原ソースの全バイト一致検査・rewriteを完了。各回は `--class impl --wait 3600` と280秒の上限、一つの整理券。独立した8本ずつ四つの小組を一つの鍵の中で採取し、全ての小組が終了するのを待ってから次へ進めた。索引の漏れ・重複なし、全reviewは**保留0**。通常importの全トークンをmodule-mapと照合し、一致を確認した。

### 137.2 差分と取り込み

プレビュー差分は**7ファイル、7行の追加・7行の削除**、全てimport先の変更。宣言名・型・証明・openのソースは変更していない。

| ファイルの末尾 | importの移動先 |
| --- | --- |
| DoldKanClosedPostcomposition | MappingAndStability/HomSpaces/DGStandardClosedPostcomposition |
| ReflectedNormalizedBKSmallSections | WeightedCones/WeightedSectionsOpposite |
| IntegerCoefficientFree | Tensor/DGSimplicialRingCoefficientComplex |
| IntegerCoefficientTensorDegrees | Tensor/DGIntegerCoefficientTensor |
| IntegerCoefficientTensorValues | Tensor/DGIntegerCoefficientTensor |
| ProductSectionsHom | MappingSpaces/UniverseJoinSimplexShapes |
| TruncatedDoldKanQuasiIso | LocalizationAndRoofs/PinchedChainMapQuasiIso |

main **`2be485f04`** を枝に取り込んだ（merge **`8c65d0319`**、競合なし）。取り込み前に確定した差分だけを `git apply -p0` で反映し、取り込み後の278本全てが取り込み前の最終プレビューと一致することを検査した。取り込み後のソースへの古い索引の流用なし。`git diff --check` も成功。

### 137.3 検収と受け渡し

コード **`93227d091`**。自分の278モジュールを全て指定した鍵付き対象ビルドは **6,570 jobs・終了コード0**。新規モジュールだけを40本ずつ選ぶ小さい監査7組は **[321, 334, 298, 310, 379, 297, 180]、計2,119宣言、全て標準三公理のみ・終了コード0**。rootビルド・公式監査の変更／実行なし。鍵はビルドと監査の間だけ使用し返却済み。

今回の2,119は、同じ全278本を分割して選んだ現在の監査の実測である。既報2,281は逐次の小監査の報告値を加算した累計であり、今回の値とは区別して記録する。278本の集合は従来のG10一覧と完全一致し、ソースはimport7行以外変えていない。過去の加算値との差の原因は今回の検査だけからは確定していない。以後の現在値には今回の全対象の実測を用いる。

証跡は `evidence/inf-supply-b/is-w2-b4-20261114/`：`approved-identity-opens.json`、`final-review.json`、`final-preview-summary.json`、`applied-preview.diff`、`build-and-audit.log.gz`、更新した `summary.json`。原ソース付きの索引全体と各採取ログは `/private/tmp/isw2-b4/` に保持。登録の照合用の全278モジュールは同フォルダの `files.json`（パスの拡張子を取り、スラッシュをピリオドに置換）である。入口・登録は調整役に委ねる。

**B4は完了**。累計278モジュール・17,116行、外枠まで2,884行。sorry・新公理0、計算上限・型の弱化・ModelCategory SSetの追加・⑤aの変更なし。/goalのB02の残り（raw有限和からMoore制限と全単体的射への接続）に戻る。B03〜B08・C・D、停止点2a・2b、3b-4段0は未完。


## 138. B02：実AW前合成と全標準単体のuncurryの照合（2026-11-14 午後）

一覧：済み 14／全体 36（うち追加 1）

B4完了後に /goal を再開。同じraw生成元、Moore射影、指定係数同型を通して、実A09逆射のAW前合成を元の実豊穣合成の逆自由随伴そのものへ同定した。さらに同じ自由随伴とuncurryで、全標準単体パラメータの各添字成分を元の豊穣合成へ戻した。各切断の照合を仮定には残さず、§134の実際の切断等式を代入している。

今回の6宣言はB02の既存構成の法則と証明分割であり、新しい構成・新しい数学の追加ではない。逆射の値の検査は、同じ同型の順方向の全射性で値を表し、順方向uncurry則から戻す形に分割した。elaboration・kernelとも既定の計算上限を維持した。

### 138.1 `FreeProductAWRawCriterion`（81行）

```lean
theorem freeProductAlexanderWhitney_f_eq_of_raw (X Y : SSet.{u}) (n : ℕ)
    (T : ModuleCat A)
    (t : (freeNegativeChains (A := A) X ⊗ freeNegativeChains (A := A) Y).X
      (-(n : ℤ)) ⟶ T)
    (h : (freeNegativeChains (A := A) (X ⊗ Y)).X (-(n : ℤ)) ⟶ T)
    (hraw : ∀ x : X.obj (Opposite.op ⦋n⦌), ∀ y : Y.obj (Opposite.op ⦋n⦌),
      ((integerCoefficientExtension φ).map
        ((alexanderWhitney (linearizedSpace X) (linearizedSpace Y)).f n ≫
          (chainIntegerTensorMap (PInftyToNormalizedMooreComplex (linearizedSpace X))
            (PInftyToNormalizedMooreComplex (linearizedSpace Y))).f n) ≫
        ((((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
          (chainIntegerTensor ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X))
            ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)))).extendXIso
              ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (negativeMooreTensorCoefficientIso φ (linearizedSpace X) (linearizedSpace Y)).hom.f
          (-(n : ℤ)) ≫
        (tensorIso (integerCoefficientFreeChainsIso φ X)
          (integerCoefficientFreeChainsIso φ Y)).hom.f (-(n : ℤ)) ≫ t)
        (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋n⦌))
          ((linearizedSpace Y).obj (Opposite.op ⦋n⦌)))
            (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)) =
      h (freeNegativeGenerator (X ⊗ Y) n (x, y))) :
    (freeProductAlexanderWhitney φ X Y).f (-(n : ℤ)) ≫ t = h

```

### 138.2 `ReflectedBKFreeTensorAW`（94行）

```lean
theorem reflectedBKFreeTensor_inverse_AW
    (φ : simplicialRingCoefficient.{u} →+* A) (P : Complex A)
    (X : CosimplicialObject (Complex A)) (m : SimplexCategory)
    (α : (standardHomSpace (R := A) P ((productTotalFunctor A).obj X)).obj (Opposite.op m))
    (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
    let S := (reflectedNormalizedBKSmallWeight A).obj j
    let B := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)
    let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    let f := liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let t := (freeTensorDiagramHomIso A (normalizedBKSmallDiagram A Y)
      (reflectedNormalizedBKSmallWeight A)).inv.app (Opposite.op m)
        (((truncatedDoldKanFunctor A).map γ).app (Opposite.op m)
          ((standardDoldKanSpaceMap (R := A) P T).app (Opposite.op m) α))
    freeProductAlexanderWhitney φ S B ≫ t.app j =
      ((freeNegativeChainsAdjunction A).homEquiv (S ⊗ B) (homObject A (Complex A) P Q)).symm
        ((g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := A) P T Q ≫
          standardDoldKanSpaceMap P Q)

```

### 138.3 `NormalizedWeightSectionInverseEvaluation`（81行）

```lean
theorem freeNegativeChainsDiagramAdjunction_hom_symm_app
    (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (f : freeNegativeChainsDiagram (A := A) W ⟶ Q) (j : J) :
    ((freeNegativeChainsAdjunction A).homEquiv (W.obj j) (Q.obj j)).symm
      ((((freeNegativeChainsDiagramAdjunction A J).homEquiv W Q) f).app j) = f.app j

theorem normalizedWeightSectionMap_hom_uncurry_inverse_app
    (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (φ : simplicialRingCoefficient.{u} →+* A) (m : SimplexCategory)
    (f : (freeTensorFrame A W (liftedStandardSimplexParameter J)).obj m ⟶ Q) (j : J) :
    ((freeNegativeChainsAdjunction A).homEquiv
      (W.obj j ⊗ (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) (Q.obj j)).symm
      ((weightedSectionsUncurry
        (liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm
          ((normalizedWeightSectionMap A W Q φ).app (Opposite.op m)
            ((freeTensorDiagramHomIso A Q W).hom.app (Opposite.op m) f)))).app j) =
    freeProductAlexanderWhitney φ (W.obj j)
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) ≫ f.app j

theorem normalizedWeightSectionMap_uncurry_inverse_app
    (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (φ : simplicialRingCoefficient.{u} →+* A) (m : SimplexCategory)
    (β : ((truncatedDoldKanFunctor A).obj (linearHomComplex A
      ((functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
        (freeNegativeChainsDiagram (A := A) W))
      ((functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj Q))).obj (Opposite.op m)) (j : J) :
    ((freeNegativeChainsAdjunction A).homEquiv
      (W.obj j ⊗ (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) (Q.obj j)).symm
      ((weightedSectionsUncurry
        (liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm
          ((normalizedWeightSectionMap A W Q φ).app (Opposite.op m) β))).app j) =
    freeProductAlexanderWhitney φ (W.obj j)
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) ≫
        ((freeTensorDiagramHomIso A Q W).inv.app (Opposite.op m) β).app j

```

### 138.4 `ReflectedBKNormalizedSectionsUncurry`（76行）

```lean
theorem reflectedBKNormalizedSections_uncurry
    (φ : simplicialRingCoefficient.{u} →+* A) (P : Complex A)
    (X : CosimplicialObject (Complex A)) (m : SimplexCategory)
    (α : (standardHomSpace (R := A) P ((productTotalFunctor A).obj X)).obj (Opposite.op m))
    (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
    let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    let f := liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    (weightedSectionsUncurry
      (liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm
        ((normalizedWeightSectionMap A (reflectedNormalizedBKSmallWeight A)
          (normalizedBKSmallDiagram A Y) φ).app (Opposite.op m)
            (((truncatedDoldKanFunctor A).map γ).app (Opposite.op m)
              ((standardDoldKanSpaceMap (R := A) P T).app (Opposite.op m) α))))).app j =
      (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := A) P T Q ≫
        standardDoldKanSpaceMap P Q

```

### 138.5 検収と残り

コード **`c6df9240b`**。個別の結合検査 `/private/tmp/isw2-reflected-uncurry-combined7.log` は終了コード0。不要な未使用letを除いた最終4モジュールの鍵付き対象ビルド `/private/tmp/isw2-build150.log` は **4,740 jobs・終了コード0**。新規分のみの監査は **6宣言（1・1・3・1）、標準三公理のみ**。鍵は `--class impl --wait 3600`、ビルドと監査の間だけ使用し返却済み。

累計 **282モジュール・17,448行**、外枠まで2,552行。現在の全対象監査の基準は§137の278本・2,119宣言で、今回の新規分監査6宣言とは区別して記録する。モジュール一覧 `/private/tmp/isw2-g10-twohundredeightytwo-modules.txt`。計算上限・既存宣言・⑤a・入口・公式監査の変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証の下書きなし。

B02全体の `gammaReflectedBKComparison_eq` はまだ未完。残りは、今回の全標準単体・各添字のuncurry等式を重み付き切断の全射の等式に戻し、元の反転end・small添字の指定同型・実Hom同型を通して同じnative比較へ運ぶこと。B03〜B08・C・D、停止点2a・2b、3b-4段0も未完。次はこの反転・添字の輸送を接続する。


## 139. B02：全uncurry、指定反転end・small添字の評価と因数分解（2026-11-14 午後）

一覧：済み 14／全体 36（うち追加 1）

§138の全標準単体の式を、持ち上げた恒等単体で評価して元のuncurry全体の各成分の等式へ戻した。反転endについては既存の内部Hom反転評価、small添字については既存のend射影の制限則を使い、同じuncurryが指定の反転・制限を保つ式を得た。元の `gammaReflectedBKComparison` も、既存の因数分解と関手の合成則で同じ反転・AW・添字同型・実Hom同型の合成へ括り直した。新しい構成や数学の追加はなく、全てB02の既存構成の法則・証明分割。

### 139.1 `WeightedSectionsReflectionEvaluation`（50行）

```lean
theorem weightedSectionsOppositeIso_uncurry (W H : I ⥤ SSet.{u}) {S : SSet.{u}}
    (f : S ⟶ weightedSections W H) (i : I) :
    (weightedSectionsUncurry
      (SSet.opFunctor.map f ≫ (weightedSectionsOppositeIso W H).hom)).app i =
    (opTensorIso (W.obj i) S).hom ≫ SSet.opFunctor.map ((weightedSectionsUncurry f).app i)

theorem weightedSectionsReflectedIso_uncurry (W H : I ⥤ SSet.{u}) {S : SSet.{u}}
    (f : S ⟶ weightedSections (W ⋙ SSet.opFunctor) H) (i : I) :
    (weightedSectionsUncurry
      (SSet.opFunctor.map f ≫ (weightedSectionsReflectedIso W H).hom)).app i =
    ((diagramDoubleOppositeIso W).inv.app i ▷ S.op) ≫
      (opTensorIso ((W ⋙ SSet.opFunctor).obj i) S).hom ≫
        SSet.opFunctor.map ((weightedSectionsUncurry f).app i)

```

### 139.2 `SmallBKIndexSectionsEvaluation`（29行）

```lean
theorem smallBKIndexSectionsMap_uncurry {I J : Type u} [SmallCategory I] [SmallCategory J]
    (F : J ⥤ I) (W H : I ⥤ SSet.{u}) {S : SSet.{u}}
    (f : S ⟶ weightedSections W H) (j : J) :
    (weightedSectionsUncurry (f ≫ smallBKIndexSectionsMap F W H)).app j =
      (weightedSectionsUncurry f).app (F.obj j)

```

### 139.3 `ReflectedBKNormalizedSectionsMapEvaluation`（93行）

```lean
theorem reflectedBKNormalizedSections_uncurry_map
    (φ : simplicialRingCoefficient.{u} →+* A) (P : Complex A)
    (X : CosimplicialObject (Complex A)) (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
    let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let ψ := standardDoldKanSpaceMap P T ≫ (truncatedDoldKanFunctor A).map γ ≫
      normalizedWeightSectionMap A (reflectedNormalizedBKSmallWeight A)
        (normalizedBKSmallDiagram A Y) φ
    (weightedSectionsUncurry ψ).app j =
      (g ⊗ₘ 𝟙 (standardHomSpace (R := A) P T)) ≫ (β_ _ _).hom ≫
        standardComposition (R := A) P T Q ≫ standardDoldKanSpaceMap P Q

```

### 139.4 `GammaReflectedBKComparisonFactor`（48行）

```lean
theorem gammaReflectedBKComparison_factor (P : Complex A)
    (X : CosimplicialObject (Complex A)) :
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let ψ := standardDoldKanSpaceMap P ((productTotalFunctor A).obj X) ≫
      (truncatedDoldKanFunctor A).map γ ≫
        normalizedWeightSectionMap A (reflectedNormalizedBKSmallWeight A)
          (normalizedBKSmallDiagram A Y) (normalizedBKCoefficientMap A)
    gammaReflectedBKComparison X (ForgetEnrichment.of (Complex A) P) =
      SSet.opFunctor.map ψ ≫
        (weightedSectionsReflectedIso (normalizedBKSmallWeight A)
          (normalizedBKSmallDiagram A Y ⋙ truncatedDoldKanFunctor A) ≪≫
            normalizedBKOriginalSectionsIso A Y).hom ≫
        (weightedSectionsFunctor (bousfieldKanWeight (AsSmall.{u} SimplexCategory))).map
          (normalizedBKReflectedHomDiagramIso X P).hom

```

### 139.5 検収と残り

コード **`bded7fe66`**。反転評価は、今回初めて読むB3移動済みの依存の古いキャッシュを更新した対象ビルド151で検査した（1,615 jobs、監査2宣言・標準三公理のみ、終了コード0）。small添字、全uncurry、因数分解もそれぞれ個別検査が終了コード0。その最終4本をまとめた鍵付き対象ビルド `/private/tmp/isw2-build152.log` は **6,548 jobs・終了コード0**、新規分だけの監査は **9宣言（2・1・1・5）、標準三公理のみ**。鍵は `--class impl --wait 3600`、検証の間だけ使用し返却済み。

累計 **286モジュール・17,668行**、外枠まで2,332行。一覧 `/private/tmp/isw2-g10-twohundredeightysix-modules.txt`。sorry・新公理0。計算上限、既存宣言、⑤a、入口・公式監査の変更なし。rootビルド・大きな監査なし。未検証下書きなし。

B02の全体等式はまだ未完。今回の評価則と因数分解を通して、元の `reflectedWeightedHomFamily` の同じ成分へ照合する最後の接続を進める。B03〜B08・C・D、停止点2a・2b、3b-4段0は未完。


## 140. B02・B03完了：元の全比較射の等式と同じ射の同値性（2026-11-14 午後）

一覧：済み 16／全体 36（うち追加 1）

型つき一覧B02 `gammaReflectedBKComparison_eq` とB03 `reflectedBKComparison_equivalence` を、§73.2の元の型のまま証明した。全試験対象・全単体・元のTot頂点・同じnative錐入力を保つ。B02では指定反転endとsmall添字の評価を通して実際の `reflectedWeightedHomFamily` そのものに一致させ、切断の普遍性で全射の等式へ戻した。B03はその等式へ既存のΓ比較の同値性を代入した。別の同値な空間／別の射への置換はしていない。

native成分の最後の照合は、実Hom同型の両逆則を先に射の段階で消去し、残った元の錐入力の成分を定義で照合する形に分割した。計算上限・再帰上限は変更していない。前提の追加、ModelCategory SSetの追加、新しい構成／数学の追加なし。

### 140.1 `GammaReflectedBKComparisonUncurry`（70行）

```lean
theorem gammaReflectedBKComparison_uncurry (P : Complex A)
    (X : CosimplicialObject (Complex A)) (j : AsSmall.{u} SimplexCategory) :
    (weightedSectionsUncurry
      (gammaReflectedBKComparison X (ForgetEnrichment.of (Complex A) P))).app j =
    (reflectedWeightedHomFamily (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (liftedEnrichedBousfieldKanCone X) (ForgetEnrichment.of (Complex A) P)).app j

```

### 140.2 `GammaReflectedBKComparisonEquality`（52行）

```lean
theorem gammaReflectedBKComparison_eq (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    gammaReflectedBKComparison X x =
      reflectedWeightedHomComparison (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (liftedEnrichedBousfieldKanCone X) x

theorem reflectedBKComparison_equivalence (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    IsSimplicialHomotopyEquivalence
      (reflectedWeightedHomComparison (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (liftedEnrichedBousfieldKanCone X) x)

```

### 140.3 検収と残り

コード **`b74819308`**。結合個別検査 `/private/tmp/isw2-gamma-equality-combined.log` は終了コード0。最終2本の鍵付き対象ビルド `/private/tmp/isw2-build153.log` は **6,551 jobs・終了コード0**。新規分のみの監査は **3宣言（1・2）、標準三公理のみ**。鍵は `--class impl --wait 3600`、検証中のみ使用し返却済み。

累計 **288モジュール・17,790行**、外枠まで2,210行。一覧 `/private/tmp/isw2-g10-twohundredeightyeight-modules.txt`。sorry・新公理0。既存宣言・⑤a・入口・公式監査の変更なし。rootビルド・大きな監査なし。未検証下書きなし。

A01〜A12・A05a・B01〜B03が完了。B04〜B08（指定native切断の族、同じ頂点／制限の照合、極限性）へ進む。Bの残りが済んだ時点で指示どおりC・Dを再見積もりする。C01〜C07・D01〜D08、停止点2a・2b、3b-4段0は未完。これはG10全体の完成報告ではない。


## 141. B04・B05完了：元のTot錐全体上の全Homの族と指定頂点評価（2026-11-14 午後）

一覧：済み 18／全体 36（うち追加 1）

B04の `nativeTotConeFamilyLift` は、元の `nativeCoherentCone X` 全体上の標準coslice切断から、既存の `coherentConeSourceFamily` により構成した。B05の頂点評価は既存の同じ族の評価則へ特殊化し、元の `nativeCoherentCone_vertex X` で正規化した。元の錐・頂点・全Homパラメータ・高次単体を保つ、型つき一覧B04・B05の実装である。制限の式B06は引き続き別に照合する。

### 141.1 型（`NativeTotConeFamilyLift`、47行）

```lean
def nativeTotConeFamilyLift (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    (SSet.uliftFunctor.{u+1,u}).obj (SimplicialCategory.sHom x
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))).op ⟶
        coherentConeSectionSpace (nativeCoherentCone X).val (coherentNerveVertex x)

theorem nativeTotConeFamilyLift_apex (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    nativeTotConeFamilyLift X x ≫ coherentConeApexEvaluation (nativeCoherentCone X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (nativeCoherentCone_vertex X) x =
    coherentCosliceFiberComparison x
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))

```

### 141.2 検収と残り

コード **81185bce8**。今回初めて使う既存 `CoherentConeSourceApex` のoleanが未作成だったため、依存を含む鍵付き対象ビルドで検査した。`/private/tmp/isw2-build154.log` は **6,090 jobs・終了コード0**、新規モジュールのみの監査は **12宣言・標準三公理のみ**。鍵は `--class impl --wait 3600`、ビルドと監査の間だけ使用し返却済み。

累計 **289モジュール・17,837行**、外枠まで2,163行。一覧 `/private/tmp/isw2-g10-twohundredeightynine-modules.txt`。sorry・新公理0、ModelCategory SSetの追加なし、計算上限・既存宣言・⑤a・入口・公式監査の変更なし。rootビルド・大きな監査なし。未検証下書きなし。

B06（同じ族の制限と既存の全BK→native比較との厳密な一致）、B07・B08が残る。既存の `fixedVertexConeSpaceEquiv_cosliceSection`、`coherentConeSourceFamily_restriction_weighted`、`weightedConeEndPrecomposition_evaluation` を使って、元のweightedな錐の点を同じcosliceの前合成へ戻す経路を進める。Bの完了後にC・Dを再見積もりする。C・D、停止点2a・2b、3b-4段0は未完。


## 142. B06：同じTot錐のweighted点・切断と固定点のend作用（2026-11-14 午後）

一覧：済み 18／全体 36（うち追加 1）

元の `nativeCoherentCone X` の正規化したcoslice切断を、指定の `reflectedWeightedConeSectionPoint` の評価へ戻した。さらにその点のYoneda表示と既存BK比較の評価則を使い、同じweightedな切断の表示を得た。B04の同じ族を制限した際の相対uncurryも、その切断に対する既存のcoslice前合成へ同定した。

end作用の側では、既存のパラメータ自然性を全切断に対して証明し、同じweighted錐の点を固定した作用が `reflectedWeightedHomComparison` に一致する式を得た。今回の6宣言はB06の既存構成の単位・自然性・評価則と証明分割であり、新しい構成／数学の追加はない。B06の最終等式には、これらの式のULift・直積の照合がなお残る。


### 142.1 `NativeTotConePointSection`（117行）

```lean
theorem nativeTotCone_cosliceSection (X : CosimplicialObject (Complex A)) :
    coherentConeCosliceSection (nativeCoherentCone X) ≫
      eqToHom (congrArg (fun w : (SimplicialNerve (ClosedCategory A (Complex A))) _⦋0⦌ =>
        sliceUnder (SSet.yonedaEquiv.symm w)) (nativeCoherentCone_vertex X)) =
    inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))
      (Δ[0] : SSet.{u+1})) ≫ relativeFunctorUncurry
        (SSet.yonedaEquiv.symm (reflectedWeightedConeSectionPoint (liftedClosedDiagram X)
          (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
          (liftedEnrichedBousfieldKanCone X)))

theorem nativeTotCone_point_yoneda (X : CosimplicialObject (Complex A)) :
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let φ := liftedEnrichedBousfieldKanCone X
    SSet.yonedaEquiv.symm (reflectedWeightedConeSectionPoint F z φ) =
      SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
        (fst (bousfieldKanWeight (AsSmall.{u} SimplexCategory))
          ((Functor.const (AsSmall.{u} SimplexCategory)).obj (Δ[0] : SSet.{u})) ≫ φ)))) ≫
        reflectedHomHolimConeComparison F z

theorem nativeTotCone_cosliceSection_weighted (X : CosimplicialObject (Complex A)) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let H := simplicialHomDiagram F z ⋙ SSet.opFunctor
    let φ := liftedEnrichedBousfieldKanCone X
    let e : (Δ[0] : SSet.{u+1}) ⟶
        (SSet.uliftFunctor.{u+1,u}).obj (bousfieldKanHolim H) :=
      SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ))))
    let s := inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) (Δ[0] : SSet.{u+1})) ≫
      (((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) ◁ e) ≫
        (uliftTensorIso (nerve I) (bousfieldKanHolim H)).inv ≫
          (SSet.uliftFunctor.{u+1,u}).map (bousfieldKanWeightedNerveEvaluation H)
    coherentConeCosliceSection (nativeCoherentCone X) ≫
      eqToHom (congrArg (fun w : (SimplicialNerve (ClosedCategory A (Complex A))) _⦋0⦌ =>
        sliceUnder (SSet.yonedaEquiv.symm w)) (nativeCoherentCone_vertex X)) =
    s ≫ weightedCosliceComparison F z

theorem nativeTotConeFamilyLift_restriction_uncurry
    (X : CosimplicialObject (Complex A)) (x : ClosedCategory A (Complex A)) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let H := simplicialHomDiagram F z ⋙ SSet.opFunctor
    let φ := liftedEnrichedBousfieldKanCone X
    let e : (Δ[0] : SSet.{u+1}) ⟶
        (SSet.uliftFunctor.{u+1,u}).obj (bousfieldKanHolim H) :=
      SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ))))
    let s := inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) (Δ[0] : SSet.{u+1})) ≫
      (((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) ◁ e) ≫
        (uliftTensorIso (nerve I) (bousfieldKanHolim H)).inv ≫
          (SSet.uliftFunctor.{u+1,u}).map (bousfieldKanWeightedNerveEvaluation H)
    relativeFunctorUncurry (nativeTotConeFamilyLift X x ≫
      coneSectionRestriction (nativeCoherentCone X) (coherentNerveVertex x)) =
    (s ▷ (SSet.uliftFunctor.{u+1,u}).obj (SimplicialCategory.sHom x z).op) ≫
      weightedCoslicePrecompositionFamily F x z

```

### 142.2 `WeightedSectionParameterNaturality`（75行）

```lean
theorem weightedSectionsParameterMap_precomp (W H H' : I ⥤ SSet.{u})
    {K B : SSet.{u}} (η : H ⋙ tensorRight B ⟶ H')
    (p : K ⟶ weightedSections W H) :
    (p ⊗ₘ 𝟙 B) ≫ weightedSectionsParameterMap W η =
      weightedSectionsLift (weightedSectionParameterTransform (weightedSectionsUncurry p) η)

theorem reflectedWeightedHomComparison_point_precomposition
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (z : C)
    (φ : bousfieldKanWeight I ⟶ simplicialHomDiagram F z ⋙ SSet.opFunctor) (x : C) :
    let p := weightedSectionsLift
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ)
    (p ⊗ₘ 𝟙 (SimplicialCategory.sHom x z).op) ≫ weightedConeEndPrecomposition F x z =
      snd (Δ[0] : SSet.{u}) (SimplicialCategory.sHom x z).op ≫
        reflectedWeightedHomComparison F z φ x

```

### 142.3 検収と残り

コード **`7d5fde8b1`**。今回初めて読む既存依存を対象ビルド155・156で作成し、残ったelaborationを個別検査で修正した。最終版の鍵付き対象ビルド `/private/tmp/isw2-build157.log` は **6,107 jobs・終了コード0**、新規分だけの監査は **6宣言（4・2）、標準三公理のみ**。鍵は `--class impl --wait 3600`、ビルドと監査の間だけ使用し返却済み。

累計 **291モジュール・18,029行**、外枠まで1,971行。一覧 `/private/tmp/isw2-g10-twohundredninetyone-modules.txt`。sorry・新公理0。計算上限・再帰上限、既存宣言、⑤a、入口・公式監査の変更なし。rootビルド・大きな監査なし。未検証下書きなし。

B06の元の制限の等式は未完。点のYoneda表示には既存 `uliftYonedaMap` がそのまま使えることを確認した。残りは、点を固定したend作用と指定weighted評価をULift直積同型で照合し、同じ相対uncurryの式を戻す接続。B07・B08、C・D、停止点2a・2b、3b-4段0も未完。


## 143. B06：元の指定族の制限の厳密な等式（2026-11-14）

一覧：済み 19／全体 36（うち追加 1）。B06 を完了。B07・B08、C01〜C07、D01〜D08 は未完。

### 143.1 証明と型

`UliftPointTensorEvaluation`（58行）は既存構成の単位・係数移送則。新しい数学のまとまりは追加しない。第0単体への二つの射影の逆則と、その各次数の一意性で証明した。`NativeTotConeRestriction`（79行）は、元の錐の相対uncurryと同じend作用の点評価を照合し、相対uncurryの単射性でB06へ戻す。既存 `uliftYonedaMap` を使い、錐・脚・全高次単体を取り換えていない。

```lean
theorem uliftPointTensorEvaluation (K E Q S : SSet.{u})
    (p : (Δ[0] : SSet.{u}) ⟶ E) (f : K ⊗ E ⟶ Q) :
    let U := SSet.uliftFunctor.{v,u}
    let e := (uliftStdSimplexIso.{u,v} 0).inv ≫ U.map p
    let s := inv (fst (U.obj K) (Δ[0] : SSet.{max u v})) ≫
      (U.obj K ◁ e) ≫ (uliftTensorIso K E).inv ≫ U.map f
    s ▷ U.obj S =
      (U.obj K ◁ U.map (inv (snd (Δ[0] : SSet.{u}) S) ≫ (p ⊗ₘ 𝟙 S))) ≫
        (uliftTensorIso K (E ⊗ S)).inv ≫
          U.map ((α_ K E S).inv ≫ (f ▷ S)) ≫ (uliftTensorIso Q S).hom

theorem nativeTotConeFamilyLift_restriction
    (X : CosimplicialObject (Complex A)) (x : ClosedCategory A (Complex A)) :
    nativeTotConeFamilyLift X x ≫
      coneSectionRestriction (nativeCoherentCone X) (coherentNerveVertex x) =
    (SSet.uliftFunctor.{u+1,u}).map
      (reflectedWeightedHomComparison (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (liftedEnrichedBousfieldKanCone X) x) ≫
      reflectedHomHolimConeComparison (liftedClosedDiagram X) x

```

### 143.2 検収と残り

鍵付き対象ビルド `/private/tmp/isw2-build158.log` は **6,109 jobs・終了コード0**。今回の二本だけの監査は **2宣言（1・1）、標準三公理のみ**。鍵は `--class impl --wait 3600`、対象ビルドと監査の間だけ保持し返却済み。sorry・新公理0、計算上限・再帰上限、既存宣言、⑤a、入口・公式監査の変更なし。rootビルド・大きな監査なし。

累計 **293モジュール・18,166行**、外枠まで1,834行。モジュール一覧 `/private/tmp/isw2-g10-twohundredninetythree-modules.txt`。B07・B08の接続を新規 `NativeTotConeLimit` に準備中（未検証・未コミット）。Bの完了後にC・Dを再見積もりする。


## 144. B07・B08完了：同じ元のTot錐のnative極限性とC・Dの再見積もり（2026-11-14）

一覧：済み 21／全体 36（うち追加 1）。A01〜A12・A05a・B01〜B08完了。C・Dは未完で、停止点2a・2bではない。

### 144.1 型と検証

`NativeTotConeLimit`（60行）。B07はB06・B03・既存のULiftホモトピー輸送と一般のBK→native比較の同値性。B08は同じ指定族 `a`、頂点式 `ha`、制限の同値性 `he` を `coherentCone_isLimit_of_family_lifts` に渡す。dg nerveへの移送には既存の同値による極限保存を使う。新しい模型圏の仮定、錐の選び直しなし。

```lean
theorem nativeTotConeFamilyLift_equivalence
    (X : CosimplicialObject (Complex A)) (x : ClosedCategory A (Complex A)) :
    IsSimplicialHomotopyEquivalence (nativeTotConeFamilyLift X x ≫
      coneSectionRestriction (nativeCoherentCone X) (coherentNerveVertex x))

theorem nativeCoherentCone_isLimit (X : CosimplicialObject (Complex A)) :
    IsLimitCone (nativeCoherentCone X)

theorem nativeDGCone_isLimit (X : CosimplicialObject (Complex A)) :
    IsLimitCone (nativeDGCone X)

```

既存依存だけの対象ビルド159は4,471 jobs・終了コード0。個別検査後の鍵付き対象ビルド160は **6,810 jobs・終了コード0**、新規一本だけの監査は **3宣言、標準三公理のみ**（`/private/tmp/isw2-build160.log`）。鍵 `--class impl --wait 3600` はビルドと監査の間だけ保持し返却済み。sorry・新公理0、計算上限・再帰上限、既存宣言、⑤a、入口・公式監査の変更なし。rootビルド・大きな監査なし。

累計 **294モジュール・18,226行**、外枠20,000行まで1,774行。モジュール一覧 `/private/tmp/isw2-g10-twohundredninetyfour-modules.txt`。未検証下書きなし。

### 144.2 Bの実測とC・Dの見込み

A完了の§101（12,781行）からB完了までの増分は **5,445行**。§72.2のBの600〜900行という見込みに対し約6.1〜9.1倍、差は+4,545〜+4,845行。§111時点のB残量400〜700行に対しても実測4,387行だった。主な差は、指定AW・随伴・Moore・係数移送と実豊穣合成の厳密等式の照合が、抽象的な同値性から自動では得られなかったこと。

| 残るまとまり | 従来の見込み | B実測を受けた現在の追加見込み | 再利用と不確定箇所 |
| --- | ---: | ---: | --- |
| C：標準脚とD(A)輸送 | 400〜700 | 900〜1,600 | rawの極限性はB08済み。出力分解の既存判定と同じ第0頂点の脚、AsSmall/ULiftのstrict等式・join引き戻しの照合が残る |
| D：全図式射・指定錐の族・離散入口 | 500〜900 | 900〜1,600 | 重みの構成は全図式に自然。実際の全nerve上の族、点での同一join射、離散比較の頂点輸送の最終式は未実装 |
| 合計 | 900〜1,600 | **1,800〜3,200** | 完成見込み20,026〜21,426行 |

単純にBの倍率をC・Dへ掛けるのは過大にもなり得る。Bで作ったHomの照合と全パラメータの評価則を再利用できる分を引いて上表としたが、現外枠に収まる保証はない。指定一覧のCの証明を進め、計算上限・型・範囲は弱めず、外枠到達または一覧外の新しい数学が必要と判明した時点で検証済みを保存して停止する。追加の第五のまとまりは現時点で要求しない。


## 145. C01の途中：同じ錐の実際の脚と指定weighted評価（2026-11-14）

一覧：済み 21／全体 36（うち追加 1）。C01の最終等式は未完。以下は既存構成の評価・単位・係数移送・自然性の法則と、C01の証明分割。新しいまとまり・新しい数学の項目は加えない。

### 145.1 型と置き場所

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.JoinConeSectionLeg`（34行）。

```lean
theorem joinCone_section_leg {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (v : K _⦋0⦌) (z : X _⦋0⦌) (h : c.vertex = z) :
    (derivedConeLeg c v).edge = SSet.yonedaEquiv
      ((joinStdSimplexIso 0 0).inv ≫
        (((coherentConeCosliceSection c ≫ eqToHom (congrArg
          (fun w => sliceUnder (SSet.yonedaEquiv.symm w)) h)).app
          (Opposite.op ⦋0⦌) v).val))

```

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.UliftPointEvaluation`（46行）。

```lean
theorem uliftPointEvaluation (K E Q : SSet.{u})
    (p : (Δ[0] : SSet.{u}) ⟶ E) (f : K ⊗ E ⟶ Q) (σ : K _⦋0⦌) :
    let U

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeSectionVertex`（77行）。

```lean
theorem nativeTotCone_cosliceSection_vertex (X : CosimplicialObject (Complex A))
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋0⦌) :
    let I

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeLegEvaluation`（57行）。

```lean
theorem nativeDGCone_leg_weighted (X : CosimplicialObject (Complex A))
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋0⦌) :
    let I

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardLeg`（34行）。

```lean
def standardLeg (X : CosimplicialObject (Complex A)) (n : SimplexCategory) :
    (productTotalFunctor A).obj X ⟶ X.obj n

theorem standardLeg_naturality {X Y : CosimplicialObject (Complex A)}
    (f : X ⟶ Y) (n : SimplexCategory) :
    (productTotalFunctor A).map f ≫ standardLeg A Y n =
      standardLeg A X n ≫ f.app n

```

### 145.2 検収と残り

鍵付き対象ビルド161は **1,800 jobs・終了コード0**、`JoinConeSectionLeg` の新規分だけの監査は **1宣言、標準三公理のみ**。対象ビルド162は **6,109 jobs・終了コード0**、他の四本の新規分だけの監査は **7宣言（1・1・1・4）、標準三公理のみ**。ログ `/private/tmp/isw2-build161.log`・`/private/tmp/isw2-build162.log`。鍵 `--class impl --wait 3600` は一つの整理券で待ち、ビルドと監査の間だけ保持し返却済み。

累計 **299モジュール・18,474行**、外枠まで1,526行。一覧 `/private/tmp/isw2-g10-twohundredninetynine-modules.txt`。sorry・新公理0、計算上限・再帰上限、既存宣言、⑤a、入口・公式監査の変更なし。rootビルド・大きな監査なし。

残るC01の最終成分は、`standardTopEval` による元の反転BK入力の恒等射頂点での評価と、第0頂点を通る標準脚の閉零射の値との等式に絞れた。既存 `reflectedBKFreeCone_generator_top` で同じ自由生成元の評価へ戻せることを個別検査した。未コミットの作業は、一次coherent単体の比較への簡約 `NativeTotConeLegSimplex`、Moore反転の第0項の単位則 `NormalizedMooreReverseZero`、Hom–Totの零行評価 `HomTotalZeroRow`、最終の `NativeTotConeStandardLeg`。前二者は個別検査済み、後二者は検査・証明中であり、今回の検収・累計には含めない。


## 146. C01の途中：同じ一次単体と零次の単位・係数移送則（2026-11-14）

一覧：済み 21／全体 36（うち追加 1）。C01は未完。今回の四本はC01の証明分割と既存構成の法則のみ。計算上限を上げず、添字の等式の消去・既存の両逆則を局所的に分けて証明した。

### 146.1 型

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeLegSimplex`（48行）。

```lean
theorem nativeDGCone_leg_simplex (X : CosimplicialObject (Complex A))
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋0⦌) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let φ := liftedEnrichedBousfieldKanCone X
    let s := (weightedNerveSectionFromTransform
      (CartesianMonoidalCategory.fst (bousfieldKanWeight I)
        ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ)).app (Opposite.op ⦋0⦌)
          (σ, SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
    (derivedConeLeg (nativeDGCone X) (ULift.up σ)).edge =
      (coherentComparison (R := A) (D := Complex A)).app (Opposite.op ⦋1⦌)
        (weightedConeSimplex F z s.2)
```

登録対象：`SerrePositivity.HomologicalAlgebra.NormalizedMooreReverseZero`（34行）。

```lean
theorem normalizedMooreReverse_zero_inclusion (W : SimplicialObject C) :
    (normalizedMooreReverse.app W).f 0 ≫ (inclusionOfMooreComplexMap W).f 0 =
      (inclusionOfMooreComplexMap (SimplicialObject.opFunctor.obj W)).f 0
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalZeroRow`（43行）。

```lean
theorem homTotalComponent_zero_ofHom (P : Complex A) (X : CosimplicialObject (Complex A))
    (f : P ⟶ (productTotalFunctor A).obj X) :
    homTotalComponent P X 0 0 (Cochain.ofHom f) =
      Cochain.ofHom (f ≫ standardZeroLeg A X)
```

登録対象：`SerrePositivity.HomologicalAlgebra.NormalizedMooreInverseInclusion`（32行）。

```lean
theorem normalizedMooreMapInv_inclusion :
    normalizedMooreMapInv F X ≫
      (F.mapHomologicalComplex (.down ℕ)).map (inclusionOfMooreComplexMap X) =
    inclusionOfMooreComplexMap (X ⋙ F) ≫
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app X
```

### 146.2 検収と残り

鍵付き対象ビルド163は **6,114 jobs・終了コード0**（`/private/tmp/isw2-build163.log`）。新規四本だけの監査は **14宣言（1・4・8・1）、標準三公理のみ**。鍵 `--class impl --wait 3600` は一つの整理券で待ち、対象ビルドと小監査の間だけ保持し返却済み。sorry・新公理0、計算上限・再帰上限、既存宣言、⑤a、入口・公式監査の変更なし。rootビルド・大きな監査なし。

累計 **303モジュール・18,631行**、外枠まで1,369行。一覧 `/private/tmp/isw2-g10-threehundredthree-modules.txt`。未コミットは `NativeTotConeStandardLeg` と、その零次係数生成元の計算の分割 `LinearWeightZeroGenerator`。前者は既存 `reflectedBKFreeCone_generator_top` で同じ自由生成元の像へ戻す所まで確認し、後者の係数逆射の法則を証明中。これらは今回の検収・累計に含めない。C01の最終式、C02〜C07、D、停止点2a・2b、3b-4段0は未完。


## 147. C01・C02・C03完了：同じ標準脚・D(A)のnative極限錐・指定頂点（2026-11-14）

一覧：済み 24／全体 36（うち追加 1）。C01・C02・C03完了。C04〜C07・Dは未完であり、停止点2a・2bではない。

### 147.1 証明と再利用

C01は、同じweighted一次単体の比較を既存自由生成元評価へ戻し、係数逆射・Moore反転の零次包含則・元の零行・第0頂点への重み比較・自由単位重みの逆Yoneda評価を合成した。最後のcochainと閉零射の値は、既存 `complexClosedHomEquiv_cochain` と `complexToClosed_map` で照合した。計算上限に当たった深い書き換えは、等式を指定した前後合成へ分割して解消した。上限の引き上げなし。

C02は既存 `dgModuleResolvedInfinity_isLimitCone_of_raw` をそのまま使い、前後の一点係数比較の同値で同じ全join錐を既存D(A)へ送った。`SemifreeRingEvaluationEquivalence` の最終版は既存 `SemifreePointComparison.semifreePointEvaluation_quasiEquivalence` の同じ評価の定義を再利用する薄い接続であり、準同値を作り直していない。C03は同じ後合成の頂点則で、元の積Totの指定半自由分解の頂点を保持する。

### 147.2 型と登録対象

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightZeroGenerator`（89行）。

```lean
theorem normalizedLinearWeightDiagramIso_inv_zero_generator (W : J ⥤ SSet.{0})
    (j : J) (s : (W.obj j) _⦋0⦌) :
    let V := linearizedSimplicialWeight A W.flip
    let N := (normalizedMooreComplex _).obj V
    let e := N.extendXIso ComplexShape.embeddingDownNat (i := 0) (i' := (0 : ℤ)) rfl
    ((inclusionOfMooreComplexMap V).f 0).app j
      (e.hom.app j (((normalizedLinearWeightDiagramIso A W).inv.f 0).app j
        (freeNegativeGenerator ((W ⋙ SSet.uliftFunctor.{u,0}).obj j) 0 (ULift.up s)))) =
      CategoryTheory.Limits.Sigma.ι (fun _ : (W.obj j) _⦋0⦌ => ModuleCat.of A A) s (1 : A)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.SemifreeRingEvaluationEquivalence`（35行）。

```lean
theorem semifreeRingEvaluationDG_quasiEquivalence :
    QuasiEquivalence (semifreeRingEvaluationDG A)

theorem semifreeRingEvaluationInfinity_isQCatEquivalence :
    IsQCatEquivalence (semifreeRingEvaluationInfinity A)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeZeroRow`（44行）。

```lean
theorem normalizedBousfieldKanConeRepresentative_zero_row
    (X : CosimplicialObject (Complex A)) :
    let T := (productTotalFunctor A).obj X
    let H := doubleOppositeDiagram ((homDiagramFunctor T).obj X)
    (negativeChainRowIso (normalizedBousfieldKanWeight (A := A)) 0).inv ≫
      (normalizedBousfieldKanConeRepresentative X).f 0 =
    (normalizedBKStandardWeightMap A).f 0 ≫
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋0⦌)).inv.app H).f 0
        (Cochain.ofHom (standardZeroLeg A X))

```

登録対象：`SerrePositivity.HomologicalAlgebra.FreeWeightEndInverseEvaluation`（43行）。

```lean
theorem freeUnitWeightEndNatIso_inv_generator (j i : J) (f : i ⟶ j)
    (X : Jᵒᵖ ⥤ Complex A) (q : ℤ) (x : (X.obj (op j)).X q) :
    ((((freeUnitWeightEndNatIso A j).inv.app X).f q x).app (op i))
      (Sigma.ι (fun _ : i ⟶ j => ModuleCat.of A A) f (1 : A)) =
    (X.map f.op).f q x

```

登録対象：`SerrePositivity.HomologicalAlgebra.NormalizedMooreReverseExtendZero`（32行）。

```lean
theorem normalizedMooreReverse_extend_zero_inclusion (W : SimplicialObject C) :
    let N := (normalizedMooreComplex C).obj W
    let Nr := (normalizedMooreComplex C).obj (SimplicialObject.opFunctor.obj W)
    (extendMap (normalizedMooreReverse.app W) ComplexShape.embeddingDownNat).f 0 ≫
      (negativeChainRowIso N 0).hom ≫ (inclusionOfMooreComplexMap W).f 0 =
    (negativeChainRowIso Nr 0).hom ≫
      (inclusionOfMooreComplexMap (SimplicialObject.opFunctor.obj W)).f 0

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BKStandardZeroGenerator`（41行）。

```lean
theorem barOverStandard_zero_generator (n : SimplexCategory) :
    let j := op (op n)
    (((barDoubleOppositeOverChainIso SimplexCategory (ModuleCat.of A A)).inv.f 0 ≫
      ((alternatingFaceMapComplex _).map
        (SimplicialRealization.barStandardWeightComparison (ModuleCat.of A A))).f 0).app j)
      (Sigma.ι (fun _ : (bousfieldKanSetWeight.obj (op ⦋0⦌)).obj j => ModuleCat.of A A)
        (nerveVertex (Over.mk (𝟙 n))) (1 : A)) =
    Sigma.ι (fun _ : op n ⟶ op ⦋0⦌ => ModuleCat.of A A)
      (SimplexCategory.const ⦋0⦌ n 0).op (1 : A)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKConeZeroRow`（88行）。

```lean
theorem reflectedBKCone_zero_generator (X : CosimplicialObject (Complex A))
    (n : SimplexCategory) :
    let j := Opposite.op (Opposite.op n)
    let W := (SimplicialObject.opFunctor.obj bousfieldKanSetWeight).flip
    let S := (W ⋙ SSet.uliftFunctor.{u,0}).obj j
    (((((normalizedLinearWeightDiagramIso A W).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat) ≫ normalizedBousfieldKanConeRepresentative X).f 0).app j)
      (freeNegativeGenerator S 0 (ULift.up (nerveVertex (Over.mk (𝟙 n))))) =
    Cochain.ofHom (standardLeg A X n)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeStandardLeg`（81行）。

```lean
theorem nativeDGCone_standardLeg (X : CosimplicialObject (Complex A)) (n : SimplexCategory) :
    (derivedConeLeg (nativeDGCone X) (ULift.up (nerveVertex (AsSmall.up.obj n)))).edge =
      (dgClosedEdge A (Complex A)
        ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map
          (standardLeg A X n))).edge

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotIndex`（41行）。

```lean
def nativeTotIndexIso :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ≅
      (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)

def strictCosimplicialComplexNerve (X : CosimplicialObject (Complex A)) :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶ nerve (Complex A)

theorem nativeTotIndexIso_vertex (n : SimplexCategory) :
    nativeTotIndexIso.{u}.hom.app (Opposite.op ⦋0⦌)
      (ULift.up (nerveVertex (AsSmall.up.obj n))) = ULift.up (nerveVertex n)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDerivedTotCone`（59行）。

```lean
def nativeDerivedDiagram (X : CosimplicialObject (Complex A)) :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶
      derivedInfinityCategory A

def nativeDerivedCone (X : CosimplicialObject (Complex A)) : JoinCone (nativeDerivedDiagram X)

theorem nativeDerivedCone_isLimit (X : CosimplicialObject (Complex A)) :
    IsLimitCone (nativeDerivedCone X)

theorem nativeDerivedCone_vertex (X : CosimplicialObject (Complex A)) :
    (nativeDerivedCone X).vertex =
      (complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌)
        (Simplex.vertex ((productTotalFunctor A).obj X))

```

### 147.3 検収・実測・残り

初回の係数二本だけのビルド165は5,020 jobs・終了コード0、3宣言・標準三公理のみ。その後に既存準同値の再利用へ整理した**最終版**の鍵付き対象ビルド166は **7,849 jobs・終了コード0**、今回十本だけの監査は **24宣言（1・2・1・1・1・5・1・1・4・7）、標準三公理のみ**。ログ `/private/tmp/isw2-build165.log`・`/private/tmp/isw2-build166.log`。鍵は一つの整理券で `--class impl --wait 3600`、対象ビルドと小監査の間だけ保持し返却済み。sorry・新公理0。既存宣言・⑤a・入口・公式監査・mainの変更なし、rootビルド・大きな監査なし。

累計 **313モジュール・19,184行**、外枠まで816行。モジュール一覧 `/private/tmp/isw2-g10-threehundredthirteen-modules.txt`。

C05の宇宙表記は§73.3の許可どおり、複体の対象宇宙u+1とHom宇宙uを分けた。`nerveMap X` は通常のMathlib版だと二つの圏の宇宙を同じに要求するため、そのままの表記を使わず、既存 `nerveAsSmallIso` と `resizedNerveMap (AsSmall.down ⋙ X)` で元のXの全単体を写す `strictCosimplicialComplexNerve` を明示した。元のXを別の図式へ置き換えるものではない。`nativeTotIndexIso` は同じAsSmallの逆と既存 `smallDiagramShapeIso` の合成で、指定次数の頂点の等式も厳密に保つ。C05の最終図式等式自体はまだ未完。

未コミットの作業はC04の一般後合成則 `ConeLegPostcomposition`（個別検査済み）と `NativeDerivedTotLeg`（そのモジュールのビルド待ち）、C05の `ComplexStrictNerveComparison`（証明中）。C04〜C07が済んだ後に停止点2aをまとめ、同じ外枠の中でDへ進む。Dの型・範囲を弱めない。


## 148. C04完了：同じ標準脚のD(A)への実一次単体の像（2026-11-14）

一覧：済み 25／全体 36（うち追加 1）。C01〜C04完了。C05〜C07とDは未完。

### 148.1 型

一般の後合成の評価則はKerodonのLimitsAndColimitsに新規ファイルとして置いた。C04はその法則とC01を同じ元の錐に適用するだけで、錐・頂点・脚を取り換えない。

登録対象：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeLegPostcomposition`（29行）。

```lean
theorem derivedConeLeg_mapJoinCone {K X Y : SSet.{u}} {p : K ⟶ X}
    (f : X ⟶ Y) (c : JoinCone p) (v : K _⦋0⦌) :
    (derivedConeLeg (mapJoinCone f c) v).edge =
      f.app (Opposite.op ⦋1⦌) (derivedConeLeg c v).edge
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDerivedTotLeg`（34行）。

```lean
theorem nativeDerivedCone_standardLeg (X : CosimplicialObject (Complex A)) (n : SimplexCategory) :
    (derivedConeLeg (nativeDerivedCone X) (ULift.up (nerveVertex (AsSmall.up.obj n)))).edge =
      (SerrePositivity.EInfinity.ComplexLimits.complexSemifreeResolutionInfinity A).app
        (Opposite.op ⦋1⦌)
        (dgClosedEdge A (Complex A)
          ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map
            (standardLeg A X n))).edge
```

### 148.2 検収と残り

鍵付き対象ビルド167は **7,849 jobs・終了コード0**（`/private/tmp/isw2-build167.log`）。新規二本だけの監査は **2宣言（1・1）、標準三公理のみ**。鍵は `--class impl --wait 3600`、一つの整理券で待ち、対象ビルド・小監査の間だけ保持し返却済み。sorry・新公理0、計算上限・再帰上限、既存宣言、⑤a、入口・公式監査・mainの変更なし。rootビルド・大きな監査なし。

累計 **315モジュール・19,247行**、外枠まで753行。一覧 `/private/tmp/isw2-g10-threehundredfifteen-modules.txt`。

C05は、同じ閉零圏のstrict nerveからcoherent比較を通した射と、既存 `closedNerveInclusion` との全単体の等式を `ComplexStrictNerveComparison` に分割して証明中。対象の一致は確認できており、閉零射と高次零成分の照合が残る。新しい図式や比較を選ぶものではない。未コミットの下書きはこの一本だけ。停止点2a・2bと3b-4段0は未完。


## 149. C05完了：元のstrict図式の全単体の厳密等式（2026-11-14）

一覧：済み 26／全体 36（うち追加 1）。C01〜C05完了、C06・C07とDは未完。

### 149.1 型と登録対象

既存構成の評価・単位則とC05の証明分割。新しい図式・比較を選ばず、同じstrict Homの定数単体の正次元成分が零であることを、既存の旗の和に項別に適用した。低次では同じ閉零射を評価する。計算上限の増加なし。各ファイルは200行以内。

登録対象：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardConstantTopEvaluation`（65行）。

```lean
theorem standardTopEval_constant_pos (z : (standardHomSpace (R := R) x y) _⦋0⦌)
    (m : ℕ) (hm : 0 < m) :
    standardTopEval x y m (PinchedHom.constant z m) = 0

theorem standardTopEval_constant_zero (z : (standardHomSpace (R := R) x y) _⦋0⦌) :
    standardTopEval x y 0 (PinchedHom.constant z 0) =
      (standardZeroEquiv (R := R) x y z).val

theorem standardZeroEquiv_homEquiv (x y : ClosedCategory R D) (f : x ⟶ y) :
    standardZeroEquiv (R := R) (D := D) x y
      (SimplicialCategory.homEquiv' x y f) = closedHomEquiv R D x y f

```

登録対象：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictCubeEvaluation`（35行）。

```lean
theorem coherentCubeComponent_orderDiagram_pos {J : Type u} [LinearOrder J]
    (F : J ⥤ ClosedCategory R D) {a b : J} (hab : a < b)
    (S : Finset (Set.Ioo a b)) (hS : 0 < S.card) :
    coherentCubeComponent (enrichedFunctorOfOrderDiagram F) hab S = 0

```

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexStrictNerveComparison`（71行）。

```lean
theorem complexClosedNerve_coherentComparison :
    nerveToCoherent (ClosedCategory A (Complex A)) ≫
      coherentComparison (R := A) (D := Complex A) = closedNerveInclusion A (Complex A)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDerivedDiagramEq`（41行）。

```lean
theorem nativeDerivedDiagram_eq (X : CosimplicialObject (Complex A)) :
    nativeDerivedDiagram X = nativeTotIndexIso.hom ≫ strictCosimplicialComplexNerve X ≫
      complexOrdinaryDerivedSource A

```

### 149.2 検収と残り

コード `5674cfded`。鍵付き対象ビルド168・169・170はそれぞれ **3,755・3,944・7,836 jobs、すべて終了コード0**。新規四本だけの分割監査は **3 + 2 + 1 = 6宣言、標準三公理のみ**（各ログ `/private/tmp/isw2-build168.log`〜`170.log`）。一つの整理券ずつ `--class impl --wait 3600`、ビルドと小監査の間だけ保持し返却済み。sorry・新公理0、既存宣言・⑤a・入口・公式監査・mainの変更なし。

累計 **319モジュール・19,459行**、外枠まで541行。一覧 `/private/tmp/isw2-g10-threehundrednineteen-modules.txt`。C06・C07は同じslice制限の同型と底図式の等式消去で証明中。Dは未着手。外枠と型つき一覧の規則を維持する。


## 150. 停止点2a：B・C完了、同じ元のstrict図式のnative極限錐（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。A・B・C完了。D01〜D08未完。停止点2bと3b-2全体の完成はまだ宣言しない。停止点2aの単独取り込み点はコード `b43d4be81`（C05 `5674cfded`を含む）。

### 150.1 C06・C07の型と登録対象

一般の部分はKerodonに、G10の適用はHAに置いた。slice制限の既存の同型と終頂点の同型不変性、同じ底図式の等式消去のみを使う既存構成の法則。各ファイル200行以内。

登録対象：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SpecifiedConeReindex`（43行）。

```lean
theorem restrictJoinCone_isLimit_of_isIso {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (f : L ⟶ K) [IsIso f] (hc : IsLimitCone c) :
    IsLimitCone (restrictJoinCone c f)

def joinConeOfDiagramEq {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCone p) : JoinCone q := h ▸ c

/-- 同じ全join射を保つ。 -/
theorem joinConeOfDiagramEq_val {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCone p) : (joinConeOfDiagramEq h c).val = c.val

theorem joinConeOfDiagramEq_isLimit {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (joinConeOfDiagramEq h c)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StrictDerivedTotCone`（51行）。

```lean
theorem nativeDerivedDiagram_reindex (X : CosimplicialObject (Complex A)) :
    nativeTotIndexIso.inv ≫ nativeDerivedDiagram X =
      strictCosimplicialComplexNerve X ≫ complexOrdinaryDerivedSource A

def strictDerivedTotCone (X : CosimplicialObject (Complex A)) :
    JoinCone (strictCosimplicialComplexNerve X ≫ complexOrdinaryDerivedSource A)

theorem strictDerivedTotCone_isLimit (X : CosimplicialObject (Complex A)) :
    IsLimitCone (strictDerivedTotCone X)

theorem strictDerivedTotCone_pullback (X : CosimplicialObject (Complex A)) :
    joinMap (𝟙 (Δ[0] : SSet.{u+1})) nativeTotIndexIso.hom ≫
      (strictDerivedTotCone X).val = (nativeDerivedCone X).val

```

### 150.2 検収と見込みとの差

鍵付き対象ビルド171は **7,841 jobs、終了コード0**。新規二本の小監査は **10宣言（4・6）、標準三公理のみ**。ログ `/private/tmp/isw2-build171.log`。`--class impl --wait 3600`、鍵は対象ビルドと小監査の間だけ保持し返却済み。sorry・新公理0、計算上限の増加、既存宣言、⑤a、入口・公式監査・mainの変更なし。

累計 **321モジュール・19,553行**、外枠まで447行。一覧 `/private/tmp/isw2-g10-threehundredtwentyone-modules.txt`。B完了18,226行からC完了までの増分は **1,327行**。§72.2の400〜700行に対して+627〜+927行、B実測を受けた§144.2の900〜1,600行の範囲内。標準脚の零単体の評価とstrict nerveの全単体の等式を明示する部分に増分が集中した。

| まとまり | §72.2の見込み | 現在の実測・残り |
| --- | ---: | --- |
| A：正規化テンソル／積重み | 残量400〜700行（§72.2） | §72の8,834行から§101の12,781行まで3,947行の増分（全体のA完了時点は12,781行） |
| B：指定豊穣Homとnative極限性 | 600〜900行 | 完了5,445行（A完了からの増分） |
| C：標準脚とD(A)輸送 | 400〜700行 | 完了1,327行 |
| D：全図式射・指定錐の族・離散入口 | 500〜900行 | 未完、§144.2の900〜1,600行を維持 |

予測だけで再停止せず、D01の全族の境界を固定する同じ全関手の部品から進める。D04の辺だけを全族の代用品にしない。外枠到達または一覧外の新しい数学が必要になった時点で検証済みをコミットして止め、3b-4の紙の整理へ移る。


## 151. Dの途中：全境界・指定複体代表の自然性・離散raw錐（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。D01〜D08は最終の型をまだ閉じていないため、完了数に加えない。以下はD01・D02・D04・D05の既存構成の自然性・合成則と証明分割であり、新しい数学のまとまりを追加しない。

### 151.1 型と登録対象

全評価を同じ全関手で固定し、元の指定BK比較を全図式射に自然にまとめた。零単体だけの族を全錐族と呼ばない。離散の補助錐は `rawCosimplicialModuleCone` と明記し、元の積Totを頂点にする。D06の整数零延長した交代余面複体を頂点にする最終 `cosimplicialModuleCone` は、このraw錐から同じ指定自然同型で移す工程が残る。後で既存宣言の型を変更して頂点を差し替える方針にはしない。

§73.4の `ρ_.inv` と `jX : Δ[0] ⟶ B` の積の紙の略記は、実際のMathlibでは単位対象（定値PUnit）と `Δ[0]` が定義的に一致しないため、そのままでは型が合わない。今回の `strictCosimplicialEvaluationNerve_at` は、既存の標準射影同型 `fst K Δ[0]` の逆を明示した同じ点での評価で述べた。点の選び直しやFunctorIsoへの弱化ではない。D03・D07もこの標準同型を表記に含める。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightEndHomTargetNaturality`（89行）。

```lean
theorem extendedChainHomRows_postcomp {H H' : CochainComplex (Jᵒᵖ ⥤ ModuleCat A) ℤ}
    (f : H ⟶ H') (q : ℤ) (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q)
    (n : ℕ) :
    extendedChainHomRows K H' q ((intervalHomPrePost A (𝟙 _) f).f q z) n =
      extendedChainHomRows K H q z n ≫ f.f (q-n)

theorem weightEndHomIso_target_naturality {X Y : Jᵒᵖ ⥤ Complex A} (f : X ⟶ Y) :
    (linearWeightEndTotalMap A f).app (op K) ≫ (weightEndHomIso A K Y).hom =
      (weightEndHomIso A K X).hom ≫
        intervalHomPrePost A (𝟙 (K.extend ComplexShape.embeddingDownNat))
          ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).map f)

theorem weightEndHomIso_target_naturality_postcompose {X Y : Jᵒᵖ ⥤ Complex A}
    (f : X ⟶ Y) :
    (linearWeightEndTotalMap A f).app (op K) ≫ (weightEndHomIso A K Y).hom =
      (weightEndHomIso A K X).hom ≫
        SerrePositivity.EInfinity.PowerOperation.linearHomComplexPostcompose A
          (K.extend ComplexShape.embeddingDownNat)
          ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).map f)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotFamilyBoundaries`（75行）。

```lean
def strictCosimplicialEvaluationNerve :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⊗
      nerve (CosimplicialObject (Complex A)) ⟶ nerve (Complex A) where
  app _ := ↾fun p => (p.1.down.prod' p.2) ⋙
    evaluationUncurried SimplexCategory (Complex A)
  naturality _ _ _

theorem strictCosimplicialEvaluationNerve_at (X : CosimplicialObject (Complex A)) :
    inv (fst ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) (Δ[0] : SSet.{u+1})) ≫
      (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex X)) ≫
        strictCosimplicialEvaluationNerve A = strictCosimplicialComplexNerve X

def derivedTotEvaluationFamily :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⊗
      nerve (CosimplicialObject (Complex A)) ⟶ derivedInfinityCategory A

def derivedTotVertexFamily :
    nerve (CosimplicialObject (Complex A)) ⟶ derivedInfinityCategory A

theorem derivedTotVertexFamily_map {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (derivedTotVertexFamily A).app (Opposite.op ⦋1⦌) (nerve.edgeMk f).edge =
      (complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk ((productTotalFunctor A).map f)).edge

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanComparisonNaturality`（77行）。

```lean
def normalizedBousfieldKanHomFunctor : CosimplicialObject (Complex A) ⥤ Complex A

theorem normalizedBousfieldKanHomComparison_naturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    normalizedBousfieldKanHomComparison X ≫ normalizedBousfieldKanHomFunctor.map f =
      (productTotalFunctor A).map f ≫ normalizedBousfieldKanHomComparison Y

def normalizedBousfieldKanHomComparisonNatTrans :
    productTotalFunctor A ⟶ normalizedBousfieldKanHomFunctor where
  app X := normalizedBousfieldKanHomComparison X
  naturality _ _ f := (normalizedBousfieldKanHomComparison_naturality f).symm

/-- 同じHom–Tot比較と指定正規化比較を全図式上で合成する。 -/
def homToNormalizedBousfieldKanNatTrans (P : Complex A) :
    productTotalFunctor A ⋙ homFunctor P ⟶
      homDiagramFunctor P ⋙ normalizedBousfieldKanHomFunctor

theorem homToNormalizedBousfieldKanNatTrans_app (P : Complex A)
    (X : CosimplicialObject (Complex A)) :
    (homToNormalizedBousfieldKanNatTrans P).app X = homToNormalizedBousfieldKan P X

theorem homToNormalizedBousfieldKan_naturality (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (homFunctor P).map ((productTotalFunctor A).map f) ≫ homToNormalizedBousfieldKan P Y =
      homToNormalizedBousfieldKan P X ≫
        normalizedBousfieldKanHomFunctor.map ((homDiagramFunctor P).map f)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeRepresentativeNaturality`（49行）。

```lean
def normalizedBKConeTargetMap (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor P).obj X)) ⟶
    (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor P).obj Y))

theorem normalizedBousfieldKanRepresentative_naturality (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y)
    (g : P ⟶ (productTotalFunctor A).obj X) :
    normalizedBousfieldKanRepresentative P X g ≫ normalizedBKConeTargetMap P f =
      normalizedBousfieldKanRepresentative P Y (g ≫ (productTotalFunctor A).map f)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteNativeTotCone`（58行）。

```lean
def strictCosimplicialModuleNerve (M : CosimplicialObject (ModuleCat.{u} A)) :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶ nerve (ModuleCat.{u} A)

def discreteModuleSource : nerve (ModuleCat.{u} A) ⟶ derivedInfinityCategory A

theorem discreteDiagram_strict (M : CosimplicialObject (ModuleCat.{u} A)) :
    strictCosimplicialComplexNerve ((discreteDiagramFunctor A).obj M) ≫
      complexOrdinaryDerivedSource A =
    strictCosimplicialModuleNerve A M ≫ discreteModuleSource A

def rawCosimplicialModuleCone (M : CosimplicialObject (ModuleCat.{u} A)) :
    JoinCone (strictCosimplicialModuleNerve A M ≫ discreteModuleSource A)

theorem rawCosimplicialModuleCone_isLimit (M : CosimplicialObject (ModuleCat.{u} A)) :
    IsLimitCone (rawCosimplicialModuleCone A M)

```

### 151.2 検収欄（最終の対象ビルド待ち）

鍵付き対象ビルド172は線形Homの単位則の型推論で失敗し、鍵を返却した。型を明示して修正後の173は **7,845 jobs・終了コード0**、三本だけの小監査は **21宣言（3・7・11）、標準三公理のみ**。これを失敗した172の成功と取り違えない。残る実複体代表の自然性・離散raw錐の個別検査は成功し、最終の二本の対象ビルド174と小監査を `--class impl --wait 3600` の一枚の整理券で待っている。174の確定結果とコードコミットは次節へ記す。

新規五本合計348行、草稿込み累計 **326モジュール・19,901行**、外枠20,000行まで **99行**。一覧 `/private/tmp/isw2-g10-threehundredtwentysix-modules.txt`。どのファイルも200行以内。全錐族の本体・両境界・各点で同じ全join射になる式、離散頂点の移送・全族・ホモロジー入口は未完。


## 152. 代わりの紙の作業：3b-4 §38.2の1・2の型つき段0案（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。これはG10完成後の3b-4を開始したという意味ではなく、外枠に近づいた際の指定された代わりの紙の作業。以下のR番号は**3b-4の提案一覧**であり、G10の36項目には加えない。Leanでelaboration・証明済みの宣言と数えない。既存ファイル、入口、⑤aの欄は変更しない。

### 152.1 既存の道具と、③-aから使う場所

- `EInfinity/BarrattEccles/FramedLimit.lean` の `framedLimitFunctor A K` は既に**全関手**。同じ右frame・一点重みのendを再定義しない。`FramedLimitLocalization.lean` の `framedLimit_inverts` と `localizedFramedLimit` は通常局所化への降下に使う。
- `FramedLimitCarrierDerivedComparison.lean` の `carrierFramedLimitComparisonIso` は台の**通常局所化**における比較。`_cone`・`_forgetCone` は同じ通常錐との両立を照合する入力。これだけでnativeな全join錐族の同型が済んだとは数えない。
- `CAlgUnderlyingDerivedComparison.lean` の `algebraCAlgSource_underlyingDerivedIso A` は実際の `algebraCAlgSource A ≫ cAlgForgetDerived A` と `nerveMap forget ≫ complexOrdinaryDerivedSource A` の**全関手同型**。Uを別の通常忘却関手で代用しない。
- `FreeProbeDerivedFreeForget.lean` の `cAlgForgetDerived_mapJoinCone_isLimit A c hc` は**追加の輸送条件を引数に取らない**既存の定理。ユーザーの11-14の訂正に従い、そのまま使用する。`FreeProbeUnitTransportCondition` を未証明の前提として再導入しない。
- 実現では `HomotopyWeight/{TensorRealization,PointwiseRealization,FrameLifting}` と既存のframe/重みの関手性を使う。右Quillen性や全対象fibrantだけでUの実現保存・通常limによるTotの計算を推論しない。

③-aの3b-3が必要な場所は二つ。(i) strictな複体図式の局所化から `Fun(I_J,D(A))` への全評価と同型を使い、下のR05・R10を局所化上の関手同型へ降ろす所。(ii) 3b-1から3b-3へ移した**全パラメータ実現余錐**とその輸送をR09・R10で使う所。図式ごとの余錐だけで全族の比較を閉じない。R01〜R04のstrict入力・台の通常比較の整理は③-aを待たずにできる。

任意のcoherent **BE値**図式への拡張（§38.2の3）は別の段。加群値の評価同値からBE値の厳密化を得たとは扱わない。そこに来たらBE版の評価同値か一般の模型定理のBEへの適用条件を具体的に受け取る。今回の段0案はその入力を仮定に隠して完成扱いしない。

### 152.2 紙の記法とTot側の型案

`E := (BarrattEccles.operad A).Algebra`、`CA := CAlg_R A`、`DA := derivedInfinityCategory A`、`S := algebraCAlgSource A`、`U := cAlgForgetDerived A`。`J₊ := AsSmall.{u} SimplexCategory`、`J₋ := AsSmall.{u} SimplexCategoryᵒᵖ`、`K± := (SSet.uliftFunctor.{u+1,u}).obj (nerve J±)`、`B± := nerve (J± ⥤ E)` とする。元のΔ・Δᵒᵖとの往復はG10の `nativeTotIndexIso` と同じAsSmall・ULiftの指定同型を使う。

`strictBE : (J± ⥤ E) → (K± ⟶ CA)` は、同じFの全nerveを `resizedNerveMap` で読みSへ後合成する表示。`evalBE± : K± ⊗ B± ⟶ CA` は同じ評価関手の全nerve。`forget± : (J± ⥤ E) ⥤ (J± ⥤ Complex A)` は既存 `Diagram.forget`。`forgetCosimp` はそのΔへの指定AsSmall引き戻し。以下はこの**紙の略記を展開してから検査する型案**。

```lean
-- R01：既存の計算全関手のnerve。新しいend/frameを選ばない。
def strictBETotVertex : B₊ ⟶ CA :=
  nerveMap (BarrattEccles.framedLimitFunctor A J₊) ≫ S

-- R02：同じ計算対象の、全図式射を含む指定錐族。
def strictBETotConeFamily : join (Δ[0] : SSet.{u+1}) K₊ ⊗ B₊ ⟶ CA
theorem strictBETotConeFamily_boundaries :
  (joinInl Δ[0] K₊ ⊗ₘ 𝟙 B₊) ≫ strictBETotConeFamily =
    pointLeftProjection B₊ ≫ strictBETotVertex ∧
  (joinInr Δ[0] K₊ ⊗ₘ 𝟙 B₊) ≫ strictBETotConeFamily = evalBE₊
def strictBETotCone (F : J₊ ⥤ E) : JoinCone (strictBE F)
theorem strictBETotConeFamily_at (F : J₊ ⥤ E) :
  pointRightSection (join Δ[0] K₊) (nerveVertex F) ≫ strictBETotConeFamily =
    (strictBETotCone F).val

-- R03：同じ指定錐そのもののnative極限性。
theorem strictBETotCone_isLimit (F : J₊ ⥤ E) : IsLimitCone (strictBETotCone F)
theorem strictBETotCone_vertex (F : J₊ ⥤ E) :
  (strictBETotCone F).vertex = S.app (Opposite.op ⦋0⦌)
    (nerveVertex ((BarrattEccles.framedLimitFunctor A J₊).obj F))

-- R04：Uの既存の全比較を、同じ評価・錐の全族へ適用。
def strictBETotUnderlyingIso : FunctorIso
  (strictBETotVertex ≫ U)
  (nerveMap forgetCosimp ≫ derivedTotVertexFamily A)
def strictBETotUnderlyingConeFamilyIso : FunctorIso
  (strictBETotConeFamily ≫ U)
  ((𝟙 _ ⊗ₘ nerveMap forgetCosimp) ≫ derivedTotConeFamily)
-- 上の同型の右境界への制限はalgebraCAlgSource_underlyingDerivedIsoの
-- 評価前合成、左境界への制限はstrictBETotUnderlyingIsoそのもの。

-- R05：上記をstrict図式の∞局所化へ降ろした全関手比較。
def strictBETotLocalizedUnderlyingIso : FunctorIso
  (TotBE ≫ U) (ForgetStrictBEInfinity ≫ TotDA)
```

`pointLeftProjection B` は `Δ[0] ⊗ B → B` の指定射影、`pointRightSection L v` は `inv (fst L Δ[0]) ≫ (𝟙 L ⊗ₘ yonedaEquiv.symm v)`。Mathlibの単位PUnitとΔ[0]を混同しない。R02〜R04の同じ全族・境界の等式は省略しない。R04の比較が必要とするG10の `derivedTotConeFamily` は**まだ未完**。

R03でUによる極限保存を使うのは、まず得られたBEの極限錐の**像**の検収。Uが保存するからBEの元の錐が極限だ、と逆向きに推論しない。BEの元の普遍性は既存frameのHom比較・模型の導来普遍性と指定native錐の橋から得る必要がある。

### 152.3 実現側・制限の型案

```lean
-- R06：既存の左frame・cofibrant重み・図式置換からの計算全関手。
def strictBERealizationModel : (J₋ ⥤ E) ⥤ E
def strictBERealizationVertex : B₋ ⟶ CA := nerveMap strictBERealizationModel ≫ S

-- R07：全パラメータの指定余錐と両境界。
def strictBERealizationCoconeFamily : join K₋ (Δ[0] : SSet.{u+1}) ⊗ B₋ ⟶ CA
-- 左境界 = evalBE₋、右境界 = pointLeftProjection B₋ ≫ strictBERealizationVertex。
def strictBERealizationCocone (F : J₋ ⥤ E) : JoinCocone (strictBE F)
theorem strictBERealizationCoconeFamily_at (F : J₋ ⥤ E) :
  pointRightSection (join K₋ Δ[0]) (nerveVertex F) ≫
    strictBERealizationCoconeFamily = (strictBERealizationCocone F).val

-- R08：同じ余錐そのもののnative余極限性。
theorem strictBERealizationCocone_isColimit (F : J₋ ⥤ E) :
  IsColimitCone (strictBERealizationCocone F)

-- R09：台のstrict図式の実現への全比較と同じ余錐の制限。
def strictBERealizationUnderlyingIso : FunctorIso
  (strictBERealizationVertex ≫ U)
  (nerveMap forgetSimplicial ≫ complexRealizationVertexFamily)
def strictBERealizationUnderlyingCoconeFamilyIso : FunctorIso
  (strictBERealizationCoconeFamily ≫ U)
  ((𝟙 _ ⊗ₘ nerveMap forgetSimplicial) ≫ complexRealizationCoconeFamily)
-- 両境界の制限はS≫Uの既存比較とstrictBERealizationUnderlyingIso。

-- R10：strict図式の∞局所化上の全関手比較。
def strictBERealizationLocalizedUnderlyingIso : FunctorIso
  (RealizeBE ≫ U) (ForgetStrictBEInfinity ≫ RealizeDA)
```

R06は「通常colimの台が通常colim」という事実のみで導来実現の台を同定しない。R09の `complexRealizationCoconeFamily` は③-aの3b-3が組み立てる3b-1第四行の全族を要求する。R05・R10に出るstrict図式局所化の実評価は、元の通常図式の射・全単体との指定同型付きで受け取る。BE図式局所化と任意の `Fun(K±,CA)` の評価同値を、加群版のR2から無条件には導かない。

最後にR11として、既存の離散BE埋め込みに制限したR02〜R05が⑤aの `ofCosimplicial_forget`・`TotalizationCone` の**既存の型・同じ指定頂点**へ一致する照合を置く。ここは⑤aの更新後の入口の型を読む段で、欄の型をこちらで変えない。R12は係数変更と指定錐族の制限の両立。必要な全同型の型を⑤aの既存欄に合わせてから確定する。この二つを確定前から完了項目に数えない。

### 152.4 置き場所・見込み・停止境界

| 束 | 提案する新規ファイル | 見込み（行、docstring/import込み） |
| --- | --- | ---: |
| R01〜R03 strict Totの模型・同じnative錐族 | `EInfinity/BarrattEccles/StrictDiagramTotalizationComparison*.lean` | 1,400〜2,300 |
| R04〜R05 TotのU比較・局所化への全輸送 | `.../StrictDiagramTotUnderlying*.lean` | 1,000〜1,800 |
| R06〜R08 strict実現の模型・同じ余錐族 | `.../StrictDiagramRealizationComparison*.lean` | 1,600〜2,800 |
| R09〜R10 実現のU比較・全関手比較 | `.../StrictDiagramRealizationUnderlying*.lean` | 1,200〜2,000 |
| R11〜R12 離散制限・既存入口・係数変更の照合 | `.../StrictDiagramDiscreteCompatibility*.lean` | 500〜900 |
| 合計 | | **5,700〜9,800** |

これは新しい承認済み外枠ではなく、3b-1/G10の実測を踏まえた**紙の提案**。R11・R12の型とBEのnative錐への模型の橋を読んだ後で再見積もりする。一般になった錐の等式移送・族の貼り合わせはKerodon、加群の共通比較はHA/DerivedCategoryModels、BE固有の照合だけを新規BEファイルに置く。既存 `FramedLimit*`、`CAlgUnderlyingDerivedComparison`、⑤aのファイルを変更・再構築しない。点つきKanのTotは作らない。今回この紙のためのBEビルドは行っていない。


## 153. 外枠直前の保存点：停止点2aは完成、Dは未完（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。B4は§137で完了済み。B・Cの停止点2aはコード `b43d4be81`、報告 `ecb21022f`（表の訂正 `fe5555f64`）。その後のD補助五本は **`acfde8f61`**。停止点2b・G10全体の完成は未達成。

### 153.1 最終検収

§151の最終の二本の鍵付き対象ビルド174は **7,850 jobs・終了コード0**、小監査は **12宣言（4・8）、標準三公理のみ**（`/private/tmp/isw2-build174.log`）。173の三本21宣言と合わせ、今回D補助五本の監査は **33宣言**。これは新規五本だけの小監査であり、全段階II・全326本を今回再監査した数字ではない。途中の失敗172は成功に含めない。

鍵は各回 `--class impl --wait 3600`、整理券一枚、対象ビルドと小監査の間だけ保持し、各ハンドルの終了コード0を確認して返却済み。sorry・新公理0、計算上限・再帰上限の増加、既存宣言・⑤a・入口・公式監査・mainへの変更なし。rootビルド・大きな監査なし。未検証のLean下書きは残さない。

全累計の対象一覧は永続ファイル `formalization-plans/stage-ii/inf-supply-b/is-w2-g10-20261114-modules.json` にも保存した。これはG10累計の対象一覧であり、mainへ未登録の差分一覧を自動的に意味しない。今回追加分の登録候補は§149〜§151に列挙した各モジュール。入口・公式監査への登録は調整役に任せる。

### 153.2 外枠と、次に残る具体的な束

現ソースを一覧から再集計して **326モジュール・19,901行**、外枠20,000行まで **99行**。Dの全族の型を弱めたり、既存の部分補題を不自然に圧縮して枠を空けたりはしない。

| 未完の項目 | 次に必要な同じ構成の照合 | 追加見込み |
| --- | --- | ---: |
| D01〜D03 | §151の実複体代表の自然性を、同じΓ・反転・豊穣Hom・BK切断の比較へ運び、元の全join錐を全パラメータで貼り合わせる。両境界と各Xでの**同じ全join射**を閉じる | 350〜650行 |
| D04 | 頂点辺の式は§151で証明済み。D02で全族の左境界をこの同じ `derivedTotVertexFamily` と確定して接続する | 上の束に含む |
| D05〜D06 | `rawCosimplicialModuleCone` を、既存 `discreteTotalCochainNatIso` により**整数零延長した交代余面複体を頂点とする**指定錐へ移す。raw頂点とその頂点の等号を仮定しない | 150〜250行 |
| D07〜D08 | 同じ離散頂点移送を全図式射・全錐族に行い、既存の導来ホモロジー比較へ接続する | 250〜450行 |
| 合計 | | **750〜1,350行** |

99行の残枠では、次のD01の全join族と各点の厳密照合の束を収められない所まで来た。`coordination.md` §2（62〜65行の規模上限・型つき一覧・代わりの紙の作業）とIS-W2 §16の外枠に従い、**検証済みをコミットした上で、この線の追加Leanをここで区切る**。新しい第五のまとまり・範囲の縮小・新しい模型圏仮定を要求しているのではなく、承認済みDの同じ型の工程が残る。数を使い切るための補題追加はしない。

代わりの紙の作業として§152に、3b-4の§38.2の1・2について、既存部品、全関手・同じ指定錐族の型案、③-aの3b-3を使う場所、規模の案を残した。BEの新規Leanや点つきKanのTotは開始していない。この紙をG10や3b-4の検証済み完成と数えない。再開箇所は上表のD01の全族への自然性の輸送であり、B4やB・Cの再実装ではない。


## 154. 再開：D01の指定複体代表から点ごとの実Γまでの全自然性（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。D01〜D08の最終結論は未完であり、今回の法則・証明分割をIDの完了数へ加えない。前ターンは停止点2aとD補助の検証・コミットという進捗。mainの `d7b418962` を作業枝へfast-forwardで取り込み、IS-W2 §17・§18と /goal 更新を読んで再開した。旧20,000行の停止は解除、G10の外枠は **23,000行**。G10後の3b-4はTot側を先に、外枠15,000行、停止点3b-4a・3b-4bの後に任意coherent BE図式の段0まで進む指示を保持する。

### 154.1 型と登録候補

同じ閉零射によるHom図式の前合成を構成済みの行合成則に特殊化し、元の指定BK錐代表の図式方向と頂点方向の自然性を一致させた。その等式を既存 `normalizedLinearWeightHomEquiv_postcomp` と `pointwiseTruncationGammaIso` の全自然性で移した。新しい比較・点・錐を選び直さず、Moore反転と再反転も元のもの。新しい数学のまとまりではなくD01の既存構成の自然性・合成・係数移送の法則。

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeSourceNaturality`（98行）。

```lean
def bousfieldKanHomSourceMap {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    doubleOppositeDiagram ((homDiagramFunctor Q).obj X) ⟶
      doubleOppositeDiagram ((homDiagramFunctor P).obj X) where
  app j := homPrecompose f (X.obj ((opOpEquivalence SimplexCategory).functor.obj j))
  naturality i j a

def normalizedBKConeSourceMap {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor Q).obj X)) ⟶
    (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor P).obj X))

theorem normalizedBKConeSourceMap_f {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) (q : ℤ) :
    (normalizedBKConeSourceMap f X).f q =
      homDiagramDegreePrecompose X 0 q q (zero_add q) (Cochain.ofHom f)

theorem normalizedBousfieldKanRepresentative_precompose {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (f : P ⟶ Q)
    (g : Q ⟶ (productTotalFunctor A).obj X) :
    normalizedBousfieldKanRepresentative Q X g ≫ normalizedBKConeSourceMap f X =
      normalizedBousfieldKanRepresentative P X (f ≫ g)

theorem normalizedBousfieldKanConeRepresentative_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    normalizedBousfieldKanConeRepresentative X ≫
        normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f =
      normalizedBousfieldKanConeRepresentative Y ≫
        normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKSetConeNaturality`（86行）。

```lean
def bousfieldKanSetHomFunctor :
    CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ ⥤
      SimplicialObject (SimplexCategoryᵒᵖᵒᵖ ⥤ Type u)

theorem normalizedBousfieldKanSetCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    normalizedBousfieldKanSetCone X ≫
        (bousfieldKanSetHomFunctor A).map
          (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f) =
      normalizedBousfieldKanSetCone Y ≫
        (bousfieldKanSetHomFunctor A).map
          (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y)

theorem reflectedBousfieldKanConeRepresentative_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    reflectedBousfieldKanConeRepresentative X ≫
        normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f =
      reflectedBousfieldKanConeRepresentative Y ≫
        normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y

theorem reflectedBousfieldKanSetCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    reflectedBousfieldKanSetCone X ≫
        (bousfieldKanSetHomFunctor A).map
          (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f) =
      reflectedBousfieldKanSetCone Y ≫
        (bousfieldKanSetHomFunctor A).map
          (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.PointwiseBKConeNaturality`（107行）。

```lean
def pointwiseBKSetHomFunctor :
    CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ ⥤
      SimplexCategoryᵒᵖᵒᵖ ⥤ SSet.{u}

def pointwiseBKSetHomComparison
    (H : CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ)

theorem pointwiseBKSetHomComparison_naturality
    {H H' : CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ} (f : H ⟶ H') :
    (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖᵒᵖ (Type u)).map
        ((bousfieldKanSetHomFunctor A).map f) ≫ pointwiseBKSetHomComparison A H' =
      pointwiseBKSetHomComparison A H ≫ (pointwiseBKSetHomFunctor A).map f

theorem reversedWeightPointwiseBousfieldKanCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    reversedWeightPointwiseBousfieldKanCone X ≫
        (pointwiseBKSetHomFunctor A).map
          (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f) =
      reversedWeightPointwiseBousfieldKanCone Y ≫
        (pointwiseBKSetHomFunctor A).map
          (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y)

theorem reflectedPointwiseBousfieldKanCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    reflectedPointwiseBousfieldKanCone X ≫
        Functor.whiskerRight ((pointwiseBKSetHomFunctor A).map
          (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f))
          SimplicialObject.opFunctor =
      reflectedPointwiseBousfieldKanCone Y ≫
        Functor.whiskerRight ((pointwiseBKSetHomFunctor A).map
          (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y))
          SimplicialObject.opFunctor

```

`pointwiseBKSetHomComparison A H` の推論された型は、`(flipFunctor Δᵒᵖ Δᵒᵖᵒᵖ (Type u)).obj ((bousfieldKanSetHomFunctor A).obj H) ⟶ (pointwiseBKSetHomFunctor A).obj H`。上の紙の表示で型を省いた場合もこの全図式射を意味し、各点のHomの元だけの主張ではない。

### 154.2 検収と継続箇所

コード **`00613f0ed`**。鍵付き対象ビルド175・176・177はそれぞれ **2,759・2,772・2,785 jobs、終了コード0**。各新規一本だけの小監査は **9・8・10宣言、いずれも標準三公理のみ**（合計27は今回三本だけの数字）。ログ `/private/tmp/isw2-build175.log`〜`177.log`。各回 `--class impl --wait 3600`、整理券一枚、対象ビルド・小監査の間だけ保持して返却済み。sorry・新公理0、計算上限の増加、既存宣言、⑤a、入口・公式監査・mainへの変更なし。200行超のファイルなし。

累計 **329モジュール・20,192行**、外枠まで **2,808行**。累計一覧は `is-w2-g10-20261114-modules.json`。D01の全錐族はまだ構成していない。次は同じΓ比較と実豊穣Homの前合成を照合する `DoldKanClosedPrecomposition`（未検証の草稿）と、その比較による同じBK錐の自然性の移送。D02〜D08と3b-4の範囲を削らず継続する。


## 155. D01の途中：実豊穣Hom・native錐の同じ入力・混合係数への接続（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。D01の全族はまだ未完。以下は既存構成の自然性・単位・合成・係数移送・表示の法則と証明分割で、ID付きの新しい数学を加えない。

### 155.1 型と登録候補

元の閉零射の前合成と標準Hom鎖写像を全単体で同定し、点ごとのΓ比較を実豊穣Homへ戻した。既存の前後作用の全関手則で合成・交換を確認し、その同じ等式を実際のAsSmall添字・指定BK重みへ引き戻した。native錐を作った入力そのものの両作用の一致であり、別の錐を選び直したものではない。

登録候補：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DoldKanClosedPrecomposition`（79行）。

```lean
theorem standardChainMap_closedPrecomposition (x y z : D)
    (f : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y) :
    Functor.whiskerRight
      (SerrePositivity.EInfinity.ComplexLimits.standardModuleChainMap
        (eHomWhiskerRight (Complex R) f (ForgetEnrichment.of (Complex R) z)))
      (forget (ModuleCat R)) =
    eHomWhiskerRight SSet f (ForgetEnrichment.of (Complex R) z)

theorem doldKanSimplicialHomIso_precomposition (x y z : D)
    (f : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y) :
    eHomWhiskerRight SSet f (ForgetEnrichment.of (Complex R) z) ≫
        (doldKanSimplicialHomIso (R := R) x z).hom =
      (doldKanSimplicialHomIso (R := R) y z).hom ≫
        Functor.whiskerRight
          ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat R) ℕ ⥤ SimplicialObject (ModuleCat R)).map
            (truncLE'Map (eHomWhiskerRight (Complex R) f (ForgetEnrichment.of (Complex R) z))
              (ComplexShape.embeddingUpIntLE 0))) (forget (ModuleCat R))

theorem complexDoldKanHomIso_precomposition {A : Type u} [CommRing A]
    {P Q : Complex A} (f : P ⟶ Q) (T : Complex A) :
    eHomWhiskerRight SSet ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map f)
        (ForgetEnrichment.of (Complex A) T) ≫ (complexDoldKanHomIso A P).hom.app T =
      (complexDoldKanHomIso A Q).hom.app T ≫
        Functor.whiskerRight
          ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ SimplicialObject (ModuleCat A)).map
            (truncLE'Map (homPrecompose f T) (ComplexShape.embeddingUpIntLE 0)))
          (forget (ModuleCat A))

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.EnrichedBKConeNaturality`（111行）。

```lean
def enrichedBKHomDiagram (P : Complex A) (X : CosimplicialObject (Complex A)) :
    SimplexCategoryᵒᵖᵒᵖ ⥤ SSet.{u}

def enrichedBKHomIso (P : Complex A) (X : CosimplicialObject (Complex A)) :
    enrichedBKHomDiagram P X ≅ (pointwiseBKSetHomFunctor A).obj
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X)))

def enrichedBKHomTargetMap (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    enrichedBKHomDiagram P X ⟶ enrichedBKHomDiagram P Y

def enrichedBKHomSourceMap {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    enrichedBKHomDiagram Q X ⟶ enrichedBKHomDiagram P X

theorem enrichedBKHomIso_target_naturality (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    enrichedBKHomTargetMap P f ≫ (enrichedBKHomIso P Y).hom =
      (enrichedBKHomIso P X).hom ≫
        (pointwiseBKSetHomFunctor A).map (normalizedBKConeTargetMap P f)

theorem enrichedBKHomIso_source_naturality {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    enrichedBKHomSourceMap f X ≫ (enrichedBKHomIso P X).hom =
      (enrichedBKHomIso Q X).hom ≫
        (pointwiseBKSetHomFunctor A).map (normalizedBKConeSourceMap f X)

theorem enrichedBousfieldKanCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    enrichedBousfieldKanCone X ≫
        Functor.whiskerRight (enrichedBKHomTargetMap ((productTotalFunctor A).obj X) f)
          SimplicialObject.opFunctor =
      enrichedBousfieldKanCone Y ≫
        Functor.whiskerRight (enrichedBKHomSourceMap ((productTotalFunctor A).map f) Y)
          SimplicialObject.opFunctor

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.EnrichedBKHomComposition`（58行）。

```lean
theorem enrichedBKHomTargetMap_id (P : Complex A) (X : CosimplicialObject (Complex A)) :
    enrichedBKHomTargetMap P (𝟙 X) = 𝟙 (enrichedBKHomDiagram P X)

theorem enrichedBKHomTargetMap_comp (P : Complex A)
    {X Y Z : CosimplicialObject (Complex A)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    enrichedBKHomTargetMap P (f ≫ g) =
      enrichedBKHomTargetMap P f ≫ enrichedBKHomTargetMap P g

theorem enrichedBKHomSourceMap_id (P : Complex A) (X : CosimplicialObject (Complex A)) :
    enrichedBKHomSourceMap (𝟙 P) X = 𝟙 (enrichedBKHomDiagram P X)

theorem enrichedBKHomSourceMap_comp {P Q T : Complex A} (f : P ⟶ Q) (g : Q ⟶ T)
    (X : CosimplicialObject (Complex A)) :
    enrichedBKHomSourceMap (f ≫ g) X =
      enrichedBKHomSourceMap g X ≫ enrichedBKHomSourceMap f X

theorem enrichedBKHomSourceMap_targetMap {P Q : Complex A} (f : P ⟶ Q)
    {X Y : CosimplicialObject (Complex A)} (g : X ⟶ Y) :
    enrichedBKHomSourceMap f X ≫ enrichedBKHomTargetMap P g =
      enrichedBKHomTargetMap Q g ≫ enrichedBKHomSourceMap f Y

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.LiftedBKConeNaturality`（57行）。

```lean
def liftedEnrichedBKHomDiagram (P : Complex A) (X : CosimplicialObject (Complex A)) :
    AsSmall.{u} SimplexCategory ⥤ SSet.{u}

def liftedEnrichedBKHomTargetMap (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    liftedEnrichedBKHomDiagram P X ⟶ liftedEnrichedBKHomDiagram P Y

def liftedEnrichedBKHomSourceMap {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    liftedEnrichedBKHomDiagram Q X ⟶ liftedEnrichedBKHomDiagram P X

theorem liftedEnrichedBousfieldKanCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    liftedEnrichedBousfieldKanCone X ≫
        liftedEnrichedBKHomTargetMap ((productTotalFunctor A).obj X) f =
      liftedEnrichedBousfieldKanCone Y ≫
        liftedEnrichedBKHomSourceMap ((productTotalFunctor A).map f) Y

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeSmallShape`（37行）。

```lean
def smallNativeTotConeDiagram (X : CosimplicialObject (Complex A)) :
    (SSet.uliftFunctor.{u+1,u}).obj
      (join (Δ[0] : SSet.{u}) (nerve (AsSmall.{u} SimplexCategory))) ⟶ dgNerve A (Complex A)

theorem smallNativeTotConeDiagram_restore (X : CosimplicialObject (Complex A)) :
    (uliftConeShapeIso (nerve (AsSmall.{u} SimplexCategory)) 0).inv ≫
      smallNativeTotConeDiagram X = (nativeDGCone X).val

```

登録候補：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCoherentCoefficientNaturality`（41行）。

```lean
theorem weightedCoherentCoefficient_map (α : H ⟶ H')
    (τ : simplexPrefixWeight n ⟶ σ ⋙ H ⋙ SSet.opFunctor) (j : Fin (n + 1)) :
    weightedCoherentCoefficient
        (τ ≫ Functor.whiskerLeft σ (Functor.whiskerRight α SSet.opFunctor)) j =
      weightedCoherentCoefficient τ j ≫ α.app (σ.obj j)

theorem weightedCoherentCoefficient_dinaturality (α : H ⟶ H'') (β : H' ⟶ H'')
    (τ : simplexPrefixWeight n ⟶ σ ⋙ H ⋙ SSet.opFunctor)
    (τ' : simplexPrefixWeight n ⟶ σ ⋙ H' ⋙ SSet.opFunctor)
    (h : τ ≫ Functor.whiskerLeft σ (Functor.whiskerRight α SSet.opFunctor) =
      τ' ≫ Functor.whiskerLeft σ (Functor.whiskerRight β SSet.opFunctor))
    (j : Fin (n + 1)) :
    weightedCoherentCoefficient τ j ≫ α.app (σ.obj j) =
      weightedCoherentCoefficient τ' j ≫ β.app (σ.obj j)

```

### 155.2 検収

実豊穣Homと指定入力の四本はコード **`3c6f9197d`**。対象ビルド178は標準成分表示の書き換えで失敗し、鍵を返却した。表示を明示して修正した179は **5,944 jobs、終了コード0**、小監査 **3宣言**。180は **6,191 jobs、終了コード0**、新規一本 **17宣言**。181は **6,204 jobs、終了コード0**、新規二本 **12宣言（7・5）**。全て標準三公理のみ。失敗した178を成功に数えない。

同じ錐の小さい形状表示と混合係数の二本はコード **`bbc48fcc0`**。対象ビルド182・183は **6,048・2,246 jobs、終了コード0**、新規分の小監査は **4・2宣言、標準三公理のみ**。ログ `/private/tmp/isw2-build179.log`〜`183.log`。各回 `--class impl --wait 3600`、整理券一枚、対象ビルドと小監査の間だけ鍵を保持し、各ハンドルの終了コード0を確認して返却済み。sorry・新公理0、計算上限・再帰上限、既存宣言、⑤a、入口・公式監査・mainの変更なし。各ファイル200行以内。

累計 **335モジュール・20,575行**、G10の外枠まで **2,425行**。累計一覧 `is-w2-g10-20261114-modules.json`。

### 155.3 mainの既存R6を再利用するD01の短い組み立て

mainの `StrictCoherentFamily A E K C` は、各パラメータでの**元の全dg nerve図式**と、全高次HA成分に厳密に可換する `StrictSimplexMap`、恒等・合成・全面・退化の整合性から、同じ全パラメータ評価を作る。`StrictCoherentFamilyEvaluation.lean` の `.evaluation` は `nerve C ⊗ (uliftFunctor.obj K) ⟶ dgNerve A E`。これは今回必要な全族の組み立ての既存部品として使える。新しいcollageや全族評価を一から作らない。

`K := join (Δ[0] : SSet.{u}) (nerve (AsSmall.{u} SimplexCategory))`、`C := CosimplicialObject (Complex A)`、`E := Complex A` とし、`.obj X` に今回検証した `smallNativeTotConeDiagram X` をそのまま置く。その形状同型を戻せば、元の `nativeDGCone X` の全join射になることも検証済み。

残る接続は次の順。

1. 各図式射fの元の閉零成分（左頂点は `productTotalFunctor.map f`、右頂点は `f.app n`）を、全HA成分に可換する `StrictSimplexMap` にする。同じ立方体の旗の評価とcoherent比較の前後作用への自然性を使う。新規の草稿 `CubeEvaluationChainNaturality`・`CoherentComparisonStrictNaturality` はこの既存構成の法則の分割。
2. mixedなweighted coneのHomでの自然性には、今回検証済みの `liftedEnrichedBousfieldKanCone_dinaturality` と `weightedCoherentCoefficient_dinaturality` を使う。尾部は元の図式射の自然性、逆方向の空Homは空型の消去。高次成分を通常の辺の自然性だけで代用しない。
3. `StrictSimplexMap.ext` で単位・合成を、同じ引き戻しと `.hext` で全面・退化を確認して `StrictCoherentFamily` へ入れる。既存の `.evaluation` を使い、積の順序と同じ形状同型を戻し、同じ出力分解へ後合成してD01の全族にする。
4. 既存 `orderedSimplexFamily_const` による各点の同じ全単体への復元と、前面・頂点への制限を使ってD02・D03を閉じ、§151の同じ頂点関手とD04を接続する。

この経路はD01の指定された構成の証明分割で、範囲・型の変更ではない。新しい一般の厳密化定理や模型圏仮定は足さない。D05〜D08、続くBEのTot・実現と任意coherent BE図式の段0を保持して継続する。


## 156. D01の途中：同じnative錐の全セル識別と全高次HA写像（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。D01の全族の完成はまだ主張しない。以下は既存構成の係数移送・単位・合成・自然性・表示・貼り合わせの法則と証明分割。

### 156.1 型と登録候補

立方体の符号付き旗和が元のHom鎖写像に可換することから、全豊穣Homの可換式を `coherentComparisonStrictMap` の**全高次HA成分の厳密可換式**へ移した。weighted coneの頂点・尾部・混合・空Homを照合し、元の図式射のTot成分と各次数の成分を持つ `nativeTotWeightedSimplexMap` と、その単位・合成則を閉じた。

さらに、元のnative錐のcoslice切断の**任意次数**の評価と、パラメータ第一射影の係数則を使い、局所weighted単体が元の同じ全join射のセル制限そのものであることを `nativeTotCone_cellMap`・`_cellSimplex` で証明した。ここは辺だけの照合でも、FunctorIsoによる別のセルへの取り換えでもない。

登録候補：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CubeEvaluationChainNaturality`（56行）。

```lean
theorem standardTopEval_chainMap (f : homObject R D x y ⟶ homObject R E x' y')
    (m : ℕ) (s : StandardSimplex R x y m) :
    standardTopEval x' y' m ((standardModuleChainMap f).app (Opposite.op ⦋m⦌) s) =
      f.f (-(m : ℤ)) (standardTopEval x y m s)

theorem cubeFlagEvaluation_chainMap {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    (f : homObject R D x y ⟶ homObject R E x' y')
    (φ : SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶
      standardHomSpace (R := R) x y) :
    cubeFlagEvaluation e (φ ≫ Functor.whiskerRight (standardModuleChainMap f)
      (forget (ModuleCat R))) = f.f (-(m : ℤ)) (cubeFlagEvaluation e φ)

theorem cubeEvaluation_chainMap {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    (f : homObject R D x y ⟶ homObject R E x' y')
    (φ : SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶
      standardHomSpace (R := R) x y) :
    cubeEvaluation e (φ ≫ Functor.whiskerRight (standardModuleChainMap f)
      (forget (ModuleCat R))) = f.f (-(m : ℤ)) (cubeEvaluation e φ)

```

登録候補：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoherentComparisonStrictNaturality`（70行）。

```lean
theorem cubeEvaluation_closed_naturality {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    {x y x' y' : D}
    (f : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) x')
    (g : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) y')
    (φ : SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶
      standardHomSpace (R := R) x y)
    (ψ : SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶
      standardHomSpace (R := R) x' y')
    (h : φ ≫ eHomWhiskerLeft SSet (ForgetEnrichment.of (Complex R) x) g =
      ψ ≫ eHomWhiskerRight SSet f (ForgetEnrichment.of (Complex R) y')) :
    compose R (closedHomEquiv R D _ _ g).val (cubeEvaluation e φ) (add_zero (-(m : ℤ))) =
      compose R (cubeEvaluation e ψ) (closedHomEquiv R D _ _ f).val
        (zero_add (-(m : ℤ)))

def coherentComparisonStrictMap {n : ℕ}
    (s t : (doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (f : ∀ i, s.obj i ⟶ t.obj i)
    (hf : ∀ i j, s.map i j ≫ eHomWhiskerLeft SSet (s.obj i) (f j) =
      t.map i j ≫ eHomWhiskerRight SSet (f i) (t.obj j)) :
    StrictSimplexMap R D (coherentSimplexData s) (coherentSimplexData t) where
  app i := closedHomEquiv R D _ _ (f (.mk (ULift.up i)))
  naturality I a b k hI ha hb hk

```

登録候補：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightedConeComparisonStrictMap`（39行）。

```lean
def weightedConeComparisonStrictMap {n : ℕ} {σ : ComposableArrows I n}
    (η : F ⟶ G) {x y : ClosedCategory R D} (f : x ⟶ y)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F x ⋙ SSet.opFunctor)
    (τ' : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram G y ⋙ SSet.opFunctor)
    (h : τ ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight (weightedConeHomTargetMap η x) SSet.opFunctor) =
      τ' ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight (weightedConeHomSourceMap f G) SSet.opFunctor)) :
    StrictSimplexMap R D (coherentSimplexData (weightedConeSimplex F x τ))
      (coherentSimplexData (weightedConeSimplex G y τ'))

```

登録候補：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.UliftPointSimplexEvaluation`（47行）。

```lean
theorem uliftPointSimplexEvaluation (K E Q : SSet.{u})
    (p : (Δ[0] : SSet.{u}) ⟶ E) (f : K ⊗ E ⟶ Q)
    {n : ℕ} (σ : K _⦋n⦌) (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    let U := SSet.uliftFunctor.{v,u}
    let e := (uliftStdSimplexIso.{u,v} 0).inv ≫ U.map p
    let s := inv (fst (U.obj K) (Δ[0] : SSet.{max u v})) ≫
      (U.obj K ◁ e) ≫ (uliftTensorIso K E).inv ≫ U.map f
    s.app (Opposite.op ⦋n⦌) (ULift.up σ) =
      ULift.up (f.app (Opposite.op ⦋n⦌)
        (σ, p.app (Opposite.op ⦋n⦌) a₀))

```

登録候補：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ClosedVertexWhiskering`（56行）。

```lean
theorem closedVertex_whiskerLeft {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    eHomEquiv SSet f ≫ eHomWhiskerLeft SSet x g = eHomEquiv SSet (f ≫ g)

theorem closedVertex_whiskerRight {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    eHomEquiv SSet g ≫ eHomWhiskerRight SSet f z = eHomEquiv SSet (f ≫ g)

theorem enrichedUnit_whiskering {x y : C} (f : x ⟶ y) :
    eId SSet x ≫ eHomWhiskerLeft SSet x f =
      eId SSet y ≫ eHomWhiskerRight SSet f y

```

登録候補：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeHomNaturality`（97行）。

```lean
theorem weightedConeTailHom_naturality {n : ℕ} {F G : Fin (n + 1) ⥤ C}
    (η : F ⟶ G) (i j : Fin (n + 1)) :
    weightedConeTailHom F i j ≫ eHomWhiskerLeft SSet (F.obj i) (η.app j) =
      weightedConeTailHom G i j ≫ eHomWhiskerRight SSet (η.app i) (G.obj j)

def weightedConeHomTargetMap (η : F ⟶ G) (x : C) :
    simplicialHomDiagram F x ⟶ simplicialHomDiagram G x

def weightedConeHomSourceMap {x y : C} (f : x ⟶ y) (G : I ⥤ C) :
    simplicialHomDiagram G y ⟶ simplicialHomDiagram G x

def weightedConeVertexMap {n : ℕ} (η : F ⟶ G) {x y : C} (f : x ⟶ y)
    (σ : ComposableArrows I n) (i : Fin (n + 2)) :
    weightedConeObj x (σ ⋙ F) i ⟶ weightedConeObj y (σ ⋙ G) i

theorem weightedConeHom_naturality {n : ℕ} {σ : ComposableArrows I n}
    (η : F ⟶ G) {x y : C} (f : x ⟶ y)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F x ⋙ SSet.opFunctor)
    (τ' : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram G y ⋙ SSet.opFunctor)
    (h : τ ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight (weightedConeHomTargetMap η x) SSet.opFunctor) =
      τ' ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight (weightedConeHomSourceMap f G) SSet.opFunctor))
    (i j : Fin (n + 2)) :
    weightedConeHom F x τ i j ≫ eHomWhiskerLeft SSet
        (weightedConeObj x (σ ⋙ F) i) (weightedConeVertexMap η f σ j) =
      weightedConeHom G y τ' i j ≫ eHomWhiskerRight SSet
        (weightedConeVertexMap η f σ i) (weightedConeObj y (σ ⋙ G) j)

```

登録候補：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.WeightedNerveCoefficientProjection`（32行）。

```lean
theorem weightedNerveCoefficients_fst (B : SSet.{u}) (φ : bousfieldKanWeight I ⟶ H)
    {n : ℕ} (σ : ComposableArrows I n) (a : (Δ[n] : SSet.{u}) ⟶ B) :
    weightedNerveCoefficients
        (fst (bousfieldKanWeight I) ((Functor.const I).obj B) ≫ φ) σ a =
      prefixOverWeight σ ≫ Functor.whiskerLeft σ φ

```

登録候補：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentConeCellEvaluation`（31行）。

```lean
theorem coherentConeCosliceSection_cell {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (z : X _⦋0⦌) (h : c.vertex = z) {n : ℕ} (σ : K _⦋n⦌) :
    (((coherentConeCosliceSection c ≫ eqToHom (congrArg
      (fun w => sliceUnder (SSet.yonedaEquiv.symm w)) h)).app
        (Opposite.op ⦋n⦌) σ)).val =
      joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm σ) ≫ c.val

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedSimplex`（73行）。

```lean
def liftedClosedDiagramMap {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    liftedClosedDiagram X ⟶ liftedClosedDiagram Y

def nativeTotWeightedPrefix (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    simplexPrefixWeight n ⟶ σ ⋙
      simplicialHomDiagram (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)) ⋙ SSet.opFunctor

def nativeTotWeightedSimplexData (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) : SimplexData A (Complex A) (n+1)

theorem nativeTotWeightedPrefix_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedPrefix X σ ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight
          (weightedConeHomTargetMap (liftedClosedDiagramMap f)
            (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))) SSet.opFunctor) =
      nativeTotWeightedPrefix Y σ ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight
          (weightedConeHomSourceMap ((complexToClosed A).map ((productTotalFunctor A).map f))
            (liftedClosedDiagram Y)) SSet.opFunctor)

def nativeTotWeightedSimplexMap
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    StrictSimplexMap A (Complex A) (nativeTotWeightedSimplexData X σ)
      (nativeTotWeightedSimplexData Y σ)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedSimplexComposition`（66行）。

```lean
theorem nativeTotWeightedSimplexMap_id (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedSimplexMap (𝟙 X) σ = StrictSimplexMap.id (nativeTotWeightedSimplexData X σ)

theorem nativeTotWeightedSimplexMap_comp {X Y Z : CosimplicialObject (Complex A)}
    (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedSimplexMap (f ≫ g) σ =
      (nativeTotWeightedSimplexMap f σ).comp (nativeTotWeightedSimplexMap g σ)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeSectionSimplex`（79行）。

```lean
theorem nativeTotCone_cosliceSection_simplex (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋n⦌)
    (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let φ := liftedEnrichedBousfieldKanCone X
    ((coherentConeCosliceSection (nativeCoherentCone X) ≫ eqToHom (congrArg
      (fun w : (SimplicialNerve (ClosedCategory A (Complex A))) _⦋0⦌ =>
        sliceUnder (SSet.yonedaEquiv.symm w)) (nativeCoherentCone_vertex X))).app
          (Opposite.op ⦋n⦌) (ULift.up σ)) =
    weightedCosliceSimplex F z
      ((weightedNerveSectionFromTransform
        (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ)).app
          (Opposite.op ⦋n⦌) (σ, a₀))

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellIdentification`（79行）。

```lean
theorem nativeTotCone_cosliceCell (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋n⦌)
    (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    (((coherentConeCosliceSection (nativeCoherentCone X) ≫ eqToHom (congrArg
      (fun w : (SimplicialNerve (ClosedCategory A (Complex A))) _⦋0⦌ =>
        sliceUnder (SSet.yonedaEquiv.symm w)) (nativeCoherentCone_vertex X))).app
          (Opposite.op ⦋n⦌) (ULift.up σ))).val =
      (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
        (weightedConeSimplex (liftedClosedDiagram X)
          (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
          (nativeTotWeightedPrefix X σ))

theorem nativeTotCone_cellMap (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋n⦌)
    (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ)) ≫
        (nativeCoherentCone X).val =
      (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
        (weightedConeSimplex (liftedClosedDiagram X)
          (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
          (nativeTotWeightedPrefix X σ))

theorem nativeTotCone_cellSimplex (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋n⦌)
    (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
      joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ)) ≫
        (nativeCoherentCone X).val) =
      weightedConeSimplex (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (nativeTotWeightedPrefix X σ)

```

### 156.2 検収・実測

立方体・全coherent比較の二本は **`22125d8a0`**。鍵付き対象ビルド184は **3,790 jobs・終了コード0**、新規一本3宣言の小監査。185は **5,949 jobs・終了コード0**、新規一本5宣言の小監査。184ではmainの既存 `StrictSimplexMap` も必要な依存として対象だけ生成したが、新規監査の数には含めていない。

weighted coneから元の全セルまでの十本は **`e9bdb2d07`**。対象ビルド186・187・188・189はそれぞれ **5,953・6,213・6,273・6,275 jobs、終了コード0**。各新規分の小監査は **10（3・5・2）・15・4（2・1・1）・5（1・1・3）宣言**。全て標準三公理のみ。これらは今回の新規対象だけの分割監査であり、全累計の再監査ではない。ログ `/private/tmp/isw2-build184.log`〜`189.log`。

各回 `--class impl --wait 3600`、整理券一枚、対象ビルドと小監査の間だけ鍵を保持し、各ハンドルの終了コード0を確認して返却済み。sorry・新公理0、計算上限・再帰上限の増加、既存宣言、⑤a、入口・公式監査・mainの変更なし。200行超のファイルなし。

累計 **347モジュール・21,300行**、外枠23,000行まで **1,700行**。累計一覧 `is-w2-g10-20261114-modules.json`。

### 156.3 そのまま継続する接続

D01の残りは、これら同じセルの写像を全面・退化と整合する**全錐形状**での `StrictCoherentFamily` へまとめ、既存 `.evaluation` を同じ形状同型で戻して元の出力分解へ後合成する所。`nativeTotCone_cellSimplex` は頂点を保持する全cosliceセルの識別を与えたが、これだけで任意のjoin単体上の全面・退化の整合性が済んだとは数えない。純粋な左頂点・右面と、重複した左頂点を持つ混合単体も既存の引き戻しとして照合する。新しい全族評価の構成は作り直さない。

その後、元の両境界・各Xでの同じ全join射（D02・D03）、保存済みの頂点辺の式（D04）、離散の整数零延長した交代余面複体への頂点移送・全族・ホモロジー入口（D05〜D08）を閉じる。3b-4の承認済みTot先行の範囲と、さらに実現・任意coherent BE図式の段0までの目標は保持している。今回は中間停止・承認待ち・目標の縮小ではなく、検証済みの保存点。


## 157. D01の全join族と元の同じ指定錐への全単体での復元（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。以下はD01〜D03の証明の分割と、既存構成の単位・自然性・貼り合わせ・表示の法則。最終D型の導来入口と両境界は引き続き接続中で、IDを先に完了として数えない。

§156の全join形状での構成は、mainの既存R6をさらに短く使い、各セルの `StrictSimplexCategory` 関手評価を既存cosliceの切断に入れて `sliceUnderUncurry` で貼り合わせる形にした。新しい評価原理・厳密化定理を作らず、純粋な左右面と重複した初点を含む全join単体は同じcosliceの既存普遍性で扱う。固定Xで元の `nativeDGCone X` の全射に厳密に戻る等式も示した。頂点や脚だけの照合ではない。

### 157.1 追加した法則・証明分割の型

共通：`A : Type u`、`[CommRing A]`。各型の名前空間・importは同名ソースのとおり。

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellFamily`（72行）。

```lean
def nativeTotWeightedCellFunctor {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    CosimplicialObject (Complex A) ⥤ StrictSimplexCategory A (Complex A) (n+1)

def nativeTotWeightedCellFamily {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nerve (CosimplicialObject (Complex A)) ⊗
      join (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1}) ⟶ dgNerve A (Complex A)

theorem nativeTotWeightedCellFamily_at {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) (X : CosimplicialObject (Complex A)) :
    lift (SSet.const (ComposableArrows.mk₀ X))
        (𝟙 (join (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1}))) ≫
      nativeTotWeightedCellFamily A σ =
    (leftPointStdSimplexIso n).hom ≫
      SSet.yonedaEquiv.symm (nativeTotWeightedCellFunctor A σ |>.obj X |>.val)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedReindex`（78行）。

```lean
theorem nativeTotWeightedPrefix_reindex (X : CosimplicialObject (Complex A))
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedPrefix X ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) =
      simplexPrefixWeightRestriction α ≫
        Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor
          (nativeTotWeightedPrefix X σ)

theorem nativeTotWeightedSimplex_reindex (X : CosimplicialObject (Complex A))
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    coherentSimplex (weightedConeSimplex (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (nativeTotWeightedPrefix X ((SimplexCategory.toCat.map α).toFunctor ⋙ σ))) =
    (coherentSimplex (weightedConeSimplex (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (nativeTotWeightedPrefix X σ))).pullback (prependOrderHom α.toOrderHom)

theorem nativeTotWeightedSimplexMap_reindex
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y)
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    HEq (nativeTotWeightedSimplexMap f ((SimplexCategory.toCat.map α).toFunctor ⋙ σ))
      ((nativeTotWeightedSimplexMap f σ).pullback (prependOrderHom α.toOrderHom))

theorem nativeTotWeightedCellFunctor_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedCellFunctor A ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) =
      nativeTotWeightedCellFunctor A σ ⋙
        strictSimplexPullbackFunctor A (Complex A) (prependOrderHom α.toOrderHom)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedApexFamily`（90行）。

```lean
def nativeTotClosedVertexFunctor :
    ClosedCategory A (Complex A) ⥤ StrictSimplexCategory A (Complex A) 0

theorem nativeTotWeightedCellFunctor_apex {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedCellFunctor A σ ⋙ strictSimplexPullbackFunctor A (Complex A)
        (SimplexCategory.const ⦋0⦌ ⦋n+1⦌ 0).toOrderHom =
      productTotalFunctor A ⋙ complexToClosed A ⋙ nativeTotClosedVertexFunctor A

def nativeTotApexFamily :
    nerve (CosimplicialObject (Complex A)) ⊗ (Δ[0] : SSet.{u+1}) ⟶
      dgNerve A (Complex A)

theorem nativeTotWeightedCellFamily_apex {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInl (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1})) ≫
        nativeTotWeightedCellFamily A σ = nativeTotApexFamily A

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellNaturality`（41行）。

```lean
theorem nativeTotWeightedCellFamily_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedCellFamily A ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) =
      (nerve (CosimplicialObject (Complex A)) ◁
        joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.stdSimplex.map α)) ≫
          nativeTotWeightedCellFamily A σ

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotFunctorCosliceFamily`（81行）。

```lean
def nativeTotFunctorCosliceSimplex {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    (sliceUnder (curry (nativeTotApexFamily A))) _⦋n⦌

def nativeTotFunctorCosliceSection :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶
      sliceUnder (curry (nativeTotApexFamily A))

def nativeTotJoinFamily :
    nerve (CosimplicialObject (Complex A)) ⊗
      join (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ⟶
          dgNerve A (Complex A)

theorem nativeTotJoinFamily_apex :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInl (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))) ≫
      nativeTotJoinFamily A = nativeTotApexFamily A

theorem nativeTotJoinFamily_cell {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinMap (𝟙 (Δ[0] : SSet.{u+1}))
        (SSet.yonedaEquiv.symm (ULift.up σ))) ≫ nativeTotJoinFamily A =
      nativeTotWeightedCellFamily A σ

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotJoinEvaluation`（92行）。

```lean
theorem nativeTotJoin_cell_ext {K L T : SSet.{u+1}} {f g : join K L ⟶ T}
    (hleft : joinInl K L ≫ f = joinInl K L ≫ g)
    (hc : ∀ (n : ℕ) (σ : L _⦋n⦌),
      joinMap (𝟙 K) (SSet.yonedaEquiv.symm σ) ≫ f =
        joinMap (𝟙 K) (SSet.yonedaEquiv.symm σ) ≫ g) : f = g

theorem nativeTotJoinFamily_at_cell (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ) : (Δ[n] : SSet.{u+1}) ⟶
      (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ≫
      (lift (SSet.const (ComposableArrows.mk₀ X))
        (𝟙 (join (Δ[0] : SSet.{u+1})
          ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))))) ≫
        nativeTotJoinFamily A) =
      joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ) : (Δ[n] : SSet.{u+1}) ⟶
      (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ≫
        (nativeDGCone X).val

theorem nativeTotJoinFamily_at (X : CosimplicialObject (Complex A)) :
    lift (SSet.const (ComposableArrows.mk₀ X))
        (𝟙 (join (Δ[0] : SSet.{u+1})
          ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))))) ≫
      nativeTotJoinFamily A = (nativeDGCone X).val

```

### 157.2 検収・残り

コード `3d090bc59`（二本150行）、`dd4962dd1`（三本212行）、`7e7941572`（一本92行）。対象ビルド191〜195はそれぞれ **6,531・6,532・6,534・6,535・6,536 jobs、終了コード0**。新規分だけの一時監査は **13・4・8（1・7）・9・3宣言**、すべて標準三公理のみ。190の結合則の書き換え失敗は、等式を単体ごとの表示で示してから合成する証明へ直し191で再検証済み。検証中の失敗を成功の数には含めていない。

鍵は各回 `--class impl --wait 3600`、整理券一枚、ビルド・小監査中だけ。全ハンドルの終了コード0を確認して返却済み。大きい累計監査・rootは実行していない。sorry・新公理0、計算・再帰上限の増加、既存宣言・⑤a・入口・公式監査・mainの変更なし。今回200行超のファイルなし。

検証済み累計 **353モジュール・21,754行**、外枠23,000行まで **1,246行**。累計JSONを今回の六本で更新。

次は同じ族を元の添字同型と既存の半自由出力分解へ後合成し、D01の型、D03の指定点制限、D02の両境界を閉じる。D04は既検証の同じ頂点辺の式へ接続する。D05〜D08、BEのTot先行・実現・任意coherent図式の紙の整理まで目標を保持して継続する。


## 158. D01・D03・D04完了、D02の両境界の照合（2026-11-14）

一覧：済み 31／全体 36（うち追加 1）。D01の全導来錐族、D03の元の同じ全指定錐への点制限、D04の図式射の像が対象ビルド・監査まで完了。D02は左境界と右境界の同じセルの照合までで、両境界の最終結論は未完。D05〜D08とBEの範囲を保持する。

D03は§151のとおり、標準零単体の第一射影の逆 `inv (fst J Δ[0])` を使う。紙の `ρ_.inv` はモノイダル単位PUnitの型なので、標準零単体との同型を含むこの表示にした。同様にD02左境界の紙の `λ_.hom` は標準零単体を左因子に持つ第二射影 `snd Δ[0] B` に固定。元の点・全パラメータ・全高次単体・既存の型は変えていない。

### 158.1 型と登録候補

共通：`A : Type u`、`[CommRing A]`。閉零頂点の二法則はmainの既存R6の計算を複体の場合へ同じ式で特殊化したもの。その他も既存構成の単位・合成・自然性・係数移送・貼り合わせの法則と一覧の証明分割。

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotConeFamily`（102行）。

```lean
def derivedTotConeFamily :
    join (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗
        nerve (CosimplicialObject (Complex A)) ⟶ derivedInfinityCategory A

theorem derivedTotConeFamily_at_lift (X : CosimplicialObject (Complex A)) :
    lift (𝟙 (join (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))))
      (SSet.const (ComposableArrows.mk₀ X)) ≫ derivedTotConeFamily A =
        (strictDerivedTotCone X).val

theorem derivedTotConeFamily_at (X : CosimplicialObject (Complex A)) :
    inv (fst (join (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))) (Δ[0] : SSet.{u+1})) ≫
      (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex X)) ≫
        derivedTotConeFamily A = (strictDerivedTotCone X).val

theorem derivedTotConeFamily_map {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (derivedTotVertexFamily A).app (Opposite.op ⦋1⦌) (nerve.edgeMk f).edge =
      (complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk ((productTotalFunctor A).map f)).edge

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotClosedVertexEvaluation`（94行）。

```lean
lemma nativeTotClosedVertex_pullback_hom (M : ClosedCategory A (Complex A)) {n : ℕ}
    (α : Fin (n + 1) →o Fin 1) (T : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hT : 2 ≤ T.card)
    (ha : a = T.min' (Index.nonempty hT)) (hb : b = T.max' (Index.nonempty hT))
    (hk : k = 2 - (T.card : ℤ)) :
    ((closedNerveSimplex (A := A) (D := Complex A)
      ((Functor.const (Fin 1)).obj M)).pullback α).hom T a b k hT ha hb hk =
        closedNerveHom (𝟙 M) k

lemma nativeTotClosedVertexEvaluation (G : C ⥤ ClosedCategory A (Complex A)) :
    lift (𝟙 (nerve C)) (SSet.stdSimplex.isTerminalObj₀.from (nerve C)) ≫
      strictSimplexFunctorEvaluation A (Complex A)
        (G ⋙ nativeTotClosedVertexFunctor A) =
      nerveMap G ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)

theorem nativeTotClosedVertexEvaluation_full (G : C ⥤ ClosedCategory A (Complex A)) :
    strictSimplexFunctorEvaluation A (Complex A) (G ⋙ nativeTotClosedVertexFunctor A) =
      fst (nerve C) (Δ[0] : SSet.{u+1}) ≫ nerveMap G ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotConeLeftBoundary`（77行）。

```lean
theorem nativeTotApexFamily_derived :
    nativeTotApexFamily A ≫ complexSemifreeResolutionInfinity A =
      fst (nerve (CosimplicialObject (Complex A))) (Δ[0] : SSet.{u+1}) ≫
        derivedTotVertexFamily A

theorem derivedTotConeFamily_left :
    (joinInl (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
      𝟙 (nerve (CosimplicialObject (Complex A)))) ≫ derivedTotConeFamily A =
      snd (Δ[0] : SSet.{u+1}) (nerve (CosimplicialObject (Complex A))) ≫
        derivedTotVertexFamily A

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedTailFamily`（99行）。

```lean
def nativeTotTailCellFunctor {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    CosimplicialObject (Complex A) ⥤ StrictSimplexCategory A (Complex A) n

theorem nativeTotWeightedCell_tail (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    ((nativeTotWeightedCellFunctor A σ).obj X).val.pullback
        (SimplexCategory.δ (0 : Fin (n+2))).toOrderHom = ((nativeTotTailCellFunctor A σ).obj X).val

theorem nativeTotWeightedCellFunctor_tail {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedCellFunctor A σ ⋙
        strictSimplexPullbackFunctor A (Complex A) (SimplexCategory.δ (0 : Fin (n+2))).toOrderHom =
      nativeTotTailCellFunctor A σ

theorem nativeTotWeightedCellFamily_tail {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInr (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1})) ≫
        nativeTotWeightedCellFamily A σ =
      strictSimplexFunctorEvaluation A (Complex A) (nativeTotTailCellFunctor A σ)

```

### 158.2 検収と実測

D01・D03・D04は **`2d6662535`**、左境界は **`9ad43eac1`**、右境界セルは **`13c3e3040`**。鍵付き対象ビルド196・197・198はそれぞれ **8,123・8,125・6,535 jobs、終了コード0**。各新規分だけの小監査は **5・5（3・2）・7宣言**、標準三公理のみ。ログ `/private/tmp/isw2-build196.log`〜`198.log`。各ハンドル終了コード0を確認、整理券一枚、`--class impl --wait 3600`、ビルド・小監査中だけ鍵を保持し返却済み。全体の新しい累計監査ではない。

sorry・新公理0、計算・再帰上限を増やさず、既存宣言・⑤a・入口・公式監査・mainは変更していない。今回も200行超のファイルなし。

検証済み累計 **357モジュール・22,126行**、外枠23,000行まで **874行**。登録候補JSONも同じ四本を追加。

次はD02右境界の対角評価を元の評価関手の全nerveと同定する。現在の `NativeTotTailCellEvaluation` は未検証草稿であり、累計に含めない。続いて両境界、離散の頂点輸送と全族・ホモロジー入口へ進む。


## 159. D02完了と、離散の全頂点輸送への短い経路（2026-11-14）

一覧：済み 32／全体 36（うち追加 1）。D01〜D04が全て対象ビルド・小監査まで完了。D05〜D08はまだ完了と数えない。

右境界の全セルを既存の底の面の法則で読み、閉零射の全射列の対角を元の評価関手のnerveと等置した。零次は閉零合成と `complexToClosed.map_comp`、高次は既存の零成分で示す。既定200,000 heartbeatsで巨大な表示の `change` が詰まった点は、`orderedSimplexFamily` の表示と零次の合成を分割して解消。計算上限は増やしていない。

### 159.1 型と登録候補

共通：`A : Type u`、`[CommRing A]`。既存構成の単位・合成・自然性・係数移送・表示・貼り合わせ則と、一覧の証明分割。

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotTailCellEvaluation`（85行）。

```lean
def nativeTotClosedEvaluationNerve :
    nerve (CosimplicialObject (Complex A)) ⊗
      ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ⟶
        nerve (ClosedCategory A (Complex A))

theorem nativeTotTailCellEvaluation_diagonal {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n)
    (d : ComposableArrows (CosimplicialObject (Complex A)) n) :
    (strictSimplexFunctorEvaluation A (Complex A) (nativeTotTailCellFunctor A σ)).app
      (Opposite.op ⦋n⦌) (d, ULift.up (𝟙 ⦋n⦌)) =
    closedNerveSimplex (((σ ⋙ AsSmall.down).prod' d) ⋙
      evaluationUncurried SimplexCategory (Complex A) ⋙ complexToClosed A)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotJoinRightBoundary`（55行）。

```lean
theorem nativeTotJoinFamily_right :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInr (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))) ≫
      nativeTotJoinFamily A = nativeTotClosedEvaluationNerve A ≫
        closedNerveInclusion A (Complex A)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotConeRightBoundary`（73行）。

```lean
theorem derivedTotConeFamily_right :
    (joinInr (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
      𝟙 (nerve (CosimplicialObject (Complex A)))) ≫ derivedTotConeFamily A =
        derivedTotEvaluationFamily A

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotConeFamilyBoundaries`（45行）。

```lean
theorem derivedTotConeFamily_boundaries :
    (joinInl (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
      𝟙 (nerve (CosimplicialObject (Complex A)))) ≫ derivedTotConeFamily A =
      snd (Δ[0] : SSet.{u+1}) (nerve (CosimplicialObject (Complex A))) ≫
        derivedTotVertexFamily A ∧
    (joinInr (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
      𝟙 (nerve (CosimplicialObject (Complex A)))) ≫ derivedTotConeFamily A =
        derivedTotEvaluationFamily A

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteTotFunctorCone`（106行）。

```lean
def rawDiscreteTotFunctorDiagram :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶
      (ihom (nerve (CosimplicialObject (ModuleCat.{u} A)))).obj (derivedInfinityCategory A)

def rawDiscreteTotFunctorCone : JoinCone (rawDiscreteTotFunctorDiagram A)

theorem rawDiscreteTotFunctorCone_at (M : CosimplicialObject (ModuleCat.{u} A)) :
    (rawDiscreteTotFunctorCone A).val ≫ evaluateFunctorAt (ComposableArrows.mk₀ M) =
      (rawCosimplicialModuleCone A M).val

theorem rawDiscreteTotFunctorCone_isLimit : IsLimitCone (rawDiscreteTotFunctorCone A)

```

### 159.2 検収・実測

D02の四本は **`d2387aae7`**（258行）。鍵付き対象ビルド199は **8,130 jobs、終了コード0**、新規四本だけの小監査 **7（4・1・1・1）宣言、標準三公理のみ**。raw離散関手圏錐は **`61525eb4c`**（106行）。対象ビルド200は **8,136 jobs、終了コード0**、新規一本の小監査 **8宣言、標準三公理のみ**。ログ `/private/tmp/isw2-build199.log`・`200.log`、全ハンドル終了コード0を確認、鍵返却済み。整理券一枚、`--class impl --wait 3600`、対象ビルド・小監査中だけ鍵を保持。sorry・新公理0、既存宣言・⑤a・入口・公式監査・mainの変更なし。200行超のファイルなし。

検証済み累計 **362モジュール・22,490行**、外枠23,000行まで **510行**。累計JSONを同じ五本で更新。

### 159.3 残る離散四項の短い経路

独立に選んだMごとの錐を後から自然にする方法は使わず、今回のraw全族を一つの関手圏の極限錐へcurryした。各Mで元のraw錐の全join射に戻る式と、既存 `isLimitCone_of_pointwise` による極限性が検証済み。

その一つの錐に、既存 `complexOrdinaryDerivedNatTransIso` を `discreteTotalCochainNatIso.inv` に適用した全関手同型と、既存 `exists_limitCone_vertex_of_invertible` を使い、頂点を `functorVertex (nerveMap discreteCochainFunctor ≫ complexOrdinaryDerivedSource)` に厳密に固定する。これにより同じ頂点の全族とその評価錐を同時に選べる。関手圏の点ごとの極限の逆向きは既存 `isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits` を再利用し、評価した錐の極限性・頂点・全族の両境界・ホモロジー入口へ戻す。一般の頂点輸送・新しい厳密化・新しい模型圏構造を作らない。

このための `DiscreteTotApexTransport` は92行の未検証草稿で累計外。mainの既存 `DerivedNatTransIso`・`LimitConeVertexTransport` の二本が冷たい依存なので、対象だけをビルド201で生成してから照合する。この段階ではD05〜D08の最終結果を主張しない。外枠の残りを追跡し、上限を超える工程が必要になったら検証済みを保存して報告する。


## 160. 停止点2b：G10の完成（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。A01〜A12・A05a、B01〜B08、C01〜C07、D01〜D08が全て完了。停止点2aに加え、全図式射・全高次単体を持つ同じ指定Tot錐の全族、両境界、各図式での同じ全join射への厳密復元、離散入力の交代余面複体への頂点輸送と全族、整数次数への零延長を明記したホモロジー入口まで閉じた。

取り込み用コードの最終点は **`39d5ccd32`**（D05・D06と頂点輸送 **`5e2448beb`**、D01・D03・D04 **`2d6662535`**、D02 **`d2387aae7`** を含む）。停止点2a後に登録する新規40本を `is-w2-stop2b-20261114-modules.json` に分けた。全G10累計は `is-w2-g10-20261114-modules.json`。入口・公式監査・mainへの取り込みは調整役に任せ、こちらでは変更していない。

### 160.1 最後の四本の型

共通：`A : Type u`、`[CommRing A]`。D08は既存 `HasDerivedCategory.standard` をlocal instanceとして使い、追加の仮定にしていない。一般のSSetの模型圏仮定なし。全て既存構成の自然性・単位・合成・係数移送・貼り合わせの法則と、承認済み一覧の証明分割。

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteTotApexTransport`（93行）。

```lean
theorem discreteTotFunctorVertex_curry_fst {B D : SSet.{u+1}} (F : B ⟶ D) :
    SSet.yonedaEquiv (curry (fst B (Δ[0] : SSet.{u+1}) ≫ F)) = functorVertex F

theorem rawDiscreteTotFunctorCone_vertex :
    (rawDiscreteTotFunctorCone A).vertex =
      functorVertex (nerveMap (discreteTotalFunctor A) ≫ complexOrdinaryDerivedSource A)

def discreteTotCochainDerivedIso :
    FunctorIso (nerveMap (discreteCochainFunctor A) ≫ complexOrdinaryDerivedSource A)
      (nerveMap (discreteTotalFunctor A) ≫ complexOrdinaryDerivedSource A)

theorem exists_discreteCochainFunctorCone :
    ∃ c : JoinCone (rawDiscreteTotFunctorDiagram A), IsLimitCone c ∧
      c.vertex = functorVertex (nerveMap (discreteCochainFunctor A) ≫
        complexOrdinaryDerivedSource A)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.CosimplicialModuleCone`（96行）。

```lean
def discreteCochainFunctorCone : JoinCone (rawDiscreteTotFunctorDiagram A)

theorem discreteCochainFunctorCone_isLimit : IsLimitCone (discreteCochainFunctorCone A)

theorem discreteCochainFunctorCone_vertex :
    (discreteCochainFunctorCone A).vertex =
      functorVertex (nerveMap (discreteCochainFunctor A) ≫ complexOrdinaryDerivedSource A)

theorem rawDiscreteTotFunctorDiagram_at (M : CosimplicialObject (ModuleCat.{u} A)) :
    evaluateFunctorDiagram (rawDiscreteTotFunctorDiagram A) (ComposableArrows.mk₀ M) =
      strictCosimplicialModuleNerve A M ≫ discreteModuleSource A

theorem discreteCochainFunctorCone_isPointwise :
    IsPointwiseLimitCone (discreteCochainFunctorCone A)

def cosimplicialModuleCone (M : CosimplicialObject (ModuleCat.{u} A)) :
    JoinCone (strictCosimplicialModuleNerve A M ≫ discreteModuleSource A)

theorem cosimplicialModuleCone_isLimit (M : CosimplicialObject (ModuleCat.{u} A)) :
    IsLimitCone (cosimplicialModuleCone A M)

theorem cosimplicialModuleCone_vertex (M : CosimplicialObject (ModuleCat.{u} A)) :
    (cosimplicialModuleCone A M).vertex =
      (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((discreteCochainFunctor A).obj M))

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.CosimplicialModuleConeFamily`（146行）。

```lean
theorem moduleConeCurry_evaluateAt {K D : SSet.{u+1}}
    (H : nerve (CosimplicialObject (ModuleCat.{u} A)) ⊗ K ⟶ D)
    (M : CosimplicialObject (ModuleCat.{u} A)) :
    curry H ≫ evaluateFunctorAt (ComposableArrows.mk₀ M) =
      lift (SSet.const (ComposableArrows.mk₀ M) : _ ⟶
      nerve (CosimplicialObject (ModuleCat.{u} A))) (𝟙 K) ≫ H

def cosimplicialModuleConeFamily :
    join (Δ[0] : SSet.{u+1}) ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗
      nerve (CosimplicialObject (ModuleCat.{u} A)) ⟶ derivedInfinityCategory A

def discreteTotEvaluationFamily :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⊗
      nerve (CosimplicialObject (ModuleCat.{u} A)) ⟶ derivedInfinityCategory A

theorem cosimplicialModuleConeFamily_at_lift (M : CosimplicialObject (ModuleCat.{u} A)) :
    lift (𝟙 _) (SSet.const (ComposableArrows.mk₀ M) : _ ⟶
      nerve (CosimplicialObject (ModuleCat.{u} A))) ≫ cosimplicialModuleConeFamily A =
      (cosimplicialModuleCone A M).val

theorem cosimplicialModuleConeFamily_at (M : CosimplicialObject (ModuleCat.{u} A)) :
    inv (fst (join (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))) (Δ[0] : SSet.{u+1})) ≫
      (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex M)) ≫ cosimplicialModuleConeFamily A =
        (cosimplicialModuleCone A M).val

theorem cosimplicialModuleConeFamily_boundaries :
    (joinInl (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ 𝟙 _) ≫
      cosimplicialModuleConeFamily A =
        snd (Δ[0] : SSet.{u+1}) (nerve (CosimplicialObject (ModuleCat.{u} A))) ≫
          nerveMap (discreteCochainFunctor A) ≫ complexOrdinaryDerivedSource A ∧
    (joinInr (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ 𝟙 _) ≫
      cosimplicialModuleConeFamily A = discreteTotEvaluationFamily A

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.CosimplicialModuleConeHomology`（45行）。

```lean
def cosimplicialModuleCone_homology (M : CosimplicialObject (ModuleCat.{u} A)) (i : ℤ) :
    derivedInfinityHomology A i (cosimplicialModuleCone A M).vertex ≃ₗ[A]
      ((discreteCochainFunctor A).obj M).homology i

```

### 160.2 最終検収

- 201は再利用するmainの既存二本の生成のみ：5,714 jobs、終了コード0。新規監査の数には含めない。
- 202：交代余面全頂点への輸送、8,153 jobs、終了コード0、新規一本6宣言・標準三公理のみ。
- 203：D05・D06および既存 `StrictHomology` の生成、10,234 jobs、終了コード0。新規一本だけの小監査10宣言・標準三公理のみ。
- 204：D07・D08、10,236 jobs、終了コード0。**停止点2a後の自レーン新規40モジュールをまとめて小監査し208宣言、標準三公理のみ**。これは全段階IIや全366本の今回の再監査ではない。A・B・Cと前段の依存は各報告の検証済み対象ビルド・監査を引き継ぐ。

ログ `/private/tmp/isw2-build201.log`〜`204.log`、最終監査 `/private/tmp/AuditISW2G10DComplete.lean`。全ハンドルの終了コード0を確認済み、鍵返却済み。各回 `--class impl --wait 3600`、整理券一枚、一回1,700秒、対象ビルド・小監査の間だけ鍵を使用。root・大きい監査は流していない。`git diff --check`成功。sorry・独自公理0、計算・再帰上限の増加なし、既存宣言・⑤a・入口・公式監査・mainの変更なし。今回200行超のファイルなし。未検証のG10草稿を残さない。

最終実測 **366モジュール・22,870行**。外枠23,000行内（残り **130行**）。

### 160.3 §37.2・§72.2の四まとまり：見込みと実測の差

実測は各まとまりを完了した報告の累計間の増分で、共通の前提計算・証明分割・docstring/importを含む。Aは両見積もりの時点で既に途中まであったので、同じ時点からA完了までを比較した。B〜DはそれぞれA・B・C完了時点からの増分。B4の配置・名前空間追従を含む最終ソースの数え直しは上記累計JSON。

| まとまり | §37.2見込み | §72.2見込み | 完了実測と差 |
| --- | ---: | ---: | --- |
| A：正規化テンソル／積重み | 1,000〜1,600 | 400〜700 | §37の5,786→A完了12,781：6,995（+5,395〜+5,995）。§72の8,834→12,781：3,947（+3,247〜+3,547） |
| B：指定豊穣Hom・native極限性 | 600〜900 | 600〜900 | 12,781→18,226：5,445（+4,545〜+4,845） |
| C：標準脚・D(A)輸送 | 400〜700 | 400〜700 | 18,226→19,553：1,327（+627〜+927） |
| D：全図式射・指定全錐族・離散入口 | 500〜900 | 500〜900 | 19,553→22,870：3,317（+2,417〜+2,817） |

主な超過は抽象的な同値から自動では出ない、元のAW/Γ/Moore/豊穣合成の同じ射の照合と、全パラメータの厳密HA写像・元の全joinセルの復元。D後半の離散部分は、既存の関手圏の点ごとの極限判定と全自然同型に沿う頂点輸送を使い、全族を作り直す増分を抑えた。型・範囲を削る短縮はしていない。

### 160.4 そのまま3b-4へ

IS-W2 §18・更新後の/goalに従い、ここで承認待ちにせず、承認済み§152のR01〜R12（外枠15,000行）のTot側から進む。TotのR01〜R05・R11/R12のTot部分が停止点3b-4a、実現のR06〜R10が停止点3b-4b。その後に任意coherent BE図式の段0を報告して止まる。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤aを変えず、無条件の `cAlgForgetDerived_mapJoinCone_isLimit` を使う。点つきKan Totは作らない。3b-4の実測はG10とは別に数える。



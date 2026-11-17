# BS-M15（⑤d）作業報告 — M10 の Hom 比較（約 8,500 行の途中報告まで）（§26〜§42、2026-11-14）

元の報告：[report-codex-m15.md](../../bhatt-scholze/reports/report-codex-m15.md)

## 26. M10/C02：指定半自由模型への全比較の降下と制限の法則（11-14）

§25 の元の通常 DK 源の全標的普遍性に、§18 の同じ通常源から指定半自由模型への関手を
渡した。既存の `localizationDescend` と同じ `localizationDescendIso` により、
全単体の比較関手 K と全関手間の指定三角同型を得る。
標準局所化頂点、正則加群の指定単位、元の U との源上の比較も同じ三角から回収する。

さらに源の全係数自然性、両端の同じ三角、§18 の同じ制限比較を貼り、
実局所化の前合成の充満忠実性で全関手間の同型を降ろす。
全厳密 BE 代数射を対象とし、元の制限が半自由対象を保つという仮定は置かない。
これは既存の M10/C02 の構成の降下・自然性・単位・貼り合わせの法則と証明分割で、
一次 ID は追加しない。

型の文脈は `A : Type u`、`[CommRing A]`。

### RawModuleComparison

```lean
def strictRawModuleComparison (X : (operad A).Algebra) :
    localizationNerve (strictRawModuleRelativeCategory A X) ⟶ strictModuleInfinity A X

def strictRawModuleComparison_sourceIso (X : (operad A).Algebra) :
    FunctorIso
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫
        strictRawModuleComparison A X)
      (strictRawModuleSource A X)

def strictRawModuleComparison_vertexIso (X : (operad A).Algebra)
    (M : (strictRawModuleRelativeCategory A X).category) :
    VertexIso
      ((strictRawModuleComparison A X).app (Opposite.op ⦋0⦌)
        (localizationNerveVertexEquiv (strictRawModuleRelativeCategory A X)
          (show KanLocalizationCategory (strictRawModuleRelativeCategory A X) from M)))
      ((strictRawModuleSource A X).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ M))

lemma strictRawModuleComparison_essentiallySurjective (X : (operad A).Algebra) :
    IsEssentiallySurjective (strictRawModuleComparison A X)

def strictRawModuleComparison_regularIso (X : (operad A).Algebra) :
    VertexIso
      ((strictRawModuleComparison A X).app (Opposite.op ⦋0⦌)
        (localizationNerveVertexEquiv (strictRawModuleRelativeCategory A X)
          (show KanLocalizationCategory (strictRawModuleRelativeCategory A X) from
            (ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleCategory A X)).obj
              (strictRawRegularObject A X).fiber)))
      (strictModuleUnit A X)

def strictRawModuleComparison_sourceUnderlyingIso (X : (operad A).Algebra) :
    FunctorIso
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫
        strictRawModuleComparison A X ≫ strictModuleUnderlying A X)
      (strictRawModuleSource A X ≫ strictModuleUnderlying A X)
```

### RawModuleComparisonRestriction

```lean
def strictRawModuleLocalization_descendIso (X : (operad A).Algebra)
    {Y : SSet.{u+1}} [Quasicategory Y]
    {F G : localizationNerve (strictRawModuleRelativeCategory A X) ⟶ Y}
    (e : FunctorIso
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫ F)
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫ G)) :
    FunctorIso F G

def strictRawModuleComparison_restrictSourceIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A Y) ≫
        localizationNerveMap (strictRawModuleRestrictRelative f) ≫ strictRawModuleComparison A X)
      (localizationNerveSourceMap (strictRawModuleRelativeCategory A Y) ≫
        strictRawModuleComparison A Y ≫ strictModuleRestrict f)

def strictRawModuleComparison_restrictIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso
      (localizationNerveMap (strictRawModuleRestrictRelative f) ≫ strictRawModuleComparison A X)
      (strictRawModuleComparison A Y ≫ strictModuleRestrict f)
```


K の本質的全射性は元の通常源の本質的全射性と同じ三角から従うが、完全忠実性は未完。
K を同値・fiber 同定とまだ呼ばない。一般の native な底の辺・全族の cocartesian 性、
M11 以降と G12 は引き続き残る。
対象ビルドと小さい監査の結果は、この節の末尾に追記する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 26.1 全比較と制限の対象ビルド・小さい監査

`RawModuleComparison`（107 行・6 宣言）と `RawModuleComparisonRestriction`（77 行・3 宣言）の
通常対象ビルドが完了し、終了コード 0。新規 9 宣言の `#print axioms` について、実出力を
宣言名と機械照合して監査も終了コード 0。依存公理は標準の
`propext`・`Classical.choice`・`Quot.sound` の範囲内で、追加公理・sorryAx はない。
共有 impl 鍵、実行上限 280 秒の組で行った。200 行を超える補題はない。

前合成の表記は、通常圏の同名 `pre` ではなく `MonoidalClosed.pre` を選ぶよう明示した。
構成された K・全三角・頂点・単位・台・全厳密制限との比較の型は上記のまま。
K の完全忠実性、一般の native 底の辺・同じ全族の fiber 同定はまだ未完なので、
M10 の完了数は更新しない。

監査まで済んだ累計は、新規 Lean **55 ファイル・5,431 行・277 宣言（private 3 を含む）**。
次は §22.3 の既存共変 Hom の合成を使い、実 frame と元の dg Hom の比較を進める。

**一覧：済み 10／全体 43（うち追加 1）**。


## 27. M10 の Hom 比較の部品：同じ点ごとの cotensor 関手（11-14）

§22.3 の既存部品をさらに確認すると、`Complexes/Cone.homCovariantDG` が
同じ `leftRepresentable` を複体の共変 Hom の実 dg 関手として公開している。
全次数の作用と、同じ閉零射が元の Hom 後合成に一致することも既に証明されている。
これを同じ加群 dg 関手に後合成し、元の加群射は点ごとの `homPostcompose` で送る。
既存の enriched 前後合成の交換を使い、全作用の自然性と通常関手の単位・合成を照合する。

以下は既存の合成・閉零射・評価の法則の分割で、一次 ID は追加しない。
文脈は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`。
閉零圏の箇所ではさらに `[Small.{u} D]`。

`Modules/CotensorPointwise.lean` の型：

```lean
def dgModuleCotensor (K : Complex A) (M : RightModule A D) : RightModule A D

abbrev moduleCotensor (K : Complex A) (M : ModuleCategory A D) : ModuleCategory A D

lemma moduleCotensor_eval (K : Complex A) (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).obj (moduleCotensor A D K M) =
      homComplex A K ((moduleEvaluation A D x).obj M)

lemma moduleCotensorMap_naturality (K : Complex A) {M N : ModuleCategory A D}
    (f : M ⟶ N) (x y : Dᵒᵖ) :
    (dgModuleCotensor A D K (ForgetEnrichment.to (Complex A) M)).map x y ≫
      homPostcompose _ (homPostcompose K ((moduleEvaluation A D y.unop).map f)) =
    (dgModuleCotensor A D K (ForgetEnrichment.to (Complex A) N)).map x y ≫
      homPrecompose (homPostcompose K ((moduleEvaluation A D x.unop).map f)) _

def moduleCotensorMap (K : Complex A) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCotensor A D K M ⟶ moduleCotensor A D K N

lemma moduleCotensorMap_eval (K : Complex A) {M N : ModuleCategory A D}
    (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleCotensorMap A D K f) =
      homPostcompose K ((moduleEvaluation A D x).map f)

def moduleCotensorFunctor (K : Complex A) : ModuleCategory A D ⥤ ModuleCategory A D

lemma moduleCotensorFunctor_evaluation (K : Complex A) (x : D) :
    moduleCotensorFunctor A D K ⋙ moduleEvaluation A D x =
      moduleEvaluation A D x ⋙ (eHomFunctor (Complex A) (Complex A)).obj (op K)
```

この時点で標準単体を入れた全 simplicial frame の Reedy fibrancy や coaugmentation の
弱同値性まで主張するものではない。元の dg Hom とモデル frame Hom の比較、
K の完全忠実性へ向けた部品として対象ビルド・小さい監査を行う。

**一覧：済み 10／全体 43（うち追加 1）**。


### 27.1 対象ビルド・小さい監査と次の接続

`CotensorPointwise:olean` の通常対象ビルドは終了コード 0。
8 宣言の `#print axioms` は、宣言名と実出力を機械照合して監査も終了コード 0。
全て標準の `propext`・`Classical.choice`・`Quot.sound` の範囲内で、追加公理・sorryAx はない。
共有 impl 鍵、実行上限 280 秒の組で行った。

評価の対象と元の dg 関手の対象は定義上同じだが、`rw` の照合では表示を揃える必要が
あったため、自然性の二つの交換式の型を明示した。単位則にも同じ定義上の等式を補った。
全て §27 の型のままであり、対象の射影性や底の平坦性を仮定していない。
新規 1 ファイル **130 行・8 公開宣言**。200 行を超える補題はない。

監査まで済んだ累計は、新規 Lean **56 ファイル・5,561 行・285 宣言（private 3 を含む）**。
この goal ターンで完成したものは、元の通常 DK 源の普遍性、指定半自由模型への全比較と
全厳密制限との比較、同じ Hom の合成による cotensor 関手の法則。
§25・§26.1 と本小節は具体的な検証済みの進捗であり、M10 全体の完了ではない。

続きは、標準単体を係数とするこの cotensor の反変作用・全 simplicial 族を照合し、
選んだ実 right frame と同じ dg Hom の比較へ進む。
比較関手 K の完全忠実性、同じ全族の一般の native 辺と fiber の同定、
M11 以降と G12 の本来の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 28. M10 の同じ cotensor の係数反変性と全 simplicial 族（11-14）

前の goal ターンは §25–§27 の通常 DK 源の普遍性・全比較・cotensor の法則を
対象ビルドと小さい監査まで通した進捗。今回は既存の cochain 合成の結合則を使い、
同じ `homPrecompose` が cotensor の全 dg 作用と可換することを照合した。
係数の前合成は全加群射に自然であり、単位・逆順の合成の法則を満たす。

その反変関手に、既存の `SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A` を代入し、
面・退化・全加群射を持つ同じ simplicial 加群の全族を構成した。
点ごとの値と全作用は元の AW 正規化複体からの内部 Hom の前後合成に一致する。
同じ通常 Hom の後合成で全標的の写像単体集合も束ねる。

いずれも既存の cotensor の係数移送・合成・自然性・評価・貼り合わせの法則と
証明の分割で、一次 ID は追加しない。
文脈は `A : Type u`、`[CommRing A]`。
加群の箇所はさらに `D : Type v`、`[DGCategory A D]`、`[Small.{u} D]`。

### CotensorScalar

```lean
lemma homCovariantDG_precomposition {K L : Complex A} (f : K ⟶ L) (P Q : Complex A) :
    (homCovariantDG A L).map P Q ≫ homPostcompose _ (homPrecompose f Q) =
      (homCovariantDG A K).map P Q ≫ homPrecompose (homPrecompose f P) _

lemma moduleCotensorPre_naturality {K L : Complex A} (f : K ⟶ L)
    (M : ModuleCategory A D) (x y : Dᵒᵖ) :
    (dgModuleCotensor A D L (ForgetEnrichment.to (Complex A) M)).map x y ≫
      homPostcompose _ (homPrecompose f ((ForgetEnrichment.to (Complex A) M).obj y)) =
    (dgModuleCotensor A D K (ForgetEnrichment.to (Complex A) M)).map x y ≫
      homPrecompose (homPrecompose f ((ForgetEnrichment.to (Complex A) M).obj x)) _

def moduleCotensorPreMap {K L : Complex A} (f : K ⟶ L) (M : ModuleCategory A D) :
    moduleCotensor A D L M ⟶ moduleCotensor A D K M

lemma moduleCotensorPreMap_eval {K L : Complex A} (f : K ⟶ L) (M : ModuleCategory A D)
    (x : D) :
    (moduleEvaluation A D x).map (moduleCotensorPreMap A D f M) =
      homPrecompose f ((moduleEvaluation A D x).obj M)

def moduleCotensorPreNat {K L : Complex A} (f : K ⟶ L) :
    moduleCotensorFunctor A D L ⟶ moduleCotensorFunctor A D K

def moduleCotensorScalarFunctor : (Complex A)ᵒᵖ ⥤ (ModuleCategory A D ⥤ ModuleCategory A D)
```

### CotensorSimplices

```lean
def moduleCotensorSimplexFamily :
    SimplexCategoryᵒᵖ ⥤ (ModuleCategory A D ⥤ ModuleCategory A D)

def moduleCotensorSimplicesFunctor :
    ModuleCategory A D ⥤ (SimplexCategoryᵒᵖ ⥤ ModuleCategory A D)

abbrev moduleCotensorSimplices (M : ModuleCategory A D) :
    SimplexCategoryᵒᵖ ⥤ ModuleCategory A D

lemma moduleCotensorSimplices_obj_eval (M : ModuleCategory A D)
    (n : SimplexCategoryᵒᵖ) (x : D) :
    (moduleEvaluation A D x).obj ((moduleCotensorSimplices A D M).obj n) =
      homComplex A (SerrePositivity.EInfinity.AlexanderWhitney.cochains A (SSet.stdSimplex.obj n.unop))
        ((moduleEvaluation A D x).obj M)

lemma moduleCotensorSimplices_map_eval (M : ModuleCategory A D)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : D) :
    (moduleEvaluation A D x).map ((moduleCotensorSimplices A D M).map f) =
      homPrecompose
        (SerrePositivity.EInfinity.AlexanderWhitney.cochainMap A (SSet.stdSimplex.map f.unop))
        ((moduleEvaluation A D x).obj M)

lemma moduleCotensorSimplicesFunctor_map_eval {M N : ModuleCategory A D} (g : M ⟶ N)
    (n : SimplexCategoryᵒᵖ) (x : D) :
    (moduleEvaluation A D x).map (((moduleCotensorSimplicesFunctor A D).map g).app n) =
      homPostcompose
        (SerrePositivity.EInfinity.AlexanderWhitney.cochains A (SSet.stdSimplex.obj n.unop))
        ((moduleEvaluation A D x).map g)

def moduleCotensorMappingSimplices (P M : ModuleCategory A D) : SSet.{u}

def moduleCotensorMappingFunctor (P : ModuleCategory A D) :
    ModuleCategory A D ⥤ SSet.{u}
```


対象ビルドは成功した。小さい依存公理監査と最終実測は本節の末尾に追記する。
この simplicial 族の Reedy fibrancy、同じ coaugmentation の弱同値性、選んだモデル frame
との比較、K の完全忠実性はまだ未完。元の全族と M11 以降・G12 の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。

### §28.1 検証と実測

CotensorScalar と CotensorSimplices の通常の対象ビルドは成功した。
同じ impl 鍵の下で新しい公開宣言 14 本の依存公理を監査し、すべて
propext・Classical.choice・Quot.sound の範囲であることを確認した。
新規 Lean は本節の 2 ファイル 223 行を加え、累計 58 ファイル・5,784 行・
明示宣言 299 本（private 3 本）。200 行を超える証明はない。
Reedy fibrancy と単位 cotensor の同定、K の完全忠実性は引き続き未完。

**一覧：済み 10／全体 43（うち追加 1）**。


## 29. M10 の同じ全単体 cotensor の余単位比較（11-14）

既存の `cochainCounitStdSimplexHomotopyEquiv` は、AW 余単位そのものを順射とする
全次元の実鎖ホモトピー同値を保持している。これを既存の
`homPrecomposeHomotopyEquiv` へ送り、値域加群に追加の仮定を課さず、元の全評価で
係数前合成が擬同型となることを証明した。

同じ AW 余単位の自然性から、単位係数 cotensor の定数図式から同じ全単体族への
比較を構成した。この比較は元の全加群射について自然で、全次数で擬同型。
その自然性と二つから三つにより、同じ simplicial 加群の全ての面・退化も擬同型になる。
いずれも既存の cotensor の余単位・自然性・係数移送・合成の法則と証明の分割で、
一次 ID は追加しない。

比較の始域は正確に `moduleCotensor A D (𝟙_ (Complex A)) M` である。
元の加群 M との同定はまだ残る。この比較だけで Reedy fibrancy や
元の加群からの frame coaugmentation、K の完全忠実性を主張しない。
文脈は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`、`[Small.{u} D]`。

```lean
lemma moduleCotensorPreMap_quasiIso {K L : Complex A} (f : K ⟶ L)
    (hf : HomologicalComplex.homotopyEquivalences (ModuleCat A) (.up ℤ) f)
    (M : ModuleCategory A D) :
    moduleQuasiIso A D (moduleCotensorPreMap A D f M)

def moduleCotensorCounitNat (M : ModuleCategory A D) :
    (Functor.const SimplexCategoryᵒᵖ).obj (moduleCotensor A D (𝟙_ (Complex A)) M) ⟶
      moduleCotensorSimplices A D M

lemma moduleCotensorCounitNat_weak (M : ModuleCategory A D) (n : SimplexCategoryᵒᵖ) :
    moduleQuasiIso A D ((moduleCotensorCounitNat A D M).app n)

def moduleCotensorCounitFamily :
    moduleCotensorFunctor A D (𝟙_ (Complex A)) ⋙ Functor.const SimplexCategoryᵒᵖ ⟶
      moduleCotensorSimplicesFunctor A D

lemma moduleCotensorSimplices_maps_weak (M : ModuleCategory A D)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    moduleQuasiIso A D ((moduleCotensorSimplices A D M).map f)
```

検証結果は本節の末尾へ追記する。

**一覧：済み 10／全体 43（うち追加 1）**。

### §29.1 検証と実測

CotensorCounit の通常の対象ビルドは成功し、新しい公開宣言 5 本の依存公理監査も
成功した（標準の propext・Classical.choice・Quot.sound のみ）。どちらも指定の
共有鍵・280 秒の塊で実行した。新規 Lean は本節の 1 ファイル 102 行を加えて、
検証済み累計 59 ファイル・5,886 行・明示宣言 304 本（private 3 本）。
200 行を超える証明はない。単位則の実装は次節で検証する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 30. M10 の同じ cotensor の単位則（11-14）

単位複体からの全次数 Hom は、その唯一の生成元での評価により元の複体と線形同値。
既存の single 複体からの cochain 微分の式を使い、これを実複体同型へ組み立てる。
全次数の dg Hom 作用と可換する式を照合し、同じ主 Hom end による加群同型へ持ち上げる。
元の全加群射への自然性も同じ後合成の評価で確認する。
既存の cotensor の単位・自然性の法則と証明の分割で、一次 ID は追加しない。
文脈は `A : Type u`、`[CommRing A]`。
加群ではさらに `D : Type v`、`[DGCategory A D]`、`[Small.{u} D]`。

```lean
def cotensorUnitDegreeEquiv (K : Complex A) (p : ℤ) :
    (homComplex A (𝟙_ (Complex A)) K).X p ≃ₗ[A] K.X p

def cotensorUnitComplexIso (K : Complex A) :
    homComplex A (𝟙_ (Complex A)) K ≅ K

lemma cotensorUnitComplexIso_naturality (P Q : Complex A) :
    (homCovariantDG A (𝟙_ (Complex A))).map P Q ≫
        homPostcompose _ (cotensorUnitComplexIso A Q).hom =
      homPrecompose (cotensorUnitComplexIso A P).hom Q

lemma cotensorUnitComplexIso_postcompose {P Q : Complex A} (f : P ⟶ Q) :
    homPostcompose (𝟙_ (Complex A)) f ≫ (cotensorUnitComplexIso A Q).hom =
      (cotensorUnitComplexIso A P).hom ≫ f

def moduleCotensorUnitIsoObj (M : ModuleCategory A D) :
    moduleCotensor A D (𝟙_ (Complex A)) M ≅ M

lemma moduleCotensorUnitIsoObj_hom_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleCotensorUnitIsoObj A D M).hom =
      (cotensorUnitComplexIso A ((moduleEvaluation A D x).obj M)).hom

def moduleCotensorUnitIso : moduleCotensorFunctor A D (𝟙_ (Complex A)) ≅
    𝟭 (ModuleCategory A D)
```

検証結果は §32.2 に記録した。Reedy fibrancy と K の完全忠実性は引き続き未完。

**一覧：済み 10／全体 43（うち追加 1）**。


## 31. M10 の元の加群からの coaugmentation（11-14）

§30 の単位自然同型の逆と §29 の余単位自然変換を貼り合わせ、
元の加群 M の定数図式から同じ全単体族への比較を作る。
全加群射の自然性は同じ自然変換の合成に含まれる。
各次数の射自身の式を回収し、同じ単位同型と余単位の擬同型性から
元の全評価で擬同型となることを確認する。
これは既存の cotensor の単位・余単位・貼り合わせの法則と証明の分割であり、
一次 ID は追加しない。Reedy fibrancy と K の完全忠実性は引き続き未完。
文脈は A : Type u、[CommRing A]、D : Type v、[DGCategory A D]、[Small.{u} D]。

```lean
def moduleCotensorCoaugmentationFamily :
    Functor.const SimplexCategoryᵒᵖ ⟶ moduleCotensorSimplicesFunctor A D

lemma moduleCotensorCoaugmentationFamily_app (M : ModuleCategory A D)
    (n : SimplexCategoryᵒᵖ) :
    ((moduleCotensorCoaugmentationFamily A D).app M).app n =
      (moduleCotensorUnitIsoObj A D M).inv ≫ (moduleCotensorCounitNat A D M).app n

lemma moduleCotensorCoaugmentationFamily_weak (M : ModuleCategory A D)
    (n : SimplexCategoryᵒᵖ) :
    moduleQuasiIso A D (((moduleCotensorCoaugmentationFamily A D).app M).app n)
```

検証結果は §32.2 に記録した。

**一覧：済み 10／全体 43（うち追加 1）**。


## 32. M10 の同じ半自由 Hom の Quillen 条件（11-14）

N01 の厳密な持ち上げで使った同じ実半自由 filtration の全次数 Hom の全射性と、
既存の半自由 Hom の擬同型保存を、同じ全 Hom 関手の右 Quillen 条件へ束ねる。
両モデル構造は構成済みの実モデルであり、モデル構造を引数に置かない。
同じ正規化単体を使う source frame 側にも利用できる入力である。
これは既存の Hom の係数移送の法則と M10 の証明の分割で、一次 ID は追加しない。
右 Quillen 条件だけで K の完全忠実性や元の全族の完成を主張しない。
文脈は A : Type u、[CommRing A]。

```lean
lemma strictRawModuleSemifree_hom_fibration (X : (operad A).Algebra)
    {P M N : strictRawModuleCategory A X}
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P)
    (p : M ⟶ N) (hp : projectiveFibrations A ((strictRawModuleUnderlying X).map p)) :
    projectiveFibrations A (eHomWhiskerLeft (Complex A) P p)

lemma strictRawModuleSemifree_hom_isRightQuillen (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P) :
    letI := strictRawModuleModelCategory A X
    letI := projectiveModelCategory A
    SerrePositivity.Quillen.IsRightQuillen
      ((eHomFunctor (Complex A) (strictRawModuleCategory A X)).obj (op P))
```

検証結果は §32.2 に記録した。

**一覧：済み 10／全体 43（うち追加 1）**。

### 32.1 同じ source frame に向けた既存の随伴の部品（紙）

`DifferentialGraded/Module/Hom/HomotopyAndOperations.tensorModuleFunctor` は、固定した
元の加群 P に対する `Complex A ⥤ ModuleCategory A D` を既に構成している。
`Module/Hom/ColimitsAndRightHom.moduleParamCurry` と `TensorFree.moduleParamUncurry` は
同じ二つの Hom 集合の間を往復し、`moduleParamUncurry_curry`・
`moduleParamCurry_uncurry` が両逆を証明している。係数射の自然性は
`moduleParamUncurry_precomp`、固定加群変数の自然性は
`moduleParamUncurry_naturality_source` にある。

したがって §32 の同じ Hom 関手の右 Quillen 条件は、これらの既存の転置の法則を
随伴へ束ねた後、`leftQuillen_frame_reedyCofibrant` と既存の
`ComplexLimits.normalizedSimplex_reedyCofibrant` に接続する候補となる。
元の加群への随伴と同じ frame Hom の比較はまだ実装していない。この紙の候補を
Reedy 条件や K の完全忠実性の証明として数えない。


### 32.2 §30–§32 の検証・実測

CotensorUnit、CotensorCoaugmentation、RawModuleHomQuillen の通常の対象ビルドは
すべて成功した。新しい公開宣言 12 本の依存公理監査も成功し、使用する公理は
propext・Classical.choice・Quot.sound のみ。指定の impl 鍵で、一回 280 秒の塊を
使った。大きい監査・root ビルドはこのレーンでは実行していない。

新規 Lean の今回の三ファイルはそれぞれ 148・57・67 行、計 272 行、公開宣言 12 本。
§29.1 の累計に加え、検証済み累計は 62 ファイル・6,158 行・明示宣言 316 本
（private 3 本）。200 行を超える証明はない。一次 ID の追加はない。

同じ単位 cotensor と元の加群の自然同型、元の加群を始域とする全単体の比較と
その各次数の擬同型性までが検証済みになった。Reedy 条件とモデル frame Hom から
元の dg Hom への全標的自然な比較、K の完全忠実性、M10 の一般の native な辺・fiber
と全族の完成は残る。M11 以降と G12 の目標も維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 33. M10 の同じ半自由 source frame と全標的 Hom（11-14）

前の goal ターンは §28–§32 の単位則・全単体 coaugmentation と半自由 Hom の
Quillen 条件を対象ビルドと小さい監査まで通した進捗。
今回、§32.1 で確認した既存の転置・逆転置の両逆を実随伴に束ねた。
標的への自然性は元の主 Hom end の評価ごとに Hom 後合成の式から証明した。

同じ `SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A` を既存の
`tensorModuleFunctor` で送り、元の全加群射に自然な source frame の全族を作る。
元の AW 余単位と既存の左単位同型から、元の加群への全自然 augmentation を保持する。

BE 固定底では N01 の実モデルと同じ Hom の右 Quillen 条件を使い、係数テンソルの
左 Quillen 条件を得る。既存の `normalizedSimplex_reedyCofibrant` と
`leftQuillen_frame_reedyCofibrant` を使い、Reedy 条件を作り直さない。
同じ AW 余単位の実鎖収縮と Brown の補題により、全作用素の弱同値性と指定 augmentation
の弱同値性を照合する。実モデルの全対象の fibrancy から、元の任意の標的への同じ
cosimplicial Hom の Kan 性を得る。

いずれも既存の tensor/Hom の随伴・自然性・単位/余単位の貼り合わせの法則と、
M10 の証明の分割であり、一次 ID は追加しない。半自由であるのは始域の probe P。
標的 N は元の任意の通常 dg 加群である。単体集合のモデル構造を仮定しない。
一般の文脈は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`、`[Small.{u} D]`。
BE の文脈では `A : Type u`、`[CommRing A]` と表示された固定 BE 底 X を使う。

### TensorHomAdjunction

```lean
lemma moduleParamCurry_postcompose {K : Complex A} {M N P : ModuleCategory A D}
    (f : moduleTensorLeftObj A D K M ⟶ N) (g : N ⟶ P) :
    moduleParamCurry A D (f ≫ g) =
      moduleParamCurry A D f ≫ eHomWhiskerLeft (Complex A) M g

def moduleTensorHomEquiv (M : ModuleCategory A D) (K : Complex A)
    (N : ModuleCategory A D) :
    ((tensorModuleFunctor (ForgetEnrichment.to (Complex A) M)).obj K ⟶ N) ≃
      (K ⟶ ((eHomFunctor (Complex A) (ModuleCategory A D)).obj (op M)).obj N)

def moduleTensorHomAdjunction (M : ModuleCategory A D) :
    tensorModuleFunctor (ForgetEnrichment.to (Complex A) M) ⊣
      (eHomFunctor (Complex A) (ModuleCategory A D)).obj (op M)
```

### TensorSimplices

```lean
def moduleTensorSimplicesFunctor :
    ModuleCategory A D ⥤ (SimplexCategory ⥤ ModuleCategory A D)

lemma moduleTensorSimplices_obj_eval (M : ModuleCategory A D) (n : SimplexCategory) (x : D) :
    (moduleEvaluation A D x).obj (((moduleTensorSimplicesFunctor A D).obj M).obj n) =
      AlexanderWhitney.cochains A (SSet.stdSimplex.obj n) ⊗
        (moduleEvaluation A D x).obj M

lemma moduleTensorSimplices_map_eval {M N : ModuleCategory A D} (f : M ⟶ N)
    (n : SimplexCategory) (x : D) :
    (moduleEvaluation A D x).map (((moduleTensorSimplicesFunctor A D).map f).app n) =
      𝟙 (AlexanderWhitney.cochains A (SSet.stdSimplex.obj n)) ⊗ₘ
        (moduleEvaluation A D x).map f

def moduleTensorSimplicesAugmentation (M : ModuleCategory A D) :
    (moduleTensorSimplicesFunctor A D).obj M ⟶ (Functor.const SimplexCategory).obj M

lemma moduleTensorSimplicesAugmentation_eval (M : ModuleCategory A D)
    (n : SimplexCategory) (x : D) :
    (moduleEvaluation A D x).map ((moduleTensorSimplicesAugmentation A D M).app n) =
      (AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n) ⊗ₘ
        𝟙 ((moduleEvaluation A D x).obj M)) ≫ (λ_ ((moduleEvaluation A D x).obj M)).hom

def moduleTensorSimplicesAugmentationFamily :
    moduleTensorSimplicesFunctor A D ⟶ Functor.const SimplexCategory
```

### RawModuleTensorFrame

```lean
lemma strictRawModuleSemifree_tensor_isLeftQuillen (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P) :
    letI := projectiveModelCategory A
    letI := strictRawModuleModelCategory A X
    SerrePositivity.Quillen.IsLeftQuillen
      (tensorModuleFunctor (ForgetEnrichment.to (Complex A) P))

lemma strictRawModuleTensorFrame_reedyCofibrant (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P) :
    letI := strictRawModuleModelCategory A X
    reedyLeft simplex (cofibrations (strictRawModuleCategory A X))
      (initial.to ((moduleTensorSimplicesFunctor A
        (dgAlgebraCategory A ((assocForget A).obj X))).obj P))

lemma strictRawModuleTensorFrame_homotopicallyConstant (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P)
    {n m : SimplexCategory} (f : n ⟶ m) :
    letI := strictRawModuleModelCategory A X
    weakEquivalences (strictRawModuleCategory A X)
      (((moduleTensorSimplicesFunctor A
        (dgAlgebraCategory A ((assocForget A).obj X))).obj P).map f)

lemma strictRawModuleTensorFrame_augmentation_weak (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P)
    (n : SimplexCategory) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((moduleTensorSimplicesAugmentation A
        (dgAlgebraCategory A ((assocForget A).obj X)) P).app n)

lemma strictRawModuleTensorHom_kanComplex (X : (operad A).Algebra)
    (P N : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P) :
    SSet.KanComplex
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
        ((moduleTensorSimplicesFunctor A
          (dgAlgebraCategory A ((assocForget A).obj X))).obj P)).obj N)
```


対象ビルド・小さい監査の結果と最終実測は §34.1 に記録した。
同じ source frame Hom と元の dg Hom との全標的自然な同型は §34 で実装した。
モデルで選んだ frame との比較、K の完全忠実性と元の全族の一般の native な辺・fiber
の完成は引き続き残る。

**一覧：済み 10／全体 43（うち追加 1）**。


## 34. M10 の同じ source frame Hom と元の dg Hom の全比較（11-14）

§33 の同じ全単体 source frame Hom を、元の主 Hom end の
`DK(τ≤0 moduleHom(P,N))` に全単体で同定する。
既存の `normalizedSimplexHomEquiv` に同じ実 tensor/Hom 転置を前置するだけであり、
Dold–Kan の部品・smart 切断・自由単体の評価は作り直さない。

同じ転置の係数前合成自然性を両逆と逆転置の法則から回収し、全ての面・退化と可換する
実単体集合同型を得る。標的射については §33 の転置の後合成自然性と既存の
`normalizedSimplexHomEquiv_postcomp` を貼り合わせる。
従って標的 N を動かす同じ全関手の自然同型となる。

比較対象の dg 圏は正確に `RightModule A D`、対象は元の P,N を
`ForgetEnrichment.to (Complex A)` で戻したもの。零次数をホモロジーの商へ変えない。
これは M10 の既存の写像空間比較の証明分割と、既存の転置・自然性の法則で、
一次 ID は追加しない。文脈は `A : Type u`、`[CommRing A]`、`D : Type v`、
`[DGCategory A D]`、`[Small.{u} D]`。
略記 `doldKanHomModule`・`doldKanHomSpace` は Kerodon の
`ExamplesOfInfinityCategories.DifferentialGradedCategories` の実 Dold–Kan。
`cosimplicialHom` は既存の `Project.HomotopyDiagramComparison.CosimplicialHom`、
`truncatedDoldKanFunctor` は既存の `EInfinity.ComplexLimits` の関手である。

```lean
lemma moduleParamCurry_precompose {K L : Complex A} {P N : ModuleCategory A D}
    (g : K ⟶ L) (f : moduleTensorLeftObj A D L P ⟶ N) :
    moduleParamCurry A D (tensorModuleMap g (ForgetEnrichment.to (Complex A) P) ≫ f) =
      g ≫ moduleParamCurry A D f

def moduleTensorSimplexHomEquiv (P N : ModuleCategory A D) (n : SimplexCategory) :
    (((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) ≃
      (doldKanHomModule (R := A) (D := RightModule A D)
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)).obj (op n)

def moduleTensorHomDoldKanIso (P N : ModuleCategory A D) :
    (cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P)).obj N ≅
      doldKanHomSpace (R := A) (D := RightModule A D)
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)

def moduleTensorHomDoldKanNatIso (P : ModuleCategory A D) :
    cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P) ≅
      (eHomFunctor (Complex A) (ModuleCategory A D)).obj (op P) ⋙
        truncatedDoldKanFunctor A
```

対象ビルドと小さい監査の結果・最終実測は §34.1 に記録した。
モデルで選んだ frame とこの具体的な source frame の全比較、K の完全忠実性、
元の全族の一般の native な辺・fiber の完成は残る。M11 以降・G12 の目標も維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 34.1 §33–§34 の検証と実測

通常の対象ビルドは TensorHomAdjunction、TensorSimplices、RawModuleTensorFrame、
TensorDoldKanHom のすべてで成功した。新しい公開宣言 18 本の依存公理監査も成功し、
propext・Classical.choice・Quot.sound のみを使う。すべて指定の impl 鍵と
一回 280 秒の塊で実行した。

新規 Lean は四ファイル、それぞれ 78・147・147・97 行、計 469 行、公開宣言 18 本。
§32.2 の累計に加え、検証済み累計は 66 ファイル・6,627 行・明示宣言 334 本
（private 3 本）。200 行を超える証明はない。一次 ID の追加はない。

同じ元の半自由 P の具体的 source frame が実モデルの条件を満たし、任意の元の標的 N
への全単体 Hom が元の dg Hom の実 Dold–Kan に全標的自然に同型になることまで検証した。
モデルで選んだ frame との全比較、通常源からの局所化比較 K の完全忠実性、
M10 の一般の native な辺・fiber と全族の完成は未完。
M11 以降と G12 を含む元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 35. M10 の選択済み frame と同じ source frame の全自然比較（11-14）

前の goal ターンは §33–§34 の実 source frame 条件と元の dg Hom の実 Dold–Kan
への全単体・全標的自然な比較を検証してコミットした進捗。
今回は元の `SemifreeDGModules` の閉零圏と同じ dg 全包含を probe のパラメータにする。
元の全閉零射を持つ全包含であり、対象の離散族に置き換えない。
N01 の同じモデル構造・同じ関手的分解・同じ `strictRawModuleSourceFrameFamily` を使う。

既存の `FrameOverFunctor.commonObj` に同じ二つの augmentation を渡し、
元の probe を底に持つ共通 Reedy cofibrant 族を得る。二つの実射と、同じ augmentation
の上で可換する全自然変換の等式を保持する。
三つの cosimplicial Hom を全 probe に反変・元の任意の標的に共変な二変数関手として構成し、
標準 Hom とテンソル Hom から同じ共通 Hom への二つの自然変換を回収する。

両脚の同じ射に `fixedFrameOverFunctor_homLeft_homotopyEquivalence` と
`fixedFrameOverFunctor_homRight_homotopyEquivalence` を適用する。
三つの元の Hom は Kan であり、二つの比較射は各 probe・各標的で実単体的ホモトピー同値。
単体集合のモデル構造を仮定せず、比較を homotopy category だけへ落とさない。

これは M10 の既存の frame/Hom 比較の証明分割と、既存の augmentation・自然性・
貼り合わせの法則であり、一次 ID は追加しない。
文脈は `A : Type u`、`[CommRing A]`。`IsSimplicialHomotopyEquivalence` は Kerodon の
`KanComplexes.TheHomotopyTheoryOfKanComplexes` の実ホモトピー同値。

### RawModuleProbeFrame

```lean
abbrev strictRawModuleProbeCategory (X : (operad A).Algebra) : Type (u + 1)

def strictRawModuleProbeFunctor (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ strictRawModuleCategory A X

lemma strictRawModuleProbeFunctor_semifree (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleProbeFunctor A X).obj P)

lemma strictRawModuleProbeFunctor_cofibrant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    let := strictRawModuleModelCategory A X
    IsCofibrant ((strictRawModuleProbeFunctor A X).obj P)

def strictRawModuleProbeTensorFrame (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ (SimplexCategory ⥤ strictRawModuleCategory A X)

def strictRawModuleProbeTensorAugmentation (X : (operad A).Algebra) :
    strictRawModuleProbeTensorFrame A X ⟶
      strictRawModuleProbeFunctor A X ⋙ Functor.const SimplexCategory

lemma strictRawModuleProbeTensorFrame_cofibrant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    let := strictRawModuleModelCategory A X
    reedyLeft simplex (cofibrations (strictRawModuleCategory A X))
      (initial.to ((strictRawModuleProbeTensorFrame A X).obj P))

lemma strictRawModuleProbeTensorAugmentation_weak (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) (n : SimplexCategory) :
    let := strictRawModuleModelCategory A X
    weakEquivalences (strictRawModuleCategory A X)
      (((strictRawModuleProbeTensorAugmentation A X).app P).app n)

lemma strictRawModuleProbeTensorFrame_homotopicallyConstant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) {n m : SimplexCategory} (f : n ⟶ m) :
    let := strictRawModuleModelCategory A X
    weakEquivalences (strictRawModuleCategory A X)
      (((strictRawModuleProbeTensorFrame A X).obj P).map f)
```

### RawModuleProbeCommonFrame

```lean
def strictRawModuleProbeStandardFrame (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ (SimplexCategory ⥤ strictRawModuleCategory A X)

def strictRawModuleProbeCommonFrame (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ (SimplexCategory ⥤ strictRawModuleCategory A X)

def strictRawModuleProbeCommonToStandard (X : (operad A).Algebra) :
    strictRawModuleProbeCommonFrame A X ⟶ strictRawModuleProbeStandardFrame A X

def strictRawModuleProbeCommonToTensor (X : (operad A).Algebra) :
    strictRawModuleProbeCommonFrame A X ⟶ strictRawModuleProbeTensorFrame A X

lemma strictRawModuleProbeCommon_over (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    strictRawModuleProbeCommonToStandard A X ≫
        Functor.whiskerLeft (strictRawModuleProbeFunctor A X)
          (strictRawModuleSourceFrameFamily A X).augmentation =
      strictRawModuleProbeCommonToTensor A X ≫ strictRawModuleProbeTensorAugmentation A X

def strictRawModuleProbeStandardHom (X : (operad A).Algebra) :
    (strictRawModuleProbeCategory A X)ᵒᵖ ⥤ strictRawModuleCategory A X ⥤ SSet.{u}

def strictRawModuleProbeTensorHom (X : (operad A).Algebra) :
    (strictRawModuleProbeCategory A X)ᵒᵖ ⥤ strictRawModuleCategory A X ⥤ SSet.{u}

def strictRawModuleProbeCommonHom (X : (operad A).Algebra) :
    (strictRawModuleProbeCategory A X)ᵒᵖ ⥤ strictRawModuleCategory A X ⥤ SSet.{u}

def strictRawModuleProbeHomFromStandard (X : (operad A).Algebra) :
    strictRawModuleProbeStandardHom A X ⟶ strictRawModuleProbeCommonHom A X

def strictRawModuleProbeHomFromTensor (X : (operad A).Algebra) :
    strictRawModuleProbeTensorHom A X ⟶ strictRawModuleProbeCommonHom A X
```

### RawModuleProbeHomComparison

```lean
lemma strictRawModuleProbeHomFromStandard_homotopyEquivalence (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    IsSimplicialHomotopyEquivalence (((strictRawModuleProbeHomFromStandard A X).app P).app N)

lemma strictRawModuleProbeHomFromTensor_homotopyEquivalence (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    IsSimplicialHomotopyEquivalence (((strictRawModuleProbeHomFromTensor A X).app P).app N)

lemma strictRawModuleProbeStandardHom_kanComplex (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    SSet.KanComplex (((strictRawModuleProbeStandardHom A X).obj P).obj N)

lemma strictRawModuleProbeTensorHom_kanComplex (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    SSet.KanComplex (((strictRawModuleProbeTensorHom A X).obj P).obj N)

lemma strictRawModuleProbeCommonHom_kanComplex (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    SSet.KanComplex (((strictRawModuleProbeCommonHom A X).obj P).obj N)
```


対象ビルドと小さい監査の結果・実測は §35.2 に記録した。
K の完全忠実性と元の全族の一般の native な辺・fiber の完成はまだ残る。
M11 以降と G12 を含む元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 35.1 同じ共通 frame 条件の証明分割

共通 Hom の Kan 条件へ直接実共通置換の構成を渡すと、深い定義の展開により
200,000 heartbeats に達した。同じ共通 frame の Reedy 条件と定数性を、その具体的な
族の型を持つ二本の補題へ分割して渡す。新しい数学の条件は加えず、モデルも同じ実構成。
いずれも既存の共通 frame の法則と M10 の証明分割であり、一次 ID は追加しない。

```lean
lemma strictRawModuleProbeCommonFrame_cofibrant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    let := strictRawModuleModelCategory A X
    reedyLeft simplex (cofibrations (strictRawModuleCategory A X))
      (initial.to ((strictRawModuleProbeCommonFrame A X).obj P))

lemma strictRawModuleProbeCommonFrame_homotopicallyConstant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) {n m : SimplexCategory} (f : n ⟶ m) :
    let := strictRawModuleModelCategory A X
    weakEquivalences (strictRawModuleCategory A X)
      (((strictRawModuleProbeCommonFrame A X).obj P).map f)
```

**一覧：済み 10／全体 43（うち追加 1）**。


### 35.2 検証と実測

RawModuleProbeFrame、RawModuleProbeCommonFrame、RawModuleProbeHomComparison の
通常の対象ビルドはすべて成功した。新しい公開宣言 26 本の依存公理監査も成功し、
propext・Classical.choice・Quot.sound の範囲である。指定の impl 鍵と
一回 280 秒の塊で実行した。

§35.1 の分割に加え、共通族の関手等式から弱同値の命題を congrArg で明示的に移送した。
大きい実共通置換の定義どうしを展開して照合することを避け、200,000 heartbeats の
制限を上げずに通った。型・数学の条件・元の比較射は変えていない。

新規 Lean は三ファイル、それぞれ 109・157・90 行、計 356 行、公開宣言 26 本。
§34.1 の累計に加え、検証済み累計は 69 ファイル・6,983 行・明示宣言 360 本
（private 3 本）。200 行を超える証明はない。一次 ID は追加していない。

同じ元の半自由 probe をパラメータとする三つの全 Hom が Kan であり、同じ二変数の
実自然変換の両脚が各 probe・任意の標的で実単体的ホモトピー同値であることまで検証した。
元の augmentation の底の全等式も保持する。
§34 の dg Hom 同型の probe 変数への自然性の束ね、通常源の局所化比較 K の同じ作用の照合と
完全忠実性、M10 の一般の native な辺・fiber と全族の完成は引き続き残る。
M11 以降と G12 を含む元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 36. M10 の元の dg Hom への二変数自然な端点同定（11-14）

前の goal ターンは §35 の同じ全 probe・全標的の frame 比較を検証・コミットした進捗。
今回は §34 の実 Dold–Kan Hom 同型に、probe 変数の自然性を付ける。
既存の逆転置の加群始域射への自然性を、同じ転置との両逆の式で戻した。
元の `eHomFunctor` と `truncatedDoldKanFunctor` を合成し、元の主 Hom end の
実 Dold–Kan を二変数関手として保持する。
源は元の閉零加群圏であり、対象の離散族に置き換えない。

同じ二変数同型を元の半自由 probe 全包含で前合成し、その逆と §35 の同じ右脚を合成する。
これにより元の dg Hom から共通 Hom への実二変数自然変換を得る。
同じ実 Dold–Kan の Kan 性と、三つの同じ Kan Hom の比較の合成則を使い、
その同じ射が各 probe・任意の元の標的で実単体的ホモトピー同値となることを照合する。

いずれも既存の tensor/Hom の始域自然性・係数移送・同型の逆・貼り合わせの法則と、
M10 の写像空間比較の証明分割であり、一次 ID は追加しない。
一般部分の文脈は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`、`[Small.{u} D]`。
BE 部分では表示された固定 BE 底 X を使う。
`cosimplicialHomBifunctor` は既存の `Project.HomotopyDiagramComparison.CosimplicialHom`、
`IsSimplicialHomotopyEquivalence` は既存の Kerodon の Kan 複体の実ホモトピー同値である。

### TensorDoldKanBifunctor

```lean
lemma moduleParamCurry_sourceMap {K : Complex A} {M P N : ModuleCategory A D}
    (g : M ⟶ P) (f : moduleTensorLeftObj A D K P ⟶ N) :
    moduleParamCurry A D (moduleTensorLeftMap A D K g ≫ f) =
      moduleParamCurry A D f ≫ eHomWhiskerRight (Complex A) g N

def moduleDoldKanHomBifunctor :
    (ModuleCategory A D)ᵒᵖ ⥤ ModuleCategory A D ⥤ SSet.{u}

def moduleTensorHomDoldKanBifunctorIso :
    (moduleTensorSimplicesFunctor A D).op ⋙ cosimplicialHomBifunctor ≅
      moduleDoldKanHomBifunctor A D
```

### RawModuleProbeDoldKanHom

```lean
def strictRawModuleProbeDoldKanHom (X : (operad A).Algebra) :
    (strictRawModuleProbeCategory A X)ᵒᵖ ⥤ strictRawModuleCategory A X ⥤ SSet.{u}

def strictRawModuleProbeTensorDoldKanIso (X : (operad A).Algebra) :
    strictRawModuleProbeTensorHom A X ≅ strictRawModuleProbeDoldKanHom A X

def strictRawModuleProbeHomFromDoldKan (X : (operad A).Algebra) :
    strictRawModuleProbeDoldKanHom A X ⟶ strictRawModuleProbeCommonHom A X

lemma strictRawModuleProbeDoldKanHom_kanComplex (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    SSet.KanComplex (((strictRawModuleProbeDoldKanHom A X).obj P).obj N)

lemma strictRawModuleProbeHomFromDoldKan_homotopyEquivalence (X : (operad A).Algebra)
    (P : (strictRawModuleProbeCategory A X)ᵒᵖ) (N : strictRawModuleCategory A X) :
    IsSimplicialHomotopyEquivalence (((strictRawModuleProbeHomFromDoldKan A X).app P).app N)
```


対象ビルド・小さい監査の結果と最終実測は §36.1 に記録した。
同じ局所化比較 K が誘導する写像空間の射の照合と完全忠実性、M10 の一般の native な辺・fiber
と全族の完成はまだ残る。M11 以降と G12 を含む元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 36.1 検証と実測

TensorDoldKanBifunctor と RawModuleProbeDoldKanHom の通常の対象ビルドは成功した。
新しい公開宣言 8 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。すべて指定の impl 鍵と一回 280 秒の塊で実行した。

新規 Lean は二ファイル、それぞれ 72・79 行、計 151 行、公開宣言 8 本。
§35.2 の累計に加え、検証済み累計は 71 ファイル・7,134 行・明示宣言 368 本
（private 3 本）。200 行を超える証明はない。一次 ID は追加していない。

同じテンソル Hom と元の dg Hom の実 Dold–Kan の同型が、元の始域・標的の両変数に
自然になった。同じ実二変数自然変換の標準側・dg Hom 側の二脚を共通 Hom に保ち、
各 probe と任意の元の標的でホモトピー同値となることまで検証した。
指定半自由模型の実 pinched Hom への端点同定、K の同じ誘導射の照合と完全忠実性、
M10 の一般の native な辺・fiber と全族の完成は未完。元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 37. M10 の指定 pinched Hom と同じ K の実誘導射（11-14）

§36 の同じ二変数 dg Hom 端点を、元の指定半自由模型の実 pinched Hom に同定する。
既存の `doldKanHomPinchedIso` を、元の二つの半自由 probe に直接適用する。
全単体テンソル Hom の端点も同じ二変数 Dold–Kan 同型と合成して同定する。
任意の同じ Hom 鎖写像への可換性は、既存の `doldKanHomPinchedIso_chainMap` の特殊化。
Dold–Kan・pinched 模型を作り直さない。

次に元の probe 全包含を同じ ULiftHom 表示へ送る全関手を作り、その標準局所化頂点を保持する。
同じ `dgModuleResolutionRetractIso` の成分から、元の通常源の値を指定半自由頂点へ戻す。
既存の同じ `strictRawModuleComparison_vertexIso` の成分を合成し、K の値の指定端点同型を得る。
対象ごとの別の同型を選ぶものではない。

その同じ K の実 `pinchedHomMap` の後に、同じ二つの端点成分による
`pinchedEndpointEquivalence` を合成する。さらに同じ実 Dold–Kan/pinched 同型の逆を合成し、
K の誘導射を元の dg Hom 座標で具体化する。その同じ座標射は、端点同型の順射を
後合成すると元の指定 pinched Hom 射を全単体で回収する。

これは M10 の既存比較の単位/余単位・係数移送・自然性・貼り合わせの法則と証明の分割であり、
一次 ID は追加しない。K の誘導射の同値性を仮定として置いていない。
この具体化だけでその射の同値性や K の完全忠実性を証明したとは数えない。
文脈は `A : Type u`、`[CommRing A]`。
`PinchedHom.pinchedHom` は既存の dg nerve の実 pinched Hom、`Basic.pinchedHom` は
既存の `TheHomotopyTheoryOfInfinityCategories.MorphismSpaces` のもの。
`Simplex.vertex` と `DifferentialGradedCategories.Functor.map` は既存の dg nerve の関手である。

### RawModuleProbeNativeHom

```lean
def strictRawModuleProbeNativeHomIso (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    SSet.uliftFunctor.{u + 1, u}.obj
      (((strictRawModuleProbeDoldKanHom A X).obj (op P)).obj
        ((strictRawModuleProbeFunctor A X).obj Q)) ≅
      PinchedHom.pinchedHom A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q)

def strictRawModuleProbeTensorNativeHomIso (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    SSet.uliftFunctor.{u + 1, u}.obj
      (((strictRawModuleProbeTensorHom A X).obj (op P)).obj
        ((strictRawModuleProbeFunctor A X).obj Q)) ≅
      PinchedHom.pinchedHom A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q)

lemma strictRawModuleProbeNativeHomIso_chainMap (X : (operad A).Algebra)
    (P Q P' Q' : strictRawModuleProbeCategory A X)
    (φ : homObject A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q) ⟶
        homObject A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
          (ForgetEnrichment.to (Complex A) P') (ForgetEnrichment.to (Complex A) Q')) :
    SSet.uliftFunctor.{u + 1, u}.map (doldKanHomSpaceChainMap
      (D := SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
      (E := SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
      (x := ForgetEnrichment.to (Complex A) P) (y := ForgetEnrichment.to (Complex A) Q)
      (x' := ForgetEnrichment.to (Complex A) P') (y' := ForgetEnrichment.to (Complex A) Q') φ) ≫
        (strictRawModuleProbeNativeHomIso A X P' Q').hom =
      (strictRawModuleProbeNativeHomIso A X P Q).hom ≫ pinchedHomChainMap φ
```

### RawModuleProbeComparisonMap

```lean
def strictRawModuleProbeRelativeFunctor (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ (strictRawModuleRelativeCategory A X).category

def strictRawModuleProbeLocalizationVertex (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    (localizationNerve (strictRawModuleRelativeCategory A X)) _⦋0⦌

def strictRawModuleProbeSourceVertexIso (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    VertexIso
      ((strictRawModuleSource A X).app (op ⦋0⦌)
        (ComposableArrows.mk₀ ((strictRawModuleProbeRelativeFunctor A X).obj P)))
      (Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A) P))

def strictRawModuleProbeComparisonVertexIso (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    VertexIso
      ((strictRawModuleComparison A X).app (op ⦋0⦌) (strictRawModuleProbeLocalizationVertex A X P))
      (Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A) P))

def strictRawModuleProbeComparisonPinchedMap (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    Basic.pinchedHom (X := localizationNerve (strictRawModuleRelativeCategory A X))
      (strictRawModuleProbeLocalizationVertex A X P) (strictRawModuleProbeLocalizationVertex A X Q) ⟶
      PinchedHom.pinchedHom A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) Q)

def strictRawModuleProbeComparisonDoldKanMap (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    Basic.pinchedHom (X := localizationNerve (strictRawModuleRelativeCategory A X))
      (strictRawModuleProbeLocalizationVertex A X P) (strictRawModuleProbeLocalizationVertex A X Q) ⟶
      SSet.uliftFunctor.{u + 1, u}.obj
        (((strictRawModuleProbeDoldKanHom A X).obj (op P)).obj
          ((strictRawModuleProbeFunctor A X).obj Q))

lemma strictRawModuleProbeComparisonDoldKanMap_triangle (X : (operad A).Algebra)
    (P Q : strictRawModuleProbeCategory A X) :
    strictRawModuleProbeComparisonDoldKanMap A X P Q ≫ (strictRawModuleProbeNativeHomIso A X P Q).hom =
      strictRawModuleProbeComparisonPinchedMap A X P Q
```


対象ビルド・小さい監査の結果と最終実測は §37.1 に記録した。
未完の中心は、ここで具体化した同じ K の全誘導射が §35–§36 の実 frame 比較と一致することと、
その射の同値性・完全忠実性である。零単体・π₀ だけの一致で代用しない。
M10 の一般の native な辺・fiber と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 37.1 検証と実測

RawModuleProbeNativeHom と RawModuleProbeComparisonMap の通常の対象ビルドは成功した。
新しい公開宣言 10 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。

新規 Lean は二ファイル、それぞれ 76・120 行、計 196 行、公開宣言 10 本。
§36.1 の累計に加え、検証済み累計は 73 ファイル・7,330 行・明示宣言 378 本
（private 3 本）。200 行を超える証明はない。一次 ID は追加していない。

同じ局所化比較 K の実 pinched Hom 射を、指定半自由端点と元の dg Hom の Dold–Kan 座標で
具体化し、元の射を全単体で回収する三角等式まで検証した。その射と実 frame 比較との
全高次照合・同値性・K の完全忠実性は未完。M10 の一般の native な辺・fiber と全族、
M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 38. M10 の元の probe 全通常 nerve 上の同じ三角比較（11-14）

§37 の頂点比較の元になっている同じ全解像度 retract を、probe の全通常 nerve へ前合成する。
通常相対圏と同じ Hom 宇宙を保つため、元の probe 閉零圏に同じ ULiftHom 表示を適用する。
元の全包含を関手として保持し、その全通常鎖を既存の `closedNerveSimplex` で指定半自由模型へ送る。

同じ dg 包含に関する `dgFunctor_closedNerveSimplex` の全次元自然性から、
全加群の元の dg 源と厳密に可換する全関手の等式を証明した。
その等式で、同じ `dgModuleResolutionRetractIso` の前合成を移送する。
さらに、同じ `strictRawModuleComparison_sourceIso` の前合成と合成し、
K の同じ三角比較を probe の全通常 nerve 上の同じ関手同型として保持する。

これは M10 の既存比較の係数移送・自然性・単位/余単位の貼り合わせの法則と証明の分割で、
一次 ID は追加しない。比較は元の全通常鎖の上にある。
frame 係数から作る全高次の評価円柱と同じ K の Hom 誘導射との照合は引き続き必要。
文脈は `A : Type u`、`[CommRing A]`。`DifferentialGradedCategories.Functor.map` は
既存の dg 関手の nerve。モデル構造や比較射の同値性を引数に置かない。

```lean
abbrev strictRawModuleLiftedProbeCategory (X : (operad A).Algebra) : Type (u + 1)

def strictRawModuleLiftedProbeFunctor (X : (operad A).Algebra) :
    strictRawModuleLiftedProbeCategory A X ⥤ (strictRawModuleRelativeCategory A X).category

def strictRawModuleLiftedProbeDGSource (X : (operad A).Algebra) :
    nerve (strictRawModuleLiftedProbeCategory A X) ⟶ strictModuleInfinity A X

lemma strictRawModuleLiftedProbeDGSource_inclusion (X : (operad A).Algebra) :
    nerveMap (strictRawModuleLiftedProbeFunctor A X) ≫ strictRawModuleDGSource A X =
      strictRawModuleLiftedProbeDGSource A X ≫
        DifferentialGradedCategories.Functor.map
          (semifreeInclusion A (dgAlgebraCategory A ((assocForget A).obj X)))

def strictRawModuleLiftedProbeSourceIso (X : (operad A).Algebra) :
    FunctorIso
      (nerveMap (strictRawModuleLiftedProbeFunctor A X) ≫ strictRawModuleSource A X)
      (strictRawModuleLiftedProbeDGSource A X)

def strictRawModuleLiftedProbeComparisonIso (X : (operad A).Algebra) :
    FunctorIso
      (nerveMap (strictRawModuleLiftedProbeFunctor A X) ≫
        (localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫
          strictRawModuleComparison A X))
      (strictRawModuleLiftedProbeDGSource A X)
```

対象ビルド・小さい監査の結果と最終実測は §38.1 に記録した。
K の同じ Hom 誘導射の同値性・完全忠実性、M10 の一般の native な辺・fiber と全族、
M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 38.1 検証と実測

RawModuleProbeSourceTriangle の通常の対象ビルドは成功した。
新しい公開宣言 6 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。

新規 Lean は一ファイル 113 行、公開宣言 6 本。
§37.1 の累計に加え、検証済み累計は 74 ファイル・7,443 行・明示宣言 384 本
（private 3 本）。200 行を超える証明はない。一次 ID は追加していない。

元の probe の同じ全通常 nerve に沿い、元の dg 源との厳密な包含等式、同じ解像度 retract
の全関手比較、同じ K の局所化三角の全関手比較まで検証した。
frame 係数からの実全高次評価円柱を、§37 の同じ K の Hom 誘導射へ結ぶ照合とその同値性は
引き続き未完であり、完全忠実性には数えない。
M10 の一般の native な辺・fiber と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 39. M10 の全 frame 単体の同じ実評価図式と源内の屋根（11-14）

§35–§38 の同じテンソル frame Hom の反対要素圏を、元の相対圏と同じ
対象・射の宇宙へ持ち上げた。全単体と全作用素の次数射影、その射影で前合成した
元の加群 frame 図式、元の augmentation と実評価を保持する。
augmentation の各成分と図式の全作用素は、検証済みの元の擬同型である。
標的 Q は任意の元の通常 dg 加群であり、frame の各対象の半自由性は仮定しない。

通常加群図式とその自然変換の全 nerve 円柱を、元の同じ
`strictRawModuleSource` へ送る。各成分が擬同型なら、その同じ円柱の辺は
全関手圏で同型になる。元の辺と切断された辺の表示の照合は、小さい私有補題に分割した。
これは元の辺の可逆性の移送で、モデル構造や比較射の同値性を仮定に加えていない。

この同じ全 augmentation の逆と同じ実評価を合成して、指定模型内の全屋根を作る。
元の通常加群の指定された二つの頂点の定値図式へ端点を移し、元の全評価円柱を回収する
三角等式を保持する。単体ごとの π₀ の屋根への置換はしていない。
本節は M10 の既存比較の自然性・係数移送・単位/余単位の貼り合わせと証明の分割で、
一次 ID は追加しない。全宣言の型は以下のとおり。

`RawModuleTensorElementDiagram`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

abbrev strictRawModuleTensorElementIndex : Type (u + 1)

instance strictRawModuleTensorElementIndexCategory :
    Category.{u + 1} (strictRawModuleTensorElementIndex A X P Q)

def strictRawModuleTensorElementDegree :
    strictRawModuleTensorElementIndex A X P Q ⥤ SimplexCategory

def strictRawModuleTensorElementDiagram :
    strictRawModuleTensorElementIndex A X P Q ⥤ strictRawModuleCategory A X

def strictRawModuleTensorElementAugmentation :
    strictRawModuleTensorElementDiagram A X P Q ⟶
      (Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj
        ((strictRawModuleProbeFunctor A X).obj P)

def strictRawModuleTensorElementEvaluation :
    strictRawModuleTensorElementDiagram A X P Q ⟶
      (Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj Q

lemma strictRawModuleTensorElementAugmentation_weak (s : strictRawModuleTensorElementIndex A X P Q) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleTensorElementAugmentation A X P Q).app s)

lemma strictRawModuleTensorElementDiagram_map_weak
    {s t : strictRawModuleTensorElementIndex A X P Q} (f : s ⟶ t) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleTensorElementDiagram A X P Q).map f)
```

`RawModuleDiagramSource`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  {I : Type (u + 1)} [Category.{u + 1} I]
  {F G : I ⥤ strictRawModuleCategory A X}

def strictRawModuleDiagramSource (F : I ⥤ strictRawModuleCategory A X) :
    nerve I ⟶ strictModuleInfinity A X

private lemma mappedNerveEdge_invertible {C : Type (u + 1)} [Category.{u + 1} C]
    {Y : SSet.{u + 1}} (F : nerve C ⟶ Y) {c d : C} (f : c ⟶ d)
    (h : IsInvertibleEdge (X := Y)
      ((edgeOfSimplex (ComposableArrows.mk₁ f)).map ((truncation 2).map F))) :
    IsInvertibleEdge (((nerve.edgeMk f).map F).toTruncated)

lemma strictRawModuleSource_edge_weak {M N : strictRawModuleCategory A X} (f : M ⟶ N)
    (hf : moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) f) :
    IsInvertibleEdge
      (((nerve.edgeMk ((ULiftHom.up.{u, u + 1, u + 1}
        (C := strictRawModuleCategory A X)).map f)).map (strictRawModuleSource A X)).toTruncated)

def strictRawModuleDiagramNatTransHomotopy (η : F ⟶ G) :
    SSet.Homotopy (strictRawModuleDiagramSource A X F) (strictRawModuleDiagramSource A X G)

lemma strictRawModuleDiagramNatTransHomotopy_component (η : F ⟶ G) (i : I) :
    (simplicialHomotopyVertexEdge (strictRawModuleDiagramNatTransHomotopy A X η)
      (nerveVertex i)).edge =
    ((nerve.edgeMk ((ULiftHom.up.{u, u + 1, u + 1}
      (C := strictRawModuleCategory A X)).map (η.app i))).map (strictRawModuleSource A X)).edge

def strictRawModuleDiagramNatTransHom (η : F ⟶ G) :
    FunctorHom (strictRawModuleDiagramSource A X F) (strictRawModuleDiagramSource A X G)

def strictRawModuleDiagramNatTransIso (η : F ⟶ G)
    (hη : ∀ i, moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) (η.app i)) :
    FunctorIso (strictRawModuleDiagramSource A X F) (strictRawModuleDiagramSource A X G)

lemma strictRawModuleDiagramNatTransIso_hom (η : F ⟶ G)
    (hη : ∀ i, moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) (η.app i)) :
    (strictRawModuleDiagramNatTransIso A X η hη).hom =
      strictRawModuleDiagramNatTransHom A X η

lemma strictRawModuleDiagramSource_const (M : strictRawModuleCategory A X) :
    strictRawModuleDiagramSource A X ((Functor.const I).obj M) =
      SSet.const ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1}
          (C := strictRawModuleCategory A X)).obj M)))

def strictRawModuleDiagramSourceConstantIso (M : strictRawModuleCategory A X) :
    FunctorIso (strictRawModuleDiagramSource A X ((Functor.const I).obj M))
      (SSet.const ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1}
          (C := strictRawModuleCategory A X)).obj M))))
```

`RawModuleTensorElementSourceRoof`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementSourceAugmentationIso :
    FunctorIso
      (strictRawModuleDiagramSource A X (strictRawModuleTensorElementDiagram A X P Q))
      (strictRawModuleDiagramSource A X
        ((Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj
          ((strictRawModuleProbeFunctor A X).obj P)))

def strictRawModuleTensorElementSourceEvaluation :
    FunctorHom
      (strictRawModuleDiagramSource A X (strictRawModuleTensorElementDiagram A X P Q))
      (strictRawModuleDiagramSource A X
        ((Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj Q))

def strictRawModuleTensorElementSourceRoof :
    FunctorHom
      (strictRawModuleDiagramSource A X
        ((Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj
          ((strictRawModuleProbeFunctor A X).obj P)))
      (strictRawModuleDiagramSource A X
        ((Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj Q))

lemma strictRawModuleTensorElementSourceRoof_triangle :
    (strictRawModuleTensorElementSourceAugmentationIso A X P Q).hom ≫
      strictRawModuleTensorElementSourceRoof A X P Q =
        strictRawModuleTensorElementSourceEvaluation A X P Q

def strictRawModuleTensorElementSourceRoofFamily :
    ConstantFunctorHom (nerve (strictRawModuleTensorElementIndex A X P Q)) (strictModuleInfinity A X)
      ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj
          ((strictRawModuleProbeFunctor A X).obj P))))
      ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj Q)))

lemma strictRawModuleTensorElementSourceRoofFamily_triangle :
    ((strictRawModuleTensorElementSourceAugmentationIso A X P Q).hom ≫
      (strictRawModuleDiagramSourceConstantIso A X (I := strictRawModuleTensorElementIndex A X P Q)
        ((strictRawModuleProbeFunctor A X).obj P)).hom) ≫
          strictRawModuleTensorElementSourceRoofFamily A X P Q =
      strictRawModuleTensorElementSourceEvaluation A X P Q ≫
        (strictRawModuleDiagramSourceConstantIso A X (I := strictRawModuleTensorElementIndex A X P Q) Q).hom
```

対象ビルド・小さい監査の結果と実測は §39.1 に記録した。
同じ K の実 Hom 誘導射と、この全評価屋根を結ぶ正規化 dg 係数の全高次照合、
その射の同値性・K の完全忠実性は引き続き未完。
M10 の一般の native な辺・fiber と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 39.1 検証と実測

RawModuleTensorElementDiagram・RawModuleDiagramSource・RawModuleTensorElementSourceRoof
の通常の対象ビルドは成功した。新しい公開宣言 23 本の依存公理監査も成功し、
propext・Classical.choice・Quot.sound の範囲である。
指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は三ファイル、それぞれ 99・146・107 行、計 352 行、明示宣言 24 本
（private 1 本、名前つき instance 1 本を含む）。§38.1 の累計に加え、
検証済み累計は 77 ファイル・7,795 行・明示宣言 408 本（private 4 本）。
200 行を超える証明はない。一次 ID は追加していない。

元の全 frame Hom の要素圏、同じ全 augmentation と実評価、同じ源の全円柱と
その反転、指定定値端点への屋根と三角式まで検証した。
同じ K の実 Hom 誘導射との全高次照合・同値性・完全忠実性は未完であり、
M10 完了には数えない。M10 の一般の native な辺・fiber と全族、M11 以降、
G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 40. M10 の同じ普遍 dg Hom 族と全要素列の再添字（11-14）

§39 の全評価屋根に対して、元の tensor/Hom 同型の係数を保つ全普遍評価族を具体化する。
元の frame 射を Yoneda 同値で同じ代表可能族へ送り、§36 の同じ二変数 Dold–Kan 同型を
後合成する。標的射との後合成則、全単体作用素との再添字則を保持し、元の恒等射を
代入した普遍族の評価式と全作用素自然性を得る。

その普遍族を、同じ反対要素圏の全通常単体列の終端パラメータで前合成する。
元の評価自然変換の終端成分との合成式を保持する。
再添字は終端を変える作用素も含み、列の元の末尾射による dg Hom の作用と厳密に整合する。
frame の係数加群を半自由と仮定せず、元の全通常 dg 加群圏内で構成する。

本節は M10 の既存 tensor/Hom 構成の自然性・係数移送・恒等・合成則と証明の分割であり、
一次 ID は追加しない。全宣言の型は以下のとおり。

`TensorHomUniversal.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleTensorHomRepresentable (P N : ModuleCategory A D) (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    stdSimplex.obj n ⟶ (cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P)).obj N

lemma moduleTensorHomRepresentable_postcomp (P : ModuleCategory A D)
    {N N' : ModuleCategory A D} (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) (h : N ⟶ N') :
    moduleTensorHomRepresentable A D P N n g ≫
      (cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P)).map h =
        moduleTensorHomRepresentable A D P N' n (g ≫ h)

lemma moduleTensorHomRepresentable_reindex (P N : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj m ⟶ N) :
    stdSimplex.map f ≫ moduleTensorHomRepresentable A D P N m g =
      moduleTensorHomRepresentable A D P N n
        (((moduleTensorSimplicesFunctor A D).obj P).map f ≫ g)

def moduleTensorHomDoldKanSimplex (P N : ModuleCategory A D) (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    stdSimplex.obj n ⟶ ((moduleDoldKanHomBifunctor A D).obj (op P)).obj N

lemma moduleTensorHomDoldKanSimplex_postcomp (P : ModuleCategory A D)
    {N N' : ModuleCategory A D} (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) (h : N ⟶ N') :
    moduleTensorHomDoldKanSimplex A D P N n g ≫
      ((moduleDoldKanHomBifunctor A D).obj (op P)).map h =
        moduleTensorHomDoldKanSimplex A D P N' n (g ≫ h)

lemma moduleTensorHomDoldKanSimplex_reindex (P N : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj m ⟶ N) :
    stdSimplex.map f ≫ moduleTensorHomDoldKanSimplex A D P N m g =
      moduleTensorHomDoldKanSimplex A D P N n
        (((moduleTensorSimplicesFunctor A D).obj P).map f ≫ g)

def moduleTensorUniversalDoldKanSimplex (P : ModuleCategory A D) (n : SimplexCategory) :
    stdSimplex.obj n ⟶ ((moduleDoldKanHomBifunctor A D).obj (op P)).obj
      (((moduleTensorSimplicesFunctor A D).obj P).obj n)

lemma moduleTensorUniversalDoldKanSimplex_evaluation (P N : ModuleCategory A D)
    (n : SimplexCategory) (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    moduleTensorUniversalDoldKanSimplex A D P n ≫
      ((moduleDoldKanHomBifunctor A D).obj (op P)).map g =
        moduleTensorHomDoldKanSimplex A D P N n g

lemma moduleTensorUniversalDoldKanSimplex_naturality (P : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m) :
    stdSimplex.map f ≫ moduleTensorUniversalDoldKanSimplex A D P m =
      moduleTensorUniversalDoldKanSimplex A D P n ≫
        ((moduleDoldKanHomBifunctor A D).obj (op P)).map
          (((moduleTensorSimplicesFunctor A D).obj P).map f)
```

`RawModuleTensorElementUniversal.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

abbrev strictRawModuleTensorElementTerminalParameter {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    ⦋n⦌ ⟶ (strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n))

def strictRawModuleTensorElementUniversalFamily {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    SSet.stdSimplex.obj ⦋n⦌ ⟶
      ((strictRawModuleProbeDoldKanHom A X).obj (op P)).obj
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)))

lemma strictRawModuleTensorElementUniversalFamily_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorElementUniversalFamily A X P Q c ≫
      ((strictRawModuleProbeDoldKanHom A X).obj (op P)).map
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n))) =
    SSet.stdSimplex.map (strictRawModuleTensorElementTerminalParameter A X P Q c) ≫
      moduleTensorHomDoldKanSimplex A (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P) Q
        ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n)))
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))

lemma strictRawModuleTensorElementUniversalFamily_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    SSet.stdSimplex.map θ ≫ strictRawModuleTensorElementUniversalFamily A X P Q c =
      strictRawModuleTensorElementUniversalFamily A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      ((strictRawModuleProbeDoldKanHom A X).obj (op P)).map
        ((strictRawModuleTensorElementDiagram A X P Q).map
          (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))
```

対象ビルド・小さい監査の結果と実測は §40.1 に記録した。
ここでは全高次の普遍評価とその自然性を保持するが、元の dg nerve の全 cone/prism 方程式、
§39 の同じ屋根との比較、同じ K の実 Hom 誘導射の同値性・完全忠実性は未完である。
M10 の一般の native な辺・fiber と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 40.1 検証と実測

TensorHomUniversal・RawModuleTensorElementUniversal の通常の対象ビルドは成功した。
新しい公開宣言 13 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は二ファイル、それぞれ 128・96 行、計 224 行、公開宣言 13 本。
§39.1 の累計に加え、検証済み累計は 79 ファイル・8,019 行・明示宣言 421 本
（private 4 本）。200 行を超える証明はない。一次 ID は追加していない。

同じ tensor/Hom 二関手の元の射からの全代表可能族、全後合成・再添字、
恒等射による普遍族と全評価、同じ全要素列の終端パラメータによる前合成、
終端を変える作用素も含む再添字式まで検証した。
次はこの同じ全族を元の全通常 dg 加群の pinched Hom の線形成分へ送り、
元の dg nerve 内の全 cone/prism と同じ実評価屋根を照合する。
既存の `doldKanHomPinchedIso`・任意 Hom 鎖写像への自然性・
`SimplexTerminalParameter.reindex` と一般の単射方程式移送を使う。
ComplexLimits の既存ファイルは読み取りだけに留め、既存の構成を置き換えない。

同じ K の実 Hom 誘導射の全高次照合・同値性・完全忠実性、M10 の一般の native な辺・fiber と
全族は未完。M11 以降と G12 の元の目標を維持し、約 8,500 行での途中見積りを予定する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 41. M10 の元の全 pinched 評価・線形成分・選択 cochain（11-14）

§40 の同じ実 Dold–Kan 族を、元の全通常 dg 加群の dg nerve の pinched Hom へ移す。
既存の `doldKanHomPinchedIso` と任意 Hom 鎖写像への自然性を使い、
同じ標的加群射による後合成、全単体作用素、恒等射による普遍族と実評価を保持する。
係数 dg 圏の対象宇宙 v と環の宇宙 u を区別し、実加群対象宇宙
`max (u + 1) v` へ持ち上げる。BE の一対象 dg 圏では v = 0 である。
係数加群の半自由性も比較射の同値性も、引数の仮定に加えない。

同じ全要素列の終端パラメータで普遍 pinched 族を前合成し、実評価・全再添字を保つ。
同じ恒等単体で評価した実単体を、既存の `PinchedHom.toLinearSimplex` で元の線形成分へ送る。
全有限部分集合・正しい次数の微分方程式、終端を変える全作用素の線形再添字、
単射による像部分集合の成分式、非単射による退化成分の零を保持する。

元の有限部分集合を昇順に選び、同じ制限列の最上位 cochain を取る。
元の末尾射で送ると元の部分集合の成分に戻ることを同じ単射再添字式で照合し、
同じ最大元への型の移送を保持する。
これは M10 の既存比較の係数移送・自然性・恒等・合成則と証明の分割で、一次 ID は追加しない。
各証明は 200 行以下。全宣言の型は以下のとおり。

`TensorHomPinched.lean`：

```lean
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleDoldKanPinchedIso (P N : ModuleCategory A D) :
    SSet.uliftFunctor.{max (u + 1) v, u}.obj
      (((moduleDoldKanHomBifunctor A D).obj (op P)).obj N) ≅
    PinchedHom.pinchedHom A (RightModule A D)
      (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)

lemma moduleDoldKanPinchedIso_postcomp (P : ModuleCategory A D)
    {N N' : ModuleCategory A D} (h : N ⟶ N') :
    SSet.uliftFunctor.{max (u + 1) v, u}.map
      (((moduleDoldKanHomBifunctor A D).obj (op P)).map h) ≫
        (moduleDoldKanPinchedIso A D P N').hom =
    (moduleDoldKanPinchedIso A D P N).hom ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P h)

def moduleTensorHomPinchedSimplex (P N : ModuleCategory A D) (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    SSet.uliftFunctor.{max (u + 1) v, u}.obj (SSet.stdSimplex.obj n) ⟶
    PinchedHom.pinchedHom A (RightModule A D)
      (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)

lemma moduleTensorHomPinchedSimplex_postcomp (P : ModuleCategory A D)
    {N N' : ModuleCategory A D} (n : SimplexCategory)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) (h : N ⟶ N') :
    moduleTensorHomPinchedSimplex A D P N n g ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P h) =
        moduleTensorHomPinchedSimplex A D P N' n (g ≫ h)

lemma moduleTensorHomPinchedSimplex_reindex (P N : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m)
    (g : ((moduleTensorSimplicesFunctor A D).obj P).obj m ⟶ N) :
    SSet.uliftFunctor.{max (u + 1) v, u}.map (SSet.stdSimplex.map f) ≫
      moduleTensorHomPinchedSimplex A D P N m g =
    moduleTensorHomPinchedSimplex A D P N n
      (((moduleTensorSimplicesFunctor A D).obj P).map f ≫ g)

def moduleTensorUniversalPinchedSimplex (P : ModuleCategory A D) (n : SimplexCategory) :
    SSet.uliftFunctor.{max (u + 1) v, u}.obj (SSet.stdSimplex.obj n) ⟶
    PinchedHom.pinchedHom A (RightModule A D) (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) (((moduleTensorSimplicesFunctor A D).obj P).obj n))

lemma moduleTensorUniversalPinchedSimplex_evaluation (P N : ModuleCategory A D)
    (n : SimplexCategory) (g : ((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) :
    moduleTensorUniversalPinchedSimplex A D P n ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P g) =
        moduleTensorHomPinchedSimplex A D P N n g

lemma moduleTensorUniversalPinchedSimplex_naturality (P : ModuleCategory A D)
    {n m : SimplexCategory} (f : n ⟶ m) :
    SSet.uliftFunctor.{max (u + 1) v, u}.map (SSet.stdSimplex.map f) ≫
      moduleTensorUniversalPinchedSimplex A D P m =
    moduleTensorUniversalPinchedSimplex A D P n ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) P
        (((moduleTensorSimplicesFunctor A D).obj P).map f))
```

`RawModuleTensorElementPinched.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementPinchedFamily {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u}) ⟶
      PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
        (ForgetEnrichment.to (Complex A)
          ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n))))

lemma strictRawModuleTensorElementPinchedFamily_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorElementPinchedFamily A X P Q c ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))) =
    SSet.uliftFunctor.{u + 1, u}.map
      (SSet.stdSimplex.map (strictRawModuleTensorElementTerminalParameter A X P Q c)) ≫
      moduleTensorHomPinchedSimplex A (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P) Q
        ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n)))
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))

lemma strictRawModuleTensorElementPinchedFamily_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    SSet.uliftFunctor.{u + 1, u}.map (SSet.stdSimplex.map θ) ≫
      strictRawModuleTensorElementPinchedFamily A X P Q c =
    strictRawModuleTensorElementPinchedFamily A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
    pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))))

def strictRawModuleTensorElementPinchedSimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n))))) _⦋n⦌

lemma strictRawModuleTensorElementPinchedSimplex_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n))))).map θ.op
      (strictRawModuleTensorElementPinchedSimplex A X P Q c) =
    (pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))))).app (op ⦋m⦌)
      (strictRawModuleTensorElementPinchedSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c))
```

`RawModuleTensorElementLinear.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementLinear {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    LinearSimplex A
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)))) n

lemma strictRawModuleTensorElementLinear_equation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    differential A ((strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk) =
      (strictRawModuleTensorElementLinear A X P Q c).val.rhs J k hk

lemma strictRawModuleTensorElementLinear_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    LinearSimplex.pullback θ.toOrderHom (strictRawModuleTensorElementLinear A X P Q c) =
    pinchedLinearSimplexMap
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementDiagram A X P Q).map
          (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))))
      (strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c))

lemma strictRawModuleTensorElementLinear_component_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).f k
      ((strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component J k hJ hk) =
    LinearData.component (pullback θ.toOrderHom
      (strictRawModuleTensorElementLinear A X P Q c).val) J k hJ hk

lemma strictRawModuleTensorElementLinear_component_inj {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).f k
      ((strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component J k hJ hk) =
    (strictRawModuleTensorElementLinear A X P Q c).val.component (J.image θ.toOrderHom) k
      (hJ.image θ.toOrderHom) (by rw [Finset.card_image_of_injOn hi]; exact hk)

lemma strictRawModuleTensorElementLinear_component_not_inj {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hi : ¬ Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))).f k
      ((strictRawModuleTensorElementLinear A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)).val.component J k hJ hk) = 0
```

`RawModuleTensorElementSelected.lean`：

```lean
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

abbrev strictRawModuleTensorElementSelection {n : ℕ} (J : Finset (Fin (n + 1)))
    (hJ : J.Nonempty) : ⦋J.card - 1⦌ ⟶ ⦋n⦌

lemma strictRawModuleTensorElementSelection_last {n : ℕ} (J : Finset (Fin (n + 1)))
    (hJ : J.Nonempty) :
    (strictRawModuleTensorElementSelection J hJ).toOrderHom (Fin.last (J.card - 1)) =
      J.max' hJ

def strictRawModuleTensorElementSelectedCochain {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom A
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleTensorElementDiagram A X P Q).obj
        (c.obj ((strictRawModuleTensorElementSelection J hJ).toOrderHom
          (Fin.last (J.card - 1)))))) k

lemma strictRawModuleTensorElementSelectedCochain_image {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last ((strictRawModuleTensorElementSelection J hJ).toOrderHom
          (Fin.last (J.card - 1)))))))).f k
      (strictRawModuleTensorElementSelectedCochain A X P Q c J k hJ hk) =
    (strictRawModuleTensorElementLinear A X P Q c).val.component J k hJ hk

def strictRawModuleTensorElementSelectedCochainAtMax {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    GradedHom A
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (J.max' hJ)))) k
```

対象ビルド・小さい監査の結果と実測は §41.1 に記録した。
同じ全 cochain を元の dg nerve の cone/prism へ組み立てる全方程式、元の全評価屋根との
三角比較、同じ K の Hom 誘導射の同値性・完全忠実性はまだ完了としていない。
M10 の一般の native な辺・fiber と全族、M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


### 41.1 検証と実測

TensorHomPinched・RawModuleTensorElementPinched・RawModuleTensorElementLinear・
RawModuleTensorElementSelected の通常の対象ビルドは成功した。
新しい公開宣言 24 本の依存公理監査も成功し、propext・Classical.choice・Quot.sound
の範囲である。指定の impl 鍵と一回 280 秒の塊で実行した。引用属性の新規追加はない。

新規 Lean は四ファイル、それぞれ 126・134・124・97 行、計 481 行、公開宣言 24 本。
§40.1 の累計に加え、検証済み累計は 83 ファイル・8,500 行・明示宣言 445 本
（private 4 本）。200 行を超える証明はない。一次 ID は追加していない。
全係数の pinched Hom の同じ実評価、全再添字、線形成分・全微分方程式、
単射/非単射の成分式、選択した cochain と元の最大元への移送を検証した。

同じ全 cone/prism と元の屋根の比較、同じ K の実 Hom 射の同値性・完全忠実性、
指定 fiber・一般の native な辺と全族は未完。M11 以降と G12 の元の目標を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。


## 42. 約 8,500 行の途中報告と残作業の見積り更新（11-14）

ユーザーの「約 8,500 行で止まらずに途中報告」に従う。
§41 の四ファイルは通常の対象ビルドが通過し、§40.1 の 8,019 行に 481 行を加えると
新設 Lean は 83 ファイル・8,500 行となる。既存の対象を変更した差分を別に隠す数え方はせず、
現作業木の M15 所有ソースも同じ合計になることを確認した。
小さい監査も成功し、確定結果は §41.1 に記録した。

M01–M09 と追加 N01 が完了。M19 の共通 IsThick の芯とその閉包の法則は作成済みだが、
同じ native 相対テンソルへの接続が残るため M19 完了には数えない。
M10 は全圏・通常の全評価・厳密制限と随伴・同じ局所化比較 K、実モデル構造、
frame 比較、元の dg Hom の全自然な同定を進めた段階である。
元の K の完全忠実性、指定 native fiber、一般の底の辺の輸送と全族の検収は未完。

段 0 の M06–M10 の 1,000〜1,800 行は、そのまま完成見込みに流用できない。
実際の projective モデル構造 N01、異なる模型の Hom 比較、同じ誘導射との全高次の
照合を個々に検収する費用が必要だった。以下は現時点の残りの**暫定作業見積り**であり、
未実装の定理の存在や上端以内の完成を保証するものではない。
M10 の幅は既存 FrameHom と一般の線形・方程式移送 API の再利用を前提とする。

| 残りの束 | 追加行数の下端 | 追加行数の上端 | 未完の主な検収 |
| --- | ---: | ---: | --- |
| M10 | 1,500 | 3,000 | 同じ全 cone/prism と K の Hom 射の照合、完全忠実性、fiber と一般輸送・全族 |
| M11–M15 | 1,800 | 2,800 | 同じ fiber の対称 operadic 相対テンソル、全構造・完全性・底変換 |
| M16–M20 | 450 | 850 | 指定単位辺と fiber・指数射、単位底比較、共通 thick との接続 |
| M21–M27 | 900 | 1,500 | 指数判定・底変換・合成・テンソル |
| M28–M30 | 600 | 1,000 | Amitsur 塔と同じ指定増大の降下 |
| M31–M35 | 500 | 800 | 同じ RHom 全関手・評価・指数二判定 |
| M36–M42 | 700 | 1,200 | 実際の完備反射・完備テンソルと同じ評価・利用側接続 |
| **残り合計** | **6,450** | **11,150** | |
| **8,500 行との合計** | **14,950** | **19,650** | |

したがって外枠 17,000 行以内の完成は、現時点では確証がない。
外枠を変更せず、既存構成の再利用と法則の共通化を進める。
Ho や離散な対象族への弱化、モデル構造・完備反射の仮定化、任意 E への範囲拡大はしない。
今回の途中報告点では停止せず、新しい一次構成・新しい定理・まとまりの外への拡張が必要に
なった時、または実際に外枠へ達した時に、共通規則どおり報告して止まる。
G12 は M15 完成後の元の段 0 と検収条件を維持する。

**一覧：済み 10／全体 43（うち追加 1）**。



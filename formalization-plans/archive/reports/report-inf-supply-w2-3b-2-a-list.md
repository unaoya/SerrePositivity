# IS-W2 の報告（report-inf-supply-w2.md） — 3b-2 の型つき一覧 A01〜A12・B01〜B02（§73〜§112、2026-11-13〜11-14）

元の報告：[report-inf-supply-w2.md](../../stage-ii/inf-supply-b/report-inf-supply-w2.md)

## 73. 3b-2 再開：型つきの残補題一覧（11-13、ユーザー承認）

§72の中間停止を解除する。今回の指示により、停止条件は下記一覧の外の新しい数学と外枠12,500行。現在141本8,834行。既存構成の照合だけの追加は3本までとし、追加時はこの報告に型を書く。下記は紙の宣言案で、証明済み・Leanで全体を elaboration 済みという意味ではない。名前空間の省略・局所略記を以下に固定する。単なる存在や零単体で代用せず、指定射・全単体・全図式射を結論に含める。実装中に型の意味を変更する必要が判明した場合も、その変更を黙って行わない。

### 73.1 共通の記法と第一のまとまり（A01〜A12）

この節では DiagramComparison、CategoryTheory、MonoidalCategory、CosimplicialHom の名前を開く。`A : Type u`、`[CommRing A]`、`J : Type u`、`[SmallCategory J]`、`W : J ⥤ SSet.{u}`、`Q : J ⥤ CochainComplex (ModuleCat A) ℤ`、`φ : simplicialRingCoefficient.{u} →+* A`。以下の略記は型を短く書くためだけのもの。

```lean
local notation "D" => J ⥤ CochainComplex (ModuleCat A) ℤ
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)
local notation "P" => standardParameterForCoefficients A J
local notation "N" => freeNegativeChainsDiagramFunctor A J
local notation "FP" => freeProductFrame A W P
local notation "FT" => freeTensorFrame A W P
local notation "AW" => freeProductFrameAW A W P φ
local notation "SH" => freeProductFrameShuffle A W P φ
local notation "NP" => P ⋙ N
local notation "Γ" => truncatedDoldKanFunctor A
```

A01は既存の図式 EZ 同値の指定射を取り出す。添字を後で `SimplexCategory × J` として使い、点ごとの存在を選び直さない。

```lean
-- A01a,b：任意の添字図式 X,Y について。AW・shuffle は既存の指定射。
def freeProductDiagramAWShuffleHomotopy (X Y : J ⥤ SSet.{u}) :
  Homotopy
    ((E).map (freeProductDiagramAW φ X Y ≫ freeProductDiagramShuffle φ X Y))
    (𝟙 ((E).obj (N.obj (X ⊗ Y))))
def freeProductDiagramShuffleAWHomotopy (X Y : J ⥤ SSet.{u}) :
  Homotopy
    ((E).map (freeProductDiagramShuffle φ X Y ≫ freeProductDiagramAW φ X Y))
    (𝟙 ((E).obj (N.obj X ⊗ N.obj Y)))

-- A02：余単体方向と J 方向を同時に含む鎖ホモトピー。
-- EE は Δ ⥤ D を、Δ ⥤ J ⥤ ModuleCat A 値の複体へ交換する関手。
-- 具体的に whiskeringRight Δ D (CochainComplex (J ⥤ ModuleCat A) ℤ)
-- の E 像の後に functorToComplexOfFunctors Δ (J ⥤ ModuleCat A) (.up ℤ)。
def freeProductFrameAWShuffleHomotopy :
  Homotopy (EE.map (AW ≫ SH)) (𝟙 (EE.obj FP))
def freeProductFrameShuffleAWHomotopy :
  Homotopy (EE.map (SH ≫ AW)) (𝟙 (EE.obj FT))

-- A03：正規化された単体の増大写像。全単体で自然な ε。
def standardParameterAugmentation : NP ⟶ 𝟙_ (SimplexCategory ⥤ D)

-- A04：両 frame のパラメータ余作用。
def productFrameCoaction : FP ⟶ FP ⊗ NP
def tensorFrameCoaction : FT ⟶ FT ⊗ NP
-- productFrameCoaction.app n は既存 freeProductParameterCoaction φ W (P.obj n)。
-- tensorFrameCoaction は第二因子の対角 AW と associator によるもの。

-- A05：単位則。δ の名前を上の二つにそれぞれ固定した二宣言。
theorem productFrameCoaction_counit :
  productFrameCoaction ≫ (𝟙 FP ⊗ₘ standardParameterAugmentation) ≫
    (ρ_ FP).hom = 𝟙 FP
theorem tensorFrameCoaction_counit :
  tensorFrameCoaction ≫ (𝟙 FT ⊗ₘ standardParameterAugmentation) ≫
    (ρ_ FT).hom = 𝟙 FT
```

A06〜A08は鎖ホモトピーから単体的ホモトピーへの具体的接続。単なる各 n の鎖ホモトピー同値から空間の同値性を主張しない。

```lean
-- I := N.obj ((Functor.const J).obj (Δ[1] : SSet.{u}))。
-- endpoint ε は正規化した 0→1 または 1→1 の頂点と Δ[0] の単位同型で定義。
def normalizedIntervalEndpoint (ε : Fin 2) : 𝟙_ D ⟶ I

-- A06：同じ鎖ホモトピーの区間による評価。R,S : D。
def normalizedIntervalHom (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) : R ⊗ I ⟶ S
theorem normalizedIntervalHom_endpoints (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
  (ρ_ R).inv ≫ (𝟙 R ⊗ₘ normalizedIntervalEndpoint 0) ≫
      normalizedIntervalHom f g h = f ∧
  (ρ_ R).inv ≫ (𝟙 R ⊗ₘ normalizedIntervalEndpoint 1) ≫
      normalizedIntervalHom f g h = g
-- 自然性も必要：a:R'→R,b:S→S'。h' は h を E.map a,b で前後合成したもの。
theorem normalizedIntervalHom_naturality
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
  (a ⊗ₘ 𝟙 I) ≫ normalizedIntervalHom f g h ≫ b =
    normalizedIntervalHom (a ≫ f ≫ b) (a ≫ g ≫ b) h'

-- A07：F,G : Δ ⥤ D。δ の自然性は NatTrans の型に含む。
def frameHomHomotopyOfChainHomotopy (F G : SimplexCategory ⥤ D)
    (δ : F ⟶ F ⊗ NP)
    (hδ : δ ≫ (𝟙 F ⊗ₘ standardParameterAugmentation) ≫ (ρ_ F).hom = 𝟙 F)
    (f g : F ⟶ G) (h : Homotopy (EE.map f) (EE.map g)) (Q : D) :
  SSet.Homotopy ((cosimplicialHomMap f).app Q) ((cosimplicialHomMap g).app Q)

-- A08：指定二射の両合成のホモトピー（Q に関する NatTrans の成分）。
def freeProductHomComparison_homotopy (Q : D) :
  SSet.Homotopy
    ((freeProductHomReverse A W P φ).app Q ≫
      (freeProductHomComparison A W P φ).app Q) (𝟙 _)
def freeProductHomReverse_homotopy (Q : D) :
  SSet.Homotopy
    ((freeProductHomComparison A W P φ).app Q ≫
      (freeProductHomReverse A W P φ).app Q) (𝟙 _)

-- A09：元の指定比較そのものの同値性。
theorem normalizedWeightSectionMap_equivalence :
  IsSimplicialHomotopyEquivalence (normalizedWeightSectionMap A W Q φ)
```

A10〜A12は同じ指定 Hom 比較の自然性と、BK の持ち上げ・反転への接続。後者の照合を新しい数学として数え直さないため初めから一覧に含める。

```lean
-- A10：Q の全射で可換。Hmap f は Γ.map (図式 linearHom の後合成 f)。
-- Smap f は weightedSectionsFunctor W が Q⋙Γ の全射を写したもの。
theorem normalizedWeightSectionMap_naturality (f : Q ⟶ Q') :
  Hmap f ≫ normalizedWeightSectionMap A W Q' φ =
    normalizedWeightSectionMap A W Q φ ≫ Smap f
-- A11：重みの全射 w:W'→W による前合成。Hpre,Spre はそれぞれ
-- 図式 linearHom と weightedSections の指定前合成（新しい選択ではない）。
theorem normalizedWeightSectionMap_weight_naturality (w : W' ⟶ W) :
  Hpre w ≫ normalizedWeightSectionMap A W' Q φ =
    normalizedWeightSectionMap A W Q φ ≫ Spre w

-- A12：X : CosimplicialObject (Complex A)、T : Complex A。
-- HΓ := Γ.obj (normalizedBousfieldKanHom ((homDiagramFunctor T).obj X))。
-- F := liftedClosedDiagram X、t := ForgetEnrichment.of (Complex A) T。
-- Hol := bousfieldKanHolim (simplicialHomDiagram F t ⋙ SSet.opFunctor)。
def normalizedBKReflectedSectionsMap (X : CosimplicialObject (Complex A))
    (T : Complex A) : HΓ.op ⟶ Hol
theorem normalizedBKReflectedSectionsMap_equivalence (X) (T) :
  IsSimplicialHomotopyEquivalence (normalizedBKReflectedSectionsMap X T)
```

A12の射はA09の射に、既存の二重 opposite・AsSmall・ULift・Γ Hom 同型を順に合成する。任意の同値を選んで型だけ合わせることは禁止。反転と持ち上げの各交換はこのA12の構成内で明示する。

### 73.2 第二のまとまり：指定豊穣 Hom と native 極限性（B01〜B08）

`X : CosimplicialObject (Complex A)`、`F := liftedClosedDiagram X`、`z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)`、`φX := liftedEnrichedBousfieldKanCone X`、`c := nativeCoherentCone X`、`hz := nativeCoherentCone_vertex X`。`C := ClosedCategory A (Complex A)`。`U := SSet.uliftFunctor.{u+1,u}`。`x : C` を全試験対象とする。`q x := reflectedWeightedHomComparison F z φX x`。

```lean
-- B01：実 Hom 同型、既存 Hom–Tot 比較、A12 を合成した指定射。
def gammaReflectedBKComparison (X) (x : C) :
  (SimplicialCategory.sHom x z).op ⟶
    bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor)
-- B02：実豊穣合成との等式。型だけの同値で代用しない。
theorem gammaReflectedBKComparison_eq (X) (x : C) :
  gammaReflectedBKComparison X x = q x
-- B03：同じ指定射の同値性。
theorem reflectedBKComparison_equivalence (X) (x : C) :
  IsSimplicialHomotopyEquivalence (q x)

-- B04：coherentCone_isLimit_of_family_lifts の a。
def nativeTotConeFamilyLift (X) (x : C) :
  U.obj (SimplicialCategory.sHom x z).op ⟶
    coherentConeSectionSpace c.val (coherentNerveVertex x)
-- B05：同定 ha（頂点の同じ実比較）。
theorem nativeTotConeFamilyLift_apex (X) (x : C) :
  nativeTotConeFamilyLift X x ≫ coherentConeApexEvaluation c z hz x =
    coherentCosliceFiberComparison x z
-- B06：制限の同定。右辺は既存の全 BK→native 比較との合成。
theorem nativeTotConeFamilyLift_restriction (X) (x : C) :
  nativeTotConeFamilyLift X x ≫ coneSectionRestriction c (coherentNerveVertex x) =
    U.map (q x) ≫ reflectedHomHolimConeComparison F x
-- B07：he。一般の reflectedHomHolimConeComparison の既存同値性を再利用。
theorem nativeTotConeFamilyLift_equivalence (X) (x : C) :
  IsSimplicialHomotopyEquivalence
    (nativeTotConeFamilyLift X x ≫ coneSectionRestriction c (coherentNerveVertex x))
-- B08：元の指定錐の native 極限性。
theorem nativeCoherentCone_isLimit (X) : IsLimitCone (nativeCoherentCone X)
theorem nativeDGCone_isLimit (X) : IsLimitCone (nativeDGCone X)
```

B04で別の錐を選ばず、指定余錐の合成の全単体を切断へ送る。B06の右辺の同値性だけを証明してB04・B05を省くことはしない。

### 73.3 第三のまとまり：標準脚と D(A) 輸送（C01〜C07）

以下 `K := (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))`、`R := complexSemifreeResolutionInfinity A`、`DA := derivedInfinityCategory A`。`v n` は K の n の指定頂点（AsSmall・ULift による像）。`standardLeg X n` は `standardZeroLeg A X ≫ X.map (SimplexCategory.const _ _ 0)` という、頂点0を選ぶ標準脚。最後の定数射の実API名は実装時に合わせるが、0以外を選ぶ仕様には変えない。

```lean
-- C01：raw dg 錐の全脚の実一次単体。edgeMk は閉射の dg 辺。
theorem nativeDGCone_standardLeg (X) (n : SimplexCategory) :
  (derivedConeLeg (nativeDGCone X) (v n)).edge =
    (dgClosedEdge A (Complex A) ((complexToClosed A).map (standardLeg X n))).edge
-- C02：R による同じ実錐の輸送（raw 極限性から、既存の出力分解判定を適用）。
def nativeDerivedDiagram (X) : K ⟶ DA := nativeDGDiagram X ≫ R
def nativeDerivedCone (X) : JoinCone (nativeDerivedDiagram X) :=
  mapJoinCone R (nativeDGCone X)
theorem nativeDerivedCone_isLimit (X) : IsLimitCone (nativeDerivedCone X)
-- C03：元の Tot の指定分解を頂点とする。
theorem nativeDerivedCone_vertex (X) :
  (nativeDerivedCone X).vertex =
    R.app (Opposite.op ⦋0⦌) (Simplex.vertex ((productTotalFunctor A).obj X))
-- C04：同じ標準脚を輸送する。
theorem nativeDerivedCone_standardLeg (X) (n) :
  (derivedConeLeg (nativeDerivedCone X) (v n)).edge =
    R.app (Opposite.op ⦋1⦌)
      (dgClosedEdge A (Complex A) ((complexToClosed A).map (standardLeg X n))).edge
-- C05：nativeDGDiagram の元の strict 図式との照合。
-- kappa : K ≅ (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)
-- は AsSmall と ULift の既存指定同型。
theorem nativeDerivedDiagram_strict (X) :
  nativeDerivedDiagram X = kappa.hom ≫
    (SSet.uliftFunctor.{u+1,0}).map (nerveMap X) ≫ complexOrdinaryDerivedSource A
-- C06：kappa で引き戻した元の図式上の指定錐とその極限性。
def strictDerivedTotCone (X) :
  JoinCone ((SSet.uliftFunctor.{u+1,0}).map (nerveMap X) ≫ complexOrdinaryDerivedSource A)
theorem strictDerivedTotCone_isLimit (X) : IsLimitCone (strictDerivedTotCone X)
-- C07：全 join 射を保持する輸送の式（脚だけの同定ではない）。
theorem strictDerivedTotCone_pullback (X) :
  joinMap (𝟙 Δ[0]) kappa.hom ≫ (strictDerivedTotCone X).val =
    (nativeDerivedCone X).val
```

C05の universe の表記は実ソース X の対象宇宙と hom 宇宙を区別して elaboration 時に固定する。普通の図式を無関係な図式同型で置換する内容ではない。もし厳密等式が成立せず指定 FunctorIso による輸送が必要であれば、型の変更として報告する。

### 73.4 第四のまとまり：全図式射・指定錐の族・離散入口（D01〜D08）

`B := nerve (CosimplicialObject (Complex A))`、`K₀ := (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)`、`jX : Δ[0] ⟶ B := SSet.yonedaEquiv.symm (nerveVertex X)`。`evalFamily : K₀ ⊗ B ⟶ DA` は評価関手 `(n,X) ↦ X.obj n` の nerve と積・ULift の既存同型、`complexOrdinaryDerivedSource A` の合成。`totFamily : B ⟶ DA := nerveMap (productTotalFunctor A) ≫ complexOrdinaryDerivedSource A`。

```lean
-- D01：同じ指定全錐の全パラメータ族。
def derivedTotConeFamily : (join (Δ[0] : SSet.{u+1}) K₀) ⊗ B ⟶ DA
-- D02：両端を全パラメータで固定する。
theorem derivedTotConeFamily_boundaries :
  (joinInl Δ[0] K₀ ⊗ₘ 𝟙 B) ≫ derivedTotConeFamily =
      (λ_ B).hom ≫ totFamily ∧
  (joinInr Δ[0] K₀ ⊗ₘ 𝟙 B) ≫ derivedTotConeFamily = evalFamily
-- D03：各点で同じ全高次単体の錐へ戻る。
theorem derivedTotConeFamily_at (X) :
  (ρ_ (join Δ[0] K₀)).inv ≫ (𝟙 _ ⊗ₘ jX) ≫ derivedTotConeFamily =
    (strictDerivedTotCone X).val
-- D04：図式射に対応する族の頂点辺は productTotalFunctor.map f の像そのもの。
theorem derivedTotConeFamily_map {X Y} (f : X ⟶ Y) :
  totFamily.app (Opposite.op ⦋1⦌) (nerve.edgeMk f).edge =
    (complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk ((productTotalFunctor A).map f)).edge
```

D01の単体的射の型が全パラメータの単体作用素・合成も含む。D04だけを証明して族の代わりにしない。離散化では既存 `discreteTotalCochainNatIso` の成分を使い、交代余面複体を頂点とする同じ錐を輸送する。

```lean
-- M : CosimplicialObject (ModuleCat.{u} A)。
-- disc := discreteDiagramFunctor A、Coch := discreteCochainFunctor A。
-- discreteModuleSource := nerveMap (HomologicalComplex.single _ (.up ℤ) 0)
--   ≫ complexOrdinaryDerivedSource A（必要な宇宙同型は固定）。
-- D05：離散加群版の指定錐。
def cosimplicialModuleCone (M) :
  JoinCone ((SSet.uliftFunctor.{u+1,0}).map (nerveMap M) ≫ discreteModuleSource)
theorem cosimplicialModuleCone_isLimit (M) : IsLimitCone (cosimplicialModuleCone M)
-- D06：頂点は同じ交代余面複体の像。
theorem cosimplicialModuleCone_vertex (M) :
  (cosimplicialModuleCone M).vertex =
    (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (Coch.obj M))
-- D07：離散入力についても全図式射・全高次単体を保持する錐族。
-- Bm := nerve (CosimplicialObject (ModuleCat.{u} A))。
def cosimplicialModuleConeFamily : (join (Δ[0] : SSet.{u+1}) K₀) ⊗ Bm ⟶ DA
theorem cosimplicialModuleConeFamily_at (M) :
  (ρ_ (join Δ[0] K₀)).inv ≫
    (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex M)) ≫ cosimplicialModuleConeFamily =
      (cosimplicialModuleCone M).val
-- 境界は D02 の evalFamily を離散化し、頂点は nerveMap Coch≫strictToD。
theorem cosimplicialModuleConeFamily_boundaries :
  (joinInl Δ[0] K₀ ⊗ₘ 𝟙 Bm) ≫ cosimplicialModuleConeFamily =
      (λ_ Bm).hom ≫ nerveMap Coch ≫ complexOrdinaryDerivedSource A ∧
  (joinInr Δ[0] K₀ ⊗ₘ 𝟙 Bm) ≫ cosimplicialModuleConeFamily = discreteEvalFamily
-- D08：G10 のホモロジー入口（整数次数の零延長を明記）。
def cosimplicialModuleCone_homology (M) (i : ℤ) :
  derivedInfinityHomology A i (cosimplicialModuleCone M).vertex ≃ₗ[A]
    (Coch.obj M).homology i
```

D08は入口表の `.homology' i` という紙の略記を、既存の整数次数への零延長 `discreteCochainFunctor` に固定して書いたもの。自然数次数には既存の extend のホモロジー同型で戻す。入口の型を黙って弱めない。

### 73.5 実装順・管理

A01から順に進める。A06・A07の区間評価は第一のまとまりに初めから含めた数学であり、後で「同定だけの追加」に数えない。A12/B01/B02も指定豊穣合成との照合として初めから含める。細部の universe・binder・既存 API 名の elaboration は検証対象で、未検証の型案を検収済み宣言と数えない。一覧外の新しい数学が必要なら、その型と漏れた理由を保存して止める。照合だけの追加枠は現在0/3。

行数は外枠12,500行だけで管理する。§72の予測だけを理由に再び止めない。停止点2で§37.2・§72.2の四行と実測を照合し、閉じた後は§38.2の1・2へ進む。凍結確定の連絡はこの記録時点で未受領。確定後はコミットを控え、型案・依存の紙の確認を続ける。

## 74. 一覧A01の検証と、A02の添字交換の照合

A01の二宣言を `DiagramComparison.FreeProductDiagramHomotopies` に実装し、`43f92578d` に保存した。新規1本36行、累計 **142本8,870行**。個別検査、鍵付き対象ビルド **2,273 jobs** と累計 **1,623宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-74.log`、監査 `/private/tmp/AuditISW2G10HundredFortyTwo.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortytwo-modules.txt`。`--wait 3600`、一枚の整理券、実行1,700秒上限で検証の間だけ鍵を使用した。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramHomotopies
```

A02のため、既存の積添字の構成と二重図式の構成の**成分の並べ替えだけ**の補題を追加する。追加枠 **1/3**。新しいホモトピーの存在定理ではなく、仮定のホモトピーの同じ成分を二重に評価する。型は以下（`J,K,C` は圏、`C` は Preadditive、`c : ComplexShape ι`）。

```lean
local notation "E₁" => functorToComplexOfFunctors (J × K) C c
local notation "E₂" =>
  (Functor.obj (Functor.whiskeringRight J (K ⥤ HomologicalComplex C c)
    (HomologicalComplex (K ⥤ C) c)) (functorToComplexOfFunctors K C c) ⋙
    functorToComplexOfFunctors J (K ⥤ C) c)

def curriedDiagramHomotopy {F G : J ⥤ K ⥤ HomologicalComplex C c}
    (f g : F ⟶ G)
    (h : Homotopy ((E₁).map (Functor.uncurry.map f))
      ((E₁).map (Functor.uncurry.map g))) :
    Homotopy ((E₂).map f) ((E₂).map g)
```

置き場所 `HomologicalAlgebra/CurriedDiagramHomotopy.lean`。この記録時点では個別検査中、未コミット・累計には未算入。A02ではこれを `Δ × J` の同じ AW・shuffle のホモトピーへ適用し、各パラメータで存在を選び直さない。停止点2は未完。新しい数学の一覧外追加はない。

## 75. A02の同じ成分の添字交換を検証

§74の `HomologicalAlgebra.CurriedDiagramHomotopy` は `72beb3083` に保存。57行、累計 **143本8,927行**。個別検査、鍵付き対象ビルド **1,227 jobs**、累計 **1,630宣言・標準三公理のみ**の監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-75.log`、監査 `/private/tmp/AuditISW2G10HundredFortyThree.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortythree-modules.txt`。鍵は指定どおり `--wait 3600`、一枚、1,700秒上限。A02全体を完了とは数えない。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.CurriedDiagramHomotopy
```

もう一つ、A02に必要な既存二構成の照合を追加する（追加枠 **2/3**）。重みの射影は `frameWeightDiagram W := CategoryTheory.Prod.snd SimplexCategory J ⋙ W` と固定し、同型の各成分は恒等。

```lean
def freeProductFrameUncurryIso (A : Type u) [CommRing A]
    {J : Type v} [Category.{w} J]
    (W : J ⥤ SSet.{u}) (P : SimplexCategory ⥤ (J ⥤ SSet.{u})) :
  Functor.uncurry.obj (freeProductFrame A W P) ≅
    freeNegativeChainsDiagram (A := A)
      (frameWeightDiagram W ⊗ Functor.uncurry.obj P)
```

自然性は自由鎖の合成則とテンソルの合成則だけで証明する。同型の存在に新しい数学を使わない。`DiagramComparison.FreeProductFrameUncurry`（39行）は個別検査済み、対象ビルド・監査中、未コミットで上の累計に未算入。検証中のファイルは変更しない。

## 76. 積frameの同定を検証、A02の両合成へ

`DiagramComparison.FreeProductFrameUncurry` は `4b718e6b8` に保存。39行、累計 **144本8,966行**。個別検査、鍵付き対象ビルド **2,275 jobs**、累計 **1,634宣言・標準三公理のみ**の監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-76.log`、監査 `/private/tmp/AuditISW2G10HundredFortyFour.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortyfour-modules.txt`。鍵は `--wait 3600`、一枚、実行1,700秒上限、検証の間だけ取得。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrameUncurry
```

A02の前向き合成 `freeProductFrameAWShuffleHomotopy` は個別検査済み。`Δ × J` 上のA01を、この指定同型で前後から合成し、§74の添字交換で戻した。全パラメータについて一つの鎖ホモトピーになっている。`FreeProductFrameHomotopies.lean` は逆順も含めて検査中で、まだコミット・累計算入していない。

逆順に用いるテンソル側の照合も明記する。追加枠 **3/3**。A02の証明内の局所同型 `e₀` として実装するが、枠から除外はしない。

```lean
-- A : Type u、[CommRing A]、J : Type v、[Category.{w} J]、
-- W : J ⥤ SSet.{u}、P : SimplexCategory ⥤ (J ⥤ SSet.{u})。
e₀ : Functor.uncurry.obj (freeTensorFrame A W P) ≅
  freeNegativeChainsDiagram (A := A) (frameWeightDiagram W) ⊗
    freeNegativeChainsDiagram (A := A) (Functor.uncurry.obj P)
```

各成分は恒等で、自然性はテンソルと自由鎖の合成則のみ。新しい数学ではない。この後、一覧外の数学または追加枠を超える独立した照合宣言が必要になれば、検証済みを保存して型と理由を報告する。A02以降のA03〜D08は未完で、停止点2ではない。

## 77. 一覧A02の全パラメータ・ホモトピーを検証

`DiagramComparison.FreeProductFrameHomotopies` のA02二宣言を `41d84b940` に保存。88行、累計 **145本9,054行**。任意の余単体パラメータ図式について、指定AW・shuffleの両合成が、二重図式の複体で恒等射にホモトピックである。A01を積添字へ適用し、恒等成分の同型と§74の並べ替えで運ぶため、全余単体作用素とJの全射への自然性を含む。これを単体的Hom空間の同値性の完成とはしない。後者はA06〜A09。

個別検査、鍵付き対象ビルド **2,278 jobs**、累計 **1,657宣言・標準三公理のみ**の監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-77.log`、監査 `/private/tmp/AuditISW2G10HundredFortyFive.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortyfive-modules.txt`。共有鍵は `--wait 3600`、一枚の整理券、実行1,700秒上限。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrameHomotopies
```

A03 `StandardParameterAugmentation` は既存の `normalizedSimplexCochainContraction_naturality` と `freeStandardSimplexParameterIso` を合成する構成。依存のoleanが未生成だったため依存ソースを含む一時ファイルで個別検査し、成功した。対象ビルド・監査中、未コミット。A04の積側 `ProductFrameCoaction` は個別検査中。いずれも上の検証済み累計には含めない。§73の `liftedStandardSimplexParameter (u := u)` は宇宙を項引数に書いてしまった記法上の誤りであり、実装では係数環と同じ宇宙を型から固定する。数学的な型の変更ではない。追加枠は3/3のまま。

## 78. 一覧A03の標準パラメータ増大写像を検証

`DiagramComparison.StandardParameterAugmentation` を `bf6a100e0` に保存。35行、累計 **146本9,089行**。既存の全単体で自然な正規化単体の増大写像を、指定 `freeStandardSimplexParameterIso` で戻した。⑤aの既存ファイルは変更していない。

依存ソースを含む個別検査、鍵付き対象ビルド **2,352 jobs**、累計 **1,669宣言・標準三公理のみ**の監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-78.log`、監査 `/private/tmp/AuditISW2G10HundredFortySix.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortysix-modules.txt`。鍵は `--wait 3600`、整理券一枚、実行1,700秒上限で検証の間だけ使用。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterAugmentation
```

## 79. 一覧A04の両frameの指定余作用を検証

`DiagramComparison.ProductFrameCoaction`（39行）と `DiagramComparison.TensorFrameCoaction`（54行）を `f592cd727` に保存。新規2本93行、累計 **148本9,182行**。

積側は既存のパラメータグラフとAW、テンソル側は同じ自由鎖の対角とAW・結合子で構成し、全単体作用素への自然性を証明した。係数環の宇宙を明示する `standardParameterForCoefficients A J` は既存 `liftedStandardSimplexParameter J` の型略記であり、新しい数学の主張ではない。§73の局所記法Pもこの略記に修正した。単位則A05はまだ証明していない。

個別検査、鍵付き対象ビルド **2,278 jobs**、累計 **1,695宣言・標準三公理のみ**の監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-79.log`、監査 `/private/tmp/AuditISW2G10HundredFortyEight.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortyeight-modules.txt`。鍵は `--wait 3600`、一枚、実行1,700秒上限。全検証プロセスは終了し、鍵は解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductFrameCoaction
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.TensorFrameCoaction
```

再開後の一覧の実績は **A01〜A04完了**。独立した照合の追加枠は§74〜76の **3/3**。未コミットのLeanはない。外枠12,500行の残りは3,318行で、行数による中間停止はしない。次はA05の指定余作用の単位則、A06〜A09の区間評価と実単体的Hom比較の同値性へ進む。B01〜D08も引き続き今回の責任であり、停止点2は未完。

A05に再利用できる候補を確認した：`EInfinity.AlexanderWhitney.cochainDiagonal_right_counit` と `cochainCounit_stdSimplex_eq_contraction`。ただし前者の対角と、今回の整数から係数移送した指定AWの一致は型の類似だけでは済ませない。A06の端点に使う零単体の単位同型には既存 `cochainCounit_stdSimplexZero_isIso` が候補となる。これらは現時点の参照候補で、A05・A06の検証完了には数えない。

## 80. A05の展開と、一覧外の右増大写像整合性による停止

A05の積側を `FrameCoactionCounit.lean` の作業木で展開した。各余単体・各図式対象での指定写像の等式へ戻し、正次数は零延長の零性で処理した。負次数は延長の指定同型と Moore 射影の分裂を使って自由生成元での等式へ帰着した。ここまでのスクリプトの残りはその生成元の目標であり、**A05の証明全体は未完**。66行の未検証下書きはコミットせず、検証済み148本9,182行には算入しない。個別検査ログ `/private/tmp/isw2-a05-generators.log` は未解決目標を報告して終了コード1であり、成功した検証とは数えない。

### 80.1 一覧に追加が必要になった数学の補題の型

A05の両単位則への接続に用いる次の二因子AWの法則が、§73の一覧から漏れていた。提案名 `freeProductAlexanderWhitney_right_augmentation`。以下は CategoryTheory、MonoidalCategory、CartesianMonoidalCategory、ComplexLimits、DiagramComparison、Project.DerivedCategories の名前を開いた表記。

```lean
theorem freeProductAlexanderWhitney_right_augmentation
    (A : Type u) [CommRing A]
    (φ : simplicialRingCoefficient.{u} →+* A)
    (Z : SSet.{u}) (n : SimplexCategory) :
  freeProductAlexanderWhitney φ Z
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) ≫
    (𝟙 (freeNegativeChains (A := A) Z) ⊗ₘ
      (normalizedSimplexCochainContraction A n).hom) ≫
    (ρ_ (freeNegativeChains (A := A) Z)).hom =
    freeNegativeChainsMap (A := A)
      (fst Z ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)))
```

この**主張の型だけ**を `/private/tmp/isw2-a05-right-augmentation-type.lean` の `rightAugmentationStatement : Prop` として elaboration し、終了コード0を確認した（ログ `/private/tmp/isw2-a05-right-augmentation-type2.log`）。証明を与えたわけではなく、公理や `sorry` で埋めてもいない。

内容は、指定AWの第二因子を同じ単体増大写像で潰すと、元の積から第一因子への射影の自由鎖写像そのものになる、という**厳密な等式**。一般のZを許す必要がある。積側A05には `Z = W.obj j × Δ[n]` を代入し、パラメータグラフを前合成する。テンソル側A05には `Z = Δ[n]` を代入し、対角を前合成する。グラフ／対角と第一射影の合成が恒等であること、および結合子の自然性で、それぞれ元のA05へ戻る。

### 80.2 漏れた理由と既存宣言との差

§73では、A05を既存のAW余単位則と係数移送に接続する内部計算として見込み、上の二因子の法則を型つきで独立に列挙しなかった。これは一覧の粒度が不足していた。

確認した既存 `EInfinity.AlexanderWhitney.cochainDiagonal_right_counit` は、`X : SSet.{0}` に対する別の直接構成の対角と、その構成の `cochainCounit` の法則。今回の左辺は、任意の宇宙のZと持ち上げ標準単体の積に対する `freeProductAlexanderWhitney` であり、`normalizedMooreMapIso`・整数テンソルの係数拡大・負次数延長を経由する。`cochainCounit_stdSimplex_eq_contraction` は増大写像の同定に使えるが、二因子AWの上の法則までは結論しない。

上の法則を作らずA05に成分計算を直接埋め込む形も数学的には考えられる。しかし、必要なAWの右増大写像計算を「実装上の同定」として追加枠から外したり、局所補題として黙って隠したりはしない。今回の停止は数学的な不可能性の主張ではなく、**残補題を型つきで列挙してから進めるという新しい規則に対する不足の報告**である。

### 80.3 保存状態と停止条件

検証済みコードは `f592cd727` まで、直前の検証報告は `f9a44613a`。148本9,182行、最後の対象ビルド2,278 jobsと累計1,695宣言・標準三公理のみの監査は§79のとおり。今回、新しく検証済みと呼べるLean宣言は増えていない。ビルドの鍵は取得していない。

ユーザー指示2「一覧にない新しい数学の補題が要ったら、検証済みをコミットして止まり、その型と一覧から漏れた理由を報告」に従い、**A05の追加証明をここで停止する**。照合追加枠は3/3のままで、この法則を4本目の単なる照合とは扱わない。外枠12,500行による停止ではない。停止点2も未完。

上の一補題を第一のまとまりのA05の前提計算として一覧に加える判断を求める。範囲を別の第五のまとまりへ広げる案ではなく、同じ指定余作用と増大写像を保持するための補題である。承認後はこの法則を証明し、A05の両単位則へ接続してからA06以降へ進む。

## 81. A05aの承認を反映、前提計算の枠を開始

11-13のユーザー指示とmainのIS-W2 §13を確認した。§80.1の型をそのまま **A05a** に追加し、停止を解除する。前提計算の枠は照合枠3/3とは別に管理する。外枠12,500行、凍結確定後はコミットを控える規則も維持する。現時点で凍結確定の連絡は未受領。

### 81.1 前提計算1/3：右因子が零次だけに値を持つ場合のAW切断和

提案・実装名 `alexanderWhitneyApp_right_zero_degree`。既存AWの右余単位計算に使う法則で、新しい比較模型を導入しない。

```lean
theorem alexanderWhitneyApp_right_zero_degree
    (C D : SimplicialObject (ModuleCat.{u} ℤ))
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : (AlgebraicTopology.alternatingFaceMapComplex _).obj C ⟶ K)
    (g : (AlgebraicTopology.alternatingFaceMapComplex _).obj D ⟶ L)
    (hg : ∀ k : ℕ, k ≠ 0 → g.f k = 0) (n : ℕ) :
    alexanderWhitneyApp C D n ≫ (chainIntegerTensorMap f g).f n =
      alexanderWhitneySummand C D n (Fin.last n) ≫ (chainIntegerTensorMap f g).f n
```

名前空間は既存の `Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories` のAW・整数テンソルを開いた表記。置き場所は `DiagramComparison/AWRightAugmentationCut.lean`。最後以外の切断では第二次数 `n-i` が正なので、仮定hgと整数テンソルの零写像則でその項を消す。A05aではMoore射影と増大写像を合成したgに適用する。まず整数係数のこの計算を閉じ、その後に指定係数移送を戻す。

この記録時点では個別検査中、未コミット。§80の未完下書きも引き続き作業木に保持し、検証済み148本9,182行には算入しない。照合枠3/3、前提計算枠1/3。

### 81.2 前提計算2/3：Moore正規化後の最後の切断

1本目を、既存のMoore包含と二因子の射影で挟む法則。`NormalizedAWRightAugmentationCut.lean` で個別検査中。名前空間は§81.1とDoldKanを開く。

```lean
theorem normalizedAlexanderWhitney_right_zero_degree
    (C D : SimplicialObject (ModuleCat.{u} ℤ))
    {L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (g : (normalizedMooreComplex _).obj D ⟶ L)
    (hg : ∀ k : ℕ, k ≠ 0 → g.f k = 0) (n : ℕ) :
  (normalizedAlexanderWhitney C D ≫ chainIntegerTensorMap (𝟙 _) g).f n =
    (inclusionOfMooreComplexMap (simplicialIntegerTensor C D)).f n ≫
      integerTensorMap ((PInftyToNormalizedMooreComplex C).f n)
        (D.map (awBack n (Fin.last n)).op ≫
          (PInftyToNormalizedMooreComplex D ≫ g).f (n - n)) ≫
      ιMapBifunctor ((normalizedMooreComplex _).obj C) L integerTensorBifunctor
        (.down ℕ) n (n - n) n (awDegrees n (Fin.last n))
```

最後の切断では `awFront n (Fin.last n) = 𝟙 _` であり、第二次数は `n-n`。dependentな次数を不必要に書き換えず、元の直和包含の添字をそのまま保持する。前提計算枠2/3、照合枠3/3。A05aの係数移送後の主張はまだ未完。

## 82. A05aの前提計算2本を検証・保存

§81.1・§81.2の型を変更せず、非正規化AWとMoore正規化AWの右零次切断則を証明した。コードコミット **`0fee2038e`**。いずれも既存AWの最後以外の切断を零にし、最後の前面が恒等であることを使う。正規化版は指定された包含・射影・直和包含を保持する。既存の宣言は変更していない。

| 新規モジュール（DiagramComparison/） | 行数 | 内容 |
| --- | ---: | --- |
| AWRightAugmentationCut | 45 | 右因子が零次以外で零のとき、有限切断和は最後の切断に等しい |
| NormalizedAWRightAugmentationCut | 54 | 同じ公式をMoore包含・射影で挟んだ正規化AWの公式 |

### 82.1 検証

個別の結合ソース検査 `/private/tmp/isw2-a05a-normalized-check6.lean` は終了コード0。続いて `with_build_lock.sh --wait 3600` と1700秒の実行上限で、`NormalizedAWRightAugmentationCut` の対象ビルドと累計の一時監査を実行し、終了コード0を確認した。対象ビルド **1,804 jobs**、累計 **150モジュール・1,697宣言、標準三公理のみ**。新規2本にsorry・新公理なし。鍵は検証終了時に返却済み。

- ログ：`/private/tmp/isw2-build82.log`
- 監査：`/private/tmp/AuditISW2G10HundredFifty.lean`
- 対象一覧：`/private/tmp/isw2-g10-hundredfifty-modules.txt`

3b-2の検証済み実測は **9,281行**（§79の9,182行 + 99行）。外枠12,500行まで3,219行。登録すべき追加モジュールは上表の2本であり、入口と公式監査は編集していない。

### 82.2 A05a本体の作業木と残り

`FreeProductAWRightAugmentation.lean` に§80.1と同じ型の証明を開始した。正次数は零延長の零性で閉じ、非正次数は指定の延長項同型・Moore射影の分裂を前合成して、元の自由生成元における等式に帰着した。個別検査 `/private/tmp/isw2-a05a-body1.log` はその負次数の生成元等式が未解決のため終了コード1。**A05aはまだ証明済みではない**。この49行の下書きと、以前の `FrameCoactionCounit.lean` 66行は未コミット・上の検証済み行数に不算入。

次に必要なのは、正規化AWの切断公式を、指定された `normalizedMooreMapIso`・`integerNegativeTensorBaseChangeIso`・自由化比較・負次数延長を通して、同じ `normalizedSimplexCochainContraction` の右増大写像へ接続する成分計算。別の直接AWへの置換や、余単位則を仮定とする型の変更はしていない。A05aが閉じた後にA05の両単位則、A06以降へ進む。停止点2は未完。

前提計算の枠は **2/3**（残り1本）、照合の枠は **3/3** のまま。新しい数学の追加による停止ではなく、承認済みA05aの証明途中の記録。凍結確定の連絡は、この保存時点で未受領。

## 83. 前提計算3/3：係数移送と斉次包含の照合

A05aで整数AWの切断公式を一般Aに移すため、既存の係数移送の成分則を前提計算枠の3本目に追加する。独立の数学的比較を作るのではなく、`integerNegativeTensorBaseChangeIso` の定義に含まれる既存の同型の成分公式を合成する。置き場所は `DiagramComparison/IntegerNegativeTensorCoefficients.lean`。

以下で `F := integerCoefficientExtension φ`、`Kφ := (F.mapHomologicalComplex (.down ℕ)).obj K`、`Lφ := (F.mapHomologicalComplex (.down ℕ)).obj L`。`A : Type u`、`[CommRing A]`、`φ : simplicialRingCoefficient.{u} →+* A`、`K L : ChainComplex (ModuleCat.{u} ℤ) ℕ` を引数とする。

```lean
theorem integerNegativeTensorBaseChangeIso_ι (i j n : ℕ) (h : i + j = n) :
    (F).map (ιMapBifunctor K L integerTensorBifunctor (.down ℕ) i j n h) ≫
      ((((F).mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor K L)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
      (integerNegativeTensorBaseChangeIso K L φ).hom.f (-(n : ℤ)) =
    (ModuleCat.extendScalars φ).map (integerCoefficientTensorIso (K.X i) (L.X j)).inv ≫
      Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ)
        (integerCoefficientModuleFunctor.obj (K.X i))
        (integerCoefficientModuleFunctor.obj (L.X j)) ≫
      (((Kφ).extendXIso ComplexShape.embeddingDownNat (i := i) (i' := -(i : ℤ)) rfl).inv ⊗ₘ
        ((Lφ).extendXIso ComplexShape.embeddingDownNat (i := j) (i' := -(j : ℤ)) rfl).inv) ≫
      ιTensorObj ((Kφ).extend ComplexShape.embeddingDownNat)
        ((Lφ).extend ComplexShape.embeddingDownNat) (-(i : ℤ)) (-(j : ℤ)) (-(n : ℤ))
        (by omega)
```

前提計算枠3/3、照合枠3/3。追加時点では証明・検査中であり、検証済みの150本・9,281行には算入しない。A05aは引き続き未完。

### 83.1 検証と保存

コード **`47d7ebdb1`**、新規1本84行。個別検査 `/private/tmp/isw2-coefficient-cut13.log` は終了コード0。鍵付きの対象ビルド（`--wait 3600`、実行上限1700秒）は **2,239 jobs** で成功し、続く累計監査も終了コード0。累計 **151モジュール・1,700宣言、標準三公理のみ**、検証済み **9,365行**。追加の3宣言にはLeanが生成した補助宣言を含み、手書きの主張は上記の一つ。sorry・新公理なし、既存宣言の変更なし。

- ログ：`/private/tmp/isw2-build83.log`
- 一時監査：`/private/tmp/AuditISW2G10HundredFiftyOne.lean`
- 対象一覧：`/private/tmp/isw2-g10-hundredfiftyone-modules.txt`
- 登録対象の追加：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerNegativeTensorCoefficients`

鍵は検証終了時に返却済み。入口と公式監査は変更していない。外枠12,500行まで3,135行。前提計算枠3/3、照合枠3/3。

A05a本体の作業木では、指定増大写像の零次以外での零性を既存の単一複体の零性から得た。また、射影側の右辺はMoore射影の自然性・零延長の指定同型・自由生成元の写像則で、第一成分の生成元をMoore射影して延長へ戻す式まで整理した（`/private/tmp/isw2-a05a-body8.log`、残る主目標があるため終了コード1）。AW側の係数移送との照合が残る。A05a・A05・停止点2はまだ未完であり、下書きはコミットしていない。

### 83.2 A05a入力のMoore比較の整理

その後、A05aの未コミット下書きで、入力の自由化比較をMoore射影の自然性で射影の前へ移し、`normalizedMooreMapIso` の逆を定義どおりに展開した。包含と射影の合成を既存の `PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap` により正規化冪等射へまとめ、既存 `alternatingMapIso_PInfty` と `PInfty_comp_PInftyToNormalizedMooreComplex` で係数移送前の射影へ戻した。追加の独立した補題は導入していない。

最後の個別検査 `/private/tmp/isw2-a05a-body19.log` は、これらの内部手順にはエラーがなく、負次数の主等式が未解決のため終了コード1。左辺の入力は今や、元の整数Moore射影の係数拡大に対し、元の整数正規化AWの係数拡大を適用する形になった。右辺は第一射影の生成元をMoore射影する明示式。次はAWの切断成分に§81・§83の公式を適用し、同じ右増大写像・右単位子を通した式を右辺と照合する。

`FreeProductAWRightAugmentation.lean` は120行の未完下書きとして作業木に保持する（検証済み9,365行に不算入）。A05a・A05・停止点2は未完。検証済みのコード保存点は引き続き `47d7ebdb1`、前提計算枠3/3・照合枠3/3。凍結確定の連絡は未受領で、未検証コードはコミットしていない。

## 84. A05aを最後の切断へ帰着、余単位の独立補題の追加判断

### 84.1 今回の到達点

A05aの作業木で、整数の正規化AWを非正規化の切断和へ戻し、§83の係数移送の斉次包含公式を適用した。同じ増大写像の零次以外の零性により、右因子の次数が正であるすべての切断成分を消した。有限和を最後の切断 `Fin.last k` だけにする内部計算も通り、A05aの主目標はその一項の等式へ帰着した。`/private/tmp/isw2-a05a-body24.log` はこの段階の主等式だけが未解決で終了コード1。証明全体の成功とは数えない。

最後の切断の値は、係数拡大随伴と既存 `integerTensor_hom_ext` で二つの整数自由生成元に帰着した。入力の自由化比較、前面・後面の純テンソル評価、二つのMoore射影の純テンソル評価は内部の小さい等式として検査を通った。A上の `ULift.module` がφ由来の加群構造と競合していたため、φ由来の `Module simplicialRingCoefficient A` を明記した。切り分け専用 `/private/tmp/isw2-coefficient-pure-probe2.log` は終了コード0。既存の宣言・インスタンスは変更していない。

### 84.2 切り出す主張の型

次の一つを `DiagramComparison/FreeProductAWLastCut.lean` に独立した補題として切り出す案。数学内容は、**指定AWの最後の切断を、同じ係数移送・Moore射影・単体増大写像・右単位子で評価する余単位則**。別の比較模型や新しい第五のまとまりではない。

```lean
theorem freeProductAlexanderWhitney_last_cut_right_augmentation
    (A : Type u) [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)
    (Z : SSet.{u}) (n : SimplexCategory) (k : ℕ) :
  let Y := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)
  let F := integerCoefficientExtension φ
  let NC := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Z)
  let ND := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)
  let e0 := Functor.isoWhiskerRight (linearizedTensorIso Z Y) F ≪≫
    integerCoefficientSimplicialFreeIso φ (Z ⊗ Y)
  F.map (alexanderWhitneySummand (linearizedSpace Z) (linearizedSpace Y)
      k (Fin.last k) ≫
      (chainIntegerTensorMap (PInftyToNormalizedMooreComplex (linearizedSpace Z))
        (PInftyToNormalizedMooreComplex (linearizedSpace Y))).f k) ≫
    (((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor NC ND)).extendXIso
      ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl).inv ≫
    ((negativeMooreTensorCoefficientIso φ (linearizedSpace Z) (linearizedSpace Y)).hom ≫
      (tensorIso (integerCoefficientFreeChainsIso φ Z)
        (integerCoefficientFreeChainsIso φ Y)).hom ≫
      (𝟙 _ ⊗ₘ (normalizedSimplexCochainContraction A n).hom) ≫
      (ρ_ (freeNegativeChains (A := A) Z)).hom).f (-(k : ℤ)) =
    e0.hom.app (Opposite.op ⦋k⦌) ≫
      (ModuleCat.free A).map ((fst Z Y).app (Opposite.op ⦋k⦌)) ≫
      (PInftyToNormalizedMooreComplex (Z ⋙ ModuleCat.free A)).f k ≫
      (((normalizedMooreComplex (ModuleCat A)).obj (Z ⋙ ModuleCat.free A)).extendXIso
        ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl).inv

```

型だけを `/private/tmp/isw2-a05a-last-cut-type.lean` の命題値の定義として検査し、終了コード0を確認した（ログ `/private/tmp/isw2-a05a-last-cut-type.log`）。これはこの命題の証明ではない。上記の独立宣言はまだ本体に追加していない。

### 84.3 独立補題が必要になった理由と停止

§81〜83では、切断和、Moore正規化後の切断公式、係数移送の斉次包含公式を三つの前提計算として列挙した。しかし最後に残る零次増大写像・右単位子の値の照合を、独立の型として列挙せずA05aの中に展開する見込みだった。

その形で実装を進めると、最後の値の計算の途中で既定の200,000 heartbeatに達する。`/private/tmp/isw2-a05a-body42.log` の一時計測では、係数テンソルの逆比較の値を述べる直前の残量は内部単位518,963（表示上のheartbeatで約519）だった。大きな式全体の書き換えを `conv` で対象箇所に限定し、増大写像の始域も局所名で揃えたが、累計の余裕を確保できていない。計算上限は上げていない。一時的な計測コードは下書きから除去した。

提案は、上記の余単位則を独立に証明し、A05a本体では最後の切断へ帰着した所から適用すること。数学的な不可能性や新たな仮定の必要性ではなく、**型つき一覧の粒度と証明の分割に関する追加判断**である。A05aの型を弱めたり、余単位則を仮定に置いたりはしない。

11-13のユーザー指示（IS-W2 §13）の「法則の補題は、3本まで止まらずに一覧に足してよい」に対し、前提計算枠は既に3/3。照合枠も3/3。この余単位則を4本目の独立補題として黙って追加しないため、ここで追加のLean作業を停止し、上記一補題の追加承認を求める。A05aと同じ第一のまとまりに属し、外枠12,500行の変更は求めない。

### 84.4 保存状態

検証済みの保存点は `47d7ebdb1`、前回の報告は `2acb5b5f3`。**151モジュール・9,365行・1,700宣言、標準三公理のみ**は§83の検収結果から変わらない。今回、新しく完成した本体宣言はないため、鍵付きビルド・監査を成功したとは報告しない。ビルドの鍵は取得しておらず、待機中の整理券もない。

A05aの下書き `FreeProductAWRightAugmentation.lean` は296行、以前の `FrameCoactionCounit.lean` は66行。両方未コミット・検証済み行数に不算入。新しい未検証コードをコミットしていない。既存宣言・⑤aのファイル・入口・公式監査は変更していない。凍結確定の連絡は未受領。A05a・A05・停止点2は引き続き未完。

## 85. §14の承認を反映し、A05aの証明を分割

11-13のユーザー指示に従い、§84.2の最後の切断の余単位則を同じ型で `FreeProductAWLastCut.lean` に切り出した。証明の分割は追加枠に算入せず、型を本報告へ記録する。前提計算は一覧の補題ごとに3本、照合枠は全体3/3、外枠12,500行の規則を維持する。計算上限は上げていない。

### 85.1 同じMoore射影計算の部分補題

以下二つはA05aで使っている既存のMoore比較と射影の計算を分けたもの。新しい模型を作らない。

`SerrePositivity/HomologicalAlgebra/NormalizedMooreMapProjection.lean`

```lean
theorem normalizedMooreMapHom_projection :
    (F.mapHomologicalComplex (.down ℕ)).map (PInftyToNormalizedMooreComplex X) ≫
      normalizedMooreMapHom F X =
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X ≫
      PInftyToNormalizedMooreComplex (X ⋙ F)
```

`SerrePositivity/InfinityCategories/Project/DerivedCategories/DiagramComparison/FreeChainsCoefficientProjection.lean`

```lean
theorem freeChainsCoefficient_projection {A : Type u} [CommRing A]
    (φ : simplicialRingCoefficient.{u} →+* A) (X : SSet.{u}) :
    ((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).map
        (PInftyToNormalizedMooreComplex (linearizedSpace X)) ≫
      normalizedMooreMapHom (integerCoefficientExtension φ) (linearizedSpace X) ≫
      (normalizedMooreComplex (ModuleCat A)).map
        (integerCoefficientSimplicialFreeIso φ X).hom =
    (alternatingFaceMapComplexCompMapHomologicalComplexIso
      (integerCoefficientExtension φ)).hom.app (linearizedSpace X) ≫
      (alternatingFaceMapComplex (ModuleCat A)).map
        (integerCoefficientSimplicialFreeIso φ X).hom ≫
      PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A)
```

第一の型では `{C D : Type*}` に圏・アーベル圏、`F : C ⥤ D` に加法性、`X : SimplicialObject C` を仮定する。第二は型に記載の引数を持つ。名前はそれぞれ `SerrePositivity.HomologicalAlgebra`、`DiagramComparison` の名前空間。結合ソースの個別検査 `/private/tmp/isw2-free-projection-check3.log` は終了コード0。鍵付きの対象ビルド・監査を実行中のため、この記録時点では検証済み151本の実績はまだ更新しない。

### 85.2 最後の切断の証明の現在地

独立した `FreeProductAWLastCut.lean` では、係数テンソルの逆比較とδの純テンソル評価を通過し、二因子のMoore比較・自由化比較・零次増大写像・右単位子の値を照合する主等式が残る。個別検査 `/private/tmp/isw2-last-cut5.log` はその主等式が未解決で終了コード1。A05aの元の下書きとともに未コミットで保持し、A05a・A05・停止点2の完了とは数えない。

### 85.3 負次数成分への同じ計算の分割

最後の切断の証明内で、以下の成分等式を使用する。`F := integerCoefficientExtension φ` とし、`A : Type u`、`[CommRing A]`、`φ : simplicialRingCoefficient.{u} →+* A` を固定する。これは§85.1を零延長の成分公式で表す同じ内容の部分計算であり、検査中。独立した新しい数学の補題として追加しない。

```lean
have hμ (X : SSet.{u}) (r : ℕ) :
      F.map ((PInftyToNormalizedMooreComplex (linearizedSpace X)).f r) ≫
        ((((F.mapHomologicalComplex (.down ℕ)).obj
          ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X))).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv) ≫
        (extendMap (normalizedMooreMapHom F (linearizedSpace X)) ComplexShape.embeddingDownNat ≫
          (integerCoefficientFreeChainsIso φ X).hom).f (-(r : ℤ)) =
      (integerCoefficientSimplicialFreeIso φ X).hom.app (Opposite.op ⦋r⦌) ≫
        (PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A)).f r ≫
        (((normalizedMooreComplex (ModuleCat A)).obj (X ⋙ ModuleCat.free A)).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
```

### 85.4 成分式と生成元評価の独立した分割

§85.3の内部計算とその自由生成元での値は、再利用時に累計heartbeatを消費しないよう `FreeChainsCoefficientDegrees.lean` に分けた。同じA05aの計算の分割である。個別検査 `/private/tmp/isw2-free-degrees2.log` は終了コード0。型は次のとおり（DiagramComparison名前空間）。

```lean
theorem freeChainsCoefficient_degree {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A) (X : SSet.{u}) (r : ℕ) :
    (integerCoefficientExtension φ).map ((PInftyToNormalizedMooreComplex (linearizedSpace X)).f r) ≫
      (((((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
        ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X))).extendXIso
        ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv) ≫
      (extendMap (normalizedMooreMapHom (integerCoefficientExtension φ) (linearizedSpace X)) ComplexShape.embeddingDownNat ≫
        (integerCoefficientFreeChainsIso φ X).hom).f (-(r : ℤ)) =
    (integerCoefficientSimplicialFreeIso φ X).hom.app (Opposite.op ⦋r⦌) ≫
      (PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A)).f r ≫
      (((normalizedMooreComplex (ModuleCat A)).obj (X ⋙ ModuleCat.free A)).extendXIso
        ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
```

```lean
theorem freeChainsCoefficient_generator_value {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A) (X : SSet.{u}) (r : ℕ) (a : X.obj (Opposite.op ⦋r⦌)) :
    ((integerCoefficientFreeChainsIso φ X).hom.f (-(r : ℤ)))
      ((extendMap (normalizedMooreMapHom (integerCoefficientExtension φ) (linearizedSpace X))
        ComplexShape.embeddingDownNat).f (-(r : ℤ))
        ((((((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
            ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X))).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv)
          ((integerCoefficientExtension φ).map
            ((PInftyToNormalizedMooreComplex (linearizedSpace X)).f r)
            ((integerCoefficientFreeAdjunction φ).unit.app _ a)))) =
    (((normalizedMooreComplex (ModuleCat A)).obj (X ⋙ ModuleCat.free A)).extendXIso
      ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
      ((PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A)).f r (ModuleCat.freeMk a))
```

### 85.5 ここまでの検収

`NormalizedMooreMapProjection` は27行、コード `df8a4ca14`。対象ビルド1,331 jobs、152モジュール・1,702宣言、標準三公理のみ（`/private/tmp/isw2-build85.log`）。`FreeChainsCoefficientProjection` は34行、コード `3a3da1089`。対象ビルド2,242 jobs、153モジュール・1,704宣言、標準三公理のみ（`/private/tmp/isw2-build85b.log`）。どちらも `--wait 3600` の鍵付きビルド・一時監査で終了コード0。検証済み実測は9,426行。入口と公式監査は変更していない。

成分・生成元評価の67行は別の鍵付きビルド・154本の一時監査で検査中。最後の切断とA05aの下書きは引き続き未完・未コミット。追加判断を求める停止ではなく、§14の承認内での証明途中。

### 85.6 最後の切断の残る値

§85.4を独立させた結合検査 `/private/tmp/isw2-last-cut-check9.log` では、両因子への生成元評価の適用を通過した。残る主等式は、第一因子が元のA自由生成元のMoore射影・負次数延長となり、第二因子が同じ標準単体増大写像をそのMoore射影へ適用した形。第二因子の零次の値が1であることと、右単位子・最後の前面の恒等性の照合が残る。この検査は主等式が未解決で終了コード1であり、最後の切断の補題の証明完了とは数えない。A05a・A05・停止点2は未完。

### 85.7 標準単体増大写像の零次の値の分割

最後の切断で残る、同じ増大写像の既存の生成元の値を次の型で `StandardParameterAugmentationValues.lean` に分割する。既存 `normalizedSimplexCochainAugmentation_zero_apply` と `normalizedSimplexChainAugmentation_zero` をMoore零次射影へ接続する同じ計算である。検査中であり、検証済み実績へ算入しない。

```lean
theorem standardParameterAugmentation_moore_generator (A : Type u) [CommRing A]
    (n : SimplexCategory)
    (a : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)).obj (Opposite.op ⦋0⦌)) :
    let W := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⋙ ModuleCat.free A
    (normalizedSimplexCochainContraction A n).hom.f 0
      ((((normalizedMooreComplex (ModuleCat A)).obj W).extendXIso
        ComplexShape.embeddingDownNat (i := 0) (i' := (0 : ℤ)) rfl).inv
        ((PInftyToNormalizedMooreComplex W).f 0 (ModuleCat.freeMk a))) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)
```

直接の個別検査では既存依存の `.olean` が9本不足したため、必要な既存ソースだけを一時ファイルに結合して検査している。共有鍵の待機は154モジュールの一件のまま。

### 85.8 成分・生成元評価の検収と残り

`FreeChainsCoefficientDegrees`（67行）は `e4d2f29c4` に保存した。鍵付き対象ビルド2,359 jobs、一時監査154モジュール・1,706宣言、標準三公理のみで終了コード0（`/private/tmp/isw2-build85c.log`、`/private/tmp/AuditISW2G10HundredFiftyFour.lean`、対象一覧 `/private/tmp/isw2-g10-hundredfiftyfour-modules.txt`）。検証済み実測 **9,493行**。今回の三つの証明分割で計128行増えた。対象のsorry・新公理なし。既存宣言・⑤aのファイル・入口・公式監査は変更していない。鍵は返却済み。

`StandardParameterAugmentationValues` の結合検査 `/private/tmp/isw2-aug-values-check3.log` は終了コード0。これはまだ対象ビルド・累計監査に含めておらず、上の154本に不算入。

最後の切断の結合検査 `/private/tmp/isw2-last-cut-check11.log` は、前面の恒等射の値で通常の `rw` が定義上の一致を見つけられず、その後の検査でも既定heartbeatに達して終了コード1。零次増大写像の値までの接続を追記したが、最後の切断の補題全体は未完。計算上限は上げず、必要な同じ計算の分割を§14の範囲内で続ける。追加承認を求める停止ではない。A05a・A05・停止点2は未完であり、最後の切断・零次増大写像・A05a・A05の各下書きは未コミット。

## 86. 最後の切断の純テンソル計算を指定単位で分割

§14に従い、前回の長い純テンソル評価を次の三宣言に分ける。`coefficientUnit` は既存の係数拡大随伴の単位への略記。二つの値公式はいずれも既存の定義から `rfl` で証明でき、`/private/tmp/isw2-tensor-values2.log` は終了コード0。同じA05aの証明の分割であり、照合枠や新しい数学の補題の追加としては数えない。型は次のとおり（DiagramComparison名前空間、`{A : Type u}`、`[CommRing A]`、`φ : simplicialRingCoefficient.{u} →+* A` を固定）。

```lean
abbrev coefficientUnit (M : ModuleCat.{u} ℤ) :=
  (simplicialRingIntegerModuleEquivalence.toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj φ)).unit.app M
```

```lean
theorem coefficientUnit_tensorMap {M M' N N' : ModuleCat.{u} ℤ}
    (f : M ⟶ M') (g : N ⟶ N') (x : M) (y : N) :
    (integerCoefficientExtension φ).map (integerTensorMap f g)
      (coefficientUnit φ (integerTensor M N) (x ⊗ₜ[ℤ] y)) =
    coefficientUnit φ (integerTensor M' N') (f x ⊗ₜ[ℤ] g y)
```

```lean
theorem coefficientUnit_tensorComparison (M N : ModuleCat.{u} ℤ) (x : M) (y : N) :
    (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ)
      (integerCoefficientModuleFunctor.obj M) (integerCoefficientModuleFunctor.obj N))
      (((ModuleCat.extendScalars φ).map (integerCoefficientTensorIso M N).inv)
        (coefficientUnit φ (integerTensor M N) (x ⊗ₜ[ℤ] y))) =
    TensorProduct.tmul A
      (M := (integerCoefficientExtension φ).obj M)
      (N := (integerCoefficientExtension φ).obj N)
      (coefficientUnit φ M x) (coefficientUnit φ N y)
```

`IntegerCoefficientTensorValues.lean` と§85.7の `StandardParameterAugmentationValues.lean` の対象ビルド・156本の一時監査を、共有鍵 `--wait 3600` で開始した。一つの整理券にまとめており、前回の鍵は返却済み。最後の切断の下書きではこの値公式に置換し、未ビルドの既存依存だけを含む一時結合ソースで個別検査中。全体の成功前にコミットしない。

### 86.1 値の部分補題2本の検収

コード `8dc9fc615`：`IntegerCoefficientTensorValues` 41行、`StandardParameterAugmentationValues` 38行。鍵付き対象ビルド3,963 jobs、累計156モジュール・1,710宣言、標準三公理のみで終了コード0（`/private/tmp/isw2-build86.log`）。一時監査 `/private/tmp/AuditISW2G10HundredFiftySix.lean`、対象一覧 `/private/tmp/isw2-g10-hundredfiftysix-modules.txt`。検証済み実測 **9,572行**。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし。鍵は返却済み。

最後の切断の結合検査は、公式の引数・適用箇所を明示しても既定heartbeatで未完。既存 `Unitors` の未ビルド依存を含む50モジュールの結合ソースになっていたため、通常のモジュール境界で検査するために既存 `Unitors` のみの対象ビルドを共有鍵 `--wait 3600` で開始した。これは最後の切断の証明成功を意味せず、A05a・A05・停止点2は未完。

## 87. 承認済みの最後の切断の余単位則を検収

`freeProductAlexanderWhitney_last_cut_right_augmentation` を§84.2と同じ型で証明した。個別検査 `/private/tmp/isw2-last-cut-check19.log` は終了コード0。コード **`7d081b8c5`**（`FreeProductAWLastCut` 169行、`StandardParameterRightUnit` 37行）。鍵付き対象ビルド4,012 jobs、累計 **158モジュール・1,713宣言、標準三公理のみ**で終了コード0（`/private/tmp/isw2-build87.log`、監査 `/private/tmp/AuditISW2G10HundredFiftyEight.lean`、一覧 `/private/tmp/isw2-g10-hundredfiftyeight-modules.txt`）。検証済み実測 **9,778行**。計算上限は既定のまま、sorry・新公理なし。

追加した単位子の部分補題の型は以下。これは同じ最後の切断の計算の分割で、§14により追加枠へ算入しない。

```lean
theorem standardParameter_right_unit (A : Type u) [CommRing A]
    (n : SimplexCategory) (P : CochainComplex (ModuleCat A) ℤ)
    (r : ℕ) (hr : r = 0) (q : ℤ)
    (a : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)).obj (Opposite.op ⦋r⦌))
    (x : P.X q) :
    let W := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⋙ ModuleCat.free A
    (ρ_ P).hom.f q (ιTensorObj P (𝟙_ (CochainComplex (ModuleCat A) ℤ)) q (-(r : ℤ)) q
      (by subst r; simp) (x ⊗ₜ[A]
      (normalizedSimplexCochainContraction A n).hom.f (-(r : ℤ))
        ((((normalizedMooreComplex (ModuleCat A)).obj W).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
          ((PInftyToNormalizedMooreComplex W).f r (ModuleCat.freeMk a))))) = x
```

A05aの本体は、最後の切断を適用してMoore冪等射の自然性で戻す末尾へ進んだ。まだ全体の検査成功前であり、A05a・A05・停止点2は未完。本体の未検証下書きはコミットしない。既存宣言・⑤a・入口・公式監査の変更なし。共有鍵は返却済み。凍結確定の連絡はこの時点で未受領。

## 88. A05a・A05を完了し、A06の端点へ

A05aは§80.1の型のまま証明・検証を完了した。コード **`6c529dfaf`**（206行）。最後の切断の余単位則を適用し、Moore冪等射の自然性・自由化比較の逆射との合成・指定射影の冪等性で元の第一射影へ戻した。個別検査 `/private/tmp/isw2-a05a-direct4.log`、鍵付き対象ビルド4,013 jobsと159モジュール・1,714宣言の一時監査が終了コード0（`/private/tmp/isw2-build88.log`）。標準三公理のみ。

A05の積側・テンソル側の指定余作用の両単位則も完了。コード **`e0d0f8e53`**（`FrameCoactionCounit` 80行）。積側はA05aとグラフの第一射影、テンソル側は同じA05aと対角の第一射影・結合子の自然性・右単位子のテンソル公式を用いた。個別検査 `/private/tmp/isw2-frame-counit9.log` と対象ビルド4,015 jobs、160モジュール・1,716宣言の一時監査が終了コード0（`/private/tmp/isw2-build89.log`）。標準三公理のみ。検証済み実測 **10,064行**。監査 `/private/tmp/AuditISW2G10HundredSixty.lean`、対象一覧 `/private/tmp/isw2-g10-hundredsixty-modules.txt`。sorry・新公理なし、既存の宣言・⑤a・入口・公式監査の変更なし。

### 88.1 A06の入口：同じ正規化区間の二つの端点

`NormalizedIntervalEndpoints.lean` で零単体の指定増大写像が同型である既存の証明を用い、その逆と二つの頂点包含を合成した。全図式の端点も自然変換として定義した。型は以下（DiagramComparison名前空間）。これはA06の同じ内容の分割。

```lean
def normalizedIntervalEndpointChain (A : Type u) [CommRing A] (ε : Fin 2) :
    𝟙_ (CochainComplex (ModuleCat A) ℤ) ⟶
      freeNegativeChains (A := A)
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj ⦋1⦌))
```

```lean
def normalizedIntervalEndpoint (A : Type u) [CommRing A]
    (J : Type v) [Category.{w} J] (ε : Fin 2) :
    𝟙_ (J ⥤ CochainComplex (ModuleCat A) ℤ) ⟶
      freeNegativeChainsDiagram (A := A) ((Functor.const J).obj
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj ⦋1⦌)))
```

個別の結合検査 `/private/tmp/isw2-interval-endpoints-check2.log` は終了コード0。44行の新規モジュールの鍵付き対象ビルドと161本の一時監査を `--wait 3600` で開始した。前の鍵は返却済み。まだ成功前のため、この記録時点では検証済み160本へ算入しない。

A06本体の `normalizedIntervalHom`・両端の評価・前後合成に関する自然性はこれから。既存 `HomologicalComplex.cylinder.desc` とその二端評価、`DifferentialGraded.dgInterval` を確認したが、これらのcylinderで指定された正規化単体区間を置き換えて済ませることはしない。使う場合も指定区間・端点への厳密な比較を保つ。A06〜D08と停止点2は未完。追加承認を求める停止ではなく、承認済みの一覧に沿った進行。

### 88.2 A06の前提計算1/3：端点と増大写像

同じ端点が指定増大写像の切断である法則を、A06の前提計算1本目として追加する。図式版は同じ点ごとの法則を束ねる証明分割。型は以下。個別検査 `/private/tmp/isw2-interval-augmentation1.log` は終了コード0。

```lean
theorem normalizedIntervalEndpointChain_augmentation (A : Type u) [CommRing A] (ε : Fin 2) :
    normalizedIntervalEndpointChain A ε ≫
      (normalizedSimplexCochainContraction A ⦋1⦌).hom = 𝟙 _
```

```lean
theorem normalizedIntervalEndpoint_augmentation (A : Type u) [CommRing A]
    (J : Type v) [Category.{w} J] (ε : Fin 2) :
    normalizedIntervalEndpoint A J ε ≫ (standardParameterAugmentation A J).app ⦋1⦌ = 𝟙 _
```

共有鍵の同じ待機中の一件へ二本の対象ビルドと162モジュールの監査をまとめた。新しい整理券は発行していない。検証成功までは新規二本をコミット・検証済み実績へ算入しない。

### 88.3 A06本体の次の接続

`normalizedIntervalHom` は指定された `N(Δ[1])` を右因子とする写像として構成する必要がある。内部Homの次数−1コチェインとして同じ鎖ホモトピーを表し、二頂点をf,g、基本1単体をそのコチェインへ送る正規化鎖写像を作り、既存のテンソル–Homの随伴で戻す経路を検討する。図式の自然性は交換関手Eを通したホモトピーの型で与えられており、点ごとの任意選択に置き換えない。

既存cylinderの普遍写像は参考になるが、指定区間とcylinderの別模型の同定を新しい照合として黙って追加しない。照合枠は全体3/3のまま。現在は端点とその増大写像則までであり、上記内部Hom経路の構成・符号・端点評価・前後合成の自然性は未検証。

## 89. A05a・A05完了、A06端点の検収

A06端点と増大写像の切断法則は **`83a842153`** に保存した。`NormalizedIntervalEndpoints` 44行、`NormalizedIntervalEndpointAugmentation` 35行。鍵付き対象ビルド3,979 jobsと162モジュールの一時監査は終了コード0（`/private/tmp/isw2-build90.log`）。累計 **162モジュール・10,143行・1,734宣言、標準三公理のみ**。宣言数にはLean生成の補助宣言も含む。一時監査 `/private/tmp/AuditISW2G10HundredSixtyTwo.lean`、対象一覧 `/private/tmp/isw2-g10-hundredsixtytwo-modules.txt`。共有鍵は返却済み、待機中の整理券はない。

§85の検証済み154本からの登録対象は、以下の8本（すべて `SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.` の後に続く名前）。入口・公式監査への登録は行っていない。

| モジュール | 行数 | 保存点 |
| --- | ---: | --- |
| IntegerCoefficientTensorValues | 41 | 8dc9fc615 |
| StandardParameterAugmentationValues | 38 | 8dc9fc615 |
| StandardParameterRightUnit | 37 | 7d081b8c5 |
| FreeProductAWLastCut | 169 | 7d081b8c5 |
| FreeProductAWRightAugmentation | 206 | 6c529dfaf |
| FrameCoactionCounit | 80 | e0d0f8e53 |
| NormalizedIntervalEndpoints | 44 | 83a842153 |
| NormalizedIntervalEndpointAugmentation | 35 | 83a842153 |

A05aは承認された型の右増大写像則、A05は積側・テンソル側の両単位則を完了した。A06は指定区間の端点・図式自然性・同じ増大写像に対する切断性まで。A06本体の区間評価、両端の評価、前後合成の自然性、A07以降、B・C・Dの各まとまりは未完であり、停止点2の完了報告ではない。

外枠12,500行まで2,357行。型・範囲を弱めず、計算上限を上げず、sorry・新公理なし。既存宣言と⑤aの既存ファイルの変更なし。照合枠は全体3/3、A06の前提計算は端点増大写像の1/3。その他の今回の分割は§14による同じ証明内容の分割として型を報告した。凍結確定の連絡は本記録時点で未受領。

## 90. A06：同じ区間の低次数境界からコチェイン評価を構成

指定された正規化区間を保持し、同じ線形化Δ[1]の交代面複体から評価を構成した。頂点はx,y、非退化な辺はw、高次は零。条件 `d w = y - x` により一次の鎖写像条件が成り立ち、二次は単調な三頂点の三辺の交代和が零であることから成り立つ。Moore正規化の指定包含を前合成し、既存の零延長・smart切断の随伴で元の正規化コチェイン区間からHへの写像へ戻した。

ホモトピー `h : Homotopy f g` のHomコチェインは `δ h = f-g` の向きなので、辺の値として `-h` を用いる。これにより辺の境界はg−fになる。現在は境界データからの評価までで、ホモトピーからのデータの構成と、Rとのテンソルへの転置、両端評価、自然性は未完。

### 90.1 同じA06の証明分割の型

下記4本は新しい模型の比較を導入せず、A06の構成とその鎖写像条件を分けたもの。追加枠に数えない証明分割として型を記録する。名前空間はDiagramComparison。Boundaryでは `{M N : Type*}` とその加法可換群構造、LowDegreesでは `(A : Type u)` と `[CommRing A]` を固定し、`L := (BarrattEccles.linearization A).obj (SSet.stdSimplex.obj ⦋1⦌)` と略記する。

`NormalizedIntervalBoundary`

```lean
def intervalVertexValue (x y : N) (i : Fin 2) : N
```

```lean
def intervalEdgeValue (w : M) (i j : Fin 2) : M
```

```lean
theorem interval_vertex_boundary (x y : N) (i j : Fin 2) (hij : i ≤ j) :
    intervalVertexValue x y j - intervalVertexValue x y i =
      if i = 0 ∧ j = 1 then y - x else 0
```

```lean
theorem interval_edge_boundary (d : M →+ N) (x y : N) (w : M) (hw : d w = y - x)
    (i j : Fin 2) (hij : i ≤ j) :
    d (intervalEdgeValue w i j) = intervalVertexValue x y j - intervalVertexValue x y i
```

```lean
theorem interval_triangle_boundary (w : M) (f : Fin 3 →o Fin 2) :
    intervalEdgeValue w (f 1) (f 2) - intervalEdgeValue w (f 0) (f 2) +
      intervalEdgeValue w (f 0) (f 1) = 0
```

`NormalizedIntervalLowDegrees`

```lean
def intervalVertexEvaluation (M : ModuleCat.{u} A) (x y : M) : (L).obj (Opposite.op ⦋0⦌) ⟶ M
```

```lean
def intervalEdgeEvaluation (M : ModuleCat.{u} A) (w : M) : (L).obj (Opposite.op ⦋1⦌) ⟶ M
```

```lean
theorem interval_evaluation_boundary {M N : ModuleCat.{u} A}
    (d : M ⟶ N) (x y : N) (w : M) (hw : d w = y - x) :
    intervalEdgeEvaluation A M w ≫ d =
      (L).map (SimplexCategory.δ (0 : Fin 2)).op ≫ intervalVertexEvaluation A N x y -
      (L).map (SimplexCategory.δ (1 : Fin 2)).op ≫ intervalVertexEvaluation A N x y
```

```lean
theorem interval_evaluation_triangle (M : ModuleCat.{u} A) (w : M) :
    (L).map (SimplexCategory.δ (0 : Fin 3)).op ≫ intervalEdgeEvaluation A M w -
      (L).map (SimplexCategory.δ (1 : Fin 3)).op ≫ intervalEdgeEvaluation A M w +
      (L).map (SimplexCategory.δ (2 : Fin 3)).op ≫ intervalEdgeEvaluation A M w = 0
```

`NormalizedIntervalRawChain`

```lean
def intervalRawChainMap (A : Type u) [CommRing A] (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (x y : K.X 0) (w : K.X 1) (hw : K.d 1 0 w = y - x) :
    (alternatingFaceMapComplex (ModuleCat A)).obj
      ((SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj ⦋1⦌)) ⟶ K
```

```lean
def intervalNormalizedChainMap (A : Type u) [CommRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℕ) (x y : K.X 0) (w : K.X 1)
    (hw : K.d 1 0 w = y - x) :
    (normalizedMooreComplex (ModuleCat A)).obj
      ((SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj ⦋1⦌)) ⟶ K
```

`NormalizedIntervalCochain`

```lean
def normalizedIntervalCochainMap (A : Type u) [CommRing A]
    (H : CochainComplex (ModuleCat.{u} A) ℤ)
    (x y : (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 0)
    (w : (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 1)
    (hw : (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).d 1 0 w = y - x) :
    (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj ⦋1⦌) ⟶ H
```

### 90.2 検収と現在地

コード **`1cac2d8b9`**。4本184行（Boundary 39、LowDegrees 67、RawChain 51、Cochain 27）。個別の結合検査 `/private/tmp/isw2-interval-cochain1.log` は終了コード0。鍵付き対象ビルド2,059 jobsと166モジュールの一時監査が終了コード0（`/private/tmp/isw2-build91.log`）。累計 **166モジュール・10,327行・1,758宣言、標準三公理のみ**。一時監査 `/private/tmp/AuditISW2G10HundredSixtySix.lean`、対象一覧 `/private/tmp/isw2-g10-hundredsixtysix-modules.txt`。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし。共有鍵は返却済み。上表の4本を登録対象へ追加する。

次は同じホモトピーの零次コチェインと次数−1成分をsmart切断へ送るデータの構成。そのため `NormalizedIntervalCycleData.lean` の作業木で既存のcyclesへの持ち上げと切断の項同型を使用している。未検証であり、上記実績に算入しない。A06本体と停止点2は未完。計算上限は上げていない。


## 91. A06本体：同じホモトピーから指定正規化区間の図式射を構成

smart切断の零次はcyclesへの持ち上げ、一次は次数−1の項同型で定義した。δh=f−g の規約なので辺には −h を入れる。この内部Homへの区間写像を、既存 `diagramTensorLinearHomEquiv` の逆で戻し、既存 `freeStandardSimplexParameterIso` で同じ自由負鎖の区間へ戻した。点ごとの選択やcylinderへの置換はしていない。

### 91.1 A06の同じ証明の分割の型

以下は一覧A06の構成・境界条件そのものの証明分割（§14）。前提計算枠・照合枠を新しく使わない。最初の二本では `A : Type u`、`[CommRing A]`、CycleDataでは `H : CochainComplex (ModuleCat.{u} A) ℤ` を固定する。Homでは `A : Type (max u v)`、`J : Type v`、`[SmallCategory J]`、`E := functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)`。

`NormalizedIntervalCycleData`

```lean
def intervalTruncCycle (z : H.X 0) (hz : H.d 0 1 z = 0) :
    (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 0
```

```lean
def intervalTruncEdge (w : H.X (-1)) :
    (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 1
```

```lean
theorem intervalTruncCycle_value (z : H.X 0) (hz : H.d 0 1 z = 0) :
    H.iCycles 0 ((H.truncLE'XIsoCycles (ComplexShape.embeddingUpIntLE 0)
      (i := 0) (i' := 0) (by simp)
      ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl)).hom
      (intervalTruncCycle A H z hz)) = z
```

```lean
theorem intervalTrunc_boundary (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x) :
    (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).d 1 0 (intervalTruncEdge A H w) =
      intervalTruncCycle A H y hy - intervalTruncCycle A H x hx
```

```lean
def normalizedIntervalCochainMapOfBoundary
    (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x) :
    (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ⟶ H
```


`HomotopyIntervalCochain`

```lean
def homotopyIntervalCochainMap (A : Type u) [CommRing A]
    {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
    {R S : CochainComplex C ℤ} (f g : R ⟶ S) (h : Homotopy f g) :
    (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj ⦋1⦌) ⟶ linearHomComplex A R S
```


`NormalizedIntervalHom`

```lean
def normalizedIntervalHom {R S : J ⥤ Complex A} (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
    R ⊗ freeNegativeChainsDiagram (A := A) ((Functor.const J).obj
      ((SSet.uliftFunctor.{max u v,0}).obj (SSet.stdSimplex.{0}.obj ⦋1⦌))) ⟶ S
```

### 91.2 検収と残り

コード **`959f883a5`**。新規3本140行（CycleData 79、HomotopyIntervalCochain 31、Hom 30）。結合個別検査 `/private/tmp/isw2-homotopy-interval1.log` と本体個別検査 `/private/tmp/isw2-diagram-interval1.log` が通り、鍵付き対象ビルドと一時監査はともに終了コード0。168本時点は2,061 jobs・1,779宣言（`/private/tmp/isw2-build92.log`）、本体追加後は既存の零次切断包含の依存も含め3,993 jobs・1,793宣言（`/private/tmp/isw2-build93.log`）。累計 **169モジュール・10,467行・1,793宣言、標準三公理のみ**。一時監査 `/private/tmp/AuditISW2G10HundredSixtyNine.lean`、対象一覧 `/private/tmp/isw2-g10-hundredsixtynine-modules.txt`。上の3本を登録対象に追加する。共有鍵は返却済み。

A06本体の射はできたが、両端の射がf,gに等しいことと前後合成の自然性は未完。作業木の `NormalizedIntervalVertexValues.lean` で零次生成元の値を照合中。A07以降・B/C/D・停止点2は未完。既存宣言、⑤a、入口、公式監査は変えていない。新公理・sorryなし、計算上限変更なし。A06前提計算は1/3、全体照合枠は3/3のまま。外枠12,500行まで検証済みから2,033行。凍結確定の連絡は未受領。


## 92. A06の指定された両端の厳密等式を完了

零次生成元での評価を、既存のsmart切断Hom回収式とcycles包含で計算した。零単体の増大写像の逆が単位の1を同じ生成元に送ること、元の頂点包含が同じ区間の頂点生成元へ送ることを確認した。内部Homにおける両端等式を、既存テンソル–Hom同値のパラメータ自然性と単位則で図式射の等式へ戻した。指定区間の作り直しも、型の弱化もしていない。

### 92.1 証明分割と前提計算の型

`DiagramTensorUnit` の単位則だけはA06の前提計算 **2/3** として追加する（既存の構成の単位法則）。残りは一覧A06の端点等式の同じ証明分割。照合枠は全体3/3のまま。VertexValuesとEndpointValuesでは `A : Type u`、`[CommRing A]` を固定。DiagramTensorUnitとHomEndpoints後半では `A : Type (max u v)`、`J : Type v`、`[SmallCategory J]`、`E := functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)`。

`NormalizedIntervalVertexValues`

```lean
def normalizedIntervalVertexGenerator (ε : Fin 2) :
    ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj ⦋1⦌)).X 0
```

```lean
theorem normalizedIntervalCochainMapOfBoundary_vertex
    (H : CochainComplex (ModuleCat.{u} A) ℤ)
    (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x) (ε : Fin 2) :
    (normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw).f 0
      (normalizedIntervalVertexGenerator A ε) = intervalVertexValue x y ε
```


`NormalizedIntervalEndpointValues`

```lean
theorem normalizedIntervalVertexGenerator_map (ε : Fin 2) :
    ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map
      (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ ε))).f 0
        (normalizedSimplexZeroGenerator A) = normalizedIntervalVertexGenerator A ε
```

```lean
theorem normalizedIntervalEndpointChain_value (ε : Fin 2) :
    (normalizedIntervalEndpointChain A ε).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) =
        normalizedIntervalVertexGenerator A ε
```

```lean
theorem normalizedIntervalCochainMapOfBoundary_endpoints
    (H : CochainComplex (ModuleCat.{u} A) ℤ)
    (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x) :
    normalizedIntervalEndpointChain A 0 ≫
      normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw =
        SerrePositivity.DifferentialGraded.unitFromCycle H ⟨x, hx⟩ ∧
    normalizedIntervalEndpointChain A 1 ≫
      normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw =
        SerrePositivity.DifferentialGraded.unitFromCycle H ⟨y, hy⟩
```


`DiagramTensorUnit`

```lean
theorem diagramTensorLinearHomEquiv_unit {R S : J ⥤ Complex A} (f : R ⟶ S) :
    diagramTensorLinearHomEquiv R S (𝟙_ (Complex A)) ((ρ_ R).hom ≫ f) =
      unitFromCycle (linearHomComplex A ((E).obj R) ((E).obj S))
        ⟨Cochain.ofHom ((E).map f), δ_ofHom ((E).map f)⟩
```


`NormalizedIntervalHomEndpoints`

```lean
theorem homotopyIntervalCochainMap_endpoints (A : Type u) [CommRing A]
    {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
    {R S : CochainComplex C ℤ} (f g : R ⟶ S) (h : Homotopy f g) :
    normalizedIntervalEndpointChain A 0 ≫ homotopyIntervalCochainMap A f g h =
      unitFromCycle (linearHomComplex A R S) ⟨Cochain.ofHom f, δ_ofHom f⟩ ∧
    normalizedIntervalEndpointChain A 1 ≫ homotopyIntervalCochainMap A f g h =
      unitFromCycle (linearHomComplex A R S) ⟨Cochain.ofHom g, δ_ofHom g⟩
```

```lean
theorem normalizedIntervalEndpoint_parameter (ε : Fin 2) :
    normalizedIntervalEndpoint A J ε ≫ (freeStandardSimplexParameterIso A J).hom.app ⦋1⦌ =
      (Functor.const J).map (normalizedIntervalEndpointChain A ε)
```

```lean
theorem normalizedIntervalHom_endpoints {R S : J ⥤ Complex A} (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
    (ρ_ R).inv ≫ (𝟙 R ⊗ₘ normalizedIntervalEndpoint A J 0) ≫
      normalizedIntervalHom f g h = f ∧
    (ρ_ R).inv ≫ (𝟙 R ⊗ₘ normalizedIntervalEndpoint A J 1) ≫
      normalizedIntervalHom f g h = g
```

### 92.2 検収と残り

コード **`c04dbbbbe`**。新規4本290行（VertexValues 71、EndpointValues 102、DiagramTensorUnit 42、HomEndpoints 75）。個別検査 `/private/tmp/isw2-interval-values4.log`、結合検査 `/private/tmp/isw2-interval-endpoint-values2.log`・`/private/tmp/isw2-interval-hom-endpoints2.log` は終了コード0。鍵付き対象ビルドと一時監査も終了コード0（`/private/tmp/isw2-build94.log`：171本・1,806宣言、`/private/tmp/isw2-build95.log`：4,000 jobs・173本・1,810宣言）。累計 **173モジュール・10,757行・1,810宣言、標準三公理のみ**。一時監査 `/private/tmp/AuditISW2G10HundredSeventyThree.lean`、一覧 `/private/tmp/isw2-g10-hundredseventythree-modules.txt`。上の4本を登録対象へ追加する。鍵は返却済み。

A06は本体と指定された両端の厳密等式まで完了。前後合成の自然性は未完で、作業木の `NormalizedIntervalChainNaturality.lean` で同じ自由鎖・正規化鎖評価の後合成を検査中。A07以降・B/C/Dと停止点2は未完。外枠12,500行まで検証済みから1,743行。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし、計算上限変更なし。凍結確定の連絡は未受領。


## 93. A06完了：本体・指定両端・全図式射の自然性

同じ自由区間の零次・一次の生成元計算で鎖評価の後合成自然性を示し、既存のsmart切断射のcycles公式・項同型で境界データを移した。既存 `normalizedChainsTruncationHomEquiv_postcomp` でコチェイン評価へ戻し、閉零次射による内部Homの前後合成を適用した。最後に既存テンソル–Homの始域・標的自然性とパラメータ同型の交換則で、元の図式射の自然性を得た。

A06は一覧の型どおり、本体 `normalizedIntervalHom`、指定された二端の厳密等式、全図式射についての前後合成自然性まで完了。ホモトピーの前後合成は右合成の後に左合成をする括弧を採用し、元の `a ≫ f ≫ b` の型に合わせた。新しいホモトピーを選んでいない。

### 93.1 同じA06の証明分割・前提計算の型

`DiagramTensorHomNaturality` の既存同値の前後合成自然性をA06の前提計算 **3/3** として追加。その他は同じ一覧A06の自然性の証明分割（§14）であり、照合枠は全体3/3のまま。最初の四本は `A : Type u` と `[CommRing A]`、HomotopyIntervalNaturalityではさらに `{C : Type v}` と `[Category.{u} C] [Preadditive C] [Linear A C]` を固定する。最後の二本は `A : Type (max u v)`、`J : Type v`、`[SmallCategory J]`、`E := functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)`。

`NormalizedIntervalChainNaturality`

```lean
theorem intervalRawChainMap_postcomp {K L : ChainComplex (ModuleCat.{u} A) ℕ} (q : K ⟶ L)
    (x y : K.X 0) (w : K.X 1) (hw : K.d 1 0 w = y - x)
    (hw' : L.d 1 0 (q.f 1 w) = q.f 0 y - q.f 0 x) :
    intervalRawChainMap A K x y w hw ≫ q =
      intervalRawChainMap A L (q.f 0 x) (q.f 0 y) (q.f 1 w) hw'
```

```lean
theorem intervalNormalizedChainMap_postcomp {K L : ChainComplex (ModuleCat.{u} A) ℕ} (q : K ⟶ L)
    (x y : K.X 0) (w : K.X 1) (hw : K.d 1 0 w = y - x)
    (hw' : L.d 1 0 (q.f 1 w) = q.f 0 y - q.f 0 x) :
    intervalNormalizedChainMap A K x y w hw ≫ q =
      intervalNormalizedChainMap A L (q.f 0 x) (q.f 0 y) (q.f 1 w) hw'
```


`NormalizedIntervalTruncationNaturality`

```lean
theorem intervalTruncCycle_naturality {H H' : CochainComplex (ModuleCat.{u} A) ℤ}
    (q : H ⟶ H') (z : H.X 0) (hz : H.d 0 1 z = 0) (hz' : H'.d 0 1 (q.f 0 z) = 0) :
    (truncLE'Map q (ComplexShape.embeddingUpIntLE 0)).f 0 (intervalTruncCycle A H z hz) =
      intervalTruncCycle A H' (q.f 0 z) hz'
```

```lean
theorem intervalTruncEdge_naturality {H H' : CochainComplex (ModuleCat.{u} A) ℤ}
    (q : H ⟶ H') (w : H.X (-1)) :
    (truncLE'Map q (ComplexShape.embeddingUpIntLE 0)).f 1 (intervalTruncEdge A H w) =
      intervalTruncEdge A H' (q.f (-1) w)
```


`NormalizedIntervalCochainNaturality`

```lean
theorem normalizedIntervalCochainMapOfBoundary_postcomp
    {H H' : CochainComplex (ModuleCat.{u} A) ℤ} (q : H ⟶ H')
    (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x)
    (hx' : H'.d 0 1 (q.f 0 x) = 0) (hy' : H'.d 0 1 (q.f 0 y) = 0)
    (hw' : H'.d (-1) 0 (q.f (-1) w) = q.f 0 y - q.f 0 x) :
    normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw ≫ q =
      normalizedIntervalCochainMapOfBoundary A H' (q.f 0 x) (q.f 0 y) hx' hy'
        (q.f (-1) w) hw'
```


`HomotopyIntervalNaturality`

```lean
def intervalHomPrePost {R R' S S' : CochainComplex C ℤ} (a : R' ⟶ R) (b : S ⟶ S') :
    linearHomComplex A R S ⟶ linearHomComplex A R' S'
```

```lean
theorem intervalHomPrePost_ofHom {R R' S S' : CochainComplex C ℤ}
    (a : R' ⟶ R) (b : S ⟶ S') (f : R ⟶ S) :
    (intervalHomPrePost A a b).f 0 (Cochain.ofHom f) = Cochain.ofHom (a ≫ f ≫ b)
```

```lean
theorem intervalHomPrePost_ofHomotopy {R R' S S' : CochainComplex C ℤ}
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S) (h : Homotopy f g) :
    (intervalHomPrePost A a b).f (-1) (-Cochain.ofHomotopy h) =
      -Cochain.ofHomotopy ((h.compRight b).compLeft a)
```

```lean
theorem homotopyIntervalCochainMap_naturality {R R' S S' : CochainComplex C ℤ}
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S) (h : Homotopy f g) :
    homotopyIntervalCochainMap A f g h ≫ intervalHomPrePost A a b =
      homotopyIntervalCochainMap A (a ≫ f ≫ b) (a ≫ g ≫ b)
        ((h.compRight b).compLeft a)
```


`DiagramTensorHomNaturality`

```lean
theorem diagramTensorLinearHomEquiv_naturality {R R' S S' : J ⥤ Complex A}
    (T : Complex A) (a : R' ⟶ R) (b : S ⟶ S') (t : R ⊗ (Functor.const J).obj T ⟶ S) :
    diagramTensorLinearHomEquiv R' S' T (((a ▷ (Functor.const J).obj T) ≫ t) ≫ b) =
      diagramTensorLinearHomEquiv R S T t ≫ intervalHomPrePost A ((E).map a) ((E).map b)
```


`NormalizedIntervalHomNaturality`

```lean
def normalizedIntervalHomotopyPrePost {R R' S S' : J ⥤ Complex A}
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
    Homotopy ((E).map (a ≫ f ≫ b)) ((E).map (a ≫ g ≫ b))
```

```lean
theorem normalizedIntervalHom_naturality {R R' S S' : J ⥤ Complex A}
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
    (a ⊗ₘ 𝟙 (freeNegativeChainsDiagram (A := A) ((Functor.const J).obj
      ((SSet.uliftFunctor.{max u v,0}).obj (SSet.stdSimplex.{0}.obj ⦋1⦌))))) ≫
        normalizedIntervalHom f g h ≫ b =
      normalizedIntervalHom (a ≫ f ≫ b) (a ≫ g ≫ b)
        (normalizedIntervalHomotopyPrePost a b f g h)
```

### 93.2 検収

コード **`b86733b2c`**（最初の4本228行）・**`38c1d4b8d`**（最後の2本94行）。個別・結合検査は終了コード0（`/private/tmp/isw2-interval-raw-nat2.log`、`/private/tmp/isw2-trunc-nat2.log`、`/private/tmp/isw2-cochain-interval-nat2.log`、`/private/tmp/isw2-hom-interval-nat2.log`、`/private/tmp/isw2-diagram-interval-nat2.log`、`/private/tmp/isw2-interval-hom-nat3.log`）。鍵付き対象ビルドと一時監査も終了コード0。

| 検収 | 対象ビルド | 累計モジュール | 累計宣言 | ログ |
| --- | --- | --- | --- | --- |
| 鎖・切断・コチェイン自然性 | 2,396 jobs | 176 | 1,815 | `/private/tmp/isw2-build96.log` |
| 内部Hom前後合成 | 2,398 jobs | 177 | 1,826 | `/private/tmp/isw2-build97.log` |
| 元の図式射の自然性（A06完了） | 3,999 jobs | 179 | 1,831 | `/private/tmp/isw2-build98.log` |

すべて標準三公理のみ。累計 **179モジュール・11,079行・1,831宣言**。一時監査 `/private/tmp/AuditISW2G10HundredSeventyNine.lean`、対象一覧 `/private/tmp/isw2-g10-hundredseventynine-modules.txt`。上の6本を登録対象に追加する。共有鍵は返却済み。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし、計算上限変更なし。凍結確定の連絡は未受領。

### 93.3 次の一覧項目A07への接続と残り

A07では、全余単体方向の指定ホモトピーを各単体次数で評価し、今の `normalizedIntervalHom` を使う。入力のn単体（`G.obj n ⟶ Q`）と区間のn単体（`⦋n⦌ ⟶ ⦋1⦌`）に対し、指定余作用 `δ.app n`、同じ正規化単体射、区間評価、入力射を順に合成する。単体作用素との可換性にはδの自然性とA06の前後合成自然性、両端にはA05の指定単位則とA06の両端等式を使う。二重図式のホモトピーを次数ごとに独立に選ばない。元の全パラメータの自然な成分を評価して使う。

A07以降、B・C・Dの各まとまり、停止点2は未完。本節はA06完了の途中報告であり、停止点2の検収報告ではない。検証済みは外枠12,500行まで残り1,421行。範囲・型は弱めていない。


## 94. A07完了：指定余作用から全単体Homのホモトピーへ

11-13のユーザー承認で3b-2の外枠は **14,500行**。一覧と§14の補題の数え方は維持する。23時の調整役の連絡で、今回のB3はmainだけの凍結と確定し、この枝は作業・コミットを続けてよい。今夜は対象ビルドと新規モジュールの小さな一時監査だけを実行し、mainは取り込まない。B4は追って指定される改名コマンドを待つ。

A07は、同じ二重図式のホモトピーを積添字へ戻してA06へ入れ、指定区間評価を全余単体方向で自然な射にした。指定余作用、区間の単体、区間評価、入力射を合成した区間射を定義し、その単体自然性・両端を示した。点ごとにホモトピーを選んでいない。

### 94.1 A07の証明分割と前提計算の型

`StandardParameterConstant.standardParameter_constant` だけをA07の前提計算 **1/3** とする（既存の増大写像・端点の余単位則）。残りは一覧A07の同じ構成と端点・単体自然性の証明分割（§14）。照合枠は3/3のまま。FrameIntervalHom中の局所`hm`は既存 `Functor.map_id` の適用であり、新しい法則の証明ではない：

```lean
have hm (W : SimplicialObject (ModuleCat A)) :
    AlgebraicTopology.NormalizedMooreComplex.map (𝟙 W) = 𝟙 _ :=
  (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map_id W
```

型の略記：FrameParameterEvaluation・Endpoints・UnderlyingMapでは `{C : Type u} [Category.{v} C] [MonoidalCategory C]`、`{F G P : SimplexCategory ⥤ C}`。FrameIntervalHom・FrameHomHomotopyは `A : Type (max u v)`、`J : Type v`、`[SmallCategory J]`、`D := J ⥤ Complex A`、`P := liftedStandardSimplexParameter J ⋙ freeNegativeChainsDiagramFunctor A J`、`I := P.obj ⦋1⦌`。EEは§73の二重図式交換関手。UncurriedDiagramHomotopyのE₁・E₂は同ファイルと既存CurriedDiagramHomotopyの定義どおり。すべてのAに`[CommRing A]`を固定。

`UncurriedDiagramHomotopy`

```lean
def uncurriedDiagramHomotopy {F G : J ⥤ K ⥤ HomologicalComplex C c} (f g : F ⟶ G)
    (h : Homotopy ((E₂).map f) ((E₂).map g)) :
    Homotopy ((E₁).map (Functor.uncurry.map f)) ((E₁).map (Functor.uncurry.map g))
```


`FrameIntervalHom`

```lean
def frameIntervalHom {F G : SimplexCategory ⥤ D} (f g : F ⟶ G)
    (h : Homotopy ((EE).map f) ((EE).map g)) :
    F ⊗ (Functor.const SimplexCategory).obj I ⟶ G
```

```lean
theorem frameIntervalHom_endpoints {F G : SimplexCategory ⥤ D} (f g : F ⟶ G)
    (h : Homotopy ((EE).map f) ((EE).map g)) :
    (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map
      (normalizedIntervalEndpoint A J 0)) ≫ frameIntervalHom f g h = f ∧
    (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map
      (normalizedIntervalEndpoint A J 1)) ≫ frameIntervalHom f g h = g
```


`FrameParameterEvaluation`

```lean
def frameParameterEvaluation (δ : F ⟶ F ⊗ P)
    (k : F ⊗ (Functor.const SimplexCategory).obj (P.obj ⦋1⦌) ⟶ G)
    (n : SimplexCategory) (t : n ⟶ ⦋1⦌) : F.obj n ⟶ G.obj n
```

```lean
theorem frameParameterEvaluation_naturality (δ : F ⟶ F ⊗ P)
    (k : F ⊗ (Functor.const SimplexCategory).obj (P.obj ⦋1⦌) ⟶ G)
    {m n : SimplexCategory} (s : m ⟶ n) (t : n ⟶ ⦋1⦌) :
    F.map s ≫ frameParameterEvaluation δ k n t =
      frameParameterEvaluation δ k m (s ≫ t) ≫ G.map s
```


`FrameParameterEndpoints`

```lean
theorem frameParameterEvaluation_endpoint
    (δ : F ⟶ F ⊗ P) (α : P ⟶ 𝟙_ (SimplexCategory ⥤ C))
    (hδ : δ ≫ (𝟙 F ⊗ₘ α) ≫ (ρ_ F).hom = 𝟙 F)
    (k : F ⊗ (Functor.const SimplexCategory).obj (P.obj ⦋1⦌) ⟶ G)
    (e : 𝟙_ C ⟶ P.obj ⦋1⦌) (f : F ⟶ G)
    (hk : (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map e) ≫ k = f)
    (n : SimplexCategory) (t : n ⟶ ⦋1⦌) (ht : P.map t = α.app n ≫ e) :
    frameParameterEvaluation δ k n t = f.app n
```


`FrameHomotopyUnderlyingMap`

```lean
def frameHomotopyUnderlyingMap (δ : F ⟶ F ⊗ P)
    (k : F ⊗ (Functor.const SimplexCategory).obj (P.obj ⦋1⦌) ⟶ G) (Q : C) :
    (cosimplicialHom G).obj Q ⊗ (SSet.stdSimplex.{v}.obj ⦋1⦌) ⟶ (cosimplicialHom F).obj Q
```


`StandardParameterConstant`

```lean
theorem standardParameter_constant (n : SimplexCategory) (ε : Fin 2) :
    (liftedStandardSimplexParameter J ⋙ freeNegativeChainsDiagramFunctor A J).map
      (SimplexCategory.const n ⦋1⦌ ε) =
    (standardParameterAugmentation A J).app n ≫ normalizedIntervalEndpoint A J ε
```


`FrameHomHomotopy`

```lean
def frameHomHomotopyOfInterval {F G : SimplexCategory ⥤ D}
    (δ : F ⟶ F ⊗ P)
    (hδ : δ ≫ (𝟙 F ⊗ₘ standardParameterAugmentation A J) ≫ (ρ_ F).hom = 𝟙 F)
    (k : F ⊗ (Functor.const SimplexCategory).obj ((P).obj ⦋1⦌) ⟶ G)
    (f g : F ⟶ G)
    (hk0 : (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map
      (normalizedIntervalEndpoint A J 0)) ≫ k = f)
    (hk1 : (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map
      (normalizedIntervalEndpoint A J 1)) ≫ k = g) (Q : D) :
    SSet.Homotopy ((cosimplicialHomMap f).app Q) ((cosimplicialHomMap g).app Q)
```

```lean
def frameHomHomotopyOfChainHomotopy (F G : SimplexCategory ⥤ D)
    (δ : F ⟶ F ⊗ P)
    (hδ : δ ≫ (𝟙 F ⊗ₘ standardParameterAugmentation A J) ≫ (ρ_ F).hom = 𝟙 F)
    (f g : F ⟶ G) (h : Homotopy ((EE).map f) ((EE).map g)) (Q : D) :
    SSet.Homotopy ((cosimplicialHomMap f).app Q) ((cosimplicialHomMap g).app Q)
```

### 94.2 検収と登録対象

コード **`9f1fb0f95`**。新規7本339行（UncurriedDiagramHomotopy 34、FrameIntervalHom 73、FrameParameterEvaluation 38、FrameParameterEndpoints 41、FrameHomotopyUnderlyingMap 34、StandardParameterConstant 48、FrameHomHomotopy 71）。個別・結合検査は最終的に終了コード0（`/private/tmp/isw2-frame-interval9.log`、`/private/tmp/isw2-frame-hom-map2.log`、`/private/tmp/isw2-standard-parameter-constant2.log`、`/private/tmp/isw2-frame-hom-homotopy3.log`）。途中の対象ビルド99・100の失敗は、定数区間の恒等射と端点計算の結合順序を明示して修正した。計算上限は上げていない。

鍵付きの最終対象ビルドは **4,008 jobs、終了コード0**（`/private/tmp/isw2-build101.log`）。今夜の連絡に合わせ、監査は新規7モジュールだけ：**58宣言、標準三公理のみ**（`/private/tmp/AuditISW2G10A07.lean`）。既検収179本・1,831宣言と合わせた累計は **186モジュール・11,418行・1,889宣言**。累計対象一覧 `/private/tmp/isw2-g10-hundredeightysix-modules.txt`。上記7本を登録対象へ追加する（共通1本・DiagramComparison6本）。共有鍵は返却済み。

新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし。外枠14,500行まで残り3,082行。A07完了、A08は既存の二つのEZホモトピーをA07へ入れる個別検査が通っており、A09の同じ指定射の同値性へ接続中。A08以降は本節の検収数に未算入。B・C・Dと停止点2は未完。


## 95. A08・A09完了：指定比較自身に同じshuffleの逆を与えた

A08は既存の全余単体AW・shuffleの両合成のEZホモトピーに、A05の指定余作用とA07を適用した。A09は既存 `freeTensorDiagramHomIso`・`freeProductSectionsHomIso` の間でこの二つの実ホモトピーを前後合成し、`normalizedWeightSectionMap` 自身の逆を既存 `normalizedWeightSectionReverse` として与えた。別の同値は選ばず、Kan性や模型圏の仮定も追加していない。

### 95.1 一覧A08・A09の型

A08は `A : Type (max u v)`、`J : Type v`、`[SmallCategory J]`、`W : J ⥤ SSet.{max u v}`、`φ : simplicialRingCoefficient.{max u v} →+* A`、`P := standardParameterForCoefficients A J`。A09は既存入口と同じ `A : Type u`、`J : Type u`、`[SmallCategory J]`、`W : J ⥤ SSet.{u}`、`Q : J ⥤ CochainComplex (ModuleCat A) ℤ`、`φ : simplicialRingCoefficient.{u} →+* A`。いずれも`[CommRing A]`を固定。追加の前提計算枠・照合枠は使っていない。

`FreeProductHomComparisonHomotopies`

```lean
def freeProductHomComparison_homotopy (Q : J ⥤ CochainComplex (ModuleCat A) ℤ) :
    SSet.Homotopy
      ((freeProductHomReverse A W P φ).app Q ≫ (freeProductHomComparison A W P φ).app Q)
      (𝟙 _)
```

```lean
def freeProductHomReverse_homotopy (Q : J ⥤ CochainComplex (ModuleCat A) ℤ) :
    SSet.Homotopy
      ((freeProductHomComparison A W P φ).app Q ≫ (freeProductHomReverse A W P φ).app Q)
      (𝟙 _)
```


`NormalizedWeightSectionEquivalence`

```lean
theorem normalizedWeightSectionMap_equivalence :
    IsSimplicialHomotopyEquivalence (normalizedWeightSectionMap A W Q φ)
```

### 95.2 検収と残り

コード **`c3000d7aa`**。新規2本84行（FreeProductHomComparisonHomotopies 45、NormalizedWeightSectionEquivalence 39）。個別・結合検査 `/private/tmp/isw2-product-hom-homotopies2.log`・`/private/tmp/isw2-weight-section-equiv1.log` は終了コード0。鍵付き対象ビルド **4,400 jobs、終了コード0**、新規2モジュールだけの一時監査 **11宣言、標準三公理のみ**（`/private/tmp/isw2-build102.log`、`/private/tmp/AuditISW2G10A08A09.lean`）。既検収と合わせた累計は **188モジュール・11,502行・1,900宣言**。一覧 `/private/tmp/isw2-g10-hundredeightyeight-modules.txt`。上記2本を登録対象へ追加。鍵は返却済み。

A10の自由テンソルHom同型の標的自然性の型が既定の200,000 heartbeatsに当たったため、既存の図式Homの標的射を明示する `DiagramHomTargetMap` とその転置の特殊化に分けて検査している。計算上限を上げず、既存宣言も変えていない。これは同じ一覧A10の構成・自然性の分割であり、新しい数学のまとまりを足していない。A10以降・B/C/D・停止点2は未完。外枠14,500行まで検証済みから2,998行。新公理・sorryなし、⑤a・入口・公式監査の変更なし。


## 96. A10完了：指定比較の標的の全図式射自然性

Γ側では同じ図式Homの標的射を明示し、切断側では元の`weightedSectionsFunctor`の射を使った。自由テンソルHom同型・自由積Hom同型・指定AW比較の三つの自然性を合成し、一覧A10の等式を閉じた。型推論の200,000 heartbeats超過は、基礎圏と宇宙引数の明示、図式Hom標的射の分離、同型の逆の自然性の相殺による証明で解消した。計算上限は変更していない。

### 96.1 A10の型と前提計算枠

`NormalizedTensorHomTargetNaturality`をA10の前提計算 **1/3**、`ProductSectionsTargetNaturality`の自然性を **2/3** とする。後者の標準単体Hom同型の自然性は、同じ積Hom同型の証明の分割。`DiagramHomTargetMap`と転置の特殊化は同じA10のHmapの構成と既存A06の自然性の特殊化であり、新しい数学ではない。照合枠は全体3/3のまま。

最初のファイルは `A : Type (max u v)`、`J : Type v`、`[SmallCategory J]`、`E := functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)`。他は既存入口と同じ `A : Type u`、`J : Type u`、`[SmallCategory J]`、`W : J ⥤ SSet.{u}`（すべて`[CommRing A]`）。最後の型では `φ : simplicialRingCoefficient.{u} →+* A`。

`DiagramHomTargetMap`

```lean
def diagramHomTargetMap (P : J ⥤ Complex A) {Q Q' : J ⥤ Complex A} (f : Q ⟶ Q') :
    linearHomComplex A ((E).obj P) ((E).obj Q) ⟶ linearHomComplex A ((E).obj P) ((E).obj Q')
```

```lean
theorem diagramTensorLinearHomEquiv_postcomp (P : J ⥤ Complex A)
    {Q Q' : J ⥤ Complex A} (T : Complex A) (t : P ⊗ (Functor.const J).obj T ⟶ Q)
    (f : Q ⟶ Q') :
    diagramTensorLinearHomEquiv P Q' T (t ≫ f) =
      diagramTensorLinearHomEquiv P Q T t ≫ diagramHomTargetMap P f
```


`NormalizedTensorHomTargetNaturality`

```lean
theorem freeTensorDiagramHomIso_target_naturality {Q Q' : J ⥤ Complex A} (f : Q ⟶ Q') :
    (cosimplicialHom (freeTensorFrame A W (liftedStandardSimplexParameter J))).map f ≫
      (freeTensorDiagramHomIso.{u,u} A Q' W).hom =
    (freeTensorDiagramHomIso.{u,u} A Q W).hom ≫ (truncatedDoldKanFunctor A).map
      (diagramHomTargetMap.{u,u} (freeNegativeChainsDiagram (A := A) W) f)
```


`ProductSectionsTargetNaturality`

```lean
theorem liftedStandardSimplexHomIso_naturality {Z Z' : SSet.{u}} (f : Z ⟶ Z') :
    (cosimplicialHom (SSet.stdSimplex.{0} ⋙ SSet.uliftFunctor.{u,0})).map f ≫
      (liftedStandardSimplexHomIso Z').hom = (liftedStandardSimplexHomIso Z).hom ≫ f
```

```lean
theorem freeProductSectionsHomIso_target_naturality (W : J ⥤ SSet.{u})
    {Q Q' : J ⥤ CochainComplex (ModuleCat A) ℤ} (f : Q ⟶ Q') :
    (cosimplicialHom (freeProductFrame A W (liftedStandardSimplexParameter J))).map f ≫
      (freeProductSectionsHomIso A W Q').hom =
    (freeProductSectionsHomIso A W Q).hom ≫ (weightedSectionsFunctor W).map
      ((Functor.whiskeringRight J (CochainComplex (ModuleCat A) ℤ) SSet.{u}).obj
        (SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A) |>.map f)
```


`NormalizedWeightSectionNaturality`

```lean
theorem normalizedWeightSectionMap_naturality {Q Q' : J ⥤ Complex A} (f : Q ⟶ Q') :
    (truncatedDoldKanFunctor A).map
      (diagramHomTargetMap.{u,u} (freeNegativeChainsDiagram (A := A) W) f) ≫
        normalizedWeightSectionMap A W Q' φ =
    normalizedWeightSectionMap A W Q φ ≫ (weightedSectionsFunctor W).map
      ((Functor.whiskeringRight J (Complex A) SSet.{u}).obj (truncatedDoldKanFunctor A) |>.map f)
```

### 96.2 検収と登録対象

コード **`36b42f9be`**。新規4本174行（DiagramHomTargetMap 32、NormalizedTensorHomTargetNaturality 44、ProductSectionsTargetNaturality 47、NormalizedWeightSectionNaturality 51）。最終結合個別検査 `/private/tmp/isw2-weight-section-nat5.log` は終了コード0。鍵付き対象ビルド **2,655 jobs、終了コード0**、新規4モジュールだけの一時監査 **10宣言、標準三公理のみ**（`/private/tmp/isw2-build103.log`、`/private/tmp/AuditISW2G10A10.lean`）。上記4本を登録対象に追加。累計対象一覧 `/private/tmp/isw2-g10-hundredninetytwo-modules.txt`。

既検収分と合わせて **192モジュール・11,676行・1,910宣言**。外枠14,500行まで残り2,824行。共有鍵は返却済み。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし。今夜の監査は新規分だけで、root・大きい累計監査は流していない。A10まで完了、A11以降・B/C/D・停止点2は未完。

### 96.3 次の一覧A11への接続（紙）

A11の切断側は既存 `WeightedRestriction.weightedSectionsPre`（実名前空間はKerodon.LimitsAndColimits.HomotopyLimitsAndColimits）を使う。`weightedSectionsUncurry_comp_pre`が元のパラメータ付き自然変換の前合成との等式を持ち、任意の重みの射に使える。Γ側は `intervalHomPrePost` の後側を恒等射に固定し、前側に元の自由鎖図式の射を入れる。型の具体化は以下（`N := freeNegativeChainsDiagramFunctor A J`、Eは上記交換関手）：

```lean
-- §73 A11。まだ未実装・未検収。
theorem normalizedWeightSectionMap_weight_naturality
    {W W' : J ⥤ SSet.{u}} (w : W' ⟶ W) :
    (truncatedDoldKanFunctor A).map
      (intervalHomPrePost A ((E).map ((N).map w)) (𝟙 ((E).obj Q))) ≫
        normalizedWeightSectionMap A W' Q φ =
      normalizedWeightSectionMap A W Q φ ≫ weightedSectionsPre w (Q ⋙ truncatedDoldKanFunctor A)
```

自由テンソル側には既存 `diagramTensorLinearHomEquiv_naturality` の前側の特殊化、自由積側には元の随伴Homの始域自然性と`weightedSectionsUncurry_comp_pre`、中間のAWには既存 `freeProductDiagramAW_naturality` を使う。別の重みの置換や別のHom同値を選ばず、元の二同型の始域自然性を照合してA10と同じ合成で結ぶ方針。


## 97. A11完了：元の重みの全射に対する指定比較の自然性

今回のgoal「Dまで進めてください」はactiveのまま。前回のgoal turnはA07〜A10の検証済みコード・報告を保存した進捗で、今回は枝がクリーンで`f594ede20`まであることを確かめてA11へ進んだ。

同じ自由鎖関手に重み射を入れ、自由積・自由テンソルのframe射と指定AWの可換性を束ねた。Γ側は同じ図式Homの前合成、切断側は既存`weightedSectionsPre`。自由テンソルHomには既存の転置の始域自然性とパラメータ同型のテンソル交換則、自由積Homには元の随伴Hom回収式と`weightedSectionsUncurry_comp_pre`を使い、一覧A11の指定射自身の等式を閉じた。

### 97.1 一覧A11の分割の型と枠

`NormalizedTensorHomSourceNaturality`はA11の前提計算 **1/3**。`WeightedAdjunctionSourceNaturality`と`ProductSectionsSourceNaturality`は同じ自由積Hom同型の自然性を段に分けたA11の前提計算 **2/3**。他は一覧A11のHpre・frame射の構成と主張の証明分割。照合枠は全体3/3のまま。既存宣言・計算上限は変えていない。

略記：Eは `functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)`。DiagramHomSourceMapは`A : Type (max u v)`・`J : Type v`・`[SmallCategory J]`。FreeFrameWeightMapsは`A : Type u`・`J : Type v`・`[Category.{w} J]`・`N := freeNegativeChainsDiagramFunctor A J`。他は既存入口と同じ`A : Type u`・`J : Type u`・`[SmallCategory J]`。すべての係数環は`[CommRing A]`。

`DiagramHomSourceMap`

```lean
def diagramHomSourceMap {P P' : J ⥤ Complex A} (a : P' ⟶ P) (Q : J ⥤ Complex A) :
    linearHomComplex A ((E).obj P) ((E).obj Q) ⟶ linearHomComplex A ((E).obj P') ((E).obj Q)
```

```lean
theorem diagramTensorLinearHomEquiv_source {P P' Q : J ⥤ Complex A}
    (T : Complex A) (a : P' ⟶ P) (t : P ⊗ (Functor.const J).obj T ⟶ Q) :
    diagramTensorLinearHomEquiv P' Q T ((a ▷ (Functor.const J).obj T) ≫ t) =
      diagramTensorLinearHomEquiv P Q T t ≫ diagramHomSourceMap a Q
```


`FreeFrameWeightMaps`

```lean
def freeProductFrameWeightMap : freeProductFrame A W' P ⟶ freeProductFrame A W P
```

```lean
def freeTensorFrameWeightMap : freeTensorFrame A W' P ⟶ freeTensorFrame A W P
```

```lean
theorem freeProductFrameAW_weight_naturality (φ : simplicialRingCoefficient.{u} →+* A) :
    freeProductFrameWeightMap A a P ≫ freeProductFrameAW A W P φ =
      freeProductFrameAW A W' P φ ≫ freeTensorFrameWeightMap A a P
```


`NormalizedTensorHomSourceNaturality`

```lean
theorem freeTensorDiagramHomIso_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (Q : J ⥤ Complex A) :
    (cosimplicialHomMap (freeTensorFrameWeightMap A w (liftedStandardSimplexParameter J))).app Q ≫
      (freeTensorDiagramHomIso.{u,u} A Q W').hom =
    (freeTensorDiagramHomIso.{u,u} A Q W).hom ≫ (truncatedDoldKanFunctor A).map
      (diagramHomSourceMap.{u,u} ((freeNegativeChainsDiagramFunctor A J).map w) Q)
```


`WeightedAdjunctionSourceNaturality`

```lean
theorem weightedSectionsAdjunction_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (K : SSet.{u}) (H : J ⥤ SSet.{u}) (s : W ⊗ (Functor.const J).obj K ⟶ H) :
    (weightedSectionsAdjunction W').homEquiv K H ((w ▷ (Functor.const J).obj K) ≫ s) =
      (weightedSectionsAdjunction W).homEquiv K H s ≫ weightedSectionsPre w H
```

```lean
theorem freeWeightedAdjunction_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (K : SSet.{u}) (Q : J ⥤ CochainComplex (ModuleCat A) ℤ)
    (s : (freeNegativeChainsDiagramFunctor A J).obj (W ⊗ (Functor.const J).obj K) ⟶ Q) :
    ((weightedSectionsAdjunction W').comp (freeNegativeChainsDiagramAdjunction A J)).homEquiv K Q
      ((freeNegativeChainsDiagramFunctor A J).map (w ▷ (Functor.const J).obj K) ≫ s) =
    ((weightedSectionsAdjunction W).comp (freeNegativeChainsDiagramAdjunction A J)).homEquiv K Q s ≫
      weightedSectionsPre w (Q ⋙ SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A)
```


`ProductSectionsSourceNaturality`

```lean
theorem freeProductSectionsHomIso_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (Q : J ⥤ CochainComplex (ModuleCat A) ℤ) :
    (cosimplicialHomMap (freeProductFrameWeightMap A w (liftedStandardSimplexParameter J))).app Q ≫
      (freeProductSectionsHomIso A W' Q).hom =
    (freeProductSectionsHomIso A W Q).hom ≫
      weightedSectionsPre w (Q ⋙ SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A)
```


`NormalizedWeightSectionSourceNaturality`

```lean
theorem normalizedWeightSectionMap_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (Q : J ⥤ Complex A) (φ : simplicialRingCoefficient.{u} →+* A) :
    (truncatedDoldKanFunctor A).map
      (diagramHomSourceMap.{u,u} ((freeNegativeChainsDiagramFunctor A J).map w) Q) ≫
        normalizedWeightSectionMap A W' Q φ =
    normalizedWeightSectionMap A W Q φ ≫ weightedSectionsPre w (Q ⋙ truncatedDoldKanFunctor A)
```

### 97.2 検収・登録対象

コード **`08a27be94`**。新規6本284行（DiagramHomSourceMap 29、FreeFrameWeightMaps 45、NormalizedTensorHomSourceNaturality 56、WeightedAdjunctionSourceNaturality 48、ProductSectionsSourceNaturality 49、NormalizedWeightSectionSourceNaturality 57）。個別・結合検査は終了コード0（`/private/tmp/isw2-tensor-hom-source-nat3.log`、`/private/tmp/isw2-weighted-adj-source2.log`、`/private/tmp/isw2-weight-section-source-nat2.log`）。

鍵付き対象ビルドは、最初の4本 **2,657 jobs**・最後の2本 **2,659 jobs**、どちらも終了コード0（`/private/tmp/isw2-build104.log`・`/private/tmp/isw2-build105.log`）。監査は新規分だけで、前者 **24宣言**・後者 **6宣言**、すべて標準三公理のみ（`/private/tmp/AuditISW2G10A11Parts.lean`・`/private/tmp/AuditISW2G10A11Finish.lean`）。共有鍵は返却済み。

累計 **198モジュール・11,960行・1,940宣言**。対象一覧 `/private/tmp/isw2-g10-hundredninetyeight-modules.txt`。上記6本を登録対象へ追加する。外枠14,500行まで残り2,540行。新公理・sorryなし、⑤a・入口・公式監査の変更なし。mainのB3凍結中なので取り込みは行っていない。

### 97.3 報告の型引用の訂正と次

§91〜96の五つの型引用（intervalTruncCycle_value、normalizedIntervalHom、normalizedIntervalHom_naturality、freeTensorDiagramHomIso_target_naturality、normalizedWeightSectionMap_naturality）が名前付き引数の`:=`で途中までになっていたため、既検収ソースの完全な型に直した。Leanの宣言には変更がない。抽出は括弧の深さを見て宣言本体の`:=`と区別する方法にした。

A11まで完了、A12・B/C/D・停止点2は未完。A12では、既存の `normalizedBousfieldKanHom` の二重反対圏の添字と、`liftedClosedDiagram` のAsSmall添字を、同じ`smallBousfieldKanWeightDown`とULift・反転の指定射で接続する。`smallBousfieldKanWeightDown`の現在の宣言は射だけを供給しているため、可逆性の既存道具と同じ射の逆の構成を確認中。これは§73 A12に初めから含めた持ち上げの照合であり、別の同値へ置換しない。


## 98. A12の途中：指定AsSmall重みとHom添字の可逆な移送

既存 `smallBousfieldKanWeightDown` の順射は変更せず、over圏の構造射と全射を元の`AsSmall.up`で持ち上げる逆を構成した。up・downの二合成は厳密な関手の等式で、全次数で同じoverの射列を保つ。その指定重み同型の前合成を、既存`weightedSectionsPre`の二逆則で切断の同型へ送る部品を作った。

同時に、図式複体のAsSmall.downによる制限で、元の線形Hom複体を同じコチェイン成分のup・downで移す同型を作った。微分との可換性は既存`δ_map`による。対象ごとの任意のHom同値は選ばない。

### 98.1 同じ一覧A12の証明分割の型

下記は§73 A12に含めたAsSmall・ULiftとΓ Homの照合の分割であり、一覧外の新しい数学のまとまりではない。前提計算枠・照合枠は追加で使っていない。SmallOverLift・SmallBousfieldKanWeightIsoは`J : Type`・`[SmallCategory J]`、WeightedRestrictionIsoは`I : Type u`・`[SmallCategory I]`・`{W W' : I ⥤ SSet.{u}}`、AsSmallLinearHomは`A : Type u`・`[CommRing A]`・`J : Type`・`[SmallCategory J]`。

`SmallOverLift`

```lean
def smallOverLift (j : AsSmall.{u} J) : Over ((AsSmall.down : AsSmall.{u} J ⥤ J).obj j) ⥤ Over j
```

```lean
theorem smallOverLift_down (j : AsSmall.{u} J) :
    smallOverLift j ⋙ Over.post (AsSmall.down : AsSmall.{u} J ⥤ J) = 𝟭 _
```

```lean
theorem smallOverDown_lift (j : AsSmall.{u} J) :
    Over.post (AsSmall.down : AsSmall.{u} J ⥤ J) ⋙ smallOverLift j = 𝟭 _
```


`SmallBousfieldKanWeightIso`

```lean
instance smallBousfieldKanWeightDown_isIso : IsIso (smallBousfieldKanWeightDown.{u} J)
```

```lean
def smallBousfieldKanWeightIso :
    bousfieldKanWeight (AsSmall.{u} J) ≅
      (AsSmall.down : AsSmall.{u} J ⥤ J) ⋙ bousfieldKanWeight J ⋙ SSet.uliftFunctor.{u,0}
```

```lean
theorem smallBousfieldKanWeightIso_hom :
    (smallBousfieldKanWeightIso.{u} J).hom = smallBousfieldKanWeightDown J
```


`WeightedRestrictionIso`

```lean
def weightedSectionsWeightIso (e : W ≅ W') (H : I ⥤ SSet.{u}) :
    weightedSections W' H ≅ weightedSections W H
```

```lean
theorem weightedSectionsWeightIso_hom (e : W ≅ W') (H : I ⥤ SSet.{u}) :
    (weightedSectionsWeightIso e H).hom = weightedSectionsPre e.hom H
```


`AsSmallLinearHom`

```lean
def asSmallComplexRestriction :
    CochainComplex (J ⥤ ModuleCat.{u} A) ℤ ⥤ CochainComplex (AsSmall.{u} J ⥤ ModuleCat.{u} A) ℤ
```

```lean
def asSmallHomCochainEquiv (P Q : CochainComplex (J ⥤ ModuleCat.{u} A) ℤ) (n : ℤ) :
    Cochain P Q n ≃ₗ[A]
      Cochain ((asSmallComplexRestriction A J).obj P) ((asSmallComplexRestriction A J).obj Q) n
```

```lean
def asSmallLinearHomIso (P Q : CochainComplex (J ⥤ ModuleCat.{u} A) ℤ) :
    linearHomComplex A P Q ≅
      linearHomComplex A ((asSmallComplexRestriction A J).obj P) ((asSmallComplexRestriction A J).obj Q)
```

### 98.2 検収と登録対象

コード **`ae5bd1dcf`**（最初の3本103行）・**`7e8efb382`**（AsSmallLinearHom 59行）。個別・結合検査 `/private/tmp/isw2-small-bk-weight-iso2.log`、`/private/tmp/isw2-weighted-restriction-iso1.log`、`/private/tmp/isw2-as-small-linear-hom2.log` は終了コード0。計算上限は上げていない。

鍵付き対象ビルドは **1,686 jobs**・**1,841 jobs**、いずれも終了コード0（`/private/tmp/isw2-build106.log`・`/private/tmp/isw2-build107.log`）。監査は新規分だけ：最初の3本 **13宣言**、最後の1本 **13宣言**、すべて標準三公理のみ（`/private/tmp/AuditISW2G10A12Lift.lean`・`/private/tmp/AuditISW2G10A12Hom.lean`）。鍵は返却済み。

累計 **202モジュール・12,122行・1,966宣言**。対象一覧 `/private/tmp/isw2-g10-twohundredtwo-modules.txt`。上記4本を登録対象に追加する（DiagramComparison3本、KerodonのHomotopyLimitsAndColimits1本）。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし。外枠14,500行まで残り2,378行。mainのB3凍結中なので、枝内でのコミットだけを行った。

### 98.3 A12の残りとDまでの継続

A12の指定射・同値性はまだ閉じていない。次は同じ正規化BK Homの係数重みを、既存 `normalizedLinearWeightFreeIso`、`normalizedMooreMapIso`、`pointwiseExtendIso`・`mapExtendIso` の指定射で、AsSmall添字の自由鎖図式へ接続する。そのΓ Homへ既存A09の指定比較を適用し、元のMoore反転と単体集合のop、今回の指定重み同型、既存の実Γ Hom図式の同型で `liftedClosedDiagram` の反転BK Holimへ戻す。射の等式と同値性は別々に検証する。

その後に一覧Bの指定豊穣合成との等式・native切断の族・極限性、Cの標準脚とD(A)への輸送、Dの全図式射・指定錐の族・離散加群入口が残る。goal「Dまで進めてください」はactiveのままで、A11や今回の部品を完了条件に置き換えていない。停止点2の完了報告ではない。


## 99. A12の途中：元の正規化BK係数重みを自由鎖図式へ接続

前回のgoal turnはA11とAsSmallの検証済みコード・報告を保存した進捗。今回の開始時に枝がクリーンで`ffbea99f3`まであることを確認し、§98.3の係数重みの接続を進めた。goal「Dまで進めてください」はactiveのまま。

既存のMoore比較を、加法関手間の自然変換に対して自然な形にした。その指定比較を評価関手で束ね、図式圏の正規化と点ごとの正規化の全自然同型を作った。既存 `pointwiseExtendIso`、`functorComplexExchangeCounitIso`、`normalizedLinearWeightFreeIso` と合成し、係数余積による正規化線形重みから同じ自由負鎖図式への指定同型を得た。最後に元の二重反対圏上の `normalizedBousfieldKanWeight` へ特殊化した。

### 99.1 同じA12の分割と前提計算の型

`normalizedMooreMapHom_functor_naturality`をA12の前提計算 **1/3** とする（既存正規化比較の自然性法則）。他は一覧A12の係数重み照合の同じ証明分割。照合枠は全体3/3のまま。既存宣言と計算上限は変更していない。

最初の二本はHomologicalAlgebra名前空間。NormalizedMooreMapFunctorNaturalityでは`{C D : Type*}`、両Category構造とAbelian構造を固定する。PointwiseNormalizedMooreでは`J : Type*`・`[Category* J]`・`C : Type*`・`[Category* C] [Abelian C]`。LinearWeightFreeDiagramIsoはDiagramComparison名前空間、`A : Type u`・`[CommRing A]`・`J : Type v`・`[Category.{w} J]`・`W : J ⥤ SSet.{0}`。最後の特殊化はHA.DerivedCategoryModels.CosimplicialTotalization名前空間。

`NormalizedMooreMapFunctorNaturality`

```lean
theorem normalizedMooreMapHom_functor_naturality {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (X : SimplicialObject C) :
    (NatTrans.mapHomologicalComplex α (.down ℕ)).app ((normalizedMooreComplex C).obj X) ≫
      normalizedMooreMapHom G X =
    normalizedMooreMapHom F X ≫ (normalizedMooreComplex D).map (Functor.whiskerLeft X α)
```


`PointwiseNormalizedMoore`

```lean
def diagramMooreFunctor : SimplicialObject (J ⥤ C) ⥤ J ⥤ ChainComplex C ℕ
```

```lean
def pointwiseMooreFunctor : SimplicialObject (J ⥤ C) ⥤ J ⥤ ChainComplex C ℕ
```

```lean
def pointwiseMooreIso : diagramMooreFunctor J C ≅ pointwiseMooreFunctor J C
```


`LinearWeightFreeDiagramIso`

```lean
def freeLinearWeightDiagramIso :
    (((normalizedMooreComplex _).obj (freeLinearizedSimplicialWeight A W.flip)).extend
      ComplexShape.embeddingDownNat) ≅
    (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0}))
```

```lean
def normalizedLinearWeightDiagramIso :
    (((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W.flip)).extend
      ComplexShape.embeddingDownNat) ≅
    (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0}))
```


`NormalizedBKFreeWeight`

```lean
def normalizedBousfieldKanWeightFreeDiagramIso (A : Type u) [CommRing A] :
    (normalizedBousfieldKanWeight (A := A)).extend ComplexShape.embeddingDownNat ≅
      (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (freeNegativeChainsDiagram (A := A) (bousfieldKanSetWeight.flip ⋙ SSet.uliftFunctor.{u,0}))
```

### 99.2 検収と登録対象

コード **`ff3dbf01a`**（共通2本70行）・**`1e434f076`**（係数重みの2本68行）。個別・結合検査 `/private/tmp/isw2-moore-functor-nat1.log`、`/private/tmp/isw2-pointwise-moore1.log`、`/private/tmp/isw2-bk-free-weight1.log` は終了コード0。

鍵付き対象ビルドは **1,339 jobs**・**2,783 jobs**、どちらも終了コード0（`/private/tmp/isw2-build108.log`・`/private/tmp/isw2-build109.log`）。監査は新規分だけで各 **8宣言**、すべて標準三公理のみ（`/private/tmp/AuditISW2G10A12Moore.lean`・`/private/tmp/AuditISW2G10A12FreeWeight.lean`）。共有鍵は返却済み。

累計 **206モジュール・12,260行・1,982宣言**。対象一覧 `/private/tmp/isw2-g10-twohundredsix-modules.txt`。上記4本を登録対象へ追加する（共通HomologicalAlgebra2本、DiagramComparison1本、HA/CosimplicialTotalization1本）。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし。外枠14,500行まで残り2,240行。mainのB3凍結中なので、枝だけで作業・コミットした。

### 99.3 残りと次の接続

今回閉じたのは元の正規化BK係数重みから自由鎖図式への同型であり、A12の反転BK比較と同値性そのものではない。次は、この指定同型と§98の`asSmallLinearHomIso`をHom複体へ運び、元のMoore反転ホモトピー同値、AsSmall・ULift・重み付き切断の指定射を通して、A09の同じ比較を反転BK Holimへ戻す。`normalizedMooreReverse`は既存の**鎖ホモトピー同値の順射**であり、根拠なく厳密な同型として扱わない。全射と同値性を元の指定比較についてそれぞれ検査する。

その後のB（指定豊穣合成・native切断の族・極限性）、C（標準脚・D(A)輸送）、D（全図式射・指定錐族・離散加群入口）は未完。目標の完了条件はDまでの検証済み実装のままで、停止点2の完了報告ではない。


## 100. A12の途中：元のΓ Homから同じAsSmall重み付き切断への指定AW比較

mainのみB3で凍結し、各枝のコミットは続けてよいという11-13 23時の連絡に従った。mainの取り込みや入口の登録は行っていない。

元の係数重みの同型を線形Homの始域へ運び、AsSmall制限の指定同型と合成した。そのΓ像の後にA09の元のAW比較を合成し、その同じ比較自身の単体的ホモトピー同値性を示した。これは反転前の接続であり、A12の最終射の代用ではない。

### 100.1 型と数え方

`linearHomSourceIso`はA12の前提計算2/3（既存の前合成の両単位則）。前提計算1/3は§99の正規化自然性。残りはA12の同じ証明の分割。照合枠は全体3/3のまま。LinearHomSourceIsoでは`A : Type u`・`[CommRing A]`・`{C : Type v}`・`[Category.{u} C] [Preadditive C] [Linear A C]`。HAの二本では`A : Type u`・`[CommRing A]`。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearHomSourceIso`

```lean
def linearHomSourceIso {P P' : CochainComplex C ℤ} (e : P ≅ P') (Q : CochainComplex C ℤ) :
    linearHomComplex A P Q ≅ linearHomComplex A P' Q
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKSmallHom`

```lean
def normalizedBKSmallWeight (_A : Type u) : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ SSet.{u}
```

```lean
def normalizedBKSmallDiagram (X : CosimplicialObject (Complex A)) :
    AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ Complex A
```

```lean
def normalizedBKSmallHomIso (X : CosimplicialObject (Complex A)) :
    normalizedBousfieldKanHom X ≅
      linearHomComplex A
        ((functorToComplexOfFunctors (AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (ModuleCat A) (.up ℤ)).obj
          (freeNegativeChainsDiagram (A := A) (normalizedBKSmallWeight A)))
        ((functorToComplexOfFunctors (AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (ModuleCat A) (.up ℤ)).obj
          (normalizedBKSmallDiagram A X))
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKSmallSections`

```lean
def normalizedBKCoefficientMap : ULift.{u} ℤ →+* A
```

```lean
def normalizedBKSmallSectionsMap (X : CosimplicialObject (Complex A)) :
    (truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom X) ⟶
      weightedSections (normalizedBKSmallWeight A)
        (normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A)
```

```lean
theorem normalizedBKSmallSectionsMap_equivalence (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (normalizedBKSmallSectionsMap A X)
```

### 100.2 検収と残り

コード **`f181b0655`**（上記3本142行）。鍵付き対象ビルド **4,585 jobs**、新規分のみの小さな監査 **16宣言（4・7・5）・標準三公理のみ**。終了コード0、ログ`/private/tmp/isw2-build110.log`、監査`/private/tmp/AuditISW2G10A12SmallSections.lean`。共有鍵は返却済み。個別結合検査のログもエラーなし。新公理・sorryなし、計算上限・既存宣言・⑤a・入口・公式監査の変更なし。

累計 **209モジュール・12,402行・1,998宣言**。一覧`/private/tmp/isw2-g10-twohundrednine-modules.txt`。外枠14,500行まで残り2,098行。登録対象は100.1の3本。累計の監査数は既検証分と今回の新規分の合計であり、大きな一括監査を流したという意味ではない。

A12のMoore反転、二重反対圏と元の添字の移送、実豊穣Homとの指定射の照合は残っている。その後のB・C・Dも未完。目標「Dまで進めてください」は継続する。


## 101. A12完了：指定Moore反転から元の反転豊穣HomのBK endへ

A12の指定型`normalizedBKReflectedSectionsMap`と、その同じ射自身の単体的ホモトピー同値性を閉じた。元のMoore反転の鎖ホモトピー同値を、既存の反変endと指定end–Hom同型で運ぶ。反転側にも同じ自由重みHom同型とA09の実AW比較を適用し、既存の反転end同型、down・二重反対・upによる指定添字移送、元のsmallBousfieldKanWeightDown、既存の実Γ Hom全自然同型を順に合成した。

反転前の切断空間のKan性は仮定にせず、同じ反転end同型と元のBK endの既存Kan性から得た。これにより既存のopのホモトピー同値性と合成則を、その必要なKan性を持つ形で使用した。

### 101.1 同じ一覧A12の証明分割の型

以下6本はA12に初めから含めた反転・AsSmall・ULift・Γ Homの接続の証明分割である。前提計算枠は§100の2/3、照合枠は全体3/3のまま。新しい数学のまとまりは追加していない。`A : Type u`・`[CommRing A]`を固定する（SmallBKIndexSectionsは環に依存せず、同じ小添字の制限を使う）。以下はすべてHA.DerivedCategoryModels.CosimplicialTotalization名前空間。

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedNormalizedBKHom`

```lean
def reflectedNormalizedBKWeight : ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat A) ℕ
```

```lean
def reflectedNormalizedBKHom (X : CosimplicialObject (Complex A)) : Complex A
```

```lean
def normalizedBKReverseHomotopyEquiv (X : CosimplicialObject (Complex A)) :
    HomotopyEquiv (normalizedBousfieldKanHom X) (reflectedNormalizedBKHom X)
```

```lean
def normalizedBKReverseSpaceMap (X : CosimplicialObject (Complex A)) :
    (truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom X) ⟶
      (truncatedDoldKanFunctor A).obj (reflectedNormalizedBKHom X)
```

```lean
theorem normalizedBKReverseSpaceMap_equivalence (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (normalizedBKReverseSpaceMap X)
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedNormalizedBKSmallHom`

```lean
def reflectedNormalizedBKSmallWeight (_A : Type u) : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ SSet.{u}
```

```lean
def reflectedNormalizedBKSmallHomIso (X : CosimplicialObject (Complex A)) :
    reflectedNormalizedBKHom X ≅
      linearHomComplex A
        ((functorToComplexOfFunctors (AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (ModuleCat A) (.up ℤ)).obj
          (freeNegativeChainsDiagram (A := A) (reflectedNormalizedBKSmallWeight A)))
        ((functorToComplexOfFunctors (AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (ModuleCat A) (.up ℤ)).obj
          (normalizedBKSmallDiagram A X))
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedNormalizedBKSmallSections`

```lean
def reflectedNormalizedBKSmallSectionsMap (X : CosimplicialObject (Complex A)) :
    (truncatedDoldKanFunctor A).obj (reflectedNormalizedBKHom X) ⟶
      weightedSections (reflectedNormalizedBKSmallWeight A)
        (normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A)
```

```lean
theorem reflectedNormalizedBKSmallSectionsMap_equivalence (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (reflectedNormalizedBKSmallSectionsMap A X)
```

```lean
def normalizedBKSmallReflectedComparison (X : CosimplicialObject (Complex A)) :
    ((truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom X)).op ⟶
      weightedSections (normalizedBKSmallWeight A)
        ((normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.SmallBKIndexSections`

```lean
def smallBKIndexToDouble : AsSmall.{u} SimplexCategory ⥤ AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)
```

```lean
def smallBKIndexFromDouble : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ AsSmall.{u} SimplexCategory
```

```lean
def smallBKIndexSectionsMap {I J : Type u} [SmallCategory I] [SmallCategory J]
    (F : J ⥤ I) (W H : I ⥤ SSet.{u}) :
    weightedSections W H ⟶ weightedSections (F ⋙ W) (F ⋙ H)
```

```lean
theorem smallBKIndexSectionsMap_π {I J : Type u} [SmallCategory I] [SmallCategory J]
    (F : J ⥤ I) (W H : I ⥤ SSet.{u}) (j : J) :
    smallBKIndexSectionsMap F W H ≫ weightedSectionsπ (F ⋙ W) (F ⋙ H) j =
      weightedSectionsπ W H (F.obj j)
```

```lean
def smallBKIndexSectionsIso (W H : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ SSet.{u}) :
    weightedSections W H ≅
      weightedSections (smallBKIndexToDouble ⋙ W) (smallBKIndexToDouble ⋙ H)
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKOriginalSections`

```lean
def normalizedBKOriginalSectionsIso (X : CosimplicialObject (Complex A)) :
    weightedSections (normalizedBKSmallWeight A)
      ((normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A) ⋙ SSet.opFunctor) ≅
      bousfieldKanHolim
        (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X ⋙
          truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)
```

```lean
def normalizedBKOriginalSectionsMap (X : CosimplicialObject (Complex A)) :
    ((truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom X)).op ⟶
      bousfieldKanHolim
        (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X ⋙
          truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)
```

```lean
theorem normalizedBKOriginalSectionsMap_factor (X : CosimplicialObject (Complex A)) :
    normalizedBKOriginalSectionsMap A X =
      SSet.opFunctor.map (normalizedBKReverseSpaceMap X ≫
        reflectedNormalizedBKSmallSectionsMap A X) ≫
      (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso
        (normalizedBKSmallWeight A) (normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A) ≪≫
          normalizedBKOriginalSectionsIso A X).hom
```

```lean
instance reflectedNormalizedBKSmallSections_kan (X : CosimplicialObject (Complex A)) :
    SSet.KanComplex (weightedSections (reflectedNormalizedBKSmallWeight A)
      (normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A))
```

```lean
theorem normalizedBKOriginalSectionsMap_equivalence (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (normalizedBKOriginalSectionsMap A X)
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKReflectedSections`

```lean
def normalizedBKReflectedHomDiagramIso (X : CosimplicialObject (Complex A)) (T : Complex A) :
    (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙
      (homDiagramFunctor T).obj X ⋙ truncatedDoldKanFunctor A) ⋙ SSet.opFunctor) ≅
    simplicialHomDiagram (liftedClosedDiagram X) (ForgetEnrichment.of (Complex A) T) ⋙
      SSet.opFunctor
```

```lean
def normalizedBKReflectedSectionsMap (X : CosimplicialObject (Complex A)) (T : Complex A) :
    ((truncatedDoldKanFunctor A).obj
      (normalizedBousfieldKanHom ((homDiagramFunctor T).obj X))).op ⟶
    bousfieldKanHolim (simplicialHomDiagram (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) T) ⋙ SSet.opFunctor)
```

```lean
theorem normalizedBKReflectedSectionsMap_equivalence (X : CosimplicialObject (Complex A))
    (T : Complex A) : IsSimplicialHomotopyEquivalence (normalizedBKReflectedSectionsMap X T)
```

### 101.2 検収・コミット・登録

コード **`5fd7f9b7b`**（反転Hom・自由重みHomの2本88行）、**`296461f29`**（反転切断の1本56行）、**`214d21cc5`**（添字移送とA12最終比較の3本235行）。個別・結合検査`/private/tmp/isw2-reflected-bk-hom2.log`、`/private/tmp/isw2-reflected-bk-small1.log`、`/private/tmp/isw2-bk-enriched-sections4.log`は終了コード0。添字の逆則と最終の合成照合は、引数の指定と同じ等式の証明分割で軽くし、計算上限は変更していない。

鍵付き対象ビルド：

| ログ | jobs | 新規分だけの監査 | 終了 |
| --- | ---: | --- | --- |
| `/private/tmp/isw2-build111.log` | 4,535 | 15宣言（9・6） | 0 |
| `/private/tmp/isw2-build112.log` | 4,733 | 5宣言 | 0 |
| `/private/tmp/isw2-build113.log` | 6,474 | 31宣言（8・10・13） | 0 |

いずれも標準三公理のみ。監査ファイルは`AuditISW2G10A12Reverse.lean`・`AuditISW2G10A12ReflectedSections.lean`・`AuditISW2G10A12Final.lean`（すべて`/private/tmp/`）。鍵は返却済み。今回の379行を加え、累計 **215モジュール・12,781行・2,049宣言**。対象一覧`/private/tmp/isw2-g10-twohundredfifteen-modules.txt`。外枠14,500行まで残り1,719行。累計監査数は検証済みの各新規分の合計。大きな監査・rootビルドは行っていない。既存宣言・⑤a・入口・公式監査の変更、新公理、sorryなし。

### 101.3 残り

A01〜A12まで完了。B01のHom–Tot比較との接続、B02の指定豊穣合成との厳密な等式、B03〜B08のnative切断・極限性、Cの標準脚とD(A)輸送、Dの全図式射・指定錐の族・離散加群入口はまだ残る。とくに今回の反転Homは反変endの移送から定めたので、元の錐代表へのMoore反転の前合成との等式はB02の中で検証する。A12の同値性をB02の厳密な等式の代わりにしない。目標「Dまで進めてください」は継続し、停止点2の完了報告ではない。


## 102. B01：実Hom同型・Hom–Tot比較・A12の指定合成

B01の`gammaReflectedBKComparison`を元の型で構成した。任意の試験対象`x : ClosedCategory A (Complex A)`を`ForgetEnrichment.to`で元の複体へ戻し、既存の実Hom同型、同じ`normalizedBousfieldKanHomSpaceComparison`、A12の指定射を合成する。この合成射自身のホモトピー同値性も証明した。これはB03の証明分割であり、実際の豊穣合成`reflectedWeightedHomComparison`とのB02の等式はまだ主張していない。

### 102.1 型

`A : Type u`・`[CommRing A]`。名前空間はHA.DerivedCategoryModels.CosimplicialTotalization。登録対象は`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.GammaReflectedBKComparison`。前提計算枠・照合枠を新たに使っていない。

```lean
def gammaReflectedBKComparison (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    (SimplicialCategory.sHom x
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))).op ⟶
    bousfieldKanHolim (simplicialHomDiagram (liftedClosedDiagram X) x ⋙ SSet.opFunctor)
```

```lean
theorem gammaReflectedBKComparison_equivalence (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    IsSimplicialHomotopyEquivalence (gammaReflectedBKComparison X x)
```

### 102.2 検収と残り

コード **`bd740ce50`**（1本60行）。個別検査`/private/tmp/isw2-gamma-bk-comparison3.log`は終了コード0。鍵付き対象ビルド **6,475 jobs**、新規分だけの小さな監査 **13宣言・標準三公理のみ**、終了コード0（`/private/tmp/isw2-build114.log`、`/private/tmp/AuditISW2G10B01.lean`）。鍵は返却済み。

累計 **216モジュール・12,841行・2,062宣言**、一覧`/private/tmp/isw2-g10-twohundredsixteen-modules.txt`。外枠14,500行まで残り1,659行。新公理・sorryなし、計算上限・既存宣言・⑤a・入口・公式監査の変更なし。mainのB3凍結中のため枝だけでコミットした。

A01〜A12・B01が完了。B02の厳密な等式、B03の実豊穣合成自身の同値性、B04〜B08の指定native切断の族と極限性、CとDは未完。次は、元の錐代表へのMoore反転の前合成と、今回の反変end移送の一致を含め、A09の指定AW比較を実豊穣合成へ照合する。単なる同値な空間への置換はしない。今回の区切りは停止点2ではなく、目標「Dまで進めてください」はactiveのまま。


## 103. B02の途中：endで運んだ反転は元の錐代表の前合成そのもの

前回のB01までの検証済みコードから続行した。B02の最初の厳密な照合として、指定符号付きend–Hom同型の重みに関する自然性を示した。既存の積射影の自然性と、負次数への零延長の指定行同型で計算し、同じMoore反転を運んだ順射が元の反転鎖射による前合成に等しいことを得た。閉零次元に適用し、元の恒等射から作った錐代表が反転後も既存の`reflectedBousfieldKanConeRepresentative`そのものへ移ることも確認した。

### 103.1 型と数え方

`weightEndHomIso_source_naturality`をB02の前提計算1/3（既存構成の自然性）とする。その行での公式と、HAの三つの反転の等式は同じ証明の分割。照合枠は全体3/3のまま。計算上限は変更していない。最初のファイルでは`A : Type u`・`[CommRing A]`・`{J : Type}`・`[SmallCategory J]`・`{K L : ChainComplex (Jᵒᵖ ⥤ ModuleCat A) ℕ}`。二本目は`{A : Type u}`・`[CommRing A]`。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightEndHomSourceNaturality`

```lean
theorem extendedChainHomRows_precomp (f : K ⟶ L)
    (H : CochainComplex (Jᵒᵖ ⥤ ModuleCat A) ℤ) (q : ℤ)
    (z : Cochain (L.extend ComplexShape.embeddingDownNat) H q) (n : ℕ) :
    extendedChainHomRows K H q
      ((intervalHomPrePost A (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat)
        (𝟙 H)).f q z) n = f.f n ≫ extendedChainHomRows L H q z n
```

```lean
theorem weightEndHomIso_source_naturality (f : K ⟶ L) (X : Jᵒᵖ ⥤ Complex A) :
    (linearWeightEndTotalFunctor A X).map f.op ≫ (weightEndHomIso A K X).hom =
      (weightEndHomIso A L X).hom ≫
        intervalHomPrePost A (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat)
          (𝟙 ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).obj X))
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKReversePrecomposition`

```lean
theorem normalizedBKReverseHomotopyEquiv_hom (X : CosimplicialObject (Complex A)) :
    (normalizedBKReverseHomotopyEquiv X).hom =
      intervalHomPrePost A
        (HomologicalComplex.extendMap
          (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
          ComplexShape.embeddingDownNat)
        (𝟙 ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
          (doubleOppositeDiagram X)))
```

```lean
theorem normalizedBKReverseHomotopyEquiv_ofHom (X : CosimplicialObject (Complex A))
    (f : normalizedBousfieldKanWeight.extend ComplexShape.embeddingDownNat ⟶
      (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram X)) :
    (normalizedBKReverseHomotopyEquiv X).hom.f 0 (Cochain.ofHom f) =
      Cochain.ofHom (HomologicalComplex.extendMap
        (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat ≫ f)
```

```lean
theorem normalizedBKReverseHomotopyEquiv_coneRepresentative (X : CosimplicialObject (Complex A)) :
    (normalizedBKReverseHomotopyEquiv
      ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X)).hom.f 0
        (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) =
      Cochain.ofHom (reflectedBousfieldKanConeRepresentative X)
```

### 103.2 検収と残り

コード **`eb59a7350`**（2本125行）。個別検査`/private/tmp/isw2-weight-end-source4.log`・`/private/tmp/isw2-bk-reverse-precomp4.log`は終了コード0。最初の対象ビルド`/private/tmp/isw2-build115.log`は閉零次元の一般的な書き換えの型照合が200,000 heartbeatsに達して失敗。計算上限を上げず、その部分を各次数の直接計算へ分けた。修正後の鍵付き対象ビルド`/private/tmp/isw2-build116.log`は **4,379 jobs・終了コード0**、新規分のみの監査は **5宣言（2・3）・標準三公理のみ**（`/private/tmp/AuditISW2G10B02Reverse.lean`）。共有鍵は返却済み。

累計 **218モジュール・12,966行・2,067宣言**。一覧`/private/tmp/isw2-g10-twohundredeighteen-modules.txt`。外枠14,500行まで残り1,534行。新公理・sorryなし、既存宣言・⑤a・入口・公式監査・mainの変更なし。

B02はまだ未完。今回閉じたのは反転の前合成との厳密な一致であり、残る指定AW比較・Hom–Tot比較と全単体の実豊穣合成との照合を省略しない。B03の元の比較自身の同値性、B04〜B08、C、Dも未完。Dまでの目標はactiveのまま。


## 104. B02の途中：元の線形重みHom同値の後合成自然性

指定錐代表から作る単体写像を後合成へ移すため、既存`normalizedLinearWeightHomEquiv`の標的複体射に関する自然性を示した。既存の延長・切断・Dold–KanのHom同値の後合成則を、同じ二変数の生成元評価へ移すもので、元の指定写像と全単体を保持する。

### 104.1 型と枠

HomologicalAlgebra名前空間。`A : Type u`・`[CommRing A]`・`{D : Type v}`・`[Category.{w} D]`。B02の前提計算 **2/3**（既存構成の後合成自然性）とする。1/3は§103のend–Hom同型の重みに関する自然性。照合枠は全体3/3のまま。

```lean
theorem normalizedLinearWeightHomEquiv_postcomp (W : SimplicialObject (D ⥤ Type))
    {H H' : CochainComplex (D ⥤ ModuleCat A) ℤ}
    (f : ((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W)).extend
      ComplexShape.embeddingDownNat ⟶ H) (g : H ⟶ H') :
    normalizedLinearWeightHomEquiv A W H' (f ≫ g) =
      normalizedLinearWeightHomEquiv A W H f ≫
        Functor.whiskerRight
          ((Abelian.DoldKan.Γ : ChainComplex (D ⥤ ModuleCat A) ℕ ⥤
            SimplicialObject (D ⥤ ModuleCat A)).map
              (truncLE'Map g (ComplexShape.embeddingUpIntLE 0)))
          ((Functor.whiskeringRight D (ModuleCat A) (Type u)).obj (forget (ModuleCat A)))
```

### 104.2 検収・登録対象・残り

コード **`be8447d78`**（32行）。個別検査`/private/tmp/isw2-normalized-weight-target1.log`は終了コード0。鍵付き対象ビルド **1,801 jobs**、新規分のみの監査 **1宣言・標準三公理のみ**、終了コード0（`/private/tmp/isw2-build117.log`、`/private/tmp/AuditISW2G10B02Target.lean`）。共有鍵は返却済み。登録対象は **`SerrePositivity.HomologicalAlgebra.NormalizedLinearWeightHomNaturality`**。

累計 **219モジュール・12,998行・2,068宣言**。対象一覧`/private/tmp/isw2-g10-twohundrednineteen-modules.txt`。外枠14,500行まで残り1,502行。新公理・sorryなし、計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。

B02は未完。A09の指定AW比較、既存Hom–Tot比較と、元の標準成分模型の実豊穣合成が全単体で一致する照合が残る。今回の自然性だけでその等式を済ませたとは扱わない。B03〜B08・C・Dも未完で、目標「Dまで進めてください」はactiveのまま。次の区切りはこの全単体の照合である。


## 105. B02の途中：指定正規化・Γ比較と元のDold–Kan Hom随伴の両立

前回は反転代表と後合成自然性を検証・保存できているので、進捗ありとして続けた。B02の全単体の照合に必要な係数移送について、元の正規化比較`normalizedMooreMapIso`と元のΓ余積比較`gammaMapIso`が同じDold–KanのHom随伴を保つことを示した。任意の加法関手を許すので、図式の評価関手にも適用できる。任意の同値を新たに選ぶ証明ではない。

まず、指定余単位の逆射にMoore包含を後合成すると、同じKaroubi模型の`N₁Γ₀.inv`の実鎖射になると示した。Karoubi単位の自然性と正規化射影で打ち消す。次にΓの恒等添字の和因子が既に正規化されている既存補題を使い、二比較の係数移送の計算を余積包含の自然性に短縮した。Moore包含で戻して指定余単位の両立を得て、最後に元のHom随伴の公式と正規化比較の自然性を適用した。

### 105.1 型と数え方

`doldKanHomEquiv_map`をB02の前提計算 **3/3**（既存構成の係数移送則）とする。余単位の具体式、Karoubi模型での同じ式、余単位の順射・逆射の式は、その同じ証明の分割。1/3は§103、2/3は§104。照合枠は全体3/3のまま。これ以上の独立した前提計算や照合を黙って追加しない。同じ一覧B02の証明分割は§14に従う。

すべてHomologicalAlgebra名前空間。`{C : Type u}`・`[Category.{v} C] [Abelian C]`を固定し、係数移送の二本ではさらに`{D : Type u'}`・`[Category.{v'} D] [Abelian D]`を固定する。

登録対象：`SerrePositivity.HomologicalAlgebra.DoldKanCounitMooreInclusion`

```lean
theorem doldKanCounitInv_inclusion (K : ChainComplex C ℕ) :
    (Abelian.DoldKan.equivalence.counitIso.inv.app K) ≫
      inclusionOfMooreComplexMap ((Abelian.DoldKan.Γ : ChainComplex C ℕ ⥤ _).obj K) =
      (N₁Γ₀.inv.app K).f
```


登録対象：`SerrePositivity.HomologicalAlgebra.DoldKanCoefficientCounit`

```lean
theorem doldKanKaroubiCounitInv_map (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    (F.mapHomologicalComplex (.down ℕ)).map (N₁Γ₀.inv.app K).f ≫
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Abelian.DoldKan.Γ.obj K) =
    (N₁Γ₀.inv.app ((F.mapHomologicalComplex (.down ℕ)).obj K)).f ≫
      (alternatingFaceMapComplex D).map (gammaMapIso F K).hom
```

```lean
theorem doldKanCounitInv_map (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    (F.mapHomologicalComplex (.down ℕ)).map (Abelian.DoldKan.equivalence.counitIso.inv.app K) ≫
      normalizedMooreMapHom F (Abelian.DoldKan.Γ.obj K) =
    Abelian.DoldKan.equivalence.counitIso.inv.app
        ((F.mapHomologicalComplex (.down ℕ)).obj K) ≫
      (normalizedMooreComplex D).map (gammaMapIso F K).hom
```


登録対象：`SerrePositivity.HomologicalAlgebra.DoldKanHomCoefficient`

```lean
theorem doldKanCounit_map (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    normalizedMooreMapHom F (Abelian.DoldKan.Γ.obj K) ≫
      (normalizedMooreComplex D).map (gammaMapIso F K).inv ≫
      Abelian.DoldKan.equivalence.counitIso.hom.app
        ((F.mapHomologicalComplex (.down ℕ)).obj K) =
    (F.mapHomologicalComplex (.down ℕ)).map (Abelian.DoldKan.equivalence.counitIso.hom.app K)
```

```lean
theorem doldKanHomEquiv_map (F : C ⥤ D) [F.Additive]
    (W : SimplicialObject C) (K : ChainComplex C ℕ)
    (f : (normalizedMooreComplex C).obj W ⟶ K) :
    (Abelian.DoldKan.equivalence : SimplicialObject D ≌ ChainComplex D ℕ).toAdjunction.homEquiv
      (W ⋙ F) ((F.mapHomologicalComplex (.down ℕ)).obj K)
      ((normalizedMooreMapIso F W).inv ≫ (F.mapHomologicalComplex (.down ℕ)).map f) ≫
        (gammaMapIso F K).hom =
    Functor.whiskerRight
      ((Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv
        W K f) F
```

### 105.2 検収・コミット・登録

コード **`62ad24b46`**（最初の2本119行）・**`0d3a623aa`**（Hom随伴の1本72行）。個別・結合検査`/private/tmp/isw2-dk-counit-inclusion1.log`、`/private/tmp/isw2-dk-coeff-counit15.log`、`/private/tmp/isw2-dk-hom-coeff5.log`は終了コード0。途中で大きな型のまま余単位を直接書き換える検査が200,000 heartbeatsに達したが、計算上限を上げず、Karoubi模型の同じ射の計算と包含による照合を分離した。

| 検査 | jobs | 新規分のみの監査 | 終了 |
| --- | ---: | --- | --- |
| `/private/tmp/isw2-build118.log` | 1,369 | 10宣言（6・4） | 0 |
| `/private/tmp/isw2-build119.log` | 1,370 | 3宣言 | 0 |

監査は`/private/tmp/AuditISW2G10B02Counit.lean`・`/private/tmp/AuditISW2G10B02HomCoefficient.lean`、どちらも標準三公理のみ。共有鍵は返却済み。新規3本191行を加え、累計 **222モジュール・13,189行・2,081宣言**。対象一覧`/private/tmp/isw2-g10-twohundredtwentytwo-modules.txt`。外枠14,500行まで残り1,311行。新公理・sorryなし、計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。登録対象は105.1の3本。大きな監査は行っていない。

### 105.3 残り

B02は未完。今回の一般の加法関手に関する式を評価関手に適用し、指定零延長・切断のmateと合わせて、元の図式圏の線形重みHom同値を点ごとの自由鎖随伴へ照合する。その後にA09の指定AW比較と元の実豊穣合成の全単体の照合を閉じる。今回のHom随伴の係数両立だけで、AW合成の一致を証明したとは扱わない。B03〜B08・C・Dも未完。目標「Dまで進めてください」はactiveのままで、停止点2の完了報告ではない。


## 106. B02の途中：実切断同型と元の零延長Hom随伴の両立

前回の指定正規化・Γ比較とHom随伴の両立から続行した。既存の`pointwiseTruncationIso`自身が、図式圏での零延長Hom随伴を点ごとの同じ随伴へ移すことを示した。右随伴の一意性から定めた元のmateの単位則を使い、図式側の調整したHom随伴を元の随伴と指定成分交換の余単位で表す。点ごとの随伴を成分交換から戻すと同じ随伴になることを各成分で確認し、最終の実切断同型についての式を閉じた。

### 106.1 型と数え方

下記4本はB02の係数移送則（§105の前提計算3/3）を元の指定切断mateへ接続する同じ証明の分割。前提計算枠はB02で3/3、照合枠は全体3/3のまま。新たな独立した前提計算や照合を追加していない。名前空間はHomologicalAlgebra、`J : Type*`・`[Category* J]`・`C : Type*`・`[Category* C] [Abelian C]`を固定する。

```lean
theorem truncationExchangeMate_homEquiv
    (K : ChainComplex (J ⥤ C) ℕ) (X : J ⥤ CochainComplex C ℤ)
    (f : ((complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight J (ChainComplex C ℕ) (CochainComplex C ℤ)).obj
        (ComplexShape.embeddingDownNat.extendFunctor C)).obj K) ⟶ X) :
    (diagramTruncationAdjunction J C).homEquiv K X f ≫
        (truncationExchangeMate J C).hom.app X =
      (pointwiseTruncationAdjunction J C).homEquiv K X f
```

```lean
theorem diagramTruncationHomEquiv_exchange
    (K : ChainComplex (J ⥤ C) ℕ) (H : CochainComplex (J ⥤ C) ℤ)
    (f : K.extend ComplexShape.embeddingDownNat ⟶ H) :
    (diagramTruncationAdjunction J C).homEquiv K
      (complexOfFunctorsToFunctorToComplex.obj H)
      ((pointwiseExtendIso J C ComplexShape.embeddingDownNat).inv.app K ≫
        complexOfFunctorsToFunctorToComplex.map f) =
    (negativeExtendTruncationAdjunction (J ⥤ C)).homEquiv K H f ≫
      ((ComplexShape.embeddingUpIntLE 0).truncLE'Functor (J ⥤ C)).map
        ((functorComplexExchangeCounitIso J C (.up ℤ)).inv.app H)
```

```lean
theorem pointwiseTruncationHomEquiv_exchange
    (K : ChainComplex (J ⥤ C) ℕ) (X : J ⥤ CochainComplex C ℤ)
    (f : ((complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight J (ChainComplex C ℕ) (CochainComplex C ℤ)).obj
        (ComplexShape.embeddingDownNat.extendFunctor C)).obj K) ⟶ X) :
    complexOfFunctorsToFunctorToComplex.map
        ((pointwiseTruncationAdjunction J C).homEquiv K X f) ≫
      (functorComplexExchangeUnitIso J C (.down ℕ)).inv.app
        (X ⋙ (ComplexShape.embeddingUpIntLE 0).truncLE'Functor C) =
    (Adjunction.whiskerRight J (negativeExtendTruncationAdjunction C)).homEquiv
      (complexOfFunctorsToFunctorToComplex.obj K) X f
```

```lean
theorem pointwiseTruncationIso_homEquiv
    (K : ChainComplex (J ⥤ C) ℕ) (H : CochainComplex (J ⥤ C) ℤ)
    (f : K.extend ComplexShape.embeddingDownNat ⟶ H) :
    complexOfFunctorsToFunctorToComplex.map
        ((negativeExtendTruncationAdjunction (J ⥤ C)).homEquiv K H f) ≫
      (pointwiseTruncationIso J C).hom.app H =
    (Adjunction.whiskerRight J (negativeExtendTruncationAdjunction C)).homEquiv
      (complexOfFunctorsToFunctorToComplex.obj K) (complexOfFunctorsToFunctorToComplex.obj H)
      ((pointwiseExtendIso J C ComplexShape.embeddingDownNat).inv.app K ≫
        complexOfFunctorsToFunctorToComplex.map f)
```

### 106.2 検収・登録対象・残り

コード **`ed24d69de`**（新規1本97行）。個別検査`/private/tmp/isw2-point-trunc-hom6.log`は終了コード0。鍵付き対象ビルド **1,536 jobs**・終了コード0、新規分だけの監査 **6宣言・標準三公理のみ**（`/private/tmp/isw2-build120.log`、`/private/tmp/AuditISW2G10B02PointwiseTruncation.lean`）。共有鍵は返却済み。

登録対象は **`SerrePositivity.HomologicalAlgebra.PointwiseTruncationHomEquiv`**。累計 **223モジュール・13,286行・2,087宣言**、一覧`/private/tmp/isw2-g10-twohundredtwentythree-modules.txt`。外枠14,500行まで残り1,214行。新公理・sorryなし、計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。大きな監査は行っていない。

B02はまだ未完。次は§105の`doldKanHomEquiv_map`を評価関手へ適用し、今回の実切断Hom両立と組み合わせて、元の正規化重みHom同値の点ごとの式にする。その後の指定AW比較と実豊穣合成の全単体の照合、B03〜B08・C・Dは残る。目標「Dまで進めてください」はactiveのまま。


## 107. B02の途中：元の正規化重みHomの全図式移送と指定余積生成元の照合

前回の実切断Hom両立は検証・保存できているので、進捗ありとして続行した。指定された正規化比較とΓ比較を、評価関手に適用した係数移送則でつなぎ、図式圏のDold–Kan Hom同値を点ごとの同じ随伴へ移す全自然変換の等式を得た。

さらに、元の`normalizedWeightHomEquiv`が元の零延長随伴とDold–Kan随伴の合成であることを明示し、指定零延長・実切断・Γの比較を通して、点ごとの同じ二随伴に一致させた。最後に、指定余積による正規化Homと自由正規化鎖の同じ随伴を、各単体で元の余積包含の1の像が同じ自由生成元となる既存公式を直接適用して照合した。

### 107.1 型と数え方

以下はB02の同じ係数移送の証明分割。前提計算枠は§105のB02 3/3、照合枠は全体3/3のまま。余積生成元には既存`copowerUnitFreeHom_generator`を証明の中で直接使い、新たな独立した前提計算の宣言を足していない。

最初の2本はHomologicalAlgebra名前空間、`J : Type*`・`[Category* J]`・`C : Type*`・`[Category* C] [Abelian C]`。`normalizedWeightHomEquiv_asAdjunction`はJに依存しない。最後の1本はDiagramComparison名前空間、`A : Type u`・`[CommRing A]`。

登録対象：`SerrePositivity.HomologicalAlgebra.PointwiseDoldKanHomEquiv`

```lean
theorem pointwiseDoldKanHomEquiv
    (W : SimplicialObject (J ⥤ C)) (K : ChainComplex (J ⥤ C) ℕ)
    (f : (normalizedMooreComplex (J ⥤ C)).obj W ⟶ K) :
    (flipFunctor SimplexCategoryᵒᵖ J C).map
        ((Abelian.DoldKan.equivalence : SimplicialObject (J ⥤ C) ≌
          ChainComplex (J ⥤ C) ℕ).toAdjunction.homEquiv W K f) ≫
      (pointwiseGammaIso J C).inv.app K =
    (Adjunction.whiskerRight J
      (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction).homEquiv
      W.flip (complexOfFunctorsToFunctorToComplex.obj K)
      ((pointwiseMooreIso J C).inv.app W ≫ complexOfFunctorsToFunctorToComplex.map f)
```


登録対象：`SerrePositivity.HomologicalAlgebra.PointwiseNormalizedWeightHom`

```lean
theorem normalizedWeightHomEquiv_asAdjunction
    (W : SimplicialObject C) (H : CochainComplex C ℤ)
    (f : ((normalizedMooreComplex C).obj W).extend ComplexShape.embeddingDownNat ⟶ H) :
    normalizedWeightHomEquiv W H f =
      (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv
        W (H.truncLE' (ComplexShape.embeddingUpIntLE 0))
        ((negativeExtendTruncationAdjunction C).homEquiv _ H f)
```

```lean
theorem pointwiseTruncationGammaIso_hom (H : CochainComplex (J ⥤ C) ℤ) :
    (pointwiseTruncationGammaIso J C).hom.app H =
      (pointwiseGammaIso J C).inv.app (H.truncLE' (ComplexShape.embeddingUpIntLE 0)) ≫
        ((Functor.whiskeringRight J (ChainComplex C ℕ) (SimplicialObject C)).obj
          Abelian.DoldKan.Γ).map ((pointwiseTruncationIso J C).hom.app H)
```

```lean
theorem pointwiseNormalizedWeightHomEquiv
    (W : SimplicialObject (J ⥤ C)) (H : CochainComplex (J ⥤ C) ℤ)
    (f : ((normalizedMooreComplex (J ⥤ C)).obj W).extend ComplexShape.embeddingDownNat ⟶ H) :
    (flipFunctor SimplexCategoryᵒᵖ J C).map (normalizedWeightHomEquiv W H f) ≫
      (pointwiseTruncationGammaIso J C).hom.app H =
    ((Adjunction.whiskerRight J
      (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction).comp
        (Adjunction.whiskerRight J (negativeExtendTruncationAdjunction C))).homEquiv
      W.flip (complexOfFunctorsToFunctorToComplex.obj H)
      (((Functor.whiskeringRight J (ChainComplex C ℕ) (CochainComplex C ℤ)).obj
          (ComplexShape.embeddingDownNat.extendFunctor C)).map
        ((pointwiseMooreIso J C).inv.app W) ≫
        (pointwiseExtendIso J C ComplexShape.embeddingDownNat).inv.app
          ((normalizedMooreComplex (J ⥤ C)).obj W) ≫
        complexOfFunctorsToFunctorToComplex.map f)
```


登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CopowerNormalizedFreeHom`

```lean
theorem copowerNormalizedHomEquiv_free (W : SSet.{0}) (H : Complex A)
    (f : ((normalizedMooreComplex (ModuleCat A)).obj
      (W ⋙ uliftFunctor.{u,0} ⋙ ModuleCat.free A)).extend
          ComplexShape.embeddingDownNat ⟶ H) :
    copowerUnitDiagramHomEquiv A W
      ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ _).obj
        (H.truncLE' (ComplexShape.embeddingUpIntLE 0)))
      (normalizedWeightHomEquiv (W ⋙ copowerFunctor (ModuleCat.of A A)) H
        (HomologicalComplex.extendMap
          ((normalizedMooreComplex (ModuleCat A)).map
            (Functor.isoWhiskerLeft W (copowerUnitFreeNatIso A)).hom)
          ComplexShape.embeddingDownNat ≫ f)) =
    (freeNegativeChainsAdjunction A).homEquiv (W ⋙ uliftFunctor.{u,0}) H f
```

### 107.2 検収・登録・コミット

コード **`4fce28163`**（共通2本105行）・**`51a9f6ae2`**（DiagramComparison1本55行）。個別・結合検査`/private/tmp/isw2-point-dk-hom5.log`、`/private/tmp/isw2-point-normalized-hom4.log`、`/private/tmp/isw2-copower-normalized-free3.log`は終了コード0。型の照合は随伴の単位・後合成の成分を明示し、元の比較射のまま行った。計算上限は変更していない。

| 鍵付き対象ビルド | jobs | 新規分のみの監査 | 終了 |
| --- | ---: | --- | --- |
| `/private/tmp/isw2-build121.log` | 1,641 | 9宣言（3・6） | 0 |
| `/private/tmp/isw2-build122.log` | 2,588 | 2宣言 | 0 |

監査は`/private/tmp/AuditISW2G10B02PointwiseHom.lean`・`/private/tmp/AuditISW2G10B02CopowerHom.lean`、どちらも標準三公理のみ。共有鍵は返却済み。累計 **226モジュール・13,446行・2,098宣言**、一覧`/private/tmp/isw2-g10-twohundredtwentysix-modules.txt`。外枠14,500行まで残り1,054行。新公理・sorryなし、既存宣言・⑤a・入口・公式監査・mainの変更なし。登録対象は107.1の3本。大きな監査は行っていない。

### 107.3 残り

B02は未完。今回閉じた全図式の移送と各単体の指定余積生成元の照合を、既存の`normalizedLinearWeightDiagramIso`の元の射と組み合わせて、図式圏の元の線形重みHom同値をA09の同じ自由鎖随伴へつなぐ。その後の指定AW比較・Hom–Tot比較と実豊穣合成の全単体の照合、B03〜B08・C・Dは残る。今回の一般の随伴の式だけでAW合成の等式を済ませたとは扱わない。目標「Dまで進めてください」はactiveのまま。


## 108. B02の途中：A12の元の比較射と図式自由鎖Hom随伴の厳密な照合

前回の全図式の正規化Hom移送と指定生成元の照合から続行した。まず`freeLinearWeightDiagramIso`の元の順射を評価へ戻した式を示した。成分交換の単位・余単位を打ち消すと、指定零延長比較・Moore比較・交換単位が残る。次に正規化・零延長比較の元の自然性を使い、係数余積から自由加群への指定同型も含め、`normalizedLinearWeightDiagramIso`の元の順射を点ごとの同じ係数移送に同定した。

この評価公式と前回の全図式のHom両立を合成し、元の図式圏の`normalizedLinearWeightHomEquiv`が、A12の同じ比較射の後で、A09が使う同じ`freeNegativeChainsDiagramAdjunction`のHom同値に一致する式を全単体で閉じた。指定余積生成元を各単体で評価しており、比較射を別の同値で置換していない。

### 108.1 型と数え方

下記はB02の同じ係数移送の証明分割。前提計算枠は§105のB02 3/3、照合枠は全体3/3のまま。新しい独立した前提計算・照合の宣言を追加していない。名前空間はDiagramComparison、`A : Type u`・`[CommRing A]`・`{J : Type v}`・`[Category.{w} J]`を固定する。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightFreeDiagramEvaluation`

```lean
theorem freeLinearWeightDiagramIso_hom_evaluation (W : J ⥤ SSet.{0}) :
    complexOfFunctorsToFunctorToComplex.map (freeLinearWeightDiagramIso A W).hom =
      (pointwiseExtendIso J (ModuleCat A) ComplexShape.embeddingDownNat).hom.app
        ((normalizedMooreComplex _).obj (freeLinearizedSimplicialWeight A W.flip)) ≫
      Functor.whiskerRight ((pointwiseMooreIso J (ModuleCat A)).hom.app
        (freeLinearizedSimplicialWeight A W.flip))
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)) ≫
      (functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app
        (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0}))
```

```lean
theorem normalizedLinearWeightDiagramIso_hom_evaluation (W : J ⥤ SSet.{0}) :
    Functor.whiskerRight ((pointwiseMooreIso J (ModuleCat A)).inv.app
        (linearizedSimplicialWeight A W.flip))
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)) ≫
      (pointwiseExtendIso J (ModuleCat A) ComplexShape.embeddingDownNat).inv.app
        ((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W.flip)) ≫
      complexOfFunctorsToFunctorToComplex.map (normalizedLinearWeightDiagramIso A W).hom =
    Functor.whiskerRight ((pointwiseMooreFunctor J (ModuleCat A)).map
        (linearizedSimplicialWeightFreeIso A W.flip).hom)
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)) ≫
      (functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app
        (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0}))
```


登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightFreeHomComparison`

```lean
theorem normalizedLinearWeightHomEquiv_freeDiagram (W : J ⥤ SSet.{0})
    (H : CochainComplex (J ⥤ ModuleCat A) ℤ)
    (f : (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0})) ⟶ H) :
    (flipFunctor SimplexCategoryᵒᵖ J (Type u)).map
        (normalizedLinearWeightHomEquiv A W.flip H
          ((normalizedLinearWeightDiagramIso A W).hom ≫ f)) ≫
      Functor.whiskerRight ((pointwiseTruncationGammaIso J (ModuleCat A)).hom.app H)
        ((Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat A) (Type u)).obj
          (forget (ModuleCat A))) =
    (freeNegativeChainsDiagramAdjunction A J).homEquiv (W ⋙ SSet.uliftFunctor.{u,0})
      (complexOfFunctorsToFunctorToComplex.obj H)
      ((functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app
          (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0})) ≫
        complexOfFunctorsToFunctorToComplex.map f)
```

### 108.2 検収と登録

コード **`bbcc4861c`**（2本172行）。個別・結合検査`/private/tmp/isw2-linear-weight-evaluation3.log`・`/private/tmp/isw2-linear-free-hom-comparison3.log`は終了コード0。型の照合は元の随伴の合成単位・後合成・指定生成元評価を明示し、計算上限は変更していない。

鍵付き対象ビルド`/private/tmp/isw2-build123.log`は **2,594 jobs・終了コード0**。新規分だけの監査`/private/tmp/AuditISW2G10B02LinearHom.lean`は **9宣言（3・6）・標準三公理のみ**。共有鍵は返却済み。累計 **228モジュール・13,618行・2,107宣言**。直前の226本の一覧を実ファイルから数え直し、13,446行であることも確認した。新しい一覧は`/private/tmp/isw2-g10-twohundredtwentyeight-modules.txt`。外枠14,500行まで残り882行。

新公理・sorryなし、既存宣言・⑤a・入口・公式監査・mainの変更なし。登録対象は108.1の2本。大きな監査は行っていない。

### 108.3 残り

B02はまだ未完。元の線形重みHomからA09の自由鎖随伴への射の照合は今回閉じた。残るのは、同じAW比較・Hom–Tot比較と、標準成分模型で定めた実豊穣合成の全単体での一致。その後にB03〜B08の指定native切断の族と極限性、Cの標準脚とD(A)輸送、Dの全図式射・指定錐の族・離散加群入口が残る。今回の随伴の照合をAW合成の一致の代用にしない。目標「Dまで進めてください」はactiveのまま。


## 109. B02の途中：実Moore射影を通した標準Hom最上位成分の回収

B3はmainだけの凍結との11-13 23時の連絡に従い、mainを取り込まず、作業枝で検証とコミットを続けた。対象ビルドと新規分だけの監査に限り、大きな監査は実行していない。

### 109.1 部分補題と型

B02の実豊穣合成の成分照合のうち、標準HomをMoore正規化する段を分割した。最上位成分の評価が退化上で消えることを既存の非単射引き戻し公式から示し、Mathlibの既存の退化消滅判定で実射影PInftyを消去する。さらに既存の正規化包含との可換式により、指定射影から正規化最上位評価への合成が元の生の評価になることを示した。射影や比較射を作り直していない。

これはB02の同じ成分照合の証明分割（§14）であり、新しい独立した前提計算や照合の枠を追加しない。前提計算枠はB02 3/3、照合枠は全体3/3のまま。名前空間はDiagramComparison。`{R : Type u}`・`[CommRing R]`・`{D : Type v}`・`[DGCategory R D]`を固定する。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardHomTopProjection`

```lean
theorem standardTopEval_degeneraciesVanish (x y : D) (n : ℕ) :
    DegeneraciesVanish (n := n) (X := standardModule (R := R) x y)
      (ModuleCat.ofHom (standardTopEval (R := R) x y n))
```

```lean
theorem standardTopEval_PInfty (x y : D) (n : ℕ) :
    (PInfty (X := standardModule (R := R) x y)).f n ≫
      ModuleCat.ofHom (standardTopEval (R := R) x y n) =
    ModuleCat.ofHom (standardTopEval (R := R) x y n)
```

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardHomNormalizedTop`

```lean
theorem standardMooreTopMap_inclusion (x y : D) (n : ℕ) :
    standardMooreTopMap (R := R) x y n =
      (inclusionOfMooreComplexMap (standardModule (R := R) x y)).f (n + 1) ≫
        ModuleCat.ofHom (standardTopEval (R := R) x y (n + 1))
```

```lean
theorem standardMooreTopMap_projection (x y : D) (n : ℕ) :
    (DoldKan.PInftyToNormalizedMooreComplex (standardModule (R := R) x y)).f (n + 1) ≫
      standardMooreTopMap (R := R) x y n =
    ModuleCat.ofHom (standardTopEval (R := R) x y (n + 1))
```

### 109.2 検収と登録

コード **`a3182379a`**（2本117行）。個別検査`/private/tmp/isw2-top-projection5.log`・`/private/tmp/isw2-normalized-top2.log`は終了コード0。零次数の退化消滅の定義は非公開なので、既存の判定定理を使って処理した。計算上限は変更していない。

最終ソースの鍵付き対象ビルド`/private/tmp/isw2-build125.log`は **3,764 jobs・終了コード0**。新規分だけの監査`/private/tmp/AuditISW2G10B02NormalizedTop.lean`は **4宣言（2・2）・標準三公理のみ**。共有鍵は返却済み。累計 **230モジュール・13,735行・2,111宣言**。対象一覧は`/private/tmp/isw2-g10-twohundredthirty-modules.txt`。外枠14,500行まで残り765行。

新公理・sorryなし。既存宣言・⑤a・入口・公式監査・mainの変更なし。登録対象は109.1の2本。

### 109.3 残り

B02は未完。今回の式はMoore正規化前後の実評価の照合であり、AW比較・Hom–Tot比較と実豊穣合成の全単体の一致を済ませたとは扱わない。そこから指定native切断の族・極限性（B03〜B08）、標準脚・D(A)輸送（C）、全図式射・指定錐の族・離散加群入口（D）へ進む。停止点2の完了報告ではない。


## 110. B02の途中：指定DK同型と実AW合成の全正次数の評価

### 110.1 同じ成分照合の分割と型

同じ随伴Homの逆写像の式と、Moore射影の既存の自然性を複体の射として合成した。指定DK同型の像を、同じΓのMoore射影・同じ余単位・同じ正次数項同型で評価すると、元の標準Homの最上位成分を回収する。零次数だけの公式で済ませず、任意の正次数を扱う。

これを実標準合成`standardAW`へ適用し、DK像の実評価が元の`awTerm`の全切断点の和となる式を閉じた。標準合成を別のΓ上の演算に置き換えていない。B02の同じ成分照合の証明分割（§14）であり、独立した前提計算・照合の枠を追加しない。B02前提計算3/3・全体照合3/3はそのまま。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardDoldKanProjectedEvaluation`。
名前空間はDiagramComparison、`{R : Type u}`・`[CommRing R]`、後二本は`{D : Type v}`・`[DGCategory R D]`。

```lean
theorem doldKanHomEquiv_projected_eval (W : SimplicialObject (ModuleCat R))
    (K : ChainComplex (ModuleCat R) ℕ)
    (f : (normalizedMooreComplex (ModuleCat R)).obj W ⟶ K) (n : ℕ) :
    (((Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat R) ≌
      ChainComplex (ModuleCat R) ℕ).toAdjunction.homEquiv W K) f).app (Opposite.op ⦋n⦌) ≫
      (DoldKan.PInftyToNormalizedMooreComplex (Abelian.DoldKan.Γ.obj K)).f n ≫
      (Abelian.DoldKan.equivalence.counitIso.hom.app K).f n =
    (DoldKan.PInftyToNormalizedMooreComplex W).f n ≫ f.f n
```

```lean
theorem standardDoldKanModuleIso_positive_projected_eval (x y : D) (n : ℕ) :
    (standardDoldKanModuleIso (R := R) x y).hom.app (Opposite.op ⦋n + 1⦌) ≫
      (DoldKan.PInftyToNormalizedMooreComplex
        (doldKanHomModule (R := R) x y)).f (n + 1) ≫
      (Abelian.DoldKan.equivalence.counitIso.hom.app
        (connectiveHomComplex (R := R) x y)).f (n + 1) ≫
      (connectiveHomComplex_positiveIso (R := R) x y n).hom =
    ModuleCat.ofHom (standardTopEval (R := R) x y (n + 1))
```

```lean
theorem standardDoldKanAW_positive_projected_eval {x y z : D} {n : ℕ}
    (g : StandardSimplex R y z (n + 1)) (f : StandardSimplex R x y (n + 1)) :
    ((standardDoldKanModuleIso (R := R) x z).hom.app (Opposite.op ⦋n + 1⦌) ≫
      (DoldKan.PInftyToNormalizedMooreComplex
        (doldKanHomModule (R := R) x z)).f (n + 1) ≫
      (Abelian.DoldKan.equivalence.counitIso.hom.app
        (connectiveHomComplex (R := R) x z)).f (n + 1) ≫
      (connectiveHomComplex_positiveIso (R := R) x z n).hom) (standardAW g f) =
    ∑ j : (Finset.univ : Finset (Fin (n + 2))),
      awTerm g.val f.val Finset.univ j (-(n + 1 : ℤ)) (by simp)
```

### 110.2 検収と登録

コード **`7000f0623`**（1本104行）。個別検査`/private/tmp/isw2-dk-projected5.log`は終了コード0。結合則は複体の射のまま整理してから各項へ移し、計算上限は変更していない。

鍵付き対象ビルド`/private/tmp/isw2-build126.log`は **3,765 jobs・終了コード0**。新規分のみの監査`/private/tmp/AuditISW2G10B02ProjectedDK.lean`は **4宣言・標準三公理のみ**。共有鍵は返却済み。累計 **231モジュール・13,839行・2,115宣言**。対象一覧は`/private/tmp/isw2-g10-twohundredthirtyone-modules.txt`、外枠14,500行まで残り661行。

新公理・sorryなし。既存宣言・⑤a・入口・公式監査・mainの変更なし。B3中は対象ビルド・新規分の小さな監査だけとし、枝でコミットを続けた。

### 110.3 残り

B02は未完。今回の実AW側の評価を、A09の自由鎖AW比較の切断点ごとの値、同じ自由鎖Hom随伴、Hom–Tot比較へ接続して全単体の等式を閉じる必要がある。単なる正規化後の値の回収だけで元の比較射の等式を済ませたとは扱わない。その後にB03〜B08、C、Dが残る。停止点2の完了報告ではなく、目標「Dまで進めてください」はactiveのまま。


## 111. 3b-2：外枠に近づいた時点の残工程の再検討と中間停止

### 111.1 authoritative state と短い経路の確認

作業枝`math/inf-supply-b`の検証済みコードは`7000f0623`、報告は`8d8f5ba5a`。作業木はclean、対象ビルド126と新規分監査は終了コード0、実行中のビルドはない。231本の一覧から実ファイルを数え直し、**13,839行**であることを確認した。外枠14,500行まで **661行**。

B02で残るのは、A09の自由鎖AWの各切断の値と§110の実標準AWの各切断の値を、指定随伴・Hom–Tot比較を介して同じ全単体の式へ結ぶこと。§110はこのうち実標準AW側を閉じたもので、自由鎖側と同じ射になったとは数えない。

B04〜B06を短く済ませるため、`ReflectedWeightedNativeCone`・`ReflectedWeightedHomComparison`・`CoherentConeNativeComparison`・`CoherentConeFamilyHomotopy`を読み直した。既存の`reflectedCoherentConeFamilyComparison`とその`_evaluation`は、頂点評価を正しくする選んだ切断の族を与える。しかし、その制限が指定`reflectedWeightedHomComparison`との合成に**等しい**というB06の式は、これらから直接は得られない。既存の族をB04に代入してB06をホモトピーの存在に弱めることはしない。指定重み付き入力から全高次単体の族を構成し、頂点評価と制限を同時に照合する工程が残る。

### 111.2 残量と停止理由

§73の型を維持した見込み。これは実装量の予測であり、数学的な行数下限ではない。特にCとDは未着手であるため、§72.2の見込みを根拠なく縮めない。新しい第五のまとまりは要求していない。

| §72.2／§73のまとまり | 現状と残る型 | 追加見込み |
| --- | --- | ---: |
| 正規化テンソル／積重み | A01〜A12完了。残る最終の実合成との照合は以下のB02に数える | 0行 |
| 指定豊穣Homとnative極限性 | B01完了。B02の自由鎖AW・Hom–Totとの全単体の等式、B03、B04〜B06の指定族と両評価、B07〜B08 | 400〜700行 |
| 標準脚とD(A)輸送 | C01〜C07未完。元の標準脚、同じ全join射の輸送、元のstrict図式との照合 | 400〜700行 |
| 全図式射・指定錐の族・離散入口 | D01〜D08未完。全パラメータ族の境界・各点・辺、離散制限、ホモロジー入口 | 500〜900行 |
| 合計 | | **1,300〜2,300行** |

完成見込みは **15,139〜16,139行**。CとDだけの従来見込み900〜1,600行も、残枠661行を超える。B02の小さい計算補題を足し続けて外枠を使い切るのではなく、「超えそうなら検証済みを保存して報告し止める」という条件に従い、**3b-2の追加Leanはここで中間停止する**。

検証済みの分はすべてコミット済みであり、未検証の下書きはない。停止点2ではない。範囲や型を弱めず、Dを3b-3へ移さず、既存宣言・⑤a・mainを変更せず、外枠を独自に引き上げない。再開には残工程と外枠についての調整が必要。目標「Dまで進めてください」は未達成のまま保持する。今回がこの外枠に関する新たな中間停止の最初のターンであり、goalをcompleteやblockedには変更しない。

## 112. 代わりの紙の作業：3b-4の既存strict模型と3b-3の受け渡しの再確認

この節は読み取りと型案のみ。Leanの宣言・新しい模型内部への参照は追加せず、ビルドの鍵も取得していない。B3の連絡に従いmainをmergeしていない。mainの読み取り時のrefは`40faa3892120211786cf463371a356c3fc9de6e1`。

### 112.1 既存部品との重複を避ける

`BarrattEccles/FramedLimit.lean`には、既に任意の小図式の**全関手**`framedLimitFunctor A K`と台の`framedLimitCarrierIso`がある。`FramedLimitCarrierDerivedComparison.lean`には、複体の通常局所化における`carrierFramedLimitComparisonIso`と、元の通常錐との両立`carrierFramedLimitComparisonIso_cone`がある。したがって、3b-4 §38.2の1・2でBEの右frame/endやその通常局所化の対象比較を新規に作り直す必要はない。これらの既存ファイルは⑤a側の部品として変更しない。実装再開時は新規ファイルで橋だけを作る。

ただし、通常局所化の同型や各対象の台の同型だけを、指定native錐の族を保つ∞関手同型と同一視しない。既存`algebraCAlgSource_underlyingDerivedIso`が与えるのは実Uと元の通常忘却の全比較であり、これと上記通常局所化の比較をつなぐ全高次単体の工程が必要。

紙の略記として、`J = Δ`に固定し、次の二つの全単体的射を比較する段を切り出す（ここでは新しいLean宣言として検査した型ではない）。

```lean
F_BE := nerveMap (framedLimitFunctor A J) ≫ algebraCAlgSource A ≫ cAlgForgetDerived A
F_DA := nerveMap (Diagram.forget A J ⋙ ComplexLimits.framedLimitFunctor A J) ≫
  ComplexLimits.complexOrdinaryDerivedSource A
-- 必要な強さ：FunctorIso F_BE F_DA と、同じ指定全錐族の輸送の式。
```

`FreeProbeDerivedLimits.lean`の`cAlgForgetDerived_mapJoinCone_isLimit_of_transport`は、`FreeProbeUnitTransportCondition A`を**明示的に仮定**する。この仮定を無条件の供給済み結果として使わず、⑤a側の供給点を確認する。右Quillen性やprojective図式の全対象fibrant性だけで、通常limを導来limと同定することもしない。

### 112.2 ③-aのR6で使える形と、まだ別の入力

mainを読み取ると、`StrictSemifreeComputedColimitFamily.lean`に`strictSemifreeComputedColimitFamilyIso`と、包含後の同じ全余錐族の比較`strictSemifreeComputedCoconeFamilyIso`がある。`StrictSemifreeRealizationFamily.lean`には、同じ実現全関手の族・頂点・辺の式がある。これらは、§38.1で求めた「3b-1から移したstrict加群図式の全パラメータ比較」に対応する受け取り候補である。B3後のB4で名前と型を引き直して使う。今は枝へ取り込まず、既存ファイルの変更やコピーもしない。

このR6の供給を、任意のcoherent BE図式の厳密化の代わりには使わない。③-aの加群図式の比較は加群値の3b-3であり、BE作用を回復する全coherent図式の比較は§38.2の3として別に残る。strict BE図式の模型計算とそのU比較が済む前から、この追加の厳密化を仮定に押し込んだ主張を作らない。

今回の紙の確認により、3b-4で最初に重複を避ける対象は上記の既存`FramedLimit*`・`CAlgUnderlyingDerivedComparison`、受け取り候補はR6の全余錐族の同型と明確になった。G10（3b-2）は未完のままなので、これを完了扱いして3b-4のLeanへ移ってはいない。



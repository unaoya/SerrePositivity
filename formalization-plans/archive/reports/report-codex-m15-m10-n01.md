# BS-M15（⑤d）作業報告 — M15 再開・M10 着手・N01（§14〜§25、2026-11-14）

元の報告：[report-codex-m15.md](../../bhatt-scholze/reports/report-codex-m15.md)

## 14. M15 再開：同じ自由局所化の全係数自然性（11-14）

B4 は §13・`735c38752` で完了したので、保持していた下書き二つの検証へ戻る。
M10 の同じ相対局所化の係数移送の法則として、既存の自由 hammock の全 Hom 作用を
豊穣関手・同じ Kan 化・全 coherent nerve へ束ねる。
元の左右比較の可換正方形を全 nerve の等式にし、同じ augmentation の逆の
既存の選択を通して、局所化の源の写像との全関手間の自然性を回収する。
全単体を保持し、頂点ごとの同型の族だけにはしない。

以下が今回検証する実際の型。新しい一次 ID は追加せず、既存の係数移送・自然性・
貼り合わせの証明の分割として扱う。共通文脈は `C D : RelativeCategory.{u}`、`F : C ⟶ D`。

`SerrePositivity/EInfinity/Modules/FreeHammockCoefficientNerve.lean`：

```lean
def freeHammockCoefficientEnriched :
    EnrichedFunctor SSet.{u} (FreeHammockObjects C) (FreeHammockObjects D)

def kanFreeHammockCoefficientFunctor :
    EnrichedFunctor SSet.{u} (KanFreeHammockCategory C) (KanFreeHammockCategory D)

def kanFreeHammockCoefficientNerve : kanFreeHammockNerve C ⟶ kanFreeHammockNerve D

lemma kanFreeHammockCoefficient_augmentation :
    (kanFreeHammockCoefficientFunctor F).comp SSet (kanFreeHammockAugmentationFunctor D) =
      (kanFreeHammockAugmentationFunctor C).comp SSet (relativeKanHammockFunctor F)

lemma kanFreeHammockCoefficient_comparison :
    (kanFreeHammockCoefficientFunctor F).comp SSet (kanFreeHammockComparisonFunctor D) =
      (kanFreeHammockComparisonFunctor C).comp SSet (kanLocalizationEnrichedMap F)

lemma kanFreeHammockCoefficientNerve_augmentation :
    kanFreeHammockCoefficientNerve F ≫ kanFreeHammockAugmentationNerve D =
      kanFreeHammockAugmentationNerve C ≫ relativeKanHammockNerve F

lemma kanFreeHammockCoefficientNerve_comparison :
    kanFreeHammockCoefficientNerve F ≫ kanFreeHammockComparisonNerve D =
      kanFreeHammockComparisonNerve C ≫ localizationNerveMap F
```

`SerrePositivity/EInfinity/Modules/LocalizationSourceNaturality.lean`：

```lean
def kanHammockLocalizationCoefficientIso :
    FunctorIso (relativeKanHammockNerve F ≫ (kanHammockLocalizationEquivalence D).hom)
      ((kanHammockLocalizationEquivalence C).hom ≫ localizationNerveMap F)

def localizationNerveSourceNaturalityIso :
    FunctorIso (localizationNerveSourceMap C ≫ localizationNerveMap F)
      (nerveMap F.functor ≫ localizationNerveSourceMap D)
```

文献属性は、coherent nerve の作用を HTT Definition 1.1.5.5 の `component`、
同じ全関手間の比較を HTT §1.2.7 の `component` として、各宣言に対応範囲を記す。
Definition 1.1.5.5 の原文は [HTT 原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf)
で確認した。一般の局所化の普遍性をこれらの宣言で証明したという属性にはしない。

この自然性ができても、指定弱自然変換の成分の辺との全照合、
半自由 native fiber の比較と全族の native cocartesian 性は引き続き必要。
M10 の完了には数えていない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 14.1 検証済みの結果と実測

二つのモジュールの正規 Lake 対象ビルドが、指定の共有鍵の下で通過した。
同じ自由局所化の Kan 豊穣係数関手、左右の全 nerve 正方形、
`kanHammockLocalizationCoefficientIso` と `localizationNerveSourceNaturalityIso` を
全て実際の型で構成できた。型指定・宇宙指定を明示し、元の全 Hom 写像は保持した。

公開 9 宣言の `#print axioms` と、その同じ 9 宣言の文献属性の環境検査を、
別の共有鍵の組で行い、終了コード 0。実出力の宣言名集合・件数が一致し、
依存公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
`sorryAx`・追加公理はない。全 9 件に HTT の `component` 属性が一件ずつ登録され、
番号は 7 件が `1.1.5.5`、2 件が `1.2.7` と確認した。

今回の追加は新規 Lean 2 ファイル・181 行・9 宣言（公開）。
`FreeHammockCoefficientNerve.lean` が 110 行・7 宣言、
`LocalizationSourceNaturality.lean` が 71 行・2 宣言。
200 行を超える補題はない。
累計は新規 Lean **32 ファイル・3,000 行・169 宣言（private 3 を含む）**。
既存構成の係数移送・自然性・貼り合わせの法則の分割なので一次 ID の追加はない。

B4 追従は §13 で完了済み。M15 は再開しているが、M10 の native fiber・
cocartesian 性、相対テンソル、RHom・完備反射・完備テンソルと G12 は引き続き未完。

**一覧：済み 9／全体 42（うち追加 0）**。

## 15. M10 の指定生成射と係数作用の照合（11-14、着手）

§14 の全係数自然性を元の指定弱辺に接続するため、既存の同じ係数作用について、
自由解像の零次の一文字の射、hammock の指定零単体・点、Kan 化した同じ射、
coherent nerve の実一単体の保存を照合する。
新しい模型や対象ごとの別の辺を選ばず、元の射 f と同じ二端点を保持する。
M10 の既存構成の係数移送・自然性の法則の分割で、一次 ID の追加はない。

`EInfinity/Modules/LocalizationArrowCoefficients.lean` の今回の型を記録する。
共通文脈は `C D : RelativeCategory.{u}`、`F : C ⟶ D`、`X Y : C.category`。

```lean
lemma freeResolutionArrowZero_coefficient (f : X ⟶ Y) :
    eqToHom (freeResolutionMap_object F (op ⦋0⦌) X).symm ≫
      ((freeResolutionMap F).app (op ⦋0⦌)).functor.map (freeResolutionArrowZero C f) ≫
        eqToHom (freeResolutionMap_object F (op ⦋0⦌) Y) =
      freeResolutionArrowZero D (F.functor.map f)

lemma freeHammockArrowZero_coefficient (f : X ⟶ Y) :
    (freeHammockDiagonalMap F X Y).app (op ⦋0⦌) (freeHammockArrowZero C f) =
      freeHammockArrowZero D (F.functor.map f)

lemma freeHammockArrowPoint_coefficient (f : X ⟶ Y) :
    freeHammockArrowPoint C f ≫ freeHammockDiagonalMap F X Y =
      freeHammockArrowPoint D (F.functor.map f)

lemma localizationArrowPoint_coefficient (f : X ⟶ Y) :
    localizationArrowPoint C f ≫ localizationHomMap F X Y =
      localizationArrowPoint D (F.functor.map f)

lemma kanLocalizationStrictHom_coefficient (f : X ⟶ Y) :
    (kanLocalizationFunctor F).map (kanLocalizationStrictHom C f) =
      kanLocalizationStrictHom D (F.functor.map f)

lemma kanFreeHammockStrictHom_coefficient (f : X ⟶ Y) :
    (kanFreeHammockCoefficientFunctor F).forget.map (kanFreeHammockStrictHom C f) =
      kanFreeHammockStrictHom D (F.functor.map f)

lemma localizationStrictEdge_coefficient (f : X ⟶ Y) :
    ((coherentNerveEdge (kanLocalizationStrictHom C f)).map (localizationNerveMap F)).edge =
      (coherentNerveEdge (kanLocalizationStrictHom D (F.functor.map f))).edge

lemma freeHammockStrictEdge_coefficient (f : X ⟶ Y) :
    ((coherentNerveEdge (kanFreeHammockStrictHom C f)).map (kanFreeHammockCoefficientNerve F)).edge =
      (coherentNerveEdge (kanFreeHammockStrictHom D (F.functor.map f))).edge
```

この辺の保存の後には、既存の `SourceHom.localizationStrictSourceIso_naturality` を
使って、元の弱射の反転と同じ native 辺を接続する。
これらはまだ半自由 native fiber の同定や全族の cocartesian 性を供給していない。
検証済みの一覧の数は据え置く。

**一覧：済み 9／全体 42（うち追加 0）**。

### 15.1 指定弱射の実辺と BE の同じ標準 lift（検証中）

`LocalizationStrictWeak.lean` は、既存の源の反転性を
`localizationStrictSourceIso_naturality` の四角形で共役し、元の指定射から作った
同じ辺そのものの可逆性を示す。共通文脈は `C : RelativeCategory.{u}`。

```lean
lemma localizationStrictEdge_invertible_of_weak {X Y : C.category}
    (f : X ⟶ Y) (hf : C.weakEquivalences f) :
    IsInvertibleEdge (coherentNerveEdge (kanLocalizationStrictHom C f)).toTruncated
```

`BarrattEccles/Modules/NativeCartesianWeak.lean` では、同じ標準 lift の局所化辺と
底への射影を指定する。共通文脈は `A : Type u`、`[CommRing A]`。

```lean
def moduleTotalVertex (M : strictRawModuleTotal A) : (moduleTotalInfinity A) _⦋0⦌

def moduleCartesianLiftEdge {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    SSet.Edge (moduleTotalVertex A
      ((strictRawModuleFiberInclusion A X).obj ((strictRawModuleRestrict f).obj M)))
      (moduleTotalVertex A ((strictRawModuleFiberInclusion A Y).obj M))

lemma moduleCartesianLiftEdge_invertible {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    IsInvertibleEdge (moduleCartesianLiftEdge A f M).toTruncated

lemma moduleCartesianLiftEdge_projection {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    ((moduleCartesianLiftEdge A f M).map (moduleTotalProjection A)).edge =
      (coherentNerveEdge (kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
        ((algebraToCofibrantDKRelative A).functor.map
          ((ULiftHom.up.{u,u+1,u+1} (C := (operad A).Algebra)).map f)))).edge

```

可逆性の文献番号は、[HTT 原典](https://www.math.ias.edu/~lurie/papers/HTT.pdf)
§1.2.4 の「同じ辺の像がホモトピー圏で同型」という定義に対応させる。
Proposition 1.2.4.3 の外側 horn の持ち上げによる判定そのものを証明したとはしない。
BE の底が弱同値の場合の標準 lift に適用し、別の可逆辺へ取り替えない。
これらも M10 の指定射・係数作用・反転の法則の分割で、追加の一次 ID はない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 15.2 検証済みの結果と実測

三つの新規モジュールの正規 Lake 対象ビルドが、指定の共有鍵の下で通過した。
自由解像の零次から実一単体までの指定生成射の保存、同じ弱射の指定辺の可逆性、
BE の元の標準 lift の実局所化辺と射影先の指定辺との等式が得られた。
切り詰め写像の元の準圏を明示し、源の選択逆を含む型照合に限って
`LocalizationStrictWeak` の一補題の `maxHeartbeats` を局所的に 800,000 とした。

今回の公開 13 宣言の `#print axioms` と文献属性の環境検査も、別の共有鍵で
終了コード 0。実出力は同じ 13 宣言と 13 属性に一致する。
依存公理は `propext`・`Classical.choice`・`Quot.sound` のみで、
`sorryAx`・追加公理はない。文献属性は全て HTT の `component` で一件ずつ、
11 件が `1.1.5.5`、弱辺反転の 2 件が `1.2.4` と各宣言について確認した。

追加は新規 Lean **3 ファイル・286 行・13 宣言（公開）**。
`LocalizationArrowCoefficients.lean` が 139 行・8 宣言、
`LocalizationStrictWeak.lean` が 68 行・1 宣言、
`NativeCartesianWeak.lean` が 79 行・4 宣言。
200 行を超える補題はない。
累計は新規 Lean **35 ファイル・3,286 行・182 宣言（private 3 を含む）**。
既存構成の係数移送・反転・指定射の照合の法則の分割で、一次 ID の追加はない。

B4 は §13 で完了済み。M10 の全関手比較と指定弱自然変換の成分の辺の照合、
半自由 native fiber の同定と全族の native cocartesian 性は引き続き必要。
今回の可逆性だけで M10 を完了とは数えない。

**一覧：済み 9／全体 42（うち追加 0）**。

## 16. M10 の全比較の成分と指定された円筒辺（11-14、着手）

前の goal ターンは、§15 の三つの対象ビルドと 13 宣言の小さい監査を通し、
`e5b5413b9` で検証済みの実辺の保存・弱 lift の反転をコミットした進捗。
今回は、円筒の同値の選択逆から作った全関手間の比較の成分が、
元の弱自然変換の指定辺と一致することを照合する。
対象ごとの別の可逆辺を選ぶのではなく、元の比較・元の射を保持する。
M10 の既存構成の前合成・成分評価・恒等・自然性の法則の分割で、一次 ID は足さない。

最初に使う補助法則の型は次のとおり。
`LocalizationComparisonEvaluation.lean` の文脈は `A B Y : SSet.{u}`、
`[Quasicategory Y]`。既存の後合成・合成・反転の評価則は import して使う。

```lean
lemma functorHomotopyEvaluation_precomp_map_app
    (q : A ⟶ B) {v w : ((ihom B).obj Y) _⦋0⦌}
    (a : (SSet.HomotopyCategory.mk v : hoFunctor.obj ((ihom B).obj Y)) ⟶
      SSet.HomotopyCategory.mk w) (x : A _⦋0⦌) :
    ((functorHomotopyEvaluation A Y).map
      ((hoFunctor.map ((pre q).app Y)).toFunctor.map a)).app (SSet.HomotopyCategory.mk x) =
      ((functorHomotopyEvaluation B Y).map a).app
        (SSet.HomotopyCategory.mk (q.app (Opposite.op ⦋0⦌) x))

lemma functorIso_precomp_hom_app {f g : B ⟶ Y}
    (e : FunctorIso f g) (q : A ⟶ B) (x : A _⦋0⦌) :
    (e.precomp q).toNatIso.hom.app (SSet.HomotopyCategory.mk x) =
      e.toNatIso.hom.app (SSet.HomotopyCategory.mk (q.app (Opposite.op ⦋0⦌) x))
```

`LocalizationStrictIdentity.lean` の文脈は `C : RelativeCategory.{u}`。
指定生成辺そのものが退化辺と等しいとは仮定しない。

```lean
lemma localizationStrictHom_id (X : C.category) :
    SSet.HomotopyCategory.homMk (coherentNerveEdge (kanLocalizationStrictHom C (𝟙 X))) =
      𝟙 _
```

**一覧：済み 9／全体 42（うち追加 0）**。

### 16.1 同じ選択逆の比較と指定交差射の型

前合成・等式比較の評価は次も使う。共通文脈は `A Y : SSet.{u}`。

```lean
lemma functorIso_eqToIso_hom_app {f g : A ⟶ Y} (h : f = g) (x : A _⦋0⦌) :
    (show FunctorIso f g from
      eqToIso (congrArg (fun k => SSet.HomotopyCategory.mk (functorVertex k)) h)).toNatIso.hom.app
      (SSet.HomotopyCategory.mk x) =
    eqToHom (congrArg (fun k : A ⟶ Y => SSet.HomotopyCategory.mk
      (k.app (Opposite.op ⦋0⦌) x)) h)
```

自分の既存 `RelativeNaturalComparison` の局所的な端点比較を、次の名前付きの
法則に分けた。同じ射影の同じ選択逆と可逆二胞体を保持し、全関手の等式による
輸送だけを明示する。既存の両端点比較・弱自然変換比較の型は変更しない。

```lean
def relativeCylinderInverseEndpointIso (C : RelativeCategory.{u}) (i : Fin 2) :
    FunctorIso (relativeCylinderProjection_isQCatEquivalence C).choose.inv
      (localizationNerveMap (relativeCylinderEndpoint C i))
```

以下は `RelativeCylinderPrescribedEdge` と `RelativeCylinderComponent` の今回の型。
同じ円筒を使い、最後の成分の主張へつなぐ法則の分割。

`RelativeCylinderPrescribedEdge.lean`：

```lean
lemma localizationStrictHom_coefficient_class {C D : RelativeCategory.{u}} (F : C ⟶ D)
    {X Y : C.category} (f : X ⟶ Y) :
    eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex F X)).symm ≫
      (hoFunctor.map (localizationNerveMap F)).toFunctor.map
        (SSet.HomotopyCategory.homMk (coherentNerveEdge (kanLocalizationStrictHom C f))) ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex F Y)) =
        SSet.HomotopyCategory.homMk
          (coherentNerveEdge (kanLocalizationStrictHom D (F.functor.map f)))

lemma relativeCylinderEndpoint_projection_vertex (i : Fin 2) (x : (localizationNerve C) _⦋0⦌) :
    (localizationNerveMap (relativeCylinderProjection C)).app (Opposite.op ⦋0⦌)
      ((localizationNerveMap (relativeCylinderEndpoint C i)).app (Opposite.op ⦋0⦌) x) = x

def relativeCylinderCrossingClass (X : C.category) :
    SSet.HomotopyCategory.mk
      ((localizationNerveMap (relativeCylinderEndpoint C 0)).app (Opposite.op ⦋0⦌)
        (localizationNerveVertexEquiv C X)) ⟶
    SSet.HomotopyCategory.mk
      ((localizationNerveMap (relativeCylinderEndpoint C 1)).app (Opposite.op ⦋0⦌)
        (localizationNerveVertexEquiv C X))

lemma relativeCylinderCrossingClass_projection (X : C.category) :
    eqToHom (congrArg SSet.HomotopyCategory.mk
      (relativeCylinderEndpoint_projection_vertex C 0 (localizationNerveVertexEquiv C X))).symm ≫
    (hoFunctor.map (localizationNerveMap (relativeCylinderProjection C))).toFunctor.map
      (relativeCylinderCrossingClass C X) ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk
      (relativeCylinderEndpoint_projection_vertex C 1 (localizationNerveVertexEquiv C X))) = 𝟙 _

```

`RelativeCylinderComponent.lean`：

```lean
lemma relativeCylinderInverseEndpointIso_component (i : Fin 2)
    (x : (localizationNerve C) _⦋0⦌) :
    ((relativeCylinderInverseEndpointIso C i).app x).hom =
      eqToHom (congrArg (fun v => SSet.HomotopyCategory.mk
        ((relativeCylinderProjection_isQCatEquivalence C).choose.inv.app (Opposite.op ⦋0⦌) v))
        (relativeCylinderEndpoint_projection_vertex C i x)).symm ≫
      (((relativeCylinderProjection_isQCatEquivalence C).choose.homInvIso).app
        ((localizationNerveMap (relativeCylinderEndpoint C i)).app (Opposite.op ⦋0⦌) x)).hom

lemma relativeCylinderEndpointIso_component_of_projection
    (x : (localizationNerve C) _⦋0⦌)
    (a : SSet.HomotopyCategory.mk
      ((localizationNerveMap (relativeCylinderEndpoint C 0)).app (Opposite.op ⦋0⦌) x) ⟶
      SSet.HomotopyCategory.mk
      ((localizationNerveMap (relativeCylinderEndpoint C 1)).app (Opposite.op ⦋0⦌) x))
    (ha : eqToHom (congrArg SSet.HomotopyCategory.mk
      (relativeCylinderEndpoint_projection_vertex C 0 x)).symm ≫
      (hoFunctor.map (localizationNerveMap (relativeCylinderProjection C))).toFunctor.map a ≫
      eqToHom (congrArg SSet.HomotopyCategory.mk
        (relativeCylinderEndpoint_projection_vertex C 1 x)) = 𝟙 _) :
    ((relativeCylinderEndpointIso C).app x).hom = a

lemma relativeCylinderEndpointIso_component (X : C.category) :
    ((relativeCylinderEndpointIso C).app (localizationNerveVertexEquiv C X)).hom =
      relativeCylinderCrossingClass C X

```

ここで `relativeCylinderEndpointIso_component` は、全関手間の比較そのものの
元の頂点での成分を、同じ指定交差射のホモトピー圏の類に等置する主張。
M10 の出力をホモトピー圏へ置き換えるものではなく、既存の native 比較の成分の法則。
全族の fiber の同定と cocartesian 性は別に必要。

**一覧：済み 9／全体 42（うち追加 0）**。

### 16.2 元の弱自然変換の指定成分への接続（検証中）

`localizationNerveMapIsoOfWeakNatTrans` でも、同じ円筒比較・同じ後合成を保持し、
全関手の零・一端点の等式による輸送を明示した。公開の型は変更していない。
指定単位・余単位を持つ弱自然変換に適用できるよう、次の成分の法則を作る。
文脈は `C D : RelativeCategory.{u}`、`F G : C ⟶ D`。

```lean
lemma relativeNaturalCylinder_crossing (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) (X : C.category) :
    (relativeNaturalCylinder η hη).functor.map ((relativeCylinderContraction C).app (1, X)) =
      η.app X

lemma localizationNerveMapIsoOfWeakNatTrans_component (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) (X : C.category) :
    eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex F X)).symm ≫
      ((localizationNerveMapIsoOfWeakNatTrans η hη).app (localizationNerveVertexEquiv C X)).hom ≫
    eqToHom (congrArg SSet.HomotopyCategory.mk (localizationNerveMap_vertex G X)) =
      SSet.HomotopyCategory.homMk (coherentNerveEdge (kanLocalizationStrictHom D (η.app X)))

```

最後の等式は、頂点比較の等式だけで両端を移した同じ全比較の成分を、元の
`η.app X` の指定生成辺の類に等置する。対象ごとの別の同型の存在に弱めない。
BE の往復比較がこの構成を使うため、影響する
`BarrattEccles/Modules/AlgebraRoundTripComparison` も対象ビルドに含める。

**一覧：済み 9／全体 42（うち追加 0）**。

## 17. M10 の同じ全射影の inner fibration 置換と弱 lift（11-14、下書き）

§16 の最後の検証の共有鍵待ちの間に、M10 の実射影の構成も進める。
元の `moduleTotalProjection` は任意の内ホーンの相対充填性をまだ持たないため、
既存の内ホーンの小対象論法を同じ射影に適用し、同じ CAlg 上で置換する。
元の全圏からの包含は inner anodyne で準圏同値、射影の合成は全単体で等しい。
新しい `[ModelCategory SSet]` や外部の分解データは入力に加えない。
これは M10 の既存の全族の射影構成の証明の分割で、一次 ID の追加はない。

指定弱 lift は元の実辺をこの包含で写したものとし、構成した inner fibration と
同じ辺の可逆性から、native な Cartesian・cocartesian 条件を適用する。
弱底変更の場合に限る。一般の底の辺の lift の存在・相対性や半自由 fiber の同定を
この置換で証明済みとはしない。
文献は HTT Theorem 2.0.0.6、Proposition 2.4.1.5、
Kerodon Theorem 5.2.4.1（Tag 024N）・Proposition 5.1.1.9（Tag 01TB）。

以下の型は文脈 `A : Type u`、`[CommRing A]`。分解データはファイル内で一度選ぶ。

`TotalInnerReplacement.lean`：

```lean
def moduleTotalInnerFactorization :
    MapFactorizationData innerHornInclusions.rlp.llp innerHornInclusions.rlp
      (moduleTotalProjection A)

def moduleTotalInnerInfinity : SSet.{u+1}

def moduleTotalInnerInclusion : moduleTotalInfinity A ⟶ moduleTotalInnerInfinity A

def moduleTotalInnerProjection : moduleTotalInnerInfinity A ⟶ CAlg_R A

instance moduleTotalInnerProjection_innerFibration : InnerFibration (moduleTotalInnerProjection A)

instance moduleTotalInnerInfinity_quasicategory : Quasicategory (moduleTotalInnerInfinity A)

lemma moduleTotalInnerInclusion_innerAnodyne : innerAnodyneExtensions (moduleTotalInnerInclusion A)

lemma moduleTotalInnerInclusion_projection :
    moduleTotalInnerInclusion A ≫ moduleTotalInnerProjection A = moduleTotalProjection A

lemma moduleTotalInnerInclusion_isQCatEquivalence : IsQCatEquivalence (moduleTotalInnerInclusion A)

```

`NativeInnerWeakLift.lean`：

```lean
def moduleInnerCartesianLiftEdge {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    SSet.Edge ((moduleTotalInnerInclusion A).app (Opposite.op ⦋0⦌)
      (moduleTotalVertex A ((strictRawModuleFiberInclusion A X).obj
        ((strictRawModuleRestrict f).obj M))))
      ((moduleTotalInnerInclusion A).app (Opposite.op ⦋0⦌)
        (moduleTotalVertex A ((strictRawModuleFiberInclusion A Y).obj M)))

lemma moduleInnerCartesianLiftEdge_invertible {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    IsomorphismsAndIsofibrations.IsInvertibleEdge (moduleInnerCartesianLiftEdge A f M).toTruncated

lemma moduleInnerCartesianLiftEdge_projection {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    ((moduleInnerCartesianLiftEdge A f M).map (moduleTotalInnerProjection A)).edge =
      (coherentNerveEdge (kanLocalizationStrictHom (cofibrantAlgebraRelativeCategory A)
        ((algebraToCofibrantDKRelative A).functor.map
          ((ULiftHom.up.{u,u+1,u+1} (C := (operad A).Algebra)).map f)))).edge

lemma moduleInnerCartesianLiftEdge_cartesian {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    IsCartesianEdge (moduleTotalInnerProjection A) (moduleInnerCartesianLiftEdge A f M).edge

lemma moduleInnerCartesianLiftEdge_cocartesian {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    IsCocartesianEdge (moduleTotalInnerProjection A) (moduleInnerCartesianLiftEdge A f M).edge

```

これら二ファイルはまだ対象ビルド・小さい監査の前の下書き。
検証済み実測には加えず、M10 の完了にも数えていない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 17.1 検証済みの結果・実測と残る kernel 照合

§16 の前合成の評価・指定恒等辺・交差辺の係数作用と射影、
`relativeCylinderEndpointIso_component` までの全円筒比較の成分の一致、
§17 の同じ射影の inner fibration 置換と元の弱 lift の native な
Cartesian・cocartesian 性は、正規 Lake の対象ビルドが通過した。
影響する自分の `AlgebraRoundTripComparison` の対象も通過している。
全て指定の共有鍵 `--class impl --wait 3600` の下、各実行の上限を 280 秒とした。

上記の新規公開 26 宣言、同じ全比較の既存 2 宣言、影響する BE 往復比較の
既存 4 宣言の計 32 宣言について、小さい `#print axioms` 監査は終了コード 0。
32 件の出力と対象名を機械照合し、依存公理は `propext`・`Classical.choice`・
`Quot.sound` のみと確認した。追加公理・`sorryAx` はない。
文献属性も同じ新規 26・既存比較 2 の計 28 宣言について一件ずつ、HTT の
`component` と各宣言の指定番号に一致することを環境から検査し、終了コード 0。
大きい監査やルートビルドは行っていない。

検証済みの新規 Lean は **6 ファイル・539 行・25 宣言**。
内訳は `LocalizationComparisonEvaluation` 81 行・3 宣言、
`LocalizationStrictIdentity` 42 行・1 宣言、
`RelativeCylinderPrescribedEdge` 116 行・4 宣言、
`RelativeCylinderComponent` 118 行・3 宣言、
`TotalInnerReplacement` 91 行・9 宣言、
`NativeInnerWeakLift` 91 行・5 宣言。
自分の既存 `RelativeNaturalComparison` の証明の分割は差引 23 行・1 宣言追加。
200 行を超える補題はない。
検証済み累計は新規 Lean **41 ファイル・3,848 行・208 宣言（private 3 を含む）**。
一次 ID は追加していない。

§16.2 の `LocalizationWeakNatComponent` は未コミットの下書きとして残す。
最後の全弱自然変換の成分式は、型だけを仮定して返す独立した kernel 照合を行い、
終了コード 0 で型自体は確認した。一つの宣言にした証明は kernel の計算上限
（200,000・800,000）に達したため、個別の法則の宣言に分けて照合を続ける。
証明の範囲や型を弱めること、追加公理で埋めることはしていない。
この下書きは上記の検証済み実測に含めないが、17,000 行の外枠には含めて管理する。

M10 は、最後の全弱自然変換の指定成分への接続、半自由 native fiber の同定、
一般の底の辺の lift・transport と全族の cocartesian 性が引き続き必要。
今回の inner fibration と弱 lift だけで M10 の完了とは数えない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 17.2 最後の成分の kernel 照合の分割（着手）

型だけの独立照合が通ったため、元の成分の型は保持して証明を分割する。
全比較の後合成の評価と同じ射の Arrow の一致を別の宣言にし、最後に同じ
`localizationNerveMap_vertex F/G` の等式による端点輸送へ戻す。
Arrow の等式には同じ射と両端の等式が含まれ、最後の主張は §16.2 の型のまま。
新たな数学の主張への範囲拡張ではなく、M10 の同じ成分の法則の証明の分割。
追加する分割の型は以下。共通文脈は `C D : RelativeCategory.{u}`、`F G : C ⟶ D`。

```lean
lemma localizationWeakNat_component_factorization (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) (x : (localizationNerve C) _⦋0⦌) :
    Arrow.mk (((localizationNerveMapIsoOfWeakNatTrans η hη).app x).hom) =
      Arrow.mk ((hoFunctor.map (localizationNerveMap (relativeNaturalCylinder η hη))).toFunctor.map
        (((relativeCylinderEndpointIso C).app x).hom))

lemma localizationWeakNat_component_arrow (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) (X : C.category) :
    Arrow.mk (((localizationNerveMapIsoOfWeakNatTrans η hη).app
      (localizationNerveVertexEquiv C X)).hom) =
      Arrow.mk (SSet.HomotopyCategory.homMk
        (coherentNerveEdge (kanLocalizationStrictHom D (η.app X))))

```

**一覧：済み 9／全体 42（うち追加 0）**。

### 17.3 同じ全比較の等式輸送の分割（着手）

全比較を両端の等式で移す法則を一般の関手比較について一度証明し、同じ弱自然変換の
比較はその法則を呼ぶ形にする。`localizationNerveMapIsoOfWeakNatTrans` は元の円筒比較・
後合成・二つの端点等式を保持する。公開の型や元の可逆二胞体は変えない。
`LocalizationComparisonEvaluation` に追加する法則は次の二つ。

```lean
def functorIsoTransport {A Y : SSet.{u}} {f g f' g' : A ⟶ Y}
    (e : FunctorIso f g) (hf : f = f') (hg : g = g') : FunctorIso f' g'

lemma functorIsoTransport_component_arrow {A Y : SSet.{u}}
    [Quasicategory A] [Quasicategory Y] {f g f' g' : A ⟶ Y}
    (e : FunctorIso f g) (hf : f = f') (hg : g = g') (x : A _⦋0⦌) :
    Arrow.mk (((functorIsoTransport e hf hg).app x).hom) = Arrow.mk ((e.app x).hom)
```

既存の全比較の等式輸送・成分評価の法則であり、一次 ID は追加しない。
元の §16.2 の成分式の型を保ち、kernel の計算のために範囲を縮めない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 17.4 最後の指定成分までの検証済み結果と実測

§16.2 の `localizationNerveMapIsoOfWeakNatTrans_component` は、元の型を保持して
正規 Lake の対象ビルド・kernel 照合を通過した。
等式輸送を `functorIsoTransport` の一般の法則へ分け、その同じ成分の法則を使い、
全比較の後合成、同じ射の Arrow の一致、元の頂点比較による両端の輸送へ分けた。
この最終ファイルの対象ビルドは 15 秒、計算上限の局所的変更は不要になった。
元の円筒の選択逆・可逆二胞体・同じ全比較を保持し、最後の主張の範囲も型も変更していない。
影響する `AlgebraRoundTripComparison` の対象も通過した。

今回の新規公開 32 宣言、同じ全比較の既存 2 宣言、BE 往復比較の既存 4 宣言の
計 38 宣言について、小さい `#print axioms` 監査が終了コード 0。
38 件の宣言名と実出力を機械照合し、依存公理は標準の
`propext`・`Classical.choice`・`Quot.sound` の範囲内。
追加公理・`sorryAx` はない。新規 32・既存比較 2 の計 34 宣言の文献属性も、
一件ずつの HTT `component` と、各宣言の指定した番号に一致することを環境から検査し、
終了コード 0。全て指定の共有鍵、実行上限 280 秒の組で行った。

この goal ターンの新規 Lean は **7 ファイル・667 行・31 宣言（公開）**。
`LocalizationComparisonEvaluation` は最終 99 行・5 宣言、
`LocalizationWeakNatComponent` は最終 110 行・4 宣言。
他の五つのファイルの実測は §17.1 と同じ。
自分の既存 `RelativeNaturalComparison` はこのターン全体で差引 21 行・1 宣言追加。
200 行を超える補題はない。
検証済み累計は新規 Lean **42 ファイル・3,974 行・214 宣言（private 3 を含む）**。
§16.2・§17.1 で下書きとしていたファイルも今回検証済みとなり、未検証の Lean 下書きはない。
全て既存構成の等式輸送・係数作用・恒等・成分評価・自然性・射影構成の証明の分割で、
一次 ID は追加していない。

M10 の全弱自然変換の指定成分への接続はできた。
半自由 native fiber の同定、一般の底の辺の lift・transport と全族の cocartesian 性、
同じ U・単位・随伴を持つ `moduleFamily` の組み立ては引き続き必要。
M11 以降の相対テンソル・RHom・完備反射・完備テンソルと G12 も未完。
M10 を完了とは数えず、元の全目標を維持して続ける。

**一覧：済み 9／全体 42（うち追加 0）**。

## 18. M10 の固定底の通常加群から指定半自由模型への源（11-14、着手）

前の goal ターンは、全弱自然変換の指定成分までの kernel 照合を通し、
`621a7b739`・`f9da36f0d` に検証済みの実装と監査をコミットした進捗。
今回は通常の閉零加群圏の DK 局所化と、半自由加群の dg nerve の間の fiber 比較を進める。
既存の `DGModuleResolutionLocalization.dgModuleResolution_isLocalization` は、
全 dg 加群の **dg nerve** から半自由模型への局所化を与える。
元の通常の閉零圏の nerve からの普遍性とは源が異なり、同じ主張として流用しない。
BE の `CAlgLocalizationUniversal.cAlgLocalizationSource_isLocalization` は既にある。
いずれも他レーンのファイルは読んで import するだけで変更しない。

まず同じ通常の閉零加群の全 nerve を元の dg nerve へ送り、同じ指定半自由分解を適用する。
元の擬同型の反転と本質的全射性を照合し、次に制限に関する全関手間の比較へつなぐ。
Hom の ULift を戻す際には通常の `nerveMap` の同一 Hom 宇宙の制約を避け、
元の列の Hom を戻して同じ閉零 dg 単体にする。
これは M10/C02 の既存構成の源・係数移送・指定辺と分解比較の証明の分割で、一次 ID は追加しない。
通常 nerve からの局所化普遍性と、全圏の fiber の同定は引き続き必要。

`RawModuleDerivedSource.lean` の今回の型。文脈は `A : Type u`、`[CommRing A]`。

```lean
def strictRawModuleDGSource (X : (operad A).Algebra) :
    nerve (strictRawModuleRelativeCategory A X).category ⟶
      dgModuleNerve A (dgAlgebraCategory A ((assocForget A).obj X))

def strictRawModuleSource (X : (operad A).Algebra) :
    nerve (strictRawModuleRelativeCategory A X).category ⟶ strictModuleInfinity A X

lemma strictRawModuleDGSource_vertex (X : (operad A).Algebra)
    (M : (strictRawModuleRelativeCategory A X).category) :
    (strictRawModuleDGSource A X).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ M) =
      Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A)
        ((ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X)).obj M))

lemma strictRawModuleDGSource_edge (X : (operad A).Algebra)
    {M N : (strictRawModuleRelativeCategory A X).category} (f : M ⟶ N) :
    (strictRawModuleDGSource A X).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) =
      (dgClosedEdge A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) f.down).edge

lemma strictRawModuleSource_vertex (X : (operad A).Algebra)
    (M : (strictRawModuleRelativeCategory A X).category) :
    (strictRawModuleSource A X).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ M) =
      (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))).app (Opposite.op ⦋0⦌)
        (Simplex.vertex (A := A) (ForgetEnrichment.to (Complex A)
          ((ULiftHom.down.{u,u+1,u+1} (C := strictRawModuleCategory A X)).obj M)))

lemma strictRawModuleSource_inverts (X : (operad A).Algebra) :
    InvertsEdges (strictRawModuleSource A X) (weakNerveEdges (strictRawModuleRelativeCategory A X))

lemma strictRawModuleSource_essentiallySurjective (X : (operad A).Algebra) :
    IsEssentiallySurjective (strictRawModuleSource A X)
```

文献は閉零 nerve の包含が HA Construction 1.3.1.9、
指定半自由分解への反転・本質的全射性は HA Proposition 1.3.5.13 の同じ dg 加群模型の成分。
同じ通常の源を局所化とする普遍性はこの属性では主張しない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 18.1 同じ通常の源と制限・台・単位の全比較の型

`RawModuleSourceRestriction.lean` の文脈は `A : Type u`、`[CommRing A]`。
全 dg 加群の分解の前後の制限を、元の擬同型保存と同じ入力前合成則で比較し、
元の通常の源の全単体自然性と貼り合わせる。
既存の `strictModuleResolvedUnderlyingIso` を同じ源で前合成し、正則加群の値も
同じ頂点の式で指定単位へ等置する。いずれも M10/C02 の元の構成の法則の分割。

```lean
lemma strictRawModuleDGSource_restrict {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    nerveMap (strictRawModuleRestrictRelative f).functor ≫ strictRawModuleDGSource A X =
      strictRawModuleDGSource A Y ≫
        N (dgModuleRestriction A (dgAlgebraCategory A ((assocForget A).obj X))
          (dgAlgebraCategory A ((assocForget A).obj Y)) (dgAlgebraMap A ((assocForget A).map f)).op)

def strictRawResolvedRestrictionIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso
      (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj Y)) ≫ strictModuleRestrict f)
      (N (dgModuleRestriction A (dgAlgebraCategory A ((assocForget A).obj X))
        (dgAlgebraCategory A ((assocForget A).obj Y)) (dgAlgebraMap A ((assocForget A).map f)).op) ≫
        moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)))

def strictRawModuleSource_restrictIso {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    FunctorIso
      (nerveMap (strictRawModuleRestrictRelative f).functor ≫ strictRawModuleSource A X)
      (strictRawModuleSource A Y ≫ strictModuleRestrict f)

def strictRawModuleSource_underlyingIso (X : (operad A).Algebra) :
    FunctorIso (strictRawModuleSource A X ≫ strictModuleUnderlying A X)
      (strictRawModuleDGSource A X ≫
        N (moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj X))
          (Opposite.op DGAlgebraPoint.star)) ≫
        dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
          (DiagramComparison.semifreePointEquivalence A).hom)

lemma strictRawModuleSource_regular (X : (operad A).Algebra) :
    (strictRawModuleSource A X).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ ((ULiftHom.up.{u,u+1,u+1}
        (C := strictRawModuleCategory A X)).obj (strictRawRegularObject A X).fiber)) =
      strictModuleUnit A X
```

上の自然性は全ての厳密 BE 代数射 `f` に対する、同じ実関手間の主張。
一般の native CAlg の辺上の transport の構成や fiber 比較の普遍性は、これから必要。
他レーンのファイルや `EInfinity/Interface/` は変更していない。

**一覧：済み 9／全体 42（うち追加 0）**。

## 19. M10/C02 の次の経路：通常 dg 加群の projective モデル構造（N01、追加案）

### 19.1 現在の入力と差

§18 の源は通常の閉零加群の全 nerve から指定半自由模型へ送るが、反転と
本質的全射性だけでは局所化普遍性にはならない。
`DGModuleResolutionLocalization.dgModuleResolution_isLocalization` の源は dg nerve。
通常 nerve と dg nerve の間の比較を、同じ定理の代入だけで埋めることはできない。
リポジトリの `ModelCategory` を持つ定義と `RightModule`・`ModuleCategory` 等が共存する
ファイルを調べたが、現在の `strictRawModuleCategory A X` のモデル構造は見つからなかった。
これは不在の形式的証明ではなく、この経路の既存入力を探した結果。

採る経路の案は、同じ通常加群圏に projective モデル構造を実際に構成し、
既存の `SimplicialLocalization/ModelBifibrantLocalization`・`ModelHammockLocalization` の
全圏・bifibrant 比較と全標的の局所化普遍性を再利用するもの。
元の弱同値類と半自由模型を同じものに照合する。
新しい `[ModelCategory SSet]` や未証明の加群モデル構造を入力に加える案ではない。

### 19.2 N01 の型と仕様（未実装・採否の確認用）

新しい一次項目の追加案 **N01** は、同じ BE 固定底の通常加群圏のモデル構造を返す構成。
文脈は `A : Type u`、`[CommRing A]`、`X : (operad A).Algebra`。

```lean
def strictRawModuleModelCategory (X : (operad A).Algebra) :
    HomotopicalAlgebra.ModelCategory (strictRawModuleCategory A X)

lemma strictRawModuleModelCategory_weakEquivalences (X : (operad A).Algebra) :
    @HomotopicalAlgebra.weakEquivalences (strictRawModuleCategory A X) _
      (strictRawModuleModelCategory A X).categoryWithWeakEquivalences =
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))

lemma strictRawModuleModelCategory_fibrations (X : (operad A).Algebra) :
    @HomotopicalAlgebra.fibrations (strictRawModuleCategory A X) _
      (strictRawModuleModelCategory A X).categoryWithFibrations =
    (projectiveFibrations A).inverseImage (strictRawModuleUnderlying X)

lemma strictRawModuleModelCategory_allFibrant (X : (operad A).Algebra)
    (M : strictRawModuleCategory A X) :
    letI := strictRawModuleModelCategory A X
    HomotopicalAlgebra.IsFibrant M

lemma strictRawModuleModelCategory_semifreeCofibrant (X : (operad A).Algebra)
    (P : SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X))) :
    letI := strictRawModuleModelCategory A X
    HomotopicalAlgebra.IsCofibrant (ForgetEnrichment.of (Complex A) P.val)
```

モデル構造の弱同値・fibration・元の半自由対象の条件までを仕様に含める。
大域 instance にはせず、必要な比較で局所的に選ぶ。
X の carrier の平坦性・cofibrancy は追加仮定にしない。
この仕様は型の案で、Lean での検証済み宣言ではない。

その後の M10/C02 内の比較の目標は、既存の型のまま次を閉じること。

```lean
lemma strictRawModuleSource_isLocalization (X : (operad A).Algebra) :
    IsLocalization (strictRawModuleSource A X)
      (weakNerveEdges (strictRawModuleRelativeCategory A X))
```

N01 の存在だけでこの局所化や全族の fiber 同定が従うとは数えない。
実 frame Hom と同じ dg Hom の比較、指定源の同じ全関手比較を実装し、
その後に全族の fiber と一般の底の辺の lift・transport を証明する。

### 19.3 再利用・見込み・文献

既存の `moduleEvaluation`・`freeEvaluationAdjunction`（`Module/TensorFree.lean`）、
`Module/ActionLimits.lean` の加群の極限・余極限、
`Module/ShiftResolution.lean` の実半自由 filtration と解像度、
`ProjectiveModel` と `ModelGeneration.rightTransfer` を再利用する。
新たに必要になるのは、同じ自由加群で移した生成 I/J の小対象性、
自由な J-cell の擬同型性、モデル構造の選択とクラスの照合、半自由対象の cofibrancy。

N01 単体の暫定見込みは **1,000〜2,200 行**。
小対象性・自由な J-cell の部分を実測して再評価する。M10 の比較の残りや
M11 以降をこの見込みに入れて完成見込みとすることはしない。
M15 の外枠 **17,000 行は据え置く**。N01 の採否が決まるまで実装は始めない。

文献は [Keller, On differential graded categories, Theorem 3.2 (1)](https://webusers.imj-prg.fr/~bernhard.keller/publ/dgcat.pdf) の projective 構造。
HA Proposition 4.3.3.15 も W/F の転送を述べるが、一般のモノイダル模型では
作用する代数の cofibrancy を仮定する。その仮定を今回の任意 X へ黙って追加しない。
[HA 原典 §4.3.3](https://www.math.ias.edu/~lurie/papers/HA.pdf) を確認した。

### 19.4 止める規則との関係

`lane-goals-2026-11-14.md` 共通規則の
「**止まって報告するのは、新しい構成・新しい定理（既存の構成の法則でないもの）**」
に照らし、通常加群圏の ModelCategory を返す構成は、元の M01〜M42 に型のない
新しい構成と判断した。この判断は当レーンの解釈であり、M10/C02 の単なる証明分割
として追加承認を不要とする指示があればそれに従う。
N01 を採用する場合だけ一次 ID の追加として数える案で、現在の一覧にはまだ追加しない。
§18 の承認範囲内の実装・検証は完了まで進める。
その後は N01 の採否を確認し、待つ間は指示どおり drafts/A5 の受け渡しを紙で照合する。

**一覧：済み 9／全体 42（うち追加 0）**。


### 19.5 N01 の追加承認と着手（11-14、調整役）

N01 は調整役の返答で追加承認された。§19.2 の仕様のまま、モデル構造を実際に
構成し、元の擬同型・次数別全射・半自由対象の cofibrancy と照合する。
ModelCategory を引数の instance として仮定しない。外枠は 17,000 行のまま。
先に既存の `HomotopicalAlgebra/Diagram/Projective.modelCategory` と
`BarrattEccles.Diagram.projectiveModelCategory`、一般の転送の構成を確認する。
N01 は未完で、一次一覧は M01〜M42 と N01 の計 43 項目となった。

**一覧：済み 9／全体 43（うち追加 1）**。


## 20. §18 の検証完了と N01 の既存部品の確認（11-14）

§18 の `RawModuleDerivedSource`（168 行・7 宣言）と
`RawModuleSourceRestriction`（137 行・5 宣言）の二つの通常対象ビルドは成功。
新規公開 12 宣言の小さい依存公理監査は、12 件の実出力を宣言名と機械照合して成功した。
依存公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内。
12 宣言の HA 文献属性も、各一件・component・指定番号を環境から照合して成功。
共有 impl 鍵、各組 280 秒上限。200 行を超える補題はない。
検証済み累計は **44 ファイル・4,279 行・226 宣言（private 3 を含む）**。
通常 nerve からの局所化普遍性や M10 全体の完成とは数えない。

§18 の型の転記に、名前付き引数の `:=` を宣言本体の区切りと誤認して途中で
切れた箇所があった。括弧の深さを追って区切る方法に直し、同節の全 12 型を
実ソースから完全な形で転記し直した。

N01 について、指定された既存の二つの構成を先に読んだ。
`HomotopicalAlgebra/Diagram/Projective.modelCategory` は通常の `K ⥤ C` を対象とし、
基礎モデルと locally presentable 性を入力に持つ。
`BarrattEccles.Diagram.projectiveModelCategory` は `K ⥤ (operad A).Algebra` を対象とし、
実自由評価族と証明済みの cell 非輪状性を一般転送に渡している。
今回の元の dg 加群圏はそのいずれの通常関手圏でもないので、直接の代入にはしない。
代わりに同じ設計の既存 `ModelGeneration.rightTransfer` を再利用する。
`EInfinity/DGAlgebra/ModelCategory` と `SmallObject` の使い方も確認した。

さらに既存 `DGModuleDiskCoverAcyclic` に、任意 dg 底の実 disk 被覆の非輪状性と、
非輪状直和項からの射影の擬同型性がある。自由 disk 被覆の全次数全射性も既存。
これらをそのまま import し、全射の左類の射 f を
`M → M ⊕ diskCover(N)` の retract として非輪状性を証明する経路にした。
新しい path object や底 X の cofibrancy 仮定を必要としない。
自由 I/J の実小対象性とこの非輪状性の実装は、次の対象ビルドで検証中。
他レーンの既存ファイルは変更していない。

N01 は着手したが未完。追加した一次 ID は N01 一件だけ。

**一覧：済み 9／全体 43（うち追加 1）**。


## 21. N01 の実構成・照合の型（11-14）

共通の文脈は `A : Type u`、`[CommRing A]`。一般の二ファイルではさらに
`D : Type v`、`[DGCategory A D]`、`[Small.{u} D]` を使う。
以下は承認済み N01 の実装とその生成射・自然性・貼り合わせ・持ち上げの証明分割。
検証結果と最終の実測は本節末尾に記録する。

### RawModuleGenerators

```lean
abbrev strictRawModuleFree (X : (operad A).Algebra) :
    Complex A ⥤ strictRawModuleCategory A X

def strictRawModuleFreeAdjunction (X : (operad A).Algebra) :
    strictRawModuleFree A X ⊣ strictRawModuleUnderlying X

def strictRawModuleGeneratingCofibrations (X : (operad A).Algebra) :
    MorphismProperty (strictRawModuleCategory A X)

def strictRawModuleGeneratingTrivialCofibrations (X : (operad A).Algebra) :
    MorphismProperty (strictRawModuleCategory A X)

lemma strictRawModuleQuasiIso_eq (X : (operad A).Algebra) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) =
      (quasiIso (ModuleCat A) (.up ℤ)).inverseImage (strictRawModuleUnderlying X)

lemma strictRawModuleGeneratingCofibrations_rlp (X : (operad A).Algebra) :
    (strictRawModuleGeneratingCofibrations A X).rlp =
      ((projectiveFibrations A) ⊓ quasiIso (ModuleCat A) (.up ℤ)).inverseImage
        (strictRawModuleUnderlying X)

lemma strictRawModuleGeneratingTrivialCofibrations_rlp (X : (operad A).Algebra) :
    (strictRawModuleGeneratingTrivialCofibrations A X).rlp =
      (projectiveFibrations A).inverseImage (strictRawModuleUnderlying X)

lemma strictRawModuleUnderlying_accessible (X : (operad A).Algebra)
    (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    (strictRawModuleUnderlying X).IsCardinalAccessible κ

lemma strictRawModuleFree_finitelyPresentable (X : (operad A).Algebra)
    (K : Complex A) [IsFinitelyPresentable.{u} K] :
    IsFinitelyPresentable.{u} ((strictRawModuleFree A X).obj K)

lemma strictRawModuleFreeFamily_smallObjectArgument (X : (operad A).Algebra)
    {ι : Type v} [Small.{u} ι] {K L : ι → Complex A}
    (f : ∀ i, K i ⟶ L i) [∀ i, IsFinitelyPresentable.{u} (K i)] :
    ((MorphismProperty.ofHoms f).strictMap (strictRawModuleFree A X)).HasSmallObjectArgument.{u}

lemma strictRawModuleGeneratingCofibrations_smallObjectArgument (X : (operad A).Algebra) :
    (strictRawModuleGeneratingCofibrations A X).HasSmallObjectArgument.{u}

lemma strictRawModuleGeneratingTrivialCofibrations_smallObjectArgument
    (X : (operad A).Algebra) :
    (strictRawModuleGeneratingTrivialCofibrations A X).HasSmallObjectArgument.{u}
```

### RawModuleAcyclicity

```lean
lemma strictRawModuleBiprodInl_quasiIso (X : (operad A).Algebra)
    (M K : strictRawModuleCategory A X)
    (hK : moduleAcyclic A (dgAlgebraCategory A ((assocForget A).obj X)) K) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      (moduleBiprodInl A _ M K)

lemma strictRawModuleFibrations_llp_quasiIso (X : (operad A).Algebra)
    {M N : strictRawModuleCategory A X} (f : M ⟶ N)
    (hf : ((projectiveFibrations A).inverseImage (strictRawModuleUnderlying X)).llp f) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) f

lemma strictRawModuleFreeCells_acyclic (X : (operad A).Algebra) :
    MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u}
        (strictRawModuleGeneratingTrivialCofibrations A X)).pushouts ≤
      moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
```

### RawModuleModel

```lean
lemma strictRawModule_hasFiniteLimits (X : (operad A).Algebra) :
    HasFiniteLimits (strictRawModuleCategory A X)

lemma strictRawModule_hasFiniteColimits (X : (operad A).Algebra) :
    HasFiniteColimits (strictRawModuleCategory A X)

def strictRawModuleModelCategory (X : (operad A).Algebra) :
    ModelCategory (strictRawModuleCategory A X)

lemma strictRawModuleModelCategory_weakEquivalences (X : (operad A).Algebra) :
    @weakEquivalences (strictRawModuleCategory A X) _
      (strictRawModuleModelCategory A X).categoryWithWeakEquivalences =
        moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))

lemma strictRawModuleModelCategory_fibrations (X : (operad A).Algebra) :
    @fibrations (strictRawModuleCategory A X) _
      (strictRawModuleModelCategory A X).categoryWithFibrations =
        (projectiveFibrations A).inverseImage (strictRawModuleUnderlying X)

lemma strictRawModuleModelCategory_cofibrantlyGenerated (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      (strictRawModuleGeneratingCofibrations A X)
      (strictRawModuleGeneratingTrivialCofibrations A X)

lemma strictRawModuleModelCategory_allFibrant (X : (operad A).Algebra)
    (M : strictRawModuleCategory A X) :
    let := strictRawModuleModelCategory A X
    IsFibrant M
```

### RawModuleCofibrancy

```lean
lemma strictRawModuleSemifree_strict_lift (X : (operad A).Algebra)
    {P M N : strictRawModuleCategory A X}
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P)
    (p : M ⟶ N) (hs : (projectiveFibrations A) ((strictRawModuleUnderlying X).map p))
    (hq : moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) p) (g : P ⟶ N) :
    ∃ l : P ⟶ M, l ≫ p = g

lemma strictRawModuleModelCategory_semifreeCofibrant (X : (operad A).Algebra)
    (P : SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X))) :
    let := strictRawModuleModelCategory A X
    IsCofibrant (ForgetEnrichment.of (Complex A) P.val)
```

### SemifreeGradedLifting

```lean
lemma moduleHom_post_pre_component {M N T U : ModuleCategory A D}
    (i : M ⟶ N) (p : T ⟶ U) (q : ℤ)
    (z : (N ⟶[Complex A] T).X q) :
    (eHomWhiskerRight (Complex A) i U).f q
      ((eHomWhiskerLeft (Complex A) N p).f q z) =
    (eHomWhiskerLeft (Complex A) M p).f q
      ((eHomWhiskerRight (Complex A) i T).f q z)

lemma moduleGradedSplit_postcompose_lift {M N Q T U : ModuleCategory A D}
    {i : M ⟶ N} {g : N ⟶ Q} (s : ModuleGradedSplit A D i g)
    (p : T ⟶ U) (q : ℤ)
    (hQ : Function.Surjective ((eHomWhiskerLeft (Complex A) Q p).f q))
    (a : (M ⟶[Complex A] T).X q)
    (z : (N ⟶[Complex A] U).X q)
    (h : (eHomWhiskerLeft (Complex A) M p).f q a =
      (eHomWhiskerRight (Complex A) i U).f q z) :
    ∃ b : (N ⟶[Complex A] T).X q,
      (eHomWhiskerLeft (Complex A) N p).f q b = z ∧
      (eHomWhiskerRight (Complex A) i T).f q b = a
```

### SemifreeGradedProjectivity

```lean
lemma moduleHom_postcompose_surjective_of_iso {M N T U : ModuleCategory A D}
    (e : M ≅ N) (p : T ⟶ U) (q : ℤ)
    (hN : Function.Surjective ((eHomWhiskerLeft (Complex A) N p).f q)) :
    Function.Surjective ((eHomWhiskerLeft (Complex A) M p).f q)

lemma moduleSphereFreePresentation_postcompose_surjective {M T U : ModuleCategory A D}
    (S : ModuleSphereFreePresentation A D M) (p : T ⟶ U)
    (hp : moduleDegreewiseSurjective A D p) (q : ℤ) :
    Function.Surjective ((eHomWhiskerLeft (Complex A) M p).f q)

lemma moduleSemifreeFiltration_postcompose_surjective {M T U : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) (p : T ⟶ U)
    (hp : moduleDegreewiseSurjective A D p) (q : ℤ) :
    Function.Surjective ((eHomWhiskerLeft (Complex A) M p).f q)
```


## 22. M10/C02 の次の接続：同じ実モデルへの frame の代入（11-14）

N01 の次には、既存の一般の関手的分解・Reedy frame・全モデル圏の hammock 普遍性を
同じ実加群モデルへ代入する。これらの一般の構成を作り直さず、ModelCategory や分解の
存在を引数の仮定として残さない。次の五つは既存構成の特殊化・証明の分割で、一次 ID は
追加しない。対象ビルドと監査の結果は本節の末尾へ追記する。

`RawModuleFrameInput.lean`。文脈は `A : Type u`、`[CommRing A]`。

```lean
def strictRawModuleCofibrantFactorization (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    MorphismProperty.FunctorialFactorizationData (cofibrations (strictRawModuleCategory A X))
      (trivialFibrations (strictRawModuleCategory A X))

def strictRawModuleFibrantFactorization (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    MorphismProperty.FunctorialFactorizationData (trivialCofibrations (strictRawModuleCategory A X))
      (fibrations (strictRawModuleCategory A X))

def strictRawModuleSourceFrameFamily (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    CofibrantResolutionFamily (C := strictRawModuleCategory A X) simplex

def strictRawModuleRightFrameFamily (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    CofibrantResolutionFamily (C := (strictRawModuleCategory A X)ᵒᵖ) simplex

lemma strictRawModuleModelHammock_isLocalization (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    IsLocalization
      (hammockLocalizationNerveMap
        (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
          (strictRawModuleCategory A X)))
      (weakNerveEdges
        (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
          (strictRawModuleCategory A X)))
```

ここで既存 `modelRelativeCategory` は AsSmall 表示であり、§18 の源の ULiftHom 表示と
定義上同じとはしない。同じ元の圏・同じ擬同型を保つ宇宙表示の比較が必要。
さらに、この hammock の普遍性を得ても、§18 の通常源から半自由 dg nerve への
`strictRawModuleSource` が局所化であることは未完のまま。同じ frame Hom と実 dg Hom、
その全標的自然性と指定源の比較をつなぐ必要がある。
M10 の全族の一般の辺・fiber の同定も、ここで終わったとは数えない。

**一覧：済み 9／全体 43（うち追加 1）**。


### 22.1 同じ通常圏の二つの宇宙表示の型

`RawModuleRelativeModel.lean` は、既存の ULiftHom・AsSmall の圏同値を合成し、
N01 の W の等式で両方向の相対関手を作る。元の通常圏の表示・弱同値検出の法則であり、
一次 ID は追加しない。これだけで半自由 dg nerve への比較を済ませたとはしない。

```lean
def strictRawModuleUniverseEquivalence (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    (strictRawModuleRelativeCategory A X).category ≌
      (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)).category

def strictRawModuleToModelRelative (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    strictRawModuleRelativeCategory A X ⟶
      SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)

def strictRawModuleFromModelRelative (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
      (strictRawModuleCategory A X) ⟶ strictRawModuleRelativeCategory A X
```


### 22.2 元の通常加群 DK 源の全標的普遍性の型

同じ宇宙表示の単位・余単位は同型であり、元の弱射でもある。
これらを既存の `isLocalization_of_weakDeformation` と同じ hammock nerve の標的比較へ
渡す実装を準備した。以下は元の通常圏の自由 DK 局所化の法則の証明分割で、一次 ID は
追加しない。半自由標的への `strictRawModuleSource` の普遍性とは別の主張である。

`RawModuleLocalizationUniversal.lean`、同じ `A : Type u`、`[CommRing A]`。

```lean
lemma strictRawModuleUniverseUnit_weak (X : (operad A).Algebra)
    (M : (strictRawModuleRelativeCategory A X).category) :
    (strictRawModuleRelativeCategory A X).weakEquivalences
      ((strictRawModuleUniverseEquivalence A X).unitIso.inv.app M)

lemma strictRawModuleUniverseCounit_weak (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    ∀ M : (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)).category,
      (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (strictRawModuleCategory A X)).weakEquivalences
          ((strictRawModuleUniverseEquivalence A X).counitIso.hom.app M)

lemma strictRawModuleHammockUniverse_isQCatEquivalence (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    IsQCatEquivalence (relativeKanHammockNerve (strictRawModuleToModelRelative A X))

lemma strictRawModuleHammock_isLocalization (X : (operad A).Algebra) :
    IsLocalization (hammockLocalizationNerveMap (strictRawModuleRelativeCategory A X))
      (weakNerveEdges (strictRawModuleRelativeCategory A X))

lemma strictRawModuleLocalization_isLocalization (X : (operad A).Algebra) :
    IsLocalization (localizationNerveSourceMap (strictRawModuleRelativeCategory A X))
      (weakNerveEdges (strictRawModuleRelativeCategory A X))
```

本小節の実装は、前の対象ビルドが共有鍵を待っている間に準備したもの。
対象ビルド・小さい監査に通るまでは検証済みと数えない。

**一覧：済み 9／全体 43（うち追加 1）**。



### 22.3 実 dg Hom との接続で再利用できる部品（紙、未実装）

通常源と dg nerve の比較で使う点ごとの Hom 加群も、作用から作り直す必要はない。
`DifferentialGraded/Module/Basic.leftRepresentable` は共変 Hom の実 dg 関手である。
そのため `D : Type v`、`[DGCategory A D]`、`K : Complex A`、
`M : RightModule A D` に対して、次の既存の合成は型として同じ右加群を返す。

```lean
M.comp (leftRepresentable A K) : RightModule A D
```

点での値は `homComplex A K (M.obj x)`。高次の作用の符号は既存の
`leftRepresentable_action` に保持されている。
標準単体の複体を K に入れる候補では、既存の
`AlexanderWhitney.simplexCochainComonFunctor` の台を再利用できる。
`KST/LocalizingInvariants/DGAlgebraMultiplicativeSimplices` も同じ単体複体に対する
内部 Hom の族を使っていることを読んだが、代数の乗法の構成を加群へコピーしない。

この式だけでは、全単体を持つ選んだ right frame との比較、Reedy fibrancy、
指定 coaugmentation の弱同値性、元の dg Hom との全標的自然性はまだ証明していない。
N01 の実モデルを得た後に、既存の tensor/Hom の随伴・標準単体の分裂と照合する。
本小節は再利用候補の紙の記録であり、検証済み Lean の追加ではない。


## 23. A5 への受け渡しの補足：§18 と N01 の到達点から（11-14、紙）

対象ビルドの共有鍵を待つ間に、`drafts/Shared/Descendable` と
`drafts/A5/StrongDescent` を再読した。drafts は変更していない。
§11 の完備反射・完備テンソル・Koszul の受け渡しに加え、今回の実装からの差を記録する。

`StrongDescent.deltaRootEdge` は `polynomialRootArrow` の nerve の辺を
`discreteDeltaFunctor` で送った辺である。通常圏の一辺を入力にしているが、型から得られる
出力は native CAlg の辺であり、厳密 BE 代数射そのものは返さない。
§18 の制限比較は厳密 BE 代数射に対する同じ全関手比較なので、この辺を代入するには
M10 の全族の transport との接続が要る。BE 特殊化の方針を維持し、任意 E の輸送を作らない。

§18 の `strictRawModuleSource_regular` と `strictRawModuleSource_underlyingIso` は、
固定した厳密 BE 底について、同じ通常の源の正則加群を指定単位へ送り、同じ台の評価と
全関手間で比較する法則である。これにより、N01 の通常モデルから出る入力の U・単位を
照合する入口ができた。A5 の一般の `deltaRootEdge` の台・単位・fiber の coherence と、
完備反射の単位・余単位は引き続き M10 および M36–M37 の実出力を使う。

N01 の `strictRawModuleModelCategory_allFibrant` は、通常 dg 加群の projective モデルの
終対象への射が次数ごとに全射、という fibrancy である。
A5 で必要な `Derived.IsDerivedComplete A s` は完備反射の固定点の条件なので、
前者から後者を得たことにはしない。実際、N01 の fibrancy の結論は全通常加群に対するもの。
`Shared/Descendable.isDescendable_complete` の入力 `hB` と、
`StrongDescent.rhom_baseChange_koszul_connection` の導来完備性の証明は、各々の型のまま残る。

N01 の半自由 cofibrancy の照合は、元の `SemifreeDGModules` の対象を別の置換へ変えない。
ただし、A5 の個別の Koszul 対象・fiber やその二乗が半自由・双対可能であることを、
この照合の名前だけで供給したとはしない。M15 が返す一般の相対テンソル・RHom・完備版の
法則を受け取り、A5 が個別の Koszul・Nakayama の証明を閉じる、という分担を維持する。

本節は利用側の型の照合だけで、一次 ID の追加はない。
N01 の最終対象ビルドと監査は待機中であり、完了数はまだ更新しない。

**一覧：済み 9／全体 43（うち追加 1）**。


## 24. N01 の完成・検証・実測（11-14）

承認された N01 は、§19.2 の仕様のまま完成した。
`strictRawModuleModelCategory` の引数は基礎可換環 A と厳密 BE 底 X であり、
ModelCategory の存在を引数の instance として仮定しない。
元の `moduleQuasiIso` と台の全整数次数全射に W/F を同定し、全対象の fibrancy と
同じ `SemifreeDGModules` の対象の cofibrancy を、実構成したモデルで証明した。
底 X の平坦性・cofibrancy や SSet のモデル構造の仮定は追加していない。

先に指定された既存部品を確認した記録は §20。
実装は構成済みの複体の `projectiveModelCategory`、元の自由評価随伴、
評価ごとの実極限・余極限、`ModelGeneration.rightTransfer` を使用した。
転送の非輪状性には既存の実自由 disk 被覆と直和射影の擬同型性を使い、
半自由 cofibrancy には既存の全作用付き filtration・全 Hom の極限と擬同型性を使った。

| 新規ファイル | 行数 | 公開宣言 |
|---|---:|---:|
| BE `Modules/RawModuleGenerators` | 176 | 12 |
| BE `Modules/RawModuleAcyclicity` | 117 | 3 |
| BE `Modules/RawModuleModel` | 129 | 7 |
| BE `Modules/RawModuleCofibrancy` | 89 | 2 |
| `Modules/SemifreeGradedLifting` | 65 | 2 |
| `Modules/SemifreeGradedProjectivity` | 117 | 3 |
| 合計 | **693** | **29** |

200 行を超える補題はない。一次 ID は承認された N01 一件だけで、
残りは同じ構成の生成射・持ち上げ・表示の等式・貼り合わせの法則と証明の分割。
全 29 型を §21 に記載した。
当初の見込み 1,000〜2,200 行より短くなったのは、§20 の既存の実部品を再利用したため。
M15 の外枠 17,000 行は維持する。

最終の通常対象ビルド `RawModuleCofibrancy:olean` は終了コード 0。
その依存の生成射・非輪状性・実モデル・全次数の半自由持ち上げも通常対象として成功した。
新規公開 29 宣言の `#print axioms` の実出力を宣言名と機械照合し、監査は終了コード 0。
全て標準の `propext`・`Classical.choice`・`Quot.sound` の範囲内で、追加公理・sorryAx はない。
自由加群と自由評価随伴の既存 HA 文献番号に付けた二件の属性も、各一件、
HA 4.2.4.4 の component であることを環境から検査して成功した。
N01 の原典の projective モデルの番号は、宣言 docstring の Keller Theorem 3.2 (1)。
いずれも共有 impl 鍵、実行上限 280 秒の組で行った。

監査まで済んだ累計は、新規 Lean **50 ファイル・4,972 行・255 宣言（private 3 を含む）**。
M10 の続きの `RawModuleFrameInput` と `RawModuleRelativeModel` の対象ビルドは通ったが、
`RawModuleLocalizationUniversal` に結果型の let の導入の修正が一箇所あり、修正後の対象ビルドと
13 宣言の監査を待つ。これら三ファイルは今回の N01 コミットに含めず、作業木に残す。
過去の報告の型転記で途中が切れていた四宣言も、§18 と同じ抽出の修正により完全な型へ補った。

N01 を完了に数える。M10 の同じ通常源と半自由 native 模型の全比較、全族の一般の辺と fiber、
M11 以降の相対テンソル・RHom・完備反射・完備テンソル、G12 は引き続き進める。

**一覧：済み 10／全体 43（うち追加 1）**。


## 25. M10/C02：元の通常加群 DK 源の普遍性まで検証（11-14）

§22 の三つのファイルの通常対象ビルドと小さい監査が完了した。
`RawModuleFrameInput` 88 行・5 宣言、`RawModuleRelativeModel` 69 行・3 宣言、
`RawModuleLocalizationUniversal` 118 行・5 宣言、計 **275 行・13 公開宣言**。
修正は結果型のモデル選択 let の導入と、BE 代数の同名判定に隠れた
`HomotopicalAlgebra.weakEquivalence_iff` の完全名指定であり、仕様を変えていない。

最終の対象 `RawModuleLocalizationUniversal:olean` は終了コード 0。
13 宣言の `#print axioms` は宣言名と実出力を機械照合し、監査は終了コード 0。
全て `propext`・`Classical.choice`・`Quot.sound` の範囲内で、追加公理・sorryAx はない。
共有 impl 鍵、実行上限 280 秒の組で行った。200 行を超える補題はない。

同じ通常加群圏の ULiftHom と AsSmall の相対比較を通じ、元の自由 DK 源
`localizationNerveSourceMap (strictRawModuleRelativeCategory A X)` が、元の擬同型を反転する
全 quasicategory 標的への局所化であることを得た。
これにより、同じ通常源から指定半自由模型への §18 の関手を全関手のまま降下できる。
その降下と指定三角比較を次に作り、完全忠実性と同じ全族の fiber の同定へ接続する。
反転・本質的全射性だけで同値・普遍性と数えることはしない。

監査まで済んだ累計は、新規 Lean **53 ファイル・5,247 行・268 宣言（private 3 を含む）**。
いずれも同じ実モデル・同じ相対局所化の比較・源移送の法則と証明分割で、一次 ID は追加しない。
M10 はまだ未完。一次一覧の完了数は M01–M09 と N01 の計 10 のまま。

**一覧：済み 10／全体 43（うち追加 1）**。



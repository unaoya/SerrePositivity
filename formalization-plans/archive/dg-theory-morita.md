# 導来Morita：このチャットのU16a・U16c統合

> **アーカイブ（2026-10-18）**：M5（dg 理論）は 2026-10-17 に完了（中心作用・群作用は M9 へ）。現状と再開点は [M5 の完了状況](../dg-theory-m5-status.md)。将来は削除する予定で、以下は当時の計画と実施記録のまま。


## U16a 公開 API（2026-10-17固定）

名前空間は `SerrePositivity.DifferentialGraded.Morita`。
以下は他担当が依存してよい名前・正確な型・仮定の契約であり、実装状態を分けて記す。
**本節の公開APIはすべて実装・検証済み。U16aはdg-theory.md §17.273の範囲で受入済み。**
未証明のLean宣言・sorry・axiomは作らない。既存公開型を変更する必要があれば変更前に本節へ旧新型と移行方法を書く。

共通の変数は次の通り。`D`・`E`・`F`の対象宇宙は独立である。
型仕様はこの変数文脈で右辺を省略した宣言として記す。共通引数の順はA・D・E・F。

```lean
universe u v w z
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
```

### 1. kernelの型・向き・恒等・合成（KernelBasic.lean）

D→Eのkernelは**右E・左D**。`functorGraph A D E f`と同じ向きであり、
この順序は将来のQuasiEquivalence*・Perfect*側でも保持する。

```lean
abbrev Kernel := DerivedBimoduleCategory A E D
def kernelIdentity : Kernel A D D
def kernelGraph (f : DGFunctor A D E) : Kernel A D E
def kernelCompose (hD : localHomKFlat A D)
  (P : Kernel A D E) (Q : Kernel A E F) : Kernel A D F
def kernelComposeMap (hD : localHomKFlat A D)
  {P P' : Kernel A D E} {Q Q' : Kernel A E F} (f : P ⟶ P') (g : Q ⟶ Q') :
  kernelCompose A D E F hD P Q ⟶ kernelCompose A D E F hD P' Q'
```

共通引数は各型に現れるものだけを抽出する。Kernel自体とkernelGraphはDのSmallを要求せず、
EのSmallだけを保持する（KernelChecksの#check出力で確認）。他の通常作用・合成は両側のSmallを保持する。
Kernelの実体は既存の主bimodule局所化。identityは対角の局所化像。
`kernelCompose A D E F hD P Q`は
`((derivedBimoduleComposeFunctor A F E D hD).obj P).obj Q`。
この合成に必要な局所Hom条件はDだけ。E・Fには追加しない。

### 2. 通常作用（KernelTensor.lean）

```lean
def kernelTensor (P : Bimodule A E D) :
  DGFunctor A (RightModule A D) (RightModule A E)
lemma kernelTensor_value (P : Bimodule A E D)
  (M : RightModule A D) (e : E) :
  ((kernelTensor A D E P).obj M).obj (Opposite.op e) =
    BalancedTensor.obj A D M (P.leftAt e)
lemma kernelTensor_graph (f : DGFunctor A D E) :
  kernelTensor A D E (functorGraph A D E f) = dgModuleExtension A D E f
```

通常作用にlocalHomKFlatは不要。準同型保存は任意入力について主張せず、入力の射影解像度を使う。

### 3. 主導来作用（実装・検証済み、U16a3）

```lean
def kernelDerivedTensorFunctor :
  Kernel A D E ⥤ (DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
def kernelDerivedTensor (P : Kernel A D E) :
  DerivedModuleCategory A D ⥤ DerivedModuleCategory A E
def kernelDerivedTensorComputation (P : Bimodule A E D)
  (M : ModuleCategory A D) (R : ModuleProjectiveResolution A D M) :
  (kernelDerivedTensor A D E
      ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).obj
      ((moduleToDerived A D).obj M) ≅
    (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj R.obj)
```

`kernelDerivedTensor A D E P`は`(kernelDerivedTensorFunctor A D E).obj P`と定義する。
主導来作用そのものにはlocalHomKFlatを課さない。右D入力のsemifree射影解像度は
DのHomのA-flat性なしで相対K-flatであり、kernelの準同型に関する不変性をこのモデルで証明する方針。
任意指定射影解像度Rの計算を公開し、単なる対象上の計算で関手・自然性を代用しない。

### 4. 導来右随伴・unit/counit（実装・検証済み、U16a13）

```lean
def kernelDerivedHom (P : Kernel A D E) :
  DerivedModuleCategory A E ⥤ DerivedModuleCategory A D
def kernelDerivedAdjunction (P : Kernel A D E) :
  kernelDerivedTensor A D E P ⊣ kernelDerivedHom A D E P
def kernelDerivedUnit (P : Kernel A D E) :
  𝟭 (DerivedModuleCategory A D) ⟶
    kernelDerivedTensor A D E P ⋙ kernelDerivedHom A D E P
def kernelDerivedCounit (P : Kernel A D E) :
  kernelDerivedHom A D E P ⋙ kernelDerivedTensor A D E P ⟶
    𝟭 (DerivedModuleCategory A E)
lemma kernelDerived_left_triangle (P : Kernel A D E)
  (X : DerivedModuleCategory A D) :
  (kernelDerivedTensor A D E P).map ((kernelDerivedUnit A D E P).app X) ≫
    (kernelDerivedCounit A D E P).app ((kernelDerivedTensor A D E P).obj X) = 𝟙 _
lemma kernelDerived_right_triangle (P : Kernel A D E)
  (Y : DerivedModuleCategory A E) :
  (kernelDerivedUnit A D E P).app ((kernelDerivedHom A D E P).obj Y) ≫
    (kernelDerivedHom A D E P).map ((kernelDerivedCounit A D E P).app Y) = 𝟙 _
```

unit/counitは上の実際の随伴の成分。随伴の存在・成分の可逆性を入力仮定として受け取らない。
Morita/AdjunctionDerived.leanをimportすれば、上記6宣言を任意kernelについて利用できる。
公開名・引数・仮定・宇宙は従来の型と同じで、局所Hom K-flat性・kernel列の射影性は不要。
通常Homのdg関手はAdjunctionHom.lean、実際の導来右随伴はtelescopeによる全入力のHom表現から構成した。
kernelDerivedHomEquivは全入力のHom同値、kernelDerivedHomEquiv_naturalityは始域の全導来射自然性。
kernelDerivedHom_objで右随伴の値をtelescopeへ、kernelDerivedCounit_modelで余単位をその標的射へ計算する。
左右三角恒等式に加え、右随伴関手・unit/counitの自然性は実際のMathlib Adjunctionのものを使える。
両単位・結合の作用coherenceもU16a20で検証し、一般随伴と同時に受け入れた。

### 5. 恒等作用（実装・検証済み、U16a4）・合成比較（実装・検証済み、U16a6）

```lean
def kernelIdentityIso :
  kernelDerivedTensor A D D (kernelIdentity A D) ≅ 𝟭 (DerivedModuleCategory A D)
def kernelCompositionIso (hD : localHomKFlat A D)
  (P : Kernel A D E) (Q : Kernel A E F) :
  kernelDerivedTensor A D E P ⋙ kernelDerivedTensor A E F Q ≅
    kernelDerivedTensor A D F (kernelCompose A D E F hD P Q)
```

恒等比較にlocalHomKFlatは不要。合成比較はU12e-localの結合子と同じく始域Dだけに条件を置く。
合成比較は入力導来加群と両kernelの任意の主導来射に自然（U16a9）。
kernelComposeMapへの自然性はkernelCompositionIso_naturalityで利用できる。
右単位はU16a15、左単位と任意主導来kernelの結合coherenceはU16a20で実装・検証済み。

```lean
lemma kernelCompositionIso_naturality (hD : localHomKFlat A D)
  {P P' : Kernel A D E} {Q Q' : Kernel A E F} (f : P ⟶ P') (g : Q ⟶ Q') :
  NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f)
      ((kernelDerivedTensorFunctor A E F).map g) ≫
      (kernelCompositionIso A D E F hD P' Q').hom =
    (kernelCompositionIso A D E F hD P Q).hom ≫
      (kernelDerivedTensorFunctor A D F).map (kernelComposeMap A D E F hD f g)
lemma kernelCompositionIso_kFlat (hD : localHomKFlat A D)
  (P : RightKFlatBimoduleCategory A E D) (Q : BimoduleCategory A F E) :
  kernelCompositionIso A D E F hD ((bimoduleToDerived A E D).obj P.obj)
      ((bimoduleToDerived A F E).obj Q) = kernelCompositionKFlatIso A D E F hD P Q
```
三因子D→E→F→Gで必要なのは既存結合子に現れるD・EのlocalHomKFlat。
同じkernel・固定dg圏の契約とし、中断した一般分解変更のcoherenceを待たない。

### 6. 右単位coherence（実装・検証済み、U16a15）

Morita/CoherenceUnitMain.leanをimportする。名前空間は同じMorita。

```lean
lemma kernelCompositionIso_rightUnit (hD : localHomKFlat A D) (P : Kernel A D E) :
  (kernelCompositionIso A D D E hD (kernelIdentity A D) P).hom ≫
    (kernelDerivedTensorFunctor A D E).map ((derivedBimoduleRightUnitIso A E D hD).hom.app P) =
  Functor.whiskerRight (kernelIdentityIso A D).hom (kernelDerivedTensor A D E P) ≫
    (Functor.leftUnitor (kernelDerivedTensor A D E P)).hom
```

bimoduleの順序では右単位、作用の順序では恒等kernelを先に作用させる図式である。
右単位図式には終域Eの局所Hom条件やPのK-flat性は要求しない。

### 7. kernel結合子と指定モデル計算（実装・検証済み、U16a17）

Morita/CoherenceAssociatorModels.leanをimportする。名前空間はMorita。
既存U12e-localの結合子を作用順に読む入口。任意主導来kernelの作用coherenceも以下の定理で検証済み。

```lean
def kernelAssociatorIso (hD : localHomKFlat A D) (hE : localHomKFlat A E)
  (P : Kernel A D E) (Q : Kernel A E F) (R : Kernel A F G) :
  kernelCompose A D E G hD P (kernelCompose A E F G hE Q R) ≅
    kernelCompose A D F G hD (kernelCompose A D E F hD P Q) R
```

共通変数にG : Type t、[DGCategory A G]・[Small.{u} G]を追加する。
既存bimodule結合子の((R⊗Q)⊗P) → R⊗(Q⊗P)の向き。
kernelAssociatorPairModelIso・kernelAssociatorNestedModelIsoは、最初の二kernelを右相対K-flatに選んだ
二モデルの計算同型。kernelAssociatorIso_model_facと_action_model_facは通常結合子との可換square。
KernelComparisonComponentsのkernelDerivedTensorOnBimoduleIso_refl・kernelDerivedTensorFunctor_map_base、
kernelCompositionIso_kFlat_facは同じ通常代表での作用比較を簡約する入口。
既存公開型・比較の定義は変更していない。
CoherenceAssociatorPathsのkernelAssociatorLeftPath・kernelAssociatorRightPathは全kernel上の公開二経路。
kernelCompositionIso_associator_modelは指定右K-flat二因子・任意通常後因子での二経路の等式として検証済み。
CoherenceAssociatorMainのkernelCompositionIso_associatorは、代表の条件を除いて任意の主導来kernelで
kernelAssociatorLeftPath A D E F G hD P Q R = kernelAssociatorRightPath A D E F G hD hE P Q R
を証明する。D・E以外の局所Hom条件は追加しない。

### 8. 左単位coherence（実装・検証済み、U16a20）

Morita/CoherenceLeftUnitMain.leanをimportする。

```lean
lemma kernelCompositionIso_leftUnit (hD : localHomKFlat A D) (hE : localHomKFlat A E)
  (P : Kernel A D E) :
  (kernelCompositionIso A D E E hD P (kernelIdentity A E)).hom ≫
    (kernelDerivedTensorFunctor A D E).map ((derivedBimoduleLeftUnitIso A E D hD).hom.app P) =
  Functor.whiskerLeft (kernelDerivedTensor A D E P) (kernelIdentityIso A E).hom ≫
    (Functor.rightUnitor (kernelDerivedTensor A D E P)).hom
```

bimodule順で左単位、作用順では恒等kernelを後に作用させる図式。
証明はD・EのlocalHomKFlatを明示して既存三角・右単位と全kernel結合coherenceを使う。
PのK-flat性・列の射影性は不要。Morita/U16a.leanは公開API全体のproduction入口、U16aChecksは統合監査入口。

### 9. 実際の右随伴の比較正方形（実装・検証済み）

Morita/AdjunctionSquare.leanは、左作用L・L'がともにIsEquivalenceである場合に、
任意の比較e : L ⋙ T ≅ S ⋙ L'からkernelDerivedHomであるR・R'の比較
kernelRightAdjointSquareIso : R ⋙ S ≅ T ⋙ R'を構成する。
A・A'の係数環宇宙と四つの対象宇宙は独立で、各Smallを保持する。
_hom_appは実際のunit/counitによる成分計算、_unit／_counitは両構造との実際の整合図式、
_identityは恒等比較での関手単位子との一致。

Morita/AdjunctionScalarExtension.leanのkernelRightAdjointLocalizedBaseChangeIsoは、
既存scalarKernelLocalizedDerivedSquareをこの定理へ適用する。
通常代表P、hα・hAug・hP'と、変更前後両kernelの作用の同値性を保持する。
_counitは元の実際の左作用の正方形へ戻す図式。
既存の三条件と明示したcompact生成から同値性を供給する接続はAdjunctionSquareChecksで検査済み。
この条件付き右随伴比較で、未完のU12f成分一致や左作用のkernel合成係数変更図式を代用しない。
既存の公開型は変更せず、新規APIとして追加した。

### 10. 恒等・合成kernelの実際の一般右随伴（実装・検証済み）

Morita/AdjunctionCoherence.leanをimportする。

```lean
def kernelDerivedHomIdentityIso :
  kernelDerivedHom A D D (kernelIdentity A D) ≅ 𝟭 (DerivedModuleCategory A D)
def kernelDerivedHomCompositionIso (hD : localHomKFlat A D)
  (P : Kernel A D E) (Q : Kernel A E F) :
  kernelDerivedHom A D F (kernelCompose A D E F hD P Q) ≅
    kernelDerivedHom A E F Q ⋙ kernelDerivedHom A D E P
```

恒等比較には局所Hom条件不要、合成にはhDだけを保持し、Morita性・列の射影性は不要。
kernelIdentityRightAdjunctionとkernelCompositionRightAdjunctionは、同じ公開作用比較で移した随伴。
後者の_unit_app／_counit_appは、元の二随伴の実際の成分とkernelCompositionIsoによる計算。
kernelDerivedHomIdentityIso_unit／_counitとkernelDerivedHomCompositionIso_unit／_counitは、
実際のkernelDerivedUnit／Counitを同じ計算へ接続する等式である。
元の一般右随伴とunit/counitの定義・型は変更していない。

### 実装状態と他担当の利用境界

| API群 | 状態 | 他担当の利用 |
| --- | --- | --- |
| Kernel・kernelIdentity・kernelGraph・kernelCompose・kernelComposeMap | 実装・対象ビルド済み | 型・向きは上記で固定 |
| kernelTensor・値・graph一致 | 実装・対象ビルド済み | 同上 |
| 主導来作用・任意解像度計算 | 実装・検証済み（U16a3） | Morita/KernelDerivedFunctor.leanをimportして利用できる |
| 一般右随伴・unit/counit・左右三角恒等式 | 実装・検証済み（U16a13） | Morita/AdjunctionDerived.lean。公開型は変更なし |
| 恒等作用比較 | 実装・検証済み（U16a4） | Morita/CoherenceIdentity.leanのkernelIdentityIso |
| 合成の作用比較・全kernel射の自然性 | 実装・検証済み（U16a9・15・20）。両単位・任意kernel結合coherenceも受入済み | Morita/CoherenceComposition.leanのkernelCompositionIso・kernelCompositionIso_naturality・kernelCompositionIso_kFlat |

U16b担当が構成するgraph作用と`dgDerivedExtension`の自然同型はQuasiEquivalence*に置く。
このチャットは同ファイルを編集しない。導来作用が未実装の間も、通常graph一致はKernelTensorで提供する。
不足する比較は双方の所有範囲の新規アダプタに置き、既存のDerived/・Endomorphism/等を変更しない。

## 分担と次工程

このチャットはU12e-local受入、U16aの公開API固定、一般経路の棚卸し、U16a証明、U16cの順に進める。
U16b→dはdg-U14チャットのMorita/QuasiEquivalence*・Perfect*・ScalarExtension*・Center*と
`dg-theory-morita-qe.md`、U17c/dの一部は局所K-flat版担当のVerdier/・Quotient/DerivedComparison*。
新しいsorry・axiom・引用は追加しない。DG-MOR等が必要なら採用せず止まって報告する。

U16cではmoduleCompact_iff_perfect、perfectEndomorphismDG_quasiEquivalence、
endomorphismDerivedEquivalence_ofCompactGeneratorを再利用する。
perfect性・全Homの擬同型・compact生成は独立条件であり、局所Hom K-flat性から自動にはしない。
U16aとU16cの実際の右随伴との統合は受入済み（§17.273・274）。U16全体はU16dの残接続を待つ。


## U16a1：公開型と通常作用の固定・検証（2026-10-17）

KernelBasic・KernelTensor・KernelChecksを対象ビルドし成功（2607 jobs、警告なし）。
KernelChecksは8宣言の#checkと直接公理監査を再現する。標準3公理以内で、新しいsorry・axiom・引用なし。
主導来作用・一般右随伴・恒等／合成の作用比較は冒頭の型のみ確定であり、U16a全受入ではない。
既存公開APIの型・名前・証明は変更していない。U16b/d担当のMoritaファイルは編集していない。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.KernelChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/KernelChecks.lean
```

次は指定の順に従い一般経路の棚卸し・docstring整理を行い、その後主導来作用の証明へ戻る。


## 一般経路の棚卸し完了・U16a証明への復帰（2026-10-17）

指定された順序の棚卸し・docstring整理を実施し、記録をdg-theory-u12e-general-inventory.mdへ保存した。
U12e-generalは中断・未受入のまま。局所入口とKernelTensorのResolution/依存はともに0件。
次は冒頭で型を固定した主導来作用、一般右随伴とunit/counit、恒等・合成の作用比較の証明を進める。
U16a・U16cの全受入を宣言するものではない。既存公開型の変更はない。


## U16a2：任意の通常kernelの導来作用と入力解像度（2026-10-17）

KernelResolution.leanは任意のP : Bimodule A E Dについて、入力右D加群だけを射影解像して
主導来関手kernelDerivedTensorOnBimoduleを構成する。Homの局所K-flat性は要求しない。
U10のmoduleDerivedResolutionFunctor・moduleDerivedResolutionIsoを再利用し、
解像度選択の自己・推移則をそのままtensorのH⁰関手へ送る。

共通変数は冒頭と同じで、以下の追加公開型を固定する。

```lean
variable (P : Bimodule A E D)
def kernelHomotopyToDerived : ModuleHomotopyCategory A D ⥤ DerivedModuleCategory A E
def kernelResolutionDerivedTensor
  (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
  DerivedModuleCategory A D ⥤ DerivedModuleCategory A E
def kernelDerivedTensorOnBimodule : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E
def kernelResolutionDerivedTensorIso
  (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
  kernelResolutionDerivedTensor A D E P R ≅ kernelResolutionDerivedTensor A D E P S
def kernelDerivedTensorOnBimoduleComputation {M : ModuleCategory A D}
  (R : ModuleProjectiveResolution A D M) :
  (kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M) ≅
    (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj R.obj)
lemma kernelDerivedTensorOnBimodule_graph (f : DGFunctor A D E) :
  kernelDerivedTensorOnBimodule A D E (functorGraph A D E f) = dgDerivedExtension A D E f
```

kernelTensorHomotopyComputationとkernelResolutionDerivedTensorComputationはH⁰と指定解像度族での計算。
kernelResolutionDerivedTensorIso_self・_transは二つ／三つの解像度族の比較の整合性。
これらは既存公開型の変更ではなく追加APIである。graph一致は既存導来延長そのものとの等式で、
U16b担当はこの通常kernel版を直接利用できる。

U16a2の時点では、主導来kernel全体のkernelDerivedTensorFunctorは型のみ確定だった。
今回の通常kernel作用をkernelの射に自然な族へまとめ、kernelの準同型を反転して降ろす必要がある。
一般右随伴・恒等／合成の作用比較・U16cも残る。U16a全受入ではない。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.KernelResolutionChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/KernelResolutionChecks.lean
```


検証：KernelResolutionChecks・既存kernel型検査・局所受入・General入口検査・Spectra.StageTwoの
合同ビルド成功（3524 jobs、警告なし）。追加10宣言の直接公理監査は標準3公理のみ。
文書検査は24 Markdown・326 exposition参照、失敗0件。新しいsorry・axiom・引用なし。


## U16a3：kernelの射・準同型反転と主導来作用の実装（2026-10-17）

**冒頭§3の三宣言は型を変えずに実装・検証済みへ更新した。**
主導来kernelの利用者は以下をimportする。一般分解の入口は経由しない。

```lean
public import SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctor
```

KernelNaturality.leanのkernelClosedFamilyNatTransは、全Hom自然な加群値bimodule射を
閉零関手の自然変換にする。源の全加群型にSmallを要求しない。
kernelTensorMap、kernelTensorHomotopyMapは通常／H⁰の入力上の作用の自然変換で、
_app・_id・_compを証明した。kernelTensorMap_valueは各値のbalanced tensor mapとの一致。
kernelTensorMap_projective_quasiIsoは、任意kernel準同型と射影的右D入力について
出力が準同型になることを示す。射影性⇒相対K-flat性の既存APIを再利用している。

KernelDerivedFunctor.leanでは次の追加公開型を固定した。共通変数は冒頭と同じ。

```lean
def kernelResolutionDerivedTensorMap
  (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
  {P P' : BimoduleCategory A E D} (f : P ⟶ P') :
  kernelResolutionDerivedTensor A D E (BimoduleCategory.underlying A E D P) R ⟶
    kernelResolutionDerivedTensor A D E (BimoduleCategory.underlying A E D P') R
lemma kernelResolutionDerivedTensorMap_isIso
  (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
  {P P' : BimoduleCategory A E D} (f : P ⟶ P')
  (hf : BimoduleCategory.quasiIso A E D f) :
  IsIso (kernelResolutionDerivedTensorMap A D E R f)
def kernelDerivedTensorOnBimoduleFunctor :
  BimoduleCategory A E D ⥤ (DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
lemma kernelDerivedTensorFunctor_fac :
  bimoduleToDerived A E D ⋙ kernelDerivedTensorFunctor A D E =
    kernelDerivedTensorOnBimoduleFunctor A D E
def kernelDerivedTensorOnBimoduleIso (P : BimoduleCategory A E D) :
  kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj P) ≅
    kernelDerivedTensorOnBimodule A D E (BimoduleCategory.underlying A E D P)
```

作用の準同型反転にはlocalHomKFlatを要求しない。H⁰上の出力準同型を主導来圏で反転し、
任意の導来入力へ既存の入力解像度計算と局所化の本質的全射性で運ぶ。
従って対象だけでなくkernelの任意の導来射に対する作用も同じ主局所化上で定まる。

kernelDerivedTensorOnBimoduleIsoとU16a2のkernelDerivedTensorOnBimodule_graphを合成すれば、
U16b担当は主導来graph kernelの作用を既存のdgDerivedExtensionへ比較できる。
こちらでQuasiEquivalence*の比較を重複実装していない。既存公開型の変更は0件。

KernelDerivedFunctorChecksは任意可換環・独立宇宙、任意指定入力解像度族、標数2で検査する。
同入口とKernelResolutionChecks・U12eLocal・General入口検査・Spectra.StageTwoの合同ビルド成功
（3526 jobs、警告なし）。追加公開22宣言の直接公理監査は重複・欠落なく標準3公理以内。
文書検査は24 Markdown・326 exposition参照、失敗0件。
主導来作用入口の推移的project依存は434ファイル、Resolution/依存0件。
U16a3時点では一般右随伴・unit/counit、恒等と合成の作用比較が型のみ確定であり、U16a全受入ではなかった。
次はこれらを証明し、その後U16cへ進む。DG-MOR等の引用は追加していない。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctorChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/KernelDerivedFunctorChecks.lean
```


## U16a4：対角kernelの恒等作用（2026-10-17）

**冒頭§5のkernelIdentityIsoは、公開型を変えず実装・検証済みへ更新した。**

```lean
public import SerrePositivity.DifferentialGraded.Morita.CoherenceIdentity
```

kernelIdentityClosedIsoは、既存の通常左bimodule単位子を全右D加群に評価した自然同型。
kernelIdentityHomotopyIsoは、その同型をMathlibの商の普遍性でH⁰へ降ろす。
全右加群型へのSmall仮定は追加しない。

kernelInputResolutionHomotopyAugmentationは任意の指定入力射影解像度族の増大を自然変換へ束ねる。
kernelInputResolutionDerivedAugmentationIsoは出力局所化で増大を反転した同型、
kernelInputResolutionDerivedCounitIsoはそれを全主導来入力へ延長した比較同型である。
**このCounitIsoは入力解像度の増大比較であり、一般kernelのtensor–Hom随伴の余単位ではない。**

kernelDerivedTensorOnBimoduleIdentityIsoはH⁰単位子と入力解像度比較を合成し、
kernelIdentityIsoはさらに既存kernelDerivedTensorOnBimoduleIsoを前置したもの。
従って主導来対角kernelそのものの作用から恒等関手への自然同型である。
任意可換環・非有界、DのSmall.{u}だけを要求し、localHomKFlatは不要。

CoherenceIdentityChecksは任意の導来入力、任意の指定入力射影解像度族、標数2で型を確認する。
主導来kernel・局所受入・General入口・Spectra.StageTwoとの合同ビルド成功（3527 jobs、警告なし）。
公開7宣言の直接公理監査は重複・欠落なく標準3公理以内。
文書検査は24 Markdown・326 exposition参照、失敗0件。
恒等作用入口の推移的project依存は435ファイル、Resolution/依存0件。
一般右随伴・unit/counit、合成比較および恒等・合成の作用coherenceは未完。U16a全受入ではない。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.CoherenceIdentityChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/CoherenceIdentityChecks.lean
```


## U16a5：通常合成・相対K-flat入力での増大比較と自然な計算モデル（2026-10-17）

ユーザーの再開指示に従い、CoherenceCompositionClosedの名前解決・dg関手外延性を修正した。
kernelTensorCompositionClosedIsoは通常作用の合成を通常合成kernelの作用に、
kernelTensorCompositionHomotopyIsoはそのH⁰関手を自然同型で比較する。
KernelAugmentationのkernelDerivedTensorAugmentationは実際の入力増大により自然な比較を作り、
kernelRelativeKFlatComputationは相対K-flat入力でそれを反転する。
KernelResolutionModelのkernelResolutionTensorModelFunctorは任意の入力射影解像度族から
通常tensorの主導来像を値に持つ実際の関手を作る。kernelResolutionTensorModelIsoと
kernelResolutionTensorModelFunctor_mapが全ての通常入力射で計算を保証する。
FubiniによるkernelTensor_relativeKFlatは合成比較の同型性に使う。

いずれにもlocalHomKFlatは不要。kernelTensor_relativeKFlatのkernelには右相対K-flat性を明示する。
主導来kernel全体のkernelCompositionIsoはこの時点ではまだ未実装であり、型のみ確定を維持する。
一般右随伴・unit/counit、kernel射に自然な作用合成のcoherence、U16cも未完。

CoherenceCompositionClosedChecksと既存作用・恒等・局所受入・一般入口・Spectra.StageTwoの
合同ビルド成功（3531 jobs）、追加21公開宣言の直接公理監査は標準3公理以内。
既存の公開APIの型・名前は変更していない。新規sorry・axiom・引用はない。


## U16a6：全導来kernelの作用の合成比較（2026-10-17）

冒頭§5のkernelCompositionIsoを、型を変更せず実装・検証済みに更新した。
利用入口はMorita/CoherenceComposition.lean。必要なlocalHomKFlatは始域Dだけで、E・Fには追加しない。

CoherenceCompositionKFlatのkernelResolutionTensorCompositionIsoは、右相対K-flatな最初のkernelと
任意の後のkernelについて、通常入力射に自然な解像度モデル上の比較を作る。
kernelDerivedTensorOnBimoduleCompositionIsoは主局所化の普遍性から全導来入力へ延長する。
CoherenceCompositionのkernelCompositionKFlatIsoはU12e-localの
 derivedBimoduleComposeKFlatValueIsoと実際の主導来作用を接続する。
kernelCompositionIsoは任意の主導来P・QをそれぞれK-flat代表・通常代表へ比較して運ぶ。
入力導来加群への自然性はこの関手自然同型に含まれる。
**kernel射に対する自然性、代表選択の整合性、恒等・結合coherenceは引き続き未完。**
一般右随伴・unit/counitも型のみ確定であり、U16a全受入はまだ行わない。

CoherenceCompositionChecksは任意可換環・独立宇宙・標数2を検査し、他担当の
kernelCompose_columnsPerfectへ実際のkernelCompositionIsoを渡せることも確認する。
他担当のPerfファイルは変更していない。U16dはeCompの入力をこの公開同型で埋められるが、
hNatを要求する比較にはまだkernel射の自然性の証明が必要。
追加4宣言の直接公理監査は標準3公理のみ。既存基盤・作用・恒等・局所受入・一般入口・
Spectra.StageTwoとの合同ビルド成功（3565 jobs）。新規sorry・axiom・引用なし。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionChecks.lean
```


## U16a7：kernel射に関する増大・計算と通常合成の自然性（2026-10-17）

KernelAugmentationNaturalityは任意の通常kernel射について、H⁰計算・任意入力解像度計算・
主導来増大の自然性を証明する。kernelResolutionTensorModelMapは自然なモデル間の実際の自然変換、
kernelResolutionTensorModelIso_kernel_naturalityは主導来作用の射との比較square。
CoherenceCompositionNaturalityは通常作用射の水平合成を入れ子bimodule射として計算し、
kernelTensorCompositionClosedIso_kernel_naturalityを既存結合子の三変数自然性から証明する。
いずれにもlocalHomKFlatは不要。追加8公開宣言の直接監査は標準3公理以内。
既存kernelCompositionIsoも再監査して同じ。合同ビルド成功（4087 jobs）。

kernelTensorCompositionSourceIsoの公開型は維持し、定義を恒等成分と全Hom map計算による
直接のNatIso.ofComponentsへ変更した。これにより成分の計算を、巨大な関手等式の輸送を展開せず使える。
資源上限の変更・新規sorry・axiom・引用はない。
全導来kernelの合成比較のkernel射自然性はまだ未完で、通常自然性からK-flat計算と
主局所化へ運ぶ必要がある。一般右随伴・unit/counitと作用coherence、U16cも未完。


## U16a8：K-flatモデルのkernel自然性と導来入力での成分計算（2026-10-17）

CoherenceCompositionKFlatNaturalityのkernelResolutionTensorCompositionIso_kernel_naturalityは、
両端が右相対K-flatな最初のkernelの任意射と、後の任意kernel射の作用合成square。
任意の指定入力射影解像度族Rを使い、localHomKFlatは要求しない。
kernelResolutionTensorCompositionIso_hom_appは増大と通常結合子での計算。
kernelDerivedTensorOnBimoduleCompositionIso_hom_appは、全導来入力へ延長した比較を
元の入力でそのモデル比較に計算する。公開名・型の変更はなく追加APIである。

追加全3宣言の直接公理監査は標準3公理のみ。合同ビルド成功（4088 jobs）。
資源上限を変更せず、成分計算を独立補題へ分けて検証した。新規sorry・axiom・引用なし。
全導来kernelのkernelCompositionIsoの射自然性・代表選択の整合性と作用coherenceは未完。
次はモデル比較のkernel自然性と今回の成分計算を主局所化からの自然変換の一意性で接続し、
K-flatkernel局所化と主導来kernel圏の比較へ運ぶ。一般右随伴・unit/counit、U16a全受入とU16cも未完。


## U16a9：積局所化による全導来kernel射の自然性（2026-10-17）

CoherenceCompositionDerivedNaturalityは、通常kernelの導来作用合成比較を両kernel射に自然にした。
KernelComparisonNaturalityは主導来作用と通常代表作用の比較、およびその水平合成の自然性。
CoherenceCompositionValueNaturalityはU12e-localのK-flat値計算を両kernel射に自然な一つのsquareへまとめる。
CoherenceCompositionFamiliesは作用の合成族・合成kernelの作用族、CoherenceCompositionLocalizationは
それらの積圏表示とkernelCompositionModelsを定義する。射のクラスは
rightKFlatQuasiIsoとBimoduleCategory.quasiIsoの積。始域DのlocalHomKFlatの下で積関手が指定局所化になる。
Mathlibの積局所化と既存rightKFlatDerivedEquivalenceを使い、一般の分解経路は経由しない。

CoherenceCompositionNaturalIsoはモデル上の三つの自然な比較を合成し、
kernelCompositionNaturalIsoを積局所化から全導来kernelへ延長する。
CoherenceCompositionのkernelCompositionIsoは、同じ公開型のままこの自然な族の成分へ更新した。
公開名・型・仮定・向きの変更はなく、利用側の移行は不要。
kernelCompositionIso_naturalityは両kernelの任意の主導来射に対する比較square。
kernelCompositionIso_modelは指定モデルでの計算、kernelCompositionIso_kFlatは既存の
kernelCompositionKFlatIsoとの一致。K-flatモデルの既存計算も保持する。

CoherenceCompositionCanonicalChecksは独立宇宙・任意可換環・標数2に加え、
他担当のperfectDerivedKernelCompositionIso_naturalityのhNatをこの実際の定理で埋めて検査する。
担当28宣言を直接監査し、追加26・既存2の再監査に欠落・重複なく標準3公理のみ。
既存自然性・合成・局所受入・一般入口・別担当QuasiEquivalence入口・Spectra.StageTwoとの
合同ビルド成功（4096 jobs、警告0件）。新しいsorry・axiom・引用・資源上限変更なし。
恒等・結合の作用coherenceと一般右随伴・unit/counitは未完。U16a全受入とU16cは継続中。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionCanonicalChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/CoherenceCompositionCanonicalChecks.lean
```


## U16a10：任意kernelの通常Homと表現対象の初期被覆（2026-10-17）

AdjunctionHom.leanのkernelHomModuleはP : Bimodule A E Dに沿って、全右E加群dg圏上の
代表加群Hom(−,N)をDへ制限する。kernelHomParamは既存のパラメータ付きYoneda作用の制限。
kernelHomはこれを全Hom自然なdg関手へまとめる。値はmoduleHom A E (P.rightAt d) Nそのもの。
kernelHom_map_πは全Hom写像を共変representableの写像で計算し、kernelHom_map_evalは
閉零射での出力評価が元の全Hom endの後合成であることを示す。
全右E加群型のSmall、kernelの射影性・局所Hom K-flat性は要求しない。
既存EndomorphismのYoneda・後合成計算を読み取り専用で再利用した。

AdjunctionBrownSeed.leanは任意の指定関手L : D(D) ⥤ D(E)と対象Yに対する初期生成元被覆。
brownSeedRawIndexは全てのp : D × ℤとL(moduleCompactGenerators p) ⟶ Yの対。
既存の主導来圏の局所小性とSmall.{u} Dにより、この添字がSmall.{u}であることを証明し、
brownSeedIndexでShrink.{u}を取って実際のu-small余積brownSeedを構成する。
指定したその余積の保存PreservesColimit (Discrete.functor (brownSeedFamily ...)) Lを明示し、
brownSeedMapと各成分の計算brownSeedMap_ιを与える。
brownSeedMap_generator_surjectiveは各shiftした代表加群のL像からYへの任意射が
L(brownSeed)を経由することを証明する。随伴や表現可能性の存在は入力にしていない。
恒等関手でこの保存仮定が実際に供給できることもChecksで検査する。

これらは一般導来右随伴の構成の部分成果である。kernelDerivedHom・kernelDerivedAdjunction・
unit/counitの公開契約は型のみ確定のまま。後続では次を証明する。

1. 実際のkernelDerivedTensorに対するu-small余積保存：任意J : Type uについて
   PreservesColimitsOfShape (Discrete J) (kernelDerivedTensor A D E K)。
   exact性・shiftは別担当Verdier/KernelActionTrianglesの存在を確認しており、読み取り専用で再利用する。
2. 生成元からのkernelに当たる全射をconeで殺す後続段階を作り、同じ初期射を延長する。
3. 可算telescopeとcompact生成から表現対象と全入力に自然なHom同値を作る。
4. そのHom同値から実際の右随伴・unit/counit・三角恒等式を構成する。

局所K-flat性をhomotopically projective性に置き換えていない。
一般右随伴を射影的な列だけへ縮小して受け入れるものではない。
恒等・結合の作用coherence、U16a全受入とU16cも未完である。

AdjunctionHomChecksの6宣言、AdjunctionBrownSeedChecksの9宣言（instance・abbrevを含む）を
直接監査し、宣言名の欠落・重複なく標準3公理のみ。
新旧合成自然性・別担当QuasiEquivalence入口・局所受入・一般入口・Spectra.StageTwoとの
合同ビルド成功（4097 jobs、警告0件）。新規sorry・axiom・引用・資源上限変更なし。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.AdjunctionHomChecks SerrePositivity.DifferentialGraded.Morita.AdjunctionBrownSeedChecks SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionCanonicalChecks SerrePositivity.DifferentialGraded.Morita.QuasiEquivalence SerrePositivity.DifferentialGraded.Checks.U12eLocal SerrePositivity.DifferentialGraded.Checks.U12eGeneralInventory SerrePositivity.Spectra.StageTwo
lake env lean SerrePositivity/DifferentialGraded/Morita/AdjunctionHomChecks.lean
lake env lean SerrePositivity/DifferentialGraded/Morita/AdjunctionBrownSeedChecks.lean
```


## U16a11：任意kernelの余積保存・関係除去・可算近似列（2026-10-17）

進行中だった単位を調査前の停止点として確定する。詳細・検証はdg-theory.md §17.262。
AdjunctionKernelCoproductsのkernelDerivedTensorPreservesCoproductsは、
任意J : Type zとSmall.{u} Jについて実際の主導来作用の余積保存を与える。
これはlemmaであり、利用箇所でletによりinstanceを供給する。
局所Hom K-flat性・kernelの射影的列は不要。

AdjunctionKernelSuccessorのkernelBrownSeedMapとkernelBrownSuccessorは、追加仮定なしで
初期生成元被覆と全生成元関係の消去を実際のkernel作用に適用する。
AdjunctionKernelSequenceのkernelBrownApproximation・kernelBrownTransitionを反復し、
kernelBrownDiagramとkernelBrownTargetCoconeへまとめた。
全段階の生成元全射性・後続関係消去・標的射の互換性も公開した。
一般右随伴の存在を仮定する構成ではなく、存在証明の途中の数学的対象である。

残るのはtelescopeの表現対象、全入力で自然なHom同値、実際の右随伴・unit/counit・三角恒等式。
恒等・結合の作用coherenceも未完。U16a全受入とU16cには進んでいない。
調査報告後はユーザー指示まで新しい証明単位に入らない。

3つの新規Checksを含む合同ビルド成功（4113 jobs、警告0）。
直接公理監査は38新規宣言で標準3公理以内。新規sorry・axiom・引用なし。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelCoproductsChecks SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelSuccessorChecks SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelSequenceChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/AdjunctionKernelCoproductsChecks.lean
lake env lean SerrePositivity/DifferentialGraded/Morita/AdjunctionKernelSuccessorChecks.lean
lake env lean SerrePositivity/DifferentialGraded/Morita/AdjunctionKernelSequenceChecks.lean
```


## U16cの新分担（2026-10-17）

ユーザーの新しい指定により、このチャットはU16aの一般右随伴・unit/counit・受入に集中し、
その後U16cの最終統合とU16全体の受入を担当する。
CriterionPerf*は局所K-flat版チャット（記録dg-theory-morita-criterion.md）、
CriterionDerived*はdg-U14チャットの所有とし、読み取り専用で利用する。
このチャットはKernel*・Adjunction*・Coherence*と統合用Criterion.lean／U16.leanを使う。
統合では両担当が作った同値の逆関手を実際の右随伴と比較し、unit/counitの可逆性を証明する。
一般右随伴の公開型は本書冒頭の型を維持し、証明完成時に実装状態を更新する。


## U16a12：telescopeと生成元上のHom全単射（2026-10-17）

AdjunctionKernelTelescopeのKernelBrownTelescopeは可算近似列のtelescopeと、
その実際のkernel像からYへの延長射を持つ。kernelBrownTelescope_nonemptyで存在を証明し、
kernelBrownTelescopeで選んだ対象を公開した。局所Hom K-flat性・kernel列の射影性は不要。
AdjunctionKernelGeneratorHomのkernelBrownTelescope_generator_bijectiveは、
全ての整数shiftした代表加群Gpに対して、f ↦ L.map f ≫ targetが
Hom(Gp,S.obj)とHom(L(Gp),Y)の全単射であることを証明する。
compact性による有限段階因子分解と後続関係消去を用い、引用を追加していない。

次は全入力へこのHom全単射を拡張し、実際の右随伴・unit/counit・三角恒等式へ進む。
冒頭の公開型は変えていない。右随伴存在は依然「型のみ確定」であり、U16a全受入ではない。
一般右随伴を完成させた後、別担当CriterionPerf*・CriterionDerived*を読み取り専用で統合する。

AdjunctionKernelTelescopeChecksを新旧入口と合同ビルドし成功（4124 jobs、警告0）。
新規14宣言の直接公理監査は標準3公理以内。詳細はdg-theory.md §17.264。


## U16a13：全入力のHom表現と実際の導来右随伴（2026-10-17）

AdjunctionHomTrianglesで指定射L(R)→YのHom比較の全単射性を三角形の両端から中央へ運んだ。
AdjunctionHomClosureでは同型・retract・保存される余積の閉性を証明し、
全shiftでの比較が全単射になる入力brownHomPropertyが三角部分圏を定めることを示した。
AdjunctionHomGenerationのbrownHomComparison_allは既存moduleLocalizing_allにより
全shift代表生成元での全単射性を全主導来入力へ拡張する。
kernelBrownTelescope_hom_bijectiveとkernelBrownTelescopeHomEquivが、任意kernelの実際のtelescopeへ適用する入口。

AdjunctionDerivedのkernelDerivedHomEquivと始域自然性から、Mathlibの
Adjunction.rightAdjointOfEquiv／adjunctionOfEquivRightで実際のkernelDerivedHomと
kernelDerivedAdjunctionを構成した。unit/counitと左右三角恒等式も公開契約どおり証明済み。
公開型・仮定は変更していない。局所Hom K-flat性・kernel列の射影性は不要。
余単位はkernelDerivedCounit_modelで構成時の標的射そのものと比較できる。

AdjunctionDerivedChecksを新旧telescope・合成自然性・QuasiEquivalence・局所入口・
一般入口・Spectra.StageTwoと合同ビルドし成功（4129 jobs、警告0）。
新規27宣言（abbrev・instanceを含む）の直接公理監査は標準3公理以内。
新規sorry・axiom・引用・資源上限変更なし。詳細はdg-theory.md §17.265。

次は恒等・結合の作用coherenceを検証してU16aを受け入れ、その後別担当のCriterionPerf*・
CriterionDerived*を実際の右随伴と統合する。U16全体の受入はまだ行っていない。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.AdjunctionDerivedChecks
lake env lean SerrePositivity/DifferentialGraded/Morita/AdjunctionDerivedChecks.lean
```


## U16a14：恒等・合成比較と通常tensor増大の同じ計算経路（2026-10-17）

CoherenceCompositionAugmentationのkernelDerivedTensorOnBimoduleCompositionIso_augmentationは、
任意通常入力で、導来合成比較と合成kernelの増大が、二つの増大と通常合成比較の経路に一致することを示す。
最初のkernelの右相対K-flat性を明示し、局所Hom K-flat性は要求しない。
_relativeKFlat版では相対K-flat入力で同じ図式を同型の等式にする。
CoherenceIdentityAugmentationのkernelDerivedTensorOnBimoduleIdentityIso_augmentationは、
既存の導来恒等比較が通常tensor増大と元の対角単位子の主導来像を計算することを示す。
入力の相対K-flat性・局所Hom K-flat性は不要。

この二つの計算は公開比較の定義を変えず、単位・結合の作用coherenceを通常bimodule図式へ帰着するもの。
coherence全体とU16a全受入は未完。一般右随伴・unit/counitの実装済み状態は維持する。
新規9宣言の直接公理監査は標準3公理以内、合同ビルド4131 jobs・警告0。
再現入口はMorita/CoherenceAugmentationChecks、詳細はdg-theory.md §17.266。


## U16a15：主導来kernel作用の右単位coherence（2026-10-17）

CoherenceUnitClosedは既存bimoduleの三角図式を全右加群で評価し、
通常作用の合成比較と元の右単位子がkernelIdentityClosedIsoに一致する図式を証明した。
kernelTensorFamilyMapは入力族のbimodule射のtensorを作用の入力射へ計算する。
CoherenceProjectiveExtのkernelActionNatTrans_ext_projectiveで、
主導来自然変換の一致を射影通常入力だけで判定できるようにした。
CoherenceUnitDerivedは増大squareを相対K-flat入力で反転して通常図式へ帰着し、
標準射影解像度の自然性で全導来入力へ右単位図式を拡張した。

CoherenceUnitMainのkernelCompositionIso_rightUnitは、公開kernelCompositionIsoと
U12e-localの実際のderivedBimoduleRightUnitIso・公開kernelIdentityIsoの図式である。
恒等kernelは右K-flatなので既存モデル計算を使い、任意の主局所化kernelへ適用できる。
合成の始域DのlocalHomKFlatだけを保持し、Eの条件やPのK-flat性は追加していない。
公開比較の定義・従来の型は変更していない。左単位・結合coherenceは残るためU16a全受入ではない。

CoherenceUnitChecksを新旧増大・一般随伴・合成自然性・QuasiEquivalence・局所受入・
一般入口・Spectra.StageTwoと合同ビルドし成功（4136 jobs、警告0）。
新規7宣言の直接公理監査は標準3公理以内。新規sorry・axiom・引用・資源上限変更なし。
詳細はdg-theory.md §17.267。


## U16a16：三因子作用の通常・右K-flatモデル上の結合coherence（2026-10-17）

CoherenceAssociatorClosedのkernelTensorCompositionClosedIso_associatorは、
通常作用の合成比較の二経路を元のbimodule結合子で比較する実際の等式。
既存pentagonを逆向きへ変形し、全右加群で評価して証明した。
CoherenceAssociatorAugmentationのkernelTripleAugmentationと左右の増大計算は、
導来経路が同じ増大を通る通常図式へ降りることを示す。

CoherenceAssociatorKFlatのkernelDerivedTensorOnBimoduleCompositionIso_associatorは、
全主導来入力について自然変換としての結合図式を証明する。
P : Bimodule A E DとQ : Bimodule A F Eの右相対K-flat性を要求し、R : Bimodule A G Fは任意。
局所Hom K-flat性・Rの射影性やK-flat性を追加していない。
公開主導来kernelの結合図式への移送と左単位coherenceは引き続き未完。
U16a全受入を宣言せず、公開kernelCompositionIsoの型・定義は保持する。

CoherenceAssociatorChecksを新旧入口と合同ビルドし成功（4140 jobs、警告0）。
新規公開8宣言の直接公理監査は標準3公理以内。新規sorry・axiom・引用なし。
詳細・再現手順・次の接続点はdg-theory.md §17.268。


## U16a17：公開kernel結合子と作用の二モデルsquare（2026-10-17）

CoherenceAssociatorModelsのkernelAssociatorIso_model_facは、U12e-localの実際の全導来結合子と
二つの三因子kernelの通常モデルを同じassociatorIsoへ接続する。
_action_model_facはその作用のsquare。kernelCompositionIso_kFlat_facは公開合成比較と通常作用比較の計算を接続する。
KernelComparisonComponentsは通常代表での既存比較が恒等同型であることを証明し、通常kernel射での主作用を計算する。

指定K-flat二因子・任意の通常後因子のままで、余分な局所Hom条件を追加していない。
作用の結合図式の両経路の貼合せ・任意kernelへの移送、左単位coherenceは未完。
公開API第7節はkernel結合子とモデル計算の実装状態を示し、U16a全受入は意味しない。

CoherenceAssociatorModelsChecksを新旧入口と合同ビルドし成功（4142 jobs、警告0）。
新規公開8宣言の直接公理監査は標準3公理以内。新規sorry・axiom・引用なし。
詳細・再現手順・次の接続点はdg-theory.md §17.269。

文書全体検査は共有ルートの担当外PowerRootHodgeTateReduction.olean未生成で失敗した。
Markdownリンクの独立検査は26文書・欠落0件。今回exposition全API照合の成功は主張しない。


## U16a18：公開結合二経路のモデル上での貼合せ（2026-10-17）

CoherenceCompositionWhiskerの片側自然性により、K-flatモデルの計算射を公開経路の末尾へ移す。
CoherenceAssociatorPathsのkernelAssociatorLeftPath・kernelAssociatorRightPathは、
任意kernelで定義した実際の結合図式の二経路である。
左右のmodel_facとkernel結合子の作用squareから、kernelCompositionIso_associator_modelを証明した。
これは指定右相対K-flat二因子の通常代表・任意の通常後因子における、公開二経路そのものの等式。
従来のkernelCompositionIso・kernelAssociatorIsoの定義・型を変更していない。

任意主導来kernelへの同型による移送と左単位coherenceが残るため、U16a全受入とはしない。
CoherenceAssociatorPathsChecksを新旧入口と合同ビルドし成功（4145 jobs、警告0）。
新規公開8宣言の直接公理監査は標準3公理以内。新規sorry・axiom・引用なし。
文書全体検査も27 Markdown・326 exposition参照で欠落0件。
詳細・再現手順・次の接続点はdg-theory.md §17.270。


## U16a19：公開結合経路の最初の二kernel射自然性（2026-10-17）

CoherenceAssociatorNaturalityのkernelAssociatorIso_first_naturality／_second_naturalityと
kernelAssociatorLeftPath_first_naturality／_second_naturality、
CoherenceAssociatorRightNaturalityのkernelAssociatorRightPath_first_naturality／_second_naturalityを公開した。
全主導来kernel射について、同じ合成kernelへの射を末尾とする左右経路の自然性を証明する。
指定K-flat代表から任意kernelへの同型による移送に使う。
6宣言の直接公理監査は標準3公理以内、合同ビルド3815 jobs・警告0。
詳細はdg-theory.md §17.272。一般右随伴は実装済み、全kernel結合coherenceと左単位は継続中。


## U16a20：任意主導来kernelの両単位・結合coherenceとU16a受入（2026-10-17）

CoherenceAssociatorMainは既存K-flatモデル上の等式を最初の二kernelの同型で運び、
kernelCompositionIso_associatorを任意の主導来kernelで証明する。
CoherenceLeftUnitMainは、kernel三角図式とこの作用結合図式を恒等kernel二個に適用し、
既存右単位図式に帰着する。恒等kernel作用の忠実性で後合成を消去し、左単位図式を得る。
新規5宣言の直接公理監査は標準3公理以内。U16aChecks・他担当Perf判定と全導来拡張・
QuasiEquivalence・局所／一般入口・Spectra.StageTwoの合同ビルド成功（4195 jobs、警告0）。

U16aの公開APIは本節冒頭のすべてを実装・検証済みとする。作用・一般右随伴は局所Hom条件なし、
合成はD、右単位はD、左単位・結合図式はD・EのlocalHomKFlatを保持。
一般分解変更のcoherenceは含まない。詳細・受入表はdg-theory.md §17.273。
次は完成済みCriterionPerf*とCriterionDerived*を一般右随伴と統合する。


## U16c最終統合：二つの逆関手と一般右随伴（2026-10-17、受入）

Morita/Criterion.leanは、完成した三条件Perf判定とCriterionDerivedの全導来拡張を直接利用する。
両側のCriterionDerivedCompactGeneration、三独立条件、対象・生成添字の独立宇宙を保持する。
局所Hom K-flat性・kernel列の射影性・右随伴の存在を追加仮定にはしていない。

- kernelMoritaEquivalence：他担当の実際の主作用の同値。
- kernelMoritaHomIsoInverse：その逆関手とkernelDerivedHomの自然同型。
- kernelMoritaHomIsoInverse_unit／_counit：実際のunit/counitを運ぶsquare。
- kernelMoritaUnit_isIso／kernelMoritaCounit_isIso：実際の自然変換全体の可逆性。
- kernelMoritaAdjunctionEquivalence：順関手kernelDerivedTensor、逆関手kernelDerivedHom、
  単位kernelDerivedUnit、余単位kernelDerivedCounitをそのまま持つ同値。四つの計算補題は定義的な一致。
- AdjunctionPerfectInverseのkernelMoritaPerfInverseActionIso／kernelMoritaPerfInverseIso：
  Perf同値の逆関手も、包含後に同じ一般右随伴へ接続。
- kernelMoritaPerfInverseIso_counit：Perf比較を実際の余単位で元の実作用比較へ戻すsquare。

CriterionChecksの合同ビルド3869 jobs・警告0、追加15宣言の直接公理監査は標準3公理以内。
詳細はdg-theory.md §17.274。U16c統合をこの明示仮定下で受け入れる。
U16d全体の受入記録はまだなく、Perf作用coherence移送・係数変更の3接続を残すため、U16全体は未受入。
他担当のCriterionPerf*・CriterionDerived*・Perfect*・ScalarExtension*と専用記録は編集していない。


## U16d接続：既存Perf比較の作用coherence（2026-10-17）

CoherencePerfectUnitとCoherencePerfectAssociatorは、別担当の既存perfectKernelCompositionIso・
perfectDerivedKernelIdentityIso・perfectDerivedKernelMapをそのまま使う図式を証明する。
公開名はperfectKernelCompositionIso_rightUnit／_leftUnit／_associator。
右単位はD、左単位・結合はD・EのlocalHomKFlat、入力kernelの列のperfect性を保持する。
合成kernelの列のperfect性は既存APIから供給し、追加仮定にしない。

合同ビルド3872 jobs・警告0、追加3宣言の直接公理監査は標準3公理以内。
CoherencePerfectChecksがU16a・cと同時の再現入口。詳細はdg-theory.md §17.275。
U16dのPerf作用coherenceへの移送を供給したが、局所化係数変更への正方形接続・
U12f成分同定・kernel合成との係数変更図式と中心作用の保留は別担当の残接続として維持する。
U16全体の受入はまだ行わない。


## 現行U16の統合入口・担当間の接続再開（2026-10-17）

Morita/U16.leanは、完成したU16a・U16cと既存U16b/dの公開APIの独立production入口。
U16Checksは同時importと主要13宣言の再監査入口。全現行Morita Checks等92対象の
合同ビルド4271 jobs・警告0、主要13宣言の直接再監査は標準3公理以内。
これはU16全体の受入ではなく、残接続を受け取る統合先の固定である。

ユーザーの明示許可により「dg U14」へ完成APIと担当係数変更3接続の継続を連絡し、
同チャットのactiveな作業再開を確認した。詳細・再現手順・残ゲートはdg-theory.md §17.276。
他担当のファイルと公開型は変更していない。


## U16d.27の受取：主kernel係数変更の条件付き作用正方形（2026-10-17）

d156f34cのScalarExtensionKernelLocalizedSquareは、既存QuasiEquivalence入口を通してU16入口へ到達する。
scalarKernelLocalizedActionIso・scalarKernelLocalizedDerivedSquareと_augmentation、
scalarKernelLocalized_columnsPerfect・scalarKernelLocalizedPerfectSquareと_inclusionを受け取った。
通常代表とhα・hAug・hP'を指定する範囲を保持する。hαは既存hπ判定から供給できるが、
hPN・hP'でhπを代用しない。局所化正方形の全主kernel射自然性はまだ受入済みとしない。
U16Checksへ専用Checksを同時importし主要19宣言を直接再監査、標準3公理以内。
合同ビルド4026 jobs・警告0。詳細はdg-theory.md §17.277。
残るU12f成分同定・kernel合成との係数変更図式と中心作用の保留は引き続き別担当の記録に従い、
U16全体の受入はまだ行わない。


## U16d.28の受取：出力評価の導来係数変更比較（2026-10-17）

4e386dc9の出力評価比較12宣言を、既存production入口とU16Checksへ取り込んだ。
評価複体のK-flat性・加群側増大の可逆性・指定モデルを保持し、十分条件版のhEと
独立した複体導来圏宇宙z・z'、各HasDerivedCategoryも保持する。
実際の二つの増大とのsquareと許容モデル間の全閉零射自然性を含む。
U12f比較の成分一致そのものは証明中であり、この比較同型の存在で代用しない。
合同ビルド4029 jobs・警告0、統合入口の主要31宣言の再監査は標準3公理以内。
詳細と残ゲートはdg-theory.md §17.278。U16全体はまだ未受入。


## 右随伴の係数変更正方形の接続（2026-10-17）

AdjunctionSquareとAdjunctionScalarExtensionは、実際の右随伴・unit/counitを
既存の左作用の係数変更正方形へ接続する。公開契約は冒頭§9、詳細はdg-theory.md §17.279。
独立宇宙・標数2・三条件判定からの同値性供給を検査し、追加7宣言は標準3公理以内。
U16Checks・局所／一般入口・Spectra.StageTwoの合同ビルド4217 jobs・警告0。
他担当の残る左作用比較の証明は引き続き必要で、U16全体の受入とはしない。


## U16d.29〜30の受取：モデル計算とkernel合成作用図式（2026-10-17）

e2e18713の左右の出力モデル計算7宣言、91cb0e13の条件構造と実際の合成作用図式5宣言を受け取った。
U16Checksで同時importし主要50宣言を直接再監査、標準3公理以内。
合同ビルド4036 jobs・警告0。詳細はdg-theory.md §17.280。

作用図式は、元と変更後の公開kernelCompositionIsoを使うが、終域kernelは二つの変更kernelの合成。
元の合成kernelを係数変更した対象とのkernel同型と、その同型を通す正方形の一致はまだ未完。
U12f成分一致などの残ゲートも維持し、U16全体の受入とはしない。


## 恒等・逆順合成の一般右随伴比較（2026-10-17）

AdjunctionCoherenceの10宣言を追加した。任意kernelでの実際の右随伴の比較と、
実際のunit/counitの計算を公開する。正確な契約は冒頭§10、詳細はdg-theory.md §17.281。
独立宇宙・標数2・最小限の局所Hom条件をAdjunctionCoherenceChecksで検査した。
合同ビルド4038 jobs・警告0、統合入口の主要60宣言の直接再監査は標準3公理以内。
係数変更側の残接続をこの一般右随伴の計算で代用せず、U16全体はまだ未受入。


## U16全体の最終受入（2026-10-17）

ユーザー決定とdg-U14のf12ea97aの最終受入表に従い、U16全体を受け入れる。
U16aは§17.273、U16cの実際の一般右随伴との一致とunit/counitは§17.274、
Perf作用のcoherenceは§17.275、最終照合はdg-theory.md §17.282。
U16dの残接続は保留し、中心作用と群作用はM9で扱う。
過去の「全体未受入」は当時の履歴。受入範囲・全保留一覧とM9の公開入口は
[dg-theory-m5-status.md](../dg-theory-m5-status.md)を参照する。
新しい実装単位には着手せず停止する。既存公開名・型の変更なし。

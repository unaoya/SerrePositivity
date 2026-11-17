# P⁰ 基盤 P4〜P6：段0（紙）の報告

作成：2026-11-16、⑤a。ユーザー方針11-16・D81。
基準：**main `79c1315e7`**。枝：`math/p0-p4-p6`。
作業木：`../SerrePositivity-p0-p4-p6`。報告をコミットして停止する。

**段0：型案28項目（P4=11、P5=10、P6=7）、Lean実装0。**
一覧・分担・外枠はこの報告を受けて決める段階であり、実装承認済みの一覧ではない。
M14のMay案は再開しない。既存の`math/bs-impl`と未検証のL23下書きはそのまま残した。

## 1. 結論と範囲

D(F_p)でDAG XIIIの順にP4→P5→P6を作る道を推奨する。
D(F_p)の安定性・presentability・Kan延長・Indの部品を利用でき、
KSTのSpのsmash積・全余極限を先に完成させる必要を避けられるためである。
ただし**「D(F_p)を使えばスペクトル的な基盤が全く不要」ではない**。
HA 4.8.4.1の適用には、標準のスペクトル上の作用と、左右のH(F_p)作用を持つ双加群が必要。
その受け取りを§3で露出させる。未供給のKSTの比較を仮定に足して本線を無条件と呼ばない。

本線の追加見込みは素の値 **29,800〜50,900行**、係数2で **59,600〜101,800行**。
P1〜P3の費用、Sp自体の建設・模型同値、任意のMayとの全次数比較は含まない。
これらを0行と評価したのではなく、担当外または別の比較として§8〜10へ分けた。
修正係数は今回指定された**2のみ**。旧M14の5倍・7.3倍を流用しない。
今回の数字は工程の見込みで、完成保証や新しい外枠ではない。

P⁰の出力は、HAのCAlg(D(F_p))から**スペクトルへの忘却のcoherentな自己変換**。
π上の自然変換だけ、BEのCAlgの局所化だけ、あるいはD(F_p)線形な射への置き換えはしない。
BS Lemma8.4の実現・完備化への適用、一般のkへの係数変更、TC/THHは今回の完成範囲に含めない。
P⁰の構成とRem2.2.7が今回の終点である。

## 2. 読んだ資料・原典の照合で修正が要る点

指定された以下の四つを基準コミットで読んだ。

- `research/p0-lurie/README.md`
- `research/p0-lurie/spectra.md`
- `research/p0-lurie/ha-for-ns.md`
- `research/p0-lurie/map/（data.json・template.html）`：埋め込みJSONを読み、59項目であることも確認した。

原典は [DAG XIII（2011-12-15）](https://www.math.ias.edu/~lurie/papers/DAG-XIII.pdf#page=29)、
[HA（2017-09-18）](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=730)、
[NS（arXiv:1707.01799v2）](https://arxiv.org/pdf/1707.01799#page=11)の該当箇所を再照合した。
以下は調査ファイルを無断で修正する代わりの訂正提案。

1. DAG XIII Ex2.2.5のB≃k^{tG}は**左k加群として**の同値。
   Bの右作用はT_pのEilenberg–Watts表示が供給する。二つを同じ作用と仮定しない。
2. 同例が引く旧番号A.7.1.2.4と現HA4.8.4.1は、必要なEilenberg–Wattsの機能を対応させる。
   版をまたいだ番号の文字通りの同一性を主張せず、現定理の仮定を§5のP5-08へ書く。
   HA4.8.4.1のC線形性で、今回のCは**スペクトルのモノイダル基盤**。
   T_pが通常のD(k)線形であるという追加入力にしない。
3. DAGのT_pはperfect上のT̂_pからの左Kan延長。NSのT_pという記号は
   X↦(X^{⊗p})^{tC_p}そのもの。この報告では後者を`NSHat`と呼び、両者の名称で混同しない。
4. Rem2.2.7の比較は`T_p(k[n])[-1] ≃ T̂_p(k[n])[-1]`。
   −1を片側だけ落とさない。π_n=H^{-n}と合わせて§6へ固定する。
5. NS III.1.4は次数0のTate対角。DAGのP⁰はπ₁(k^{tG})の指定類と
   Tateの**シフトした境界**も使う。NSのTate値FrobeniusをP⁰と同一視しない。
   NS III.1.10とその直前にはD(Z)値の素朴な対角への注意もあるため、NS III.1.2を
   D(k)値のexact関手へそのまま置き換えない。
6. `FunctorHom`の既存定義は**関手準圏のホモトピー圏の射**。
   以下では構成に必要な辺・cofiberの図式を保持するため、実際の関手準圏の辺を使う。
   各対象でπの写像を作ってからcoherentな変換と呼ぶ方法は使わない。

研究資料の「実現・完備化とも両立」は、P⁰のcoherentな自然性だけで全てが終わるという
定理として採用しない。BSへの後続では、同じ図式・保存・指定辺の比較が別に要る。
今回はその旧M14の穴を追わない。

## 3. 紙の型の規約と、⑤dから受け取るP1〜P3の型

以下は**Markdown内の型案**。Leanファイル・新しいaxiom・実装用の仮定追加ではない。
既存名は明記するが、未構築のHAの構造の名前は紙の略記で、型検査済みとはしない。
宇宙は一つ上へ持ち上げ、BGと関手準圏のuniversesを合わせる。BGを有限単体集合とは扱わない。

```lean
-- 実在する準圏・辺の表記を基礎にする紙の略記。
FunQ (X C : SSet) := (ihom X).obj C
Obj (C : SSet) := C _⦋0⦌
NatQ {X C : SSet} (F G : X ⟶ C) := SSet.Homotopy F G
-- FunctorIso、QCatEquivalence、IsExactFunctorは既存の準圏の宣言。
-- MapQ C x y は既存のKan写像空間を選んで表したもの。
-- IsEquivalenceEdge、ColimPreserving、FiberwiseLimits等は以下の意味の紙の述語。
```

`NatQ`は辺を持つcoherentな変換。`MapQ (FunQ X C) ...`は変換の**全写像空間**を表す。
同じ記法をホモトピー圏のNatTransの型として使わない。
`SpecifiedLimitCone F`はΣc:JoinCone F, IsLimitCone c、余錐はその双対。
`SpecifiedHomotopyOfNat α β`は同じ端点を固定した関手準圏の写像空間内のpathを表す。
`IsSemiadditiveInfinity C`は全有限族のcanonicalな余積→積が同値である述語で、
単にhCにPreadditive instanceがあるという別名ではない。
`PointRepresenting c`はその写像空間の点と、そのπ₀がcである証明の対。
全加群の対象をDの座標へ書く際は、常にI03のmoduleComparisonの逆で輸送する。
`point n`/`shift n`はスペクトルの[n]と整合し、k[n]は複体では−n次数。

### 受け取りI01：HA流の対称モノイダル構造と全図式のp入力

```lean
D := derivedInfinityCategory (EInfinityPrimeField p)
Dsym : SymmetricMonoidalInfinityCategory  -- HA 2.0.0.7
Dsym_carrier : QCatEquivalence Dsym.carrier D
unitD : Obj D
powerSigma (n : ℕ) : D ⟶ FunQ (BG (Equiv.Perm (Fin n))) D
powerUnit : FunctorIso (unitPoint ≫ powerSigma p) (trivialActionPoint unitD)
tensor_exact_separately : TensorExactSeparately Dsym
tensor_colimit_separately : TensorPreservesSmallColimitsSeparately Dsym
```

pは素数、C_p→Σ_pは実際のp-cycleの選択と固定した向き。P4が作用圏の前合成を作り、
`powerCp := powerSigma p ≫ restriction(cyclicPermutation p)`とする。
既存の鎖のp重テンソルをこの欄の定義に代用しない。

### 受け取りI02：HA流CAlg、指定乗法と単位

```lean
AlgK : SSet
forgetAlg : AlgK ⟶ D
pi0Alg : ho(AlgK) ⥤ CommAlgCat k
pi0Alg_underlying : UnderlyingAdditive(pi0Alg) ≅ Pi0(forgetAlg)
multiplySigma : NatQ (forgetAlg ≫ powerSigma p)
                         (forgetAlg ≫ trivialActionSigma p)
unit_and_power_laws : CoherentCommutativeAlgebraLaws multiplySigma
```

型が表すのはHA2.1.3.1のCAlgと、その全対称群等変な乗法。
HA3.2.4.7の「テンソル＝余積」の全関手・単位・脚との整合を含めて受け取る。
Sym^pのorbit関手が必要ならP4の左Kan延長の包装と共用し、
P2にnormを作ることを前提にする循環を置かない。
BEとの比較はこの受け取りに含めず、§8で別の比較として記す。

### 受け取りI03：加群とspectral enrichmentを含むD(k)の意味づけ

```lean
SpHA : SSet
SpHA_structure : StandardStablePresentableSpectra SpHA
Hk : Obj (CAlg SpHA)
moduleComparison : SymmetricMonoidalQCatEquivalence D (LMod Hk SpHA)
perfectSmall : SSet
perfectInclusion : perfectSmall ⟶ D
perfect_compact : PerfectObjectsAreExactlyCompact perfectInclusion
indComparison : QCatEquivalence (Ind perfectSmall) D
spectralActionD : PresentableLeftAction SpHA D
moduleAndBimoduleCategories : HAModuleAndBimoduleCategories SpHA Hk
relativeTensor : HARelativeTensorWithCoherentAssociativity SpHA Hk
```

HA4.5.2.1、7.1.2.13、7.2.4.2に対応する型だけを要求し、このレーンでP1〜P3を実装しない。
ただしP3の当初の範囲に`SpHA_structure`やspectralActionDが含まれるかは**分担の確認点**。
なければHA4.8.4.1の適用前に別の供給が要り、型名があるだけで供給済みにしない。
`D`が安定・presentableという既存定理だけから、対称モノイダル構造・右Hk作用を既に持つとしない。

KSTのSpをこのSpHAと定義的に同じにする入力や、`[ModelCategory SSet]`は要求しない。
旧`eilenbergMacLaneDerived`の値域はKSTのSpなので、共通の値域の比較なしに
上の標準加群の忘却と同じ関手だとはしない。比較の型はC-06。

## 4. P4：normとTate構成の型つき一覧

この節のCは小さい図式のKan延長を持つ安定な準圏。実例はD(k)。
X,Yは小さいKan複体、fは相対有限groupoidの射、段階構成ではその(−1)/0切断の対角を使う。
一般の安定準圏だけに、BG添字の全極限・余極限があると仮定しない。
各項目の場所・見込みは§7の同じIDの行に対応する。

### P4-01 作用の準圏と制限

文献：DAG Not2.1.1/Ex2.1.2、NS I.1冒頭。

```lean
def classifyingSpace (G : Type) [Group G] : SSet
instance classifyingSpace_kan : KanComplex (classifyingSpace G)
def actionInfinity (G : Type) [Group G] (C : SSet) := FunQ (classifyingSpace G) C
def restriction (f : X ⟶ Y) : FunQ Y C ⟶ FunQ X C
```

BGはone-object groupoidのnerveと既存のgroupoid→Kanの比較を使う。
∞の作用をMathlibの`Action OmegaSpectrum G`の対象に制限しない。

### P4-02 左右Kan関手・随伴と点ごとの指定錐

文献：HTT4.3.3.7、DAG Not2.1.1、NS I.1。

```lean
def lan (f : X ⟶ Y) : FunQ X C ⟶ FunQ Y C
def ran (f : X ⟶ Y) : FunQ X C ⟶ FunQ Y C
def lanAdjunction : QCatAdjunction (lan f) (restriction f)
def ranAdjunction : QCatAdjunction (restriction f) (ran f)
def lanAt (F : X ⟶ C) (y : Obj Y) : SpecifiedColimitCone (leftKanFiberDiagram f F y)
def ranAt (F : X ⟶ C) (y : Obj Y) : SpecifiedLimitCone (rightKanFiberDiagram f F y)
```

既存Kerodonの相対Kan制限の同値・存在とfiberwise比較を使い、全関手へ包装する。
相対制限の定理の`Mono/InnerFibration/fully faithful`の仮定を一般のfへ無言で適用しない。

### P4-03 canonical mateによるBeck–Chevalley

文献：DAG Lem1.1.5、HA6.1.6.3/4.7.4.13、NS ConI.1.7。
平方はg:X′→X、g′:Y′→Y、f:X→Y、f′:X′→Y′のhomotopy pullback。

```lean
def rightBC : NatQ (ran f ≫ restriction g') (restriction g ≫ ran f')
def leftBC  : NatQ (restriction g ≫ lan f') (lan f ≫ restriction g')
theorem rightBC_invertible (h : IsHomotopyPullback sigma) : IsEquivalenceNat rightBC
theorem leftBC_invertible  (h : IsHomotopyPullback sigma) : IsEquivalenceNat leftBC
```

同じ随伴の単位・余単位から作ったmateであることと、平方の貼り合わせとの両立を保持する。
単なる二つの関手間の同型の存在や、通常圏のmateEquivに置換しない。

### P4-04 pointed性・安定性から(−1)段のnorm

文献：DAG Con2.1.3/Prop2.1.6、HA6.1.6.4/.7、NS LemI.1.8。

```lean
def normMinusOne (f : X ⟶ Y) (hf : MinusOneTruncatedFibers f) : NatQ (lan f) (ran f)
theorem normMinusOne_invertible [HasZeroVertex C] : IsEquivalenceNat (normMinusOne f hf)
theorem stable_semiadditive [IsStable C] : IsSemiadditiveInfinity C
```

空fiberと可縮fiber、対角の同値・逆、pointedのcanonicalな零射を使う。
本体`preadditive_ho`と有限双積から、∞のcanonical有限和→積が同値である橋を明示する。

### P4-05 有限集合fiberのnorm

文献：DAG Con2.1.7/Def2.1.12、HA6.1.6.8/.11/.12、NS LemI.1.9。

```lean
def normFiniteSet (f : X ⟶ Y) (hf : FiniteDiscreteFibers f) : NatQ (lan f) (ran f)
theorem normFiniteSet_invertible [IsSemiadditiveInfinity C] :
  IsEquivalenceNat (normFiniteSet f hf)
```

対角のP4-04のnormの**逆**を用いる同じ構成。離散有限集合での成分δ_ijを確認し、
安定なホモトピー圏の双積だけで全自然変換を定義したことにはしない。

### P4-06 相対有限groupoidのnorm

文献：DAG Con2.1.18、HA6.1.6.19/.22、NS ConI.1.7/DefI.1.10。

```lean
def normFiniteGroupoid (f : X ⟶ Y) (hf : RelativeFiniteGroupoid f) :
  NatQ (lan f) (ran f)
```

δ:X→X×_Y Xのfinite-set normの逆、同じ随伴のunit/counitとP4-03で作る。
BG→点へ適用する。有限groupoidの全normが同値とは主張しない。

### P4-07 normの制限・基底変換・合成との整合

文献：DAG Rem2.1.19〜2.1.22、HA6.1.6.20/.21、NS I.1の構成。

```lean
def normBaseChange : SpecifiedHomotopyOfNat
  (baseChangeOfNorm sigma) (normFiniteGroupoid f' hf')
def normComposition : SpecifiedHomotopyOfNat
  (normFiniteGroupoid (f ≫ g) hfg) (compositeNorm f g)
```

対角の再帰で選んだ逆とmateの同じデータの法則。特に自明部分群からの誘導の比較に使う。
この法則はnormの後に必要になるもので、二つの規約のnormを黙って同じにしない。

### P4-08 群のorbit/fixedとΣ_gの検算

文献：DAG Ex2.1.21/Rem2.1.22、HA6.1.6.22/.23、NS ExI.1.11。

```lean
def orbits (G) : actionInfinity G C ⟶ C
def fixed (G) : actionInfinity G C ⟶ C
def norm (G) : NatQ (orbits G) (fixed G)
theorem norm_after_unit_before_counit (M : Obj (actionInfinity G C)) :
  hom(orbitUnit M) ≫ hom(norm_at M) ≫ hom(fixedEvaluation M) =
    ∑ g : G, actionHom M g
```

最後の式はhCでの法則。**その式をnormの定義にしない**。
BGの全単体に自然なP4-06の変換が先にあり、その検算として述べる。

### P4-09 Tate関手と同じ境界

文献：DAG Def2.1.23、NS DefI.1.13。

```lean
def tate (G) : actionInfinity G C ⟶ C
def tateTriangle : PointwiseCofiberSequence (orbits G) (fixed G) (tate G) (norm G)
def tateBoundary : NatQ (tate G ≫ shift C (-1)) (orbits G)
```

安定な関手準圏で同じnormのcofiberを取り、三角形の全関手版と境界を指定する。
任意に選んだ各対象の境界射を後から自然に束ねない。

### P4-10 誘導作用での同値・Tate消滅

文献：DAG Ex2.1.25、NS III.1.1が引くI.1の消滅。

```lean
def inductionFromTrivial (G) : C ⟶ actionInfinity G C
theorem induced_norm_equivalence (M : Obj C) :
  IsEquivalenceEdge (norm_at ((inductionFromTrivial G).obj M))
def induced_tate_zero : FunctorIso (inductionFromTrivial G ≫ tate G) (zeroFunctor C C)
```

i:点→BGのKan延長とfinite setの比較を使う。鎖の正則表現の非輪状性を定義にしない。

### P4-11 exact性

文献：DAG2.1.23の直後、NS I.1/III.1.1の入力。

```lean
theorem orbits_exact : IsExactFunctor (orbits G)
theorem fixed_exact : IsExactFunctor (fixed G)
theorem tate_exact : IsExactFunctor (tate G)
```

図式圏の安定性と有限(co)limitsの可換性を使う。
P4-10は有限群を使うが、ここでは必要な全BG(co)limitsを持つことが依然として仮定。

## 5. P5：T̂_p、exact性、Kan延長とEilenberg–Watts

k=F_p、D=D(k)、pは素数。I01/I03とP4の正式な出力を受け取った後の型。
この節ではNSのid_Sp→NSHatとDAGのT_p→T̂_pを混同しない。

### P5-01 T̂_p

文献：DAG Con2.2.1/.2、NS PropIII.1.1。

```lean
def tatePowerHat : D ⟶ D := powerCp p ≫ tate (Cp p)
```

P2の全対称群のp入力を巡回群へ制限する。鎖の`projectivePowerSpectrum`をこの定義に使わない。

### P5-02 p-cubeのfiltrationと中間層の誘導表示

文献：DAG Prop2.2.3、NS PropIII.1.1の証明。

```lean
def powerCubeFiltration (s : CofiberSequence D) : EquivariantFiniteFiltration (powerCp p s.middle)
def mixedLayerInduced (s) (j : ℕ) (hj : 0 < j ∧ j < p) :
  ∃ W, VertexIso (layer (powerCubeFiltration s) j) ((inductionFromTrivial (Cp p)).obj W)
```

既存`powerOperationCyclicPermutation_mixed_free`の有限組合せの証明は再利用できる。
Kan延長での層の表示と、実際のtensorのcofiberの全図式の比較は新規。
二項直和を保つだけでexactと結論しない。

### P5-03 T̂_pのexact性

文献：DAG Prop2.2.3、NS PropIII.1.1。

```lean
theorem tatePowerHat_exact : IsExactFunctor (tatePowerHat p)
```

P5-02の全層の比較へP4-10/.11を適用する。tensorの各変数exact性はI01から。

### P5-04 perfect/compactとIndの指定包含

文献：DAG Ex2.2.5、HA7.2.4.2、HTT5.3.5.10。

```lean
def perfectUnit : Obj perfectSmall
def perfectUnit_value : VertexIso (perfectInclusion.obj perfectUnit) unitD
def D_ind_perfect : QCatEquivalence (Ind perfectSmall) D
```

I03のHAのperfect=compactを、既存のIndの普遍性の入力へ接続する。
dgの`moduleCompact_iff_perfect`をcoherentなD(k)の包含の証明なしにそのまま代入しない。

### P5-05 T_pと比較、余極限保存

文献：DAG Ex2.2.5、HTTのKan延長/Ind。

```lean
def tatePower : D ⟶ D
def tatePowerExtensionUnit : NatQ (perfectInclusion ≫ tatePowerHat p)
  (perfectInclusion ≫ tatePower p)
def tatePowerLeftKan : IsLeftKanExtensionData perfectInclusion
  (perfectInclusion ≫ tatePowerHat p) (tatePower p) tatePowerExtensionUnit
def tatePowerComparison : NatQ (tatePower p) (tatePowerHat p)
theorem tatePowerComparison_perfect (M : Obj perfectSmall) :
  IsEquivalenceEdge (component tatePowerComparison (perfectInclusion.obj M))
theorem tatePower_preservesColimits : PreservesSmallColimits (tatePower p)
```

Ind延長でfiltered保存、exact性から有限和・cofiber、従って全小余極限の保存を示す。
T̂_p自体はfiltered余極限を保つと仮定しない。既存のInd普遍性だけでは最後の全保存はまだ結論である。

### P5-06 canonicalなスペクトル線形性

文献：HA4.8.2.18〜.20、4.8.4.1の適用条件。

```lean
def colimitPreserving_isSpectralLinear (F : D ⟶ D) (hF : PreservesSmallColimits F) :
  SpectralLinearFunctor spectralActionD spectralActionD F
```

標準の安定presentableな圏のSp作用に対する構造。T_pにD(k)線形構造を追加する型ではない。
この橋がI03からそのまま来るならここは接続の法則だけとなる。担当と控除は実装前に確認する。

### P5-07 Eilenberg–Watts用の自由加群のbar resolution

文献：HA4.8.4.10以下を用いる4.8.4.1の証明、4.7のbar構成。

```lean
def moduleBar (M : Obj (RMod A C)) : SimplicialObjectQ (RMod A C)
def moduleBarAugmentation (M) : Augmentation (moduleBar M) M
theorem moduleBar_realization (M) : IsColimitCone (moduleBarAugmentation M)
```

自由忘却随伴からの**∞圏の**分裂barと、線形関手・relative tensorの下での比較。
厳密BEのbar図式や通常圏の自由加群随伴が、そのままこの主張とはしない。
I03の加群・線形関手の準圏を使う。P1〜P3の構造自体をここで作る見込みではない。

### P5-08 HA4.8.4.1の評価の同値

文献：HA Theorem4.8.4.1。ここは一般型を明示し、適用はC=SpHA。

```lean
def evaluateRegularModule :
  LinearColimitFunctors C K (RMod A C) M ⟶ LMod A M
theorem evaluateRegularModule_equivalence
    (hK : IncludesSimplicialRealizations K)
    (hC : AdmitsColimits C K) (hM : AdmitsColimits M K)
    (hTensor : TensorPreservesColimitsSeparately C M K) :
  IsQCatEquivalence evaluateRegularModule
```

対応表`research/ha-coverage/review/ch4.csv`ではnone。
既存のdg核が関手を作るという片方向だけでこの全線形関手圏の同値を証明済みにしない。
上の左右をモノイダルoppositeで交換し、
`Fun^L(LMod Hk,LMod Hk) ≃ Hk-BMod-Hk(SpHA)`の必要な向きを得る。
一般型を作るかSpHA/Hkの特殊化から先に作るかは段0後の判断点。見込みは一般型の証明を含む。

### P5-09 Bと二つの作用、左加群としてのk^{tG}比較

文献：DAG Ex2.2.5。

```lean
def powerKernel : Bimodule Hk Hk SpHA
def powerKernelTensorIso : FunctorIso (tensorByBimodule powerKernel) (tatePower p)
def powerKernelLeftIso : VertexIso (forgetRightAction powerKernel)
  ((tate (Cp p)).obj (trivialAction unitD))
```

最初の同型は全関手版で、そのregular moduleでの評価を比較に固定する。
最後の同型からright actionをコピーしない。右作用は最初のEilenberg–Wattsの出力に保つ。

### P5-10 perfect上での同じ比較とshiftの指定

文献：DAG Ex2.2.5/Rem2.2.7、HAの安定性。

```lean
def powerComparisonShifted (n : ℤ) :
  VertexIso ((tatePower p).obj (shiftedUnit n)) ((tatePowerHat p).obj (shiftedUnit n))
theorem powerComparisonShifted_hom (n : ℤ) :
  hom(powerComparisonShifted n) = hom(component tatePowerComparison (shiftedUnit n))
```

境界との合成では両辺へ同じ[-1]を施す。
exact性からの同型を、元の比較射との一致なしに差し替えない。

## 6. P6：指定類、P⁰のcoherentな構成、Rem2.2.7

### P6-01 標準の忘却Vとπ/H

文献：HA7.1.2.13・4.2、DAG Con2.2.6の値域。

```lean
def V : D ⟶ SpHA := moduleComparison.hom ≫ forgetModule Hk
def piHomologyIso (n : ℤ) : hoMap V ⋙ spectrumPi n ≅ additiveCohomologyOnHo k (-n)
```

旧EMのπ/Hは比較の材料になる。標準のVのπ/Hの証明自体はmoduleComparisonとt構造に沿って行う。
旧EMへ後で接続するために、標準の入力複体を単体化するsource比較も保持する。
KSTへの同値なしに二つの関手を同じ値域のFunctorIsoと書かない。

### P6-02 k^{tC_p}のπ₁と指定された1

文献：DAG Con2.2.6、NS I.1（HMのTateコホモロジー）。

```lean
def unitTatePiOne : spectrumPi 1 (V.obj (tateCpOfUnit p)) ≃+
  AddSubgroup.ker (multiplicationBy p : k →+ k)
def unitTateClass : spectrumPi 1 (V.obj (tateCpOfUnit p))
theorem unitTateClass_value : unitTatePiOne unitTateClass = ⟨1, charP_zero⟩
```

trivial unitのorbitのπ₀=k、fixedのπ₀=k、normがp倍、fixedのπ₁=0をP4から計算する。
指定境界を用いるので、ここで周期解像度でTateを定義し直さずに必要な次数だけ計算可能。
全整数次数のTateコホモロジー比較はC-02へ分ける。

### P6-03 右k加群の射e

文献：DAG Con2.2.6、HAの自由右加群の随伴。

```lean
def eSpaceEquiv : QCatEquivalence
  (MapQ (RMod Hk SpHA) rightRegular (shiftRightModule (forgetLeft powerKernel) (-1)))
  (omegaInfinity (underlyingSpectrum (shiftBimodule powerKernel (-1))))
def chosenTateClassLift : Nonempty (PointRepresenting unitTateClass)
def tateClassRightMap (c : PointRepresenting unitTateClass) :
  Edge rightRegular (shiftRightModule (forgetLeft powerKernel) (-1))
```

π₁BをP5-09の左側の比較で計算し、右加群のregular unitからの写像空間で読む。
π₀の類1は写像空間のcomponentを指定する。選んだ代表の空間が可縮とは仮定しない。
構成は代表をパラメータにして先に作り、同じcomponentの選択はP⁰のホモトピーへ写ることを保持する。
左k線形なeは要求しない。k=F_pでも高次の右作用を通常のスカラー作用として省略しない。

### P6-04 eをテンソルしたSp値の全自然変換

文献：DAG Con2.2.6、HA4.8.4.1のkernelの構造。

```lean
def eTensor (c : PointRepresenting unitTateClass) :
  NatQ V (tatePower p ≫ shift D (-1) ≫ V)
```

各Mでの合成は`V M ≃ k⊗_k M → B[-1]⊗_k M ≃ V(T_p M[-1])`。
最初の射は右k加群の射eをテンソルした**スペクトルの射**。
ここをD(k)値NatQへ強めない。tensorの双関手性とP5の指定同型を用いて全M射に自然とする。

### P6-05 P⁰の合成そのもの

文献：DAG Rem2.2.4/Con2.2.6、Warning2.2.8/.10。

```lean
def W : AlgK ⟶ SpHA := forgetAlg ≫ V
def pZeroOfTateClass (c : PointRepresenting unitTateClass) : NatQ W W
```

同じcからの合成は次の一つに固定する。

```text
VA ≃ k⊗k A → B[-1]⊗k A ≃ V(T_p A[-1])
   → V(T̂_p A[-1]) → V((A⊗k p)hCp) → V(Sym^p_k A) → VA.
```

中の境界はP4-09のもの。後半はP2のΣ_p等変乗法と、群の包含に沿うorbitの射。
Sp値の関手準圏の辺として構成し、代表cを動かす写像空間の写像も持つ。
したがって同じunitTateClassを表すc同士はcoherentな自己変換としてホモトピックになる。
CAlgの自己射や、各nの群値NatTransの集まりへの置換はしない。

### P6-06 正次数の消滅

文献：DAG Rem2.2.7。

```lean
def representPiClass (A : Obj AlgK) (n : ℤ) :
  HomHo D (shiftedUnit n) (forgetAlg.obj A) ≃+ Pi n (W.obj A)
def pZeroFactorThroughOrbit (A) (n : ℤ) (eta : HomHo D (shiftedUnit n) (forgetAlg.obj A)) :
  SpecifiedFactorization (pZeroOfTateClass_onClass eta)
    (V.obj ((orbits (Cp p)).obj (powerCp p |>.obj (shiftedUnit n))))
theorem powerOrbitShift_pi_zero (n : ℤ) (hn : 0 < n) :
  IsZero (Pi n (V.obj ((orbits (Cp p)).obj (powerCp p |>.obj (shiftedUnit n)))))
theorem pZero_pos (A : Obj AlgK) (n : ℤ) (hn : 0 < n) :
  PiMap n (pZeroAt A) = 0
```

k[n]はperfectなのでP5-10を使える。p-foldの台はhomological次数pnに集中し、
orbitのconnectivityからn<pnなら該当群は零となる。
η:k[n]→Aは**加群の射**なので、CAlg上のP⁰の自然性だけをηへ適用しない。
P5の関手の比較とP6-04の加群入力の自然性で因数分解を作り、最後に乗法を適用する。
上のSpecifiedFactorizationは、π_nの代表Sphere[n]→V(k[n])を通る同じ合成が、
V(orbit(powerCp(k[n])))を経由するという射の等式とその全パラメータでの比較を表す。
該当π_nが零であることから全Sp-Hom(V(k[n]),−)が零だとする余分な推論は使わない。
周期解像度のbounded/flat仮定を一般Aへの追加入力にしない。

### P6-07 π₀でのFrobenius

文献：DAG Rem2.2.7、NS ExIV.1.2との関係は§9。

```lean
theorem unitClass_boundary_value : PiMap 0 (unitTateBoundaryAppliedToClass) = 1
theorem pZero_zero (A : Obj AlgK) (a : underlyingRing (pi0Alg.obj (mk A))) :
  pi0AlgEquiv (PiMap 0 (pZeroAt A) (pi0AlgEquiv.symm a)) = a ^ p
```

P6-02の1、P4の境界、単位上の同じ比較と、P2のp入力の乗法で計算する。
MayのD₀の計算で新しい演算の値を定義したり、未証明のMay=Lurieを使ったりしない。
NSのπ₀のTate値Frobeniusは標的がA/pであり、このπ₀Aの自己演算とは区別する。

## 7. 項目ごとの見込み・置き場所・実装順

文献に沿う新しい一般論は旧`EInfinity/PowerOperation`に足さない。
次の略記のパスは全て`SerrePositivity/InfinityCategories/`から。
既存の配置に合わせ、HAの節に対応する新設の下位ディレクトリを提案する。

- **K**：`Kerodon/LimitsAndColimits/KanExtensions/`。一般Kan随伴とgroupoid基底変換。
- **H**：`HA/Section6_1_6/`。Semiadditivity、段階別Norm、GroupOrbits、Tate。
- **I**：`Kerodon/LargeInfinityCategories/IndCompletionsOfInfinityCategories/`。一般のInd延長の法則。
- **E**：`HA/Section4_8_4/`。SpectralLinearity、ModuleBarResolution、EilenbergWatts。
- **P**：`HA/PowerOperations/`。DAGのTatePower、PerfectExtension、Kernel、PowerOperationZero・値の計算。
- **S**：`HA/Spectra/`（または既存の対応するHA§1.4の節）。NSの安定化・自然変換の普遍性。

KにはHTTと対応するKerodonの既知Tag、H/EにはHAの番号、PにはDAG XIII、
NSの構成にはNSの版と番号を付ける。Tagを確認していない新しい主張に架空のTagを付けない。
`Util/Citation.lean`の既知キーには現時点でDAGXIII/NSがないため、
`research/bibliography.json`と属性側への版の登録が先に必要。
今回そこは編集しない。登録後に`@[cite DAGXIII "2.2.6"]`等を使う提案であり、
未登録の属性が現在通ると主張しない。

見込みはdocstring/importと各項目の法則・証明分割を含む追加Lean行数。
**右欄は両端を正確に2倍**した値。既存の完成分を再実装する費用は入れない。
全線形関手圏・相対tensor等の構造をP3から受け取れない場合は表の前提が欠けるので、
その費用をこの数字に隠さず段0を再分割する。

| ID | 新規に要る部分・乗せる既存土台 | 場所 | 素の値 | 係数2の後 |
| --- | --- | --- | ---: | ---: |
| P4-01 | BG・作用準圏。nerve/groupoidとinternalHom | H/GroupActions | 800〜1,400 | 1,600〜2,800 |
| P4-02 | Kan随伴の全関手包装・指定錐。既存相対Kanの部品 | K/GroupoidKanAdjunctions | 1,200〜2,000 | 2,400〜4,000 |
| P4-03 | ∞のcanonical mate・fiberwise BC。既存comma比較 | K/GroupoidBeckChevalley | 1,600〜2,600 | 3,200〜5,200 |
| P4-04 | pointed norm・∞semiadditivity。既存preadditive_ho | H/Semiadditivity | 700〜1,200 | 1,400〜2,400 |
| P4-05 | finite-set norm・対角の逆・同じ有限双積 | H/FiniteSetNorm | 1,000〜1,700 | 2,000〜3,400 |
| P4-06 | finite-groupoid normの全自然構成 | H/FiniteGroupoidNorm | 1,400〜2,300 | 2,800〜4,600 |
| P4-07 | normの基底変換・合成の同じ指定変換の照合 | H/NormBaseChange | 800〜1,400 | 1,600〜2,800 |
| P4-08 | orbit/fixed全関手・hCでの和の検算 | H/GroupNorm | 500〜900 | 1,000〜1,800 |
| P4-09 | 関手圏の同じcofiberと境界。既存安定∞圏 | H/TateConstruction | 800〜1,400 | 1,600〜2,800 |
| P4-10 | native誘導作用の同値・Tate消滅 | H/InducedTateVanishing | 1,000〜1,700 | 2,000〜3,400 |
| P4-11 | orbit/fixed/Tateのexact性 | H/TateExact | 700〜1,200 | 1,400〜2,400 |
| P5-01 | P2のp入力とP4の合成。新しい模型定義は不要 | P/TatePower | 300〜500 | 600〜1,000 |
| P5-02 | equivariant p-cube・層のKan表示。既存mixed_freeを再利用 | P/TensorCubeFiltration | 1,800〜3,000 | 3,600〜6,000 |
| P5-03 | 全層からexactへの接続 | P/TatePowerExact | 700〜1,200 | 1,400〜2,400 |
| P5-04 | I03のperfect/compact/Indを同じ包含へ接続 | I/PerfectModuleInput | 500〜900 | 1,000〜1,800 |
| P5-05 | Lan・指定比較・全余極限保存 | P/TatePowerExtension | 1,200〜2,000 | 2,400〜4,000 |
| P5-06 | Sp作用に対するcanonical線形性、D(k)線形とはしない | E/SpectralLinearity | 1,000〜1,800 | 2,000〜3,600 |
| P5-07 | nativeな自由加群barと相対tensorの指定実現 | E/ModuleBarResolution | 2,000〜3,500 | 4,000〜7,000 |
| P5-08 | HA4.8.4.1の全関手圏の評価同値 | E/EilenbergWatts | 2,600〜4,200 | 5,200〜8,400 |
| P5-09 | Tpから双加群Bと右作用、左Tate比較を得る | P/TatePowerKernel | 900〜1,500 | 1,800〜3,000 |
| P5-10 | perfect・全shiftで元の比較射との一致 | P/TatePowerShift | 500〜900 | 1,000〜1,800 |
| P6-01 | 標準Vのπ/Hと指定源。P3の加群比較 | P/ModuleSpectrumForget | 1,600〜2,800 | 3,200〜5,600 |
| P6-02 | native Tateのπ1と1、同じnormと境界の値 | P/TateUnitClass | 900〜1,600 | 1,800〜3,200 |
| P6-03 | 右加群の自由随伴からe、代表のcomponent | P/TateClassRightModule | 900〜1,600 | 1,800〜3,200 |
| P6-04 | e⊗−のSp値の全自然性とBのkernel同型 | P/TateCoefficientTransformation | 700〜1,200 | 1,400〜2,400 |
| P6-05 | 原典の同じ合成をcoherentなP⁰に | P/PowerOperationZero | 700〜1,200 | 1,400〜2,400 |
| P6-06 | k[n]での因数分解とconnectivity、全整数の次数規約 | P/PowerOperationPositive | 1,600〜2,800 | 3,200〜5,600 |
| P6-07 | 指定類・境界・π0のp乗の計算 | P/PowerOperationZeroDegree | 1,400〜2,400 | 2,800〜4,800 |

| 段 | 素の計 | 係数2の計 |
| --- | ---: | ---: |
| P4 | 10,500〜17,800 | 21,000〜35,600 |
| P5 | 11,500〜19,500 | 23,000〜39,000 |
| P6 | 7,800〜13,600 | 15,600〜27,200 |
| 本線28項目 | 29,800〜50,900 | 59,600〜101,800 |

順序はP4-01〜03→P4-04〜08→P4-09〜11→P5-01〜05→P5-06〜10→P6-01〜07。
P6-01はI03の到着後ならP5の途中で準備できるが、今回並列実装の指示はしない。
規模が膨らみやすい所はP4-03/.07のmate、P5-02の同じ層の比較、P5-08の全関手圏、
P6-03/.04の右作用の向きである。係数2はこれらの存在問題を証明した値ではない。

## 8. 鎖の段階の部品・Mayの演算はどの比較に使うか

既存の模型は消さず、原典の構成を定義した**後**の計算・比較に使う。
比較を置く前に、一般の部分をOE-W1の手順で正しい場所へ移す。③-bの整理と同じファイルを
同時に動かさない。今回の段0では旧ファイルのimport・名前・文献属性も編集していない。

### 棚卸しの具体的な根拠

| 既存の宣言・場所 | 使える内容 | 供給したとは数えないもの |
| --- | --- | --- |
| Kerodon/KanExtensions/RelativeLeftRestrictionTheoremのkanRelativeLeftKanRestriction_trivialKanFibration等 | 相対Kanの制限と全関手の普遍性の部品 | 任意のfのf!・f*の随伴とcanonical BCそのもの |
| HA/StableInfinityCategories/HomotopyPreadditive.preadditive_ho | 同じhCの可換群・有限双積 | 全coherent normの構成 |
| HA/DerivedCategoryModels/DerivedCategories/DerivedCategory.derivedInfinityCategory_isPresentable、同じD(A)の安定性 | D(k)でBGの小(co)limitsが存在する土台 | 対称モノイダル∞構造やMod_Hkとの同値 |
| Kerodon/IndCompletions…/IndRestrictionEquivalence.indKappaContinuousRestriction_isQCatEquivalence | HTT5.3.5.10に対応する全Indの普遍性 | Tpのexact性と全余極限保存、双加群の右作用 |
| EInfinity/PowerOperation/CyclicTateComplex.cyclicTateComplex | 偶数ρ(g)−1、奇数normの周期係数の全複体 | native normのcofiberという定義 |
| CyclicOrbitModel.cyclicOrbitProjectiveResolution・cyclicOrbitTotalFunctor | **逆生成元**を用いる同じorbit模型とdirect-sum total | 一般の非有界図式のorbitとの指定比較 |
| CyclicInducedAcyclic.cyclicTateComplex_regularTensor_acyclic(_field) | 正則表現に対する鎖版の非輪状性 | P4-10の全nativeな誘導対象の消滅 |
| CyclicMixedOrbit.powerOperationCyclicPermutation_mixed_free | 素数pの混合語の安定化群が自明という有限組合せ | p-cubeの層のnativeな誘導表示 |
| TateCoefficientClass.powerOperationTateCoefficientClassと_value | 係数複体のH^{-1}の1 | Bの**右**Hk作用や右加群のe |
| CyclicCoefficientSeed.powerOperationCoefficientSeed | k線形な鎖のseed | 左線形性を要求しない原典のeの定義 |
| ProjectivePowerSpectrum.projectivePowerSpectrum等 | 限定した相対模型からKSTのSpへの実関手・source比較 | native Tateとの同型、一般SpでのTate関手 |
| MayResolution.mayResolutionComparison/_Homotopy、MayNormalization.mayNu | W→BE、指定生成元・ν・比較変更の法則 | LurieのcoherentなP⁰、HA流CAlgとの比較 |
| BarrattEccles/Theory/MayPowerOperation.barrattEcclesPowerOp0 | ho(CAlg_BE Fp)上の全整数の群値自然演算 | D81のCAlg(D(k))上のSp値自然変換 |
| SimplexCuts/Coalgebra等、CosimplicialNormalization | BEの全作用法則、正規化と同じ包含の指定比較 | HA流CAlgの定義やP⁰の定義。今回BFの続きは作らない |

### 比較の型（本線の定義の代用にはしない）

比較の略記`RepSource`はordinaryなFp表現を**零次複体**としてFun(BC_p,D(k))へ送る全関手。
`Q`は既存の複体のD(k)への源。一般のcoherent作用の厳密化をここで仮定していない。

```lean
-- C-01: 同じRepのbar解像度のorbit/fixedとcanonical normの全比較。
def orbitModelIso : FunctorIso (RepSource ≫ orbits Cp) (orbitChainSource ≫ Q)
def fixedModelIso : FunctorIso (RepSource ≫ fixed Cp) (fixedChainSource ≫ Q)
def normModelCompatibility : SpecifiedHomotopyOfNat
  (transportNativeNorm orbitModelIso fixedModelIso) chainNorm

-- C-02: normのcofiberとしての比較、全整数での係数計算。
def periodicTateIso : FunctorIso
  (RepSource ≫ tate Cp) (nerveMap cyclicTateModuleComplexFunctor ≫ Q)
theorem periodicTate_boundary : BoundaryCompatibility periodicTateIso normModelCompatibility

-- C-03: nativeな指定類が同じH^{-1}の1へ写る。eの右線形性の代用ではない。
theorem native_class_is_periodic_one :
  piOneUnderComparison unitTateClass = powerOperationTateCoefficientClass p k

-- C-04: finiteな色の分類をnativeなp-cubeの層の添字へ運ぶ。
def mixedOrbitIndexEquiv : Equiv (NativeMixedLayerOrbitIndex p) (ExistingMixedWordOrbitIndex p)

-- C-05: HA流CAlgとBEの比較を受け取った後だけの、π上の比較。
theorem pZero_may_comparison (E : QCatEquivalence AlgK CAlg_BE)
    (hE : SymmetricMonoidalAlgebraPresentationCompatibility E) (n : ℤ) :
  conjugatePiNat E (PiNat n pZeroOfTateClass) = mayPrimeFieldPowerZero p n

-- C-06: 値域の比較を与えた後のVと既存EM。単なるπ/Hの一致からは作らない。
def oldEMComparison (s : QCatEquivalence SpHA KST.Spectra.Sp) :
  FunctorIso (V ≫ s.hom) (eilenbergMacLaneDerived k)
```

C-01/C-02はまずordinaryなRepに限る。周期Homのproduct totalとorbitのsum total、
逆巡回生成元と正巡回生成元、Tate境界の符号、非有界化はそれぞれ照合が要る。
既存のbounded/flatの弱同値保存から全非有界入力への一般化を無料としない。
C-03はP6-02の指定1の検算にもなるが、P6はnativeなLESで値を計算できるため必須ではない。
C-04の既存の有限組合せはP5-02内でも再利用する。下表の費用は別の独立した比較を公表する場合だけ。
C-05は同じ全整数n、同じν・指定生成元・同じコホモロジー比較を保持する。
MayにはcoherentなSp値の出力がないので、「二つのSp値自己変換が同じ」という型にはしない。
C-06のsの建設は担当外のSpの提示比較で、下表の関手の接続費とは別。

| 比較 | 素の値 | 係数2の後 | 本線への算入 |
| --- | ---: | ---: | --- |
| C-01 | 1,200〜2,200 | 2,400〜4,400 | 任意。定義後 |
| C-02 | 1,800〜3,000 | 3,600〜6,000 | 任意。全周期計算が必要なとき |
| C-03 | 1,000〜1,800 | 2,000〜3,600 | 任意。seedはeの代用にしない |
| C-04 | 500〜900 | 1,000〜1,800 | 任意の独立比較。本線の組合せ利用はP5-02で計上済み |
| C-05 | 1,800〜3,200 | 3,600〜6,400 | HA↔BE比較を受領した場合の追加 |
| C-06 | 2,500〜4,500 | 5,000〜9,000 | Spの提示比較を受領した場合の追加 |
| **追加として全六比較を公表する場合** | **8,800〜15,600** | **17,600〜31,200** | **本線とは別。外部比較の建設費を除く** |

既存の10,216行・Mayの30,586行を本線から丸ごと引く計算はしない。
それらは原典のnativeなnorm・Tate・双加群をまだ定義しておらず、表では使える計算だけを控除した。
反対に全部を再実装する見込みでもない。

### OE-W1と衝突させない移動の候補

- cyclicTateComplexと周期解像度：`HomologicalAlgebra/GroupCohomology/Cyclic/`等、純粋な鎖の計算の場所。
- mixed_free：`HA/PowerOperations/Combinatorics/`または一般の有限群作用の組合せの場所。
- EMの一般部品：HAの加群・スペクトル比較の模型側。`EInfinity/PowerOperation`の名前のまま原典定義の依存にしない。
- MayのBE作用と群値演算：模型側の比較として旧場所を保持し得る。D81本体のCAlgの定義とは分ける。

具体的な移動表、公開名のalias、直接importerの追従・監査は③-b/OE-W1と調整してから。
今回の報告に挙げたことを移動の実行許可とは読まない。

## 9. D(F_p)でDAG XIIIを追う道と、SpでNSを追う道

### 9.1 基準コミットのSpの状態

`KST/Spectra/CoherentNerve`のSpはBF型Ωスペクトルのcoherent nerve。
`sp_quasicategory`、零対象・有限極限、厳密作用からの
`homotopyFixedPointsInfinityCone_isLimit`は実在する。
しかしD3TailStabilityの`sp_isStable`は`NativeLoopComparison`を引数に持つ。
D3ComparisonOutputの同名は型であり、本体が供給されたという定理ではない。

KSTには一般のnativeなorbit/norm/Tate、smash積、Spのpresentabilityの供給を確認できない。
`FilteredOmegaSpectrum`の段ごとの構成を、任意のcoherentな余極限の普遍性として使わない。
`Spectra/`にある1圏の対称スペクトルのsmash積・モデル構造とは未接続で、
その利用に`[ModelCategory SSet]`を足す経路は採らない。
古いKSTの条件付き安定性をglobal instanceにして報告することもしない。

### 9.2 NSの道で追加になる型つきの五項目

以下の`Sp`は**標準の安定presentable対称モノイダルSp**であり、
現在のKSTのSpへ無条件に代入できるという意味ではない。

```lean
-- N-01 / NS III.1.2, HA 1.4.2.23 + Yoneda
-- Fにはexact性だけ。colimit保存に勝手に強めない。
def exactNatAtSphere (F : Sp ⟶ Sp) (hF : IsExactFunctor F) :
  QCatEquivalence (MapQ (FunQ Sp Sp) idVertex (functorVertex F))
    (MapQ Sp sphere (F.obj sphere))

-- N-02 / NS III.1.4: NSHat=X↦(X^⊗p)^tCp（DAGのTpとは別）。
def tateDiagonal : NatQ (𝟙 Sp) NSHat
theorem tateDiagonal_atSphere :
  exactNatAtSphere.image tateDiagonal =
    hom(sphere_to_trivial_fixed ≫ fixed_to_tate)

-- N-03 / NS I.3.1: NSのFrobeniusをE∞射として扱う場合。
def tateLaxMonoidal : LaxSymmetricMonoidalStructure (tate Cp)
theorem tateLax_unique : IsContractible (CompatibleTateLaxStructures fixed_to_tate)

-- N-04 / NS IV.1.1: scalar p-cycle multiplicationとTate対角の合成。
def tateValuedFrobenius : NatQ (forgetCAlgSp) (tateOfTrivialAlgebra)
-- E∞射へのrefinementはN-03を用いる。Sp値だけならその部分は不要。

-- N-05: 相対係数のP⁰をNS流の普遍性で取り出す場合の追加の橋。
-- NS III.1.10後のSp値の議論、HA 1.4.2.23 + stable Yoneda。
def exactNatAtModuleUnit (F : D ⟶ Sp) (hF : IsExactFunctor F) :
  QCatEquivalence (MapQ (FunQ D Sp) (functorVertex V) (functorVertex F))
    (MapQ Sp sphere (F.obj unitD))
```

N-02の点は球→球のhomotopy **fixed**→Tateである。
球→homotopy orbit→Tateの合成ではない（normの後のcofiberへの合成を使うと零になる）。
この点は`research/p0-lurie/README.md` §1.2の該当表記への訂正提案でもある。

N-05をF=V∘T̂_p[-1]へ適用し、π₁k^{tG}の同じ点を選べば、
Sp値のV→V∘T̂_p[-1]を得る候補がある。その後は同じ境界と乗法でP⁰へ進む。
これはD(k)値のid→T̂_pを作る主張ではなく、NS III.1.10のno-goと混同しない。
ただし、その候補を**DAGのTp・右加群eによる定義と同じ**とするには、
両方の係数変換のunitでの値と、この全写像空間の同値による比較を証明する必要がある。
その普遍性の基盤も現在は未供給。採用済みの短縮経路とはしない。

| NSの追加 | 素の値 | 係数2の後 | 注意 |
| --- | ---: | ---: | --- |
| N-01 | 1,500〜2,500 | 3,000〜5,000 | 標準SpとHA1.4の基盤を受領する前提 |
| N-02 | 300〜500 | 600〜1,000 | N-01とP4の後 |
| N-03 | 2,500〜4,500 | 5,000〜9,000 | 全NSのE∞射としてのFrobeniusを追うなら必要 |
| N-04 | 1,000〜1,800 | 2,000〜3,600 | 同じ乗法と球の対角。P⁰そのものではない |
| N-05 | 1,500〜2,800 | 3,000〜5,600 | 相対係数の橋。新しい特徴づけとして採るかは未決 |
| **計** | **6,800〜12,100** | **13,600〜24,200** | **Spの建設・P1〜P3は外部費用** |

### 9.3 同じ終点までの比較

| 比較点 | D(F_p)・DAGの順 | Sp・NSの順 |
| --- | --- | --- |
| 始められる土台 | D(k)の安定性・presentabilityは無条件。P4はそのKan延長から開始 | KSTのSpをそのままでは安定・全BG(co)limits・smashに使えない |
| 対称性 | P1〜P3からD(k)^⊗・CAlg・p入力を受領 | さらに標準Sp^⊗と球・自由安定化の普遍性が必要 |
| norm/Tate | P4の一般安定圏での構成をD(k)へ | 同じP4を標準Spへ。strict KST fixedだけでは不足 |
| exact性 | P5-01〜03。mixed orbitの既存の組合せを使用 | 同じcubeの証明。NS III.1.1 |
| 対角・係数 | perfectからのTp、spectral Eilenberg–Watts、右Hk加群のe | NSの球のTate対角は次数0。相対係数と次数1の類への橋N-05がなお必要 |
| P⁰の忠実さ | DAG2.2.6の同じ合成を直接定義できる | NSのφ_Rと同一視できない。DAGとの比較または特徴づけを証明して採る判断が必要 |
| 既存V | 同じD(k)を源とするπ/H比較・模型として再利用可能。値域比較は別 | 現在のVはKSTのSp値。標準Spの忘却との提示比較がさらに必要 |
| 主な未供給 | P1〜P3、spectral action、HA4.8.4.1 | 標準Spの建設/比較、P1〜P3、N-01/N-05の全普遍性 |

段0の見込みの比較は、担当外のSp建設費を0と置かず、次のように条件を揃える。

- **DAG本線**：P1〜P3とI03の標準spectral actionを受領した後、
  追加29,800〜50,900行（×2で59,600〜101,800）。28項目の内訳は§7。
- **NS＋相対係数の特徴づけ案**：同じP4、P5-01〜03、N-01〜05、P6-01/.02/.06/.07を数えると、
  追加25,600〜44,200行（×2で51,200〜88,400）。ただしN-05による
  新しい特徴づけとDAGの定義の比較を採用する判断、標準Spの基盤が必要。
  N-03のE∞値へのrefinementを不要と決めるなら、その束は別途除けるが自己判断では除かない。
- **DAGの文字通りのTpもNSと並べて両方実装する場合**は、NS案から省いたP5-04〜10等が再び要る。
  一つのTate対角だけ作ればDAGの全定義が既に存在する、として差し引かない。

後者の行数が小さいことだけでNSを推奨することはできない。
担当外の標準Spの安定化・smash・KSTとの提示比較は、今回新たに型一覧を作って見積もった対象ではなく、
**未見積の外部依存**である。既存KSTの未供給のNativeLoopComparison一件の型だけを見て
その外部依存を数百行と仮置きしない。
D(k)経路にもI03のspectral actionが要るので、「Spの不足は全て回避」とは書かない。

**推奨**：まずP4の一般論をD(k)に載せる。P5の前に⑤dからI03の供給範囲を確定し、
原典のTp・kernel・右作用を辿るDAG本線を基本とする。
N-05の特徴づけはNS側の比較・将来の短縮案として紙で残す。
今回のD81の方針を、旧BEの局所化を定義に戻す判断には読み替えない。

## 10. 段0の受け渡し・未決点・検証記録

1. ⑤dからI01〜I03を受け取る。spectral action、linear functorの準圏、双加群の準圏と
   relative tensorがP3のどの段に属するかを特に確認する。型を書いたことを供給済みと数えない。
2. P4のKan随伴とBCは一般のKerodonの部品であり、OE-W1/③-bの移動対象と所有を確認してから使う。
   同じファイルの移動や公開名の改名を⑤aだけで進めない。
3. 文献属性のDAGXIII/NSの版の登録を先に行う。HAの番号は2017-09-18版、NSはv2を基準にする。
4. 係数は最初F_p、有限群はP4で一般の有限群を許し、P5以後はC_p。
   一般k・全NSの乗法性・BSの完備化への応用を同じ上端に紛れ込ませない。
5. 任意の比較C-01〜06を本線と一緒に行うかは未決。Mayとの比較は定義後の定理であり、
   P⁰の定義やRem2.2.7をMayに置き換える許可ではない。
6. P4/P5/P6の分担・実装順・外枠はこの紙の後に決める。行数の係数2の表を自己承認の外枠にしない。

今回行った検証は、基準コミット、指定四資料、対応する本体宣言の型、原典の番号と仮定、
p0-mapの59項目、28項目の表と係数2の加算の照合、`git diff --check`。
**Leanの追加・編集・型検査・lake build・監査・鍵の取得は一切なし。**
新規ファイルはこのMarkdown一つだけ。mainや⑤dの作業木、研究資料、既存Mayの作業木は変更していない。
報告をコミットしたら停止し、ユーザーと調整役の段0の判断を待つ。

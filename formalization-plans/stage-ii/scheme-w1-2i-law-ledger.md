# SC-W1 2i：追加する照合・合成則の台帳

2026-11-17。指示書末尾の11-17夕の事前承認（新しい数学でない／既存の署名・仮定を変えない／一本の補正後上端800行以内／mainの既存本体を変えない）による追加。元の66署名の型は保持する。

## L01：arcBaseChangeTransIso

```lean
def arcBaseChangeTransIso {A B T S : Type u}
    [CommRing A] [CommRing B] [CommRing T] [CommRing S]
    (f : A →+* B) (g : A →+* T) (h : T →+* S) (k : A →+* S)
    (hk : h.comp g = k) :
    Arrow.mk (CommRingCat.ofHom (arcBaseChangeHom f k)) ≅
      Arrow.mk (CommRingCat.ofHom (arcBaseChangeHom (arcBaseChangeHom f g) h))
```

- 理由：U07で検証した既存のtensor関手と押し出しの合成則を、区間の制限O08と正次数の照合P05でも使うため、同じ指定Arrow同型としてまとめる。新しい幾何や降下の仮定を足さない。
- 依存：U01と、上記の既存二宣言。置き場所：SerrePositivity/AlgebraicGeometry/ArcRouteB/BaseChangeComparison.lean、名前空間SerrePositivity.AlgebraicGeometry.ArcRouteB。
- 素30〜90行、係数2：60〜180行。上端180≤800。既存main本体の変更なし。U07の検証済み候補の本体も変更しない。
- hkは元の係数射の可換三角形。Arrowの同型を先に作り、その後で増大conerveへ送る。選ばれたČech余極限の内部を書き換えず、元の係数・脚を保つ。
- 原典：形式化のための合成法則であり独立したBM18の新定理ではない。用途はBM18 Prop4.8の区間の制限と、B1の正次数の係数への移送。
- 元のO08・P05の署名・仮定を変えず、依存先だけL01を追加した。元の66署名と合わせ67頂点・112辺、DFSで循環0を確認。
- 検証済み13署名・実測160行だけを確定分とし、残りに係数2と登録予備を保った完成見込み **3,732〜8,700行**。外枠9,000行以内。現在の5モジュールは対象ビルドが通り監査待ちだが、この計算ではまだ完了分へ数えていない。

一覧：済み13／全体67（うち追加1）。この台帳の時点ではL01のLeanは未着手。指示書の条件を満たすので、記録後は承認を待たず実装・対象検証へ進む。


## L01の検証（03338bc40）

記録した型のまま実装・対象ビルド・直接importer・所有監査を完了。本体49行、登録2行、所有5宣言・標準三公理のみ。既存main本体の変更なし。一覧：追加法則の済み1／全体1、2i全体の済み49／全体67（うち追加1）。


## L02：arcBaseChangeArrowIso（記録後に着手）

```lean
def arcBaseChangeArrowIso {A : Type u} [CommRing A]
    (B : Under (CommRingCat.of A)) (D : Type u) [CommRing D] [Algebra A D] :
    Arrow.mk (CommRingCat.ofHom (arcBaseChangeHom B.hom.hom (algebraMap A D))) ≅
      Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of D)).obj B).hom
```

- 用途：O06の普遍貼り合わせとP01の普遍超積で、同じ係数の環射の底変換をB1のUnderの底変換へ渡す。選ばれたconerveの内部で代数構造を書き換えず、Arrowの照合を先に行う。
- 依存：U01、既存のtoAlgebra_algebraMap（Mathlib/Algebra/Algebra/Defs.lean:262）とCommRingCat.tensorProd（Algebra/Category/Ring/Under/Basic.lean:127）。置き場所：ArcRouteB/BaseChangeArrowComparison.lean。
- 素20〜70行、係数2：40〜140行、上端140≤800。新数学なし、元の署名・仮定・既存main本体の変更なし。元の66署名にL01と合わせ68署名。
- O06・P01の型は保持し、依存先だけL02を足した。DFSで68頂点・115辺・循環0を確認。原典上は独立した主張ではなく、形式化のための同じ構造射の照合。
- 検証済み53署名・実測1,422行を確定分にし、残りの係数2と登録予備を含む完成見込みは2,862〜4,868行。9,000行以内。記録後は事前承認に従い止まらず実装へ。

一覧：済み53／全体68（うち追加2）。この台帳の時点ではL02のLeanは未着手。


## L03：既存の完全係数の構成の抽出（記録後に着手）

```lean
theorem intervalCoefficient_primeQuotient_perfect (p : ℕ) [Fact p.Prime] {V : Type u}
    [CommRing V] [IsDomain V] [ValuationRing V] [PerfectRing V p]
    (hp : (p : V) = 0) (a : PrimeSpectrum V) :
    PerfectRing (V ⧸ a.asIdeal) p
```

- 依存する既存の構成：Arc.perfectRing_primeResidue @ SerrePositivity/BhattScholze/Perfectoidization/Arc/Milnor/ArcMilnorTensor.lean:92（証明内の同じ商のPerfectRing）、perfectRing_interval @ SerrePositivity/CommutativeAlgebra/ValuationInterval/Basic.lean:128。
- 筋：既存の証明内で構成済みの、商への根の移送と既約な商のreduced性を、そのまま名前付きの係数法則として抽出する。
- 元のO06の型・仮定は保持し、同じ局所化・素イデアル商の係数を扱う。新しい幾何・数学の仮定・Noether帰着はない。mainの既存本体は変更せず、新規のIntervalCoefficientPerfect.leanに置く。
- 素25〜80行、係数2：50〜160行。上端160≤800。既存の係数移送の証明の分割として、指示書の事前承認に従って記録後に進める。


## L04：既存の完全係数の構成の抽出（記録後に着手）

```lean
theorem intervalCoefficient_primeLocalization_perfect (p : ℕ) [Fact p.Prime] {V : Type u}
    [CommRing V] [IsDomain V] [ValuationRing V] [PerfectRing V p]
    (hp : (p : V) = 0) (a : PrimeSpectrum V) :
    PerfectRing (Localization.AtPrime a.asIdeal) p
```

- 依存する既存の構成：perfectRing_interval @ SerrePositivity/CommutativeAlgebra/ValuationInterval/Basic.lean:128–151（同じ局所化の根と分母の構成）。
- 筋：既存の区間環の証明の局所化の構成を、下端の商を取らない同じ係数で使う。分母の根が同じ素イデアルの外にあるという既存の計算を保つ。
- 元のO06の型・仮定は保持し、同じ局所化・素イデアル商の係数を扱う。新しい幾何・数学の仮定・Noether帰着はない。mainの既存本体は変更せず、新規のIntervalCoefficientPerfect.leanに置く。
- 素25〜80行、係数2：50〜160行。上端160≤800。既存の係数移送の証明の分割として、指示書の事前承認に従って記録後に進める。


追加後は70頂点・117辺、DFSで循環0。検証済み53署名・実測1,422行を確定分とした補正後の完成見込みは2,962〜5,188行で、外枠9,000行以内。一覧：済み53／全体70（うち追加4）。


## L05：moduleCechの同じ係数検出の分割（記録後に着手）

```lean
theorem cechExact_of_overlapTensor_coefficients (p : ℕ) [Fact p.Prime]
    {V T : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing T] [Algebra V T] [PerfectRing V p] [PerfectRing T p]
    (B : Under (CommRingCat.of T)) [PerfectRing B.right p] (hp : (p : V) = 0)
    {a b : PrimeSpectrum V} (h : a ≤ b)
    (hl : Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of T)
      (CommRingCat.of (T ⊗[V] Localization.AtPrime b.asIdeal))).obj B).hom))
    (hq : Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of T)
      (CommRingCat.of (T ⊗[V] (V ⧸ a.asIdeal)))).obj B).hom))
    (hr : Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of T)
      (CommRingCat.of (T ⊗[V] ValuationIntervalRing h))).obj B).hom)) :
    Cech.IsCechExact (Arrow.mk B.hom)
```

- 位置：O06で予定した、O05のT上の短完全列をmoduleCechへ適用する段を名前付きで分ける。O09の和の上の係数でも再利用する。原典はBM18 Prop4.8(5)に対応する既存の構成の適用で、別の数学を供給しない。
- 依存：O05・U09、既存のArc.acyclic_of_tensorShortExact・moduleCech_tor_subsingleton・cechExact_baseChange_iff_tensorCochain・tensorCochain_unitIso。配置：ArcRouteB/OverlapCoefficientDetection.lean。
- 素50〜120行、係数2：100〜240行、上端240≤800。元のO06・O09の型・仮定を変えず、mainの既存本体も変えない。Tの平坦性を要求しない。対象は同じ列と同じ複体のまま。
- 元の66署名と照合・分割5本で71署名。DFSで71頂点・121辺、循環0。確定分53署名・1,422行だけで計算した完成見込みは3,062〜5,428行、9,000行以内。

一覧：済み53／全体71（うち追加5）。記録後は事前承認に従い止まらず実装する。


### L01〜L05の検証結果（11-17夜）

L01は03338bc40、L02〜L04は47de0d6db、L05はfddd1a4cdで同じ記録済みの型のまま検証・コミット済み。各束の対象ビルドと所有宣言の公理監査が成功（標準三公理のみ）。元の66署名の型・仮定、mainにある既存の本体は変更していない。一覧：済み65／全体71（うち追加5）。


### 停止点2i

L01〜L05を含む71署名全て検証済み。元66署名の完全な型の一致を再照合し、既存mainの数学の本体は変更していない。最終の正本の型チェック・所有宣言監査はscheme-w1-2i-verify.lean、結果はscheme-w1-2i-verification.json。一覧：済み71／全体71（うち追加5）。

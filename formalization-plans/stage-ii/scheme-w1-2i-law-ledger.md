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

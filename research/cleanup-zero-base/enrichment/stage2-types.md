# EN-W1 段2　厳密な豊穣化の型案

main `6fc90a31e` を取り込んだ `e991924fd` と固定 Mathlib `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6` が基準。以下の `TensorCotensor` と `EnrichedRepresentability` は現在の `SerrePositivity.Enriched` の型を指す。新設する構成は `CategoryTheory` の下に置く。型ブロックは証明を省いたヘッダーで、各節の `variable` は同じ節のブロックで共用する。A1 の自己豊穣化は Mathlib の `MonoidalClosed.enrichedOrdinaryCategorySelf` を使う。右随伴の比較、関手輸送、通常の圏を取り出す操作は既存のものを使う。

## A3・B3　作用から作る `OfAction.lean`

豊穣化だけには `r` 一つを受け取り、余テンソルを選ぶ `q` は B3 で加える。作用の結合子は `T(P ⊗ Q) ≅ T Q ⋙ T P`。従って評価して得る合成では `R(Y,Z)` が左因子になり、Mathlib の `eComp` の順に揃えるときは基底の組紐を使う。単位・結合・通常射の法則は `MonoidalLeftAction` の自然性、左右単位・五角形、随伴の転置の単射性から示す。閉性はこの段階では不要。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.BraidedCategory
open SerrePositivity.Enriched
universe u v u' v'
variable {V : Type u} {M : Type u'} [Category.{v} V] [Category.{v'} M]
  [MonoidalCategory V] [BraidedCategory V] [MonoidalLeftAction V M]
local notation "H" => MonoidalLeftAction.curriedAction V M
local notation "T" => Functor.obj H
variable {R : Mᵒᵖ ⥤ M ⥤ V} {Q : Vᵒᵖ ⥤ M ⥤ M}
local notation "R₁" => fun X : M => R.obj (op X)
local notation "homV" => fun X Y : M => Functor.obj (R.obj (op X)) Y

def actionAssoc (P Q : V) : T (P ⊗ Q) ≅ T Q ⋙ T P
def actionEvaluation (r : (H).flip ⊣₂ R) (X Y : M) :
    (T (homV X Y)).obj X ⟶ Y
def actionUnit (r : (H).flip ⊣₂ R) (X : M) : 𝟙_ V ⟶ homV X X
def actionComposition (r : (H).flip ⊣₂ R) (X Y Z : M) :
    homV X Y ⊗ homV Y Z ⟶ homV X Z
def actionHomEquiv (r : (H).flip ⊣₂ R) (X Y : M) :
    (X ⟶ Y) ≃ (𝟙_ V ⟶ homV X Y)
lemma actionEvaluation_eq (r : (H).flip ⊣₂ R) (X Y : M) :
    actionEvaluation r X Y = (r.adj X).counit.app Y
lemma actionUnit_eq (r : (H).flip ⊣₂ R) (X : M) :
    actionUnit r X = (r.adj X).homEquiv (𝟙_ V) X
      ((MonoidalLeftAction.actionUnitNatIso V M).hom.app X)
lemma actionComposition_eq (r : (H).flip ⊣₂ R) (X Y Z : M) :
    actionComposition r X Y Z =
      (r.adj X).homEquiv (homV X Y ⊗ homV Y Z) Z
        (((H).map (β_ (homV X Y) (homV Y Z)).hom).app X ≫
          ((actionAssoc (M := M) (homV Y Z) (homV X Y)).hom.app X) ≫
          (T (homV Y Z)).map (actionEvaluation r X Y) ≫ actionEvaluation r Y Z)
lemma actionHomEquiv_apply (r : (H).flip ⊣₂ R) {X Y : M} (f : X ⟶ Y) :
    actionHomEquiv r X Y f = (r.adj X).homEquiv (𝟙_ V) Y
      (((MonoidalLeftAction.actionUnitNatIso V M).hom.app X) ≫ f)
@[instance_reducible] def ofAction (r : (H).flip ⊣₂ R) :
    EnrichedOrdinaryCategory V M
def ofActionHomIso (r : (H).flip ⊣₂ R) :
    let : EnrichedOrdinaryCategory V M := ofAction r
    eHomFunctor V M ≅ R
lemma ofActionHomIso_hom_app (r : (H).flip ⊣₂ R) (X Y : M) :
    let : EnrichedOrdinaryCategory V M := ofAction r
    ((ofActionHomIso r).hom.app (op X)).app Y = 𝟙 (homV X Y)
def ofActionTensorCotensor (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) :
    let : EnrichedOrdinaryCategory V M := ofAction r
    TensorCotensor V M
lemma ofAction_tensorHomEquiv (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q)
    (P : V) (X Y : M) (f : (T P).obj X ⟶ Y) :
    let : EnrichedOrdinaryCategory V M := ofAction r
    (ofActionTensorCotensor r q).tensorHomEquiv P X Y f = (r.adj X).homEquiv P Y f
```

`actionAssoc` は Mathlib の三変数同型の二つの成分。 `actionEvaluation` は `r.adj X` の余単位、`actionUnit` は `actionUnitNatIso.hom.app X` の転置、`actionHomEquiv` は同じ単位子による前合成と `r.adj X` の転置の合成。 `actionComposition` は `β_{R(X,Y),R(Y,Z)}`、作用結合子、`R(Y,Z)` による左作用が写す評価 $X\to Y$、評価 $Y\to Z$ を順に合成して転置する。構造の Hom、単位、合成、通常射との同値はこれらの値に定義的に還元する。

`ofActionHomIso` の対象成分は恒等。終変数での自然性は評価の後合成、原変数では `r.homEquiv_naturality_one` を使う。B3 の `tensor=H`、`cotensor=Q` と `tensorCotensor=q` は選んだデータそのまま。 `tensorHom` は `ParametrizedAdjunctionTransport.right` で `r` を `ofActionHomIso.symm` に沿って輸送する。上の転置の式と `unitMap_comp` により、B3 の `unitIso` が元の作用単位子と成分ごとに一致する。

既存 `RepresentedMapping` の法則は、一般の左作用の仮定から呼ぶ。評価後の補題、whiskering、右随伴の比較の中間命題をそれぞれ移すか局所化する。個別の63件の予定は末尾の表。A3 の型には基底変更（自由対象、評価関手、モデル圏）を持ち込まない。

## B1　テンソル・余テンソルの豊穣表現 `TensorCotensor.lean`

`TensorCotensor` の二つの通常随伴だけでは結合の同型は従わない。反例は閉対称モノイダルな三元鎖 $0<a<1$（単位 $1$、$a\otimes a=0$、ゼロは吸収元）と、通常圏としての二元鎖。豊穣 Hom は順序が成り立つとき (1)、それ以外は (0) とする。テンソルは係数 (0) で定値の最小元、それ以外で恒等。余テンソルは係数 (0) で定値の最大元、それ以外で恒等。二つの通常 Hom の対比そのものは、この設定で三変数に自然な随伴を与える。$P=a$、$X$ を最大元、$Y$ を最小元とすると、`Map(T P X,Y)` と `Map(X,Q P Y)` は $0$、内部 Hom $[a,0]$ は $a$。係数や通常点の欄を埋める以前に、二つの対象同型が存在しない。

別の入力として、係数二変数と対象に自然な作用結合の同型を取り、単位には今ある `S.unitIso` を使用する。必要なのは、この単位との左右の整合。右随伴比較と点の計算に五角形は使わない。実際に作用を持つ場合は A3・B2 の結合子を渡せる。既存の `TensorCotensor`、`EnrichedRepresentability` の欄はそのままにできる。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor Opposite
open SerrePositivity.Enriched
universe u v u' v'
variable {V : Type u} {M : Type u'} [Category.{v} V] [Category.{v'} M]
  [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
  [EnrichedOrdinaryCategory V M]
variable (S : TensorCotensor V M)
local notation "T" => S.tensor

structure TensorAssociativity where
  iso : bifunctorComp₁₂ (curriedTensor V) T ≅ bifunctorComp₂₃ T T
  leftUnit (P : V) (X : M) :
    (((iso.hom.app (𝟙_ V)).app P).app X) ≫ (S.unitIso.hom.app (((T).obj P).obj X)) =
      ((T).map (λ_ P).hom).app X
  rightUnit (P : V) (X : M) :
    (((iso.hom.app P).app (𝟙_ V)).app X) ≫ ((T).obj P).map (S.unitIso.hom.app X) =
      ((T).map (ρ_ P).hom).app X

def tensorHomIsoOfAssoc (a : TensorAssociativity S) (P : V) :
    tensorEnrichedHom S P ≅ powerHom (C := M) P
def cotensorHomIsoOfAssoc (a : TensorAssociativity S) (P : V) :
    cotensorEnrichedHom S P ≅ powerHom (C := M) P

lemma tensorHomIsoOfAssoc_parameter (a : TensorAssociativity S)
    {P P' : V} (p : P ⟶ P') (X Y : M) :
    eHomWhiskerRight V (((T).map p).app X) Y ≫
        ((tensorHomIsoOfAssoc S a P).hom.app (op X)).app Y =
      ((tensorHomIsoOfAssoc S a P').hom.app (op X)).app Y ≫
        (MonoidalClosed.pre p).app (X ⟶[V] Y)
lemma cotensorHomIsoOfAssoc_parameter (a : TensorAssociativity S)
    {P P' : V} (p : P ⟶ P') (X Y : M) :
    eHomWhiskerLeft V X ((S.cotensor.map p.op).app Y) ≫
        ((cotensorHomIsoOfAssoc S a P).hom.app (op X)).app Y =
      ((cotensorHomIsoOfAssoc S a P').hom.app (op X)).app Y ≫
        (MonoidalClosed.pre p).app (X ⟶[V] Y)
lemma tensorHomIsoOfAssoc_points (a : TensorAssociativity S)
    (P : V) (X Y : M) (f : ((T).obj P).obj X ⟶ Y) :
    (MonoidalClosed.curryHomEquiv' (X := P) (Y := X ⟶[V] Y)).symm
        (eHomEquiv V f ≫ ((tensorHomIsoOfAssoc S a P).hom.app (op X)).app Y) =
      S.tensorHomEquiv P X Y f
lemma cotensorHomIsoOfAssoc_points (a : TensorAssociativity S)
    (P : V) (X Y : M) (f : X ⟶ (S.cotensor.obj (op P)).obj Y) :
    (MonoidalClosed.curryHomEquiv' (X := P) (Y := X ⟶[V] Y)).symm
        (eHomEquiv V f ≫ ((cotensorHomIsoOfAssoc S a P).hom.app (op X)).app Y) =
      S.cotensorHomEquiv P X Y f

def ofTensorCotensor (a : TensorAssociativity S) : EnrichedRepresentability S
```

テンソル側は `tensorRight P ⋙ T.flip.obj X` と `T.flip.obj (((T).obj P).obj X)`、余テンソル側は `tensorLeft P ⋙ T.flip.obj X` と `T.flip.obj X ⋙ (T).obj P` を結合子で比較する。テンソル側の `tensorRight P` は組紐で `tensorLeft P` に移して閉随伴を使う。右随伴を `ActionComparisonAdjunction.rightIso` で比較すれば、任意のパラメータでの転置が揃う。係数自然性は `ParametrizedAdjunction` の自然性、閉構造の `pre`、結合子の二係数の自然性から示し、原変数の自然性も同じ右随伴比較で束ねる。点の二式は一般のパラメータを単位に取り、左右単位の整合と `unitMap_comp` で示す。余テンソル側は `q` の転置の逆を先に取る。 `ofTensorCotensor` は上の二つの実同型と四つの比較式をフィールドに入れる。

## A2・B2　モノイダル随伴による基底変更

### `BaseChange.lean`

Mathlib の `TransportEnrichment.enrichedOrdinaryCategory` は型別名 `TransportEnrichment G W` を受け手とし、Hom 点 `𝟙 ⟶ A` の自然な全単射が `ε G ≫ G.map -` であることを要求する。元の通常圏の対象型のまま使う非大域の定義は現行 `TransportOrdinaryEnrichment.ordinaryCategory` と同じ形で保つ。以下では通常圏と単位点を揃えた後の `eHomFunctor` を自然同型で比較する。基底を変えたことで既存のカテゴリーの instance を選び直さない。固定版では型別名が定義的に透過で、`TransportEnrichment.enrichedOrdinaryCategory M G e he` を `EnrichedOrdinaryCategory V M` として受けられることを照合した。公開する型は元の対象型と通常圏を固定し、Mathlib の定義をその中で使える。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
universe u v u' v' u'' v''
variable {U : Type u} {V : Type u'} {M : Type u''}
  [Category.{v} U] [Category.{v'} V] [Category.{v''} M]
  [MonoidalCategory U] [MonoidalCategory V] [EnrichedOrdinaryCategory U M]

@[instance_reducible] def ordinaryBaseChange
  (G : U ⥤ V) [G.LaxMonoidal]
  (e : ∀ Z : U, (𝟙_ U ⟶ Z) ≃ (𝟙_ V ⟶ G.obj Z))
  (he : ∀ (Z : U) (f : 𝟙_ U ⟶ Z), e Z f = Functor.LaxMonoidal.ε G ≫ G.map f) :
    EnrichedOrdinaryCategory V M
def ordinaryBaseChangeHomIso (G : U ⥤ V) [G.LaxMonoidal]
    (e : ∀ Z : U, (𝟙_ U ⟶ Z) ≃ (𝟙_ V ⟶ G.obj Z))
    (he : ∀ (Z : U) (f : 𝟙_ U ⟶ Z), e Z f = Functor.LaxMonoidal.ε G ≫ G.map f) :
    let : EnrichedOrdinaryCategory V M := ordinaryBaseChange G e he
    eHomFunctor V M ≅ eHomFunctor U M ⋙ (Functor.whiskeringRight M U V).obj G
```

`ordinaryBaseChange` には宣言の引数として `G e he` を残す。Hom は `G.obj`、単位は `ε G` と元の単位、合成は `μ G` と元の合成、単位点への同値は元の `eHomEquiv` と `e` の合成。Mathlib 版との比較は対象型の同型を新設する作業ではなく、同じ入力の構造を持つ値の型の照合になる。

### `MonoidalAdjunction.lean`

下の `F` の強モノイダル性は B2 で `η F : F(𝟙) ⟶ 𝟙` を反転するために使う。新しく選ぶ右随伴の lax 構造は `adj.rightAdjointLaxMonoidal`。単位点の同値は `η F` で前合成する同値の後の `adj.homEquiv`。この写像の式は `homEquiv_naturality_right` と mate による `ε G` の定義で得る。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open SerrePositivity.Enriched
universe u v u' v'
variable {V : Type u} {W : Type u'} [Category.{v} V] [Category.{v'} W]
  [MonoidalCategory V] [MonoidalCategory W] [SymmetricCategory W] [MonoidalClosed W]
  {F : V ⥤ W} {G : W ⥤ V} [F.Monoidal]
local notation "Act" => F ⋙ curriedTensor W
local notation "Cot" => F.op ⋙ MonoidalClosed.internalHom
local notation "Map" => MonoidalClosed.internalHom ⋙ Functor.obj (Functor.whiskeringRight W W V) G

def adjunctionPointEquiv (d : F ⊣ G) (Z : W) :
    (𝟙_ W ⟶ Z) ≃ (𝟙_ V ⟶ G.obj Z)
lemma adjunctionPointEquiv_apply (d : F ⊣ G) (Z : W) (f : 𝟙_ W ⟶ Z) :
    let : G.LaxMonoidal := d.rightAdjointLaxMonoidal
    adjunctionPointEquiv d Z f = Functor.LaxMonoidal.ε G ≫ G.map f

def adjunctionCotensorAdjunction (F : V ⥤ W) :
    F ⋙ curriedTensor W ⊣₂ F.op ⋙ MonoidalClosed.internalHom
def adjunctionMappingAdjunction (d : F ⊣ G) : (Act).flip ⊣₂ Map

@[instance_reducible] def ofMonoidalAdjunction (d : F ⊣ G) :
    EnrichedOrdinaryCategory V W
def ofMonoidalAdjunctionHomIso (d : F ⊣ G) :
    let : EnrichedOrdinaryCategory V W := ofMonoidalAdjunction d
    eHomFunctor V W ≅ Map
def ofMonoidalAdjunctionTensorCotensor (d : F ⊣ G) :
    let : EnrichedOrdinaryCategory V W := ofMonoidalAdjunction d
    TensorCotensor V W
lemma ofMonoidalAdjunction_tensorHomEquiv (d : F ⊣ G)
    (P : V) (X Y : W) (f : F.obj P ⊗ X ⟶ Y) :
    let : EnrichedOrdinaryCategory V W := ofMonoidalAdjunction d
    (ofMonoidalAdjunctionTensorCotensor d).tensorHomEquiv P X Y f =
      (adjunctionMappingAdjunction d).homEquiv f
```

`adjunctionCotensorAdjunction` は `ParametrizedAdjunctionTransport.restrict` で `MonoidalClosed.internalHomAdjunction₂` を `F` に沿って制限。 `adjunctionMappingAdjunction` は `MonoidalMappingAdjunction.transportedParametrizedAdjunction` の現在の構成を利用し、(F(P)\otimes X\to Y) を組紐で (X\otimes F(P)\to Y) として閉転置してから `d` の転置を取る。 `ofMonoidalAdjunction` は W の `enrichedOrdinaryCategorySelf` を `ordinaryBaseChange` に渡す。 `ofMonoidalAdjunctionHomIso` の成分は恒等。 `tensor=Act`、`cotensor=Cot`、二つの随伴のうち Hom 側だけをこの同型の逆に沿って右輸送する。従って上の `f` が両方の転置の定義域に入る。テンソル・余テンソルの値は (F(P)\otimes X) と ([F(P),X])。

## B4　二通りの比較 `Comparison.lean`

B2 には `[F.Monoidal]` で足りる。B4 では `V` の組紐と **`[F.Braided]`** を取る。A3 から Mathlib の合成順に戻すときの (β_V) を B2 の (β_W) と照合するためで、強モノイダル性だけでこの照合を仮定しない。`F ⋙ MonoidalLeftAction.curriedActionMop W W` から作用を作り、対応する曲がった関手の比較をほどき、`actionTensorIso` を取る。A3 の右随伴は固定した `Map`、左はこの作用。`ParametrizedAdjunctionTransport.left` で B2 が使う随伴を `actionTensorIso.symm` に沿って移したものを選ぶ。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open SerrePositivity.Enriched
universe u v u' v'
variable {V : Type u} {W : Type u'} [Category.{v} V] [Category.{v'} W]
  [MonoidalCategory V] [BraidedCategory V] [MonoidalCategory W]
  [SymmetricCategory W] [MonoidalClosed W]
  {F : V ⥤ W} {G : W ⥤ V} [F.Braided]
local notation "Act" => F ⋙ curriedTensor W
local notation "Cot" => F.op ⋙ MonoidalClosed.internalHom
local notation "Map" => MonoidalClosed.internalHom ⋙ Functor.obj (Functor.whiskeringRight W W V) G

@[instance_reducible] def actionOfMonoidal (F : V ⥤ W) [F.Braided] :
    MonoidalLeftAction V W
def actionTensorIso (F : V ⥤ W) [F.Braided] :
    let : MonoidalLeftAction V W := actionOfMonoidal F
    MonoidalLeftAction.curriedAction V W ≅ F ⋙ curriedTensor W
def adjunctionActionMapping (d : F ⊣ G) :
    let : MonoidalLeftAction V W := actionOfMonoidal F
    (MonoidalLeftAction.curriedAction V W).flip ⊣₂ Map
def adjunctionActionCotensor (F : V ⥤ W) [F.Braided] :
    let : MonoidalLeftAction V W := actionOfMonoidal F
    MonoidalLeftAction.curriedAction V W ⊣₂ F.op ⋙ MonoidalClosed.internalHom
def adjunctionActionOrdinary (d : F ⊣ G) : EnrichedOrdinaryCategory V W
def adjunctionActionTensorCotensor (d : F ⊣ G) :
    let : EnrichedOrdinaryCategory V W := adjunctionActionOrdinary d
    TensorCotensor V W
def adjunctionEnrichmentIso (d : F ⊣ G) :
    @eHomFunctor V _ _ W _ (adjunctionActionOrdinary d) ≅
      @eHomFunctor V _ _ W _ (ofMonoidalAdjunction d)
```

```lean
set_option backward.isDefEq.respectTransparency false
local notation "EA[" d "]" => adjunctionActionOrdinary d
local notation "EB[" d "]" => ofMonoidalAdjunction d
local notation "SA[" d "]" => adjunctionActionTensorCotensor d
local notation "SB[" d "]" => ofMonoidalAdjunctionTensorCotensor d
local notation "TA[" d "]" => @TensorCotensor.tensor V _ _ W _ (EA[d]) (SA[d])
local notation "TB[" d "]" => @TensorCotensor.tensor V _ _ W _ (EB[d]) (SB[d])
local notation "QA[" d "]" => @TensorCotensor.cotensor V _ _ W _ (EA[d]) (SA[d])
local notation "QB[" d "]" => @TensorCotensor.cotensor V _ _ W _ (EB[d]) (SB[d])

lemma adjunctionEnrichmentIso_id (d : F ⊣ G) (X : W) :
    @eId V _ _ W (EnrichedOrdinaryCategory.toEnrichedCategory (self := EA[d])) X ≫
      ((adjunctionEnrichmentIso d).hom.app (op X)).app X =
      @eId V _ _ W (EnrichedOrdinaryCategory.toEnrichedCategory (self := EB[d])) X
lemma adjunctionEnrichmentIso_comp (d : F ⊣ G) (X Y Z : W) :
    @eComp V _ _ W (EnrichedOrdinaryCategory.toEnrichedCategory (self := EA[d])) X Y Z ≫
      ((adjunctionEnrichmentIso d).hom.app (op X)).app Z =
      (((adjunctionEnrichmentIso d).hom.app (op X)).app Y ⊗ₘ ((adjunctionEnrichmentIso d).hom.app (op Y)).app Z) ≫
        @eComp V _ _ W (EnrichedOrdinaryCategory.toEnrichedCategory (self := EB[d])) X Y Z
lemma adjunctionEnrichmentIso_points (d : F ⊣ G) {X Y : W} (f : X ⟶ Y) :
    (@eHomEquiv V _ _ W _ EA[d] X Y) f ≫ ((adjunctionEnrichmentIso d).hom.app (op X)).app Y =
      (@eHomEquiv V _ _ W _ EB[d] X Y) f

def adjunctionTensorIso (d : F ⊣ G) : TA[d] ≅ TB[d]
def adjunctionCotensorIso (d : F ⊣ G) : QA[d] ≅ QB[d]
lemma adjunctionEnrichmentIso_tensorHomEquiv (d : F ⊣ G) (P : V) (X Y : W)
    (f : ((TB[d]).obj P).obj X ⟶ Y) :
    (@TensorCotensor.tensorHomEquiv V _ _ W _ (EA[d]) (SA[d]))
        P X Y (((adjunctionTensorIso d).hom.app P).app X ≫ f) ≫
      ((adjunctionEnrichmentIso d).hom.app (op X)).app Y =
      (@TensorCotensor.tensorHomEquiv V _ _ W _ (EB[d]) (SB[d])) P X Y f
lemma adjunctionEnrichmentIso_tensorCotensorHomEquiv (d : F ⊣ G) (P : V) (X Y : W)
    (f : ((TB[d]).obj P).obj X ⟶ Y) :
    (@TensorCotensor.tensorCotensorHomEquiv V _ _ W _ (EA[d]) (SA[d]))
        P X Y (((adjunctionTensorIso d).hom.app P).app X ≫ f) ≫
      ((adjunctionCotensorIso d).hom.app (op P)).app Y =
        (@TensorCotensor.tensorCotensorHomEquiv V _ _ W _ (EB[d]) (SB[d])) P X Y f
```

`adjunctionActionOrdinary` は `ofAction` に `adjunctionActionMapping` を渡す。もう一方の通常豊穣化は B2。 `adjunctionEnrichmentIso` は両方の Hom 関手の `Map` への比較の合成。単位は `η F` の mate、合成では `δ F` と二つの余単位のテンソルの mate を使い、`F.Braided` で因子順を一致させる。通常射と単位点の等式は両構成の `adjunctionPointEquiv` との一致。最後の二式を合成すれば余テンソルから写像対象への転置の両立も得られる。使う側は自然な比較とこの転置の式を使って段ごとの評価・係数・原変数を移す。豊穣圏の構造レコード全体の等号を要求すると、選んだ作用・随伴の実装が違う場合に式が使いにくくなる。

## C-軽　部分圏・対・関手圏・表現可能な Hom

### `FullSubcategory.lean` と `Product.lean`

部分圏の Hom は元の Hom。通常圏がある場合は Mathlib の `ObjectProperty.FullSubcategory` の既存の構造を使う。別の Hom 表示との比較は `HomCongr` を使う。対は成分ごとの `V × V` 豊穣を `MonoidalCategory.tensor V` に沿って輸送する。固定対象を入れる挿入は、固定側の単位射と対象ごとの単位子で作る。通常の直積圏の射との比較は、単位からの射が二つの点に分かれる場合に使える。SSet のデカルト構造ではこの条件が成立する。 `EnrichedCat` の双圏構造を使え、ここでそのモノイダル構造を登録する必要はない。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory
universe u v w z
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  {D : Type w} {E : Type z} [EnrichedCategory V D] [EnrichedCategory V E]

@[instance_reducible] def enrichedFullSubcategory (p : D → Prop) :
    EnrichedCategory V {X : D // p X}
def enrichedFullSubcategoryInclusion (p : D → Prop) :
    let : EnrichedCategory V {X : D // p X} := enrichedFullSubcategory (V := V) p
    EnrichedFunctor V {X : D // p X} D

variable [BraidedCategory V]

@[instance_reducible] def tensorEnrichedCategory (D : Type w) (E : Type z)
    [EnrichedCategory V D] [EnrichedCategory V E] : EnrichedCategory V (D × E)
def tensorEnrichedIncludeFirst (Y : E) :
    let : EnrichedCategory V (D × E) := tensorEnrichedCategory (V := V) D E
    EnrichedFunctor V D (D × E)
def tensorEnrichedIncludeSecond (X : D) :
    let : EnrichedCategory V (D × E) := tensorEnrichedCategory (V := V) D E
    EnrichedFunctor V E (D × E)
```

### `FunctorCategory.lean`

Mathlib の `Enriched.FunctorCategory` の二つの構成は通常の添字圏 `J` 上の `J ⥤ E` に対するもの。ここでは Mathlib の `enrichedNatTransYoneda` が表す、**豊穣**添字 D の自然性を使う。Hom は `∏ X, E(FX,GX)` から `∏ (X,Y), [D(X,Y),E(FX,GY)]` への二射の等化子。射はそれぞれ G による後合成と F による前合成（後者は組紐で配置を揃える）の転置。同時評価の対の合成と等化子の条件で組紐の逆を照合するため、関手圏の入口では対称性を仮定する。対象と対象対の二種類の離散添字の積を明記し、V の対象・射の宇宙は添字と独立にする。評価は固定 X なら射影、同時評価なら射影と動く引数の Hom を G の作用で合成する。二つの評価順が一致するのは等化子の条件。単位点では、豊穣自然性を満たす変換を得る。Mathlib の `EnrichedNatTrans` は通常圏に忘れた自然変換であり、V の単位点が豊穣 Hom の射を検出するときに限って、この等化子の点をその通常圏の射と同一視できる。一般の V では `ForgetEnrichment` によって通常圏を作る。SSet でも頂点だけで任意の単体写像を検出できないので、全 Hom と可換な通常射族を使って比較する。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe u v w z
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {D : Type w} {E : Type z} [EnrichedCategory V D] [EnrichedCategory V E]
  [HasProductsOfShape D V] [HasProductsOfShape (D × D) V] [HasEqualizers V]

def enrichedFunctorHom (F G : EnrichedFunctor V D E) : V
def enrichedFunctorHomπ (F G : EnrichedFunctor V D E) (X : D) :
    enrichedFunctorHom F G ⟶ F.obj X ⟶[V] G.obj X
def enrichedFunctorHomEquiv (F G : EnrichedFunctor V D E) (P : V) :
    (P ⟶ enrichedFunctorHom F G) ≃ GradedNatTrans ((Center.ofBraided V).obj P) F G
@[instance_reducible] def enrichedFunctorEnrichment (D : Type w) (E : Type z)
    [EnrichedCategory V D] [EnrichedCategory V E]
    [HasProductsOfShape D V] [HasProductsOfShape (D × D) V] :
    EnrichedCategory V (EnrichedFunctor V D E)
def enrichedFunctorEvaluateAt (X : D) :
    let : EnrichedCategory V (EnrichedFunctor V D E) := enrichedFunctorEnrichment (V := V) D E
    EnrichedFunctor V (EnrichedFunctor V D E) E
def enrichedFunctorEvaluation (D : Type w) (E : Type z)
    [EnrichedCategory V D] [EnrichedCategory V E]
    [HasProductsOfShape D V] [HasProductsOfShape (D × D) V] :
    let : EnrichedCategory V (EnrichedFunctor V D E) := enrichedFunctorEnrichment (V := V) D E
    let : EnrichedCategory V (EnrichedFunctor V D E × D) :=
      tensorEnrichedCategory (V := V) (EnrichedFunctor V D E) D
    EnrichedFunctor V (EnrichedFunctor V D E × D) E
```

### `Representable.lean`

共変では合成を内部 Hom に転置する。反変は Mathlib の `EnrichedCategory.opposite` を使い、前合成の因子順を組紐で揃える。これは対象を一つ固定した豊穣関手で、`eCoyoneda` が与える通常の V 値関手は通常射の変数で照合する。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
universe u v w
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {D : Type w} [EnrichedCategory V D]

def enrichedRepresentableCovariant (X : D) :
    let : EnrichedOrdinaryCategory V V := MonoidalClosed.enrichedOrdinaryCategorySelf V
    EnrichedFunctor V D V
def enrichedRepresentable (X : D) :
    let : EnrichedOrdinaryCategory V V := MonoidalClosed.enrichedOrdinaryCategorySelf V
    EnrichedFunctor V Dᵒᵖ V
```

| 適用 | dg | SSet |
| --- | --- | --- |
| 部分圏 | `dgFullSubcategoryEnrichment`、包含 | `kanObject_enrichedCategory`、`quasicategoryObject_enrichedCategory` |
| 対と挿入 | `dgPairEnrichment`、`dgTensorEnrichment`、`dgTensorIncludeFirst/Second` | `simplicialPairObject_enrichedCategory`、そこから `kanTensorEnriched` の定義域へ |
| 関手圏 | `dgFunctorHom`、`dgFunctorHomEquiv`、`dgFunctorEnrichment`、`dgFunctorEvaluationDG` | `QuasicategoryEnrichedComparison` は単位点での条件。関手圏を準圏に制限する場合は局所 Hom の閉性を別に示す。通常の添字の `simplicialSSetDiagram_simplicialCategory` は現行 Mathlib の構成を維持 |
| 可表 Hom | `DifferentialGraded` の `representable` | `representableHomFunctor`、FrameHom の既存の一致補題 |

dg 領域の対象と段1の照合結果は [構成別の表 D](general-theory.md#d-dg-で実装されている-v-に一般な構成) にある。前層・双加群の構造比較、米田・余米田の同型、双加群の合成と Dold–Kan の適用はここでは設計を広げない。

## B1 の作用への適用

A3 側は作用結合子の比較を B3 のテンソルに入れ、左右の単位則は `ofActionTensorCotensor` の単位が作用単位子と一致することから示す。B2 側は `F` の二項比較と W の結合子を使うので、この適用にも基底 V の組紐以外に `F.Braided` は要らない。各節に `[MonoidalClosed V]` を追加すると、`ofTensorCotensor` に以下の構造を渡せる。

```lean
-- OfAction の文脈
variable [MonoidalClosed V]

def ofActionTensorAssociativity (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) :
    let : EnrichedOrdinaryCategory V M := ofAction r
    TensorAssociativity (ofActionTensorCotensor r q)
```

```lean
-- MonoidalAdjunction の文脈
variable [BraidedCategory V] [MonoidalClosed V]

def ofMonoidalAdjunctionTensorAssociativity (d : F ⊣ G) :
    let : EnrichedOrdinaryCategory V W := ofMonoidalAdjunction d
    TensorAssociativity (ofMonoidalAdjunctionTensorCotensor d)
```

## 対称スペクトルと基点付き単体集合

### 対称スペクトル（段4）

固定 Mathlib の `Mod` に対し、本体の `MonoidalBalancedTensor.symmetricCategory`、`MonoidalModuleInternalHom.moduleMonoidalClosed`、`MonoidalBalancedTensor.freeFunctorMonoidal`、`MonoidalBalancedTensor.freeFunctorBraided` を使う。可換モノイドと、相対テンソル・内部 Hom の構成に必要な余等化子・等化子のもとで型クラスを推論できる。スペクトルの対称性と閉性にもこれらの instance が使われる。

`freeAtAdjunction 0` は存在し、左辺は `SymmetricSequence.freeAt 0 ⋙ GeneralSymmetricSpectrum.freeFunctor K`、右辺は `GeneralSymmetricSpectrum.forget K ⋙ SymmetricSequence.evaluation 0`。列側の `freeAt 0` の `Monoidal` が欠けている。 単位に `freeZeroUnitIso` の逆、二項に `freePairConvolutionIso 0 0` を取り、自然性、単位、結合、B4 用の組紐を自由生成子で照合する。加群側の自由関手と合成すれば F₀ の `Monoidal` と `Braided` を組める。B2 を先に使う場合は `Monoidal` までで足りる。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite
open SerrePositivity SerrePositivity.Enriched
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0,0} C] [HasLimitsOfSize.{0,0} C] (K : C)
local notation "Sp" => GeneralSymmetricSpectrum C K
local notation "F₀" => GeneralSymmetricSpectrum.freeAt (K := K) 0
local notation "Ev₀" => GeneralSymmetricSpectrum.evaluation (K := K) 0
local notation "d₀" => GeneralSymmetricSpectrum.freeAtAdjunction (K := K) 0

def freeZeroSequenceMonoidalCore (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [HasColimitsOfSize.{0,0} C] [MonoidalClosed C] [SymmetricCategory C] :
    (SymmetricSequence.freeAt (C := C) 0).CoreMonoidal
@[instance_reducible] def spectrumOrdinaryOfAdjunction (hF : (F₀).Monoidal) : EnrichedOrdinaryCategory C Sp
def spectrumTensorCotensorOfAdjunction (hF : (F₀).Monoidal) :
    let : EnrichedOrdinaryCategory C Sp := spectrumOrdinaryOfAdjunction K hF
    TensorCotensor C Sp
def spectrumMappingObjectIso (hF : (F₀).Monoidal) :
    let : EnrichedOrdinaryCategory C Sp := spectrumOrdinaryOfAdjunction K hF
    eHomFunctor C Sp ≅ GeneralSymmetricSpectrum.mappingObjectBifunctor (K := K)
def spectrumTensorIso (hF : (F₀).Monoidal) :
    let : EnrichedOrdinaryCategory C Sp := spectrumOrdinaryOfAdjunction K hF
    (spectrumTensorCotensorOfAdjunction K hF).tensor ≅
      @TensorCotensor.tensor C _ _ Sp _ (GeneralSymmetricSpectrum.mappingEnrichedOrdinaryCategory
        (K := K)) (GeneralSymmetricSpectrum.spectrumTensorCotensor (K := K))
def spectrumCotensorIso (hF : (F₀).Monoidal) :
    let : EnrichedOrdinaryCategory C Sp := spectrumOrdinaryOfAdjunction K hF
    (spectrumTensorCotensorOfAdjunction K hF).cotensor ≅
      @TensorCotensor.cotensor C _ _ Sp _ (GeneralSymmetricSpectrum.mappingEnrichedOrdinaryCategory
        (K := K)) (GeneralSymmetricSpectrum.spectrumTensorCotensor (K := K))
```

`spectrumOrdinaryOfAdjunction` は `letI := hF` のもとで `ofMonoidalAdjunction d₀`。テンソル・余テンソルの表示には、既存の `tensorFreeZeroPointwiseBifunctorIso` と `internalHomCotensorBifunctorIso` を使う。写像対象は両方 `Ev₀ [X,Y]`。自己豊穣化の `internalHom` と本体の `internalHomBifunctor` は定義的に一致する。既存の `spectrumTensorCotensor_tensorHomEquiv` により、テンソルの転置は `mappingObjectHomEquiv` で計算できる。二つの通常随伴を既存の輸送と照合すると、余テンソルから写像対象への転置も比較できる。利用側には `pointwiseTensor_level`、`cotensor_level` と射・単位の各段の計算を残す。旧豊穣化の単位と合成は旧作用の `pointwiseTensorAssociatorNatIso` と新しい作用結合子の生成子での一致を通して比べる。

### 基点付き単体集合（段3の試験）

`adjoinBasepointAdjunction` があり、smash の `SymmetricCategory` と `MonoidalClosed` を推論できる。 `adjoinBasepointFunctor.Monoidal` は推論できない。 `adjoinBasepointUnitIso` の逆と `adjoinBasepointProductIso` の組で、左右単位と結合を対の元・基点の像で確認する。B4 まで試すなら同じ表示で組紐も照合する。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity SerrePositivity.Enriched
universe u

def adjoinBasepointMonoidalCore : (PointedSimplicialSet.adjoinBasepointFunctor.{u}).CoreMonoidal
@[instance_reducible] def pointedOrdinaryOfAdjunction (hF : (PointedSimplicialSet.adjoinBasepointFunctor.{u}).Monoidal) : EnrichedOrdinaryCategory SSet.{u} PointedSimplicialSet.{u}
def pointedTensorCotensorOfAdjunction (hF : (PointedSimplicialSet.adjoinBasepointFunctor.{u}).Monoidal) :
    let : EnrichedOrdinaryCategory SSet.{u} PointedSimplicialSet.{u} := pointedOrdinaryOfAdjunction hF
    TensorCotensor SSet.{u} PointedSimplicialSet.{u}
def pointedAdjunctionHomIso (hF : (PointedSimplicialSet.adjoinBasepointFunctor.{u}).Monoidal) :
    @eHomFunctor SSet.{u} _ _ PointedSimplicialSet.{u} _ (pointedOrdinaryOfAdjunction hF) ≅
      @eHomFunctor SSet.{u} _ _ PointedSimplicialSet.{u} _ KST.Spectra.PointedEnrichment.simplicialCategory
```

`letI := hF` のもとで `ofMonoidalAdjunction adjoinBasepointAdjunction` を取る。テンソルは基点付加との smash、余テンソルは基点付き内部 Hom。現行 `PointedEnrichment.simplicialCategory` も忘却した基点付き内部 Hom が写像対象。単位点は `forgetUnitHomEquiv_formula` と `adjunctionPointEquiv_apply` で比べる。忘却関手の既存の lax 比較と随伴の mate が、積の対および単位点で一致することを別に示せば、現行の合成・単位とも両立する。局所 Kan 性はあとで付ける性質として残る。

## 現行 120 宣言の行き先

各行は段1の A2 の採取に対応。旧名の共通の接頭辞 `SerrePositivity.` を省略した。行数は [採取表](../spectra/layers-a.csv) の宣言範囲（コメント・空行を含み得る）。「消える」は段3–4の利用側移行後の見込み。改名・移動も、対応表・blueprint を含め旧名を使う側の移行後に行う。章や文献への対応が付いた定理は新しい対応が取れるまで互換名を維持する。

`CategoryTheory/Adjunction/Comparison.lean` と `CategoryTheory/FunctorTransport.lean` はそのまま使う。以下の表の短いファイル名は `CategoryTheory/Enriched/` からの相対名。 `Simplicial/EnrichedHomLaws.lean` は `CategoryTheory/` からの相対名。表の「移す」は主張を引き継ぎ、公開する入口は Mathlib の名前空間に揃える。現行 `TensorCotensor` と `EnrichedRepresentability` の型と欄は保存する。

### `RepresentedMapping.lean`

| 旧宣言 | 行 | 扱い | 行き先・置き換え |
| --- | ---: | --- | --- |
| `MappingArrowComposition.arrowCompositionEvaluationLaw` | 6 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingArrowComposition.arrow_composition_evaluation` | 22 | 移す | `OfAction.lean`。SU-W1 段14a の評価則・自然性を使う |
| `MappingArrowComposition.representedArrowCompositionLaw` | 8 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingArrowComposition.represented_arrow_composition` | 13 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingAssociativity.associativityEvaluationLaw` | 9 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingAssociativity.associativity_evaluation` | 26 | 移す | `OfAction.lean`。SU-W1 段14a の評価則・自然性を使う |
| `MappingAssociativity.compositionEvaluation` | 5 | 消える | 評価後の式に展開 |
| `MappingAssociativity.representedAssociativityLaw` | 9 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingAssociativity.represented_associativity` | 11 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingUnitLaws.left_unit_evaluation` | 15 | 移す | `OfAction.lean`。SU-W1 段14a の評価則・自然性を使う |
| `MappingUnitLaws.parameterFunctor` | 6 | 消える | 作用の `H.flip.obj` |
| `MappingUnitLaws.right_unit_evaluation` | 15 | 移す | `OfAction.lean`。SU-W1 段14a の評価則・自然性を使う |
| `MappingWhiskering.enriched_post` | 15 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingWhiskering.enriched_pre` | 16 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingWhiskering.post_composition` | 39 | 移す | `OfAction.lean`。SU-W1 段14a の評価則・自然性を使う |
| `MappingWhiskering.post_evaluation` | 14 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingWhiskering.pre_composition` | 42 | 移す | `OfAction.lean`。SU-W1 段14a の評価則・自然性を使う |
| `MappingWhiskering.pre_evaluation` | 15 | 消える | OfAction.lean の法則の証明に吸収 |
| `MonoidalMappingAdjunction.adjunction` | 3 | 移す | `MonoidalAdjunction.lean`。閉随伴と随伴の合成・自然性を共有 |
| `MonoidalMappingAdjunction.compositeDerivedPreLaw` | 8 | 消える | MonoidalAdjunction.lean の法則の証明に吸収 |
| `MonoidalMappingAdjunction.compositeTransportedPreLaw` | 7 | 消える | MonoidalAdjunction.lean の法則の証明に吸収 |
| `MonoidalMappingAdjunction.composite_derived_pre` | 12 | 消える | 一般の前合成の自然性 |
| `MonoidalMappingAdjunction.composite_transported_pre` | 10 | 移す | `MonoidalAdjunction.lean`。閉随伴と随伴の合成・自然性を共有 |
| `MonoidalMappingAdjunction.homEquiv_formula` | 11 | 移す | `MonoidalAdjunction.lean`。閉随伴と随伴の合成・自然性を共有 |
| `MonoidalMappingAdjunction.homEquiv_pre` | 9 | 移す | `MonoidalAdjunction.lean`。閉随伴と随伴の合成・自然性を共有 |
| `MonoidalMappingAdjunction.transportedParametrizedAdjunction` | 6 | 移す | `MonoidalAdjunction.lean`。閉随伴と随伴の合成・自然性を共有 |
| `MonoidalMappingAdjunction.transportedPreLaw` | 6 | 消える | MonoidalAdjunction.lean の法則の証明に吸収 |
| `MonoidalMappingAdjunction.transportedUncurryPreLaw` | 7 | 消える | MonoidalAdjunction.lean の法則の証明に吸収 |
| `MonoidalMappingAdjunction.transported_pre` | 9 | 移す | `MonoidalAdjunction.lean`。閉随伴と随伴の合成・自然性を共有 |
| `MonoidalMappingAdjunction.transported_pre_bifunctor` | 9 | 移す | `MonoidalAdjunction.lean`。閉随伴と随伴の合成・自然性を共有 |
| `MonoidalMappingAdjunction.transported_uncurry_pre` | 14 | 消える | パラメータ付き随伴の自然性 |
| `RepresentedHomFunctor.homFunctorIso` | 23 | 移す | `OfAction.lean`。既存の成分比較を A3 の内部で共有 |
| `RepresentedHomFunctor.homFunctorIso_ofParametrized` | 19 | 改名 | OfAction.lean の `ofActionHomIso` |
| `RepresentedMappingEnrichment.arrow` | 2 | 消える | `actionHomEquiv` の適用 |
| `RepresentedMappingEnrichment.arrowCompositionLaw` | 5 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.arrowEquiv` | 3 | 改名 | OfAction.lean の `actionHomEquiv` |
| `RepresentedMappingEnrichment.arrowIdentityLaw` | 3 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.arrow_identity` | 3 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.associativity` | 7 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.associativityEvaluationLaw` | 6 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.associativityLaw` | 6 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.associativity_evaluation` | 21 | 移す | `OfAction.lean` |
| `RepresentedMappingEnrichment.composition` | 3 | 移す | `OfAction.lean`。評価後の計算で使う逆順の式。新しい作用の合成そのものとは組紐で比較 |
| `RepresentedMappingEnrichment.compositionEvaluation` | 5 | 消える | 評価後の式に展開 |
| `RepresentedMappingEnrichment.compositionEvaluationLaw` | 4 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.composition_evaluation` | 3 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.enrichedCategory` | 15 | 移す | `OfAction.lean`。`ofAction` の内部の構成 |
| `RepresentedMappingEnrichment.enrichedCategory_comp` | 6 | 消える | 新しい合成の定義式。一致には組紐を挟む |
| `RepresentedMappingEnrichment.enrichedCategory_id` | 5 | 消える | 新しい単位の定義式 |
| `RepresentedMappingEnrichment.evaluation` | 2 | 改名 | OfAction.lean の `actionEvaluation` |
| `RepresentedMappingEnrichment.hom` | 2 | 消える | 選んだ右随伴 `R` の対象成分 |
| `RepresentedMappingEnrichment.leftUnitEvaluationLaw` | 5 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.leftUnitLaw` | 4 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.left_unit` | 5 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.left_unit_evaluation` | 14 | 移す | `OfAction.lean` |
| `RepresentedMappingEnrichment.ordinaryCategory` | 15 | 改名 | OfAction.lean の `ofAction` |
| `RepresentedMappingEnrichment.rightUnitEvaluationLaw` | 5 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.rightUnitLaw` | 4 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.right_unit` | 5 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.right_unit_evaluation` | 14 | 移す | `OfAction.lean` |
| `RepresentedMappingEnrichment.unit` | 2 | 改名 | OfAction.lean の `actionUnit` |
| `RepresentedMappingEnrichment.unitEvaluationLaw` | 3 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.unit_evaluation` | 3 | 消える | OfAction.lean の法則の証明に吸収 |

### `Transport.lean`

| 旧宣言 | 行 | 扱い | 行き先・置き換え |
| --- | ---: | --- | --- |
| `LaxPointHom.composition` | 12 | 移す | `BaseChange.lean` |
| `LaxPointHom.left_action` | 8 | 移す | `BaseChange.lean` |
| `LaxPointHom.map` | 2 | 移す | `BaseChange.lean` |
| `LaxPointHom.right_action` | 8 | 移す | `BaseChange.lean` |
| `ReverseComposition.associativity` | 10 | 移す | `BaseChange.lean`。合成を入れ替える構成と法則を共有 |
| `ReverseComposition.enrichedCategory` | 28 | 移す | `BaseChange.lean`。合成を入れ替える構成と法則を共有 |
| `ReverseComposition.left_unit` | 6 | 移す | `BaseChange.lean`。合成を入れ替える構成と法則を共有 |
| `ReverseComposition.points` | 8 | 移す | `BaseChange.lean`。合成を入れ替える構成と法則を共有 |
| `ReverseComposition.reverse` | 2 | 移す | `BaseChange.lean`。合成を入れ替える構成と法則を共有 |
| `ReverseComposition.reverse_three` | 7 | 移す | `BaseChange.lean`。合成を入れ替える構成と法則を共有 |
| `ReverseComposition.right_unit` | 6 | 移す | `BaseChange.lean`。合成を入れ替える構成と法則を共有 |
| `TransportEnrichmentComparisons.category` | 4 | 移す | `BaseChange.lean`。Mathlib の輸送を使う現行の比較。外部利用を合わせてから薄くする |
| `TransportEnrichmentComparisons.identityLaw` | 3 | 消える | Mathlib の輸送の単位の定義式 |
| `TransportEnrichmentComparisons.identity_eq` | 7 | 消える | Mathlib の輸送の単位の定義式 |
| `TransportEnrichmentComparisons.reverseCompositionLaw` | 6 | 消える | 輸送の合成の定義式と組紐の自然性 |
| `TransportEnrichmentComparisons.reverse_composition` | 8 | 消える | 輸送の合成の定義式と組紐の自然性 |
| `TransportOrdinaryEnrichment.homFunctorIso` | 15 | 改名 | BaseChange.lean の `ordinaryBaseChangeHomIso` |
| `TransportOrdinaryEnrichment.ordinaryCategory` | 16 | 改名 | BaseChange.lean の `ordinaryBaseChange` |
| `TransportOrdinaryEnrichment.whiskerLeft_map` | 9 | 移す | `BaseChange.lean` |
| `TransportOrdinaryEnrichment.whiskerRight_map` | 9 | 移す | `BaseChange.lean` |

### `TensorCotensor.lean`

| 旧宣言 | 行 | 扱い | 行き先・置き換え |
| --- | ---: | --- | --- |
| `Enriched.EnrichedRepresentability` | 21 | 残す | `TensorCotensor.lean` |
| `Enriched.EnrichedRepresentability.cotensorHomIso` | 3 | 残す | `TensorCotensor.lean` |
| `Enriched.EnrichedRepresentability.homObjectComparison` | 4 | 残す | `TensorCotensor.lean` |
| `Enriched.EnrichedRepresentability.homObjectComparison_points` | 17 | 残す | `TensorCotensor.lean` |
| `Enriched.EnrichedRepresentability.tensorHomIso` | 3 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor` | 7 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.coevaluation` | 3 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.cotensorHomEquiv` | 3 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.cotensorHom_naturality_parameter` | 10 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.cotensorHom_naturality_source` | 9 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.cotensorHom_naturality_target` | 10 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.cotensor_triangle` | 4 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.evaluation` | 3 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.homEquiv_compatibility` | 4 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.tensorCotensorHomEquiv` | 3 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.tensorCotensor_naturality_parameter` | 5 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.tensorCotensor_naturality_source` | 5 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.tensorCotensor_naturality_target` | 5 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.tensorHomEquiv` | 3 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.tensorHom_naturality_parameter` | 5 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.tensorHom_naturality_source` | 5 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.tensorHom_naturality_target` | 5 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.tensor_triangle` | 3 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.unitIso` | 4 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.unitMap` | 2 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.unitMap_comp` | 5 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.unitMap_isIso` | 9 | 残す | `TensorCotensor.lean` |
| `Enriched.TensorCotensor.unitMap_naturality` | 5 | 残す | `TensorCotensor.lean` |
| `Enriched.cotensorEnrichedHom` | 2 | 残す | `TensorCotensor.lean` |
| `Enriched.eHomEquiv_postcomp` | 4 | 残す | `TensorCotensor.lean` |
| `Enriched.eHomEquiv_precomp` | 4 | 残す | `TensorCotensor.lean` |
| `Enriched.powerHom` | 2 | 残す | `TensorCotensor.lean` |
| `Enriched.tensorEnrichedHom` | 2 | 残す | `TensorCotensor.lean` |

### `Simplicial.lean`

| 旧宣言 | 行 | 扱い | 行き先・置き換え |
| --- | ---: | --- | --- |
| `SimplicialHomLaws.composition` | 5 | 移す | `Simplicial/EnrichedHomLaws.lean` |
| `SimplicialHomLaws.compositionLaw` | 4 | 移す | `Simplicial/EnrichedHomLaws.lean` |
| `SimplicialHomLaws.identity` | 5 | 移す | `Simplicial/EnrichedHomLaws.lean` |
| `SimplicialHomLaws.identityLaw` | 3 | 移す | `Simplicial/EnrichedHomLaws.lean` |

## 行数の見積もりと段3の分け方

| 旧ファイル | 残す（宣言／行） | 改名（宣言／行） | 移す（宣言／行） | 消える（宣言／行） |
| --- | ---: | ---: | ---: | ---: |
| RepresentedMapping | 0／0 | 5／41 | 19／306 | 39／272 |
| Transport | 0／0 | 2／31 | 14／119 | 4／24 |
| TensorCotensor | 33／179 | 0／0 | 0／0 | 0／0 |
| Simplicial | 0／0 | 0／0 | 4／17 | 0／0 |
| 合計 | 33／179 | 7／72 | 37／442 | 43／296 |

型案は71宣言（一般論 A・B 48、C-軽13、試験とスペクトル10）。このうち7は表にある改名・置換先なので、改名を除く追加の入口は64件。証明行は、既存補題を使える部分と、転置の自然性・モノイダル整合・等化子を新たに証明する部分を分けて見積もった。下表の行には型と証明を含む。局所補題を数え上げる前の幅で、移す既存の442行は含めない。

| 次段以降の作業 | 型案の件数（改名を含む） | 実装行の見込み |
| --- | ---: | ---: |
| 段3a　A2・A3・B3。元の通常圏上の基底変更、作用からの豊穣化、随伴つきテンソル・余テンソル。一般補題の移動と単体的補題の分離 | 16 | 150–260 |
| 段3b　B1。結合・単位の入力と二つの右随伴比較、係数自然性と単位点、A3 側の適用 | 9 | 220–400 |
| 段3c　B2・B4、B2 側の B1 の入力。右随伴の mate、作用との比較と二つの転置 | 23 | 210–400 |
| 段3d　基点付き単体集合。基点付加のモノイダル整合と現行の忘却による豊穣化との照合 | 4 | 90–180 |
| 段4　スペクトルの自由第0段、相対テンソルと各段の表示 | 6 | 100–230 |
| 段5　C-軽。充満部分圏、対と挿入、等化子と評価、可表 Hom | 13 | 220–420 |

合計は990–1,890行の設計見積もり。上表で消える旧宣言は43件・296行。一般論の中の新しい整合の証明を一度置き、段4の利用側から移せるスペクトル固有でない宣言は、実装時に旧転置・生成子の照合を経て取り除く。この行数にはスペクトル利用側の削減を加算していない。

[SU-W1 段14a の58件](../spectra/stage14-types.md) は次の単位で引き継ぐ。

| 旧案 | 件数 | EN-W1 での置き方 |
| --- | ---: | --- |
| 作用の結合、評価則、通常圏の組立て、Hom の両変数の射 | 13 | A3 に継承。評価則と whiskering は `ofAction` と `ofActionHomIso` の証明に使う |
| テンソル・余テンソルの構造と写像対象への転置 | 2 | B3 の二つの型に継承 |
| 比較随伴・右随伴比較、係数・原変数・単位の転置則、Hom の二変数同型と `EnrichedRepresentability` | 34 | B1 に継承。作用のデータで直接書いていた式は `TensorAssociativity` と `TensorCotensor` で述べ、必要な補題を内部で使う |
| 各段の加群テンソルの表示6件、列の pairing 2件、零対象1件 | 9 | 各段の表示は段4の資料。列の pairing と零対象の配置は一般の豊穣化の入口から独立 |

段3の最後は基点付き単体集合の写像対象、通常射・単位・合成と二つの転置の照合。スペクトルの利用側切り替えは段4、dg と SSet の C-軽の適用は段5。SU-W1 段14の実装保留をこの設計で解除しない。

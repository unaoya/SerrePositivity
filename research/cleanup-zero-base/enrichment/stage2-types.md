# EN-W1 段2b　閉じた加群からの豊穣化

main `bfc902136` を取り込んだ `abc86598b` と固定 Mathlib `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6` を基準にした型案。文献の略号、番号、実装の順は [文献対応表](../../../formalization-plans/stage-ii/consolidation/enrichment-literature-map.md) に従う。型ブロックは実装時の署名。文献番号のコメントは次の番号コメントまでの宣言にかかる。既存の `TensorCotensor` と `EnrichedRepresentability` は `SerrePositivity.Enriched` の型を指す。「補助」は原典に単独の宣言として対応する項目がないことを表す。

## 1. 基準の構造と A3・B3（OfAction.lean）

`ClosedModule V M` は既存の通常圏 M と選んだ左作用 `[MonoidalLeftAction V M]` 上のデータ付きクラス。Mathlib の `MonoidalClosed` と同様に、閉性を追加する。左作用は H 4.1.6 の右作用を読み替え、二つの随伴は H 4.1.12 と同じデータを別々の `ParametrizedAdjunction` に分ける。基底の閉性は後の V 値の表現に課す。V での Hom を作る段は組紐で足りる。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory Opposite
open SerrePositivity.Enriched
universe u v w z
variable {V : Type u} {M : Type w} [Category.{v} V] [Category.{z} M]
  [MonoidalCategory V]

-- R 10.1.3、H 4.1.6・4.1.12。H は右作用。
class ClosedModule (V : Type u) (M : Type w) [Category.{v} V] [Category.{z} M]
    [MonoidalCategory V] [MonoidalLeftAction V M] where
  cotensor : Vᵒᵖ ⥤ M ⥤ M
  mapping : Mᵒᵖ ⥤ M ⥤ V
  cotensorAdj : MonoidalLeftAction.curriedAction V M ⊣₂ cotensor
  mappingAdj : (MonoidalLeftAction.curriedAction V M).flip ⊣₂ mapping

variable [MonoidalLeftAction V M]
variable (L : ClosedModule V M)
local notation "T" => MonoidalLeftAction.curriedAction V M
local notation "R[" L "]" => @ClosedModule.mapping V M _ _ _ _ L
local notation "evHom[" L "]" => fun X Y : M => Functor.obj (Functor.obj (R[L]) (op X)) Y

-- R 10.1.4 の余単位による構成。比較の値を固定する補助。
def actionEvaluation (L : ClosedModule V M) (X Y : M) :
    ((T).obj (evHom[L] X Y)).obj X ⟶ Y
-- R 10.1.4、3.4.9 の証明の単位式を作用に適用。
def actionUnit (L : ClosedModule V M) (X : M) : 𝟙_ V ⟶ evHom[L] X X
-- R 10.1.4、3.4.9 の証明の (3.4.11) を作用に適用。
def actionHomEquiv (L : ClosedModule V M) (X Y : M) : (X ⟶ Y) ≃ (𝟙_ V ⟶ evHom[L] X Y)

variable [BraidedCategory V]

-- R 10.1.4、(3.3.8) と (3.4.6) の合成を図式順にする。
def actionComposition (L : ClosedModule V M) (X Y Z : M) :
    evHom[L] X Y ⊗ evHom[L] Y Z ⟶ evHom[L] X Z
-- R 10.1.4、K (1.3)、H 4.1.6 の四重の整合。
lemma actionComposition_assoc (L : ClosedModule V M) (W X Y Z : M) :
    (actionComposition L W X Y ▷ evHom[L] Y Z) ≫ actionComposition L W Y Z =
      (α_ (evHom[L] W X) (evHom[L] X Y) (evHom[L] Y Z)).hom ≫
        (evHom[L] W X ◁ actionComposition L X Y Z) ≫ actionComposition L W X Z
-- R 10.1.4 の前半。R 3.4.5 の通常射も固定。
@[instance_reducible] def ofAction (L : ClosedModule V M) : EnrichedOrdinaryCategory V M
-- 補助。R 10.1.4 の表示を現行 eHomFunctor に接続。
def ofActionHomIso (L : ClosedModule V M) :
    @eHomFunctor V _ _ M _ (ofAction L) ≅ R[L]
-- R 10.1.4、H 4.1.12。B3 の忘却。
def ofActionTensorCotensor (L : ClosedModule V M) :
    @TensorCotensor V _ _ M _ (ofAction L)
```

評価は `(L.mappingAdj.adj X).counit.app Y`。作用の単位の順射を `L.mappingAdj.adj X` で転置して単位を作る。通常射の同値は、作用単位子の順射で前合成して同じ随伴で転置する。合成は $M(X,Y)⊗M(Y,Z)$ を $M(Y,Z)⊗M(X,Y)$ に組紐で交換し、作用に入れてから作用の結合子の順射で $T(M(Y,Z),T(M(X,Y),X))$ に移す。二つの評価を順に合成し、転置する。A3 の結合律は随伴で両辺を戻し、評価の自然性、組紐の六角形、作用の四重の整合を使う。この手順は `ReverseComposition` で合成を図式順に移す。作用での評価則は `OfAction` で随伴の余単位と作用の整合から示す。B3 のテンソルは外から渡した作用関手、余テンソルは L の欄の値。Hom 側だけ、成分が恒等の `ofActionHomIso` の逆に沿って随伴を輸送する。点の転置の一致はこの恒等成分と上記の通常射の式で従う。

### 五角形を使う範囲と忘却の選択

| 入力 | B1 の係数自然性二つ | B1 の単位点の一致二つ | A3 の結合律 |
| --- | --- | --- | --- |
| 既存の通常豊穣圏、`TensorCotensor`、自然な結合子と `unitIso` との左右の整合（段2 `TensorAssociativity`） | 示せる。結合子の係数自然性、組紐・閉随伴の自然性 | 示せる。列を単位で評価し、左右の単位図式と `unitMap_comp` を使う | 一般には示せない。作用の四重の整合がない |
| `ClosedModule`（`MonoidalLeftAction` ＋随伴二つ） | 示せる。作用結合子は三変数に自然 | 示せる。作用単位子が B3 の `unitIso` と一致する | 示せる。評価後の二経路は作用の五角形 |

五角形の差は、例えば整数次数付きの ℚ ベクトル空間の自己作用で見える。通常の結合子に、三つの純次数がすべて 1 の成分だけ係数 2 を掛ける。これは次数保存の射に自然で、単位が次数 0 なので左右単位を保つ。同じテンソル・余テンソル・通常随伴を使える。純次数 0、1、2、3 の一次元空間を順に取り、各隣接 Hom の次数 1 の生成元を合成する。最初の二射の合成を先に取る場合には、元の対象の次数が 0 で、さらに係数の一方が 2 次になってから第三の射を合成する。後の二射を先に取る場合には、二係数と作用先がすべて 1 次の箇所が一度現れる。得られる二つの合成は係数 2 だけ異なる。従って既存の豊穣圏を前提とする B1 の弱い仮定で、その作用から A3 の豊穣圏を新たに生成することはできない。結合子も無い場合は、三元鎖 $0<a<1$ を $a⊗a=0$、単位 $1$、ゼロ吸収の閉対称モノイダル圏にする。二元鎖を、順序が成り立つ Hom を 1、残りを 0 として豊穣化する。係数 0 のテンソルは最小元、余テンソルは最大元への定値関手。それ以外の係数は恒等関手。通常随伴は両方作れるが、$P=a$、$X=\mathrm{max}$、$Y=\mathrm{min}$ で二つの豊穣 Hom は 0、$[a,0]=a$。

**提案**　閉じた加群を供給口にし、`TensorCotensor` は B3 で取り出せる随伴の部分として残す。既に選んだ豊穣化を保つ利用側には下記の兼ね合いを束ねる入口を使える。テンソルを二重に選ぶ API にはせず、作用からのテンソルと既存のテンソルを自然同型でつなぐ。単位子も B3 が決める単位と揃える。定義的に一致しない現行の作用の表示には、作用を自然同型に沿って輸送してからこの入口を使う。

```lean
-- OfAction の文脈。補助。既存の通常豊穣化を固定する移行口。
structure ClosedModuleOn (V : Type u) (M : Type w) [Category.{v} V] [Category.{z} M]
    [MonoidalCategory V] [MonoidalLeftAction V M] [EnrichedOrdinaryCategory V M] where
  adjunctions : TensorCotensor V M
  tensorIso : MonoidalLeftAction.curriedAction V M ≅ adjunctions.tensor
  unit_hom_app (X : M) :
    (tensorIso.hom.app (𝟙_ V)).app X ≫ adjunctions.unitIso.hom.app X =
      (MonoidalLeftAction.actionUnitNatIso V M).hom.app X

-- 補助。二つの随伴を tensorIso の逆に沿って作用へ移す。
def ClosedModuleOn.toClosedModule [EnrichedOrdinaryCategory V M] (L : ClosedModuleOn V M) :
    ClosedModule V M
-- 補助。A3・B3 の閉加群を、モデル圏を受ける入口へ渡す。
def ofActionClosedModuleOn [BraidedCategory V] (L : ClosedModule V M) :
    @ClosedModuleOn V M _ _ _ _ (ofAction L)
```

`ClosedModuleOn` は既存の豊穣化との標準比較が別途確定している利用側の入口。ここから `ClosedModule` の随伴の右辺を `eHomFunctor` として取り出せる。逆方向は `ofAction` の値を明示引数に渡す。B6 へ既存の豊穣化を持ち込むときは、単位と二つの随伴の一致に加え、B4 と同じ全 Hom の合成の比較を別途示す。閉じた加群を受ける公開のモデル圏 API はこの入口を使い、pushout-product の三つの言い方を扱う小さい補題は随伴部分で共有できる。移行の行数と吸収案との差は末尾の表に示す。

## 2. B1　Hom による全単射の列（TensorCotensor.lean）

B1 の検査は五角形を使わない旧入力と閉じた加群を並べる。任意の試験対象 A に対し、テンソル側は次の列を取る。

1. `V(A,Map(T P X,Y)) ≃ M(T A (T P X),Y)`（写像随伴の逆）。
2. `≃ M(T(A ⊗ P) X,Y)`（作用結合子の順射で前合成）。
3. `≃ V(A ⊗ P,Map(X,Y))`（写像随伴）。
4. `≃ V(P ⊗ A,Map(X,Y))`（`β(P,A).hom` で前合成）。
5. `≃ V(A,[P,Map(X,Y)])`（左テンソルの閉随伴）。

余テンソル側は `V(A,Map(X,Q P Y)) ≃ M(T A X,Q P Y) ≃ M(T P (T A X),Y) ≃ M(T(P ⊗ A) X,Y) ≃ V(P ⊗ A,Map(X,Y)) ≃ V(A,[P,Map(X,Y)])`。二番目は余テンソルの随伴の逆。左右で異なる順を通るため、組紐はテンソルの列の第4段に入れる。自然性は A の前合成、P の反変自然性、X の反変自然性、Y の共変自然性を取る。A=単位では、テンソル側は A を外す作用の左単位、余テンソル側は内側の右単位を使う。閉随伴と単位の比較では `curryHomEquiv'` を使い、四つの欄を既存の構造に入れる。

```lean
open CategoryTheory CategoryTheory.Functor CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory Opposite SerrePositivity.Enriched
universe u v w z
variable {V : Type u} {M : Type w} [Category.{v} V] [Category.{z} M]
  [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V] [EnrichedOrdinaryCategory V M]
variable (S : TensorCotensor V M)
local notation "t" => S.tensor
local notation "q" => S.cotensor
local notation "aHom" => fun X Y : M => @EnrichedCategory.Hom V _ _ M _ X Y

-- 補助。R 10.1.3 の結合と単位のうち B1 に要る部分。強い入口との比較専用。
structure TensorAssociativity where
  iso : bifunctorComp₁₂ (curriedTensor V) t ≅ bifunctorComp₂₃ t t
  leftUnit (P : V) (X : M) :
    (((iso.hom.app (𝟙_ V)).app P).app X) ≫ S.unitIso.hom.app (((t).obj P).obj X) =
      ((t).map (λ_ P).hom).app X
  rightUnit (P : V) (X : M) :
    (((iso.hom.app P).app (𝟙_ V)).app X) ≫ ((t).obj P).map (S.unitIso.hom.app X) =
      ((t).map (ρ_ P).hom).app X

-- R 10.1.4 の全単射の列。各 E の数字は上の列の段。
def actionTensorEquiv1 (A P : V) (X Y : M) :
    (A ⟶ aHom (((t).obj P).obj X) Y) ≃ ((((t).obj A).obj (((t).obj P).obj X)) ⟶ Y)
def actionTensorEquiv2 (a : TensorAssociativity S) (A P : V) (X Y : M) :
    ((((t).obj A).obj (((t).obj P).obj X)) ⟶ Y) ≃ (((t).obj (A ⊗ P)).obj X ⟶ Y)
def actionTensorEquiv3 (A P : V) (X Y : M) :
    (((t).obj (A ⊗ P)).obj X ⟶ Y) ≃ (A ⊗ P ⟶ aHom X Y)
def actionTensorEquiv4 (A P Z : V) : (A ⊗ P ⟶ Z) ≃ (P ⊗ A ⟶ Z)
def actionTensorEquiv5 (A P Z : V) : (P ⊗ A ⟶ Z) ≃ (A ⟶ (ihom P).obj Z)
-- R 10.1.4、3.7.3・3.7.4。余テンソル列の 1–4。
def actionCotensorEquiv1 (A P : V) (X Y : M) :
    (A ⟶ aHom X (((q).obj (op P)).obj Y)) ≃ (((t).obj A).obj X ⟶ ((q).obj (op P)).obj Y)
def actionCotensorEquiv2 (A P : V) (X Y : M) :
    (((t).obj A).obj X ⟶ ((q).obj (op P)).obj Y) ≃ ((((t).obj P).obj (((t).obj A).obj X)) ⟶ Y)
def actionCotensorEquiv3 (a : TensorAssociativity S) (A P : V) (X Y : M) :
    ((((t).obj P).obj (((t).obj A).obj X)) ⟶ Y) ≃ (((t).obj (P ⊗ A)).obj X ⟶ Y)
def actionCotensorEquiv4 (A P : V) (X Y : M) :
    (((t).obj (P ⊗ A)).obj X ⟶ Y) ≃ (P ⊗ A ⟶ aHom X Y)

-- R 3.5.12、10.1.4。各段で試験射 f の前合成と可換。
lemma actionTensorEquiv1_test {A A' : V} (f : A' ⟶ A) (P : V) (X Y : M)
    (g : A ⟶ aHom (((t).obj P).obj X) Y) :
    actionTensorEquiv1 S A' P X Y (f ≫ g) =
      ((t).map f).app (((t).obj P).obj X) ≫ actionTensorEquiv1 S A P X Y g
lemma actionTensorEquiv2_test (a : TensorAssociativity S) {A A' : V} (f : A' ⟶ A)
    (P : V) (X Y : M) (g : ((t).obj A).obj (((t).obj P).obj X) ⟶ Y) :
    actionTensorEquiv2 S a A' P X Y (((t).map f).app (((t).obj P).obj X) ≫ g) =
      ((t).map (f ▷ P)).app X ≫ actionTensorEquiv2 S a A P X Y g
lemma actionTensorEquiv3_test {A A' : V} (f : A' ⟶ A) (P : V) (X Y : M)
    (g : ((t).obj (A ⊗ P)).obj X ⟶ Y) :
    actionTensorEquiv3 S A' P X Y (((t).map (f ▷ P)).app X ≫ g) =
      (f ▷ P) ≫ actionTensorEquiv3 S A P X Y g
lemma actionTensorEquiv4_test {A A' : V} (f : A' ⟶ A) (P Z : V) (g : A ⊗ P ⟶ Z) :
    actionTensorEquiv4 A' P Z ((f ▷ P) ≫ g) = (P ◁ f) ≫ actionTensorEquiv4 A P Z g
lemma actionTensorEquiv5_test {A A' : V} (f : A' ⟶ A) (P Z : V) (g : P ⊗ A ⟶ Z) :
    actionTensorEquiv5 A' P Z ((P ◁ f) ≫ g) = f ≫ actionTensorEquiv5 A P Z g
lemma actionCotensorEquiv1_test {A A' : V} (f : A' ⟶ A) (P : V) (X Y : M)
    (g : A ⟶ aHom X (((q).obj (op P)).obj Y)) :
    actionCotensorEquiv1 S A' P X Y (f ≫ g) = ((t).map f).app X ≫ actionCotensorEquiv1 S A P X Y g
lemma actionCotensorEquiv2_test {A A' : V} (f : A' ⟶ A) (P : V) (X Y : M)
    (g : ((t).obj A).obj X ⟶ ((q).obj (op P)).obj Y) :
    actionCotensorEquiv2 S A' P X Y (((t).map f).app X ≫ g) =
      ((t).obj P).map (((t).map f).app X) ≫ actionCotensorEquiv2 S A P X Y g
lemma actionCotensorEquiv3_test (a : TensorAssociativity S) {A A' : V} (f : A' ⟶ A)
    (P : V) (X Y : M) (g : ((t).obj P).obj (((t).obj A).obj X) ⟶ Y) :
    actionCotensorEquiv3 S a A' P X Y (((t).obj P).map (((t).map f).app X) ≫ g) =
      ((t).map (P ◁ f)).app X ≫ actionCotensorEquiv3 S a A P X Y g
lemma actionCotensorEquiv4_test {A A' : V} (f : A' ⟶ A) (P : V) (X Y : M)
    (g : ((t).obj (P ⊗ A)).obj X ⟶ Y) :
    actionCotensorEquiv4 S A' P X Y (((t).map (P ◁ f)).app X ≫ g) =
      (P ◁ f) ≫ actionCotensorEquiv4 S A P X Y g

-- R 10.1.4、R 3.5.12 の方法。試験対象 A を変えた二つの前層。
def tensorHomEquivChain (a : TensorAssociativity S) (A P : V) (X Y : M) :
    (A ⟶ aHom (((t).obj P).obj X) Y) ≃ (A ⟶ (ihom P).obj (aHom X Y))
def cotensorHomEquivChain (a : TensorAssociativity S) (A P : V) (X Y : M) :
    (A ⟶ aHom X (((q).obj (op P)).obj Y)) ≃ (A ⟶ (ihom P).obj (aHom X Y))

-- R 3.5.12。各段の前合成についての等式を貼る。
lemma tensorHomEquivChain_test (a : TensorAssociativity S) {A A' : V} (f : A' ⟶ A)
    (P : V) (X Y : M) (g : A ⟶ aHom (((t).obj P).obj X) Y) :
    tensorHomEquivChain S a A' P X Y (f ≫ g) = f ≫ tensorHomEquivChain S a A P X Y g
lemma cotensorHomEquivChain_test (a : TensorAssociativity S) {A A' : V} (f : A' ⟶ A)
    (P : V) (X Y : M) (g : A ⟶ aHom X (((q).obj (op P)).obj Y)) :
    cotensorHomEquivChain S a A' P X Y (f ≫ g) = f ≫ cotensorHomEquivChain S a A P X Y g

-- R 3.5.12 の通常米田。左の表現対象 D と右の表現対象 E の同型を返す。
def isoOfHomEquivChain {D E : V} (hom : ∀ A : V, (A ⟶ D) ≃ (A ⟶ E))
    (natural : ∀ {A A' : V} (f : A' ⟶ A) (g : A ⟶ D),
      hom A' (f ≫ g) = f ≫ hom A g) : D ≅ E

-- R 3.7.2・3.7.3、10.1.4、K (3.44)・(3.42)。米田で得る値。
def tensorHomIsoOfAssoc (a : TensorAssociativity S) (P : V) :
    tensorEnrichedHom S P ≅ powerHom (C := M) P
def cotensorHomIsoOfAssoc (a : TensorAssociativity S) (P : V) :
    cotensorEnrichedHom S P ≅ powerHom (C := M) P

-- R 3.7.2・3.7.3 の係数自然性。各列の P の自然性を米田で読む。
lemma tensorHomIsoOfAssoc_parameter (a : TensorAssociativity S) {P P' : V} (p : P ⟶ P') (X Y : M) :
    eHomWhiskerRight V (((t).map p).app X) Y ≫ ((tensorHomIsoOfAssoc S a P).hom.app (op X)).app Y =
      ((tensorHomIsoOfAssoc S a P').hom.app (op X)).app Y ≫ (MonoidalClosed.pre p).app (aHom X Y)
lemma cotensorHomIsoOfAssoc_parameter (a : TensorAssociativity S) {P P' : V} (p : P ⟶ P') (X Y : M) :
    eHomWhiskerLeft V X (((q).map p.op).app Y) ≫ ((cotensorHomIsoOfAssoc S a P).hom.app (op X)).app Y =
      ((cotensorHomIsoOfAssoc S a P').hom.app (op X)).app Y ≫ (MonoidalClosed.pre p).app (aHom X Y)

-- R 10.1.4 の随伴への制限。単位への評価。
lemma tensorHomIsoOfAssoc_points (a : TensorAssociativity S) (P : V) (X Y : M)
    (f : ((t).obj P).obj X ⟶ Y) :
    (MonoidalClosed.curryHomEquiv' (X := P) (Y := aHom X Y)).symm
      (eHomEquiv V f ≫ ((tensorHomIsoOfAssoc S a P).hom.app (op X)).app Y) = S.tensorHomEquiv P X Y f
lemma cotensorHomIsoOfAssoc_points (a : TensorAssociativity S) (P : V) (X Y : M)
    (f : X ⟶ ((q).obj (op P)).obj Y) :
    (MonoidalClosed.curryHomEquiv' (X := P) (Y := aHom X Y)).symm
      (eHomEquiv V f ≫ ((cotensorHomIsoOfAssoc S a P).hom.app (op X)).app Y) = S.cotensorHomEquiv P X Y f
```

```lean
-- OfAction の文脈に戻る。
variable [MonoidalClosed V]

-- 補助。H 4.1.6 の作用から弱い B1 入力への比較。
def ofActionTensorAssociativity (L : ClosedModule V M) :
    letI := ofAction L
    TensorAssociativity (ofActionTensorCotensor L)
-- R 10.1.4 後半、3.7.4。上の実同型と四つの法則を返す。
def ofClosedModuleRepresentability (L : ClosedModule V M) :
    letI := ofAction L
    EnrichedRepresentability (ofActionTensorCotensor L)
```

段3b では、弱い入力を検証用の内側に置き、公開の `ofClosedModuleRepresentability` は閉じた加群を取る。 `Yoneda.fullyFaithful` により A を動かした前層同型から対象の同型を定義する。X・Y の自然性は写像随伴と余テンソル随伴の当該変数の自然性であり、構成した同型の自然性として束ねる。同型とその単位点での揃い方が、B4 で用いる一意性の比較を固定する。

## 3. A2・B2・B4　任意の閉じた U 加群の基底変更

A2 は R 3.4.3 の lax モノイダル関手で Hom を運ぶ。元の通常圏を保つには、単位の lax 射で得る点の写像が全単射であることを要求する。固定版の `TransportEnrichment.enrichedOrdinaryCategory` は対象別名が定義的に透過で、同じ対象型・通常圏を返す入口に使える。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
universe u v w z x y
variable {V : Type u} {U : Type w} {M : Type x}
  [Category.{v} V] [Category.{z} U] [Category.{y} M]
  [MonoidalCategory V] [MonoidalCategory U] [EnrichedOrdinaryCategory U M]

-- R 3.4.3・3.4.5 と通常圏を保つ点の条件。
@[instance_reducible] def ordinaryBaseChange (G : U ⥤ V) [G.LaxMonoidal]
  (e : ∀ Z : U, (𝟙_ U ⟶ Z) ≃ (𝟙_ V ⟶ G.obj Z))
  (he : ∀ (Z : U) (f : 𝟙_ U ⟶ Z), e Z f = Functor.LaxMonoidal.ε G ≫ G.map f) :
    EnrichedOrdinaryCategory V M
-- 補助。R 3.4.3 を通常の二変数関手として読む。
def ordinaryBaseChangeHomIso (G : U ⥤ V) [G.LaxMonoidal]
  (e : ∀ Z : U, (𝟙_ U ⟶ Z) ≃ (𝟙_ V ⟶ G.obj Z))
  (he : ∀ (Z : U) (f : 𝟙_ U ⟶ Z), e Z f = Functor.LaxMonoidal.ε G ≫ G.map f) :
    letI := ordinaryBaseChange (M := M) G e he
    eHomFunctor V M ≅ eHomFunctor U M ⋙ (Functor.whiskeringRight M U V).obj G
```

### 一般の B2（MonoidalAdjunction.lean）

`[MonoidalLeftAction U M]` と `L : ClosedModule U M` を取る。戻り値は制限した作用と、その作用上の閉加群クラスの値を束ねた依存対。全体 instance には登録しない。作用は `F ⋙ T`。その結合子は `δ F`（強モノイダルの逆向きの比較）と L の結合子を合成して得る。単位は `η F` と L の単位。 `curriedActionMop` へ F を合成し `actionOfMonoidalFunctorToEndofunctorMop` で束ねる。余テンソルは `F.op ⋙ L.cotensor`、写像対象は `L.mapping ⋙ whiskeringRight(G)`。 `restrict` と `composeSecond` で二つの通常随伴を作り、新しい作用の関手に自然同型に沿って移す。通常の圏を保つ A2 の入力は `η F` で前合成して `d.homEquiv` を取る全単射。 `rightAdjointLaxMonoidal` の単位の定義から `ε G ≫ G.map f` に一致する。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory Opposite
open SerrePositivity.Enriched
universe u v w z x y
variable {V : Type u} {U : Type w} {M : Type x}
  [Category.{v} V] [Category.{z} U] [Category.{y} M]
  [MonoidalCategory V] [MonoidalCategory U]
  {F : V ⥤ U} {G : U ⥤ V} [F.Monoidal]
variable [MonoidalLeftAction U M]
local notation "T" => MonoidalLeftAction.curriedAction U M
local notation "Rm[" L "]" => fun X Y : M => Functor.obj (Functor.obj (@ClosedModule.mapping U M _ _ _ _ L) (op X)) Y
local notation "Qm[" L "]" => fun P : U => Functor.obj (@ClosedModule.cotensor U M _ _ _ _ L) (op P)
local notation "act" => F ⋙ T
local notation "GM[" L "]" => @ClosedModule.mapping U M _ _ _ _ L ⋙ Functor.obj (Functor.whiskeringRight M U V) G

-- R 3.7.11、H 4.1.14。閉加群の作用・随伴の制限。
@[instance_reducible] def restrictedAction (F : V ⥤ U) [F.Monoidal] (M : Type x)
    [Category.{y} M] [MonoidalLeftAction U M] : MonoidalLeftAction V M
-- 補助。結合・単位は比較を通して制限作用のもの。
def restrictedActionIso (F : V ⥤ U) [F.Monoidal] :
    @MonoidalLeftAction.curriedAction V M _ _ _ (restrictedAction F M) ≅ F ⋙ T
-- R 3.7.11 の通常随伴部分。U 側の閉加群 L は任意。
def restrictedCotensorAdj (F : V ⥤ U) (L : ClosedModule U M) :
    F ⋙ T ⊣₂ F.op ⋙ L.cotensor
def restrictedMappingAdj (d : F ⊣ G) (L : ClosedModule U M) :
    (act).flip ⊣₂ GM[L]
-- R 3.7.11、R 10.1.3、H 4.1.6（左に読み替える）。
def changeClosedModule (d : F ⊣ G) (L : ClosedModule U M) :
    Σ a : MonoidalLeftAction V M, @ClosedModule V M _ _ _ a

-- 補助。R 3.7.11 の mate と R 3.4.5 の点の条件。
def adjunctionPointEquiv (d : F ⊣ G) (Z : U) : (𝟙_ U ⟶ Z) ≃ (𝟙_ V ⟶ G.obj Z)
lemma adjunctionPointEquiv_apply (d : F ⊣ G) (Z : U) (f : 𝟙_ U ⟶ Z) :
    letI := d.rightAdjointLaxMonoidal
    adjunctionPointEquiv d Z f = Functor.LaxMonoidal.ε G ≫ G.map f

variable [BraidedCategory U]

-- R 3.4.3・3.7.11。G を Hom・単位・合成に適用。
@[instance_reducible] def changedOrdinary (d : F ⊣ G) (L : ClosedModule U M) :
    EnrichedOrdinaryCategory V M
-- 補助。R 3.7.11 の GM と Mathlib の関手の比較。各対象で恒等。
def changedHomIso (d : F ⊣ G) (L : ClosedModule U M) :
    letI := changedOrdinary d L
    eHomFunctor V M ≅ GM[L]
-- R 3.7.11、H 4.1.12。各随伴の値は F ⋙ T、F.op ⋙ Q、G R。
def changedTensorCotensor (d : F ⊣ G) (L : ClosedModule U M) :
    letI := changedOrdinary d L
    TensorCotensor V M
```

`changedOrdinary` は `ofAction L` に A2 を適用する。`changedTensorCotensor` は上の二つの制限随伴に `changedHomIso.symm` を使う。以下の B2 の独立な列で、この側にも `EnrichedRepresentability` を得る。ここまでは F の組紐保存を要しない。文献順の合成と Mathlib 順の合成の両方を比較する B4 と、B4 経由で A2 版を使う B6 の出力では組紐保存を明示する。

### B2 の全単射の列と米田

R 3.7.11 の式を `Equiv.trans` でつなぐ。左端は $V(A,G R(T(FP)X,Y))$、右端は $V(A,[P,G R(X,Y)])$。各段は次の型。余テンソル列は左端 $V(A,G R(X,Q(FP)Y))$ から最後の三段へ合流する。

| 段 | テンソルの表示と Lean の値 | 余テンソルの表示と Lean の値 | 自然性を与える法則 |
| --- | --- | --- | --- |
| 1 | $V(A,GZ) ≃ U(FA,Z)$、`changedHomAdjEquiv` | 同じ。Z の選び方が異なる | d の原変数・終変数の自然性 |
| 2 | $U(FA,R(T(FP)X,Y)) ≃ M(T(FA)(T(FP)X),Y)$、`changedTensorEquiv2` | $U(FA,R(X,Q(FP)Y)) ≃ M(T(FA)X,Q(FP)Y)$、`changedCotensorEquiv2` | `mappingAdj.homEquiv_naturality_one` と各随伴の自然性 |
| 3 | $M(T(FA)(T(FP)X),Y) ≃ M(T(FA⊗FP)X,Y)$、`changedTensorEquiv3` | $M(T(FA)X,Q(FP)Y) ≃ M(T(FP)(T(FA)X),Y)$、`changedCotensorEquiv3` | 作用結合子または `cotensorAdj` の自然性 |
| 4 | $M(T(FA⊗FP)X,Y) ≃ U(FA⊗FP,R(X,Y))$、`changedActionEquiv` | 結合子で前合成する `changedCotensorEquiv4`、続けて $M(T(FP⊗FA)X,Y) ≃ U(FP⊗FA,R(X,Y))$、`changedActionEquiv` | U の三変数の結合の自然性、写像随伴 |
| 5 | $U(FA⊗FP,Z) ≃ U(F(A⊗P),Z)$、`changedMonoidalEquiv` | $U(FP⊗FA,Z) ≃ U(F(P⊗A),Z)$、同じ関数の引数を交換 | `δ F` の二変数の自然性 |
| 6 | $U(F(A⊗P),Z) ≃ V(A⊗P,GZ)$、`changedHomAdjEquiv.symm` | $U(F(P⊗A),Z) ≃ V(P⊗A,GZ)$ | d の自然性 |
| 7 | V の組紐で前合成し $V(P⊗A,GZ)$ に移し、閉随伴で $V(A,[P,GZ])$ | $V(P⊗A,GZ)$ から閉随伴のみ | 組紐、閉随伴、`MonoidalClosed.pre` の自然性 |

```lean
-- 一般 B2 の文脈。
local notation "tx" => fun P : U => Functor.obj (T) P

-- R 3.7.11 の列の各段。
def changedHomAdjEquiv (d : F ⊣ G) (A : V) (Z : U) :
    (A ⟶ G.obj Z) ≃ (F.obj A ⟶ Z)
def changedTensorEquiv2 (L : ClosedModule U M) (A P : U) (X Y : M) :
    (A ⟶ Rm[L] ((tx P).obj X) Y) ≃ ((tx A).obj ((tx P).obj X) ⟶ Y)
def changedTensorEquiv3 (L : ClosedModule U M) (A P : U) (X Y : M) :
    ((tx A).obj ((tx P).obj X) ⟶ Y) ≃ ((tx (A ⊗ P)).obj X ⟶ Y)
def changedActionEquiv (L : ClosedModule U M) (P : U) (X Y : M) :
    ((tx P).obj X ⟶ Y) ≃ (P ⟶ Rm[L] X Y)
def changedCotensorEquiv2 (L : ClosedModule U M) (A P : U) (X Y : M) :
    (A ⟶ Rm[L] X ((Qm[L] P).obj Y)) ≃ ((tx A).obj X ⟶ (Qm[L] P).obj Y)
def changedCotensorEquiv3 (L : ClosedModule U M) (A P : U) (X Y : M) :
    ((tx A).obj X ⟶ (Qm[L] P).obj Y) ≃ ((tx P).obj ((tx A).obj X) ⟶ Y)
def changedCotensorEquiv4 (L : ClosedModule U M) (A P : U) (X Y : M) :
    ((tx P).obj ((tx A).obj X) ⟶ Y) ≃ ((tx (P ⊗ A)).obj X ⟶ Y)
def changedMonoidalEquiv (F : V ⥤ U) [F.Monoidal] (A P : V) (Z : U) :
    (F.obj A ⊗ F.obj P ⟶ Z) ≃ (F.obj (A ⊗ P) ⟶ Z)

-- R 3.7.11 の各段の自然性。U 内の段は F.map f に適用する。
lemma changedHomAdjEquiv_test (d : F ⊣ G) {A A' : V} (f : A' ⟶ A)
    (Z : U) (g : A ⟶ G.obj Z) :
    changedHomAdjEquiv d A' Z (f ≫ g) = F.map f ≫ changedHomAdjEquiv d A Z g
lemma changedHomAdjEquiv_target (d : F ⊣ G) (A : V) {Z Z' : U} (f : Z ⟶ Z')
    (g : A ⟶ G.obj Z) :
    changedHomAdjEquiv d A Z' (g ≫ G.map f) = changedHomAdjEquiv d A Z g ≫ f
lemma changedTensorEquiv2_test (L : ClosedModule U M) {A A' : U} (f : A' ⟶ A)
    (P : U) (X Y : M) (g : A ⟶ Rm[L] ((tx P).obj X) Y) :
    changedTensorEquiv2 L A' P X Y (f ≫ g) =
      ((T).map f).app ((tx P).obj X) ≫ changedTensorEquiv2 L A P X Y g
lemma changedTensorEquiv3_test (L : ClosedModule U M) {A A' : U} (f : A' ⟶ A)
    (P : U) (X Y : M) (g : (tx A).obj ((tx P).obj X) ⟶ Y) :
    changedTensorEquiv3 L A' P X Y (((T).map f).app ((tx P).obj X) ≫ g) =
      ((T).map (f ▷ P)).app X ≫ changedTensorEquiv3 L A P X Y g
lemma changedActionEquiv_test (L : ClosedModule U M) {P P' : U} (f : P' ⟶ P)
    (X Y : M) (g : (tx P).obj X ⟶ Y) :
    changedActionEquiv L P' X Y (((T).map f).app X ≫ g) = f ≫ changedActionEquiv L P X Y g
lemma changedCotensorEquiv2_test (L : ClosedModule U M) {A A' : U} (f : A' ⟶ A)
    (P : U) (X Y : M) (g : A ⟶ Rm[L] X ((Qm[L] P).obj Y)) :
    changedCotensorEquiv2 L A' P X Y (f ≫ g) =
      ((T).map f).app X ≫ changedCotensorEquiv2 L A P X Y g
lemma changedCotensorEquiv3_test (L : ClosedModule U M) {A A' : U} (f : A' ⟶ A)
    (P : U) (X Y : M) (g : (tx A).obj X ⟶ (Qm[L] P).obj Y) :
    changedCotensorEquiv3 L A' P X Y (((T).map f).app X ≫ g) =
      (tx P).map (((T).map f).app X) ≫ changedCotensorEquiv3 L A P X Y g
lemma changedCotensorEquiv4_test (L : ClosedModule U M) {A A' : U} (f : A' ⟶ A)
    (P : U) (X Y : M) (g : (tx P).obj ((tx A).obj X) ⟶ Y) :
    changedCotensorEquiv4 L A' P X Y ((tx P).map (((T).map f).app X) ≫ g) =
      ((T).map (P ◁ f)).app X ≫ changedCotensorEquiv4 L A P X Y g
lemma changedMonoidalEquiv_left (F : V ⥤ U) [F.Monoidal] {A A' : V} (f : A' ⟶ A)
    (P : V) (Z : U) (g : F.obj A ⊗ F.obj P ⟶ Z) :
    changedMonoidalEquiv F A' P Z ((F.map f ▷ F.obj P) ≫ g) =
      F.map (f ▷ P) ≫ changedMonoidalEquiv F A P Z g
lemma changedMonoidalEquiv_right (F : V ⥤ U) [F.Monoidal] (A : V) {P P' : V} (f : P' ⟶ P)
    (Z : U) (g : F.obj A ⊗ F.obj P ⟶ Z) :
    changedMonoidalEquiv F A P' Z ((F.obj A ◁ F.map f) ≫ g) =
      F.map (A ◁ f) ≫ changedMonoidalEquiv F A P Z g

-- R 3.7.11 の自然な列。A を動かして R 3.5.12 を適用。
variable [BraidedCategory V] [MonoidalClosed V]
local notation "tm" => fun P : V => tx (F.obj P)
local notation "cm[" L "]" => fun P : V => Qm[L] (F.obj P)
local notation "gr[" L "]" => fun X Y : M => Functor.obj G (Rm[L] X Y)
local notation "pw[" L "]" => fun P X Y => Functor.obj (ihom P) (gr[L] X Y)

def changedTensorHomChain (d : F ⊣ G) (L : ClosedModule U M) (A P : V) (X Y : M) :
    (A ⟶ gr[L] ((tm P).obj X) Y) ≃ (A ⟶ pw[L] P X Y)
def changedCotensorHomChain (d : F ⊣ G) (L : ClosedModule U M) (A P : V) (X Y : M) :
    (A ⟶ gr[L] X ((cm[L] P).obj Y)) ≃ (A ⟶ pw[L] P X Y)
lemma changedTensorHomChain_test (d : F ⊣ G) (L : ClosedModule U M)
    {A A' : V} (f : A' ⟶ A) (P : V) (X Y : M) (g : A ⟶ gr[L] ((tm P).obj X) Y) :
    changedTensorHomChain d L A' P X Y (f ≫ g) = f ≫ changedTensorHomChain d L A P X Y g
lemma changedCotensorHomChain_test (d : F ⊣ G) (L : ClosedModule U M)
    {A A' : V} (f : A' ⟶ A) (P : V) (X Y : M) (g : A ⟶ gr[L] X ((cm[L] P).obj Y)) :
    changedCotensorHomChain d L A' P X Y (f ≫ g) = f ≫ changedCotensorHomChain d L A P X Y g

-- R 3.7.11。米田で得る二つの Hom 関手の同型。
def changedTensorHomIso (d : F ⊣ G) (L : ClosedModule U M) (P : V) :
    letI := changedOrdinary d L
    tensorEnrichedHom (changedTensorCotensor d L) P ≅ powerHom (C := M) P
def changedCotensorHomIso (d : F ⊣ G) (L : ClosedModule U M) (P : V) :
    letI := changedOrdinary d L
    cotensorEnrichedHom (changedTensorCotensor d L) P ≅ powerHom (C := M) P

-- R 3.7.11。米田の同型から二つの欄と自然性・点の法則を組む。
def changedRepresentability (d : F ⊣ G) (L : ClosedModule U M) :
    letI := changedOrdinary d L
    EnrichedRepresentability (changedTensorCotensor d L)
```

A の自然性は各段の前合成に対する等式を順に連結する。P の自然性には F の合成保存・強モノイダル比較の二変数自然性を追加し、X・Y の自然性には L の随伴の二変数自然性と G の合成保存を使う。A を単位に取ったときは `η F` と `δ F` の左右単位図式を使い、それぞれ `restrictedMappingAdj` の転置と `restrictedCotensorAdj` の逆転置に一致させる。これで出力の四欄が固定される。 `changedTensorHomIso`・`changedCotensorHomIso` の成分は `isoOfHomEquivChain` に二つの列を入れて得る。これらを比較の四式とともに `changedRepresentability` に束ねる。

### 自己作用と B4（Comparison.lean）

U 自身への適用は `closedModuleSelf U` を L に入れる。写像随伴は Mathlib の閉随伴を組紐で右テンソルへ輸送する。A3 のこの自己作用の Hom 表示は、Mathlib の `MonoidalClosed.enrichedOrdinaryCategorySelf` と、対称な基底では単位・合成・点で一致する。自己作用での左テンソルと、右テンソルを左閉随伴に入れる組紐は向きを区別する。

```lean
-- 一般 B2 の文脈。
-- R 3.7.5、3.4.9、K §1.6。U の自己作用とその随伴。
def closedModuleSelf (U : Type w) [Category.{z} U] [MonoidalCategory U]
    [BraidedCategory U] [MonoidalClosed U] :
    @ClosedModule U U _ _ _ (selfLeftAction U)
-- R 3.4.9、K (1.28)。自己作用と Mathlib の自己豊穣の比較。
def closedModuleSelfHomIso (U : Type w) [Category.{z} U] [MonoidalCategory U]
    [SymmetricCategory U] [MonoidalClosed U] :
    @eHomFunctor U _ _ U _ (ofAction (closedModuleSelf U)) ≅
      @eHomFunctor U _ _ U _ (MonoidalClosed.enrichedOrdinaryCategorySelf U)

-- R 3.7.11 の U 自身への特殊化。
def changeSelfClosedModule [MonoidalClosed U] (d : F ⊣ G) :
    Σ a : MonoidalLeftAction V U, @ClosedModule V U _ _ _ a

```

B4 ではこの同型を使い、A3 側の合成は最初に V の `β`、A2 側は U の合成に含まれる U の `β` を通ることを比較する。 `F.Braided` により F の二項比較で移した二つの組紐が一致する。強モノイダル構造だけからその式は出ない。H 4.1.5 の直後の例では、通常の交換と Koszul 符号付き交換を備えた二つの整数次数付きベクトル空間の間で、恒等関手は強モノイダルだが、奇数次同士の組紐の比較式は落ちる。A3 と A2 の比較に使う指定の Hom 同型を保つには、この差を見落とせない。

B4 の補題は次の型。a と b はそれぞれ `@ofActionTensorCotensor V M _ _ _ (changeClosedModule d L).1 _ (changeClosedModule d L).2` と `changedTensorCotensor d L`。T と Q の二つの比較は `restrictedActionIso` と余テンソルの定義。以下で `hXY` は豊穣 Hom に取った成分。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory Opposite
open SerrePositivity.Enriched
universe u v w z x y
variable {V : Type u} {U : Type w} {M : Type x}
  [Category.{v} V] [Category.{z} U] [Category.{y} M]
  [MonoidalCategory V] [MonoidalCategory U] [BraidedCategory V] [BraidedCategory U]
  {F : V ⥤ U} {G : U ⥤ V} [F.Braided] [MonoidalLeftAction U M]

-- R 3.7.11 の定義と 10.1.4 の一意性の実装。対応する組紐を固定。
def changedActionHomIso (d : F ⊣ G) (L : ClosedModule U M) :
    @eHomFunctor V _ _ M _ (@ofAction V M _ _ _ (changeClosedModule d L).1 _ (changeClosedModule d L).2) ≅
      @eHomFunctor V _ _ M _ (changedOrdinary d L)
local notation "EA[" d "," L "]" => @ofAction V M _ _ _ (Sigma.fst (changeClosedModule d L)) _ (Sigma.snd (changeClosedModule d L))
local notation "EB[" d "," L "]" => changedOrdinary d L
local notation "SA[" d "," L "]" => @ofActionTensorCotensor V M _ _ _ (Sigma.fst (changeClosedModule d L)) _ (Sigma.snd (changeClosedModule d L))
local notation "SB[" d "," L "]" => changedTensorCotensor d L
local notation "TA[" d "," L "]" => @TensorCotensor.tensor V _ _ M _ (EA[d,L]) (SA[d,L])
local notation "TB[" d "," L "]" => @TensorCotensor.tensor V _ _ M _ (EB[d,L]) (SB[d,L])
local notation "QA[" d "," L "]" => @TensorCotensor.cotensor V _ _ M _ (EA[d,L]) (SA[d,L])
local notation "QB[" d "," L "]" => @TensorCotensor.cotensor V _ _ M _ (EB[d,L]) (SB[d,L])
local notation "hXY[" d "," L "]" => fun X Y : M =>
  NatTrans.app (NatTrans.app (Iso.hom (changedActionHomIso d L)) (op X)) Y

-- R 10.1.4 の一意性の成分、R 3.4.5 の点。
lemma changedActionHomIso_id (d : F ⊣ G) (L : ClosedModule U M) (X : M) :
    @eId V _ _ M (EnrichedOrdinaryCategory.toEnrichedCategory (self := EA[d,L])) X ≫ hXY[d,L] X X =
      @eId V _ _ M (EnrichedOrdinaryCategory.toEnrichedCategory (self := EB[d,L])) X
lemma changedActionHomIso_comp (d : F ⊣ G) (L : ClosedModule U M) (X Y Z : M) :
    @eComp V _ _ M (EnrichedOrdinaryCategory.toEnrichedCategory (self := EA[d,L])) X Y Z ≫
        hXY[d,L] X Z =
      (hXY[d,L] X Y ⊗ₘ hXY[d,L] Y Z) ≫
        @eComp V _ _ M (EnrichedOrdinaryCategory.toEnrichedCategory (self := EB[d,L])) X Y Z
lemma changedActionHomIso_points (d : F ⊣ G) (L : ClosedModule U M) {X Y : M} (f : X ⟶ Y) :
    (@eHomEquiv V _ _ M _ EA[d,L] X Y) f ≫ hXY[d,L] X Y =
      (@eHomEquiv V _ _ M _ EB[d,L] X Y) f

-- 補助。R 3.7.11 の表示を比較用に束ねる。
def changedActionTensorIso (d : F ⊣ G) (L : ClosedModule U M) : TA[d,L] ≅ TB[d,L]
def changedActionCotensorIso (d : F ⊣ G) (L : ClosedModule U M) : QA[d,L] ≅ QB[d,L]
-- R 10.1.4 の二つの転置、H 4.1.12。
lemma changedAction_tensorHom (d : F ⊣ G) (L : ClosedModule U M) (P : V) (X Y : M)
    (f : ((TB[d,L]).obj P).obj X ⟶ Y) :
    (@TensorCotensor.tensorHomEquiv V _ _ M _ EA[d,L] SA[d,L]) P X Y
        (((changedActionTensorIso d L).hom.app P).app X ≫ f) ≫ hXY[d,L] X Y =
      (@TensorCotensor.tensorHomEquiv V _ _ M _ EB[d,L] SB[d,L]) P X Y f
lemma changedAction_tensorCotensor (d : F ⊣ G) (L : ClosedModule U M) (P : V) (X Y : M)
    (f : ((TB[d,L]).obj P).obj X ⟶ Y) :
    (@TensorCotensor.tensorCotensorHomEquiv V _ _ M _ EA[d,L] SA[d,L]) P X Y
        (((changedActionTensorIso d L).hom.app P).app X ≫ f) ≫
      ((changedActionCotensorIso d L).hom.app (op P)).app Y =
        (@TensorCotensor.tensorCotensorHomEquiv V _ _ M _ EB[d,L] SB[d,L]) P X Y f
```

B4 では豊穣構造の等式の代わりに、Hom の二変数自然同型を固定する。単位は `η F` の mate、合成は `δ F` と二つの評価の mate、点は作用の単位で転置して比較する。二つの転置は随伴の輸送で同じ全単射になり、余テンソルから写像対象への転置はその合成で比較できる。使う側の具体的なレベル表示はこの比較を使う。

## 4. B6　閉じた加群の関手と V 随伴

`LinearFunctor.lean` を豊穣関手と比較する入口、`EnrichedAdjunction.lean` を随伴の入口とする。Mathlib の `Functor.LaxLeftLinear` の向き $v⊙F x→F(v⊙x)$ は R 10.1.5。その比較が可逆の場合の `Functor.LeftLinear`（右作用版は `Functor.RightLinear`）が H 4.1.7 の関手。 `Functor.OplaxLeftLinear` はテンソル側で矢印が逆の別の条件で、余テンソル比較には随伴で写す。Mathlib の `EnrichedFunctor` は豊穣 Hom の射と単位・合成の保存を持つ。その通常の関手を固定した比較は、以下の `EnrichedLift` で与える。

固定版の `EnrichedNatTrans.out` は `F.forget ⟶ G.forget` で、豊穣 Hom 全体の可換条件を課していない。 `GradedNatTrans` の単位中心対象での自然性が R 3.5.8、K §1.2 の条件に当たる。 `EnrichedCat.bicategory` と一般の `Bicategory.Adjunction` を組み合わせると単位点だけに自然な 2-セルを許す。そこで既存の通常圏で指定された単位・余単位に、豊穣 Hom 上の可換を陽に課す。通常の三角律は与えられた随伴が持つ。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
universe u v w z x y
variable {V : Type u} {M : Type w} {N : Type x}
  [Category.{v} V] [Category.{z} M] [Category.{y} N] [MonoidalCategory V]
  [EnrichedOrdinaryCategory V M] [EnrichedOrdinaryCategory V N]

-- R 3.5.1、K §1.2。補助の map_point で元の通常関手を固定する。
structure EnrichedLift (F : M ⥤ N) where
  map (X Y : M) : (X ⟶[V] Y) ⟶ (F.obj X ⟶[V] F.obj Y)
  map_id (X : M) : eId V X ≫ map X X = eId V (F.obj X)
  map_comp (X Y Z : M) :
    eComp V X Y Z ≫ map X Z =
      (map X Y ⊗ₘ map Y Z) ≫ eComp V (F.obj X) (F.obj Y) (F.obj Z)
  map_point {X Y : M} (f : X ⟶ Y) : eHomEquiv V f ≫ map X Y = eHomEquiv V (F.map f)

-- R 3.5.1。Mathlib の既存の V 関手へ。
def EnrichedLift.toEnrichedFunctor {F : M ⥤ N} (l : EnrichedLift (V := V) F) :
    EnrichedFunctor V M N

-- 補助。V 関手の恒等と合成で通常関手も固定。
def EnrichedLift.id (M : Type w) [Category.{z} M] [EnrichedOrdinaryCategory V M] :
    EnrichedLift (V := V) (𝟭 M)
def EnrichedLift.comp {P : Type*} [Category P] [EnrichedOrdinaryCategory V P]
    {F : M ⥤ N} {G : N ⥤ P}
    (l : EnrichedLift (V := V) F) (r : EnrichedLift (V := V) G) :
    EnrichedLift (V := V) (F ⋙ G)

-- R 3.5.8、K §1.2 (1.7)。全豊穣 Hom 上の条件。
def IsEnrichedNat {F G : M ⥤ N} (l : EnrichedLift (V := V) F) (r : EnrichedLift (V := V) G)
    (α : F ⟶ G) : Prop
lemma isEnrichedNat_iff {F G : M ⥤ N} (l : EnrichedLift (V := V) F) (r : EnrichedLift (V := V) G)
    (α : F ⟶ G) :
    IsEnrichedNat l r α ↔ ∀ X Y : M,
      l.map X Y ≫ eHomWhiskerLeft V (F.obj X) (α.app Y) =
        r.map X Y ≫ eHomWhiskerRight V (α.app X) (G.obj Y)

-- R 3.5.14、K §1.11。d.unit と d.counit を固定した V 随伴。
structure EnrichedAdjunctionOver {F : M ⥤ N} {G : N ⥤ M} (d : F ⊣ G) where
  leftLift : EnrichedLift (V := V) F
  rightLift : EnrichedLift (V := V) G
  unit_enriched : IsEnrichedNat (EnrichedLift.id (V := V) M) (leftLift.comp rightLift) d.unit
  counit_enriched : IsEnrichedNat (rightLift.comp leftLift) (EnrichedLift.id (V := V) N) d.counit

-- R 3.5.14、K (1.51)。Hom 側は二変数の普通の自然同型として表示。
-- 豊穣自然性は上の厳密な単位・余単位から、全 Hom 上で従う。
def enrichedAdjunctionHomIso {F : M ⥤ N} {G : N ⥤ M} {d : F ⊣ G}
    (e : EnrichedAdjunctionOver (V := V) d) :
    F.op ⋙ eHomFunctor V N ≅ eHomFunctor V M ⋙ (Functor.whiskeringLeft N M V).obj G
```

Hom の順射は左の Hom に `rightLift.map` を適用し、通常の単位の豊穣点で前合成。逆射は `leftLift.map` を適用し余単位の点で後合成する。両辺が恒等になるのは全 Hom 自然性と通常の三角律による。通常射への制限は d の転置。左右の豊穣自然性は同じ四角と豊穣合成の結合律から得る。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
universe u v w z x y
variable {V : Type u} {M : Type w} {N : Type x} [Category.{v} V] [Category.{z} M] [Category.{y} N]
  [MonoidalCategory V] [BraidedCategory V]
  [MonoidalLeftAction V M] [MonoidalLeftAction V N]
  (L : ClosedModule V M) (K : ClosedModule V N)

-- R 10.1.5。H 4.1.7 は LeftLinear に限定した場合。
def leftLinearEnrichedEquiv (L : ClosedModule V M) (K : ClosedModule V N) (F : M ⥤ N) :
    F.LaxLeftLinear V ≃ @EnrichedLift V M N _ _ _ _ (ofAction L) (ofAction K) F

-- R 3.7.10、10.1.6 の余テンソル比較。任意の V 関手では一般に射。
def cotensorLineator (L : ClosedModule V M) (K : ClosedModule V N) (G : N ⥤ M) :
    @EnrichedLift V N M _ _ _ _ (ofAction K) (ofAction L) G →
      (∀ (P : V) (Y : N), G.obj ((K.cotensor.obj (op P)).obj Y) ⟶
        (L.cotensor.obj (op P)).obj (G.obj Y))

-- R 3.7.10 (i)↔(ii)、H 4.1.7。比較は上の同値で定まるもの。
def enrichedAdjunctionLeftEquiv (L : ClosedModule V M) (K : ClosedModule V N)
    {F : M ⥤ N} {G : N ⥤ M} (d : F ⊣ G) :
    @EnrichedAdjunctionOver V M N _ _ _ _ (ofAction L) (ofAction K) F G d ≃ F.LeftLinear V

-- R 3.7.10 (i)↔(iii)、10.1.6。右側は V 関手と指定の比較の可逆性。
def enrichedAdjunctionRightEquiv (L : ClosedModule V M) (K : ClosedModule V N)
    {F : M ⥤ N} {G : N ⥤ M} (d : F ⊣ G) :
    @EnrichedAdjunctionOver V M N _ _ _ _ (ofAction L) (ofAction K) F G d ≃
      { r : @EnrichedLift V N M _ _ _ _ (ofAction K) (ofAction L) G // ∀ (P : V) (Y : N), IsIso (cotensorLineator L K G r P Y) }
```

R 10.1.5 の順方向は $v→M(X,v⊙X)→N(FX,F(v⊙X))$ を転置する。逆方向は $M(X,Y)⊙FX→F(M(X,Y)⊙X)→FY$ を転置する。単位では `μₗ_unitality`、二つの合成では `μₗ_associativity` と評価の自然性を使い、随伴の三角律で互いに逆にする。H 4.1.7 の加群自然変換は、この比較を通常の自然変換で横切る正方形と `IsEnrichedNat` の同値として扱う。

R 3.7.10 の左から作る方向では、任意の A に対する $V(A,N(FX,Y)) ≃ N(A⊙FX,Y) ≃ N(F(A⊙X),Y) ≃ M(A⊙X,GY) ≃ V(A,M(X,GY))$ を通常の米田で対象同型にする。可逆な比較は F の既存の豊穣関手から定まるものを使う。右から作る方向は余テンソルと同じ転置。単位点では d の同値に一致する。随伴の単位・余単位の豊穣自然性は、全 Hom 上の正方形を随伴で移して lineator の自然性・整合と三角律に帰着する。逆向きは対象同型を用いて同じ列を逆にたどり、通常の Hom の米田で指定の比較が可逆だと示す。余テンソル比較は対応する普遍評価の像で固定する。任意に選んだ対象同型だけではこの判定の入力にならない。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
universe u v w z
variable {V : Type u} {U : Type w} [Category.{v} V] [Category.{z} U]
  [MonoidalCategory V] [MonoidalCategory U] [BraidedCategory V] [BraidedCategory U]
  [MonoidalClosed V] [MonoidalClosed U] {F : V ⥤ U} {G : U ⥤ V} [F.Monoidal]

-- R 3.7.12。F の左 lineator はモノイダル比較。
def monoidalAdjunctionLeftLinear (d : F ⊣ G) :
    letI := (changeSelfClosedModule d).1
    F.LeftLinear V
-- R 3.7.12、K §1.11。制限作用から作る豊穣化での V 随伴。
def monoidalAdjunctionEnriched (d : F ⊣ G) :
    @EnrichedAdjunctionOver V V U _ _ _ _ (ofAction (closedModuleSelf V))
      (@ofAction V U _ _ _ (changeSelfClosedModule d).1 _ (changeSelfClosedModule d).2) F G d

variable [SymmetricCategory V] [SymmetricCategory U]

-- F.Monoidal の代わりに F.Braided からモノイダル構造も選ぶ。
omit [F.Monoidal] in
-- R 3.7.12 を右随伴による基底変更側で読む。B4 の組紐保存を使用。
def monoidalAdjunctionEnrichedTransport [F.Braided] (d : F ⊣ G) :
    @EnrichedAdjunctionOver V V U _ _ _ _ (MonoidalClosed.enrichedOrdinaryCategorySelf V)
      (changedOrdinary d (closedModuleSelf U)) F G d
```

ここで F の比較は $F(v)⊗F(x)→F(v⊗x)$。強モノイダル性で可逆、自然性と整合は F の公理による。制限作用で作った豊穣化にはこの比較を直接使って R 3.7.10 を適用できる。G で U の豊穣化を輸送した表示では B4 の Hom の同型で単位・余単位ごと移す。さらに R 3.7.12 の列では、$[Fv,u]_U$ を使う B2 の写像随伴、F の二項比較、V の閉随伴の順にとれば、右側の写像対象が $[v,Gu]_V$ になる。

### スペクトルの適用先

[stage14.csv](../spectra/stage14.csv) の `b6` 欄に、全149行を照合して該当先を印した。通常射の前後合成の五行は、直ちに任意の豊穣射の自然性を主張するものではなく、R 10.1.5 で構成した関手を既存の通常関手と照合する B6 の点での式である。加えて写像随伴と転置の六行に、B6 の固定原対象での V 随伴の通常の式になることを記した。 `simplicialLoopNatIso` は今は通常の右随伴の一意性。B6 で比較まで運ぶには、選んだ二つの懸垂の左 lineator と比較の整合を先に示す。表にない `suspensionLoopAdjunction`、`simplicialSuspensionNatIso`、`freeAtAdjunction n` は行を追加せず、次の適用の入口として扱う。 `F₀` は R 3.7.12。 `Fₙ`（任意の n）は強モノイダル性から推論せず、$P⊙FₙX≅Fₙ(P⊗X)$ を自由生成子で、`Evₙ` の余テンソルとの両立は段の表示で確認する。懸垂では係数と円周の順を組紐で移す線形性が必要で、導来随伴の比較には別に Quillen 条件が要る。

## C-軽　部分圏・対・関手圏・表現可能な Hom

### `FullSubcategory.lean` と `Product.lean`

部分圏の Hom は元の Hom。通常圏がある場合は Mathlib の `ObjectProperty.FullSubcategory` の既存の構造を使う。別の Hom 表示との比較は `Iso.eHomCongr` を使う。対は成分ごとの `V × V` 豊穣を `MonoidalCategory.tensor V` に沿って輸送する。固定対象を入れる挿入は、固定側の単位射と対象ごとの単位子で作る。通常の直積圏の射との比較は、単位からの射が二つの点に分かれる場合に使える。SSet のデカルト構造ではこの条件が成立する。 `EnrichedCat` の双圏構造を使え、ここでそのモノイダル構造を登録する必要はない。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory
universe u v w z
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  {D : Type w} {E : Type z} [EnrichedCategory V D] [EnrichedCategory V E]

-- K §1.2。
@[instance_reducible] def enrichedFullSubcategory (p : D → Prop) :
    EnrichedCategory V {X : D // p X}
def enrichedFullSubcategoryInclusion (p : D → Prop) :
    let : EnrichedCategory V {X : D // p X} := enrichedFullSubcategory (V := V) p
    EnrichedFunctor V {X : D // p X} D

variable [BraidedCategory V]

-- K §1.4 の対。二つの挿入は同じ対を使う補助。
@[instance_reducible] def tensorEnrichedCategory (D : Type w) (E : Type z)
    [EnrichedCategory V D] [EnrichedCategory V E] : EnrichedCategory V (D × E)
-- 補助。K §1.4 の対の片側を固定。
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

-- K §2.1 (2.2)、§2.2 (2.10)–(2.12)。
def enrichedFunctorHom (F G : EnrichedFunctor V D E) : V
def enrichedFunctorHomπ (F G : EnrichedFunctor V D E) (X : D) :
    enrichedFunctorHom F G ⟶ F.obj X ⟶[V] G.obj X
def enrichedFunctorHomEquiv (F G : EnrichedFunctor V D E) (P : V) :
    (P ⟶ enrichedFunctorHom F G) ≃ GradedNatTrans ((Center.ofBraided V).obj P) F G
-- K §2.2。[A, B] と評価。enrichedFunctorEvaluateAt は固定対象の補助。
@[instance_reducible] def enrichedFunctorEnrichment (D : Type w) (E : Type z)
    [EnrichedCategory V D] [EnrichedCategory V E]
    [HasProductsOfShape D V] [HasProductsOfShape (D × D) V] :
    EnrichedCategory V (EnrichedFunctor V D E)
-- 補助。K §2.2 の評価の対象を固定。
def enrichedFunctorEvaluateAt (X : D) :
    let : EnrichedCategory V (EnrichedFunctor V D E) := enrichedFunctorEnrichment (V := V) D E
    EnrichedFunctor V (EnrichedFunctor V D E) E
-- K §2.2 の同時評価。
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

-- R 3.5.4、K §1.6 (1.29)。
def enrichedRepresentableCovariant (X : D) :
    let : EnrichedOrdinaryCategory V V := MonoidalClosed.enrichedOrdinaryCategorySelf V
    EnrichedFunctor V D V
-- K §1.6 の可表 Hom に §1.4 の反対を適用（§1.10 の反変表示）。
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

## 対称スペクトルと基点付き単体集合

### 対称スペクトル（段4）

現行で確認したのは HS 6.2 の $C=D$ に当たる形。係数は C、旧基底 U と加群 M はともにスペクトル。HS 6.2–6.3 の右加群の表示と本体の左 `Mod` は区別する。次の LeftAction で係数が左にあるのは R と本体の規約。右表示との具体的な照合と、HS の $C\ne D$ を本体に持つかは段4の未決。自由加群の対称性・閉性、自由加群関手の `Monoidal` と `Braided` は本体で推論できる。自由第0段全体の `Monoidal` は列の自由第0段の `CoreMonoidal` を組んで得る。単位は `freeZeroUnitIso.symm`、二項は `freePairConvolutionIso 0 0`。自然性と整合を生成子で比較した後、自由加群と合成する。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite
open SerrePositivity SerrePositivity.Enriched
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0,0} C] [HasLimitsOfSize.{0,0} C] (K : C)
local notation "Sp" => GeneralSymmetricSpectrum C K
local notation "F₀" => GeneralSymmetricSpectrum.freeAt (K := K) 0
local notation "d₀" => GeneralSymmetricSpectrum.freeAtAdjunction (K := K) 0

-- HS 6.3 の比較を自由列の段階で組む補助。
def freeZeroSequenceMonoidalCore (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [HasColimitsOfSize.{0,0} C] [MonoidalClosed C] [SymmetricCategory C] :
    (SymmetricSequence.freeAt (C := C) 0).CoreMonoidal
-- R 3.7.11、HS 6.2・6.3。
def spectrumClosedModule (hF : (F₀).Monoidal) :
    Σ a : MonoidalLeftAction C Sp, @ClosedModule C Sp _ _ _ a
@[instance_reducible] def spectrumOrdinaryOfAdjunction (hF : (F₀).Monoidal) :
    EnrichedOrdinaryCategory C Sp
def spectrumMappingObjectIso (hF : (F₀).Monoidal) :
    letI := spectrumOrdinaryOfAdjunction K hF
    eHomFunctor C Sp ≅ GeneralSymmetricSpectrum.mappingObjectBifunctor (K := K)
def spectrumTensorCotensorOfAdjunction (hF : (F₀).Monoidal) :
    letI := spectrumOrdinaryOfAdjunction K hF
    TensorCotensor C Sp
-- HS 6.3 の各段での具体化。旧 TensorCotensor は比較の対象。
def spectrumTensorIso (hF : (F₀).Monoidal) :
    letI := spectrumOrdinaryOfAdjunction K hF
    (spectrumTensorCotensorOfAdjunction K hF).tensor ≅
      @TensorCotensor.tensor C _ _ Sp _ (GeneralSymmetricSpectrum.mappingEnrichedOrdinaryCategory
        (K := K)) (GeneralSymmetricSpectrum.spectrumTensorCotensor (K := K))
def spectrumCotensorIso (hF : (F₀).Monoidal) :
    letI := spectrumOrdinaryOfAdjunction K hF
    (spectrumTensorCotensorOfAdjunction K hF).cotensor ≅
      @TensorCotensor.cotensor C _ _ Sp _ (GeneralSymmetricSpectrum.mappingEnrichedOrdinaryCategory
        (K := K)) (GeneralSymmetricSpectrum.spectrumTensorCotensor (K := K))
```

`letI := hF` の下でそれぞれ `changeSelfClosedModule d₀`、`changedOrdinary d₀ (closedModuleSelf Sp)`、`changedTensorCotensor d₀ (closedModuleSelf Sp)`。写像対象は `Ev₀ [X,Y]`。閉構造の `internalHom` と本体の `internalHomBifunctor` は定義的に一致する。二つの随伴の各段表示は既存の `tensorFreeZeroPointwiseBifunctorIso` と `internalHomCotensorBifunctorIso`。旧 `spectrumTensorCotensor_tensorHomEquiv` の転置を用い、単位、合成、余テンソルと Hom への転置を B4 で比較する。HS 7.3 と 7.11 の後の注意はモデル圏に進んだ後の適用。ここではその弱同値と単位条件を含めない。

### 基点付き単体集合（段3e）

R 3.3.14 の smash の閉性と R 3.7.13 の基点付加随伴を使う。既存の `adjoinBasepointUnitIso.symm` と `adjoinBasepointProductIso` を組み、左右単位・結合・組紐を対の元と基点で比較する。基点付加関手が強モノイダルであることは、これらの比較を束ねて示す。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity SerrePositivity.Enriched
universe u

-- R 3.7.13。
def adjoinBasepointMonoidalCore : (PointedSimplicialSet.adjoinBasepointFunctor.{u}).CoreMonoidal
def pointedClosedModule (hF : (PointedSimplicialSet.adjoinBasepointFunctor.{u}).Monoidal) :
    Σ a : MonoidalLeftAction SSet.{u} PointedSimplicialSet.{u},
      @ClosedModule SSet.{u} PointedSimplicialSet.{u} _ _ _ a
@[instance_reducible] def pointedOrdinaryOfAdjunction
    (hF : (PointedSimplicialSet.adjoinBasepointFunctor.{u}).Monoidal) :
    EnrichedOrdinaryCategory SSet.{u} PointedSimplicialSet.{u}
def pointedTensorCotensorOfAdjunction
    (hF : (PointedSimplicialSet.adjoinBasepointFunctor.{u}).Monoidal) :
    letI := pointedOrdinaryOfAdjunction hF
    TensorCotensor SSet.{u} PointedSimplicialSet.{u}
-- 補助。R 3.7.13 の忘却した内部 Hom を現行の値と比較。
def pointedAdjunctionHomIso (hF : (PointedSimplicialSet.adjoinBasepointFunctor.{u}).Monoidal) :
    @eHomFunctor SSet.{u} _ _ PointedSimplicialSet.{u} _ (pointedOrdinaryOfAdjunction hF) ≅
      @eHomFunctor SSet.{u} _ _ PointedSimplicialSet.{u} _ KST.Spectra.PointedEnrichment.simplicialCategory
```

`letI := hF` の下で `changeSelfClosedModule adjoinBasepointAdjunction` を取る。同じ自己閉加群から `changedOrdinary` と `changedTensorCotensor` を取る。前者は忘却した基点付き内部 Hom、後者は $P_+∧X$ と $[P_+,Y]$。既存の単位点は `forgetUnitHomEquiv_formula` と比較する。忘却関手の既存の lax 比較と随伴の mate が単位と対の元で一致すれば、現行の単位・合成との比較を取れる。

## 現行 120 宣言の行き先

各行は段1の A2 の採取に対応。旧名の共通の接頭辞 `SerrePositivity.` を省略した。行数は [採取表](../spectra/layers-a.csv) の宣言範囲（コメント・空行を含み得る）。「消える」は段3–4の利用側移行後の見込み。改名・移動も、対応表・blueprint を含め旧名を使う側の移行後に行う。章や文献への対応が付いた定理は新しい対応が取れるまで互換名を維持する。

`CategoryTheory/Adjunction/Comparison.lean` と `CategoryTheory/FunctorTransport.lean` はそのまま使う。以下の表の短いファイル名は `CategoryTheory/Enriched/` からの相対名。 `Simplicial/EnrichedHomLaws.lean` は `CategoryTheory/` からの相対名。表の「移す」は主張を引き継ぎ、公開する入口は Mathlib の名前空間に揃える。現行 `TensorCotensor` と `EnrichedRepresentability` の型と欄は保存する。

### `RepresentedMapping.lean`

| 旧宣言 | 行 | 扱い | 行き先・置き換え |
| --- | ---: | --- | --- |
| `MappingArrowComposition.arrowCompositionEvaluationLaw` | 6 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingArrowComposition.arrow_composition_evaluation` | 22 | 移す | `ActionEvaluation.lean` |
| `MappingArrowComposition.representedArrowCompositionLaw` | 8 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingArrowComposition.represented_arrow_composition` | 13 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingAssociativity.associativityEvaluationLaw` | 9 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingAssociativity.associativity_evaluation` | 26 | 移す | `ActionEvaluation.lean` |
| `MappingAssociativity.compositionEvaluation` | 5 | 消える | 評価後の式に展開 |
| `MappingAssociativity.representedAssociativityLaw` | 9 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingAssociativity.represented_associativity` | 11 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingUnitLaws.left_unit_evaluation` | 15 | 移す | `ActionEvaluation.lean` |
| `MappingUnitLaws.parameterFunctor` | 6 | 消える | 作用の `H.flip.obj` |
| `MappingUnitLaws.right_unit_evaluation` | 15 | 移す | `ActionEvaluation.lean` |
| `MappingWhiskering.enriched_post` | 15 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingWhiskering.enriched_pre` | 16 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingWhiskering.post_composition` | 39 | 移す | `AdjunctionDataHomFunctor.lean` |
| `MappingWhiskering.post_evaluation` | 14 | 消える | OfAction.lean の法則の証明に吸収 |
| `MappingWhiskering.pre_composition` | 42 | 移す | `AdjunctionDataHomFunctor.lean` |
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
| `RepresentedHomFunctor.homFunctorIso` | 23 | 移す | `AdjunctionDataHomFunctor.lean` |
| `RepresentedHomFunctor.homFunctorIso_ofParametrized` | 19 | 据え置き | `AdjunctionDataHomFunctor.lean`。新しい `ofActionHomIso` は別宣言 |
| `RepresentedMappingEnrichment.arrow` | 2 | 消える | `actionHomEquiv` の適用 |
| `RepresentedMappingEnrichment.arrowCompositionLaw` | 5 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.arrowEquiv` | 3 | 据え置き | `OfAdjunctionData.lean`。新しい `actionHomEquiv` は別宣言 |
| `RepresentedMappingEnrichment.arrowIdentityLaw` | 3 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.arrow_identity` | 3 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.associativity` | 7 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.associativityEvaluationLaw` | 6 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.associativityLaw` | 6 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.associativity_evaluation` | 21 | 移す | `OfAdjunctionData.lean` |
| `RepresentedMappingEnrichment.composition` | 3 | 移す | `OfAdjunctionData.lean` |
| `RepresentedMappingEnrichment.compositionEvaluation` | 5 | 消える | 評価後の式に展開 |
| `RepresentedMappingEnrichment.compositionEvaluationLaw` | 4 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.composition_evaluation` | 3 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.enrichedCategory` | 15 | 移す | `OfAdjunctionData.lean` |
| `RepresentedMappingEnrichment.enrichedCategory_comp` | 6 | 消える | 新しい合成の定義式。一致には組紐を挟む |
| `RepresentedMappingEnrichment.enrichedCategory_id` | 5 | 消える | 新しい単位の定義式 |
| `RepresentedMappingEnrichment.evaluation` | 2 | 据え置き | `OfAdjunctionData.lean`。新しい `actionEvaluation` は別宣言 |
| `RepresentedMappingEnrichment.hom` | 2 | 消える | 選んだ右随伴 `R` の対象成分 |
| `RepresentedMappingEnrichment.leftUnitEvaluationLaw` | 5 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.leftUnitLaw` | 4 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.left_unit` | 5 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.left_unit_evaluation` | 14 | 移す | `OfAdjunctionData.lean` |
| `RepresentedMappingEnrichment.ordinaryCategory` | 15 | 据え置き | `OfAdjunctionData.lean`。新しい `ofAction` は別宣言 |
| `RepresentedMappingEnrichment.rightUnitEvaluationLaw` | 5 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.rightUnitLaw` | 4 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.right_unit` | 5 | 消える | OfAction.lean の法則の証明に吸収 |
| `RepresentedMappingEnrichment.right_unit_evaluation` | 14 | 移す | `OfAdjunctionData.lean` |
| `RepresentedMappingEnrichment.unit` | 2 | 据え置き | `OfAdjunctionData.lean`。新しい `actionUnit` は別宣言 |
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
| `TransportOrdinaryEnrichment.homFunctorIso` | 15 | 据え置き | `BaseChange.lean`。新しい `ordinaryBaseChangeHomIso` は同型が逆向き |
| `TransportOrdinaryEnrichment.ordinaryCategory` | 16 | 据え置き | `BaseChange.lean`。新しい `ordinaryBaseChange` では圏の型を暗黙引数から決める |
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

| 旧ファイル | 残す（宣言／行） | 据え置き（宣言／行） | 移す（宣言／行） | 消える（宣言／行） |
| --- | ---: | ---: | ---: | ---: |
| RepresentedMapping | 0／0 | 5／41 | 19／306 | 39／272 |
| Transport | 0／0 | 2／31 | 14／119 | 4／24 |
| TensorCotensor | 33／179 | 0／0 | 0／0 | 0／0 |
| Simplicial | 0／0 | 0／0 | 4／17 | 0／0 |
| 合計 | 33／179 | 7／72 | 37／442 | 43／296 |

## 利用側の書き換え量

[consumers.md](consumers.md) の8構成を、非 Archive の追跡済み Lean ソースで照合した。型欄の「箇所」は `TensorCotensor` を型として明記した宣言・セクションの引数行、または供給元の戻り型。コメント、引用属性の文字列、import、一般論自身の `CategoryTheory/Enriched/TensorCotensor.lean` は集計外。射影欄はその引数に対するテンソル・余テンソル・評価・単位の明示的なドット参照の物理行を数える。一般論の再利用と、個々に書き換える場合の差を、同じ受け口で比べた。

| consumers.md の構成 | 型の箇所／ファイル | 射影行 | 随伴を残す案で直接編集する既存行 | 吸収案で既存の射影を直書きにする場合の既存行 |
| --- | ---: | ---: | ---: | ---: |
| 通常の Hom・豊穣 Hom の関手 | 0 | 0 | 0 | 0 |
| テンソル・余テンソル・モデル圏適合性 | 4／4 | 40 | 4 | 44 |
| ホモトピー関数複体・豊穣局所化 | 58／37 | 92 | 58 | 147 |
| 豊穣関手と図式の圏 | 0 | 0 | 0 | 0 |
| Coherent 神経 | 0 | 0 | 0 | 0 |
| dg 神経、H⁰、dg 商と完備化 | 0 | 0 | 0 | 0 |
| 単体的局所化とモデル圏比較の hammock・神経の入口 | 0 | 0 | 0 | 0 |
| K 理論の S 構成とスペクトル | 1／1 | — | 供給元の1行とモデル側の呼出し | 供給元と下記の名前付き参照23行（供給元を含む） |

残す案は、閉じた加群を取る型へ明示引数62行を替え、`ClosedModuleOn` から取る `adjunctions` の共用射影・転置を少数の前方定義で現行のドット名に揃える見積もり。モデル・局所化を横切って加群の値を受け渡す箇所には同じ値を渡せる。既存の弱い型を使う計算補題は `S.adjunctions` を渡す。吸収案でも同名の前方定義を作れば利用側の直接変更量は近づくが、現行の33宣言のうち二つの随伴から導出する API と引用を新構造上へ移す必要がある。射影を個別に展開する吸収案は、二つの構成だけで重複を除き191行。残す案の62行は型と射影の既知の範囲での比較で、前方定義・供給側の整合・他ファイルからの位置引数の調整、import 改名の行を含まない。スペクトル側では旧名を随伴を返す互換入口にできるため、23行を一括で置換する必要はない。どちらの案でも、旧来は自由だった `TensorCotensor` の値の供給側に作用の整合が必要になる。

### モデル・単位置換・固定単体的条件

| ファイルと最初の型の行 | 型の行 | 射影行数 | 個別に直す場合の行数 |
| --- | --- | ---: | ---: |
| [TensorCotensor](../../../SerrePositivity/HomotopicalAlgebra/Enriched/TensorCotensor.lean#L27) | 27 | 17 | 18 |
| [UnitAxiom](../../../SerrePositivity/HomotopicalAlgebra/Enriched/UnitAxiom.lean#L24) | 24 | 3 | 4 |
| [UnitChangeModel](../../../SerrePositivity/HomotopicalAlgebra/Enriched/UnitChangeModel.lean#L20) | 20 | 1 | 2 |
| [FixedSimplicialModelCompatibility](../../../SerrePositivity/InfinityCategories/Project/ModelCategoryComparison/Replacements/FixedSimplicialModelCompatibility.lean#L39) | 39 | 19 | 20 |

### 関数複体、置換、局所化、HTT/Kerodon の Quillen 比較

| ファイルと最初の型の行 | 型の行 | 射影行数 | 個別に直す場合の行数 |
| --- | --- | ---: | ---: |
| [DerivedMapping](../../../SerrePositivity/HomotopicalAlgebra/Enriched/DerivedMapping.lean#L42) | 42 | 3 | 3 |
| [UnitFrame](../../../SerrePositivity/HomotopicalAlgebra/Enriched/UnitFrame.lean#L27) | 27 | 18 | 19 |
| [ChosenMapComparison](../../../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ChosenMapComparison.lean#L42) | 42 | 1 | 2 |
| [EnrichedTensorFrameHom](../../../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/EnrichedTensorFrameHom.lean#L22) | 22 | 3 | 4 |
| [SimplicialMapComparison](../../../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/SimplicialMapComparison.lean#L24) | 24 | 1 | 2 |
| [SimplicialTensorAugmentation](../../../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/SimplicialTensorAugmentation.lean#L20) | 20 | 6 | 7 |
| [SimplicialTensorCofibrant](../../../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/SimplicialTensorCofibrant.lean#L24) | 24 | 4 | 4 |
| [SimplicialTensorConstant](../../../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/SimplicialTensorConstant.lean#L45) | 45 | 3 | 3 |
| [SimplicialTensorHom](../../../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/SimplicialTensorHom.lean#L22) | 22 | 8 | 9 |
| [Enriched](../../../SerrePositivity/HomotopicalAlgebra/Localization/Enriched.lean#L31) | 31 | 6 | 7 |
| [EnrichedDetection](../../../SerrePositivity/HomotopicalAlgebra/Localization/EnrichedDetection.lean#L30) | 30 | 4 | 5 |
| [EnrichedExistence](../../../SerrePositivity/HomotopicalAlgebra/Localization/EnrichedExistence.lean#L38) | 38 | 5 | 6 |
| [EnrichedLocalObjects](../../../SerrePositivity/HomotopicalAlgebra/Localization/EnrichedLocalObjects.lean#L29) | 29 | 3 | 4 |
| [EnrichedTestComparison](../../../SerrePositivity/HomotopicalAlgebra/Localization/EnrichedTestComparison.lean#L24) | 24 | 1 | 2 |
| [QuillenCfCollage](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfCollage.lean#L40) | 40, 41 | 1 | 3 |
| [QuillenCfCollageInclusions](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfCollageInclusions.lean#L38) | 38, 44 | 2 | 4 |
| [QuillenCfCollageProjection](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfCollageProjection.lean#L96) | 96, 97 | 1 | 3 |
| [QuillenCfDerivedComparison](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfDerivedComparison.lean#L34) | 34, 35 | 1 | 3 |
| [QuillenCfDerivedLimits](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfDerivedLimits.lean#L30) | 30, 31 | 1 | 3 |
| [QuillenCfDerivedTransport](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfDerivedTransport.lean#L32) | 32, 33 | 1 | 3 |
| [QuillenCfFinalHornFixedEdge](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfFinalHornFixedEdge.lean#L31) | 31, 32 | 1 | 3 |
| [QuillenCfFinalHornHollow](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfFinalHornHollow.lean#L26) | 26, 27 | 1 | 3 |
| [QuillenCfFinalHornUnknownHom](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfFinalHornUnknownHom.lean#L31) | 31, 32 | 1 | 3 |
| [QuillenCfFullyFaithful](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfFullyFaithful.lean#L38) | 38, 39 | 1 | 3 |
| [QuillenCfLeftCocartesian](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfLeftCocartesian.lean#L34) | 34, 35 | 1 | 3 |
| [QuillenCfLeftLift](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfLeftLift.lean#L75) | 75 | 1 | 2 |
| [QuillenCfLeftOrdinaryComparison](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfLeftOrdinaryComparison.lean#L34) | 34, 35 | 1 | 3 |
| [QuillenCfLeftReplacement](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfLeftReplacement.lean#L33) | 33, 34 | 1 | 3 |
| [QuillenCfOuterHomFilling](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfOuterHomFilling.lean#L26) | 26, 57 | 2 | 4 |
| [QuillenCfReplacementHom](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfReplacementHom.lean#L51) | 51, 75 | 2 | 4 |
| [QuillenCfRightCartesian](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfRightCartesian.lean#L32) | 32, 33 | 1 | 3 |
| [QuillenCfRightLift](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfRightLift.lean#L59) | 59 | 1 | 2 |
| [QuillenCfRightOrdinaryComparison](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfRightOrdinaryComparison.lean#L29) | 29, 30 | 1 | 3 |
| [QuillenCfRightReplacement](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfRightReplacement.lean#L31) | 31, 32 | 1 | 3 |
| [QuillenCfUnitPrism](../../../SerrePositivity/InfinityCategories/HTT/ModelCategoryAdjunctions/QuillenCfUnitPrism.lean#L30) | 30, 31 | 1 | 3 |
| [QuillenCfBifibration](../../../SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/QuillenCfBifibration.lean#L33) | 33, 34 | 1 | 3 |
| [QuillenCfDerivedAdjunction](../../../SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/QuillenCfDerivedAdjunction.lean#L36) | 36, 37 | 1 | 3 |

### スペクトルの名前付き供給・受け取り

| ファイル | `spectrumTensorCotensor` の行 |
| --- | --- |
| [General/CotensorMappingPoints](../../../SerrePositivity/Spectra/General/CotensorMappingPoints.lean#L72) | 72 |
| [General/EnrichedMappingObjects](../../../SerrePositivity/Spectra/General/EnrichedMappingObjects.lean#L30) | 30, 39 |
| [General/EnrichedRepresentability](../../../SerrePositivity/Spectra/General/EnrichedRepresentability.lean#L27) | 27 |
| [General/TensorCotensorEnriched](../../../SerrePositivity/Spectra/General/TensorCotensorEnriched.lean#L24) | 24, 35 |
| [General/TensorMappingPoints](../../../SerrePositivity/Spectra/General/TensorMappingPoints.lean#L67) | 67 |
| [ModelCategory/GeneralLevelEnriched](../../../SerrePositivity/Spectra/ModelCategory/GeneralLevelEnriched.lean#L34) | 34, 36, 39, 47 |
| [Stable/EnrichedModel](../../../SerrePositivity/Spectra/Stable/EnrichedModel.lean#L54) | 54, 60, 62, 67, 122, 124, 130, 137 |
| [Stable/TensorCompatibility](../../../SerrePositivity/Spectra/Stable/TensorCompatibility.lean#L54) | 54, 57, 92, 95 |

## 原典との突合

| 部分 | 合成と作用の規約の確認 |
| --- | --- |
| A1・A3・B3 | 作用は `curriedAction V M`、係数が先。写像随伴だけ `.flip`。A3 の合成は $M(X,Y)⊗M(Y,Z)$ が入力で、R 3.3.1 の順に戻す組紐は評価を始める直前の一回。H 4.1.6 は右を左に読み替え、結合の同型の向きも上の順射に合わせた |
| B1 | テンソルの列で $A⊗P$ を $P⊗A$ からの前合成に移す。余テンソルの列は第3段ですでに $P⊗A$。Mathlib の閉随伴は `tensorLeft P`。R の記号 $×$ はここで直積に限らない |
| A2・B2・B4 | G の比較は Mathlib 順の因子に適用。`F ⋙ T` の係数を $F(P)$ にする。R の文献順で輸送した後に交換する経路との一致は、B4 で F の組紐保存を明示。強モノイダル性だけで作る B2 の通常随伴と米田の列にはこの比較を仮定しない |
| B6 | `LaxLeftLinear.μₗ` は $P⊙FX→F(P⊙X)$、余テンソルの比較は $G(Y^P)→(GY)^P$。豊穣関手の合成法則と自然変換は `eComp V X Y Z` の図式順 |
| C-軽 | K §1.4 の対を `tensor V` の二項比較で運び、成分ごとの単位と合成を図式順に保つ。関手圏の同時評価は図式順で射を合成し、組紐の逆の照合に対称性を使う。反対と反変可表関手は Mathlib の反対の組紐を使う |
| スペクトル・基点付き単体集合 | 現行のスペクトルは HS 6.2 の右加群と逆の左加群。段4では係数を左に置く型と、右側の原典の各段式の照合が必要。基点付き単体集合は R 3.7.13 の左作用 $P_+∧X$ |

### 対応表にあって独立の型を置かない項目

| 文献対応表 §2 の項目 | 段2bでの扱い |
| --- | --- |
| R 3.3.1・3.3.6・(3.3.7)・3.3.9、3.4.1、3.4.5、3.5.1、H 4.1.1–4.1.5・4.1.13 | Mathlib の既存構造と閉随伴を使用。R 3.3.9 の閉構造の内部 curry は `MonoidalClosed.ihomCurryIso` を使用可。H 4.1.5 の組紐保存は B4 の入力 |
| R 3.3.14 | smash の閉構造は既存、試験例は R 3.7.13 を型にした |
| R 3.5.10、K §1.3 | 2 関手として束ねる宣言は置かず、Mathlib の `ForgetEnrichment` と `EnrichedFunctor.forget` を使う |
| R 3.7.4 の全 V 二変数随伴、10.1.2、10.1.6 の末尾 | B1 は二つの V 値の同型、通常の二変数自然性・係数自然性・点での一致を束ねる。豊穣二変数関手とその全豊穣自然性を一体化した随伴レコードは今回の型に置かない。B6 では一変数の余テンソルの比較を具体化 |
| R 3.7.7 | 豊穣表現から作用を復元する B5 は保留。単位と結合子は今回の入力 |
| R (10.1.1)、H 4.1.6・4.1.12 | 作用は `ClosedModule` の外から `MonoidalLeftAction` として渡し、欄には `ParametrizedAdjunction` を使う |
| H 4.1.7 の加群自然変換、4.1.8、§4.1 末尾の閉じた代数と双対 2 関手 | B6 で全 Hom の自然性と lineator の比較四角を使う。加群自然変換圏の独立の型、代数側の言い換え、2 圏の双対全体は対象外 |
| H 4.2.1・4.2.2・4.2.6・4.2.10・4.2.16・4.2.18 | モデル圏側の既存の Quillen・単位条件を使う。4.2.18 に合わせる利用側の受け口と書き換え量は上に記録。4.2.16 の単位の置換の弱同値は試験例の型に含めない |
| K §1.4 の反対、§1.6 の自己豊穣、§1.10 の受け身変数の一般定理 | 反対と自己豊穣は Mathlib。§1.10 は表現可能な Hom を作るのに使う範囲まで |
| K §2.3、§2.6、§3.11、§3.12 | 指数法則と宇宙拡大は段5で判断。型案では二つの添字の積があることを仮定 |
| K §3.5、§1.9、§2.4 | 充満部分圏と極限、豊穣米田・余米田は保留。B1・B2 の同型を取るのは通常米田（R 3.5.12） |
| HS 6.1、6.2 の $C\ne D$、7.3、7.11 の後の注意 | 対称列の畳み込みは既存。一般の C と D、射影・安定モデル圏での結論は段4で設計。HS 6.3 の自由第0段の強モノイダル性は型案に置いた |

## 改訂後の実装見積もり

| 段 | 宣言署名 | 実装行の見込み | 作業 |
| --- | ---: | ---: | --- |
| 3a | 16 | 200–360 | A2・A3・B3、自己閉加群、作用と随伴の受け口、物理ファイルの配置と文献略号 |
| 3b | 32 | 300–520 | B1 の列、米田、四欄と作用を使う入口。弱い入力でできる箇所を個別に確認 |
| 3c | 44 | 400–700 | 任意 M の B2。随伴の制限と変換、B2 自身の列、B4 の全 Hom 比較と転置 |
| 3d | 15 | 320–630 | B6 の lax lineator、指定した通常関手の V 関手化、単位・余単位と随伴、F ⊣ G 自身の適用 |
| 3e | 5 | 100–190 | 基点付き単体集合でモノイダル整合を作り、現行 Hom・単位・合成・二つの転置を照合 |
| 4 | 7 | 130–280 | スペクトル。自由第0段の比較と各段での表示。HS の向きと C、D の範囲を先に決める |
| 5 | 13 | 220–420 | C-軽を dg と SSet に適用。添字宇宙を先に照合 |
| 合計 | 132 | 1,670–3,100 | 旧入口と型が異なる7件を含め、すべて新しい入口・補助 |

宣言は、文献との照合のため型を独立に書いた各段の同値・自然性も含めた数。行数は型と証明の合計の概算で、旧宣言43件・296行の削減候補、移動分、利用側の移行行、略号表は別。段3以降は監査の区切りを待つ。SU-W1 段14a の作用の評価則と二重転置を継承し、実装保留は継続する。

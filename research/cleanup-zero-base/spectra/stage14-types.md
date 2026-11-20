# SU-W1 段14a　写像対象と豊穣化の型案

基準は main `24eff0979` を取り込んだ `c7e3e6762`。型ヘッダーは設計案。下の変数と局所表記を各ブロックで共用する。対応する B の宣言は [stage14.csv](stage14.csv) の `application` 列で引ける。

## 仮定と作用の取り方

`V` は豊穣化の基底、`M` は既に通常の Hom を持つ圏。B では `V = C`、`M = GeneralSymmetricSpectrum C K`。作用 `H : V ⥤ M ⥤ M` は次数ごとのテンソル。結合子の向きは `H(P ⊗ Q) ≅ H(Q) ⋙ H(P)`、単位子は `H(𝟙) ≅ 𝟭 M`。係数二変数と対象の射についての自然性、五角形、左右の単位の式は Mathlib の `MonoidalLeftAction` に載せる。B の作用を登録する箇所では、各段での結合子と係数射の計算、既存の `pointwiseAction_pentagon`、`pointwiseAction_triangle`、`pointwiseAction_left_unit` を使う。

写像対象 `R : Mᵒᵖ ⥤ M ⥤ V` は `(H).flip` のパラメータ付き右随伴、余テンソル `Q : Vᵒᵖ ⥤ M ⥤ M` は `H` のパラメータ付き右随伴。したがって各 `P,X,Y` で
`Hom_M(H(P)X,Y) ≃ Hom_V(P,R(X,Y))` と
`Hom_M(H(P)X,Y) ≃ Hom_M(X,Q(P)Y)` があり、余テンソルから写像対象への同値は後者の逆と前者の合成。別の整合公理は要らない。豊穣化と Hom 関手の比較には組紐、内部 Hom への比較にはさらに閉性を使う。対称性、極限、余極限、モデル構造はこの構成の入力に含まれない。B でそれらを使う箇所は二つの随伴や作用を用意する側にある。

```lean
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
universe u v u' v'
variable {V : Type u} {M : Type u'} [Category.{v} V] [Category.{v'} M]
  [MonoidalCategory V] [MonoidalLeftAction V M]

local notation "H" => MonoidalLeftAction.curriedAction V M
local notation "uₕ" => MonoidalLeftAction.actionUnitNatIso V M
variable {R : Mᵒᵖ ⥤ M ⥤ V} {Q : Vᵒᵖ ⥤ M ⥤ M}
local notation "L" => Functor.obj (Functor.flip H)
local notation "T" => Functor.obj H
local notation "U" => fun P : V => Q.obj (op P)
local notation "R₁" => fun X : M => R.obj (op X)
local notation "homV" => fun X Y : M => Functor.obj (R.obj (op X)) Y
```

下の `functorAssoc` は `((H).obj (P ⊗ Q)) ≅ (H).obj Q ⋙ (H).obj P`。Mathlib の三変数同型から二度 `.app` を取るか、同型 `αₗ P Q X` を `NatIso.ofComponents` で束ねる。型上の局所略記 `a` はその結果を指す。

B では、現在の二変数関手の対象・射と結合子・単位子をそのまま使って局所作用を作る。Mathlib の `curriedAction` と現行 `pointwiseTensorBifunctor` のレコードが定義的に揃わない場合、各対象で恒等を成分とする自然同型を、対象と射の計算を照合して作る。その順逆と `ParametrizedAdjunctionTransport.left` で二つの随伴を移す（写像対象側は`Functor.flipFunctor` の `mapIso` を使う）。結合子と単位子の順射も現行と同じ成分であることを照合する。この橋で揃わない型は削除候補から外す。任意の自然同型で置き換えると既存の転置の式まで自動的に保たれるとは限らない。

## 作用から豊穣化へ（`CategoryTheory/Enriched/RepresentedMapping.lean` への追記案）

`RepresentedAction` 名前空間に以下を置く。定義・補題は既存の `RepresentedMappingEnrichment`、`MappingUnitLaws`、`MappingArrowComposition`、`MappingWhiskering`、`RepresentedHomFunctor` に作用の整合式を渡して使う。作用の単位は既に入力にあるため、その部分を `TensorCotensor.unitIso` の再構成に依存させない。

```lean
def functorAssoc (P Q : V) : T (P ⊗ Q) ≅ T Q ⋙ T P
local notation "a" => fun P Q : V => functorAssoc (M := M) P Q

lemma left_unit_evaluation (r : (H).flip ⊣₂ R) (X Y : M) :
    RepresentedMappingEnrichment.leftUnitEvaluationLaw H a uₕ R₁ r.adj X Y
lemma right_unit_evaluation (r : (H).flip ⊣₂ R) (X Y : M) :
    RepresentedMappingEnrichment.rightUnitEvaluationLaw H a uₕ R₁ r.adj X Y
lemma associativity_evaluation (r : (H).flip ⊣₂ R) (X Y Z W : M) :
    RepresentedMappingEnrichment.associativityEvaluationLaw H a R₁ r.adj X Y Z W
lemma arrow_composition_evaluation (r : (H).flip ⊣₂ R) {X Y Z : M} (f : X ⟶ Y) (g : Y ⟶ Z) :
    MappingArrowComposition.arrowCompositionEvaluationLaw H a uₕ f g
      (RepresentedMappingEnrichment.arrow H uₕ R₁ r.adj g)
      (RepresentedMappingEnrichment.arrow H uₕ R₁ r.adj f)
      (RepresentedMappingEnrichment.evaluation H R₁ r.adj X Y)
      (RepresentedMappingEnrichment.evaluation H R₁ r.adj Y Z)
lemma composition_post (r : (H).flip ⊣₂ R) (X : M) {Y Z : M} (g : Y ⟶ Z) :
    (λ_ (homV X Y)).inv ≫
      RepresentedMappingEnrichment.arrow H uₕ R₁ r.adj g ▷ homV X Y ≫
      RepresentedMappingEnrichment.composition H a R₁ r.adj X Y Z =
        (R₁ X).map g
lemma composition_pre (r : (H).flip ⊣₂ R) {X Y : M} (f : X ⟶ Y) (Z : M) :
    (ρ_ (homV Y Z)).inv ≫
      homV Y Z ◁ RepresentedMappingEnrichment.arrow H uₕ R₁ r.adj f ≫
      RepresentedMappingEnrichment.composition H a R₁ r.adj X Y Z =
        (R.map f.op).app Z
```

```lean
variable [BraidedCategory V]
@[instance_reducible] def enrichedCategory (r : (H).flip ⊣₂ R) : EnrichedCategory V M
@[instance_reducible] def enrichedOrdinaryCategory (r : (H).flip ⊣₂ R) : EnrichedOrdinaryCategory V M
def homFunctorIso (r : (H).flip ⊣₂ R) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    eHomFunctor V M ≅ R
lemma homFunctorIso_hom_app (r : (H).flip ⊣₂ R) (X Y : M) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    ((homFunctorIso r).hom.app (op X)).app Y = 𝟙 (homV X Y)
lemma enriched_post (r : (H).flip ⊣₂ R) (X : M) {Y Z : M} (g : Y ⟶ Z) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    eHomWhiskerLeft V X g = (R₁ X).map g
lemma enriched_pre (r : (H).flip ⊣₂ R) {X Y : M} (f : X ⟶ Y) (Z : M) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    eHomWhiskerRight V f Z = (R.map f.op).app Z
```

既存の `RepresentedMappingEnrichment` は単位、合成、単位点とその通常 Hom 同値、評価を既に定義する。B の `mappingObjectEvaluation`、`mappingObjectUnit`、`mappingObjectComposition`、`mappingObjectArrow`、`mappingObjectArrowEquiv` にはこの型を再利用する。新しい `enrichedCategory/enrichedOrdinaryCategory` はその既存の構成へ渡す法則を閉じた入口。既存の `homFunctorIso_ofParametrized` を `r` と作用の自然性から適用し、成分を恒等に固定する。これが B の `mappingEnrichedHomFunctorIso` の対応。`enrichedOrdinaryCategory` の豊穣 Hom は各対象で `homV X Y`、`eHomEquiv` は `RepresentedMappingEnrichment.arrowEquiv` に定義的に還元する。順射が恒等なので逆射も恒等で、写像対象への転置を変えずに `eHomFunctor` へ輸送できる。

## 作用からテンソル・余テンソルつき豊穣圏へ（新規 `CategoryTheory/Enriched/ActionRepresentability.lean`）

`TensorCotensor` と `EnrichedRepresentability` は既存のまま使う。前者の `tensor`、`cotensor`、`tensorCotensor` は定義的に `H`、`Q`、`q`。 `tensorHom` は `r` の右を `homFunctorIso.symm` で輸送したもの。以下は同じ `RepresentedAction` 名前空間に置く。

| 型案 | A の既存宣言との関係 |
|---|---|
| `tensorCotensor`、`tensorCotensor_tensorHomEquiv` | 既存の `Enriched.TensorCotensor` と `ParametrizedAdjunctionTransport.right` を使う新しい構成と比較。 |
| `*ParameterIso`、`*PowerAdjunction`、`cotensorAdjunction` | 作用の結合子と随伴の合成を組み合わせる新しい定義。 |
| `*MappingNatIso`、`*_homEquiv`、`*Mapping_parameter/source`、`*MappingBifunctorIso` | `ActionComparisonAdjunction` と `ActionComparisonNaturality` を使う新しい適用。既存の比較の型を維持する。 |
| `*EnrichedIso` とその成分・係数・点の式、`enrichedRepresentability` | 既存の `EnrichedRepresentability` に入れる自然同型と証明を組み立てる新しい入口。 |

```lean
def tensorCotensor (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    Enriched.TensorCotensor V M
lemma tensorCotensor_tensorHomEquiv (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P : V) (X Y : M)
    (f : (T P).obj X ⟶ Y) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    (tensorCotensor r q).tensorHomEquiv P X Y f = (r.adj X).homEquiv P Y f

variable [MonoidalClosed V]
def tensorParameterIso (P : V) (X : M) :
    tensorRight P ⋙ L X ≅ L ((T P).obj X)
def cotensorParameterIso (P : V) (X : M) :
    tensorLeft P ⋙ L X ≅ L X ⋙ T P
def tensorPowerAdjunction (r : (H).flip ⊣₂ R) (P : V) (X : M) :
    tensorRight P ⋙ L X ⊣ R₁ X ⋙ ihom P
def cotensorPowerAdjunction (r : (H).flip ⊣₂ R) (P : V) (X : M) :
    tensorLeft P ⋙ L X ⊣ R₁ X ⋙ ihom P
def cotensorAdjunction (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P : V) (X : M) :
    L X ⋙ T P ⊣ U P ⋙ R₁ X
def tensorMappingNatIso (r : (H).flip ⊣₂ R) (P : V) (X : M) :
    R₁ ((T P).obj X) ≅ R₁ X ⋙ ihom P
def cotensorMappingNatIso (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P : V) (X : M) :
    U P ⋙ R₁ X ≅ R₁ X ⋙ ihom P

lemma tensorMappingNatIso_homEquiv (r : (H).flip ⊣₂ R) (P S : V) (X Y : M)
    (f : (T (S ⊗ P)).obj X ⟶ Y) :
    (r.adj ((T P).obj X)).homEquiv S Y ((a S P).inv.app X ≫ f) ≫
      (tensorMappingNatIso r P X).hom.app Y =
        (tensorPowerAdjunction r P X).homEquiv S Y f
lemma cotensorMappingNatIso_homEquiv (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P S : V) (X Y : M)
    (f : (T (P ⊗ S)).obj X ⟶ Y) :
    (cotensorAdjunction r q P X).homEquiv S Y ((a P S).inv.app X ≫ f) ≫
      (cotensorMappingNatIso r q P X).hom.app Y =
        (cotensorPowerAdjunction r P X).homEquiv S Y f
```

前二つの自然同型は作用の結合子。テンソルでは `tensorRight P` の随伴を組紐で `ihom P` に合わせてから `r.adj X` と合成。余テンソルでは左側で `ihom.adjunction P` と `r.adj X`、右側で `r.adj X` と `q.adj P` を合成。両比較を `ActionComparisonAdjunction.rightIso` に結合子の逆向きで渡し、任意の一般化点について `rightIso_homEquiv` を使う。B の `*MappingParameterIso`、`*MappingPowerAdjunction`、`*MappingNatIso` とその `_homEquiv` に対応する。

### 自然性と点の型

以下で `tP` は `(tensorMappingNatIso r P X).hom.app Y`、`cP` は余テンソル側の順成分の略記。型ヘッダーでは成分を明記する。

```lean
lemma tensorMapping_parameter (r : (H).flip ⊣₂ R) {P P' : V} (p : P ⟶ P') (X Y : M) :
    (R.map (((H).map p).app X).op).app Y ≫ (tensorMappingNatIso r P X).hom.app Y =
      (tensorMappingNatIso r P' X).hom.app Y ≫ (MonoidalClosed.pre p).app (homV X Y)
lemma cotensorMapping_parameter (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) {P P' : V} (p : P ⟶ P') (X Y : M) :
    (R₁ X).map ((Q.map p.op).app Y) ≫ (cotensorMappingNatIso r q P X).hom.app Y =
      (cotensorMappingNatIso r q P' X).hom.app Y ≫ (MonoidalClosed.pre p).app (homV X Y)

lemma tensorMapping_source (r : (H).flip ⊣₂ R) (P : V) {X X' : M} (f : X ⟶ X') (Y : M) :
    (R.map ((T P).map f).op).app Y ≫ (tensorMappingNatIso r P X).hom.app Y =
      (tensorMappingNatIso r P X').hom.app Y ≫ (ihom P).map ((R.map f.op).app Y)
lemma cotensorMapping_source (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P : V) {X X' : M} (f : X ⟶ X') (Y : M) :
    (R.map f.op).app ((U P).obj Y) ≫ (cotensorMappingNatIso r q P X).hom.app Y =
      (cotensorMappingNatIso r q P X').hom.app Y ≫ (ihom P).map ((R.map f.op).app Y)

def tensorMappingBifunctorIso (r : (H).flip ⊣₂ R) (P : V) :
    (T P).op ⋙ R ≅ R ⋙ (Functor.whiskeringRight M V V).obj (ihom P)
def cotensorMappingBifunctorIso (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P : V) :
    R ⋙ (Functor.whiskeringLeft M M V).obj (U P) ≅
      R ⋙ (Functor.whiskeringRight M V V).obj (ihom P)

def tensorEnrichedIso (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P : V) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    Enriched.tensorEnrichedHom (tensorCotensor r q) P ≅ Enriched.powerHom (C := M) P
def cotensorEnrichedIso (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P : V) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    Enriched.cotensorEnrichedHom (tensorCotensor r q) P ≅ Enriched.powerHom (C := M) P
lemma tensorEnrichedIso_hom_app (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P : V) (X Y : M) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    ((tensorEnrichedIso r q P).hom.app (op X)).app Y =
      (tensorMappingNatIso r P X).hom.app Y
lemma cotensorEnrichedIso_hom_app (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P : V) (X Y : M) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    ((cotensorEnrichedIso r q P).hom.app (op X)).app Y =
      (cotensorMappingNatIso r q P X).hom.app Y

lemma tensorEnriched_parameter (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) {P P' : V} (p : P ⟶ P') (X Y : M) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    eHomWhiskerRight V (((H).map p).app X) Y ≫
      ((tensorEnrichedIso r q P).hom.app (op X)).app Y =
      ((tensorEnrichedIso r q P').hom.app (op X)).app Y ≫
        (MonoidalClosed.pre p).app (X ⟶[V] Y)
lemma cotensorEnriched_parameter (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) {P P' : V} (p : P ⟶ P') (X Y : M) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    eHomWhiskerLeft V X ((Q.map p.op).app Y) ≫
      ((cotensorEnrichedIso r q P).hom.app (op X)).app Y =
      ((cotensorEnrichedIso r q P').hom.app (op X)).app Y ≫
        (MonoidalClosed.pre p).app (X ⟶[V] Y)

lemma tensorEnriched_points (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P : V) (X Y : M) (f : (T P).obj X ⟶ Y) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    (MonoidalClosed.curryHomEquiv' (X := P) (Y := X ⟶[V] Y)).symm
      (eHomEquiv V f ≫ ((tensorEnrichedIso r q P).hom.app (op X)).app Y) =
        (tensorCotensor r q).tensorHomEquiv P X Y f
lemma cotensorEnriched_points (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P : V) (X Y : M) (f : X ⟶ (U P).obj Y) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    (MonoidalClosed.curryHomEquiv' (X := P) (Y := X ⟶[V] Y)).symm
      (eHomEquiv V f ≫ ((cotensorEnrichedIso r q P).hom.app (op X)).app Y) =
        (tensorCotensor r q).cotensorHomEquiv P X Y f

def enrichedRepresentability (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) :
    let : EnrichedOrdinaryCategory V M := enrichedOrdinaryCategory r
    Enriched.EnrichedRepresentability (tensorCotensor r q)
```

後二変数の自然性は随伴または右随伴同型の自然性。係数射 `p` を両辺で動かすときは `MonoidalClosed.pre p` が反変で、テンソル側は `tensorRight` の係数射と組紐の自然性を通す。余テンソル側では `q.homEquiv_naturality_one` が `Q.map p.op` を与える。原変数の式には `r.homEquiv_naturality_one` を用いる。現在の `*PowerAdjunction_naturality_source/parameter` と `cotensorMappingAdjunction_naturality_source/parameter` は、この証明中で合成随伴の成分を計算する式。原変数・係数ごとに `ActionComparisonNaturality.parameter`、`parameter_composite`、`composite_pre` を使い、B に公開補題として再定義しない案（利用がある場合の一行化は表に記す）。

単位点は全一般化点の比較で `S = 𝟙_ V` とする。テンソル側は `(λ_ P).hom`、余テンソル側は `(ρ_ P).hom` を `(H).map` し、左・右の作用単位律を使う。テンソル側の合成随伴では右テンソルを左テンソルへ戻す組紐と単位子の式も使う。これで B の `*PowerAdjunction_unit` と `*MappingIso_arrow` の計算を一般の `*_points` に収められる。途中の算式は次の型で A の局所補題に切り出せる。実装時に同じ式が一度だけ必要なら、親の証明内の局所式にする。

```lean
lemma tensorPower_parameter (r : (H).flip ⊣₂ R) {P P' : V} (p : P ⟶ P') (S : V) (X Y : M)
    (f : (T (S ⊗ P')).obj X ⟶ Y) :
    (tensorPowerAdjunction r P X).homEquiv S Y (((H).map (S ◁ p)).app X ≫ f) =
      (tensorPowerAdjunction r P' X).homEquiv S Y f ≫
        (MonoidalClosed.pre p).app (homV X Y)
lemma cotensorPower_parameter (r : (H).flip ⊣₂ R) {P P' : V} (p : P ⟶ P') (S : V) (X Y : M)
    (f : (T (P' ⊗ S)).obj X ⟶ Y) :
    (cotensorPowerAdjunction r P X).homEquiv S Y (((H).map (p ▷ S)).app X ≫ f) =
      (cotensorPowerAdjunction r P' X).homEquiv S Y f ≫
        (MonoidalClosed.pre p).app (homV X Y)
lemma cotensorAdjunction_parameter (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) {P P' : V} (p : P ⟶ P') (S : V) (X Y : M)
    (f : (T P').obj ((T S).obj X) ⟶ Y) :
    (cotensorAdjunction r q P X).homEquiv S Y (((H).map p).app ((T S).obj X) ≫ f) =
      (cotensorAdjunction r q P' X).homEquiv S Y f ≫
        (R₁ X).map ((Q.map p.op).app Y)

lemma tensorPower_source (r : (H).flip ⊣₂ R) (P S : V) {X X' : M} (b : X ⟶ X') (Y : M)
    (f : (T (S ⊗ P)).obj X' ⟶ Y) :
    (tensorPowerAdjunction r P X).homEquiv S Y ((T (S ⊗ P)).map b ≫ f) =
      (tensorPowerAdjunction r P X').homEquiv S Y f ≫
        (ihom P).map ((R.map b.op).app Y)
lemma cotensorPower_source (r : (H).flip ⊣₂ R) (P S : V) {X X' : M} (b : X ⟶ X') (Y : M)
    (f : (T (P ⊗ S)).obj X' ⟶ Y) :
    (cotensorPowerAdjunction r P X).homEquiv S Y ((T (P ⊗ S)).map b ≫ f) =
      (cotensorPowerAdjunction r P X').homEquiv S Y f ≫
        (ihom P).map ((R.map b.op).app Y)
lemma cotensorAdjunction_source (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P S : V) {X X' : M} (b : X ⟶ X') (Y : M)
    (f : (T P).obj ((T S).obj X') ⟶ Y) :
    (cotensorAdjunction r q P X).homEquiv S Y ((T P).map ((T S).map b) ≫ f) =
      (cotensorAdjunction r q P X').homEquiv S Y f ≫
        (R.map b.op).app ((U P).obj Y)

lemma tensorPower_unit (r : (H).flip ⊣₂ R) (P : V) (X Y : M) (f : (T P).obj X ⟶ Y) :
    (tensorPowerAdjunction r P X).homEquiv (𝟙_ V) Y (((H).map (λ_ P).hom).app X ≫ f) =
      MonoidalClosed.curry' ((r.adj X).homEquiv P Y f)
lemma cotensorPower_unit (r : (H).flip ⊣₂ R) (P : V) (X Y : M) (f : (T P).obj X ⟶ Y) :
    (cotensorPowerAdjunction r P X).homEquiv (𝟙_ V) Y (((H).map (ρ_ P).hom).app X ≫ f) =
      MonoidalClosed.curry' ((r.adj X).homEquiv P Y f)
lemma tensorMapping_arrow (r : (H).flip ⊣₂ R) (P : V) (X Y : M) (f : (T P).obj X ⟶ Y) :
    RepresentedMappingEnrichment.arrow H uₕ R₁ r.adj f ≫
      (tensorMappingNatIso r P X).hom.app Y =
        MonoidalClosed.curry' ((r.adj X).homEquiv P Y f)
lemma cotensorMapping_arrow (r : (H).flip ⊣₂ R) (q : H ⊣₂ Q) (P : V) (X Y : M) (f : X ⟶ (U P).obj Y) :
    RepresentedMappingEnrichment.arrow H uₕ R₁ r.adj f ≫
      (cotensorMappingNatIso r q P X).hom.app Y =
        MonoidalClosed.curry' ((r.adj X).homEquiv P Y (((q.adj P).homEquiv X Y).symm f))
```

## 残りの移動候補9件の型

この節は、同じ39件の目録に含まれる対称列と零対象の設計。作用の豊穣化と別の差分で進められる。候補 `pointwiseTensorBifunctor` とその比較は既存 `FunctorTransport.transport/iso` を利用して任意の対称列モノイド `N` で定める。次のブロックの `SC` は `SymmetricSequence V`、`D` は `Mod SC N`、`F₀ : V ⥤ D` は `SymmetricSequence.freeAt 0` と `MonoidalFreeModule` の自由加群関手の合成。モノイダル構造を使う型では B の相対テンソルと同じく `N` の可換性と必要な極限・余極限を仮定する。
`pointwiseModuleBifunctor` の対象成分は定義的に `pointwiseTensorModuleFunctor N` とする。輸送に使う成分同型は `freeZeroTensorPointwiseModuleNatIso N`。

```lean
-- Spectra/SymmetricSequence/PointwiseTensorModule.lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
variable {V : Type u} [Category.{v} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [HasColimitsOfSize.{0, 0} V] [HasLimitsOfSize.{0, 0} V]
  [HasEqualizers (SymmetricSequence V)] [HasCoequalizers (SymmetricSequence V)]
  {N : SymmetricSequence V} [MonObj N] [IsCommMonObj N]
local notation "D" => Mod (SymmetricSequence V) N
local notation "F₀" => SymmetricSequence.freeAt 0 ⋙ MonoidalFreeModule.freeFunctor N

def pointwiseModuleBifunctor (N : SymmetricSequence V) [MonObj N] [IsCommMonObj N] :
    V ⥤ Mod (SymmetricSequence V) N ⥤ Mod (SymmetricSequence V) N
def freeZeroPointwiseModuleBifunctorIso :
    F₀ ⋙ curriedTensor D ≅ pointwiseModuleBifunctor (N := N)

-- Spectra/SymmetricSequence/PointwiseTensorModuleAssociator.lean
lemma pointwiseModuleAssociator_naturality (P Q : V) {X Y : D} (f : X ⟶ Y) :
    ((pointwiseModuleBifunctor (N := N)).obj (P ⊗ Q)).map f ≫
      (pointwiseTensorModuleAssociator N P Q Y).hom =
    (pointwiseTensorModuleAssociator N P Q X).hom ≫
      ((pointwiseModuleBifunctor (N := N)).obj P).map
        (((pointwiseModuleBifunctor (N := N)).obj Q).map f)
def pointwiseModuleAssociatorNatIso (P Q : V) :
    (pointwiseModuleBifunctor (N := N)).obj (P ⊗ Q) ≅
      (pointwiseModuleBifunctor (N := N)).obj Q ⋙
        (pointwiseModuleBifunctor (N := N)).obj P

-- Spectra/SymmetricSequence/PointwiseTensorMapLevels.lean
lemma pointwiseModulePost_level {P P' : V} (p : P ⟶ P') (X : D) (n : ℕ) :
    (((pointwiseModuleBifunctor (N := N)).map p).app X).hom.app
        (FiniteBijection.of n) = p ▷ SymmetricSequence.level X.X n
lemma pointwiseModuleAssociator_parameter
    {P P' Q Q' : V} (p : P ⟶ P') (q' : Q ⟶ Q') (X : D) :
    ((pointwiseModuleBifunctor (N := N)).map (p ⊗ₘ q')).app X ≫
      (pointwiseTensorModuleAssociator N P' Q' X).hom =
    (pointwiseTensorModuleAssociator N P Q X).hom ≫
      ((pointwiseModuleBifunctor (N := N)).map p).app
        (((pointwiseModuleBifunctor (N := N)).obj Q).obj X) ≫
      ((pointwiseModuleBifunctor (N := N)).obj P').map
        (((pointwiseModuleBifunctor (N := N)).map q').app X)
```

```lean
-- Spectra/SymmetricSequence/Convolution.lean（convolutionUnit の隣）
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
variable {V : Type u} [Category.{v} V] [MonoidalCategory V] [HasColimitsOfSize.{0, 0} V]

def pairing (F G : SymmetricSequence V) (p q : ℕ) :
    SymmetricSequence.level F p ⊗ SymmetricSequence.level G q ⟶
      SymmetricSequence.level (SymmetricSequence.convolution F G) (p + q)
lemma pairing_equivariance (F G : SymmetricSequence V) (p q : ℕ)
    (s : Equiv.Perm (Fin p)) (t : Equiv.Perm (Fin q)) :
    (F.map (FiniteBijection.permutation p s) ⊗ₘ
        G.map (FiniteBijection.permutation q t)) ≫ pairing F G p q =
      pairing F G p q ≫ (SymmetricSequence.convolution F G).map
        (FiniteBijection.sumMap (FiniteBijection.permutation p s)
          (FiniteBijection.permutation q t))

-- CategoryTheory/Limits/Zero.lean（新規候補。既存の補題を再利用）
open CategoryTheory CategoryTheory.Limits
variable {M : Type u'} {D : Type u} [Category.{v'} M] [Category.{v} D]
lemma initial_isZero_of_preserves_initial_reflects_terminal (F : M ⥤ D)
    [Limits.HasInitial M] [Limits.HasZeroObject D]
    [Limits.PreservesColimit (Functor.empty.{0} M) F]
    [Limits.ReflectsLimit (Functor.empty.{0} M) F] :
    Limits.IsZero (⊥_ M)
```

最後の型の `D` は任意の通常の圏。初対象の像が初対象なので零対象であり、その終対象性を反映する。対称列の次数・置換を使う型やスペクトルの余接合・ループの式には、対応表の別の既存一般論を使う。

# BS-M15（⑤d）作業報告 — G01 前半（約 10,000 行の途中報告まで）（§75〜§102、2026-11-15）

元の報告：[report-codex-m15.md](../../bhatt-scholze/reports/report-codex-m15.md)

## §75 BS-M15 §8 の受領と G01 の実装開始（11-15）

### 75.1 承認された範囲

G01〜G15、外枠20,000行を受領した。順序はG01〜G03、G04〜G06、G07〜G09、
G10〜G12、G13〜G15。約10,000行で途中報告し、G09のcanonical比較の同値の完成を
途中取り込みの点として報告する。その時点で実装を止めない。
G12の完成後に5a-4mの段0を出す。M15は5∞-2待ちを維持する。
G01の部品を小さく分けても一覧の済みを増やさず、G01の実結論を検収してから1と数える。

### 75.2 全自己関手の合成と walking monad の入力型

新設場所は InfinityCategories/HA/Monads/。BEへの適用はまだない。

- EndofunctorComposition.lean：全Fun(C,C)の合成の単体写像、単位・結合則、
  実際の内部MonObj、元の単体写像f≫gのcurryとの照合。
- EndofunctorSimplicialMonoid.lean：同じ合成を次数ごとのMonCat値単体的対象へ表示し、
  全ての単体作用・単位・積が元の全関手単体集合のものと一致することを示す。
- WalkingMonad.lean：空順序集合を含むΔ₊のnerve、全次数の順序和、単位、
  一点順序集合の指定を、対象Cと同じ宇宙へ持ち上げる。
- NativeMonad.lean：その全単体作用と単位・順序和の保存を持つモナドの型を定義し、
  一点順序集合の作用から実際のunderlying endofunctorを取り出す。

主な型（同じ構成の法則。新しい一覧IDには数えない）：

```lean
EndofunctorSpace (C : SSet.{u}) := (ihom C).obj C
endofunctorComposition C :
  EndofunctorSpace C ⊗ EndofunctorSpace C ⟶ EndofunctorSpace C
endofunctorCompositionMonObj C : MonObj (EndofunctorSpace C)
endofunctorSimplicialMonoid C : SimplicialObject MonCat.{u}
WalkingMonadShape : SSet.{u}
walkingMonadUnit : 𝟙_ SSet.{u} ⟶ WalkingMonadShape
walkingMonadComposition : WalkingMonadShape ⊗ WalkingMonadShape ⟶ WalkingMonadShape

structure NativeMonad (C : SSet.{u}) where
  action : WalkingMonadShape ⟶ EndofunctorSpace C
  map_unit : walkingMonadUnit ≫ action = endofunctorUnit C
  map_composition : walkingMonadComposition ≫ action =
    (action ⊗ₘ action) ≫ endofunctorComposition C

NativeMonad.endofunctor (T : NativeMonad C) : C ⟶ C
```

NativeMonadのデータはh Fun上の通常Monadではなく、N(Δ₊)の全単体からの作用である。
これはG01の構成先の型を定めた段階。与えられたQCatAdjunctionからこの全作用を
構成したことにはしない。G01のinducedNativeMonadと元のF≫UへのFunctorIsoは未完。
このwalking monadの表示とHAのモナドの表示の比較、および同じ単位・余単位の照合も
G01の検収に残す。h Funの随伴を構造の欄へ入れただけでG01完成とはしない。

原典はHA §4.7.2–§4.7.3・Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。
全walking monadの順序和の表示と随伴の全coherenceへの拡張の証明経路として、
[Riehl–Verity, *Homotopy coherent adjunctions and the formal theory of monads*](https://math.jhu.edu/~eriehl/adjunctions.pdf)
Remark 3.3.8、Theorems 4.3.9・4.3.11を確認した。
これらの拡張定理は未証明の引用や追加instanceとして入れていない。

### 75.3 同じ構成の法則の型

`EndofunctorComposition.lean`（NativeMonad.lean内はnamespace NativeMonad）：

```lean
lemma endofunctorUnit_comp (C : SSet.{u}) :
    (λ_ (EndofunctorSpace C)).inv ≫ endofunctorUnit C ▷ _ ≫
      endofunctorComposition C = 𝟙 _

lemma endofunctorComp_unit (C : SSet.{u}) :
    (ρ_ (EndofunctorSpace C)).inv ≫ _ ◁ endofunctorUnit C ≫
      endofunctorComposition C = 𝟙 _

lemma endofunctorComp_assoc (C : SSet.{u}) :
    (α_ _ _ _).inv ≫ endofunctorComposition C ▷ _ ≫ endofunctorComposition C =
      _ ◁ endofunctorComposition C ≫ endofunctorComposition C

lemma endofunctorUnit_eq_curry (C : SSet.{u}) :
    endofunctorUnit C = curry' (𝟙 C)

lemma endofunctorComposition_curry {C : SSet.{u}} (f g : C ⟶ C) :
    (λ_ (𝟙_ SSet)).inv ≫ (curry' f ⊗ₘ curry' g) ≫ endofunctorComposition C =
      curry' (f ≫ g)
```

`EndofunctorSimplicialMonoid.lean`（NativeMonad.lean内はnamespace NativeMonad）：

```lean
lemma endofunctorSimplicialMonoid_obj (C : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    ↥((endofunctorSimplicialMonoid C).obj n) = (EndofunctorSpace C).obj n

lemma endofunctorSimplicialMonoid_map_apply (C : SSet.{u})
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (EndofunctorSpace C).obj n) :
    (endofunctorSimplicialMonoid C).map f x = (EndofunctorSpace C).map f x

lemma endofunctorSimplicialMonoid_one (C : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (1 : (endofunctorSimplicialMonoid C).obj n) =
      (endofunctorUnit C).app n PUnit.unit

lemma endofunctorSimplicialMonoid_mul (C : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (x y : (endofunctorSimplicialMonoid C).obj n) :
    x * y = (endofunctorComposition C).app n (x, y)
```

`NativeMonad.lean`（NativeMonad.lean内はnamespace NativeMonad）：

```lean
lemma ext {T T' : NativeMonad C} (h : T.action = T'.action) : T = T'

lemma curry_endofunctor (T : NativeMonad C) :
    curry' T.endofunctor = (SSet.unitHomEquiv _).symm
      (T.action.app (Opposite.op ⦋0⦌) walkingMonadGenerator)

lemma endofunctor_vertex (T : NativeMonad C) :
    SSet.unitHomEquiv _ (curry' T.endofunctor) =
      T.action.app (Opposite.op ⦋0⦌) walkingMonadGenerator
```

`WalkingMonad.lean`（NativeMonad.lean内はnamespace NativeMonad）：

```lean
lemma walkingMonadComposition_apply (n : SimplexCategoryᵒᵖ)
    (x y : WalkingMonadShape.{u}.obj n) :
    ((walkingMonadComposition).app n (x, y)).down =
      x.down.prod' y.down ⋙ tensor AugmentedSimplexCategory
```

### 75.4 実測と検証の状態

現作業木の追加は4ファイル312行、明示宣言25（structure 1、その他24）。
全てG01の構成・その法則の途中であり、G01〜G15の済みは0のまま。
200行を超える証明はない。M15の検証済み16,936行は変更していない。

最初のEndofunctorComposition（105行の版）は指定のimpl鍵で対象ビルドに成功した。
class値のdefの還元性の警告を受けて@[instance_reducible]を付けた現行106行版は、
他の3ファイルとまとめた再検証の対象にした。
現時点では次の1件だけが生きた実行セッションで共有鍵を待っている：

```text
session 29814
scripts/refactor/with_build_lock.sh --class impl --wait 3600 --
  gtimeout --kill-after=3s 280 lake build
  SerrePositivity.InfinityCategories.HA.Monads.NativeMonad:olean
  SerrePositivity.InfinityCategories.HA.Monads.EndofunctorSimplicialMonoid:olean
```

既存セッションをポーリングして追い、待機を失敗とみなして重複起動しない。
新設の4ファイルの全検証が終わるまでLeanのコミットを保留する。
小さい公理監査の入力は/tmp/g12-small-audit.leanに準備済み（24宣言とNativeMonad.mk）。
監査はまだ実行していない。対象ビルドの終了後、同じimpl鍵でこの監査だけを行う。
大きい監査・rootビルド・他レーンへの書き込みは行っていない。
この節のコミットは、未検証のLeanを検証済みとするものではない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §76 G01 の全合成・walking monad・指定単位の検証（11-15）

### 76.1 検証した範囲と未完の結論

§75の4ファイルを含め、HA/Monads/ の新設8ファイル695行を対象ビルドで検証した。
明示宣言50（構造・inductiveを各1、名前付き局所instanceを1含む）。
小さい公理監査も50宣言の根を全て照合し、依存は標準のpropext・Classical.choice・Quot.soundのみ。
検証済みのG12 Lean累計は **8ファイル695行**。M15の16,936行とは別枠。
全ファイルは125行以下で、200行を超える証明はない。

今回の対象はG01の構成先と法則の部品。**G01自体は未完**。
QCatAdjunctionからNativeMonadを構成するinducedNativeMonadと、指定F≫UへのFunctorIso、
元の単位・余単位との全比較が残る。G01〜G15の一覧の済みは0のままにする。
存在を仮定するinstanceや、元の随伴だけを欄に入れて全coherenceと呼ぶ代用は置いていない。

§75以後に検証したもの：

| ファイル | 行数 | 検証した内容 |
|---|---:|---|
| EndofunctorComposition.lean | 106 | 全自己関手の合成・単位・結合則と実内部MonObj |
| EndofunctorSimplicialMonoid.lean | 62 | 全次数のモノイド表示と元の単体作用との一致 |
| WalkingMonad.lean | 63 | N(Δ₊)と順序和の全単体写像 |
| NativeMonad.lean | 81 | 全作用の型、元のunderlying endofunctorの回収 |
| WalkingMonadLaws.lean | 125 | 順序和の全単位・結合則、実walkingMonadMonObj |
| WalkingMonadEnrichment.lean | 117 | 実単体的豊穣walking monad、全作用と豊穣関手の往復 |
| NativeMonadUnit.lean | 75 | 全作用から同じ恒等関手→同じ自己関手への単位の実辺を回収 |
| AdjunctionRepresentatives.lean | 66 | 元の随伴の単位・余単位の実辺と同じ二胞体の類の照合 |
| **合計** | **695** | G01の途中。新しい一覧IDは加えない |

豊穣関手の値域は、閉構造からのSSetの自己豊穣構造を明示した。
別の既存のSSetの豊穣instanceを暗黙に選んだ場合の合成と混同しない。
名前付き局所instance endofunctorClosedEnrichment は既存の自己豊穣構造そのものであり、
未証明の命題を仮定するinstanceではない。この宣言も監査対象に入れた。

原典はHA §4.7.2–§4.7.3・Proposition 4.7.3.3とKerodon Remark 6.2.1.4（Tag 02EN）。
[Riehl–Verity](https://math.jhu.edu/~eriehl/adjunctions.pdf) Definition 6.1.1の
全coherentなモナドの定義は、N(Δ₊)から全自己Homへの単位と順序和を保つ全単体写像である。
現在のNativeMonadはこの表示を採っている。HAの表示との比較と、随伴からの全拡張の存在は
G01の検収に残す。全拡張には同書Theorems 4.3.9・4.3.11の構成経路を検討している。
これらをsorryや追加公理で導入してはいない。

### 76.2 同じ構成の法則の型

以下の型は各ファイルと同じ変数・準圏性・豊穣構造の文脈で読む。
§75に既出の型は繰り返さない。これら法則の分割で一覧の本数を増やさない。

`WalkingMonadLaws.lean`（NativeMonadの節の宣言はそのnamespace内）：

```lean
lemma ordinalSum_assoc (x y z : AugmentedSimplexCategory) :
    (x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)

lemma ordinalSum_associator_hom (x y z : AugmentedSimplexCategory) :
    (α_ x y z).hom = eqToHom (ordinalSum_assoc x y z)

lemma ordinalSumFunctor_assoc (F G H : I ⥤ AugmentedSimplexCategory) :
    ((F.prod' G ⋙ tensor _).prod' H ⋙ tensor _) =
      (F.prod' (G.prod' H ⋙ tensor _) ⋙ tensor _)

lemma ordinalSum_leftUnit (x : AugmentedSimplexCategory) :
    (WithInitial.star : AugmentedSimplexCategory) ⊗ x = x

lemma ordinalSum_rightUnit (x : AugmentedSimplexCategory) :
    x ⊗ (WithInitial.star : AugmentedSimplexCategory) = x

lemma ordinalSum_leftUnitor_hom (x : AugmentedSimplexCategory) :
    (λ_ x).hom = eqToHom (ordinalSum_leftUnit x)

lemma ordinalSum_rightUnitor_hom (x : AugmentedSimplexCategory) :
    (ρ_ x).hom = eqToHom (ordinalSum_rightUnit x)

lemma ordinalSumFunctor_leftUnit (F : I ⥤ AugmentedSimplexCategory) :
    (((Functor.const I).obj WithInitial.star).prod' F ⋙ tensor _) = F

lemma ordinalSumFunctor_rightUnit (F : I ⥤ AugmentedSimplexCategory) :
    (F.prod' ((Functor.const I).obj WithInitial.star) ⋙ tensor _) = F

@[instance_reducible]
def walkingMonadMonObj : MonObj WalkingMonadShape.{u}
```

`WalkingMonadEnrichment.lean`（NativeMonadの節の宣言はそのnamespace内）：

```lean
instance walkingMonadEnrichedCategory : EnrichedCategory SSet.{u} WalkingMonadObject

local instance endofunctorClosedEnrichment : EnrichedCategory SSet.{u} SSet.{u}

def toEnrichedFunctor (T : NativeMonad C) :
    EnrichedFunctor SSet.{u} WalkingMonadObject SSet.{u}

def ofEnrichedFunctor
    (F : EnrichedFunctor SSet.{u} WalkingMonadObject SSet.{u}) :
    NativeMonad (F.obj .star)

lemma of_toEnrichedFunctor (T : NativeMonad C) :
    ofEnrichedFunctor T.toEnrichedFunctor = T

lemma to_ofEnrichedFunctor (F : EnrichedFunctor SSet.{u} WalkingMonadObject SSet.{u}) :
    (ofEnrichedFunctor F).toEnrichedFunctor = F
```

`NativeMonadUnit.lean`（NativeMonadの節の宣言はそのnamespace内）：

```lean
def walkingMonadArrow {x y : AugmentedSimplexCategory} (f : x ⟶ y) :
    WalkingMonadShape.{u}.Edge (ULift.up (ComposableArrows.mk₀ x))
      (ULift.up (ComposableArrows.mk₀ y))

lemma unit_vertex (T : NativeMonad C) :
    T.action.app (Opposite.op ⦋0⦌)
      (ULift.up (ComposableArrows.mk₀ (WithInitial.star : AugmentedSimplexCategory))) =
        SSet.unitHomEquiv _ (curry' (𝟙 C))

def unitEdge (T : NativeMonad C) :
    (EndofunctorSpace C).Edge (SSet.unitHomEquiv _ (curry' (𝟙 C)))
      (SSet.unitHomEquiv _ (curry' T.endofunctor))

lemma unitEdge_edge (T : NativeMonad C) :
    T.unitEdge.edge = T.action.app (Opposite.op ⦋1⦌)
      (ULift.up (ComposableArrows.mk₁
        (WithInitial.homTo (⦋0⦌ : SimplexCategory))))
```

`AdjunctionRepresentatives.lean`（NativeMonadの節の宣言はそのnamespace内）：

```lean
def adjunctionUnitRepresentative (a : QCatAdjunction F U) :
    ((ihom C).obj C).Edge (functorVertex (𝟙 C)) (functorVertex (F ≫ U))

lemma adjunctionUnitRepresentative_homMk (a : QCatAdjunction F U) :
    SSet.Truncated.HomotopyCategory.homMk (adjunctionUnitRepresentative a).toTruncated =
      a.unitHom

def adjunctionCounitRepresentative (a : QCatAdjunction F U) :
    ((ihom E).obj E).Edge (functorVertex (U ≫ F)) (functorVertex (𝟙 E))

lemma adjunctionCounitRepresentative_homMk (a : QCatAdjunction F U) :
    SSet.Truncated.HomotopyCategory.homMk (adjunctionCounitRepresentative a).toTruncated =
      a.counitHom
```

### 76.3 対象ビルドと小さい監査

全て指定のwith_build_lock.sh --class impl --wait 3600の下で行った。
最初のセッション29814はNativeMonadのcurryの型推論エラーで終了1。
続く63893ではその修正が通り、WalkingMonadLawsの対象等式・関手の等式の引数で終了1。
どちらも終端を確認してから次の枠へ進み、観測のタイムアウトを理由に重複起動していない。

最後のセッション41384は、280秒を上限とする同じimpl枠内で必要な修正を検証した。
対象は次の4つの末端モジュールだけ（その依存として上の8ファイルを覆う）：

```text
lake build
  SerrePositivity.InfinityCategories.HA.Monads.WalkingMonadEnrichment:olean
  SerrePositivity.InfinityCategories.HA.Monads.NativeMonadUnit:olean
  SerrePositivity.InfinityCategories.HA.Monads.EndofunctorSimplicialMonoid:olean
  SerrePositivity.InfinityCategories.HA.Monads.AdjunctionRepresentatives:olean
```

最終の対象ビルドは **G12_BUILD_EXIT=0**、警告なし。
その後、名前付き局所instanceのdocstringを2行追記した。型・定義・証明は変更していない。
この文書2行も上の実測695行に含めた。
続く新設宣言だけの監査 lake env lean /tmp/g12-small-audit.lean は **G12_AUDIT_EXIT=0**。
全50の出力名が監査入力の50名と一致し、sorryAx・追加公理がないことを小さいPython検査でも確認した。
監査の入力（テキスト保存）・根の名前・全出力は
[g12-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-audit-2026-11-15/)に保存した。

枠の外側の終了値は124。これは対象ビルド0・監査0の後、次の操作を待つループが
280秒の上限で終了したものであり、対象ビルドや監査の失敗として扱わない。
両コマンドの成功印と50件の実際の監査出力を確認した。現在はこの実行セッションも終端で、
自分の生きたビルド・監査・待ち整理券はない。全体ビルド・大きい監査は行っていない。

M15のLean、main、⑤a・③系、Interface、draftsには書き込んでいない。
次はG01の未完の全拡張と指定F≫Uの比較を進める。G01未完のままG04以後へ飛ばさない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。外枠20,000行中、検証済み695行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §77 G01：walking adjunction の混合Homの有限順序表示（11-15）

### 77.1 実構成と検証

G01の全拡張の添字に必要な混合Homを進めた。追加は2ファイル398行・明示宣言37。
G12の累計は **10ファイル1,093行・明示宣言87**（§76の695行・50宣言との和）。
G01は未完であり、G01〜G15の一覧の済みは0のまま。
有限順序集合上の随伴を、準圏の全モナドを構成したことに読み替えない。

- OrdinalAdjoints.lean：247行。有限下方fiberの最大による実右随伴、上方fiberの最小による
  実左随伴、端点保存とそれぞれの存在の同値、往復・恒等射・合成則を証明した。
- EndpointSimplex.lean：151行。最小元保存の圏BottomSimplexCategoryと最大元保存の圏
  TopSimplexCategoryを実際に作り、右・左随伴による反変関手と、その往復の関手の等式から
  BottomSimplexCategory ≌ TopSimplexCategoryᵒᵖを構成した。

原典は[Riehl–Verity](https://math.jhu.edu/~eriehl/adjunctions.pdf) Observation 3.3.6・
Remark 3.3.8。これらはHA Proposition 4.7.3.3の全拡張を構成するための
walking adjunctionの混合Homの表示に使う。docstringにはその用途と
Kerodon Remark 6.2.1.4（Tag 02EN）を記した。原典の番号をG01の完成属性として登録してはいない。

G01の残りは、全walking adjunctionの合成とその全拡張、元のF≫Uへの比較、元の単位・余単位との照合。
今回の混合Homの表示だけでこれらを完成とはしない。新しい一覧IDは加えていない。

### 77.2 同じ構成の法則・表示の型

以下は各ファイルと同じ文脈（m,n,k : ℕ、圏構造、端点保存の性質）で読む。
全てG01の構成・その法則の分割。200行を超える宣言・証明はない。
ファイル全体が200行を超えるOrdinalAdjoints.leanの行数は上にも明記した。

`OrdinalAdjoints.lean`：

```lean
def ordinalLowerFiber (f : Fin (m + 1) →o Fin (n + 1)) (j : Fin (n + 1)) :
    Finset (Fin (m + 1))

lemma ordinalLowerFiber_nonempty (f : Fin (m + 1) →o Fin (n + 1))
    (hf : f 0 = 0) (j : Fin (n + 1)) : (ordinalLowerFiber f j).Nonempty

def ordinalRightAdjointValue (f : Fin (m + 1) →o Fin (n + 1))
    (hf : f 0 = 0) (j : Fin (n + 1)) : Fin (m + 1)

lemma ordinalRightAdjointValue_gc (f : Fin (m + 1) →o Fin (n + 1))
    (hf : f 0 = 0) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    f i ≤ j ↔ i ≤ ordinalRightAdjointValue f hf j

def ordinalRightAdjoint (f : Fin (m + 1) →o Fin (n + 1)) (hf : f 0 = 0) :
    Fin (n + 1) →o Fin (m + 1)

lemma ordinalRightAdjoint_gc (f : Fin (m + 1) →o Fin (n + 1)) (hf : f 0 = 0) :
    GaloisConnection f (ordinalRightAdjoint f hf)

lemma ordinalRightAdjoint_last (f : Fin (m + 1) →o Fin (n + 1)) (hf : f 0 = 0) :
    ordinalRightAdjoint f hf (Fin.last n) = Fin.last m

def ordinalUpperFiber (g : Fin (n + 1) →o Fin (m + 1)) (i : Fin (m + 1)) :
    Finset (Fin (n + 1))

lemma ordinalUpperFiber_nonempty (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) (i : Fin (m + 1)) :
    (ordinalUpperFiber g i).Nonempty

def ordinalLeftAdjointValue (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) (i : Fin (m + 1)) : Fin (n + 1)

lemma ordinalLeftAdjointValue_gc (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ordinalLeftAdjointValue g hg i ≤ j ↔ i ≤ g j

def ordinalLeftAdjoint (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) : Fin (m + 1) →o Fin (n + 1)

lemma ordinalLeftAdjoint_gc (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) :
    GaloisConnection (ordinalLeftAdjoint g hg) g

lemma ordinalLeftAdjoint_zero (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) : ordinalLeftAdjoint g hg 0 = 0

lemma ordinal_zero_of_gc {f : Fin (m + 1) →o Fin (n + 1)}
    {g : Fin (n + 1) →o Fin (m + 1)} (h : GaloisConnection f g) : f 0 = 0

lemma ordinal_last_of_gc {f : Fin (m + 1) →o Fin (n + 1)}
    {g : Fin (n + 1) →o Fin (m + 1)} (h : GaloisConnection f g) :
    g (Fin.last n) = Fin.last m

lemma ordinal_rightAdjoint_exists_iff (f : Fin (m + 1) →o Fin (n + 1)) :
    (∃ g : Fin (n + 1) →o Fin (m + 1), GaloisConnection f g) ↔ f 0 = 0

lemma ordinal_leftAdjoint_exists_iff (g : Fin (n + 1) →o Fin (m + 1)) :
    (∃ f : Fin (m + 1) →o Fin (n + 1), GaloisConnection f g) ↔
      g (Fin.last n) = Fin.last m

lemma ordinal_left_right (f : Fin (m + 1) →o Fin (n + 1)) (hf : f 0 = 0) :
    ordinalLeftAdjoint (ordinalRightAdjoint f hf) (ordinalRightAdjoint_last f hf) = f

lemma ordinal_right_left (g : Fin (n + 1) →o Fin (m + 1))
    (hg : g (Fin.last n) = Fin.last m) :
    ordinalRightAdjoint (ordinalLeftAdjoint g hg) (ordinalLeftAdjoint_zero g hg) = g

lemma ordinalRightAdjoint_id (m : ℕ) :
    ordinalRightAdjoint (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) rfl = OrderHom.id

lemma ordinalRightAdjoint_comp (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (n + 1) →o Fin (k + 1)) (hf : f 0 = 0) (hg : g 0 = 0) :
    ordinalRightAdjoint (g.comp f) (by change g (f 0) = 0; rw [hf, hg]) =
      (ordinalRightAdjoint f hf).comp (ordinalRightAdjoint g hg)

lemma ordinalLeftAdjoint_id (m : ℕ) :
    ordinalLeftAdjoint (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) rfl = OrderHom.id

lemma ordinalLeftAdjoint_comp (f : Fin (n + 1) →o Fin (m + 1))
    (g : Fin (k + 1) →o Fin (n + 1))
    (hf : f (Fin.last n) = Fin.last m) (hg : g (Fin.last k) = Fin.last n) :
    ordinalLeftAdjoint (f.comp g) (by change f (g (Fin.last k)) = Fin.last m; rw [hg, hf]) =
      (ordinalLeftAdjoint g hg).comp (ordinalLeftAdjoint f hf)
```

`EndpointSimplex.lean`：

```lean
def simplexPreservesBottom : MorphismProperty SimplexCategory

instance simplexPreservesBottom_multiplicative : simplexPreservesBottom.IsMultiplicative

def simplexPreservesTop : MorphismProperty SimplexCategory

instance simplexPreservesTop_multiplicative : simplexPreservesTop.IsMultiplicative

abbrev BottomSimplexCategory

abbrev TopSimplexCategory

def bottomSimplexRightAdjoint {X Y : BottomSimplexCategory} (f : X ⟶ Y) :
    (⟨Y.obj⟩ : TopSimplexCategory) ⟶ ⟨X.obj⟩

def topSimplexLeftAdjoint {X Y : TopSimplexCategory} (g : X ⟶ Y) :
    (⟨Y.obj⟩ : BottomSimplexCategory) ⟶ ⟨X.obj⟩

def bottomSimplexToTopOp : BottomSimplexCategory ⥤ TopSimplexCategoryᵒᵖ

def topOpSimplexToBottom : TopSimplexCategoryᵒᵖ ⥤ BottomSimplexCategory

lemma bottomSimplex_roundtrip : bottomSimplexToTopOp ⋙ topOpSimplexToBottom =
    𝟭 BottomSimplexCategory

lemma topSimplex_roundtrip : topOpSimplexToBottom ⋙ bottomSimplexToTopOp =
    𝟭 TopSimplexCategoryᵒᵖ

def endpointSimplexEquivalence : BottomSimplexCategory ≌ TopSimplexCategoryᵒᵖ
```

### 77.3 対象検証と今回の受け渡し

セッション61416をwith_build_lock.sh --class impl --wait 3600、最大280秒のimpl枠で検証した。
対象はlake build SerrePositivity.InfinityCategories.HA.Monads.EndpointSimplex:oleanだけ。
依存にOrdinalAdjointsを含む。初回の型推論・importのエラーを同じ短い枠で修正し、
最終 **G12_ORDINAL_BUILD_EXIT=0**、警告なし。
続く新設37宣言の小さい監査は **G12_ORDINAL_AUDIT_EXIT=0**。
全37の出力名が入力と一致し、公理依存は標準のpropext・Classical.choice・Quot.soundのみ。
追加公理・sorryAxはない。監査後に枠へexitを渡して明示的に返却し、外側の終了値も0。
自分の生きたビルド・監査・待ち整理券はない。

監査の入力・根の名前・全出力は[g12-ordinal-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-ordinal-audit-2026-11-15/)へ保存した。
§76の既存8ファイルは変更していない。M15のLean・drafts・main・⑤a・③系・Interfaceには書き込んでいない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み1,093行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §78 G01：混合Homの4つの水平合成の双関手（11-15）

### 78.1 実構成の範囲

G01のwalking adjunctionの水平合成を進めた。追加は2ファイル331行・明示宣言22。
G12の検証済み累計は **12ファイル1,424行・明示宣言109**。
G01自体は未完であり、一覧の済みは0のまま。

| ファイル | 行数 | 構成・法則 |
|---|---:|---|
| OrdinalSumFunctor.lean | 106 | 非空順序和の実双関手、両側の包含、片側の因子だけからの端点保存 |
| EndpointOrdinalActions.lean | 225 | 空順序集合を含む左右の合成の実関手族、包含の全自然性、反対側の2つの双関手 |
| **追加** | **331** | G01の構成とその法則の分割。新しい一覧IDは加えない |

直接の二つはΔ₊×Δ∞→Δ∞とΔ−∞×Δ₊→Δ−∞。
既存の順序和と端点の包含から非空の場合の全関手族を作り、WithInitial.liftで
空順序集合の値を同じ恒等関手として拡張した。構成済みのGalois双対と反対圏を通じ、
Δ₊ᵒᵖ×Δ−∞→Δ−∞とΔ∞×Δ₊ᵒᵖ→Δ∞も実双関手として構成した。
対象の値だけでなく、両変数の射の合成・自然性を含む。

原典は[Riehl–Verity](https://math.jhu.edu/~eriehl/adjunctions.pdf) Remark 3.3.8。
HA Proposition 4.7.3.3 の全拡張の添字の構成に使い、docstringにもその用途と
Kerodon Remark 6.2.1.4（Tag 02EN）を記した。

**未完との境界**：これらのActionという名前の宣言は水平合成の双関手を構成した段階。
walking adjunction全体の結合則を検収した意味ではない。
混合Hom同士の二つの水平合成（区間表示を通るもの）、全体の結合・単位の法則、
元の∞随伴からの全拡張、そのF≫U・元の単位・余単位との比較がG01に残る。
今回の4双関手の対象ビルドを、これらの未完部分の検証の代わりに使わない。

### 78.2 同じ構成の型と法則

以下は各ファイルと同じ圏構造と変数の文脈で読む。
200行を超える宣言・証明はない。ファイル全体が200行を超えるものの行数は上表に示した。

`OrdinalSumFunctor.lean`：

```lean
def simplexOrdinalSum : SimplexCategory × SimplexCategory ⥤ SimplexCategory

lemma simplexOrdinalSum_inl {x₁ x₂ y₁ y₂ : SimplexCategory}
    (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    inl' x₁ x₂ ≫ tensorHomOf f g = f ≫ inl' y₁ y₂

lemma simplexOrdinalSum_inr {x₁ x₂ y₁ y₂ : SimplexCategory}
    (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    inr' x₁ x₂ ≫ tensorHomOf f g = g ≫ inr' y₁ y₂

lemma simplexOrdinalSum_inl_zero (x y : SimplexCategory) :
    (inl' x y).toOrderHom 0 = 0

lemma simplexOrdinalSum_inr_last (x y : SimplexCategory) :
    (inr' x y).toOrderHom (Fin.last y.len) = Fin.last (tensorObjOf x y).len

lemma simplexOrdinalSum_preservesBottom {x₁ x₂ y₁ y₂ : SimplexCategory}
    (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) (hf : simplexPreservesBottom f) :
    simplexPreservesBottom (tensorHomOf f g)

lemma simplexOrdinalSum_preservesTop {x₁ x₂ y₁ y₂ : SimplexCategory}
    (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) (hg : simplexPreservesTop g) :
    simplexPreservesTop (tensorHomOf f g)
```

`EndpointOrdinalActions.lean`：

```lean
def topOrdinalPrefix : SimplexCategory ⥤ TopSimplexCategory ⥤ TopSimplexCategory

def topOrdinalPrefixInclusion (x : SimplexCategory) :
    𝟭 TopSimplexCategory ⟶ topOrdinalPrefix.obj x

lemma topOrdinalPrefixInclusion_naturality {x y : SimplexCategory} (f : x ⟶ y) :
    topOrdinalPrefixInclusion x ≫ topOrdinalPrefix.map f = topOrdinalPrefixInclusion y

def topOrdinalPrefixExtended :
    AugmentedSimplexCategory ⥤ TopSimplexCategory ⥤ TopSimplexCategory

def topOrdinalAction : AugmentedSimplexCategory × TopSimplexCategory ⥤ TopSimplexCategory

lemma topOrdinalPrefixExtended_empty :
    topOrdinalPrefixExtended.obj WithInitial.star = 𝟭 TopSimplexCategory

def bottomOrdinalSuffix : SimplexCategory ⥤ BottomSimplexCategory ⥤ BottomSimplexCategory

def bottomOrdinalSuffixInclusion (x : SimplexCategory) :
    𝟭 BottomSimplexCategory ⟶ bottomOrdinalSuffix.obj x

lemma bottomOrdinalSuffixInclusion_naturality {x y : SimplexCategory} (f : x ⟶ y) :
    bottomOrdinalSuffixInclusion x ≫ bottomOrdinalSuffix.map f =
      bottomOrdinalSuffixInclusion y

def bottomOrdinalSuffixExtended :
    AugmentedSimplexCategory ⥤ BottomSimplexCategory ⥤ BottomSimplexCategory

def bottomOrdinalAction :
    BottomSimplexCategory × AugmentedSimplexCategory ⥤ BottomSimplexCategory

lemma bottomOrdinalSuffixExtended_empty :
    bottomOrdinalSuffixExtended.obj WithInitial.star = 𝟭 BottomSimplexCategory

def topToBottomOpEquivalence : TopSimplexCategory ≌ BottomSimplexCategoryᵒᵖ

def bottomOppositeOrdinalAction :
    AugmentedSimplexCategoryᵒᵖ × BottomSimplexCategory ⥤ BottomSimplexCategory

def topOppositeOrdinalAction :
    TopSimplexCategory × AugmentedSimplexCategoryᵒᵖ ⥤ TopSimplexCategory
```

### 78.3 対象ビルド・小さい監査

全てwith_build_lock.sh --class impl --wait 3600の下、280秒以内の短いimpl枠で実施した。
対象はlake build SerrePositivity.InfinityCategories.HA.Monads.EndpointOrdinalActions:olean。
依存としてOrdinalSumFunctorを含む。初回の7162は、双関手の型推論と合成の照合を修正中に
280秒の上限で終了124。実行セッションの終端を確認してから77967の新しい枠に進んだ。

修正の要点は、積圏の3対象を明示し、自然変換の合成成分と広部分圏の底の射の合成を
同じ式へ展開すること。初期の型エラーに続いてLeanのコード生成のpanic出力も出たが、
全ての型エラーを除いた最終の対象ビルドは **G12_ACTION_BUILD_EXIT=0**、警告なしで通った。
コンパイラの検査を無効にしたり、追加公理・sorryで埋めたりはしていない。

続く新設22宣言の小さい公理監査は **G12_ACTION_AUDIT_EXIT=0**。
出力名22件が入力と一致し、依存は標準のpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理はない。監査後にexitを渡して明示的に返却し、外側の終了値も0。
自分の生きたビルド・監査・待ち整理券はない。

監査入力・根の名前・全出力と最終対象ビルドのログは
[g12-action-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-action-audit-2026-11-15/)へ保存した。
既存の10ファイルは変更していない。M15のLean・drafts・main・⑤a・③系・Interfaceには書き込んでいない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み1,424行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §79 G01：区間表示の射の実構成と相互逆（11-15）

### 79.1 空を含む有限順序射と区間射の対応

G01の残る混合Hom同士の水平合成に必要な区間表示を、有限順序射の段階で進めた。
追加は2ファイル284行・明示宣言24。検証済みのG12累計は
**14ファイル1,708行・明示宣言133**。G01は未完で一覧の済みは0のまま。

| ファイル | 行数 | 検証した実構成 |
|---|---:|---|
| OrdinalAdjoinTop.lean | 145 | 最大元付加、最大元の反映、元の点への制限、付加・制限の往復、恒等・合成則 |
| OrdinalIntervalHom.lean | 139 | 付加した射の実左随伴による区間射、両端点保存、実右随伴からの逆変換、全単射と反変合成 |
| **追加** | **284** | G01の同じ添字の構成・法則の分割 |

有限順序集合の点の個数をm,nとし、**m=0・n=0も含める**。
元の単調射f : Fin m →o Fin nに最大元を付加してから実左Galois随伴を取り、
Fin(n+1)→oFin(m+1)の両端点を保つ射を構成した。
逆は、区間射の実右随伴が最大元を反映することを証明し、その元の点への制限で作る。
いずれも実際の有限単調射の構成であり、逆変換の存在を仮定していない。

原典は[Riehl–Verity](https://math.jhu.edu/~eriehl/adjunctions.pdf) Remark 3.3.8の
区間表示ir:Δ₊ᵒᵖ→Δ₊と、その表示を通る混合Hom同士の合成。
docstringにはHA Proposition 4.7.3.3への用途と、Kerodon Remark 6.2.1.4（Tag 02EN）も記した。

**未完との境界**：今回の完成は、数値添字の有限順序射の全単射と反変合成の法則。
増大単体圏と両端点保存の圏の間の全関手への包装、区間表示を使う二つの混合Hom同士の合成、
walking adjunction全体の結合・単位の法則と、元の∞随伴からの全拡張はまだ残る。
F≫U・元の単位・余単位の検収も未完。これらを今回の全単射から証明済みとはしない。
新しい一覧IDは加えていない。200行を超える宣言・証明はない。

### 79.2 同じ構成と法則の型

以下は各ファイルと同じm,n,k : ℕの文脈で読む。

`OrdinalAdjoinTop.lean`：

```lean
def ordinalAdjoinTop (f : Fin m →o Fin n) : Fin (m + 1) →o Fin (n + 1)

@[simp] lemma ordinalAdjoinTop_castSucc (f : Fin m →o Fin n) (i : Fin m) :
    ordinalAdjoinTop f i.castSucc = (f i).castSucc

@[simp] lemma ordinalAdjoinTop_last (f : Fin m →o Fin n) :
    ordinalAdjoinTop f (Fin.last m) = Fin.last n

lemma ordinalAdjoinTop_reflectsLast (f : Fin m →o Fin n) (i : Fin (m + 1)) :
    ordinalAdjoinTop f i = Fin.last n ↔ i = Fin.last m

lemma ordinalAdjoinTop_injective : Function.Injective
    (ordinalAdjoinTop : (Fin m →o Fin n) → _)

lemma ordinalAdjoinTop_id (m : ℕ) :
    ordinalAdjoinTop (OrderHom.id : Fin m →o Fin m) = OrderHom.id

lemma ordinalAdjoinTop_comp (f : Fin m →o Fin n) (g : Fin n →o Fin k) :
    ordinalAdjoinTop (g.comp f) = (ordinalAdjoinTop g).comp (ordinalAdjoinTop f)

lemma ordinalRemoveTop_bound (g : Fin (m + 1) →o Fin (n + 1))
    (hg : ∀ i, g i = Fin.last n ↔ i = Fin.last m) (i : Fin m) :
    (g i.castSucc).val < n

def ordinalRemoveTop (g : Fin (m + 1) →o Fin (n + 1))
    (hg : ∀ i, g i = Fin.last n ↔ i = Fin.last m) : Fin m →o Fin n

lemma ordinalRemoveTop_castSucc (g : Fin (m + 1) →o Fin (n + 1))
    (hg : ∀ i, g i = Fin.last n ↔ i = Fin.last m) (i : Fin m) :
    (ordinalRemoveTop g hg i).castSucc = g i.castSucc

lemma ordinalRemoveTop_adjoin (f : Fin m →o Fin n) :
    ordinalRemoveTop (ordinalAdjoinTop f) (ordinalAdjoinTop_reflectsLast f) = f

lemma ordinalAdjoinTop_remove (g : Fin (m + 1) →o Fin (n + 1))
    (hg : ∀ i, g i = Fin.last n ↔ i = Fin.last m)
    (ht : g (Fin.last m) = Fin.last n) :
    ordinalAdjoinTop (ordinalRemoveTop g hg) = g
```

`OrdinalIntervalHom.lean`：

```lean
def ordinalIntervalMap (f : Fin m →o Fin n) : Fin (n + 1) →o Fin (m + 1)

lemma ordinalIntervalMap_gc (f : Fin m →o Fin n) :
    GaloisConnection (ordinalIntervalMap f) (ordinalAdjoinTop f)

lemma ordinalIntervalMap_zero (f : Fin m →o Fin n) : ordinalIntervalMap f 0 = 0

lemma ordinalIntervalMap_last (f : Fin m →o Fin n) :
    ordinalIntervalMap f (Fin.last n) = Fin.last m

lemma intervalRightAdjoint_reflectsLast (l : Fin (n + 1) →o Fin (m + 1))
    (h₀ : l 0 = 0) (h₁ : l (Fin.last n) = Fin.last m) (i : Fin (m + 1)) :
    ordinalRightAdjoint l h₀ i = Fin.last n ↔ i = Fin.last m

def ordinalRecoverMap (l : Fin (n + 1) →o Fin (m + 1))
    (h₀ : l 0 = 0) (h₁ : l (Fin.last n) = Fin.last m) : Fin m →o Fin n

lemma ordinalRecoverMap_adjoin (l : Fin (n + 1) →o Fin (m + 1))
    (h₀ : l 0 = 0) (h₁ : l (Fin.last n) = Fin.last m) :
    ordinalAdjoinTop (ordinalRecoverMap l h₀ h₁) = ordinalRightAdjoint l h₀

lemma ordinalRecoverMap_interval (f : Fin m →o Fin n) :
    ordinalRecoverMap (ordinalIntervalMap f) (ordinalIntervalMap_zero f)
      (ordinalIntervalMap_last f) = f

lemma ordinalIntervalMap_recover (l : Fin (n + 1) →o Fin (m + 1))
    (h₀ : l 0 = 0) (h₁ : l (Fin.last n) = Fin.last m) :
    ordinalIntervalMap (ordinalRecoverMap l h₀ h₁) = l

def ordinalIntervalHomEquiv (m n : ℕ) :
    (Fin m →o Fin n) ≃
      {l : Fin (n + 1) →o Fin (m + 1) // l 0 = 0 ∧ l (Fin.last n) = Fin.last m}

lemma ordinalIntervalMap_id (m : ℕ) :
    ordinalIntervalMap (OrderHom.id : Fin m →o Fin m) = OrderHom.id

lemma ordinalIntervalMap_comp (f : Fin m →o Fin n) (g : Fin n →o Fin k) :
    ordinalIntervalMap (g.comp f) = (ordinalIntervalMap f).comp (ordinalIntervalMap g)
```

### 79.3 対象ビルドと小さい監査

セッション19627をwith_build_lock.sh --class impl --wait 3600、最大280秒の短いimpl枠で検証した。
対象はlake build SerrePositivity.InfinityCategories.HA.Monads.OrdinalIntervalHom:olean。
依存にOrdinalAdjoinTopを含む。初回はFin.lastCasesの引数と値の簡約で失敗し、
同じ短い枠内で、射の定義と場合分けの簡約を明示して修正した。
最終 **G12_INTERVAL_BUILD_EXIT=0**、警告なし。

続く新設24宣言の小さい監査は **G12_INTERVAL_AUDIT_EXIT=0**。
出力名24件が入力の24名と一致し、公理依存は標準のpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理はない。監査後にexitを渡し、外側も終了0で枠を返却した。
現在、自分の生きたビルド・監査・待ち整理券はない。

監査入力・根の名前・全出力と最終対象ビルドのログは
[g12-interval-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-interval-audit-2026-11-15/)へ保存した。
既存の12ファイルは変更していない。M15のLean・drafts・main・⑤a・③系・Interfaceには書き込んでいない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み1,708行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。


## §80 G01：区間表示の実同値と残る二つの混合水平合成（11-15）

### 80.1 実装と検収の境界

G01の区間表示を、Homの全単射から実関手・実同値へまとめた。
追加はAugmentedOrdinalMaps.leanの134行とOrdinalIntervalFunctor.leanの162行、
計2ファイル296行・明示宣言22。累計 **16ファイル2,004行・明示宣言155**。

augmentedOrderHomEquivは空も含む有限順序射と増大単体圏の射の実全単射。
ordinalIntervalRepresentationはその反対圏から両端点保存の単体圏への実関手で、
忠実性・充満性・本質的全射性を実際に証明した。IsEquivalenceを引数に仮定せず、
これらの証明から逆関手・単位・余単位を持つordinalIntervalEquivalenceを構成した。
両端点保存の順序和bottomTopIntervalSumとこの逆からmixedBottomTopOrdinalを作り、
Galois双対と反対圏を経てmixedTopBottomOrdinalも実双関手として作った。

これで8通りの水平合成の実双関手のデータは揃ったが、全組合せの結合則・単位則を
備えたwalking adjunctionにはまだ組み上げていない。一般の同値の逆を使う箇所は、
必要な対象等式・自然性の法則を次に照合する。元のQCatAdjunctionからの全拡張、
F≫Uとの比較、元の単位・余単位との照合も未完。G01を完成とは数えない。
原典はHA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8、
Kerodon Remark 6.2.1.4（Tag 02EN）。原典番号を完成属性としては登録していない。

### 80.2 同じ構成の法則・表示の型

以下はnamespace SerrePositivity.InfinityCategories.HA.Monads内。
新しい一覧IDは加えず、G01の構成とその法則の分割として報告する。
200行を超える宣言・証明はない。

```lean
abbrev augmentedOrdinalCard : AugmentedSimplexCategory → ℕ
  | .star => 0
  | .of x => x.len + 1

/-- 概要：点の個数から同じ増大単体圏の対象を作る。
方針：0か後続数かで分ける。規約：指定された骨格の対象。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の対象の逆。 -/
def augmentedOrdinalOfCard : ℕ → AugmentedSimplexCategory
  | 0 => .star
  | n + 1 => .of (SimplexCategory.mk n)

/-- 概要：個数から作った対象は指定された点の個数を持つ。
方針：自然数を場合分けする。規約：空の場合も含む。
使われ方：Riehl–Verity Remark 3.3.8 の本質的全射性。 -/
@[simp] lemma augmentedOrdinalCard_ofCard (n : ℕ) :
    augmentedOrdinalCard (augmentedOrdinalOfCard n) = n

def augmentedOrdinalOfCard : ℕ → AugmentedSimplexCategory
  | 0 => .star
  | n + 1 => .of (SimplexCategory.mk n)

/-- 概要：個数から作った対象は指定された点の個数を持つ。
方針：自然数を場合分けする。規約：空の場合も含む。
使われ方：Riehl–Verity Remark 3.3.8 の本質的全射性。 -/
@[simp] lemma augmentedOrdinalCard_ofCard (n : ℕ) :
    augmentedOrdinalCard (augmentedOrdinalOfCard n) = n

@[simp] lemma augmentedOrdinalCard_ofCard (n : ℕ) :
    augmentedOrdinalCard (augmentedOrdinalOfCard n) = n

def augmentedOrderHom {X Y : AugmentedSimplexCategory} (f : X ⟶ Y) :
    Fin (augmentedOrdinalCard X) →o Fin (augmentedOrdinalCard Y)

def augmentedHomOfOrder (X Y : AugmentedSimplexCategory)
    (f : Fin (augmentedOrdinalCard X) →o Fin (augmentedOrdinalCard Y)) : X ⟶ Y

lemma augmentedHomOfOrder_order {X Y : AugmentedSimplexCategory} (f : X ⟶ Y) :
    augmentedHomOfOrder X Y (augmentedOrderHom f) = f

lemma augmentedOrderHom_ofOrder (X Y : AugmentedSimplexCategory)
    (f : Fin (augmentedOrdinalCard X) →o Fin (augmentedOrdinalCard Y)) :
    augmentedOrderHom (augmentedHomOfOrder X Y f) = f

def augmentedOrderHomEquiv (X Y : AugmentedSimplexCategory) :
    (X ⟶ Y) ≃ (Fin (augmentedOrdinalCard X) →o Fin (augmentedOrdinalCard Y))

@[simp] lemma augmentedOrderHom_id (X : AugmentedSimplexCategory) :
    augmentedOrderHom (𝟙 X) = OrderHom.id

@[simp] lemma augmentedOrderHom_comp {X Y Z : AugmentedSimplexCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    augmentedOrderHom (f ≫ g) = (augmentedOrderHom g).comp (augmentedOrderHom f)

def simplexPreservesEndpoints : MorphismProperty SimplexCategory

instance simplexPreservesEndpoints_multiplicative :
    simplexPreservesEndpoints.IsMultiplicative

abbrev IntervalSimplexCategory

def ordinalIntervalRepresentation : AugmentedSimplexCategoryᵒᵖ ⥤ IntervalSimplexCategory

instance ordinalIntervalRepresentation_faithful : ordinalIntervalRepresentation.Faithful

instance ordinalIntervalRepresentation_full : ordinalIntervalRepresentation.Full

instance ordinalIntervalRepresentation_essSurj : ordinalIntervalRepresentation.EssSurj

instance ordinalIntervalRepresentation_isEquivalence :
    ordinalIntervalRepresentation.IsEquivalence

def ordinalIntervalEquivalence : AugmentedSimplexCategoryᵒᵖ ≌ IntervalSimplexCategory

def bottomTopIntervalSum :
    BottomSimplexCategory × TopSimplexCategory ⥤ IntervalSimplexCategory

def mixedBottomTopOrdinal :
    BottomSimplexCategory × TopSimplexCategory ⥤ AugmentedSimplexCategoryᵒᵖ

def mixedTopBottomOrdinal :
    TopSimplexCategory × BottomSimplexCategory ⥤ AugmentedSimplexCategory
```

### 80.3 対象ビルドと小さい監査

対象ビルドはwith_build_lock.sh --class impl --wait 3600の短い280秒のimpl枠で、
lake build SerrePositivity.InfinityCategories.HA.Monads.OrdinalIntervalFunctor:olean。
依存のAugmentedOrdinalMapsも含めて成功、警告なし（最終ログ1163 jobs）。
前の対話式枠は終了済みで、新設22宣言の監査は別の最大240秒のimpl枠
（セッション67429、待ち時間は別）で実行し、外側の終了0まで確認した。
入力名22件と出力名22件は一致し、公理依存は標準のpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理はない。監査入力・根・全出力と対象ビルドログを
[g12-functor-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-functor-audit-2026-11-15/)に保存した。
現在、自分の生きたビルド・監査・整理券はない。

既存の14ファイル、M15のLean、drafts、main、⑤aのファイル、Interfaceには書き込んでいない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み2,004行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。


## §81 G01：逆区間表示の厳密な往復と、全水平合成の対象の法則（11-15）

### 81.1 実装と残る検収

§80の実区間同値の逆を使う箇所について、選択した逆関手の対象・往復を照合した。
さらに、walking adjunctionの二対象・四Hom圏・八つの水平合成を同じ型族に組み合わせた。
今回の追加は次の2ファイル401行・明示した根33（構成子2件は別）。
累計 **18ファイル2,405行・明示宣言188**。一覧の済みは0のまま。

| ファイル（InfinityCategories/HA/Monads/） | 行数 | 今回の検収 |
|---|---:|---|
| OrdinalIntervalLaws.lean | 182 | 増大単体圏・区間圏の同型の剛性、実区間同値の往復の関手等式、逆・混合合成の対象の個数と正準の対象等式 |
| WalkingAdjunctionComposition.lean | 219 | 二対象・四Hom圏・八実双関手、重みの単射性と加法則、全対象の結合則・左右単位則 |
| **追加** | **401** | G01の同じ構成と法則の分割。新しい一覧IDは加えない |

一般の同値の逆を使っていることから対象の一致を推測せず、
実際の単位・余単位と、同型の射がeqToHomになることから関手そのものの往復等式を証明した。
逆区間表示の対象の個数は元の区間の次元であり、二つの混合合成の個数は
X.obj.len + Y.obj.len + 1になる。全ての逆は§80の構成済みの同値から来ている。

水平合成の引数は「先に使う射、後に使う射」の順。
Riehl–Verityのwalking adjunctionの水平反対を採る規約で、
Hom(plus,plus)=Δ₊、Hom(minus,minus)=Δ₊ᵒᵖ、
Hom(plus,minus)=最大元保存、Hom(minus,plus)=最小元保存とした。
これによりplusの自己Homの順序和を既存NativeMonadの積と合わせる。
これは向きの規約であり、対象の型を取り替えたというだけで元の随伴との比較を済みとはしない。

四Homの共通の重みは順に点の個数、反対の点の個数、次元、次元+1。
重みが対象を区別し、全水平合成の重みが加法になることから、対象の全16組の結合則と
左右単位則を同じ型で証明した。ただし**射についての結合則・単位則は未完**。
EnrichedCategoryのinstanceを宣言せず、豊穣walking adjunctionの完成とは数えない。
元のQCatAdjunctionからの全拡張、F≫Uとの比較、元の単位・余単位との照合も残る。

原典はHA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8、
Kerodon Remark 6.2.1.4（Tag 02EN）。完成の引用属性はまだ登録していない。
200行を超える宣言・証明はない（219行はファイル全体）。

### 81.2 同じ構成の法則の型

以下はnamespace SerrePositivity.InfinityCategories.HA.Monads内。
WalkingAdjunctionPointとその構成子は同じG01のwalking adjunctionの添字。

```lean
@[simp] lemma augmentedOrdinalOfCard_card (X : AugmentedSimplexCategory) :
    augmentedOrdinalOfCard (augmentedOrdinalCard X) = X

lemma augmentedOrdinalCard_injective : Function.Injective augmentedOrdinalCard

lemma augmentedIso_obj_eq {X Y : AugmentedSimplexCategory} (e : X ≅ Y) : X = Y

lemma augmentedIso_hom_eqToHom {X Y : AugmentedSimplexCategory} (e : X ≅ Y) :
    e.hom = eqToHom (augmentedIso_obj_eq e)

lemma augmentedOpIso_obj_eq {X Y : AugmentedSimplexCategoryᵒᵖ} (e : X ≅ Y) : X = Y

lemma augmentedOpIso_hom_eqToHom {X Y : AugmentedSimplexCategoryᵒᵖ} (e : X ≅ Y) :
    e.hom = eqToHom (augmentedOpIso_obj_eq e)

lemma intervalIso_obj_eq {X Y : IntervalSimplexCategory} (e : X ≅ Y) : X = Y

lemma intervalIso_hom_eqToHom {X Y : IntervalSimplexCategory} (e : X ≅ Y) :
    e.hom = eqToHom (intervalIso_obj_eq e)

lemma ordinalInterval_source_roundtrip :
    ordinalIntervalRepresentation ⋙ ordinalIntervalEquivalence.inverse =
      𝟭 AugmentedSimplexCategoryᵒᵖ

lemma ordinalInterval_target_roundtrip :
    ordinalIntervalEquivalence.inverse ⋙ ordinalIntervalRepresentation =
      𝟭 IntervalSimplexCategory

lemma ordinalInterval_inverse_card (X : IntervalSimplexCategory) :
    augmentedOrdinalCard (ordinalIntervalEquivalence.inverse.obj X).unop = X.obj.len

lemma ordinalInterval_inverse_obj (X : IntervalSimplexCategory) :
    ordinalIntervalEquivalence.inverse.obj X = op (augmentedOrdinalOfCard X.obj.len)

lemma mixedBottomTopOrdinal_card (X : BottomSimplexCategory) (Y : TopSimplexCategory) :
    augmentedOrdinalCard (mixedBottomTopOrdinal.obj (X, Y)).unop =
      X.obj.len + Y.obj.len + 1

lemma mixedBottomTopOrdinal_obj (X : BottomSimplexCategory) (Y : TopSimplexCategory) :
    mixedBottomTopOrdinal.obj (X, Y) =
      op (augmentedOrdinalOfCard (X.obj.len + Y.obj.len + 1))

lemma mixedTopBottomOrdinal_card (X : TopSimplexCategory) (Y : BottomSimplexCategory) :
    augmentedOrdinalCard (mixedTopBottomOrdinal.obj (X, Y)) =
      X.obj.len + Y.obj.len + 1

lemma mixedTopBottomOrdinal_obj (X : TopSimplexCategory) (Y : BottomSimplexCategory) :
    mixedTopBottomOrdinal.obj (X, Y) =
      augmentedOrdinalOfCard (X.obj.len + Y.obj.len + 1)

inductive WalkingAdjunctionPoint where
  | plus
  | minus

def walkingAdjunctionHom : WalkingAdjunctionPoint → WalkingAdjunctionPoint → Type
  | .plus, .plus => AugmentedSimplexCategory
  | .plus, .minus => TopSimplexCategory
  | .minus, .plus => BottomSimplexCategory
  | .minus, .minus => AugmentedSimplexCategoryᵒᵖ

/-- 概要：四つのHomはそれぞれ構成済みの実圏。
方針：対象を場合分けする。規約：Homの圏構造を引数の仮定にしない。
使われ方：Riehl–Verity Remark 3.3.8 の全単体のnerve。 -/
instance walkingAdjunctionHom_category (X Y : WalkingAdjunctionPoint) :
    Category (walkingAdjunctionHom X Y)

instance walkingAdjunctionHom_category (X Y : WalkingAdjunctionPoint) :
    Category (walkingAdjunctionHom X Y)

def walkingAdjunctionHorizontal : (X Y Z : WalkingAdjunctionPoint) →
    walkingAdjunctionHom X Y × walkingAdjunctionHom Y Z ⥤ walkingAdjunctionHom X Z
  | .plus, .plus, .plus => tensor AugmentedSimplexCategory
  | .plus, .plus, .minus => topOrdinalAction
  | .plus, .minus, .plus => mixedTopBottomOrdinal
  | .plus, .minus, .minus => topOppositeOrdinalAction
  | .minus, .plus, .plus => bottomOrdinalAction
  | .minus, .plus, .minus => mixedBottomTopOrdinal
  | .minus, .minus, .plus => bottomOppositeOrdinalAction
  | .minus, .minus, .minus =>
      (prodOpEquiv (C

def walkingAdjunctionIdentity : (X : WalkingAdjunctionPoint) → walkingAdjunctionHom X X
  | .plus => WithInitial.star
  | .minus => op WithInitial.star

/-- 概要：四つのHomの対象を共通の非負整数の重みで表す。
方針：最小元保存側だけ次元に1を加える。規約：左随伴の生成射の重みは0。
使われ方：Riehl–Verity Remark 3.3.8 の全対象の結合則。 -/
def walkingAdjunctionWeight : (X Y : WalkingAdjunctionPoint) → walkingAdjunctionHom X Y → ℕ
  | .plus, .plus, f => augmentedOrdinalCard f
  | .plus, .minus, f => f.obj.len
  | .minus, .plus, f => f.obj.len + 1
  | .minus, .minus, f => augmentedOrdinalCard f.unop

/-- 概要：各Homの重みは対象を区別する。
方針：増大単体圏の個数と単体圏の次元の単射性を使う。
規約：同じ始点・終点の対象同士。使われ方：Riehl–Verity Remark 3.3.8 の骨格。 -/
lemma walkingAdjunctionWeight_injective (X Y : WalkingAdjunctionPoint) :
    Function.Injective (walkingAdjunctionWeight X Y)

def walkingAdjunctionWeight : (X Y : WalkingAdjunctionPoint) → walkingAdjunctionHom X Y → ℕ
  | .plus, .plus, f => augmentedOrdinalCard f
  | .plus, .minus, f => f.obj.len
  | .minus, .plus, f => f.obj.len + 1
  | .minus, .minus, f => augmentedOrdinalCard f.unop

/-- 概要：各Homの重みは対象を区別する。
方針：増大単体圏の個数と単体圏の次元の単射性を使う。
規約：同じ始点・終点の対象同士。使われ方：Riehl–Verity Remark 3.3.8 の骨格。 -/
lemma walkingAdjunctionWeight_injective (X Y : WalkingAdjunctionPoint) :
    Function.Injective (walkingAdjunctionWeight X Y)

lemma walkingAdjunctionWeight_injective (X Y : WalkingAdjunctionPoint) :
    Function.Injective (walkingAdjunctionWeight X Y)

lemma augmentedOrdinalCard_tensor (X Y : AugmentedSimplexCategory) :
    augmentedOrdinalCard (X ⊗ Y) = augmentedOrdinalCard X + augmentedOrdinalCard Y

lemma topOrdinalAction_len (a : AugmentedSimplexCategory) (X : TopSimplexCategory) :
    (topOrdinalAction.obj (a, X)).obj.len = augmentedOrdinalCard a + X.obj.len

lemma bottomOrdinalAction_len (X : BottomSimplexCategory) (a : AugmentedSimplexCategory) :
    (bottomOrdinalAction.obj (X, a)).obj.len = X.obj.len + augmentedOrdinalCard a

lemma bottomOppositeOrdinalAction_len (a : AugmentedSimplexCategoryᵒᵖ)
    (X : BottomSimplexCategory) :
    (bottomOppositeOrdinalAction.obj (a, X)).obj.len =
      augmentedOrdinalCard a.unop + X.obj.len

lemma topOppositeOrdinalAction_len (X : TopSimplexCategory)
    (a : AugmentedSimplexCategoryᵒᵖ) :
    (topOppositeOrdinalAction.obj (X, a)).obj.len =
      X.obj.len + augmentedOrdinalCard a.unop

lemma walkingAdjunctionHorizontal_weight (X Y Z : WalkingAdjunctionPoint)
    (f : walkingAdjunctionHom X Y) (g : walkingAdjunctionHom Y Z) :
    walkingAdjunctionWeight X Z ((walkingAdjunctionHorizontal X Y Z).obj (f, g)) =
      walkingAdjunctionWeight X Y f + walkingAdjunctionWeight Y Z g

lemma walkingAdjunctionIdentity_weight (X : WalkingAdjunctionPoint) :
    walkingAdjunctionWeight X X (walkingAdjunctionIdentity X) = 0

lemma walkingAdjunctionHorizontal_obj_assoc (W X Y Z : WalkingAdjunctionPoint)
    (f : walkingAdjunctionHom W X) (g : walkingAdjunctionHom X Y)
    (h : walkingAdjunctionHom Y Z) :
    (walkingAdjunctionHorizontal W Y Z).obj
        ((walkingAdjunctionHorizontal W X Y).obj (f, g), h) =
      (walkingAdjunctionHorizontal W X Z).obj
        (f, (walkingAdjunctionHorizontal X Y Z).obj (g, h))

lemma walkingAdjunctionHorizontal_obj_id_left (X Y : WalkingAdjunctionPoint)
    (f : walkingAdjunctionHom X Y) :
    (walkingAdjunctionHorizontal X X Y).obj (walkingAdjunctionIdentity X, f) = f

lemma walkingAdjunctionHorizontal_obj_id_right (X Y : WalkingAdjunctionPoint)
    (f : walkingAdjunctionHom X Y) :
    (walkingAdjunctionHorizontal X Y Y).obj (f, walkingAdjunctionIdentity Y) = f
```

### 81.3 対象ビルドと小さい監査

全てwith_build_lock.sh --class impl --wait 3600を使った短いimpl枠。
最初のOrdinalIntervalLawsの対象ビルドではレコードの構文と反対射の簡約で失敗し、
修正後、セッション60228の最大280秒枠で最終 **G12_LAWS_BUILD_EXIT=0**、警告なし。
同じ枠の16根の監査も終了0、入力名・出力名一致、標準公理のみ。exitで終了0まで確認した。

続くセッション93781も最大280秒枠で、対象は
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionComposition:olean。
順序和の実定義への帰着と空の場合の加法の簡約を明示して修正し、
最終 **G12_COMPOSITION_BUILD_EXIT=0**、警告なし（1253 jobs）。
二つの新設ファイルの33根にWalkingAdjunctionPointの構成子2件を加えた35件の
小さい監査は **G12_COMPOSITION_AUDIT_EXIT=0**。
入力35名と出力35名は一致し、公理依存は標準のpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理はない。exitで外側の終了0も確認した。
監査入力・根・全出力と対象ビルドログは
[g12-composition-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-composition-audit-2026-11-15/)に保存した。
現在、自分の生きたビルド・監査・整理券はない。

既存の16ファイル、M15のLean、drafts、main、⑤aのファイル、Interfaceには書き込んでいない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み2,405行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。


## §82 G01：全水平単位則と、順序和・Galois双対による六つの全結合則（11-15）

### 82.1 今回の検収

前のgoal turnは§80〜§81のLeanと報告を検証・コミットした進捗あり。
今回は対象の等式から射の全法則へ進めた。追加は3ファイル444行・明示宣言27。
累計 **21ファイル2,849行・明示宣言215**。G01は未完、一覧の済みは0。

| ファイル（InfinityCategories/HA/Monads/） | 行数 | 検収 |
|---|---:|---|
| WalkingAdjunctionUnits.lean | 137 | 四Homの全8通りの左右単位則。任意の添字圏Iの全関手の等式 |
| OrdinalActionComparison.lean | 168 | 忠実かつ対象で単射な端点の包含、作用と順序和の全比較、左右作用の全結合則 |
| OppositeOrdinalActionLaws.lean | 139 | Galois双対の厳密な往復と作用比較、反対の順序和と反対側の二作用の全結合則 |
| **追加** | **444** | G01の同じ構成・自然性・合成則の分割。新しい一覧IDは加えない |

単位則は空の順序集合の作用の全射の一致を証明した。
反対の自己Homでは元の順序和の単位則の反対を使い、混合Homでは実際の左・右Galois随伴の
往復を使う。これはh Funでの単位の一致だけでなく、全I上の実関手の等式である。

endpointAugmentedForgetは広部分圏の包含と非空部分の包含の合成であり、
忠実性を実際に構成し、対象でも単射であることを証明した。
この包含へ忘却した最大元保存の左作用・最小元保存の右作用は、元の増大単体圏の順序和と
全関手で一致する。空から非空への射も場合分けし、包含の自然性と順序和の関手性で照合した。
この全比較から、元の順序和の全結合則を作用へ戻せる。

反対側はtopToBottomOpEquivalenceの両方の厳密な往復を証明した。
同じ双対へ送った作用の実関手は元の作用の反対に等しく、
その等式から二つの反対側の作用と反対の順序和の全結合則を得た。
双対や結合則を引数の仮定に置いていない。

### 82.2 残る境界

W,X,Y,Zの16通りのうち、全関手の結合則が揃ったのは次の6通り。
`+`はplus、`-`はminus。

| 四対象 | 法則 |
|---|---|
| ++++ | 既存ordinalSumFunctor_assoc |
| +++- | topOrdinalActionFunctor_assoc |
| -+++ | bottomOrdinalActionFunctor_assoc |
| ---- | oppositeOrdinalSumFunctor_assoc |
| ---+ | bottomOppositeOrdinalActionFunctor_assoc |
| +--- | topOppositeOrdinalActionFunctor_assoc |

残る10通りは、二方向の作用の可換性2通りと、混合Hom同士の合成を含む8通り。
これらが揃うまでwalking adjunctionのEnrichedCategoryのinstanceは宣言しない。
また、与えられたQCatAdjunctionからの全拡張、元のF≫U・単位・余単位との比較は未完。
G01の完成、G09の途中の取り込みの点、G12のpresentabilityの完成とは数えない。
原典はHA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8、
Kerodon Remark 6.2.1.4（Tag 02EN）。完成の引用属性はまだ登録していない。
200行を超える宣言・証明はない。

### 82.3 同じ構成の法則・比較の型

namespace SerrePositivity.InfinityCategories.HA.Monads内。
I : Type u、[Category.{v} I]を共通の変数とする。

```lean
lemma topOrdinalAction_leftUnit (F : I ⥤ TopSimplexCategory) :
    (((Functor.const I).obj WithInitial.star).prod' F ⋙ topOrdinalAction) = F

lemma bottomOrdinalAction_rightUnit (F : I ⥤ BottomSimplexCategory) :
    (F.prod' ((Functor.const I).obj WithInitial.star) ⋙ bottomOrdinalAction) = F

lemma bottomOppositeOrdinalAction_leftUnit (F : I ⥤ BottomSimplexCategory) :
    (((Functor.const I).obj (op (WithInitial.star : AugmentedSimplexCategory))).prod' F ⋙
      bottomOppositeOrdinalAction) = F

lemma topOppositeOrdinalAction_rightUnit (F : I ⥤ TopSimplexCategory) :
    (F.prod' ((Functor.const I).obj (op (WithInitial.star : AugmentedSimplexCategory))) ⋙
      topOppositeOrdinalAction) = F

lemma oppositeOrdinalSum_leftUnit (F : I ⥤ AugmentedSimplexCategoryᵒᵖ) :
    (((Functor.const I).obj (op (WithInitial.star : AugmentedSimplexCategory))).prod' F ⋙
      (prodOpEquiv (C

lemma oppositeOrdinalSum_rightUnit (F : I ⥤ AugmentedSimplexCategoryᵒᵖ) :
    (F.prod' ((Functor.const I).obj (op (WithInitial.star : AugmentedSimplexCategory))) ⋙
      (prodOpEquiv (C

lemma walkingAdjunctionHorizontal_leftUnit (X Y : WalkingAdjunctionPoint)
    (F : I ⥤ walkingAdjunctionHom X Y) :
    (((Functor.const I).obj (walkingAdjunctionIdentity X)).prod' F ⋙
      walkingAdjunctionHorizontal X X Y) = F

lemma walkingAdjunctionHorizontal_rightUnit (X Y : WalkingAdjunctionPoint)
    (F : I ⥤ walkingAdjunctionHom X Y) :
    (F.prod' ((Functor.const I).obj (walkingAdjunctionIdentity Y)) ⋙
      walkingAdjunctionHorizontal X Y Y) = F

def endpointAugmentedForget (P : MorphismProperty SimplexCategory) [P.IsMultiplicative] :
    WideSubcategory P ⥤ AugmentedSimplexCategory

instance endpointAugmentedForget_faithful (P : MorphismProperty SimplexCategory)
    [P.IsMultiplicative] : (endpointAugmentedForget P).Faithful

lemma endpointAugmentedForget_obj_injective (P : MorphismProperty SimplexCategory)
    [P.IsMultiplicative] : Function.Injective (endpointAugmentedForget P).obj

lemma endpointAugmentedForget_comp_injective (P : MorphismProperty SimplexCategory)
    [P.IsMultiplicative] {F G : I ⥤ WideSubcategory P}
    (h : F ⋙ endpointAugmentedForget P = G ⋙ endpointAugmentedForget P) : F = G

lemma topOrdinalAction_forget :
    topOrdinalAction ⋙ endpointAugmentedForget simplexPreservesTop =
      (𝟭 AugmentedSimplexCategory).prod (endpointAugmentedForget simplexPreservesTop) ⋙
        tensor AugmentedSimplexCategory

lemma bottomOrdinalAction_forget :
    bottomOrdinalAction ⋙ endpointAugmentedForget simplexPreservesBottom =
      (endpointAugmentedForget simplexPreservesBottom).prod (𝟭 AugmentedSimplexCategory) ⋙
        tensor AugmentedSimplexCategory

lemma topOrdinalActionFunctor_forget (F : I ⥤ AugmentedSimplexCategory)
    (G : I ⥤ TopSimplexCategory) :
    (F.prod' G ⋙ topOrdinalAction) ⋙ endpointAugmentedForget simplexPreservesTop =
      F.prod' (G ⋙ endpointAugmentedForget simplexPreservesTop) ⋙
        tensor AugmentedSimplexCategory

lemma bottomOrdinalActionFunctor_forget (F : I ⥤ BottomSimplexCategory)
    (G : I ⥤ AugmentedSimplexCategory) :
    (F.prod' G ⋙ bottomOrdinalAction) ⋙ endpointAugmentedForget simplexPreservesBottom =
      (F ⋙ endpointAugmentedForget simplexPreservesBottom).prod' G ⋙
        tensor AugmentedSimplexCategory

lemma topOrdinalActionFunctor_assoc (F G : I ⥤ AugmentedSimplexCategory)
    (H : I ⥤ TopSimplexCategory) :
    ((F.prod' G ⋙ tensor AugmentedSimplexCategory).prod' H ⋙ topOrdinalAction) =
      (F.prod' (G.prod' H ⋙ topOrdinalAction) ⋙ topOrdinalAction)

lemma bottomOrdinalActionFunctor_assoc (F : I ⥤ BottomSimplexCategory)
    (G H : I ⥤ AugmentedSimplexCategory) :
    ((F.prod' G ⋙ bottomOrdinalAction).prod' H ⋙ bottomOrdinalAction) =
      (F.prod' (G.prod' H ⋙ tensor AugmentedSimplexCategory) ⋙ bottomOrdinalAction)

lemma topToBottomOp_source_roundtrip :
    topToBottomOpEquivalence.functor ⋙ topToBottomOpEquivalence.inverse =
      𝟭 TopSimplexCategory

lemma topToBottomOp_target_roundtrip :
    topToBottomOpEquivalence.inverse ⋙ topToBottomOpEquivalence.functor =
      𝟭 BottomSimplexCategoryᵒᵖ

lemma bottomFunctor_eq_of_dual {F G : I ⥤ BottomSimplexCategory}
    (h : F ⋙ endpointSimplexEquivalence.functor = G ⋙ endpointSimplexEquivalence.functor) :
    F = G

lemma topFunctor_eq_of_dual {F G : I ⥤ TopSimplexCategory}
    (h : F ⋙ topToBottomOpEquivalence.functor = G ⋙ topToBottomOpEquivalence.functor) :
    F = G

lemma bottomOppositeOrdinalActionFunctor_dual (F : I ⥤ AugmentedSimplexCategoryᵒᵖ)
    (G : I ⥤ BottomSimplexCategory) :
    (F.prod' G ⋙ bottomOppositeOrdinalAction) ⋙ endpointSimplexEquivalence.functor =
      (F.leftOp.prod' (G ⋙ endpointSimplexEquivalence.functor).leftOp ⋙
        topOrdinalAction).rightOp

lemma topOppositeOrdinalActionFunctor_dual (F : I ⥤ TopSimplexCategory)
    (G : I ⥤ AugmentedSimplexCategoryᵒᵖ) :
    (F.prod' G ⋙ topOppositeOrdinalAction) ⋙ topToBottomOpEquivalence.functor =
      ((F ⋙ topToBottomOpEquivalence.functor).leftOp.prod' G.leftOp ⋙
        bottomOrdinalAction).rightOp

lemma oppositeOrdinalSumFunctor_assoc (F G H : I ⥤ AugmentedSimplexCategoryᵒᵖ) :
    ((F.prod' G ⋙ walkingAdjunctionHorizontal .minus .minus .minus).prod' H ⋙
      walkingAdjunctionHorizontal .minus .minus .minus) =
      (F.prod' (G.prod' H ⋙ walkingAdjunctionHorizontal .minus .minus .minus) ⋙
        walkingAdjunctionHorizontal .minus .minus .minus)

lemma bottomOppositeOrdinalActionFunctor_assoc
    (F G : I ⥤ AugmentedSimplexCategoryᵒᵖ) (H : I ⥤ BottomSimplexCategory) :
    ((F.prod' G ⋙ walkingAdjunctionHorizontal .minus .minus .minus).prod' H ⋙
      bottomOppositeOrdinalAction) =
      (F.prod' (G.prod' H ⋙ bottomOppositeOrdinalAction) ⋙ bottomOppositeOrdinalAction)

lemma topOppositeOrdinalActionFunctor_assoc (F : I ⥤ TopSimplexCategory)
    (G H : I ⥤ AugmentedSimplexCategoryᵒᵖ) :
    ((F.prod' G ⋙ topOppositeOrdinalAction).prod' H ⋙ topOppositeOrdinalAction) =
      (F.prod' (G.prod' H ⋙ walkingAdjunctionHorizontal .minus .minus .minus) ⋙
        topOppositeOrdinalAction)
```

### 82.4 対象ビルドと小さい監査

全てwith_build_lock.sh --class impl --wait 3600、最大280秒の短いimpl枠で実行した。

- セッション46826：WalkingAdjunctionUnits:olean。Functor.ext・Functor.map_idの名前衝突を
  完全名で解き、空での値を構成済みの恒等関手に正規化した。最終
  **G12_UNITS_BUILD_EXIT=0**、警告なし（1254 jobs）。新設8根の監査も終了0。
- セッション46645：OrdinalActionComparison:olean。関手等式の回収で合成関手の
  対象・射の簡約を明示して修正した。最終 **G12_ACTION_COMPARE_BUILD_EXIT=0**、
  警告なし（1255 jobs）。上の2ファイル18根の監査も終了0。
- セッション28649：OppositeOrdinalActionLaws:olean。初回で
  **G12_OPPOSITE_BUILD_EXIT=0**、警告なし（1256 jobs）。3ファイル27根の監査も
  **G12_OPPOSITE_AUDIT_EXIT=0**。

各枠はexitで外側の終了0まで確認して返却した。
最終の入力27名と出力27名は一致し、公理依存は標準のpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理はない。監査入力・根・全出力と三つの対象ビルドログは
[g12-unit-assoc-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-unit-assoc-audit-2026-11-15/)に保存した。
現在、自分の生きたビルド・監査・整理券はない。

既存の18ファイル、M15のLean、drafts、main、⑤aのファイル、Interfaceには書き込んでいない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み2,849行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。


## §83 G01：二つの混合Homの間の自己Homを移す全結合則（11-15）

### 83.1 検証済みの追加

前のgoal turnは§82のLean・報告を検証・コミットした進捗あり。
今回はIntervalMixedBalancing.leanの **1ファイル112行・明示宣言7** を検証した。
累計 **22ファイル2,961行・明示宣言222**。G01は未完で一覧の済みは0。

mixedBottomTopOrdinalを実区間表示へ送ると、構成元のbottomTopIntervalSumに
全関手で戻ることを、実同値の厳密な往復から示した。
さらに両端点を忘却すると元の増大単体圏の順序和と全関手で一致する。
この全比較に任意のI上の関手を前合成し、区間表示の忠実性と
端点の忘却の忠実性・対象の単射性で等式を回収した。

これにより **-++-**（Bottom × Augmented × Top）の全結合則を証明した。
逆順の混合合成の反対がGalois双対に送った元の混合合成であることは
実双関手の定義から一致する。既存の二つの反対側の作用の双対比較を使い、
**+--+**（Top × Augmentedᵒᵖ × Bottom）の全結合則も証明した。
全てIの任意の射に関する関手の等式であり、対象の個数の照合だけではない。

§82の6通りと合わせて、全結合則は **16通り中8通り**。
残る8通りは++-+、++--、+-++、+-+-、-+-+、-+--、--++、--+-。
全8通りの単位則は§82で検証済み。
全豊穣walking adjunction、与えられたQCatAdjunctionからの全拡張、
元のF≫U・単位・余単位との比較は未完。G01完成とは数えない。

原典はHA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8、
Kerodon Remark 6.2.1.4（Tag 02EN）。新しい一覧IDは加えず、G01の同じ構成と
自然性・合成則の分割として数える。200行を超える宣言・証明はない。

### 83.2 同じ構成の比較・法則の型

namespace SerrePositivity.InfinityCategories.HA.Monads内。
I : Type u、[Category.{v} I]を共通の変数とする。

```lean
lemma mixedBottomTopOrdinal_representation :
    mixedBottomTopOrdinal ⋙ ordinalIntervalRepresentation = bottomTopIntervalSum

lemma bottomTopIntervalSum_forget :
    bottomTopIntervalSum ⋙ endpointAugmentedForget simplexPreservesEndpoints =
      (endpointAugmentedForget simplexPreservesBottom).prod
        (endpointAugmentedForget simplexPreservesTop) ⋙ tensor AugmentedSimplexCategory

lemma ordinalIntervalRepresentation_comp_injective
    {F G : I ⥤ AugmentedSimplexCategoryᵒᵖ}
    (h : F ⋙ ordinalIntervalRepresentation = G ⋙ ordinalIntervalRepresentation) : F = G

lemma mixedBottomTopFunctor_forget (F : I ⥤ BottomSimplexCategory)
    (G : I ⥤ TopSimplexCategory) :
    ((F.prod' G ⋙ mixedBottomTopOrdinal) ⋙ ordinalIntervalRepresentation) ⋙
        endpointAugmentedForget simplexPreservesEndpoints =
      (F ⋙ endpointAugmentedForget simplexPreservesBottom).prod'
        (G ⋙ endpointAugmentedForget simplexPreservesTop) ⋙ tensor AugmentedSimplexCategory

lemma mixedBottomTopFunctor_balance (F : I ⥤ BottomSimplexCategory)
    (G : I ⥤ AugmentedSimplexCategory) (H : I ⥤ TopSimplexCategory) :
    ((F.prod' G ⋙ bottomOrdinalAction).prod' H ⋙ mixedBottomTopOrdinal) =
      (F.prod' (G.prod' H ⋙ topOrdinalAction) ⋙ mixedBottomTopOrdinal)

lemma mixedTopBottomFunctor_op (F : I ⥤ TopSimplexCategory)
    (G : I ⥤ BottomSimplexCategory) :
    (F.prod' G ⋙ mixedTopBottomOrdinal).op =
      (F ⋙ topToBottomOpEquivalence.functor).leftOp.prod'
        (G ⋙ endpointSimplexEquivalence.functor).leftOp ⋙ mixedBottomTopOrdinal

lemma mixedTopBottomFunctor_balance (F : I ⥤ TopSimplexCategory)
    (G : I ⥤ AugmentedSimplexCategoryᵒᵖ) (H : I ⥤ BottomSimplexCategory) :
    ((F.prod' G ⋙ topOppositeOrdinalAction).prod' H ⋙ mixedTopBottomOrdinal) =
      (F.prod' (G.prod' H ⋙ bottomOppositeOrdinalAction) ⋙ mixedTopBottomOrdinal)
```

### 83.3 検証と次の作業木

対象はlake build SerrePositivity.InfinityCategories.HA.Monads.IntervalMixedBalancing:olean。
with_build_lock.sh --class impl --wait 3600、最大280秒の短いimpl枠（セッション88597）で実行。
前合成した比較の両辺を関手の結合則で正規化して修正し、
最終 **G12_BALANCE_BUILD_EXIT=0**、警告なし（1257 jobs）。
新設7根の小さい監査は **G12_BALANCE_AUDIT_EXIT=0**。
入力7名と出力7名は一致し、公理依存は標準のpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理はない。exitで外側の終了0まで確認して返却した。
入力・根・全出力・対象ビルドログは
[g12-balance-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-balance-audit-2026-11-15/)へ保存した。

続く作業木のOrdinalConcatenation.lean、OrdinalConcatenationLaws.lean、OrdinalGlueGalois.leanは
残る8通りの射の比較に使う同じ構成の値の表示・貼り合わせ・Galois随伴の法則。
この§83の検証済みの行数・宣言数・コミットには含めない。
前のセッション42796は最大280秒で終了124を確認し、その後にセッション37662の
別の短いimpl枠へ並び直して検証を継続している。古い枠を生きたまま再起動していない。
新しい射の表示が既存の全合成と一致することは、Galois随伴の一意性でこれから検収する。
値の表示だけから残る8通りの全関手の結合則が済んだとは数えない。

既存の21ファイル、M15のLean、drafts、main、⑤aのファイル、Interfaceには書き込んでいない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み2,961行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。


## §84 G01：混合合成の順序和・端点共有の射の表示とGalois比較（11-15）

### 84.1 実装と残る境界

追加は3ファイル391行・明示宣言19。累計 **25ファイル3,352行・明示宣言241**。
今回の射の表示だけから、§83で残っている8通りの全関手の結合則が完成したとは数えない。
G01は未完、一覧の済みは0のまま。

| ファイル（InfinityCategories/HA/Monads/） | 行数 | 検収 |
|---|---:|---|
| OrdinalConcatenation.lean | 140 | 空も含む順序和の射と、非空区間の端点共有の単調射、各区間での値、型の輸送を含む外延性 |
| OrdinalConcatenationLaws.lean | 122 | 非空の左因子の添字の輸送、順序和と端点共有の二つの結合則（個数の加法の結合則をHEqで保持） |
| OrdinalGlueGalois.lean | 129 | 左・右に区間表示を貼る射と順序和の実Galois条件、最大元付加の随伴保存、右随伴の区間表示の照合 |
| **追加** | **391** | G01の同じ合成の値の表示・合成則・貼り合わせ・係数輸送の分割 |

ordinalAppendは元の順序和のFin.addCasesによる射の表示。
ordinalGlueは共有点まで左の射、それより後は右の射の値を左の次元だけずらす単調射。
写像自体は両射に端点条件を課さず作れる。実圏の双関手の合成と比較するときの端点条件は
別に照合する。ordinalAppendNonemptyは同じ順序和の個数の表示をFin.castOrderIsoで移すだけである。

順序和を前に加えて端点共有する操作と、先に端点共有して後ろに順序和を加える操作の
二つの結合則を、三つの区間で値を照合して証明した。対象の個数の等式を隠さずHEqで保持する。

混合水平合成の既存の定義はGalois随伴と区間同値の逆を使うため、新しい値の表示が
同じ射であることをまだ検収する必要がある。今回、左に区間表示を貼る単調射の右随伴が
元の射と右随伴の順序和であること、右に区間表示を貼る単調射の左随伴が
左随伴と元の射の順序和であることを実際のGalois条件として証明した。
後者の右の区間では、既存の区間表示の随伴条件の否定を使って厳密不等式を照合した。
最大元付加も有限Galois随伴を保ち、最小元保存の右随伴の区間表示は元の射の最大元付加に等しい。

これらは既存の水平合成と射の値の表示を比較するための法則。
未検証のOrdinalIntervalConcatenation.leanには、最大元付加と順序和・端点共有の照合、
区間表示の順序和への適合、既存tensorHomOfとの照合を置いて作業木で検証を続ける。
このファイルは今回の検証済み行数・宣言数・コミットに含めない。
既存の合成との比較が済むまで、残る8通りの全関手の結合則には進みを加算しない。
全豊穣walking adjunction、随伴からの全拡張、元のF≫U・単位・余単位との比較も未完。

原典はHA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8、
Kerodon Remark 6.2.1.4（Tag 02EN）。新しい一覧IDは加えない。
200行を超える宣言・証明はない。

### 84.2 同じ構成の射の表示・法則・比較の型

namespace SerrePositivity.InfinityCategories.HA.Monads内。
m,n,p,q,r,s : ℕを共通の暗黙の変数とする。

```lean
def ordinalAppend (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    Fin (m + p) →o Fin (n + q)

@[simp] lemma ordinalAppend_castAdd (f : Fin m →o Fin n) (g : Fin p →o Fin q) (i : Fin m) :
    ordinalAppend f g (i.castAdd p) = (f i).castAdd q

@[simp] lemma ordinalAppend_natAdd (f : Fin m →o Fin n) (g : Fin p →o Fin q) (i : Fin p) :
    ordinalAppend f g (i.natAdd m) = (g i).natAdd n

lemma ordinalAppend_val_left (f : Fin m →o Fin n) (g : Fin p →o Fin q)
    (i : Fin (m + p)) (hi : i.val < m) :
    (ordinalAppend f g i).val = (f ⟨i.val, hi⟩).val

lemma ordinalAppend_val_right (f : Fin m →o Fin n) (g : Fin p →o Fin q)
    (i : Fin (m + p)) (hi : m ≤ i.val) :
    (ordinalAppend f g i).val = n + (g ⟨i.val - m, by have

def ordinalGlue (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) : Fin (m + p + 1) →o Fin (n + q + 1)

@[simp] lemma ordinalGlue_val_left (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (i : Fin (m + 1)) :
    (ordinalGlue f g ⟨i.val, by have

lemma ordinalGlue_val_right (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) (hg : g 0 = 0)
    (i : Fin (p + 1)) :
    (ordinalGlue f g ⟨m + i.val, by have

lemma ordinalHom_hext {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (f : Fin a →o Fin b) (g : Fin c →o Fin d)
    (h : ∀ (i : Fin a) (j : Fin c), i.val = j.val → (f i).val = (g j).val) : HEq f g

def ordinalAppendNonempty (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin p →o Fin q) : Fin (m + p + 1) →o Fin (n + q + 1)

lemma ordinalAppendNonempty_val (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin p →o Fin q) (i : Fin (m + p + 1)) :
    (ordinalAppendNonempty f g i).val =
      (ordinalAppend f g ⟨i.val, by have

lemma ordinalGlue_val_of_le (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (i : Fin (m + p + 1)) (hi : i.val ≤ m) :
    (ordinalGlue f g i).val = (f ⟨i.val, by omega⟩).val

lemma ordinalGlue_val_of_lt (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (i : Fin (m + p + 1)) (hi : m < i.val) :
    (ordinalGlue f g i).val = n + (g ⟨i.val - m, by have

lemma ordinalAppend_glue_assoc (f : Fin m →o Fin n)
    (g : Fin (p + 1) →o Fin (q + 1)) (h : Fin (r + 1) →o Fin (s + 1)) :
    HEq (ordinalGlue (m

lemma ordinalGlue_append_assoc (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (h : Fin r →o Fin s) :
    HEq (ordinalAppendNonempty (ordinalGlue f g) h)
      (ordinalGlue f (ordinalAppendNonempty g h))

lemma ordinalGlue_interval_gc (f : Fin n →o Fin m)
    (g : Fin (p + 1) →o Fin (q + 1)) (hg : g 0 = 0) :
    GaloisConnection (ordinalGlue (ordinalIntervalMap f) g)
      (ordinalAppend (m

lemma ordinalGlue_interval_gc_right (f : Fin (m + 1) →o Fin (n + 1))
    (hf : f (Fin.last m) = Fin.last n) (g : Fin q →o Fin p) :
    GaloisConnection (ordinalAppendNonempty (ordinalLeftAdjoint f hf) g)
      (ordinalGlue f (ordinalIntervalMap g))

lemma ordinalAdjoinTop_gc {a b : ℕ} {f : Fin a →o Fin b} {g : Fin b →o Fin a}
    (h : GaloisConnection f g) : GaloisConnection (ordinalAdjoinTop f) (ordinalAdjoinTop g)

lemma ordinalIntervalMap_rightAdjoint (g : Fin (p + 1) →o Fin (q + 1)) (hg : g 0 = 0) :
    ordinalIntervalMap (ordinalRightAdjoint g hg) = ordinalAdjoinTop g
```

### 84.3 検証

with_build_lock.sh --class impl --wait 3600を使い、各impl枠は最大280秒または240秒。
セッション42796と37662は、依存するFin点の書換えと型の輸送を修正しながら検証した。
順序和と端点共有の本体、二つの結合則、二つの実Galois条件と最大元付加の法則は対象ビルドを通った。
未検証のOrdinalIntervalConcatenationでは既存の順序和の添字の輸送の照合が残った。
二つの対話式枠は終了124をそれぞれ確認し、終了済みの枠を生きたまま再起動していない。

その後、セッション65725の最大240秒の短い一回の処理で
lake build SerrePositivity.InfinityCategories.HA.Monads.OrdinalGlueGalois:oleanと
新設3ファイル19根の小さい監査を続けて実行した。
最終 **G12_CONCAT_VERIFIED_BUILD_EXIT=0**、警告なし。
監査は **G12_CONCAT_AUDIT_EXIT=0**。
入力19名と出力19名が一致し、公理依存は標準のpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理はない。外側の終了0まで確認して枠を返却した。
入力・根・全出力と最終対象ビルドログは
[g12-concat-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-concat-audit-2026-11-15/)に保存した。
現在、自分の生きたビルド・監査・整理券はない。

既存の22ファイル、M15のLean、drafts、main、⑤aのファイル、Interfaceには書き込んでいない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み3,352行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。


## §85 G01：既存の順序和・区間表示と混合合成の実随伴の照合（11-15）

### 85.1 検証済みの区切り

前のgoal turnは§83〜§84のLeanと報告を検証・コミットした進捗あり。
今回は§84の作業木の区間表示の比較を仕上げ、混合合成に使う実随伴との照合を進めた。
追加は **2ファイル223行・明示宣言9**。累計 **27ファイル3,575行・明示宣言250**。
G01は未完で一覧の済みは0のまま。

| ファイル（InfinityCategories/HA/Monads/） | 行数 | 今回の検収 |
|---|---:|---|
| OrdinalIntervalConcatenation.lean | 131 | 最大元付加と順序和・端点共有の照合、区間表示の順序和への適合、既存tensorHomOfとの全射の照合 |
| OrdinalMixedAdjoints.lean | 92 | 順序和の端点保存の実証明、左・右実随伴と端点共有の一致、混合区間の回収の照合 |
| **追加** | **223** | G01の同じ合成の法則・自然性・係数輸送・貼り合わせの分割。新しい一覧IDなし |

空も許す順序和の最後に最大元を付加する操作は、右因子へ最大元を付加する操作と一致する。
端点共有の写像でも同じ照合を最後の点と元の区間の全点で証明した。
この照合と構成済みのGalois条件から、順序和の区間表示が二つの区間表示の端点共有の射に
等しいことを、同じ右随伴を持つ左随伴の一意性で示した。
既存のAugmentedSimplexCategory.tensorHomOfとの比較も、元のFin.addCasesと添字の輸送まで展開した。

続いて、左の非空因子が最小元を保つときの順序和の最小元保存、右の非空因子が最大元を保つ
ときの最大元保存を実際に証明した。それらを入力に使い、既存の実右随伴・実左随伴が
端点共有の写像と同じであることを一意性から証明した。随伴の存在を未証明のinstanceにしていない。
混合合成の逆区間表示に必要なordinalRecoverMapの照合は、元の区間射が持つ両端点の条件を
引数とし、最大元付加の単射性と同じ右随伴の一意性で示した。
これらは既存の混合合成の実際の射の比較であり、対象の個数を合わせただけではない。

### 85.2 残る境界と型

これから、§84の値の結合則を既存の八つの水平合成の全関手へ戻す。
AugmentedOrdinalTensorMaps.leanを作業木に置き、混合Homの非空の因子を持つ順序和について、
他方が空から非空へ動く射も含めた比較を検証中。このファイルは今回の検証済み行数・宣言数・
コミットには含めない。
§83の全結合則は **16通り中8通り**のまま。残る8通り、全豊穣walking adjunction、
元の随伴からの全拡張、F≫U・単位・余単位との比較が未完であり、G01完成とは数えない。

原典はHA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8、
Kerodon Remark 6.2.1.4（Tag 02EN）。200行を超える宣言・証明はない。
以下はnamespace SerrePositivity.InfinityCategories.HA.Monads内、m,n,p,q : ℕを共通の暗黙変数とする。

```lean
lemma ordinalAppend_adjoinTop (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    ordinalAdjoinTop (ordinalAppend f g) =
      ordinalAppend (m

lemma ordinalGlue_adjoinTop (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) :
    ordinalGlue (p

lemma ordinalIntervalMap_append (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    ordinalIntervalMap (ordinalAppend f g) =
      ordinalGlue (ordinalIntervalMap f) (ordinalIntervalMap g)

lemma simplexTensorHomOf_append {X Y Z W : SimplexCategory} (f : X ⟶ Y) (g : Z ⟶ W) :
    (AugmentedSimplexCategory.tensorHomOf f g).toOrderHom =
      ordinalAppendNonempty f.toOrderHom g.toOrderHom

lemma ordinalAppendNonempty_zero (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin p →o Fin q) (hf : f 0 = 0) : ordinalAppendNonempty f g 0 = 0

lemma ordinalAppend_last (f : Fin m →o Fin n)
    (g : Fin (p + 1) →o Fin (q + 1)) (hg : g (Fin.last p) = Fin.last q) :
    ordinalAppend (m

lemma ordinalRightAdjoint_append_glue (f : Fin (m + 1) →o Fin (n + 1))
    (hf : f (Fin.last m) = Fin.last n) (g : Fin q →o Fin p) :
    ordinalRightAdjoint (ordinalAppendNonempty (ordinalLeftAdjoint f hf) g)
        (ordinalAppendNonempty_zero _ _ (ordinalLeftAdjoint_zero f hf)) =
      ordinalGlue f (ordinalIntervalMap g)

lemma ordinalLeftAdjoint_append_glue (f : Fin n →o Fin m)
    (g : Fin (p + 1) →o Fin (q + 1)) (hg : g 0 = 0) :
    ordinalLeftAdjoint
        (ordinalAppend (m

lemma ordinalRecoverMap_append_glue (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) (hg : g 0 = 0)
    (h₀ : ordinalAppendNonempty (ordinalLeftAdjoint f hf) (ordinalRightAdjoint g hg) 0 = 0)
    (h₁ : ordinalAppendNonempty (ordinalLeftAdjoint f hf) (ordinalRightAdjoint g hg)
      (Fin.last (n + q + 1)) = Fin.last (m + p + 1)) :
    ordinalRecoverMap
        (ordinalAppendNonempty (ordinalLeftAdjoint f hf) (ordinalRightAdjoint g hg)) h₀ h₁ =
      ordinalGlue f g
```

### 85.3 検証

各枠はwith_build_lock.sh --class impl --wait 3600、最大280秒の短いimpl枠。
セッション3934では最後の点の依存する添字の書換えと既存順序和の輸送を修正し、終了124まで確認。
セッション60532ではOrdinalMixedAdjoints:oleanを対象に依存のOrdinalIntervalConcatenationも検証した。
最後の点の輸送を明示的な等式にconvertして修正後、両ファイルを含む対象ビルドは
**G12_CONCAT_BUILD_EXIT=0**。不要な手続きと長い行を整理し、最終は警告なし（1165 jobs）。

その後、新設2ファイル9根の小さい監査は **G12_CONCAT_AUDIT_EXIT=0**。
入力9名と出力9名は一致し、公理依存は標準のpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理はない。成功した対象ビルドと9根の監査のログは別名に保存してから、
同じ枠の残りで作業木のAugmentedOrdinalTensorMapsの対象ビルドを始めた。
こちらでは空の対象の個数の簡約を明示して修正し、修正後の再検証を残して枠の終了124を確認した。
枠の終了124を、先に確認・保存した上の2ファイルの検証の成功と取り違えていない。

入力・根・全出力と成功した対象ビルドログは
[g12-mixed-comparison-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-mixed-comparison-audit-2026-11-15/)に保存した。
現在、自分の生きたビルド・監査・整理券はない。
既存の25ファイル、M15のLean、drafts、main、⑤aのファイル、Interfaceには書き込んでいない。
mainのcitation-attributes.md §15も読み取り、B3′の影響候補が⑤dは0であることを確認した。
この区切りでmainの取り込みや古い索引の流用はしていない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み3,575行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。


## §86 G01：全増大順序和と四つの水平作用の全射の表示（11-15）

### 86.1 検証済みの追加

追加は **3ファイル334行・明示宣言14**。累計 **30ファイル3,909行・明示宣言264**。
この3ファイルまでを検証し、G01の一覧の済みは0のまま。

| ファイル（InfinityCategories/HA/Monads/） | 行数 | 今回の検収 |
|---|---:|---|
| AugmentedOrdinalTensorMaps.lean | 149 | 非空の因子の添字の輸送、左右の空から非空への射の照合、両方空も含む全増大順序和の射の照合 |
| OrdinalActionMapProfiles.lean | 113 | 関手等式からの全射の移送、有限随伴・区間表示・回収の型の輸送、通常側の二作用の全射の表示 |
| OppositeOrdinalActionMapProfiles.lean | 72 | 二つの反対側の作用の全射と、区間表示との端点共有の射の一致 |
| **追加** | **334** | G01の同じ合成・自然性・係数移送・貼り合わせの法則。新しい一覧IDなし |

混合Homで使う一方が非空の順序和は、他方の空と非空を場合分けして照合した。
空から非空への射では元の左・右包含の値を使う。両方の始域が空なら空の点を除去することで、
全増大単体圏の順序和の射がordinalAppendと一致することもHEqでまとめた。
両因子を非空に制限した結果だけを全増大単体圏の主張とは読んでいない。

構成済みの忘却後の全関手等式から、通常側のtopOrdinalAction・bottomOrdinalActionの
全射の表示を取り出した。対象の個数が違う表示を同じ型と仮定せず、
区間表示・実左随伴・実右随伴・区間の回収の係数移送を、個数の等式を引数にして証明した。
この個数の等式は実際の作用の長さの既存の法則から供給する。

反対側では、実定義どおりGalois双対に送った通常側の作用の全射を正規化し、
§85の実随伴の一意性による照合を適用した。その結果、
topOppositeOrdinalActionの全射は元の最大元保存の射と区間表示の端点共有、
bottomOppositeOrdinalActionの全射は区間表示と元の最小元保存の射の端点共有に一致する。
この二つも空の自己Homの因子と空から非空へ動く射を含む。
追加のModelCategoryや随伴の存在のinstanceは仮定していない。

### 86.2 残る境界と型

四つの作用の全射の表示が揃った。これから、実区間同値の逆を使う二つの混合合成の射も
同じ表示へ移し、§84の二つの値の結合則を既存の水平合成の全関手へ戻す。
§83の全結合則は **16通り中8通り**のまま。
残る8通り、全豊穣walking adjunction、与えられた随伴からの全拡張、
元のF≫U・単位・余単位との比較が未完であり、G01完成とは数えない。

原典はHA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8、
Kerodon Remark 6.2.1.4（Tag 02EN）。200行を超える宣言・証明はない。
以下はnamespace SerrePositivity.InfinityCategories.HA.Monads内。

```lean
lemma ordinalAppendNonempty_heq {m n p q : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin p →o Fin q) : HEq (ordinalAppendNonempty f g) (ordinalAppend f g)

lemma simplexTensorHomOf_append_heq {X Y Z W : SimplexCategory} (f : X ⟶ Y) (g : Z ⟶ W) :
    HEq (AugmentedSimplexCategory.tensorHomOf f g).toOrderHom
      (ordinalAppend f.toOrderHom g.toOrderHom)

lemma augmentedOrderHom_tensor_nonempty_right {A B : AugmentedSimplexCategory}
    {C D : SimplexCategory} (f : A ⟶ B) (g : C ⟶ D) :
    HEq (augmentedOrderHom (f ⊗ₘ WithInitial.incl.map g))
      (ordinalAppend (augmentedOrderHom f) g.toOrderHom)

lemma augmentedOrderHom_tensor_nonempty_left {A B : AugmentedSimplexCategory}
    {C D : SimplexCategory} (f : C ⟶ D) (g : A ⟶ B) :
    HEq (augmentedOrderHom (WithInitial.incl.map f ⊗ₘ g))
      (ordinalAppend f.toOrderHom (augmentedOrderHom g))

lemma augmentedOrderHom_tensor {A B C D : AugmentedSimplexCategory}
    (f : A ⟶ B) (g : C ⟶ D) :
    HEq (augmentedOrderHom (f ⊗ₘ g))
      (ordinalAppend (augmentedOrderHom f) (augmentedOrderHom g))

lemma augmentedOrderHom_functor_map_heq {I : Type u} [Category.{v} I]
    {F G : I ⥤ AugmentedSimplexCategory} (h : F = G) {X Y : I} (f : X ⟶ Y) :
    HEq (augmentedOrderHom (F.map f)) (augmentedOrderHom (G.map f))

lemma ordinalIntervalMap_heq {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    {f : Fin a →o Fin b} {g : Fin c →o Fin d} (h : HEq f g) :
    HEq (ordinalIntervalMap f) (ordinalIntervalMap g)

lemma ordinalRightAdjoint_heq {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    {f : Fin (a + 1) →o Fin (b + 1)} {g : Fin (c + 1) →o Fin (d + 1)}
    (hf : f 0 = 0) (hg : g 0 = 0) (h : HEq f g) :
    HEq (ordinalRightAdjoint f hf) (ordinalRightAdjoint g hg)

lemma ordinalLeftAdjoint_heq {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    {f : Fin (a + 1) →o Fin (b + 1)} {g : Fin (c + 1) →o Fin (d + 1)}
    (hf : f (Fin.last a) = Fin.last b) (hg : g (Fin.last c) = Fin.last d)
    (h : HEq f g) : HEq (ordinalLeftAdjoint f hf) (ordinalLeftAdjoint g hg)

lemma ordinalRecoverMap_heq {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    {f : Fin (a + 1) →o Fin (b + 1)} {g : Fin (c + 1) →o Fin (d + 1)}
    (hf₀ : f 0 = 0) (hf₁ : f (Fin.last a) = Fin.last b)
    (hg₀ : g 0 = 0) (hg₁ : g (Fin.last c) = Fin.last d) (h : HEq f g) :
    HEq (ordinalRecoverMap f hf₀ hf₁) (ordinalRecoverMap g hg₀ hg₁)

lemma topOrdinalAction_map_heq {A B : AugmentedSimplexCategory} {X Y : TopSimplexCategory}
    (f : A ⟶ B) (g : X ⟶ Y) :
    HEq (topOrdinalAction.map (X

lemma bottomOrdinalAction_map_heq {A B : AugmentedSimplexCategory}
    {X Y : BottomSimplexCategory} (f : X ⟶ Y) (g : A ⟶ B) :
    HEq (bottomOrdinalAction.map (X

lemma topOppositeOrdinalAction_map_heq {A B : AugmentedSimplexCategoryᵒᵖ}
    {X Y : TopSimplexCategory} (f : X ⟶ Y) (g : A ⟶ B) :
    HEq (topOppositeOrdinalAction.map (X

lemma bottomOppositeOrdinalAction_map_heq {A B : AugmentedSimplexCategoryᵒᵖ}
    {X Y : BottomSimplexCategory} (f : A ⟶ B) (g : X ⟶ Y) :
    HEq (bottomOppositeOrdinalAction.map (X
```

### 86.3 検証

with_build_lock.sh --class impl --wait 3600、セッション65994の最大240秒の短いimpl枠で検証した。
待ち列で対象をこの3ファイルの塊へまとめ、最終の対象は
lake build SerrePositivity.InfinityCategories.HA.Monads.OppositeOrdinalActionMapProfiles:olean。
依存のAugmentedOrdinalTensorMaps・OrdinalActionMapProfilesを含む。
増大順序和の個数の簡約を明示した後、全増大順序和の比較は通った。
左右作用の積の圏の始域・終域を明示し、既存の忘却比較のimportを補って修正した。
最終 **G12_AUG_PROFILE_BUILD_EXIT=0**、警告なし（1263 jobs）。

新設14根の小さい監査は **G12_AUG_PROFILE_AUDIT_EXIT=0**。
入力14名と出力14名は一致し、公理依存は標準のpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理はない。exitで外側の終了0まで確認し、枠を返却した。
監査入力・根・全出力・最終対象ビルドログは
[g12-action-profile-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-action-profile-audit-2026-11-15/)に保存した。
現在、自分の生きたビルド・監査・整理券はない。

既存の27ファイル、M15のLean、drafts、main、⑤aのファイル、Interfaceには書き込んでいない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み3,909行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §87 G01：実区間同値の逆と全水平合成の共通表示（11-15）

### 87.1 検証済みの追加

追加は **2ファイル346行・明示宣言24**。累計 **32ファイル4,255行・明示宣言288**。
IntervalInverseMapProfiles.lean は111行・5宣言、WalkingAdjunctionMapRepresentation.lean は235行・19宣言。
200行を超える個別の宣言・証明はない。
G01の同じ構成の自然性・係数移送・合成則の証明の分割なので、新しい一覧IDは足さない。

実区間同値の逆の射を、構成済みの厳密な往復と区間射の回収から照合した。
その比較を使って、二つの混合合成の全射の有限単調射の表示も確定した。
四つのHomについて、共通の点の個数・全射の表示、minusへの入出の区間の次元を定めた。
共通表示の異種等式から元のHomの射を回収する補題を証明し、
plusを経由する四合成は順序和、minusを経由する四合成は端点共有としてまとめた。
空の自己Homを排除する仮定や、追加のModelCategory・随伴の存在の仮定は置いていない。

### 87.2 型と残る境界

原典の対応はHA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8、
Kerodon Remark 6.2.1.4（Tag 02EN）。今回検証した型は以下。

```lean
lemma intervalOrderHom_functor_map_heq {I : Type u} [Category.{v} I]
    {F G : I ⥤ IntervalSimplexCategory} (h : F = G) {X Y : I} (f : X ⟶ Y) :
    HEq (F.map f).hom.toOrderHom (G.map f).hom.toOrderHom

lemma ordinalIntervalInverse_map_heq {X Y : IntervalSimplexCategory} (f : X ⟶ Y) :
    HEq (augmentedOrderHom (ordinalIntervalEquivalence.inverse.map f).unop)
      (ordinalRecoverMap f.hom.toOrderHom f.property.1 f.property.2)

lemma augmentedInterval_tensor_heq {A B C D : AugmentedSimplexCategory}
    (f : A ⟶ B) (g : C ⟶ D) :
    HEq (ordinalIntervalMap (augmentedOrderHom (f ⊗ₘ g)))
      (ordinalGlue (ordinalIntervalMap (augmentedOrderHom f))
        (ordinalIntervalMap (augmentedOrderHom g)))

lemma mixedBottomTopInterval_map_heq {X₁ X₂ : BottomSimplexCategory}
    {Y₁ Y₂ : TopSimplexCategory} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    HEq (ordinalIntervalMap (augmentedOrderHom
        (mixedBottomTopOrdinal.map (X := (X₁, Y₁)) (Y := (X₂, Y₂)) (f, g)).unop))
      (ordinalAppend f.hom.toOrderHom g.hom.toOrderHom)

lemma mixedTopBottomOrdinal_map_heq {X₁ X₂ : TopSimplexCategory}
    {Y₁ Y₂ : BottomSimplexCategory} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    HEq (augmentedOrderHom
        (mixedTopBottomOrdinal.map (X := (X₁, Y₁)) (Y := (X₂, Y₂)) (f, g)))
      (ordinalGlue f.hom.toOrderHom g.hom.toOrderHom)

def walkingAdjunctionOrdinalCard : (X Y : WalkingAdjunctionPoint) → walkingAdjunctionHom X Y → ℕ

def walkingAdjunctionOrderHom {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) :
    Fin (walkingAdjunctionOrdinalCard X Y A) →o Fin (walkingAdjunctionOrdinalCard X Y B)

def walkingAdjunctionIncomingDim : (X : WalkingAdjunctionPoint) → walkingAdjunctionHom X .minus → ℕ

def walkingAdjunctionOutgoingDim : (Y : WalkingAdjunctionPoint) → walkingAdjunctionHom .minus Y → ℕ

def walkingAdjunctionIncomingMap {X : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X .minus} (f : A ⟶ B) :
    Fin (walkingAdjunctionIncomingDim X A + 1) →o Fin (walkingAdjunctionIncomingDim X B + 1)

def walkingAdjunctionOutgoingMap {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) :
    Fin (walkingAdjunctionOutgoingDim Y A + 1) →o Fin (walkingAdjunctionOutgoingDim Y B + 1)

def walkingAdjunctionTargetCorrection : WalkingAdjunctionPoint → ℕ

lemma walkingAdjunctionOrdinalCard_weight (X Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X Y) :
    walkingAdjunctionOrdinalCard X Y A =
      walkingAdjunctionWeight X Y A + walkingAdjunctionTargetCorrection Y

lemma walkingAdjunctionIncomingDim_weight (X : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X .minus) :
    walkingAdjunctionIncomingDim X A = walkingAdjunctionWeight X .minus A

lemma walkingAdjunctionIncoming_card (X : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X .minus) :
    walkingAdjunctionOrdinalCard X .minus A = walkingAdjunctionIncomingDim X A + 1

lemma walkingAdjunctionOutgoing_card (Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom .minus Y) :
    walkingAdjunctionOrdinalCard .minus Y A = walkingAdjunctionOutgoingDim Y A + 1

lemma walkingAdjunctionIncomingMap_heq {X : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X .minus} (f : A ⟶ B) :
    HEq (walkingAdjunctionIncomingMap (X := X) f)
      (walkingAdjunctionOrderHom (X := X) (Y := .minus) f)

lemma walkingAdjunctionOutgoingMap_heq {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) :
    HEq (walkingAdjunctionOutgoingMap (Y := Y) f)
      (walkingAdjunctionOrderHom (X := .minus) (Y := Y) f)

lemma walkingAdjunctionOrdinalCard_injective (X Y : WalkingAdjunctionPoint) :
    Function.Injective (walkingAdjunctionOrdinalCard X Y)

lemma walkingAdjunctionOrdinalCard_comp_plus (X Z : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X .plus) (B : walkingAdjunctionHom .plus Z) :
    walkingAdjunctionOrdinalCard X Z ((walkingAdjunctionHorizontal X .plus Z).obj (A, B)) =
      walkingAdjunctionOrdinalCard X .plus A + walkingAdjunctionOrdinalCard .plus Z B

lemma walkingAdjunctionOrdinalCard_comp_minus (X Z : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X .minus) (B : walkingAdjunctionHom .minus Z) :
    walkingAdjunctionOrdinalCard X Z ((walkingAdjunctionHorizontal X .minus Z).obj (A, B)) =
      walkingAdjunctionIncomingDim X A + walkingAdjunctionOutgoingDim Z B + 1

lemma walkingAdjunctionOrderHom_hext {X Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom X Y} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B')
    (h : HEq (walkingAdjunctionOrderHom (X := X) (Y := Y) f)
      (walkingAdjunctionOrderHom (X := X) (Y := Y) g)) : HEq f g

lemma walkingAdjunctionOrderHom_comp_plus (X Z : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X .plus} {B B' : walkingAdjunctionHom .plus Z}
    (f : A ⟶ A') (g : B ⟶ B') :
    HEq (walkingAdjunctionOrderHom (X := X) (Y := Z)
        ((walkingAdjunctionHorizontal X .plus Z).map (X := (A, B)) (Y := (A', B')) (f, g)))
      (ordinalAppend (walkingAdjunctionOrderHom (X := X) (Y := .plus) f)
        (walkingAdjunctionOrderHom (X := .plus) (Y := Z) g))

lemma walkingAdjunctionOrderHom_comp_minus (X Z : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X .minus} {B B' : walkingAdjunctionHom .minus Z}
    (f : A ⟶ A') (g : B ⟶ B') :
    HEq (walkingAdjunctionOrderHom (X := X) (Y := Z)
        ((walkingAdjunctionHorizontal X .minus Z).map (X := (A, B)) (Y := (A', B')) (f, g)))
      (ordinalGlue (walkingAdjunctionIncomingMap (X := X) f)
        (walkingAdjunctionOutgoingMap (Y := Z) g))
```

全水平合成の残る結合則と豊穣圏構造の実装は別の未検証の作業木に置いている。
それらを今回の検証済み数には入れない。
元のQCatAdjunctionからの全coherentな延長、HAのモデルとの比較、
元のF≫Uと単位・余単位の照合は引き続き未完であり、G01を済みにはしない。

### 87.3 検証と進み

with_build_lock.sh --class impl --wait 3600 の最大240秒の枠、セッション73700で、
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionMapRepresentation:olean
を実行し、終了0・警告なし（1267 jobs）。その後の追加24根の監査も終了0。
入力24名と出力24名は完全一致、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。外側の終了0を確認して枠は返却済み。
入力・根・全出力・ビルドログは
[g12-inverse-representation-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-inverse-representation-audit-2026-11-15/)に保存。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み4,255行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §88 G01：全十六結合則と実単体的豊穣walking adjunction（11-15）

### 88.1 検証済みの追加

追加は **2ファイル275行・明示宣言11**。累計 **34ファイル4,530行・明示宣言299**。
WalkingAdjunctionMixedAssociativity.lean は202行・7宣言、
WalkingAdjunctionEnrichment.lean は73行・4宣言。200行を超える個別の宣言・証明はない。
G01の既存の構成の係数移送・合成則とその証明の分割であり、新しい一覧IDは足さない。

§87の忠実な全射の共通表示を用いて、中央の二点がplus・minusとminus・plusの
二つの一般形の結合則を証明した。これは両端の四通りずつ、残っていた八通りを覆う。
前者は順序和と端点共有の結合則、後者は端点共有と順序和の結合則へ戻した。
区間の次元の移送は合成の点の個数の法則から供給し、共通表示の異種等式から元の射へ戻す。
既存の八通りと合わせ、十六通り全ての結合則を、任意の添字圏上の全関手の等式として得た。

四Hom圏のnerveを宇宙持ち上げし、構成済みの八つの実双関手を全次数で適用した。
空の自己Homの定値列を単位とし、全単位則と全十六結合則を使って
実際のEnrichedCategory SSet WalkingAdjunctionPointのinstanceを構成した。
そのinstanceの存在や合成の法則を引数として仮定していない。

### 88.2 型と残る境界

原典はHA §4.7.2–§4.7.3・Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8、
Kerodon Remark 6.2.1.4（Tag 02EN）。検証した型は以下。

```lean
lemma ordinalAppend_heq {m n p q m' n' p' q' : ℕ}
    (hm : m = m') (hn : n = n') (hp : p = p') (hq : q = q')
    {f : Fin (m) →o Fin (n)} {f' : Fin (m') →o Fin (n')}
    {g : Fin (p) →o Fin (q)} {g' : Fin (p') →o Fin (q')}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (ordinalAppend f g) (ordinalAppend f' g')

lemma ordinalGlue_heq {m n p q m' n' p' q' : ℕ}
    (hm : m = m') (hn : n = n') (hp : p = p') (hq : q = q')
    {f : Fin (m + 1) →o Fin (n + 1)} {f' : Fin (m' + 1) →o Fin (n' + 1)}
    {g : Fin (p + 1) →o Fin (q + 1)} {g' : Fin (p' + 1) →o Fin (q' + 1)}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (ordinalGlue f g) (ordinalGlue f' g')

lemma walkingAdjunctionIncomingDim_comp_plus (X : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X .plus) (B : walkingAdjunctionHom .plus .minus) :
    walkingAdjunctionIncomingDim X ((walkingAdjunctionHorizontal X .plus .minus).obj (A, B)) =
      walkingAdjunctionOrdinalCard X .plus A + walkingAdjunctionIncomingDim .plus B

lemma walkingAdjunctionOutgoingDim_comp_plus (Z : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom .minus .plus) (B : walkingAdjunctionHom .plus Z) :
    walkingAdjunctionOutgoingDim Z ((walkingAdjunctionHorizontal .minus .plus Z).obj (A, B)) =
      walkingAdjunctionOutgoingDim .plus A + walkingAdjunctionOrdinalCard .plus Z B

lemma walkingAdjunctionHorizontal_assoc_plus_minus (X Z : WalkingAdjunctionPoint)
    (F : I ⥤ walkingAdjunctionHom X .plus)
    (G : I ⥤ walkingAdjunctionHom .plus .minus)
    (H : I ⥤ walkingAdjunctionHom .minus Z) :
    ((F.prod' G ⋙ walkingAdjunctionHorizontal X .plus .minus).prod' H ⋙
        walkingAdjunctionHorizontal X .minus Z) =
      (F.prod' (G.prod' H ⋙ walkingAdjunctionHorizontal .plus .minus Z) ⋙
        walkingAdjunctionHorizontal X .plus Z)

lemma walkingAdjunctionHorizontal_assoc_minus_plus (X Z : WalkingAdjunctionPoint)
    (F : I ⥤ walkingAdjunctionHom X .minus)
    (G : I ⥤ walkingAdjunctionHom .minus .plus)
    (H : I ⥤ walkingAdjunctionHom .plus Z) :
    ((F.prod' G ⋙ walkingAdjunctionHorizontal X .minus .plus).prod' H ⋙
        walkingAdjunctionHorizontal X .plus Z) =
      (F.prod' (G.prod' H ⋙ walkingAdjunctionHorizontal .minus .plus Z) ⋙
        walkingAdjunctionHorizontal X .minus Z)

lemma walkingAdjunctionHorizontal_assoc (W X Y Z : WalkingAdjunctionPoint)
    (F : I ⥤ walkingAdjunctionHom W X) (G : I ⥤ walkingAdjunctionHom X Y)
    (H : I ⥤ walkingAdjunctionHom Y Z) :
    ((F.prod' G ⋙ walkingAdjunctionHorizontal W X Y).prod' H ⋙
        walkingAdjunctionHorizontal W Y Z) =
      (F.prod' (G.prod' H ⋙ walkingAdjunctionHorizontal X Y Z) ⋙
        walkingAdjunctionHorizontal W X Z)

abbrev WalkingAdjunctionHomShape (X Y : WalkingAdjunctionPoint) : SSet.{u}

def walkingAdjunctionUnit (X : WalkingAdjunctionPoint) :
    𝟙_ SSet.{u} ⟶ WalkingAdjunctionHomShape X X

def walkingAdjunctionComposition (X Y Z : WalkingAdjunctionPoint) :
    WalkingAdjunctionHomShape.{u} X Y ⊗ WalkingAdjunctionHomShape.{u} Y Z ⟶
      WalkingAdjunctionHomShape.{u} X Z

instance walkingAdjunctionEnrichedCategory : EnrichedCategory SSet.{u} WalkingAdjunctionPoint
```

今回完成したのはG01の添字となる実豊穣圏である。
元のQCatAdjunctionをこの豊穣圏からの全coherentな豊穣関手へ延長する構成は未完。
Riehl–Verity Theorems 4.3.9・4.3.11の延長を、原典のparental subcomputadの
filtrationと充填から実装する部分が次に残る。構成済みの水平反対の向きとの照合も要る。
原典：[Homotopy coherent adjunctions and the formal theory of monads](https://emilyriehl.github.io/files/adjunctions.pdf)。
単なる豊穣圏の構成をこの延長の代わりとはせず、延長の存在を仮定として追加しない。
元のF≫UとのFunctorIso、元の単位・余単位、HAモデルの照合、G02以降も未完。

### 88.3 検証と進み

with_build_lock.sh --class impl --wait 3600、セッション15089、最大280秒の短いimpl枠。
WalkingAdjunctionMixedAssociativity:oleanの対象ビルドは初回終了0・警告なし（1268 jobs）。
WalkingAdjunctionEnrichment:oleanの対象ビルドも初回終了0・警告なし（1272 jobs）。
追加11根の小さい監査はG12_MIXED_AUDIT_EXIT=0。
入力11名と出力11名は一致、公理依存は標準のpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。exitで外側の終了0まで確認して枠を返却した。
入力・根・全出力・両対象ビルドログは
[g12-walking-adjunction-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-walking-adjunction-audit-2026-11-15/)に保存した。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み4,530行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §89 G01：全頂点の自由な生成語と指定F・Uの零次元の延長（11-15）

### 89.1 検証済みの追加

追加は **3ファイル423行・明示宣言32**。累計 **37ファイル4,953行・明示宣言331**。
WalkingAdjunctionVertices.lean は178行・16宣言、WalkingAdjunctionVertexPaths.lean は133行・9宣言、
WalkingAdjunctionVertexEvaluation.lean は112行・7宣言。
200行を超える個別の宣言・証明はない。
G01の同じwalking adjunctionの生成射・合成則・係数移送・照合の証明の分割であり、
新しい一覧IDを追加していない。

§88の実豊穣圏のHom圏の対象を射とする頂点の圏を構成した。
二点を結ぶ一つずつの生成射のquiverから、その道を水平合成する実関手を作った。
四Homの各対象に語の長さを与え、八つの合成全ての長さの加法則を証明した。
長さは同じ端点の頂点を区別し、道の長さはその実像の長さと一致する。

同じ始点と長さを持つ交互の道は終点を含めて一致することを道の帰納法で示した。
自己Homには標準の偶数語、混合Homには標準の奇数語を与えたので、
空の自己Homを含む全頂点が道の像となる。これにより比較関手のFull・Faithfulを実際に構成した。
その原像から実頂点を道へ戻す実関手を作り、実像の回収と二つの生成射の回収を検証した。

任意の圏DのC・Eと、指定したF : C ⟶ E・U : E ⟶ Cに対して、
この逆比較と自由な道の普遍性を用い、全頂点を評価する実関手を構成した。
二つの生成射の像は同型類ではなく指定したF・Uそのものである。
この構成は元の準圏間の射に適用できる零次元の指定であり、
単位・余単位や高次の延長の存在は仮定していない。

### 89.2 型と残る境界

原典の対応はRiehl–Verity Proposition 3.1.10・Example 3.1.11・Theorem 4.3.9、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。
検証した型は以下。

```lean
structure WalkingAdjunctionVertex where
  point : WalkingAdjunctionPoint

instance walkingAdjunctionVertexCategory : Category WalkingAdjunctionVertex

def walkingAdjunctionOther : WalkingAdjunctionPoint → WalkingAdjunctionPoint

lemma walkingAdjunctionOther_other (X : WalkingAdjunctionPoint) :
    walkingAdjunctionOther (walkingAdjunctionOther X) = X

instance walkingAdjunctionGeneratingQuiver : Quiver WalkingAdjunctionPoint

def walkingAdjunctionGeneratorVertex (X : WalkingAdjunctionPoint) :
    walkingAdjunctionHom X (walkingAdjunctionOther X)

def walkingAdjunctionGeneratorPrefunctor :
    WalkingAdjunctionPoint ⥤q WalkingAdjunctionVertex

def walkingAdjunctionPathFunctor :
    Paths WalkingAdjunctionPoint ⥤ WalkingAdjunctionVertex

def walkingAdjunctionVertexLength : (X Y : WalkingAdjunctionPoint) →
    walkingAdjunctionHom X Y → ℕ

lemma walkingAdjunctionVertexLength_weight (X Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X Y) :
    walkingAdjunctionVertexLength X Y A + walkingAdjunctionTargetCorrection X =
      2 * walkingAdjunctionWeight X Y A + walkingAdjunctionTargetCorrection Y

lemma walkingAdjunctionVertexLength_comp (X Y Z : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X Y) (B : walkingAdjunctionHom Y Z) :
    walkingAdjunctionVertexLength X Z ((walkingAdjunctionHorizontal X Y Z).obj (A, B)) =
      walkingAdjunctionVertexLength X Y A + walkingAdjunctionVertexLength Y Z B

lemma walkingAdjunctionVertexLength_injective (X Y : WalkingAdjunctionPoint) :
    Function.Injective (walkingAdjunctionVertexLength X Y)

lemma walkingAdjunctionVertexLength_id (X : WalkingAdjunctionPoint) :
    walkingAdjunctionVertexLength X X (walkingAdjunctionIdentity X) = 0

lemma walkingAdjunctionVertexLength_generator (X : WalkingAdjunctionPoint) :
    walkingAdjunctionVertexLength X (walkingAdjunctionOther X)
      (walkingAdjunctionGeneratorVertex X) = 1

lemma walkingAdjunctionVertexLength_prefunctor {X Y : WalkingAdjunctionPoint} (e : X ⟶ Y) :
    walkingAdjunctionVertexLength X Y (walkingAdjunctionGeneratorPrefunctor.map e) = 1

lemma walkingAdjunctionPathFunctor_length {X Y : WalkingAdjunctionPoint} (p : Quiver.Path X Y) :
    walkingAdjunctionVertexLength X Y (walkingAdjunctionPathFunctor.map p) = p.length

def walkingAdjunctionGeneratingArrow (X : WalkingAdjunctionPoint) :
    X ⟶ walkingAdjunctionOther X

def walkingAdjunctionEvenPath (X : WalkingAdjunctionPoint) : ℕ → Quiver.Path X X

def walkingAdjunctionOddPath (X : WalkingAdjunctionPoint) (n : ℕ) :
    Quiver.Path X (walkingAdjunctionOther X)

lemma walkingAdjunctionEvenPath_length (X : WalkingAdjunctionPoint) (n : ℕ) :
    (walkingAdjunctionEvenPath X n).length = 2 * n

lemma walkingAdjunctionOddPath_length (X : WalkingAdjunctionPoint) (n : ℕ) :
    (walkingAdjunctionOddPath X n).length = 2 * n + 1

lemma walkingAdjunctionOther_of_ne {X Y : WalkingAdjunctionPoint} (h : X ≠ Y) :
    Y = walkingAdjunctionOther X

lemma walkingAdjunctionGeneratingPath_hext {X Y Z : WalkingAdjunctionPoint}
    (p : Quiver.Path X Y) (q : Quiver.Path X Z) (h : p.length = q.length) :
    Y = Z ∧ HEq p q

instance walkingAdjunctionPathFunctor_faithful : walkingAdjunctionPathFunctor.Faithful

instance walkingAdjunctionPathFunctor_full : walkingAdjunctionPathFunctor.Full

def walkingAdjunctionVertexToPath : WalkingAdjunctionVertex ⥤ Paths WalkingAdjunctionPoint

lemma walkingAdjunctionVertexToPath_map (X Y : WalkingAdjunctionVertex) (f : X ⟶ Y) :
    walkingAdjunctionPathFunctor.map (walkingAdjunctionVertexToPath.map f) = f

lemma walkingAdjunctionVertexToPath_generator (X : WalkingAdjunctionPoint) :
    walkingAdjunctionVertexToPath.map
      (X

def walkingAdjunctionEvaluationPrefunctor (C E : D) (F : C ⟶ E) (U : E ⟶ C) :
    WalkingAdjunctionPoint ⥤q D

def walkingAdjunctionVertexEvaluation (C E : D) (F : C ⟶ E) (U : E ⟶ C) :
    WalkingAdjunctionVertex ⥤ D

lemma walkingAdjunctionVertexEvaluation_left (C E : D) (F : C ⟶ E) (U : E ⟶ C) :
    (walkingAdjunctionVertexEvaluation C E F U).map
      (X

lemma walkingAdjunctionVertexEvaluation_right (C E : D) (F : C ⟶ E) (U : E ⟶ C) :
    (walkingAdjunctionVertexEvaluation C E F U).map
      (X
```

今回得た自由性は零次元に限る。高次のatomicな射の自由な分解・退化との両立、
parental subcomputadのfiltrationと実充填、水平反対の向きの照合は引き続き残る。
元の随伴の単位・余単位の辺の代表は既存のAdjunctionRepresentativesで選んでいるが、
その全coherentな延長を今回の頂点の評価関手から推定しない。
元のF≫UとのFunctorIso、HAモデルの比較とG02以降も未完。
G01の一覧の済みは0を維持する。

### 89.3 検証と進み

with_build_lock.sh --class impl --wait 3600、セッション39231、最大280秒の短いimpl枠。
対象はlake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionVertexEvaluation:olean。
単体記法のスコープ、道の圏と元のquiverの基底型の明示、
道の帰納法における終点の等式輸送と既に閉じた証明の余分なタクティクを修正した。
最終の対象ビルドはG12_VERTEX_BUILD_EXIT=0、警告なし（1277 jobs）。
追加32根の小さい監査はG12_VERTEX_AUDIT_EXIT=0。
入力32名と出力32名は一致し、公理依存は標準のpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。exitで外側の終了0まで確認して枠を返却した。
入力・根・全出力・最終対象ビルドログは
[g12-adjunction-vertices-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-adjunction-vertices-audit-2026-11-15/)に保存した。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み4,953行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §90 G01：全次数の原子的な生成語と自由な道からの全射（11-15）

### 90.1 検証済みの追加

追加は **3ファイル284行・明示宣言19**。累計 **40ファイル5,237行・明示宣言350**。
WalkingAdjunctionLevels.lean は116行・9宣言、WalkingAdjunctionAtomicWords.lean は84行・3宣言、
WalkingAdjunctionAtomicPaths.lean は84行・7宣言。
200行を超える個別の宣言・証明はない。
G01の同じ全随伴の生成射・合成則・分解と照合の証明の分割であり、新しい一覧IDは足さない。

各次数nにおいて、Fin(n+1)から四Hom圏への実関手を射とする実圏を構成した。
§88で証明済みの全単位則と全結合則から圏構造を与え、各単体の全ての頂点の
生成語の長さを足した有限の長さを定めた。この長さは水平合成で加法的である。
長さ0なら端点が同じであり、全関手として単位の定値列に一致することを証明した。
単位の対象の自己射の一意性を使っているので、頂点の等式だけで止めていない。

原子的な射を「長さが正であり、二つに分解すると一方の長さが0」と定義した。
長さ0が実単位を検出する上の証明により、これは非単位で非自明には分解しない条件である。
原子的な語は空の語・原子・語の合成を持つ実データの型とした。
非原子的な正の長さの射は二つのより短い射へ分解できるので、長さの強い帰納法から
全次数の全ての実射について、この語のデータの存在を得た。

原子的な実射を生成射とするquiver、その自由な道を実際に水平合成する比較関手を構成した。
原子的な語のデータから実際の道を作り、その像が元の射そのものとなることを証明した。
これにより全次数の比較関手のFullを構成した。
単に分解の存在を引数に置いたり、生成するという命題を包んだ型を仮定したりしていない。

### 90.2 型と残る境界

原典はRiehl–Verity Definition 2.1.4・Proposition 3.1.10・Theorem 4.3.9、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。今回の型は以下。

```lean
structure WalkingAdjunctionLevel (n : ℕ) where
  point : WalkingAdjunctionPoint

instance walkingAdjunctionLevelCategory (n : ℕ) : Category (WalkingAdjunctionLevel n)

def walkingAdjunctionLevelSize {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) : ℕ

lemma walkingAdjunctionLevelSize_id (n : ℕ) (X : WalkingAdjunctionPoint) :
    walkingAdjunctionLevelSize
      ((Functor.const (Fin (n + 1))).obj (walkingAdjunctionIdentity X)) = 0

lemma walkingAdjunctionLevelSize_comp {n : ℕ} (X Y Z : WalkingAdjunctionPoint)
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (G : Fin (n + 1) ⥤ walkingAdjunctionHom Y Z) :
    walkingAdjunctionLevelSize (F.prod' G ⋙ walkingAdjunctionHorizontal X Y Z) =
      walkingAdjunctionLevelSize F + walkingAdjunctionLevelSize G

lemma walkingAdjunctionLevelSize_vertex_zero {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (h : walkingAdjunctionLevelSize F = 0)
    (i : Fin (n + 1)) : walkingAdjunctionVertexLength X Y (F.obj i) = 0

lemma walkingAdjunctionLevelSize_zero_endpoints {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (h : walkingAdjunctionLevelSize F = 0) :
    X = Y

instance walkingAdjunctionIdentityHom_subsingleton (X : WalkingAdjunctionPoint) :
    Subsingleton (walkingAdjunctionIdentity X ⟶ walkingAdjunctionIdentity X)

lemma walkingAdjunctionLevelSize_zero_eq_id {n : ℕ} {X : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X X) (h : walkingAdjunctionLevelSize F = 0) :
    F = (Functor.const _).obj (walkingAdjunctionIdentity X)

def WalkingAdjunctionLevelIsAtomic {n : ℕ} {X Y : WalkingAdjunctionLevel n} (F : X ⟶ Y) : Prop

inductive WalkingAdjunctionAtomicWord (n : ℕ) :
    {X Y : WalkingAdjunctionLevel n} → (X ⟶ Y) → Type
  | nil (X : WalkingAdjunctionLevel n) : WalkingAdjunctionAtomicWord n (𝟙 X)
  | atom {X Y : WalkingAdjunctionLevel n} (F : X ⟶ Y) (h : WalkingAdjunctionLevelIsAtomic F) :
      WalkingAdjunctionAtomicWord n F
  | comp {X Y Z : WalkingAdjunctionLevel n} {F : X ⟶ Y} {G : Y ⟶ Z}
      (a : WalkingAdjunctionAtomicWord n F) (b : WalkingAdjunctionAtomicWord n G) :
      WalkingAdjunctionAtomicWord n (F ≫ G)

lemma walkingAdjunctionAtomicWord_nonempty {n : ℕ} {X Y : WalkingAdjunctionLevel n}
    (F : X ⟶ Y) : Nonempty (WalkingAdjunctionAtomicWord n F)

structure WalkingAdjunctionAtomicVertex (n : ℕ) where
  level : WalkingAdjunctionLevel n

instance walkingAdjunctionAtomicQuiver (n : ℕ) : Quiver (WalkingAdjunctionAtomicVertex n)

def walkingAdjunctionAtomicPrefunctor (n : ℕ) :
    WalkingAdjunctionAtomicVertex n ⥤q WalkingAdjunctionLevel n

def walkingAdjunctionAtomicPathFunctor (n : ℕ) :
    Paths (WalkingAdjunctionAtomicVertex n) ⥤ WalkingAdjunctionLevel n

def WalkingAdjunctionAtomicWord.toPath {n : ℕ} {X Y : WalkingAdjunctionLevel n} {F : X ⟶ Y}
    (a : WalkingAdjunctionAtomicWord n F) :
    Quiver.Path (V := WalkingAdjunctionAtomicVertex n) ⟨X⟩ ⟨Y⟩

lemma WalkingAdjunctionAtomicWord.toPath_map {n : ℕ} {X Y : WalkingAdjunctionLevel n}
    {F : X ⟶ Y} (a : WalkingAdjunctionAtomicWord n F) :
    (walkingAdjunctionAtomicPathFunctor n).map a.toPath = F

instance walkingAdjunctionAtomicPathFunctor_full (n : ℕ) :
    (walkingAdjunctionAtomicPathFunctor n).Full
```

今回の一般次数の比較についてはFullだけを証明した。Faithfulはまだ証明していない。
原子的な語の型は二項の合成を記録し、括弧付けの一意性を主張する型ではない。
語から自由な道へ送ることで実際の道の像を検収しているが、異なる道の像が等しいときの
道の等式の反映は引き続き別に必要である。
§89の零次元の完全忠実性を、一般次数の忠実性へ流用していない。

次はこの比較のFaithfulと原子性の退化との両立を検収し、
parental subcomputadのfiltrationと実充填を構成する。
水平反対の向きの照合、元のQCatAdjunctionからの全coherentな延長、元のF≫UとのFunctorIso、
元の単位・余単位とHAモデルの比較、G02以降は引き続き未完である。
G01の一覧の済みは0を維持する。

### 90.3 検証と進み

with_build_lock.sh --class impl --wait 3600、セッション22732、最大280秒の短いimpl枠。
対象はlake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicPaths:olean。
全次数の圏・長さ・原子的な分解は初回の対象ビルドで数学の証明が通った。
命題のhaveIと旧push_negの二警告を修正し、道への比較を追加した最終対象ビルドは
G12_LEVEL_BUILD_EXIT=0・警告なし（1303 jobs）。
追加19根の小さい監査はG12_LEVEL_AUDIT_EXIT=0。
入力19名と出力19名は一致し、公理依存は標準のpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。exitで外側の終了0まで確認して枠を返却した。
入力・根・全出力・最終対象ビルドログは
[g12-atomic-generation-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-atomic-generation-audit-2026-11-15/)に保存した。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み5,237行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §91 G01：全水平合成の忠実性と固定した切れ目での全関手の回収（11-15）

### 91.1 検証済みの追加

追加は **2ファイル240行・明示宣言13**。累計 **42ファイル5,477行・明示宣言363**。
OrdinalConcatenationCancellation.lean は91行・4宣言、
WalkingAdjunctionHorizontalFaithful.lean は149行・9宣言。
200行を超える個別の宣言・証明はない。
G01の既存の水平合成の消去則・係数移送とその証明の分割であり、新しい一覧IDは足さない。

既存の有限単調射の順序和の等式から、左と右の因子の射の等式を回収した。
端点共有では、共有点までの包含から左因子を回収し、右因子は最小元保存を明示して
0を別に照合した上で共有点の後の包含から回収した。因子の個数は固定している。

minusから出る実射の区間表示が最小元を保つことを、二つのHomの場合で証明した。
共通表示・入る区間の表示・出る区間の表示のそれぞれの単射性をまとめ、
plus経由では順序和の消去、minus経由では端点共有の消去を適用した。
これにより全八水平合成の実双関手のFaithfulを実際に構成した。

さらに対象の四つの等式を輸送した射の異種等式も、両因子の異種等式へ戻せるようにした。
任意の添字圏Iについて、二つの水平分解の各頂点の因子の対象がそれぞれ一致する場合は、
合成関手の等式から、両方の因子の全関手の等式を回収した。
頂点の同一視だけで終わらず全Iの射を含む。

### 91.2 型と残る境界

原典はRiehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。検証した型は以下。

```lean
lemma ordinalAppend_inj {m n p q : ℕ}
    {f f' : Fin m →o Fin n} {g g' : Fin p →o Fin q}
    (h : ordinalAppend f g = ordinalAppend f' g') : f = f' ∧ g = g'

lemma ordinalGlue_left_inj {m n p q : ℕ}
    {f f' : Fin (m + 1) →o Fin (n + 1)} {g g' : Fin (p + 1) →o Fin (q + 1)}
    (h : ordinalGlue f g = ordinalGlue f' g') : f = f'

lemma ordinalGlue_right_inj {m n p q : ℕ}
    {f f' : Fin (m + 1) →o Fin (n + 1)} {g g' : Fin (p + 1) →o Fin (q + 1)}
    (hg : g 0 = 0) (hg' : g' 0 = 0)
    (h : ordinalGlue f g = ordinalGlue f' g') : g = g'

lemma ordinalGlue_inj {m n p q : ℕ}
    {f f' : Fin (m + 1) →o Fin (n + 1)} {g g' : Fin (p + 1) →o Fin (q + 1)}
    (hg : g 0 = 0) (hg' : g' 0 = 0)
    (h : ordinalGlue f g = ordinalGlue f' g') : f = f' ∧ g = g'

lemma walkingAdjunctionOutgoingMap_zero {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) :
    walkingAdjunctionOutgoingMap (Y := Y) f 0 = 0

lemma walkingAdjunctionOrderHom_injective {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} :
    Function.Injective (walkingAdjunctionOrderHom (X := X) (Y := Y) (A := A) (B := B))

lemma walkingAdjunctionIncomingMap_injective {X : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X .minus} :
    Function.Injective (walkingAdjunctionIncomingMap (X := X) (A := A) (B := B))

lemma walkingAdjunctionOutgoingMap_injective {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} :
    Function.Injective (walkingAdjunctionOutgoingMap (Y := Y) (A := A) (B := B))

lemma walkingAdjunctionHorizontal_plus_map_inj (X Z : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X .plus} {B B' : walkingAdjunctionHom .plus Z}
    (f f' : A ⟶ A') (g g' : B ⟶ B')
    (h : (walkingAdjunctionHorizontal X .plus Z).map (X := (A, B)) (Y := (A', B')) (f, g) =
      (walkingAdjunctionHorizontal X .plus Z).map (X := (A, B)) (Y := (A', B')) (f', g')) :
    f = f' ∧ g = g'

lemma walkingAdjunctionHorizontal_minus_map_inj (X Z : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X .minus} {B B' : walkingAdjunctionHom .minus Z}
    (f f' : A ⟶ A') (g g' : B ⟶ B')
    (h : (walkingAdjunctionHorizontal X .minus Z).map (X := (A, B)) (Y := (A', B')) (f, g) =
      (walkingAdjunctionHorizontal X .minus Z).map (X := (A, B)) (Y := (A', B')) (f', g')) :
    f = f' ∧ g = g'

instance walkingAdjunctionHorizontal_faithful (X Y Z : WalkingAdjunctionPoint) :
    (walkingAdjunctionHorizontal X Y Z).Faithful

lemma walkingAdjunctionHorizontal_map_hext (X Y Z : WalkingAdjunctionPoint)
    {A B A' B' : walkingAdjunctionHom X Y} {C D C' D' : walkingAdjunctionHom Y Z}
    (hA : A = A') (hB : B = B') (hC : C = C') (hD : D = D')
    (f : A ⟶ B) (f' : A' ⟶ B') (g : C ⟶ D) (g' : C' ⟶ D')
    (h : HEq ((walkingAdjunctionHorizontal X Y Z).map (X := (A, C)) (Y := (B, D)) (f, g))
      ((walkingAdjunctionHorizontal X Y Z).map (X := (A', C')) (Y := (B', D')) (f', g'))) :
    HEq f f' ∧ HEq g g'

lemma walkingAdjunctionHorizontal_functor_inj {I : Type*} [Category I]
    (X Y Z : WalkingAdjunctionPoint)
    (F F' : I ⥤ walkingAdjunctionHom X Y) (G G' : I ⥤ walkingAdjunctionHom Y Z)
    (hF : ∀ i, F.obj i = F'.obj i) (hG : ∀ i, G.obj i = G'.obj i)
    (h : F.prod' G ⋙ walkingAdjunctionHorizontal X Y Z =
      F'.prod' G' ⋙ walkingAdjunctionHorizontal X Y Z) : F = F' ∧ G = G'
```

今回のFaithfulは積の各固定Hom上の射の等式の反映であり、
§90の原子的な自由な道からの比較関手のFaithfulとは異なる。
対象の因子、つまり各頂点の切れ目が異なる二つの分解の比較はまだ残る。
その切れ目の比較を有限単調射と区間表示のGalois対応から検収し、
原子的な道の一意性と退化との両立へ進める。
parental subcomputadのfiltration・実充填、水平反対の向きの照合、
元のQCatAdjunctionからの全coherentな延長と同じF≫U・単位・余単位・HAモデルの照合、
G02以降は引き続き未完。G01の済みは0を維持する。

### 91.3 検証と進み

with_build_lock.sh --class impl --wait 3600、セッション77285、最大280秒の短いimpl枠。
対象はlake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionHorizontalFaithful:olean。
Finの包含の単射性の二つの個数を明示し、有限点の値の簡約を補った。
全関手への移送では補助関手の値域を実Hom圏と同じ宇宙0に明示した。
最終G12_CANCEL_BUILD_EXIT=0・警告なし（1269 jobs）。
追加13根の小さい監査はG12_CANCEL_AUDIT_EXIT=0。
入力13名と出力13名は一致、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。exitで外側の終了0を確認して枠を返却した。
入力・根・全出力・対象ビルドログは
[g12-horizontal-cancellation-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-horizontal-cancellation-audit-2026-11-15/)に保存した。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み5,477行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §92 G01：全頂点の切れ目の一貫した比較と実水平分解からの回収（11-15）

### 92.1 検証済みの追加

追加は **3ファイル339行・明示宣言22**。累計 **45ファイル5,816行・明示宣言385**。
OrdinalCutComparison.lean は115行・7宣言、WalkingAdjunctionCutChains.lean は144行・12宣言、
WalkingAdjunctionFactorCuts.lean は80行・3宣言。
200行を超える個別の宣言・証明はない。
G01の既存の水平合成の切れ目の移送・回収・比較の法則とその証明の分割なので、
新しい一覧IDは足さない。

切れ目は、その左にある全ての点の条件で区別できる。
既存の最大元付加と実区間表示のGalois対応から、元の点の像が切れ目より左にある条件と、
逆向きの区間表示で戻した切れ目より元の点が左にある条件が同値であることを証明した。
これを使い、順序和の二因子の間の切れ目を実区間表示から回収した。
端点共有については左因子の最大元保存から共有点の像を照合した。
どちらも個数の等式と射の異種等式の輸送を伴う表示にも適用できるようにした。

実単体の全頂点のplusの切れ目を、逆向きの区間表示の可換条件で結んだデータを定義した。
minusの共有点は元の有限単調射の可換条件で結ぶ。
plusの切れ目は終頂点から一意に決まり、終頂点の順序が全頂点へ戻る。
minusの共有点は始頂点から一意に決まり、始頂点の順序が全頂点へ進む。
従って二つのplusの切れ目、二つのminusの共有点はそれぞれ全頂点で一貫して比較できる。
Galois対応を使い、minusの共有点がplusの切れ目より左にある条件も全頂点で不変であることを
証明した。二種類の切れ目の比較についても、途中で順序が入れ替わることはない。

最後に、実際のplus経由の水平分解から左因子の点の個数を切れ目とするデータを構成した。
minus経由では左因子の入る区間の次元を共有点とした。
全射の可換条件は既存の八つの合成の実射の表示と切れ目・共有点の回収から証明し、
これらの条件を新たな仮定として追加していない。

### 92.2 型と残る境界

原典はRiehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。検証した型は以下。

```lean
lemma ordinalCut_ext {m : ℕ} (a b : Fin (m + 1))
    (h : ∀ i : Fin m, i.val < a.val ↔ i.val < b.val) : a = b

lemma ordinalIntervalMap_cut_iff {m n : ℕ} (f : Fin m →o Fin n)
    (i : Fin m) (c : Fin (n + 1)) :
    i.val < (ordinalIntervalMap f c).val ↔ (f i).val < c.val

lemma ordinalIntervalMap_cut_unique {m n : ℕ} (f : Fin m →o Fin n)
    (a : Fin (m + 1)) (b : Fin (n + 1))
    (h : ∀ i : Fin m, i.val < a.val ↔ (f i).val < b.val) :
    ordinalIntervalMap f b = a

lemma ordinalAppend_cut {m n p q : ℕ} (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    ordinalIntervalMap (ordinalAppend f g) ⟨n, by omega⟩ = ⟨m, by omega⟩

lemma ordinalGlue_shared {m n p q : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) :
    ordinalGlue f g ⟨m, by omega⟩ = ⟨n, by omega⟩

lemma ordinalCut_of_append_profile {a b m n p q : ℕ} (ha : a = m + p) (hb : b = n + q)
    (H : Fin a →o Fin b) (f : Fin m →o Fin n) (g : Fin p →o Fin q)
    (h : HEq H (ordinalAppend f g)) (c : Fin (a + 1)) (d : Fin (b + 1))
    (hc : c.val = m) (hd : d.val = n) : ordinalIntervalMap H d = c

lemma ordinalCut_of_glue_profile {a b m n p q : ℕ}
    (ha : a = m + p + 1) (hb : b = n + q + 1)
    (H : Fin a →o Fin b) (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n)
    (h : HEq H (ordinalGlue f g)) (c : Fin a) (d : Fin b)
    (hc : c.val = m) (hd : d.val = n) : H c = d

structure WalkingAdjunctionPlusCut {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) where
  value (i : Fin (n + 1)) : Fin (walkingAdjunctionOrdinalCard X Y (F.obj i) + 1)
  naturality {i j : Fin (n + 1)} (h : i ≤ j) :
    ordinalIntervalMap (walkingAdjunctionOrderHom (F.map (homOfLE h))) (value j) = value i

structure WalkingAdjunctionMinusCut {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) where
  value (i : Fin (n + 1)) : Fin (walkingAdjunctionOrdinalCard X Y (F.obj i))
  naturality {i j : Fin (n + 1)} (h : i ≤ j) :
    walkingAdjunctionOrderHom (F.map (homOfLE h)) (value i) = value j

@[ext] lemma WalkingAdjunctionPlusCut.ext {a b : WalkingAdjunctionPlusCut F}
    (h : ∀ i, a.value i = b.value i) : a = b

@[ext] lemma WalkingAdjunctionMinusCut.ext {a b : WalkingAdjunctionMinusCut F}
    (h : ∀ i, a.value i = b.value i) : a = b

lemma WalkingAdjunctionPlusCut.le (a b : WalkingAdjunctionPlusCut F)
    (h : a.value (Fin.last n) ≤ b.value (Fin.last n)) (i : Fin (n + 1)) :
    a.value i ≤ b.value i

lemma WalkingAdjunctionPlusCut.last_injective :
    Function.Injective (fun a : WalkingAdjunctionPlusCut F => a.value (Fin.last n))

lemma WalkingAdjunctionPlusCut.total (a b : WalkingAdjunctionPlusCut F) :
    (∀ i, a.value i ≤ b.value i) ∨ (∀ i, b.value i ≤ a.value i)

lemma WalkingAdjunctionMinusCut.le (a b : WalkingAdjunctionMinusCut F)
    (h : a.value 0 ≤ b.value 0) (i : Fin (n + 1)) : a.value i ≤ b.value i

lemma WalkingAdjunctionMinusCut.first_injective :
    Function.Injective (fun a : WalkingAdjunctionMinusCut F => a.value 0)

lemma WalkingAdjunctionMinusCut.total (a b : WalkingAdjunctionMinusCut F) :
    (∀ i, a.value i ≤ b.value i) ∨ (∀ i, b.value i ≤ a.value i)

lemma walkingAdjunctionCut_mixed_iff (a : WalkingAdjunctionPlusCut F)
    (b : WalkingAdjunctionMinusCut F) (i : Fin (n + 1)) :
    (b.value i).val < (a.value i).val ↔ (b.value 0).val < (a.value 0).val

lemma walkingAdjunctionCut_mixed_total (a : WalkingAdjunctionPlusCut F)
    (b : WalkingAdjunctionMinusCut F) :
    (∀ i, (b.value i).val < (a.value i).val) ∨
      (∀ i, (a.value i).val ≤ (b.value i).val)

lemma walkingAdjunctionIncomingMap_last {X : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X .minus} (f : A ⟶ B) :
    walkingAdjunctionIncomingMap f (Fin.last (walkingAdjunctionIncomingDim X A)) =
      Fin.last (walkingAdjunctionIncomingDim X B)

def walkingAdjunctionPlusFactorCut {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X .plus)
    (G : Fin (n + 1) ⥤ walkingAdjunctionHom .plus Y) :
    WalkingAdjunctionPlusCut (F.prod' G ⋙ walkingAdjunctionHorizontal X .plus Y)

def walkingAdjunctionMinusFactorCut {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X .minus)
    (G : Fin (n + 1) ⥤ walkingAdjunctionHom .minus Y) :
    WalkingAdjunctionMinusCut (F.prod' G ⋙ walkingAdjunctionHorizontal X .minus Y)
```

今回の切れ目のデータには外側の切れ目も含み、全ての追跡データを任意の端点を持つ
水平分解へ戻せるとは主張していない。必要な端点の条件は因子の回収時に照合する。
構成した実分解から切れ目への方向は、実射を含めて全次数で検証した。

同じ単体の二つの分解の比較には、合成関手の等式に沿ってこのデータを輸送し、
切れ目の大小から短い因子の分解を実際に回収する部分が残る。
§90の原子的な自由な道の比較のFaithful、原子性の退化との両立、parental subcomputadの
filtration・実充填はまだ未完。元のQCatAdjunctionからの全coherentな延長と
同じF≫U・単位・余単位・HAモデルの照合、G02以降も未完。G01の済みは0を維持する。

### 92.3 検証と進み

with_build_lock.sh --class impl --wait 3600、セッション41448、最大280秒の短いimpl枠。
対象はlake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFactorCuts:olean。
切れ目の比較、全頂点の追跡、実水平分解からの構成はいずれも初回の対象ビルドで通った。
最終G12_CUT_BUILD_EXIT=0・警告なし（1272 jobs）。
追加22根の小さい監査はG12_CUT_AUDIT_EXIT=0。
入力22名と出力22名は一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。監査終了0の後、外側の短い枠は期限で終了124となった。
これは監査の失敗ではなく、対象ビルド・監査の終了0はログと印字で確認済み。
同じセッションの終了124を確認しており、生きた自分の枠は残っていない。
入力・根・全出力・対象ビルドログは
[g12-cut-comparison-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-cut-comparison-audit-2026-11-15/)に保存した。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み5,816行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §93 G01：同じ全単体の実水平分解の全比較と等しい切れ目の回収（11-15）

### 93.1 検証済みの追加

追加は **2ファイル271行・明示宣言14**。累計 **47ファイル6,087行・明示宣言399**。
WalkingAdjunctionCutRank.lean は113行・6宣言、WalkingAdjunctionFactorOrder.lean は158行・8宣言。
200行を超える個別の宣言・証明はない。
G01の同じ水平合成の切れ目・係数移送・分解の照合の法則と証明の分割なので、
新しい一覧IDは足さない。

plusの切れ目を偶数の順位、minusの共有点を奇数の順位としてまとめた。
合成関手の等式に沿って切れ目の全データを同じ単体へ移す構成と、
その輸送が各頂点の順位を変えないことを証明した。
§92の三種類の比較から、任意の二種類の切れ目の順位が全頂点で一貫して比較できる。

指定した同じ全単体Hの水平分解の実データとして、中点・左右の実関手・全合成の等式を記録した。
実分解から構成した切れ目を、合成の等式に沿ってHへ輸送した。
その順位は、元の左因子の頂点の長さと始点の補正の和に一致する。
従って、同じHの任意の二つの水平分解の左因子の長さは、全頂点で一貫して比較できる。

左因子の長さが全頂点で一致する二つの分解については、長さの偶奇から中点を回収した。
長さの単射性から左因子の全頂点の対象を回収し、合成の重みの加法則から右因子の全頂点も回収した。
§91の全関手の消去則を適用し、左右の実関手と分解の実データ全体の等式を証明した。
分解の存在や、元の随伴からの高次の延長の存在を仮定として増やしていない。

### 93.2 型と残る境界

原典はRiehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。検証した型は以下。

```lean
def WalkingAdjunctionCut {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) : WalkingAdjunctionPoint → Type

def walkingAdjunctionCutCoordinate {n : ℕ} {X Y M : WalkingAdjunctionPoint}
    {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y} (a : WalkingAdjunctionCut F M)
    (i : Fin (n + 1)) : ℕ

def walkingAdjunctionCutRank {n : ℕ} {X Y M : WalkingAdjunctionPoint}
    {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y} (a : WalkingAdjunctionCut F M)
    (i : Fin (n + 1)) : ℕ

def walkingAdjunctionCutTransport (h : F = G) (M : WalkingAdjunctionPoint)
    (a : WalkingAdjunctionCut F M) : WalkingAdjunctionCut G M

lemma walkingAdjunctionCutRank_transport (h : F = G) (a : WalkingAdjunctionCut F M)
    (i : Fin (n + 1)) :
    walkingAdjunctionCutRank (walkingAdjunctionCutTransport h M a) i =
      walkingAdjunctionCutRank a i

lemma walkingAdjunctionCutRank_total (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N) :
    (∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) ∨
      (∀ i, walkingAdjunctionCutRank b i ≤ walkingAdjunctionCutRank a i)

structure WalkingAdjunctionFactorization {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) where
  middle : WalkingAdjunctionPoint
  left : Fin (n + 1) ⥤ walkingAdjunctionHom X middle
  right : Fin (n + 1) ⥤ walkingAdjunctionHom middle Y
  fac : left.prod' right ⋙ walkingAdjunctionHorizontal X middle Y = H

def WalkingAdjunctionFactorization.sourceCut (a : WalkingAdjunctionFactorization H) :
    WalkingAdjunctionCut
      (a.left.prod' a.right ⋙ walkingAdjunctionHorizontal X a.middle Y) a.middle

def WalkingAdjunctionFactorization.cut (a : WalkingAdjunctionFactorization H) :
    WalkingAdjunctionCut H a.middle

lemma WalkingAdjunctionFactorization.sourceCut_rank (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    walkingAdjunctionCutRank a.sourceCut i =
      walkingAdjunctionVertexLength X a.middle (a.left.obj i) +
        walkingAdjunctionTargetCorrection X

lemma WalkingAdjunctionFactorization.cut_rank (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    walkingAdjunctionCutRank a.cut i =
      walkingAdjunctionVertexLength X a.middle (a.left.obj i) +
        walkingAdjunctionTargetCorrection X

lemma WalkingAdjunctionFactorization.prefix_total (a b : WalkingAdjunctionFactorization H) :
    (∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) ∨
    (∀ i, walkingAdjunctionVertexLength X b.middle (b.left.obj i) ≤
      walkingAdjunctionVertexLength X a.middle (a.left.obj i))

lemma WalkingAdjunctionFactorization.middle_eq_of_length (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) =
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) : a.middle = b.middle

lemma WalkingAdjunctionFactorization.ext_prefix_length (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) =
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) : a = b
```

今回得たのは、全単体の実水平分解についての全比較と、左因子の長さによる等式の反映である。
長さが小さい方の左因子を大きい方の左因子から実際に分離する、残りの因子の構成は未完。
大小の比較だけから、その残りの実関手の存在を推定していない。
この残りの因子を有限単調射の制限と既存の端点条件の照合から構成する部分へ進む。

§90の原子的な自由な道の比較のFaithful、原子性の退化との両立、parental subcomputadの
filtration・実充填、元のQCatAdjunctionからの全coherentな延長と同じF≫U・単位・余単位・
HAモデルの照合、G02以降は引き続き未完。G01の済みは0を維持する。

### 93.3 検証と進み

with_build_lock.sh --class impl --wait 3600、セッション32752、最大280秒の短いimpl枠。
対象はlake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFactorOrder:olean。
順位の全比較は初回の対象ビルドで通った。
分解の全比較・一意性は、既存の頂点の長さのimportを補った後、数学の証明を変更せず通った。
最終G12_RANK_BUILD_EXIT=0・警告なし（1282 jobs）。
追加14根の小さい監査はG12_RANK_AUDIT_EXIT=0。
入力14名と出力14名は一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。exitで外側の終了0まで確認し、枠を返却した。
入力・根・全出力・対象ビルドログは
[g12-factor-order-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-factor-order-audit-2026-11-15/)に保存した。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み6,087行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §94 G01：残りの実対象・実射の回収と二つの切れ目の間への実制限（11-15）

### 94.1 検証済みの追加

追加は **4ファイル573行・明示宣言31**。累計 **51ファイル6,660行・明示宣言430**。
WalkingAdjunctionOrderProfiles.lean は182行・10宣言、WalkingAdjunctionResidualObjects.lean は127行・8宣言、
OrdinalRestriction.lean は110行・6宣言、WalkingAdjunctionCutIntervals.lean は154行・7宣言。
200行を超える個別の宣言・証明はない。
G01の同じ四Homの射の回収・係数移送・合成則・区間への制限と証明の分割であり、
新しい一覧IDは足さない。

始点がminusなら最小元、終点がminusなら最大元を保つという共通表示の端点条件を定義した。
実Homの対象が端点を持つときの個数の非零を、各実Homから証明した。
四Homの全ての実射がこの端点条件を満たすことを示し、条件を持つ有限単調射から
元の実Homの射を作る構成と両方向の往復を証明した。これにより四Homの全単射を構成した。

左因子の長さの比較から重みの大小を回収し、その差に対応する元の実Homの対象を作った。
minusからplusへの重みが正でなければならない場合も、長さの比較の偶奇から証明した。
短い左因子とこの残りの対象の合成が長い左因子になること、
同じ合成の二分解についてこの残りの対象と短い右因子の合成が長い右因子になることを照合した。
今回の対象の構成は存在を仮定する欄ではなく、元の四Hom内の実対象である。

有限区間への包含と、元の射の像の上下の条件から実際の区間制限を構成した。
その包含との可換性、恒等射の保存、合成の保存を証明した。
実切れ目については、切れ目の右にある点の像も切れ目の右にあり、
切れ目の左側の区間の像も対応する区間内にあることを、plusのGalois条件とminusの共有点から示した。
二つの順位が比較済みなら、その間の区間は元の全体に入り、元の各射の像も対応する区間へ入る。
これらを使って、上下の条件を追加の仮定として課さず、二つの切れ目の間の実有限単調射を構成した。

### 94.2 型と残る境界

原典はRiehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。型の一覧は以下。
後半の区間の法則では、n・X・Y・M・Nと実関手F : Fin(n+1) ⥤ walkingAdjunctionHom X Yを暗黙に固定する。

```lean
instance walkingAdjunctionOrdinalCard_sourceMinus_neZero (Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom .minus Y) : NeZero (walkingAdjunctionOrdinalCard .minus Y A)

instance walkingAdjunctionOrdinalCard_targetMinus_neZero (X : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X .minus) : NeZero (walkingAdjunctionOrdinalCard X .minus A)

def WalkingAdjunctionOrderBoundary (X Y : WalkingAdjunctionPoint)
    {m n : ℕ} (f : Fin m →o Fin n) : Prop

lemma walkingAdjunctionOrderHom_bottom {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B)
    (i : Fin (walkingAdjunctionOrdinalCard .minus Y A)) (hi : i.val = 0) :
    (walkingAdjunctionOrderHom f i).val = 0

lemma walkingAdjunctionOrderHom_top {X : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X .minus} (f : A ⟶ B)
    (i : Fin (walkingAdjunctionOrdinalCard X .minus A))
    (hi : i.val + 1 = walkingAdjunctionOrdinalCard X .minus A) :
    (walkingAdjunctionOrderHom f i).val + 1 = walkingAdjunctionOrdinalCard X .minus B

lemma walkingAdjunctionOrderHom_boundary {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) :
    WalkingAdjunctionOrderBoundary X Y (walkingAdjunctionOrderHom f)

def walkingAdjunctionHomOfOrder {X Y : WalkingAdjunctionPoint}
    (A B : walkingAdjunctionHom X Y)
    (f : Fin (walkingAdjunctionOrdinalCard X Y A) →o Fin (walkingAdjunctionOrdinalCard X Y B))
    (hf : WalkingAdjunctionOrderBoundary X Y f) : A ⟶ B

lemma walkingAdjunctionOrderHom_ofOrder {X Y : WalkingAdjunctionPoint}
    (A B : walkingAdjunctionHom X Y)
    (f : Fin (walkingAdjunctionOrdinalCard X Y A) →o Fin (walkingAdjunctionOrdinalCard X Y B))
    (hf : WalkingAdjunctionOrderBoundary X Y f) :
    walkingAdjunctionOrderHom (walkingAdjunctionHomOfOrder A B f hf) = f

lemma walkingAdjunctionHomOfOrder_order {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) :
    walkingAdjunctionHomOfOrder A B (walkingAdjunctionOrderHom f)
      (walkingAdjunctionOrderHom_boundary f) = f

def walkingAdjunctionOrderProfileEquiv {X Y : WalkingAdjunctionPoint}
    (A B : walkingAdjunctionHom X Y) :
    (A ⟶ B) ≃ {f : Fin (walkingAdjunctionOrdinalCard X Y A) →o
      Fin (walkingAdjunctionOrdinalCard X Y B) // WalkingAdjunctionOrderBoundary X Y f}

def walkingAdjunctionObjectOfWeight (X Y : WalkingAdjunctionPoint) (w : ℕ)
    (_h : X = .minus → Y = .plus → 0 < w) : walkingAdjunctionHom X Y

lemma walkingAdjunctionObjectOfWeight_weight (X Y : WalkingAdjunctionPoint) (w : ℕ)
    (h : X = .minus → Y = .plus → 0 < w) :
    walkingAdjunctionWeight X Y (walkingAdjunctionObjectOfWeight X Y w h) = w

lemma walkingAdjunctionPrefix_weight_le {X M N : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B) :
    walkingAdjunctionWeight X M A ≤ walkingAdjunctionWeight X N B

lemma walkingAdjunctionPrefix_difference_admissible {X M N : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B) :
    M = .minus → N = .plus →
      0 < walkingAdjunctionWeight X N B - walkingAdjunctionWeight X M A

def walkingAdjunctionResidualObject {X M N : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B) :
    walkingAdjunctionHom M N

lemma walkingAdjunctionResidualObject_weight {X M N : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B) :
    walkingAdjunctionWeight M N (walkingAdjunctionResidualObject A B h) =
      walkingAdjunctionWeight X N B - walkingAdjunctionWeight X M A

lemma walkingAdjunctionResidualObject_prefix {X M N : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B) :
    (walkingAdjunctionHorizontal X M N).obj (A, walkingAdjunctionResidualObject A B h) = B

lemma walkingAdjunctionResidualObject_suffix {X M N Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (C : walkingAdjunctionHom M Y) (D : walkingAdjunctionHom N Y)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B)
    (hc : (walkingAdjunctionHorizontal X M Y).obj (A, C) =
      (walkingAdjunctionHorizontal X N Y).obj (B, D)) :
    (walkingAdjunctionHorizontal M N Y).obj (walkingAdjunctionResidualObject A B h, D) = C

def ordinalSegmentInclusion (m a r : ℕ) (h : a + r ≤ m) : Fin r →o Fin m

def ordinalRestrict {m n : ℕ} (f : Fin m →o Fin n) (a c r s : ℕ) (ha : a + r ≤ m)
    (hl : ∀ i, c ≤ (f (ordinalSegmentInclusion m a r ha i)).val)
    (hu : ∀ i, (f (ordinalSegmentInclusion m a r ha i)).val < c + s) : Fin r →o Fin s

lemma ordinalRestrict_val {m n : ℕ} (f : Fin m →o Fin n) (a c r s : ℕ) (ha : a + r ≤ m)
    (hl : ∀ i, c ≤ (f (ordinalSegmentInclusion m a r ha i)).val)
    (hu : ∀ i, (f (ordinalSegmentInclusion m a r ha i)).val < c + s) (i : Fin r) :
    (ordinalRestrict f a c r s ha hl hu i).val =
      (f (ordinalSegmentInclusion m a r ha i)).val - c

lemma ordinalRestrict_square {m n : ℕ} (f : Fin m →o Fin n) (a c r s : ℕ)
    (ha : a + r ≤ m) (hc : c + s ≤ n)
    (hl : ∀ i, c ≤ (f (ordinalSegmentInclusion m a r ha i)).val)
    (hu : ∀ i, (f (ordinalSegmentInclusion m a r ha i)).val < c + s) :
    (ordinalSegmentInclusion n c s hc).comp (ordinalRestrict f a c r s ha hl hu) =
      f.comp (ordinalSegmentInclusion m a r ha)

lemma ordinalRestrict_id {m a r : ℕ} (ha : a + r ≤ m)
    (hl : ∀ i, a ≤ ((OrderHom.id : Fin m →o Fin m)
      (ordinalSegmentInclusion m a r ha i)).val)
    (hu : ∀ i, ((OrderHom.id : Fin m →o Fin m)
      (ordinalSegmentInclusion m a r ha i)).val < a + r) :
    ordinalRestrict OrderHom.id a a r r ha hl hu = OrderHom.id

lemma ordinalRestrict_comp {m n k a c d r s t : ℕ} (f : Fin m →o Fin n) (g : Fin n →o Fin k)
    (ha : a + r ≤ m) (hc : c + s ≤ n)
    (hlf : ∀ i, c ≤ (f (ordinalSegmentInclusion m a r ha i)).val)
    (huf : ∀ i, (f (ordinalSegmentInclusion m a r ha i)).val < c + s)
    (hlg : ∀ i, d ≤ (g (ordinalSegmentInclusion n c s hc i)).val)
    (hug : ∀ i, (g (ordinalSegmentInclusion n c s hc i)).val < d + t)
    (hl : ∀ i, d ≤ ((g.comp f) (ordinalSegmentInclusion m a r ha i)).val)
    (hu : ∀ i, ((g.comp f) (ordinalSegmentInclusion m a r ha i)).val < d + t) :
    ordinalRestrict (g.comp f) a d r t ha hl hu =
      (ordinalRestrict g c d s t hc hlg hug).comp (ordinalRestrict f a c r s ha hlf huf)

lemma walkingAdjunctionCut_bound (a : WalkingAdjunctionCut F M) (i : Fin (n + 1)) :
    walkingAdjunctionCutCoordinate a i + walkingAdjunctionTargetCorrection M ≤
      walkingAdjunctionOrdinalCard X Y (F.obj i)

lemma walkingAdjunctionCutCoordinate_le (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N) (i : Fin (n + 1))
    (h : walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) :
    walkingAdjunctionCutCoordinate a i ≤ walkingAdjunctionCutCoordinate b i

lemma walkingAdjunctionCut_lower (a : WalkingAdjunctionCut F M) {i j : Fin (n + 1)}
    (h : i ≤ j) (k : Fin (walkingAdjunctionOrdinalCard X Y (F.obj i)))
    (hk : walkingAdjunctionCutCoordinate a i ≤ k.val) :
    walkingAdjunctionCutCoordinate a j ≤
      (walkingAdjunctionOrderHom (F.map (homOfLE h)) k).val

lemma walkingAdjunctionCut_upper (a : WalkingAdjunctionCut F M) {i j : Fin (n + 1)}
    (h : i ≤ j) (k : Fin (walkingAdjunctionOrdinalCard X Y (F.obj i)))
    (hk : k.val < walkingAdjunctionCutCoordinate a i + walkingAdjunctionTargetCorrection M) :
    (walkingAdjunctionOrderHom (F.map (homOfLE h)) k).val <
      walkingAdjunctionCutCoordinate a j + walkingAdjunctionTargetCorrection M

def walkingAdjunctionCutIntervalSize (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N) (i : Fin (n + 1)) : ℕ

lemma walkingAdjunctionCutInterval_bound (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N) (i : Fin (n + 1))
    (h : walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) :
    walkingAdjunctionCutCoordinate a i + walkingAdjunctionCutIntervalSize a b i ≤
      walkingAdjunctionOrdinalCard X Y (F.obj i)

def walkingAdjunctionCutIntervalMap (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    Fin (walkingAdjunctionCutIntervalSize a b i) →o
      Fin (walkingAdjunctionCutIntervalSize a b j)
```

二つの切れ目の間の有限単調射を作るところまで検証した。
それが持つべき端点条件、恒等射・全合成の保存を実単体の全射に対して照合し、
重みの差から作った実対象の間の射へ戻して残りの実関手を構成する部分はまだ残る。
一般の区間制限の恒等・合成則だけから、元の準圏でのこの実関手の存在を推定していない。

原子的な自由な道の比較のFaithful、原子性の退化との両立、parental subcomputadの
filtration・実充填、元のQCatAdjunctionからの全coherentな延長と同じF≫U・単位・余単位・
HAモデルの照合、G02以降も引き続き未完。G01の済みは0を維持する。

### 94.3 検証と進み

with_build_lock.sh --class impl --wait 3600、各最大280秒の短いimpl枠。
実Homの射の回収はセッション12403で対象ビルド終了0・警告なし（1270 jobs）、
追加10根の監査もG12_PROFILE_AUDIT_EXIT=0。
この監査終了後、実行中の制御スクリプトを編集していたことにより外側は構文エラーで終了1となった。
対象ビルドと監査の終了0はそれぞれログ・印字で確認済みであり、同じセッションの終了1も確認している。
以後は実行中の制御スクリプトを変更せず、対象・指令の別ファイルだけを更新した。

セッション45142で残りの実対象と区間制限をまとめて検証し、
最終対象はlake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutIntervals:olean。
実対象は初回の対象ビルドで通った。区間制限は像の下限を各点で明示し、
包含との可換式を各点の式へ変えて修正した。
切れ目の制限は共有点の自然数の不等式と、値域の幅だけを書き換える等式を明示した。
最終G12_RESTRICT_BUILD_EXIT=0・警告なし（1285 jobs）。
残りの追加21根の監査はG12_RESTRICT_AUDIT_EXIT=0。
10根・21根とも入力名と出力名は完全一致、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。後の枠はexitで外側の終了0まで確認して返却した。
入力・根・両監査の全出力・対象ビルドログは
[g12-residual-construction-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-residual-construction-audit-2026-11-15/)に保存した。
現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み6,660行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §95 G01：切れ目の間の実関手と元の左因子の全包含（11-15）

### 95.1 検証済みの追加

追加は **4ファイル484行・明示宣言26**。累計 **55ファイル7,144行・明示宣言456**。
WalkingAdjunctionIntervalLaws.lean は183行・9宣言、OrdinalOrderTransport.lean は68行・5宣言、
WalkingAdjunctionResidualFunctor.lean は112行・6宣言、WalkingAdjunctionPrefixInclusions.lean は121行・6宣言。
200行を超える個別の宣言・証明はない。
G01の既存の水平合成の制限・係数移送・合成則・照合の法則と証明の分割なので、
新しい一覧IDは足さない。

四Homの共通表示の恒等射と全合成の保存をまとめた。
二つの切れ目の間の区間の実包含と、その単射性、制限した射との全可換正方形を証明した。
単射な包含を通すことで、制限した射の恒等射・全合成の保存を元の全単体の法則から回収した。
また始点がminusなら最小元、終点がminusなら最大元を保つ条件を、
共有点の可換条件から証明した。端点条件や全合成の法則を新しい仮定に追加していない。

個数の等式に沿う射の輸送と、端点条件・恒等射・全合成との両立を証明した。
同じHの二つの実水平分解の左因子の長さの比較を、同じH上の切れ目の順位へ移した。
分解の切れ目の座標は左因子の重みであり、重みの差から作った残りの実対象の個数は
切れ目の間の区間の個数に一致する。
その等式で制限した射を移し、§94の四Homの実全単射で戻して、
残りの実対象の間の実射を作った。

これらを組み立て、Fin(n+1)から元のHomの圏への **residualFunctorを実際に構成した**。
map_id・map_compは区間制限と個数の輸送の検証済みの法則を忠実な共通表示から戻して証明した。
これは関手の存在を仮定する欄ではなく、実対象・実射・全法則を持つ構成である。

続いて左因子の個数が全合成の個数以下であることを全八合成で証明した。
共通表示を左の先頭区間で評価すると、元の左因子の全射に戻ることを、
順序和と端点共有の全射の表示から照合した。
指定したHの各実水平分解について、左因子をHへ入れる先頭区間の実包含を作り、
全ての射についてこの包含との可換正方形を証明した。

### 95.2 型と残る境界

原典はRiehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。検証した型は以下。
後半ではn・X・YとH : Fin(n+1) ⥤ walkingAdjunctionHom X Yを暗黙に固定する。

```lean
lemma walkingAdjunctionOrderHom_id (X Y : WalkingAdjunctionPoint) (A : walkingAdjunctionHom X Y) :
    walkingAdjunctionOrderHom (𝟙 A) = OrderHom.id

lemma walkingAdjunctionOrderHom_comp {X Y : WalkingAdjunctionPoint}
    {A B C : walkingAdjunctionHom X Y} (f : A ⟶ B) (g : B ⟶ C) :
    walkingAdjunctionOrderHom (f ≫ g) =
      (walkingAdjunctionOrderHom g).comp (walkingAdjunctionOrderHom f)

def walkingAdjunctionCutIntervalInclusion (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) (i : Fin (n + 1)) :
    Fin (walkingAdjunctionCutIntervalSize a b i) →o
      Fin (walkingAdjunctionOrdinalCard X Y (F.obj i))

lemma walkingAdjunctionCutIntervalInclusion_injective (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) (i : Fin (n + 1)) :
    Function.Injective (walkingAdjunctionCutIntervalInclusion a b h i)

lemma walkingAdjunctionCutInterval_square (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (walkingAdjunctionCutIntervalInclusion a b h j).comp
        (walkingAdjunctionCutIntervalMap a b h hij) =
      (walkingAdjunctionOrderHom (F.map (homOfLE hij))).comp
        (walkingAdjunctionCutIntervalInclusion a b h i)

lemma walkingAdjunctionCutInterval_square_apply (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (hij : i ≤ j) (k : Fin (walkingAdjunctionCutIntervalSize a b i)) :
    walkingAdjunctionCutIntervalInclusion a b h j (walkingAdjunctionCutIntervalMap a b h hij k) =
      walkingAdjunctionOrderHom (F.map (homOfLE hij))
        (walkingAdjunctionCutIntervalInclusion a b h i k)

lemma walkingAdjunctionCutIntervalMap_id (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) (i : Fin (n + 1)) :
    walkingAdjunctionCutIntervalMap a b h (le_refl i) = OrderHom.id

lemma walkingAdjunctionCutIntervalMap_comp (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    walkingAdjunctionCutIntervalMap a b h (hij.trans hjk) =
      (walkingAdjunctionCutIntervalMap a b h hjk).comp
        (walkingAdjunctionCutIntervalMap a b h hij)

lemma walkingAdjunctionCutIntervalMap_boundary (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    WalkingAdjunctionOrderBoundary M N (walkingAdjunctionCutIntervalMap a b h hij)

def ordinalOrderHomTransport {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (f : Fin a →o Fin b) : Fin c →o Fin d

lemma ordinalOrderHomTransport_heq {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (f : Fin a →o Fin b) : HEq (ordinalOrderHomTransport hac hbd f) f

lemma ordinalOrderHomTransport_boundary {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (X Y : WalkingAdjunctionPoint) (f : Fin a →o Fin b)
    (hf : WalkingAdjunctionOrderBoundary X Y f) :
    WalkingAdjunctionOrderBoundary X Y (ordinalOrderHomTransport hac hbd f)

lemma ordinalOrderHomTransport_id {a c : ℕ} (hac : a = c) :
    ordinalOrderHomTransport hac hac (OrderHom.id : Fin a →o Fin a) = OrderHom.id

lemma ordinalOrderHomTransport_comp {a b c a' b' c' : ℕ}
    (ha : a = a') (hb : b = b') (hc : c = c') (f : Fin a →o Fin b) (g : Fin b →o Fin c) :
    ordinalOrderHomTransport ha hc (g.comp f) =
      (ordinalOrderHomTransport hb hc g).comp (ordinalOrderHomTransport ha hb f)

lemma WalkingAdjunctionFactorization.rank_le_of_prefix_le (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) :
    ∀ i, walkingAdjunctionCutRank a.cut i ≤ walkingAdjunctionCutRank b.cut i

lemma WalkingAdjunctionFactorization.cut_coordinate (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    walkingAdjunctionCutCoordinate a.cut i = walkingAdjunctionWeight X a.middle (a.left.obj i)

lemma WalkingAdjunctionFactorization.residualObject_card (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard a.middle b.middle
      (walkingAdjunctionResidualObject (a.left.obj i) (b.left.obj i) (h i)) =
        walkingAdjunctionCutIntervalSize a.cut b.cut i

def WalkingAdjunctionFactorization.residualMap (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    walkingAdjunctionResidualObject (a.left.obj i) (b.left.obj i) (h i) ⟶
      walkingAdjunctionResidualObject (a.left.obj j) (b.left.obj j) (h j)

lemma WalkingAdjunctionFactorization.residualMap_profile (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    walkingAdjunctionOrderHom (a.residualMap b h f) =
      ordinalOrderHomTransport (a.residualObject_card b h i).symm (a.residualObject_card b h j).symm
        (walkingAdjunctionCutIntervalMap a.cut b.cut (a.rank_le_of_prefix_le b h) (leOfHom f))

def WalkingAdjunctionFactorization.residualFunctor (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) :
    Fin (n + 1) ⥤ walkingAdjunctionHom a.middle b.middle

lemma ordinalOrderHom_heq_val {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (f : Fin a →o Fin b) (g : Fin c →o Fin d) (h : HEq f g)
    (i : Fin a) (j : Fin c) (hij : i.val = j.val) : (f i).val = (g j).val

lemma walkingAdjunctionHorizontal_prefix_card_le (X M Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom M Y) :
    walkingAdjunctionOrdinalCard X M A ≤
      walkingAdjunctionOrdinalCard X Y ((walkingAdjunctionHorizontal X M Y).obj (A, B))

lemma walkingAdjunctionHorizontal_prefix_val (X M Y : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X M} {B B' : walkingAdjunctionHom M Y}
    (f : A ⟶ A') (g : B ⟶ B') (i : Fin (walkingAdjunctionOrdinalCard X M A)) :
    (walkingAdjunctionOrderHom
      ((walkingAdjunctionHorizontal X M Y).map (X := (A, B)) (Y := (A', B')) (f, g))
        (Fin.castLE (walkingAdjunctionHorizontal_prefix_card_le X M Y A B) i)).val =
      (walkingAdjunctionOrderHom f i).val

lemma WalkingAdjunctionFactorization.prefix_card_le (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard X a.middle (a.left.obj i) ≤
      walkingAdjunctionOrdinalCard X Y (H.obj i)

def WalkingAdjunctionFactorization.prefixInclusion (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    Fin (walkingAdjunctionOrdinalCard X a.middle (a.left.obj i)) →o
      Fin (walkingAdjunctionOrdinalCard X Y (H.obj i))

lemma WalkingAdjunctionFactorization.prefix_square (a : WalkingAdjunctionFactorization H)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    (a.prefixInclusion j).comp (walkingAdjunctionOrderHom (a.left.map f)) =
      (walkingAdjunctionOrderHom (H.map f)).comp (a.prefixInclusion i)
```

残りの実関手residualFunctorの存在と全関手の法則は今回構成済みとなった。
これを元の左因子と合成すると長い左因子に、短い右因子と合成すると長い右因子に戻るという
全関手の二つの等式はまだ未完。対象の等式は§94で検証済みだが、それを全射の等式に流用しない。
次は残りの実関手のHへの区間包含との可換性と、今回の先頭区間の可換性を使って照合する。

原子的な自由な道の比較のFaithful、原子性の退化との両立、parental subcomputadの
filtration・実充填、元のQCatAdjunctionからの全coherentな延長と同じF≫U・単位・余単位・
HAモデルの照合、G02以降は引き続き未完。G01の済みは0を維持する。

### 95.3 検証と進み

with_build_lock.sh --class impl --wait 3600、各最大280秒の短いimpl枠。
セッション94415で区間制限の法則と残りの実関手を検証した。
共通表示の合成の定義の簡約と、二つの正方形を使う計算を明示した後、
残りの実関手の数学の証明は初回の対象ビルドで通った。
行長修正後にその枠は期限で終了124となったことを同じセッションで確認した。

セッション74986で修正後の依存を含め、最終対象
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPrefixInclusions:olean
を検証し、G12_PREFIX_BUILD_EXIT=0・警告なし（1290 jobs）。
先頭区間の全射の照合と実包含の正方形も初回の対象ビルドで通った。
追加26根の小さい監査はG12_PREFIX_AUDIT_EXIT=0。
入力26名と出力26名は一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。exitで外側の終了0まで確認して枠を返却した。
入力・根・全出力・最終対象ビルドログは
[g12-residual-functor-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-residual-functor-audit-2026-11-15/)に保存した。
現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み7,144行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §96 G01：残りの実関手の左右の全合成と実細分（11-15）

### 96.1 検証済みの追加

追加は **2ファイル303行・明示宣言8**。累計 **57ファイル7,447行・明示宣言464**。
WalkingAdjunctionResidualInclusions.lean は92行・5宣言、
WalkingAdjunctionResidualFactorization.lean は211行・3宣言。
個別の宣言・証明に200行を超えるものはない。
G01の同じ水平合成の包含・係数移送・合成則・分解の照合とその証明の分割であり、
新しい一覧IDは足さない。

左因子の点の個数は切れ目の座標と中点の補正の和に一致することをまとめた。
残りの実関手の各実対象を同じHの区間へ入れる実包含を構成し、
その値は左の切れ目の座標に元の点の値を加えたものであることを照合した。
残りの実関手の全射の共通表示は、個数を移した元の区間制限と異種等式で一致する。
これを元の区間制限の可換正方形へ戻し、残りの実関手の全射がHへの実包含と可換することを示した。

短い左因子と残りの実関手の合成が長い左因子に一致することを、全関手の等式として証明した。
対象の等式は§94の構成を使い、射は全ての有限点で照合した。
先頭区間内の点では§95の元の左因子の包含との正方形を使った。
残りの区間内の点では、plusの順序和またはminusの端点共有の表示を用い、
残りの実関手の包含の正方形と、元の長い左因子の先頭区間の正方形を比較した。
共有点を捨てず、minusの場合は左区間の最後の点を含む先頭側へ入れている。

残りの実関手と短い右因子の合成が長い右因子へ戻ることも、全関手の等式で証明した。
全結合則と左の合成の等式で同じ全体Hへ送り、対象の等式を§94の重みの照合から与え、
§91の実水平合成の忠実性で固定した左因子を消した。

以上と全頂点の長さの比較から、同じ全単体の任意の二つの実水平分解について、
一方の分解を他方で細分する **実関手と左右の全合成の等式** の存在を得た。
細分の関手の存在を仮定する欄を導入した結果ではない。

### 96.2 型と残る境界

原典はRiehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。検証した型は以下。
ここではn・X・YとH : Fin(n+1) ⥤ walkingAdjunctionHom X Yを暗黙に固定する。

```lean
lemma WalkingAdjunctionFactorization.prefix_card (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard X a.middle (a.left.obj i) =
      walkingAdjunctionCutCoordinate a.cut i + walkingAdjunctionTargetCorrection a.middle

def WalkingAdjunctionFactorization.residualInclusion (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) (i : Fin (n + 1)) :
    Fin (walkingAdjunctionOrdinalCard a.middle b.middle ((a.residualFunctor b h).obj i)) →o
      Fin (walkingAdjunctionOrdinalCard X Y (H.obj i))

lemma WalkingAdjunctionFactorization.residualInclusion_val (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) (i : Fin (n + 1))
    (x : Fin (walkingAdjunctionOrdinalCard a.middle b.middle
      ((a.residualFunctor b h).obj i))) :
    (a.residualInclusion b h i x).val = walkingAdjunctionCutCoordinate a.cut i + x.val

lemma WalkingAdjunctionFactorization.residualMap_interval_heq
    (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    HEq (walkingAdjunctionOrderHom ((a.residualFunctor b h).map f))
      (walkingAdjunctionCutIntervalMap a.cut b.cut (a.rank_le_of_prefix_le b h) (leOfHom f))

lemma WalkingAdjunctionFactorization.residual_square (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    (a.residualInclusion b h j).comp (walkingAdjunctionOrderHom ((a.residualFunctor b h).map f)) =
      (walkingAdjunctionOrderHom (H.map f)).comp (a.residualInclusion b h i)

lemma WalkingAdjunctionFactorization.residual_prefix (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) :
    a.left.prod' (a.residualFunctor b h) ⋙ walkingAdjunctionHorizontal X a.middle b.middle =
      b.left

lemma WalkingAdjunctionFactorization.residual_suffix (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) :
    (a.residualFunctor b h).prod' b.right ⋙ walkingAdjunctionHorizontal a.middle b.middle Y =
      a.right

lemma WalkingAdjunctionFactorization.exists_refinement (a b : WalkingAdjunctionFactorization H) :
    (∃ T : Fin (n + 1) ⥤ walkingAdjunctionHom a.middle b.middle,
      a.left.prod' T ⋙ walkingAdjunctionHorizontal X a.middle b.middle = b.left ∧
      T.prod' b.right ⋙ walkingAdjunctionHorizontal a.middle b.middle Y = a.right) ∨
    (∃ T : Fin (n + 1) ⥤ walkingAdjunctionHom b.middle a.middle,
      b.left.prod' T ⋙ walkingAdjunctionHorizontal X b.middle a.middle = a.left ∧
      T.prod' a.right ⋙ walkingAdjunctionHorizontal b.middle a.middle Y = b.right)
```

同じ全単体の二つの実水平分解の比較から残りの実関手を構成し、
その左右の全合成の等式を得るところは今回完成した。
次はこれを原子的な左因子の一意性へ適用し、§90の原子的な自由な道の比較のFaithfulへ進める。
一般の水平分解の比較ができたことだけで、自由な道のFaithfulを済みとはしない。

原子性の退化との両立、parental subcomputadのfiltration・実充填、
元のQCatAdjunctionからの全coherentな延長と同じF≫U・単位・余単位・HAモデルの照合、
G02以降も引き続き未完。G01の済みは0を維持する。

### 96.3 検証と進み

with_build_lock.sh --class impl --wait 3600、各最大280秒の短いimpl枠。
最初のセッション46761で残りの包含の数学の証明が通り、
区間制限への輸送の等式は書き換えから等式の直接の合成へ修正した。
その短い枠の終了124を同じセッションで確認した。

セッション35561で最終対象
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionResidualFactorization:olean
を検証した。左の合成の照合では、右包含の有限点の値を自然数の和へ明示的に変える一か所を修正した。
右の合成と実細分の存在は、その後数学の証明を変更せず通った。
最終G12_RESINCL_BUILD_EXIT=0・警告なし（1292 jobs）。
追加8根の小さい監査はG12_RESINCL_AUDIT_EXIT=0。
入力8名と出力8名は一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。exitで外側の終了0まで確認して枠を返却した。
入力・根・全出力・最終対象ビルドログは
[g12-residual-factorization-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-residual-factorization-audit-2026-11-15/)に保存した。
現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み7,447行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §97 G01：原子的な自由な道の忠実性と各次数の相互逆な実表示（11-15）

### 97.1 検証済みの追加

追加は **3ファイル323行・明示宣言13**。累計 **60ファイル7,770行・明示宣言477**。
WalkingAdjunctionAtomicCancellation.lean は95行・3宣言、
WalkingAdjunctionAtomicFaithful.lean は147行・5宣言、
WalkingAdjunctionAtomicPresentation.lean は81行・5宣言。
200行を超える個別の宣言・証明はない。
G01の同じ全随伴の原子的な分解・合成の消去・照合の法則とその証明の分割であり、
新しい一覧IDは足さない。

同じ全単体の原子的な左因子を持つ二分解を、§96の実細分で比較した。
大きい左因子の原子性と短い左因子の正の長さから、間の細分関手の長さが0となる。
長さ0が実際の単位の定値関手を検出する既存の証明と全単位則を適用し、
中点・左右の実関手・分解の実データ全体の等式を得た。
これを各次数の射の合成の等式へ適用し、先頭の実原子の合成が等しいときは
中間の対象が等しく、先頭と残りの射を異種等式で回収できることを証明した。

原子的な一段の道は元の実射へ写ることを確認した。
原子で終わる道、従って空でない原子的な道の実像は、全射の長さの加法性から正の長さを持つ。
道の長さの強い帰納法で、空の道は実像の長さ0から回収し、
空でない道は先頭の原子と残りの回収を使って短い道へ戻した。
全次数について、同じ実像を持つ二つの原子的な自由な道の等式を証明し、
比較関手の **Faithfulを実際に構成した**。§90で構成済みのFullと合わせて完全忠実となった。

さらに、存在を証明済みの原子的な語を実際の道へ展開し、その実像が元の射となることを示した。
これを各次数の実射の圏から原子的な自由な道の圏への逆関手に組み立てた。
単位・全合成の法則は忠実性で戻し、比較と逆関手の両方向の合成が
**全関手そのものとして恒等関手に等しい**ことを証明した。
各次数での自由な表示は存在の仮定ではなく相互逆な実関手として構成済みとなった。

### 97.2 型と残る境界

原典はRiehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。検証した型は以下。
最初の二つの分解の法則ではn・X・YとH : Fin(n+1) ⥤ walkingAdjunctionHom X Yを暗黙に固定する。

```lean
lemma WalkingAdjunctionFactorization.eq_of_atomic_refinement
    (a b : WalkingAdjunctionFactorization H)
    (T : Fin (n + 1) ⥤ walkingAdjunctionHom a.middle b.middle)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨a.middle⟩) a.left)
    (hb : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨b.middle⟩) b.left)
    (hp : a.left.prod' T ⋙ walkingAdjunctionHorizontal X a.middle b.middle = b.left)
    (hq : T.prod' b.right ⋙ walkingAdjunctionHorizontal a.middle b.middle Y = a.right) : a = b

lemma WalkingAdjunctionFactorization.eq_of_atomic_left (a b : WalkingAdjunctionFactorization H)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨a.middle⟩) a.left)
    (hb : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨b.middle⟩) b.left) : a = b

lemma walkingAdjunctionAtomicLeftCancellation {A B C D : WalkingAdjunctionLevel n}
    (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D)
    (hf : WalkingAdjunctionLevelIsAtomic f) (hg : WalkingAdjunctionLevelIsAtomic g)
    (h : f ≫ u = g ≫ v) : ∃ _hBC : B = C, HEq f g ∧ HEq u v

lemma walkingAdjunctionAtomicPathFunctor_generator
    {A B : WalkingAdjunctionAtomicVertex n} (e : A ⟶ B) :
    (walkingAdjunctionAtomicPathFunctor n).map e.toPath = e.val

lemma walkingAdjunctionAtomicPathFunctor_cons_size
    {A B C : WalkingAdjunctionAtomicVertex n} (p : Quiver.Path A B) (e : B ⟶ C) :
    0 < walkingAdjunctionLevelSize ((walkingAdjunctionAtomicPathFunctor n).map (p.cons e))

lemma walkingAdjunctionAtomicPathFunctor_size_pos
    {A B : WalkingAdjunctionAtomicVertex n} (p : Quiver.Path A B) (hp : 0 < p.length) :
    0 < walkingAdjunctionLevelSize ((walkingAdjunctionAtomicPathFunctor n).map p)

lemma walkingAdjunctionAtomicPathFunctor_map_injective
    {A B : WalkingAdjunctionAtomicVertex n} (p q : Quiver.Path A B)
    (h : (walkingAdjunctionAtomicPathFunctor n).map p =
      (walkingAdjunctionAtomicPathFunctor n).map q) : p = q

instance walkingAdjunctionAtomicPathFunctor_faithful (n : ℕ) :
    (walkingAdjunctionAtomicPathFunctor n).Faithful

def walkingAdjunctionAtomicWordPath {n : ℕ} {X Y : WalkingAdjunctionLevel n} (f : X ⟶ Y) :
    Quiver.Path (V := WalkingAdjunctionAtomicVertex n) ⟨X⟩ ⟨Y⟩

lemma walkingAdjunctionAtomicWordPath_map {n : ℕ} {X Y : WalkingAdjunctionLevel n} (f : X ⟶ Y) :
    (walkingAdjunctionAtomicPathFunctor n).map (walkingAdjunctionAtomicWordPath f) = f

def walkingAdjunctionAtomicInverse (n : ℕ) :
    WalkingAdjunctionLevel n ⥤ Paths (WalkingAdjunctionAtomicVertex n)

lemma walkingAdjunctionAtomic_path_roundtrip (n : ℕ) :
    walkingAdjunctionAtomicPathFunctor n ⋙ walkingAdjunctionAtomicInverse n =
      𝟭 (Paths (WalkingAdjunctionAtomicVertex n))

lemma walkingAdjunctionAtomic_level_roundtrip (n : ℕ) :
    walkingAdjunctionAtomicInverse n ⋙ walkingAdjunctionAtomicPathFunctor n =
      𝟭 (WalkingAdjunctionLevel n)
```

今回完成したのは各次数の自由な表示である。
原子的な射が退化で原子的な射へ写ることはまだ未証明であり、
simplicial computadとしての全ての条件を完成とはしていない。
次は有限順序集合の再添字付けと、原子性の退化との両立を検収する。

原典のfillableな原子とそのparent、parental subcomputadのfiltration・実充填、
元のQCatAdjunctionからの全coherentな延長と同じF≫U・単位・余単位・HAモデルの照合、
G02以降も未完。G01の済みは0を維持する。
原典の§4.1–§4.3を再確認したが、fillableなparentの存在を仮定する型を実装に追加していない。
原典：[Homotopy coherent adjunctions and the formal theory of monads](https://emilyriehl.github.io/files/adjunctions.pdf)。

### 97.3 検証と進み

with_build_lock.sh --class impl --wait 3600、短いimpl枠。
セッション56927の最大280秒の枠で原子的な左因子の回収と道の忠実性を検証した。
道の圏の型同義語を扱う箇所では、書き換えを実関手の合成則の直接の等式へ変更し、
忠実性のinstanceの暗黙の引数を明示した。
その後、同じ枠の期限による終了124を確認した。ここでは監査を済みとは数えていない。

セッション5568の最大240秒の枠で、最終対象
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicPresentation:olean
を検証した。逆関手は汎用の原像APIでの対象推論を避け、検証済みの原子的な語の実展開で構成した。
最終G12_PRESENTATION_BUILD_EXIT=0・警告なし（1323 jobs）。
追加13根の小さい監査はG12_PRESENTATION_AUDIT_EXIT=0。
入力13名と出力13名は一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。exitで外側の終了0まで確認して枠を返却した。
入力・根・全出力・最終対象ビルドログは
[g12-atomic-presentation-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-atomic-presentation-audit-2026-11-15/)に保存した。
現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み7,770行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §98 G01：実単体作用の再添字付けと原子性の退化での保存（11-15）

### 98.1 検証済みの追加

追加は **4ファイル369行・明示宣言20**。累計 **64ファイル8,139行・明示宣言497**。
WalkingAdjunctionReindexing.lean は65行・4宣言、WalkingAdjunctionCutFibers.lean は108行・5宣言、
WalkingAdjunctionAtomicReindexing.lean は92行・3宣言、WalkingAdjunctionDegeneracies.lean は104行・8宣言。
200行を超える個別の宣言・証明はない。
G01の同じ全随伴の単体作用・原子的な分解・係数移送とその証明の分割なので、
新しい一覧IDは足さない。

任意の有限順序関手Pによる実Homへの前合成を、各次数の実圏の間の実関手にした。
その恒等・合成の法則を示し、長さ0の単体を再添字付けても長さ0であることを証明した。
元の射が対象の等式による恒等射の輸送である場合、plusの切れ目とminusの共有点の
座標は変わらない。これは四Homの共通表示の恒等則と、二種類の切れ目の可換条件から得た。

Pの同じ像の頂点へ写る二点について、実分解の左因子の長さが同じことを示した。
二点の全順序と薄い順序圏での射の一意性を用い、元の全射が恒等射の輸送となることを適用した。
右因子の長さも、左因子の長さの一致と全水平合成の長さの加法則から一致する。

実切断Qを持つPについて、分解の因子がQ上で長さ0なら全体で長さ0となることを示した。
各頂点を、Q上の同じPの像を持つ頂点と比較している。
これを使い、原子的な全単体Fの再添字付けP⋙Fの実分解をQへ戻し、
Fの原子性を適用して、一方の因子が全体で長さ0となることを証明した。
従って、切断を持つ有限順序関手での再添字付けは原子性を保つ。
この段階の切断は実関手を指定する条件つきの法則であり、次の実退化でその条件を構成した。

単体圏の実射の有限順序関手を作り、恒等射・合成の保存を証明した。
実退化σiと実面δ(i.castSucc)について、第三単体恒等式から実切断の全関手の等式を構成した。
これにより、各次数の実退化関手が原子を原子へ送ることを証明した。
さらに、元のWalkingAdjunctionHomShapeのnerveの退化がこの有限順序関手での前合成そのもので
あることを実定義で照合し、元の全Homの単体集合の退化に対する原子性の保存を得た。
原子性の保存や切断の存在を、完成した実退化の結論の仮定に追加していない。

### 98.2 型と残る境界

原典はRiehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）。検証した型は以下。

```lean
def walkingAdjunctionLevelReindex {m n : ℕ} (P : Fin (m + 1) ⥤ Fin (n + 1)) :
    WalkingAdjunctionLevel n ⥤ WalkingAdjunctionLevel m

lemma walkingAdjunctionLevelReindex_id (n : ℕ) :
    walkingAdjunctionLevelReindex (𝟭 (Fin (n + 1))) = 𝟭 (WalkingAdjunctionLevel n)

lemma walkingAdjunctionLevelReindex_comp {l m n : ℕ}
    (P : Fin (m + 1) ⥤ Fin (n + 1)) (Q : Fin (l + 1) ⥤ Fin (m + 1)) :
    walkingAdjunctionLevelReindex P ⋙ walkingAdjunctionLevelReindex Q =
      walkingAdjunctionLevelReindex (Q ⋙ P)

lemma walkingAdjunctionLevelSize_precomp_zero {m n : ℕ} {X Y : WalkingAdjunctionPoint}
    (P : Fin (m + 1) ⥤ Fin (n + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (h : walkingAdjunctionLevelSize F = 0) : walkingAdjunctionLevelSize (P ⋙ F) = 0

lemma walkingAdjunctionOrderHom_eqToHom_heq {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (h : A = B) :
    HEq (walkingAdjunctionOrderHom (eqToHom h))
      (OrderHom.id : Fin (walkingAdjunctionOrdinalCard X Y A) →o
        Fin (walkingAdjunctionOrdinalCard X Y A))

lemma walkingAdjunctionCut_coordinate_eq_of_identity {n : ℕ} {X Y M : WalkingAdjunctionPoint}
    {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y} (a : WalkingAdjunctionCut F M)
    {i j : Fin (n + 1)} (hij : i ≤ j) (he : F.obj i = F.obj j)
    (hf : F.map (homOfLE hij) = eqToHom he) :
    walkingAdjunctionCutCoordinate a i = walkingAdjunctionCutCoordinate a j

lemma WalkingAdjunctionFactorization.left_length_eq_of_identity {n : ℕ}
    {X Y : WalkingAdjunctionPoint} {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}
    (a : WalkingAdjunctionFactorization F) {i j : Fin (n + 1)} (hij : i ≤ j)
    (he : F.obj i = F.obj j) (hf : F.map (homOfLE hij) = eqToHom he) :
    walkingAdjunctionVertexLength X a.middle (a.left.obj i) =
      walkingAdjunctionVertexLength X a.middle (a.left.obj j)

lemma WalkingAdjunctionFactorization.left_length_eq_of_reindex_fiber {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (a : WalkingAdjunctionFactorization (P ⋙ F))
    {i j : Fin (m + 1)} (he : P.obj i = P.obj j) :
    walkingAdjunctionVertexLength X a.middle (a.left.obj i) =
      walkingAdjunctionVertexLength X a.middle (a.left.obj j)

lemma WalkingAdjunctionFactorization.right_length_eq_of_reindex_fiber {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (a : WalkingAdjunctionFactorization (P ⋙ F))
    {i j : Fin (m + 1)} (he : P.obj i = P.obj j) :
    walkingAdjunctionVertexLength a.middle Y (a.right.obj i) =
      walkingAdjunctionVertexLength a.middle Y (a.right.obj j)

lemma WalkingAdjunctionFactorization.left_size_zero_of_section_zero {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (Q : Fin (n + 1) ⥤ Fin (m + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hQP : Q ⋙ P = 𝟭 (Fin (n + 1))) (a : WalkingAdjunctionFactorization (P ⋙ F))
    (ha : walkingAdjunctionLevelSize (Q ⋙ a.left) = 0) : walkingAdjunctionLevelSize a.left = 0

lemma WalkingAdjunctionFactorization.right_size_zero_of_section_zero {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (Q : Fin (n + 1) ⥤ Fin (m + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hQP : Q ⋙ P = 𝟭 (Fin (n + 1))) (a : WalkingAdjunctionFactorization (P ⋙ F))
    (ha : walkingAdjunctionLevelSize (Q ⋙ a.right) = 0) :
    walkingAdjunctionLevelSize a.right = 0

lemma walkingAdjunctionLevelIsAtomic_precomp_of_split {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (Q : Fin (n + 1) ⥤ Fin (m + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hQP : Q ⋙ P = 𝟭 (Fin (n + 1)))
    (hf : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) F) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) (P ⋙ F)

def walkingAdjunctionSimplexFunctor {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    Fin (m + 1) ⥤ Fin (n + 1)

lemma walkingAdjunctionSimplexFunctor_id (n : ℕ) :
    walkingAdjunctionSimplexFunctor (𝟙 ⦋n⦌) = 𝟭 (Fin (n + 1))

lemma walkingAdjunctionSimplexFunctor_comp {l m n : ℕ}
    (f : ⦋l⦌ ⟶ ⦋m⦌) (g : ⦋m⦌ ⟶ ⦋n⦌) :
    walkingAdjunctionSimplexFunctor f ⋙ walkingAdjunctionSimplexFunctor g =
      walkingAdjunctionSimplexFunctor (f ≫ g)

lemma walkingAdjunctionDegeneracy_section (n : ℕ) (i : Fin (n + 1)) :
    walkingAdjunctionSimplexFunctor (SimplexCategory.δ i.castSucc) ⋙
      walkingAdjunctionSimplexFunctor (SimplexCategory.σ i) = 𝟭 (Fin (n + 1))

def walkingAdjunctionDegeneracyFunctor (n : ℕ) (i : Fin (n + 1)) :
    WalkingAdjunctionLevel n ⥤ WalkingAdjunctionLevel (n + 1)

lemma walkingAdjunctionDegeneracyFunctor_map_atomic (n : ℕ) (i : Fin (n + 1))
    {X Y : WalkingAdjunctionLevel n} (F : X ⟶ Y) (hf : WalkingAdjunctionLevelIsAtomic F) :
    WalkingAdjunctionLevelIsAtomic ((walkingAdjunctionDegeneracyFunctor n i).map F)

lemma walkingAdjunctionHomShape_degeneracy {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (i : Fin (n + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    (((WalkingAdjunctionHomShape.{u} X Y).map (SimplexCategory.σ i).op) (ULift.up F)).down =
      walkingAdjunctionSimplexFunctor (SimplexCategory.σ i) ⋙ F

lemma walkingAdjunctionHomShape_degeneracy_atomic {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (i : Fin (n + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hf : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) F) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩)
      ((((WalkingAdjunctionHomShape.{u} X Y).map (SimplexCategory.σ i).op) (ULift.up F)).down)
```

現在の実模型について、§97の各次数の原子的な自由な道との相互逆な実表示と、
今回の元のnerveの退化での原子性の保存の二条件を検証した。
これはRiehl–Verity Definition 2.1.4のsimplicial computadの二条件の実模型上の検証である。
この入力模型の二条件を、随伴の全coherentな延長の存在へ読み替えていない。

次は原典§4.1–§4.3のfillableな原子・parental subcomputadのfiltration・実充填へ進む。
現在の水平反対の向きと原典の向きの照合、元のQCatAdjunctionからの延長と
同じF≫U・単位・余単位・HAモデルの照合、G02以降はまだ未完。
G01の済みは0を維持する。

### 98.3 検証と進み

with_build_lock.sh --class impl --wait 3600、短いimpl枠。
セッション81418の最大280秒の枠で、再添字付け・同じ像の頂点の照合・切断上の長さ0の検出・
実退化の原子性の保存は全て初回の対象ビルドで数学の証明が通った。
行長修正時にはその枠の期限による終了124を同じセッションで確認した。
ここでは監査を済みとは数えていない。

セッション50199の最大240秒の新しい枠で、修正後の最終対象
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionDegeneracies:olean
を検証し、対象ビルド・その後の小さい監査・外側の終了0を確認した。
対象ビルドは警告なし（1327 jobs）。
追加20根の監査は入力20名と出力20名が一致し、
公理依存はpropext・Classical.choice・Quot.soundのみ。sorryAx・追加公理なし。
入力・根・全出力・最終対象ビルドログは
[g12-atomic-degeneracies-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-atomic-degeneracies-audit-2026-11-15/)に保存した。
現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み8,139行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §99 G01：任意の切れ目の間の実関手と外端からの全単体の回収（11-15）

### 99.1 検証済みの追加

追加は **4ファイル425行・明示宣言24**。累計 **68ファイル8,564行・明示宣言521**。
WalkingAdjunctionCutFunctor.lean は127行・7宣言、WalkingAdjunctionOuterCuts.lean は134行・11宣言、
WalkingAdjunctionCutInclusions.lean は89行・4宣言、WalkingAdjunctionWholeInterval.lean は75行・2宣言。
200行を超える個別の宣言・証明はない。
G01の同じ全随伴の区間表示・単位・係数移送・合成則・照合とその証明の分割なので、
新しい一覧IDは足さない。

§95の実残余関手は既存の二つの実分解から来る切れ目を入力としていた。
今回は任意の比較された二つの切れ目を入力にし、分解から来る条件を使わずに、
その間の元の四Homへの実関手を構成した。
minusからplusへの座標差が正であることは順位の偶奇の補正から証明した。
各対象は座標差の重みで構成し、射は実区間制限の端点条件を個数の等式で移して戻した。
恒等射と全合成の法則も既存の区間制限の法則から実際に回収した。

左単位分解・右単位分解を実関手と実単位則から構成し、その同じ全単体H上の切れ目を取った。
左端の座標は0、右端の座標はHの重みであり、順位はそれぞれ始点の補正と
Hの長さに始点の補正を足したものとなる。
実分解の切れ目がこの両端の間にあることは、因子の長さの非負性と全水平合成の長さの加法則から示した。
任意の抽象的な切れ目がこの範囲にあるとは主張していない。

実区間関手の対象を元のHの区間に入れる実包含を構成し、全ての射の正方形の可換性を証明した。
左右の外端の間の場合、この包含は点の値を変えず、実関手の対象の重みはHと一致する。
これにより、外端の間の実区間関手がH自身と、対象・全射を含む全関手として等しいことを証明した。
関手の存在・関手則・比較の等式の存在を引数に追加していない。

### 99.2 型と残る境界

原典は[Riehl–Verity §4.1–§4.2](https://emilyriehl.github.io/files/adjunctions.pdf)、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。
現模型での区間の回収の法則として、検証した型は以下。

```lean
lemma walkingAdjunctionCut_difference_admissible
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1)) : M = .minus → N = .plus →
      0 < walkingAdjunctionCutCoordinate b i - walkingAdjunctionCutCoordinate a i

def walkingAdjunctionCutIntervalObject
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1)) : walkingAdjunctionHom M N

lemma walkingAdjunctionCutIntervalObject_weight
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1)) :
    walkingAdjunctionWeight M N (walkingAdjunctionCutIntervalObject a b h i) =
      walkingAdjunctionCutCoordinate b i - walkingAdjunctionCutCoordinate a i

lemma walkingAdjunctionCutIntervalObject_card
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard M N (walkingAdjunctionCutIntervalObject a b h i) =
      walkingAdjunctionCutIntervalSize a b i

def walkingAdjunctionCutIntervalHom
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    walkingAdjunctionCutIntervalObject a b h i ⟶ walkingAdjunctionCutIntervalObject a b h j

lemma walkingAdjunctionCutIntervalHom_profile
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    walkingAdjunctionOrderHom (walkingAdjunctionCutIntervalHom a b h f) =
      ordinalOrderHomTransport (walkingAdjunctionCutIntervalObject_card a b h i).symm
        (walkingAdjunctionCutIntervalObject_card a b h j).symm
        (walkingAdjunctionCutIntervalMap a b h (leOfHom f))

def walkingAdjunctionCutIntervalFunctor
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) :
    Fin (n + 1) ⥤ walkingAdjunctionHom M N

def walkingAdjunctionSourceFactorization (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionFactorization H

def walkingAdjunctionTargetFactorization (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionFactorization H

def walkingAdjunctionSourceCut (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionCut H X

def walkingAdjunctionTargetCut (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionCut H Y

lemma walkingAdjunctionSourceCut_coordinate
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (i : Fin (n + 1)) :
    walkingAdjunctionCutCoordinate (walkingAdjunctionSourceCut H) i = 0

lemma walkingAdjunctionTargetCut_coordinate
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (i : Fin (n + 1)) :
    walkingAdjunctionCutCoordinate (walkingAdjunctionTargetCut H) i =
      walkingAdjunctionWeight X Y (H.obj i)

lemma walkingAdjunctionSourceCut_rank
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (i : Fin (n + 1)) :
    walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i =
      walkingAdjunctionTargetCorrection X

lemma walkingAdjunctionTargetCut_rank
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (i : Fin (n + 1)) :
    walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i =
      walkingAdjunctionVertexLength X Y (H.obj i) + walkingAdjunctionTargetCorrection X

lemma walkingAdjunctionOuterCuts_le
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i

lemma WalkingAdjunctionFactorization.sourceCut_le
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y} (a : WalkingAdjunctionFactorization H) :
    ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank a.cut i

lemma WalkingAdjunctionFactorization.le_targetCut
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y} (a : WalkingAdjunctionFactorization H) :
    ∀ i, walkingAdjunctionCutRank a.cut i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i

def walkingAdjunctionCutFunctorInclusion
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1)) :
    Fin (walkingAdjunctionOrdinalCard M N ((walkingAdjunctionCutIntervalFunctor a b h).obj i)) →o
      Fin (walkingAdjunctionOrdinalCard X Y (H.obj i))

lemma walkingAdjunctionCutFunctorInclusion_val
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1))
    (x : Fin (walkingAdjunctionOrdinalCard M N
      ((walkingAdjunctionCutIntervalFunctor a b h).obj i))) :
    (walkingAdjunctionCutFunctorInclusion a b h i x).val =
      walkingAdjunctionCutCoordinate a i + x.val

lemma walkingAdjunctionCutIntervalHom_heq
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    HEq (walkingAdjunctionOrderHom ((walkingAdjunctionCutIntervalFunctor a b h).map f))
      (walkingAdjunctionCutIntervalMap a b h (leOfHom f))

lemma walkingAdjunctionCutFunctor_square
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    (walkingAdjunctionCutFunctorInclusion a b h j).comp
        (walkingAdjunctionOrderHom ((walkingAdjunctionCutIntervalFunctor a b h).map f)) =
      (walkingAdjunctionOrderHom (H.map f)).comp
        (walkingAdjunctionCutFunctorInclusion a b h i)

lemma walkingAdjunctionWholeInterval_obj {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (i : Fin (n + 1)) :
    (walkingAdjunctionCutIntervalFunctor (walkingAdjunctionSourceCut H)
      (walkingAdjunctionTargetCut H) (walkingAdjunctionOuterCuts_le H)).obj i = H.obj i

lemma walkingAdjunctionWholeInterval {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    walkingAdjunctionCutIntervalFunctor (walkingAdjunctionSourceCut H)
      (walkingAdjunctionTargetCut H) (walkingAdjunctionOuterCuts_le H) = H
```

任意の許される切れ目からの左右の実因子の合成、fillableな原子と親の構成、
parental subcomputadのfiltrationと随伴の実充填はまだ完成していない。
原典のcodomain minusという向きは、現模型の水平反対ではsource minusとなる。
この向きの全比較と、与えたQCatAdjunctionからのcoherentな延長、
元のF≫U・単位・余単位・HAモデルの照合も引き続き未完。
今回の全区間の回収を、coherentな延長の存在と読み替えていない。
G01の済みは0、G02以降も未完を維持する。

### 99.3 検証と進み

with_build_lock.sh --class impl --wait 3600、各最大240秒の短いimpl枠。
セッション13970でCutFunctor、69760でOuterCutsの対象ビルドの終了0を確認した。
セッション32973ではWholeIntervalの対象表示の比較証明をLeanが推論できず、終了1を確認した。
比較証明を明記し、最終セッション17861で修正後の
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionWholeInterval:olean
と、続く追加24根だけの公理監査、外側の終了0を確認した。
追加24根は入力名と出力名が一致し、
公理依存はpropext・Classical.choice・Quot.soundのみ。sorryAx・追加公理なし。
入力・根・全出力・最終対象ビルドログは
[g12-cut-functor-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-cut-functor-audit-2026-11-15/)に保存した。
200行を超える個別の宣言・証明はなく、新規Leanの行長は100文字以下。
現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み8,564行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §100 G01：実区間の貼り合わせ・切れ目と実分解の往復・原子の境界（11-15）

### 100.1 検証済みの追加

追加は **6ファイル694行・明示宣言25**。累計 **74ファイル9,258行・明示宣言546**。
WalkingAdjunctionCutComposition.lean は202行・3宣言、WalkingAdjunctionCutFactorization.lean は98行・5宣言、
WalkingAdjunctionCutEndpoints.lean は110行・8宣言、WalkingAdjunctionAtomicBoundaries.lean は90行・3宣言、
WalkingAdjunctionCutBounds.lean は110行・5宣言、WalkingAdjunctionAtomicCuts.lean は84行・1宣言。
200行を超える個別の宣言・証明はない。ファイル全体が202行のCutCompositionでも、
個々の宣言・証明は200行未満である。
G01の同じ全随伴の区間表示・単位・係数移送・合成則・貼り合わせ・照合とその証明の分割なので、
新しい一覧IDは足さない。

三つの比較された切れ目a≤b≤cについて、a–bとb–cの実区間関手の水平合成が、
a–cの実区間関手に全関手として等しいことを証明した。
対象は座標差の重みの加法則で、全射は先頭と残りに分け、元のHの同じ射と実包含の正方形で比較した。
plusの中点では順序和、minusの中点では端点共有の共通表示を使い、空の因子と共有点を含めた。

両外端の間の任意の切れ目から、その左右の実区間関手を因子として実水平分解を構成した。
合成の検収は今回の貼り合わせと§99の全区間の回収を使う。
その分解の切れ目が元の切れ目と一致することと、元の実分解の切れ目から構成し直した分解が
元の実分解と一致することの両往復を、自然性と全射と合成の証明を含む実データの等式で証明した。
分解の存在を新しい仮定に置いていない。

plusの切れ目は終頂点の任意の有限切れ目から逆向きの区間表示で構成し、
minusの共有点は始頂点の任意の有限点から元の共通表示で構成した。
恒等射・全合成の法則で自然性を証明し、端点での評価と全データへの復元の両往復から実全単射を作った。
全てのminusの共有点は両外端の間にあることを有限点の上限と順位の補正から示した。
plusの切れ目は、始点がminusなら終頂点の値が正、終点がminusならその値が元の点の個数未満、
という二つの端点の条件から全頂点で両外端の間にあることを証明した。
全順位の比較を使っており、全頂点の条件を仮定し直していない。

実分解の左因子の長さ0は左の単位分解との等式、右因子の長さ0は右の単位分解との等式と同値である。
これにより、元の原子性は長さが正で、実分解が左右の単位分解だけである条件と同値となる。
さらに、切れ目から実分解を作る構成とその往復を使い、原子性が「両外端の間の全ての切れ目の順位は、
全頂点で左外端または全頂点で右外端に一致する」という条件と同値であることを証明した。

### 100.2 型と残る境界

原典は[Riehl–Verity §4.1–§4.2](https://emilyriehl.github.io/files/adjunctions.pdf)、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。
現模型での原子の実表示とその法則として、検証した型は以下。

```lean
lemma walkingAdjunctionCutFunctor_square_val
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (f : i ⟶ j)
    (k : Fin (walkingAdjunctionOrdinalCard M N
      ((walkingAdjunctionCutIntervalFunctor a b h).obj i))) :
    walkingAdjunctionCutCoordinate a j +
        (walkingAdjunctionOrderHom ((walkingAdjunctionCutIntervalFunctor a b h).map f) k).val =
      (walkingAdjunctionOrderHom (H.map f)
        (walkingAdjunctionCutFunctorInclusion a b h i k)).val

lemma walkingAdjunctionCutIntervalObject_comp
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (c : WalkingAdjunctionCut H P)
    (hab : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (hbc : ∀ i, walkingAdjunctionCutRank b i ≤ walkingAdjunctionCutRank c i)
    (i : Fin (n + 1)) :
    (walkingAdjunctionHorizontal M N P).obj
      (walkingAdjunctionCutIntervalObject a b hab i,
        walkingAdjunctionCutIntervalObject b c hbc i) =
      walkingAdjunctionCutIntervalObject a c (fun j => (hab j).trans (hbc j)) i

lemma walkingAdjunctionCutIntervalFunctor_comp
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (c : WalkingAdjunctionCut H P)
    (hab : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (hbc : ∀ i, walkingAdjunctionCutRank b i ≤ walkingAdjunctionCutRank c i) :
    (walkingAdjunctionCutIntervalFunctor a b hab).prod'
        (walkingAdjunctionCutIntervalFunctor b c hbc) ⋙ walkingAdjunctionHorizontal M N P =
      walkingAdjunctionCutIntervalFunctor a c (fun i => (hab i).trans (hbc i))

lemma walkingAdjunctionCut_ext {a b : WalkingAdjunctionCut H M}
    (h : ∀ i, walkingAdjunctionCutCoordinate a i = walkingAdjunctionCutCoordinate b i) : a = b

def walkingAdjunctionFactorizationOfCut (a : WalkingAdjunctionCut H M)
    (hl : ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank a i)
    (hr : ∀ i, walkingAdjunctionCutRank a i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i) :
    WalkingAdjunctionFactorization H

lemma walkingAdjunctionFactorizationOfCut_coordinate (a : WalkingAdjunctionCut H M)
    (hl : ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank a i)
    (hr : ∀ i, walkingAdjunctionCutRank a i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i) (i : Fin (n + 1)) :
    walkingAdjunctionCutCoordinate (walkingAdjunctionFactorizationOfCut a hl hr).cut i =
      walkingAdjunctionCutCoordinate a i

lemma walkingAdjunctionFactorizationOfCut_cut (a : WalkingAdjunctionCut H M)
    (hl : ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank a i)
    (hr : ∀ i, walkingAdjunctionCutRank a i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i) :
    (walkingAdjunctionFactorizationOfCut a hl hr).cut = a

lemma WalkingAdjunctionFactorization.ofCut_roundtrip (a : WalkingAdjunctionFactorization H) :
    walkingAdjunctionFactorizationOfCut a.cut a.sourceCut_le a.le_targetCut = a

def WalkingAdjunctionPlusCut.ofLast
    (t : Fin (walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) + 1)) :
    WalkingAdjunctionPlusCut H

lemma WalkingAdjunctionPlusCut.ofLast_value_last
    (t : Fin (walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) + 1)) :
    (WalkingAdjunctionPlusCut.ofLast H t).value (Fin.last n) = t

lemma WalkingAdjunctionPlusCut.ofLast_roundtrip (a : WalkingAdjunctionPlusCut H) :
    WalkingAdjunctionPlusCut.ofLast H (a.value (Fin.last n)) = a

def WalkingAdjunctionPlusCut.lastEquiv : WalkingAdjunctionPlusCut H ≃
    Fin (walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) + 1)

def WalkingAdjunctionMinusCut.ofFirst
    (t : Fin (walkingAdjunctionOrdinalCard X Y (H.obj 0))) : WalkingAdjunctionMinusCut H

lemma WalkingAdjunctionMinusCut.ofFirst_value_zero
    (t : Fin (walkingAdjunctionOrdinalCard X Y (H.obj 0))) :
    (WalkingAdjunctionMinusCut.ofFirst H t).value 0 = t

lemma WalkingAdjunctionMinusCut.ofFirst_roundtrip (a : WalkingAdjunctionMinusCut H) :
    WalkingAdjunctionMinusCut.ofFirst H (a.value 0) = a

def WalkingAdjunctionMinusCut.firstEquiv : WalkingAdjunctionMinusCut H ≃
    Fin (walkingAdjunctionOrdinalCard X Y (H.obj 0))

lemma WalkingAdjunctionFactorization.left_size_zero_iff
    (a : WalkingAdjunctionFactorization H) : walkingAdjunctionLevelSize a.left = 0 ↔
      a = walkingAdjunctionSourceFactorization H

lemma WalkingAdjunctionFactorization.right_size_zero_iff
    (a : WalkingAdjunctionFactorization H) : walkingAdjunctionLevelSize a.right = 0 ↔
      a = walkingAdjunctionTargetFactorization H

lemma walkingAdjunctionLevelIsAtomic_iff_boundary_factorizations
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ↔
      0 < walkingAdjunctionLevelSize H ∧ ∀ a : WalkingAdjunctionFactorization H,
        a = walkingAdjunctionSourceFactorization H ∨
          a = walkingAdjunctionTargetFactorization H

lemma walkingAdjunctionTargetCut_rank_card (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (i : Fin (n + 1)) :
    walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i +
        walkingAdjunctionTargetCorrection Y = 2 * walkingAdjunctionOrdinalCard X Y (H.obj i)

lemma WalkingAdjunctionMinusCut.source_le (a : WalkingAdjunctionMinusCut H) :
    ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank (M := .minus) a i

lemma WalkingAdjunctionMinusCut.le_target (a : WalkingAdjunctionMinusCut H) :
    ∀ i, walkingAdjunctionCutRank (M := .minus) a i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i

lemma WalkingAdjunctionPlusCut.source_le (a : WalkingAdjunctionPlusCut H)
    (hl : X = .minus → 0 < (a.value (Fin.last n)).val) :
    ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank (M := .plus) a i

lemma WalkingAdjunctionPlusCut.le_target (a : WalkingAdjunctionPlusCut H)
    (hr : Y = .minus → (a.value (Fin.last n)).val <
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n))) :
    ∀ i, walkingAdjunctionCutRank (M := .plus) a i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i

lemma walkingAdjunctionLevelIsAtomic_iff_boundary_cuts {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ↔
      0 < walkingAdjunctionLevelSize H ∧
        ∀ (M : WalkingAdjunctionPoint) (a : WalkingAdjunctionCut H M)
          (_hl : ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
            walkingAdjunctionCutRank a i)
          (_hr : ∀ i, walkingAdjunctionCutRank a i ≤
            walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i),
          (∀ i, walkingAdjunctionCutRank a i =
            walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i) ∨
          (∀ i, walkingAdjunctionCutRank a i =
            walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i)
```

原子性を両外端の条件まで移したが、非退化の原子のfillable条件と親の実構成、
parental subcomputadのfiltration、元のQCatAdjunctionからの全coherentな延長はまだ未完。
原典の向きと現模型の水平反対の全比較、同じF≫U・単位・余単位・HAモデルの照合も未完である。
今回の切れ目と実分解の両往復を、coherentな延長の存在へ読み替えていない。
G01の済みは0、G02以降も未完を維持する。

### 100.3 検証と進み

with_build_lock.sh --class impl --wait 3600、各最大240秒の短いimpl枠。
区間合成はセッション7636の表示の不一致による算術失敗を確認し、
関手・対象の表示を明記してセッション54785で対象ビルドの終了0を確認した。
セッション23422でCutFactorization、3822でCutEndpointsの対象ビルドが通った。
3822ではAtomicBoundariesの依存する型の算術書き換えが失敗し、
書き換えを局所化して2964で対象ビルドと追加19根の小さい監査の終了0を確認した。
最終セッション5769で、追加の境界則と原子の切れ目の判定を含む最終対象
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicCuts:olean
SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutBounds:olean
と、続く追加25根だけの公理監査、外側の終了0を確認した。
追加25根は入力名と出力名が一致し、
公理依存はpropext・Classical.choice・Quot.soundのみ。sorryAx・追加公理なし。
入力・根・全出力・最終対象ビルドログは
[g12-cut-gluing-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-cut-gluing-audit-2026-11-15/)に保存した。
新規Leanの行長は100文字以下。現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み9,258行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §101 G01：実全単体の原子性の有限端点による必要十分条件（11-15）

### 101.1 検証済みの追加

追加は **4ファイル403行・明示宣言14**。累計 **78ファイル9,661行・明示宣言560**。
WalkingAdjunctionEndpointSizes.lean は114行・5宣言、WalkingAdjunctionAtomicEndpointBounds.lean は96行・3宣言、
WalkingAdjunctionCutBoundaryEquality.lean は83行・4宣言、WalkingAdjunctionAtomicEndpoints.lean は110行・2宣言。
200行を超える個別の宣言・証明はない。新規Leanの行長は100文字以下。
G01の同じ原子的な分解の実表示・端点の照合・単位・係数移送とその証明の分割なので、
新しい一覧IDは足さない。

原子的な実全単体Hの有限端点による必要十分条件を証明した。
始頂点の共通表示の個数は始点・終点の補正の和、終頂点の個数は1となる。
四Homでの始頂点の個数はplus→plusで0、混合で1、minus→minusで2である。
全ての場合に終頂点は一点である。

長さが正なら終頂点は非空である。空なら各頂点からの元の実射の表示が全頂点を空にし、
長さの有限和は0となるためである。
minus自己Homでは、始頂点が一点なら最小元・最大元の保存が全頂点を一点にし、全長0となる。
従って正の長さなら始頂点は二点以上である。
混合Homの非空性と合わせ、正の長さから始頂点の個数の補正による下限を得た。

原子性からの上限は、余分な点がある場合に実際の内側の切れ目を構成して証明した。
終頂点に二点以上あれば、値1のplusの切れ目が両外端の間にあり、どちらの外端とも順位が一致しない。
始頂点の個数が補正の和を超える場合は、始点の補正を値とするminusの共有点が同じ矛盾を与える。
§100の切れ目と実分解の往復を介して元の原子性を使い、端点の個数の必要条件を得た。

逆向きには、二つの端点の個数は正の全長を保証する。
plusの切れ目は終頂点で0か1だけで、両外端の間にある条件により実際に存在する方の外端に一致する。
minusの共有点は始頂点で、四Homに応じて空、一つの外端、二つの外端に分かれる。
端点の評価の単射性から自然性を含む実切れ目の等式を得て、元の全分解の原子性へ戻した。
頂点の必要条件だけを原子性と宣言したのではなく、全ての実分解・全射を含む元の定義との同値を証明した。

### 101.2 型と残る境界

原典は[Riehl–Verity §4.1–§4.2](https://emilyriehl.github.io/files/adjunctions.pdf)、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。
現在の有限順序の実模型の原子の表示の法則として、検証した型は以下。

```lean
lemma walkingAdjunctionVertexLength_card (X Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X Y) :
    walkingAdjunctionVertexLength X Y A + walkingAdjunctionTargetCorrection X +
      walkingAdjunctionTargetCorrection Y = 2 * walkingAdjunctionOrdinalCard X Y A

lemma walkingAdjunctionLastCard_pos_of_size_pos {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (hp : 0 < walkingAdjunctionLevelSize H) :
    0 < walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n))

lemma walkingAdjunctionMinusFirstCard_two_le_of_size_pos {n : ℕ}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom .minus .minus)
    (hp : 0 < walkingAdjunctionLevelSize H) :
    2 ≤ walkingAdjunctionOrdinalCard .minus .minus (H.obj 0)

lemma walkingAdjunctionFirstCard_corrections_le_of_size_pos {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hp : 0 < walkingAdjunctionLevelSize H) :
    walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y ≤
      walkingAdjunctionOrdinalCard X Y (H.obj 0)

lemma walkingAdjunctionSize_pos_of_endpoint_cards {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hfirst : walkingAdjunctionOrdinalCard X Y (H.obj 0) =
      walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y)
    (hlast : walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 1) :
    0 < walkingAdjunctionLevelSize H

lemma walkingAdjunctionAtomic_last_card_le_one
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) ≤ 1

lemma walkingAdjunctionAtomic_first_card_le_corrections
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard X Y (H.obj 0) ≤
      walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y

lemma walkingAdjunctionAtomic_endpoint_cards
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard X Y (H.obj 0) =
        walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y ∧
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 1

lemma WalkingAdjunctionPlusCut.eq_source_of_last_zero {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom .plus Y} (a : WalkingAdjunctionPlusCut H)
    (hz : (a.value (Fin.last n)).val = 0) : a = walkingAdjunctionSourceCut H

lemma WalkingAdjunctionPlusCut.eq_target_of_last_card {n : ℕ} {X : WalkingAdjunctionPoint}
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom X .plus} (a : WalkingAdjunctionPlusCut H)
    (ht : (a.value (Fin.last n)).val =
      walkingAdjunctionOrdinalCard X .plus (H.obj (Fin.last n))) :
    a = walkingAdjunctionTargetCut H

lemma WalkingAdjunctionMinusCut.eq_source_of_first_zero {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom .minus Y} (a : WalkingAdjunctionMinusCut H)
    (hz : (a.value 0).val = 0) : a = walkingAdjunctionSourceCut H

lemma WalkingAdjunctionMinusCut.eq_target_of_first_top {n : ℕ} {X : WalkingAdjunctionPoint}
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom X .minus} (a : WalkingAdjunctionMinusCut H)
    (ht : (a.value 0).val + 1 = walkingAdjunctionOrdinalCard X .minus (H.obj 0)) :
    a = walkingAdjunctionTargetCut H

lemma walkingAdjunctionAtomic_of_endpoint_cards {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hfirst : walkingAdjunctionOrdinalCard X Y (H.obj 0) =
      walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y)
    (hlast : walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 1) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H

lemma walkingAdjunctionLevelIsAtomic_iff_endpoint_cards {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ↔
      walkingAdjunctionOrdinalCard X Y (H.obj 0) =
          walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y ∧
        walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 1
```

非退化の原子のfillable条件と親の実構成、parental subcomputadのfiltration、
元のQCatAdjunctionからの全coherentな延長はまだ未完。
原典の向きと現模型の水平反対の全比較、同じF≫U・単位・余単位・HAモデルの照合も未完。
今回の原子の有限端点による判定を、coherentな延長の存在へ読み替えていない。
G01の済みは0、G02以降も未完を維持する。

### 101.3 検証と進み

with_build_lock.sh --class impl --wait 3600、各最大240秒の短いimpl枠。
セッション13139でEndpointSizes、49731でAtomicEndpointBounds・CutBoundaryEqualityの対象ビルドの終了0を確認した。
セッション54125で最終対象
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicEndpoints:olean
と、続く追加14根だけの公理監査、外側の終了0を確認した。
今回の数学の証明は全て最初の対象ビルドで通過した。最終対象ビルドは警告なし（1331 jobs）。
追加14根は入力名と出力名が一致し、公理依存はpropext・Classical.choice・Quot.soundのみ。
sorryAx・追加公理なし。入力・根・全出力・最終対象ビルドログは
[g12-atomic-endpoints-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-atomic-endpoints-audit-2026-11-15/)に保存した。
現在自分の生きたビルド・監査の枠は残っていない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み9,661行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。

## §102 G01：最初の実併合・元の射の実因子化・約10,000行の途中報告（11-15）

### 102.1 検証済みの追加

追加は **3ファイル341行・明示宣言21**。累計 **81ファイル10,002行・明示宣言581**。
OrdinalBottomMerge.lean は100行・7宣言、WalkingAdjunctionBottomMerge.lean は141行・8宣言、
WalkingAdjunctionBottomMergeLaws.lean は100行・6宣言。
200行を超える個別の宣言・証明はない。新規Leanの行長は100文字以下。
G01の同じ実区間・原子の親の実表示の構成と、その単位・係数移送・合成・照合の法則と証明の分割なので、
新しい一覧IDは足さない。

最初の二点を併合する実有限単調射Fin(m+2)→Fin(m+1)と、後の点を選ぶ実切断を構成した。
最初の二点の像が同じ有限単調射fは、fとその切断の合成を残余射として、併合を通して実際に因子化する。
切断の等式、全点での因子化の等式、最小元・最大元の保存と残余射の端点条件を証明した。

始点minusの元の実Homでは、点の個数が一つ小さい実対象を構成した。
元の実射fが二番目の点を0へ送る場合、元の最小元の保存と合わせて最初の二点の像は同じになる。
個数の等式による輸送と四Homの共通表示の回収により、実併合射と実残余射を構成し、
それらの合成が元の実射fに、元のHom内の射の等式として一致することを証明した。
二つの実射やその合成の等式の存在を仮定に追加していない。

実併合の共通表示は構成済みの切断から全射である。
全射性を使い、実併合との合成は右因子を区別することと、右因子が構成した実残余射に一意に一致することを示した。
併合前後の実対象は点の個数が一つ違うため異なり、この最初の実射は対象の等式による単位ではない。

### 102.2 型と残る境界

原典は[Riehl–Verity §4.1–§4.2](https://emilyriehl.github.io/files/adjunctions.pdf)、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）。
現模型での原子の親に用いる射の細分とその法則として、検証した型は以下。

```lean
def ordinalBottomMerge (m : ℕ) : Fin (m + 2) →o Fin (m + 1)

def ordinalBottomMergeSection (m : ℕ) : Fin (m + 1) →o Fin (m + 2)

lemma ordinalBottomMerge_val (m : ℕ) (i : Fin (m + 2)) :
    (ordinalBottomMerge m i).val = i.val - 1

lemma ordinalBottomMerge_section (m : ℕ) :
    (ordinalBottomMerge m).comp (ordinalBottomMergeSection m) = OrderHom.id

lemma ordinalBottomMerge_factor {m n : ℕ} (f : Fin (m + 2) →o Fin n)
    (h : f 0 = f (0 : Fin (m + 1)).succ) :
    (f.comp (ordinalBottomMergeSection m)).comp (ordinalBottomMerge m) = f

lemma ordinalBottomMerge_boundary (m : ℕ) :
    WalkingAdjunctionOrderBoundary .minus .minus (ordinalBottomMerge m)

lemma ordinalBottomMerge_residual_boundary {m n : ℕ} (Y : WalkingAdjunctionPoint)
    (f : Fin (m + 2) →o Fin n) (hf : WalkingAdjunctionOrderBoundary .minus Y f)
    (h1 : (f (0 : Fin (m + 1)).succ).val = 0) :
    WalkingAdjunctionOrderBoundary .minus Y (f.comp (ordinalBottomMergeSection m))

def walkingAdjunctionBottomMergeObject (Y : WalkingAdjunctionPoint) (m : ℕ) :
    walkingAdjunctionHom .minus Y

lemma walkingAdjunctionBottomMergeObject_card (Y : WalkingAdjunctionPoint) (m : ℕ) :
    walkingAdjunctionOrdinalCard .minus Y (walkingAdjunctionBottomMergeObject Y m) = m + 1

def walkingAdjunctionBottomMergeArrow {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2) :
    A ⟶ walkingAdjunctionBottomMergeObject Y m

lemma walkingAdjunctionBottomMergeArrow_profile {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2) :
    walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA) =
      ordinalOrderHomTransport hA.symm (walkingAdjunctionBottomMergeObject_card Y m).symm
        (ordinalBottomMerge m)

lemma walkingAdjunctionBottomMerge_raw_one {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0) :
    ((ordinalOrderHomTransport hA rfl (walkingAdjunctionOrderHom f))
      (0 : Fin (m + 1)).succ).val = 0

def walkingAdjunctionBottomMergeResidual {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0) :
    walkingAdjunctionBottomMergeObject Y m ⟶ B

lemma walkingAdjunctionBottomMergeResidual_profile {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0) :
    walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeResidual f m hA h1) =
      ordinalOrderHomTransport (walkingAdjunctionBottomMergeObject_card Y m).symm rfl
        ((ordinalOrderHomTransport hA rfl (walkingAdjunctionOrderHom f)).comp
          (ordinalBottomMergeSection m))

lemma walkingAdjunctionBottomMerge_factor {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0) :
    walkingAdjunctionBottomMergeArrow A m hA ≫ walkingAdjunctionBottomMergeResidual f m hA h1 =
      f

lemma ordinalBottomMerge_surjective (m : ℕ) : Function.Surjective (ordinalBottomMerge m)

lemma ordinalOrderHomTransport_surjective {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (f : Fin a →o Fin b) (hf : Function.Surjective f) :
    Function.Surjective (ordinalOrderHomTransport hac hbd f)

lemma walkingAdjunctionBottomMergeArrow_surjective {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2) :
    Function.Surjective (walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA))

lemma walkingAdjunctionBottomMergeObject_ne {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2) :
    A ≠ walkingAdjunctionBottomMergeObject Y m

lemma walkingAdjunctionBottomMergeArrow_cancel {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    {B : walkingAdjunctionHom .minus Y} (f g : walkingAdjunctionBottomMergeObject Y m ⟶ B)
    (h : walkingAdjunctionBottomMergeArrow A m hA ≫ f =
      walkingAdjunctionBottomMergeArrow A m hA ≫ g) : f = g

lemma walkingAdjunctionBottomMergeResidual_unique {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0)
    (g : walkingAdjunctionBottomMergeObject Y m ⟶ B)
    (hg : walkingAdjunctionBottomMergeArrow A m hA ≫ g = f) :
    g = walkingAdjunctionBottomMergeResidual f m hA h1
```

今回は一つの元の射の実細分とその一意性までである。
全単体で最初の併合を選ぶ過程、細分した射を挿入した実全単体、
非退化の原子のfillable条件と親、parental subcomputadのfiltration、
元のQCatAdjunctionからの全coherentな延長はまだ未完。
原典の向きと現模型の水平反対の全比較、同じF≫U・単位・余単位・HAモデルの照合も未完。
今回の元の射の因子化を、原子の親の完成やcoherentな延長の存在へ読み替えていない。
G01の済みは0、G02以降も未完を維持する。

### 102.3 検証

with_build_lock.sh --class impl --wait 3600、各最大240秒の短いimpl枠。
セッション5607では切断の単調性の型が一致せず、その未完成の定義に依存する後続宣言にも失敗が出た。
切断の単調性を値の加算の不等式として明記し、34740でOrdinalBottomMergeと
WalkingAdjunctionBottomMergeの対象ビルド・追加15根の小さい監査の終了0を確認した。
元の実Homの因子化の回収は最初の対象ビルドで通った。
セッション7377で最終対象
lake build SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergeLaws:olean
と、続く追加21根だけの公理監査、外側の終了0を確認した。
最終対象ビルドは警告なし（1293 jobs）。追加21根は入力名と出力名が一致し、
公理依存はpropext・Classical.choice・Quot.soundのみ。sorryAx・追加公理なし。
入力・根・全出力・最終対象ビルドログは
[g12-bottom-merge-audit-2026-11-15/](../../../evidence/bhatt-scholze/g12/g12-bottom-merge-audit-2026-11-15/)に保存した。
現在自分の生きたビルド・監査の枠は残っていない。

### 102.4 約10,000行の途中報告

BS-M15 §8の約10,000行の途中報告として記録する。
外枠20,000行中、検証済みは**10,002行**、残りは**9,998行**である。
現在までに全随伴の有限順序による全Hom・全水平合成・原子的な自由表示・退化の原子性・
切れ目と実分解の両往復・原子の有限端点による判定・元の射の最初の併合による細分までを検証した。
これらはG01の入力模型とその実構成の法則であり、G01の実結論の完成とは数えていない。
G01の全coherentな延長と指定された元のモナドとの照合が未完、G02〜G15も未完である。
承認済みの指示どおり、この途中の行数では止めずに原子の親の実構成へ続ける。
外枠・一覧を変更したことにはしない。

M15・drafts・main・⑤aの既存ファイル・Interfaceは変更していない。
全体ビルド・大きい監査は行っていない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01実装中、外枠20,000行中、検証済み10,002行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。


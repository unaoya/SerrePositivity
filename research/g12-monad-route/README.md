# 打ち切ったG12モナド経路の部品目録

2026-11-16、⑤d。BS-M15 §11・D81の続きに基づく参照用の紙。
対象は `SerrePositivity/InfinityCategories/HA/Monads/` の **179ファイル・18,959行**。
G12のモナド経路は打ち切りであり、この取り込みはG12・Barr–Beck・CAlgのpresentabilityの完成を意味しない。
ここでは既存の型と到達点を記録し、実装を再開しない。

## 基準・取り込み・検証の出所

| 役割 | コミット・成果物 |
|---|---|
| 最後のLean追加 | `8bd16ab2b`：実原子の親子の全単射。以後の二コミットは報告のみ |
| 残枠の報告 | `37fe25328`：⑤d報告§129 |
| 一般理論／BEの残量・別経路の紙 | `afd5b5c3b`：⑤d報告§130–§132 |
| mainへの取り込み | `c14cab8ead684321ac6e92978c8c4206571f8034`：`math/bs-m15`のmerge |
| 入口・監査への登録／この目録の基準main | `293f12d884f67f31c57faae5f0f9e65888b285f1` |
| 目録作成枝 | `codex/g12-monad-catalog`（上のmainから分岐、旧枝は保持） |
| MonadsディレクトリのGit tree | `f4b7c42506d9f56551a8d6cf4cef246fdbb792f3`。`8bd16ab2b`と基準mainで一致 |

登録先は [Derivedの入口](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/Project/Entrypoints/Derived.lean) と
[Derivedの監査](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/scripts/audit_derived_infinity.lean)。
基準mainでは入口に179モジュールのimportがある。rootビルド・Derived監査の通過は取り込み時のユーザー報告による。
この目録の作成ではLeanの変更、ビルド、監査の再実行をしていない。
既存の対象ビルド・小さい公理監査の記録は [⑤d報告§131–§132](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/formalization-plans/bhatt-scholze/reports/report-codex-m15.md) およびその前の各追加節にある。

## 読み方・原典・型の規約

主な入口は、全合成の `EndofunctorComposition`、全作用の型の `NativeMonad`、
実豊穣圏の `WalkingAdjunctionEnrichment`、全次数の自由な道の `WalkingAdjunctionAtomicPresentation`、
実親子の全単射の `WalkingAdjunctionAtomicCellPairing`。
後者から実filtrationやcoherent延長を取り出す宣言はまだない。

原典略記：

- **HA**：[Higher Algebra（2017-09-18）](https://www.math.ias.edu/~lurie/papers/HA.pdf)、§4.7.2–§4.7.3、特にProposition 4.7.3.3。
- **RV**：[Riehl–Verity, Homotopy coherent adjunctions and the formal theory of monads](https://emilyriehl.github.io/files/adjunctions.pdf)。
  Remark 3.3.8は有限順序模型、Proposition 3.1.10は自由性、§4.1–§4.2は親子・付着・filtration、
  Theorem 4.3.9は延長、§6–§7は代数準圏・モナド性。
- **Kerodon**：[Remark 6.2.1.4、Tag 02EN](https://kerodon.net/tag/02EN)。
  これはホモトピー双圏の随伴の照合の位置であり、全coherentな延長やEM準圏の存在定理の代用ではない。

各ファイルの「原典・利用箇所」はソースのmodule docstringを基に記録した。
補助計算の番号は**利用する位置**であり、そのファイルが当該原典の一般定理を全部証明したという対応ではない。
共通のHA・Kerodonの参照だけで、有限順序模型とHAのモナド表示の全比較を済みにしない。
現在のwalking adjunctionはRVの向きとの水平反対を伴う模型。向きと全作用の比較は未完である。
`NativeFillable`は現在の模型で定義した純粋性条件であり、原典の文字列条件との全比較は未完。

下の型は**実ソースから抜き出した宣言のヘッダー**である。証明・実装本体は省き、構造の欄は保持する。
各ファイルの主な構成と法則を1〜4本選んだ（全宣言の索引ではない）。
共通namespaceは `SerrePositivity.InfinityCategories.HA.Monads`。
`NativeMonad`内部の短い名前はそのnamespaceも付記する。
暗黙引数の局所`variable`文脈を併記し、`universe`・`open`・記法・importはリンク先のソースに従う。
同じファイルでも文脈は宣言位置ごとに異なるため、以下の文脈と型の抜粋をまとめてLeanへ貼って実行する用途ではない。
型の`:=`以降の省略を未証明の追加宣言と解釈しない。

## 役割別の一覧

| 役割 | ファイル数 | Lean行数 |
|---|---:|---:|
| 1. 全自己関手・walking monad・NativeMonad・指定随伴 | 8 | 695 |
| 2. 有限順序・端点保存圏・区間表示 | 26 | 3,277 |
| 3. walking adjunctionの四Hom・水平合成・実豊穣圏 | 14 | 2,026 |
| 4. 零次元の生成射と自由な道・評価 | 3 | 423 |
| 5. 全次数の分解・切れ目・残余・区間 | 23 | 2,853 |
| 6. 原子的な語・自由な道・相互逆な表示 | 7 | 665 |
| 7. 有限鎖の挿入・細分・面・非退化性の一般補題 | 17 | 1,439 |
| 8. 原子の端点・有限順序の幅・有限性・再添字 | 27 | 2,634 |
| 9. 最初の併合・minus側の親・内側の子 | 19 | 1,849 |
| 10. plus側の親・最後の子・前置の回収 | 10 | 1,000 |
| 11. 非指定面・幅と深さの減少・境界の例外 | 19 | 1,477 |
| 12. 実原子の型・実親子・全単射 | 6 | 621 |
| **合計** | **179** | **18,959** |

### 1. 全自己関手・walking monad・NativeMonad・指定随伴

#### [AdjunctionRepresentatives.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/AdjunctionRepresentatives.lean)

指定された∞随伴の単位・余単位の全関手準圏内の辺を選ぶ。（66行）

原典・利用箇所：HA Proposition 4.7.3.3 の誘導モナドの構成に用いる始めのデータ。 Riehl–Verity Theorems 4.3.9・4.3.11、Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`adjunctionUnitRepresentative`

```lean
variable {C E : SSet.{u}} [Quasicategory C] [Quasicategory E]
  {F : C ⟶ E} {U : E ⟶ C}

def adjunctionUnitRepresentative (a : QCatAdjunction F U) :
    ((ihom C).obj C).Edge (functorVertex (𝟙 C)) (functorVertex (F ≫ U))
```

主宣言：`adjunctionCounitRepresentative`

```lean
variable {C E : SSet.{u}} [Quasicategory C] [Quasicategory E]
  {F : C ⟶ E} {U : E ⟶ C}

def adjunctionCounitRepresentative (a : QCatAdjunction F U) :
    ((ihom E).obj E).Edge (functorVertex (U ≫ F)) (functorVertex (𝟙 E))
```

#### [EndofunctorComposition.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/EndofunctorComposition.lean)

関手準圏 Fun(C,C) の合成を、全単体集合上の積として固定する。（106行）

原典・利用箇所：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の誘導モナドの周囲の合成。 Kerodon Remark 6.2.1.4（Tag 02EN）の h Fun への移行に先立つ全関手単体集合を使う。 このファイルは周囲の合成だけを構成し、随伴の coherent なモナドへの持ち上げは別に行う。

主宣言：`EndofunctorSpace`

```lean
abbrev EndofunctorSpace (C : SSet.{u}) : SSet.{u}
```

主宣言：`endofunctorComposition`

```lean
def endofunctorComposition (C : SSet.{u}) :
    EndofunctorSpace C ⊗ EndofunctorSpace C ⟶ EndofunctorSpace C
```

主宣言：`endofunctorCompositionMonObj`

```lean
@[instance_reducible]
def endofunctorCompositionMonObj (C : SSet.{u}) : MonObj (EndofunctorSpace C)
```

#### [EndofunctorSimplicialMonoid.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/EndofunctorSimplicialMonoid.lean)

自己関手の全合成を、次数ごとのモノイドと全ての単体作用に表示する。（62行）

原典・利用箇所：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の周囲の全合成。 Kerodon Remark 6.2.1.4（Tag 02EN）の h Fun へ忘却する前の合成を保持する。

主宣言：`endofunctorSimplicialMonoid`

```lean
def endofunctorSimplicialMonoid (C : SSet.{u}) : SimplicialObject MonCat.{u}
```

主宣言：`endofunctorSimplicialMonoid_mul`

```lean
lemma endofunctorSimplicialMonoid_mul (C : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (x y : (endofunctorSimplicialMonoid C).obj n) :
    x * y = (endofunctorComposition C).app n (x, y)
```

#### [NativeMonad.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/NativeMonad.lean)

walking monad の全単体作用として coherent なモナドの型を固定する。（81行）

原典・利用箇所：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の誘導モナドとその代数の共通入力。 walking monad の表示は Riehl–Verity, Homotopy coherent adjunctions and the formal  theory of monads, Remark 3.3.8 の有限順序集合と順序和による表示。 Kerodon Remark 6.2.1.4（Tag 02EN）のホモトピー双圏へ忘却する前の作用を保持する。 随伴からこの全作用を構成する存在定理は別途必要であり、ここでは仮定しない。

主宣言：`NativeMonad`

```lean
structure NativeMonad (C : SSet.{u}) where
  /-- N(Δ₊) の全単体の作用。頂点・辺だけに切り詰めない。 -/
  action : WalkingMonadShape.{u} ⟶ EndofunctorSpace C
  /-- 空順序集合が指定された恒等自己関手に作用する法則。 -/
  map_unit : walkingMonadUnit ≫ action = endofunctorUnit C
  /-- 全順序和の作用が同じ全関手の合成と一致する法則。 -/
  map_composition : walkingMonadComposition ≫ action =
    (action ⊗ₘ action) ≫ endofunctorComposition C
```

主宣言：`NativeMonad.endofunctor`

```lean
variable {C : SSet.{u}}

-- namespace NativeMonad
def endofunctor (T : NativeMonad C) : C ⟶ C
```

#### [NativeMonadUnit.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/NativeMonadUnit.lean)

全モナド作用の単位を、全自己関手準圏の実際の辺として取り出す。（75行）

原典・利用箇所：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の元の単位の照合。 Riehl–Verity Definition 6.1.1、Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`NativeMonad.unitEdge`

```lean
variable {C : SSet.{u}}

-- namespace NativeMonad
def unitEdge (T : NativeMonad C) :
    (EndofunctorSpace C).Edge (SSet.unitHomEquiv _ (curry' (𝟙 C)))
      (SSet.unitHomEquiv _ (curry' T.endofunctor))
```

主宣言：`NativeMonad.unitEdge_edge`

```lean
variable {C : SSet.{u}}

-- namespace NativeMonad
lemma unitEdge_edge (T : NativeMonad C) :
    T.unitEdge.edge = T.action.app (Opposite.op ⦋1⦌)
      (ULift.up (ComposableArrows.mk₁
        (WithInitial.homTo (⦋0⦌ : SimplexCategory))))
```

#### [WalkingMonad.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingMonad.lean)

全モナドの添字である有限順序集合の圏の nerve と順序和を指定する。（63行）

原典・利用箇所：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の全モナドの表示。 Riehl–Verity, Homotopy coherent adjunctions and the formal theory of monads, Remark 3.3.8 の順序和による walking monad の Hom を使う。 Kerodon Remark 6.2.1.4（Tag 02EN）の二胞体へ忘却する前の全添字を保持する。

主宣言：`WalkingMonadShape`

```lean
abbrev WalkingMonadShape : SSet.{u}
```

主宣言：`walkingMonadComposition`

```lean
def walkingMonadComposition :
    WalkingMonadShape.{u} ⊗ WalkingMonadShape.{u} ⟶ WalkingMonadShape.{u}
```

主宣言：`walkingMonadGenerator`

```lean
def walkingMonadGenerator : WalkingMonadShape.{u} _⦋0⦌
```

#### [WalkingMonadEnrichment.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingMonadEnrichment.lean)

walking monad の単体的豊穣圏と、全作用の豊穣関手による表示。（117行）

原典・利用箇所：HA §4.7.2–§4.7.3・Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8。 Kerodon Remark 6.2.1.4（Tag 02EN）への忘却に先立つ全coherenceの表示。

主宣言：`walkingMonadEnrichedCategory`

```lean
instance walkingMonadEnrichedCategory : EnrichedCategory SSet.{u} WalkingMonadObject
```

主宣言：`NativeMonad.toEnrichedFunctor`

```lean
variable {C : SSet.{u}}

-- namespace NativeMonad
def toEnrichedFunctor (T : NativeMonad C) :
    EnrichedFunctor SSet.{u} WalkingMonadObject SSet.{u}
```

主宣言：`NativeMonad.ofEnrichedFunctor`

```lean
variable {C : SSet.{u}}

-- namespace NativeMonad
def ofEnrichedFunctor
    (F : EnrichedFunctor SSet.{u} WalkingMonadObject SSet.{u}) :
    NativeMonad (F.obj .star)
```

#### [WalkingMonadLaws.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingMonadLaws.lean)

walking monad の順序和の全単位・結合則。（125行）

原典・利用箇所：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の全モナドの添字の合成。 Riehl–Verity Remark 3.3.8 の順序和、Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`walkingMonadMonObj`

```lean
variable {I : Type v} [Category.{w} I]

@[instance_reducible]
def walkingMonadMonObj : MonObj WalkingMonadShape.{u}
```

### 2. 有限順序・端点保存圏・区間表示

#### [AugmentedOrdinalMaps.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/AugmentedOrdinalMaps.lean)

増大単体圏の射を、空も含む有限順序集合の実単調射として表示する。（134行）

原典・利用箇所：HA Proposition 4.7.3.3 のwalking adjunctionの区間表示への包装。 Riehl–Verity Remark 3.3.8、Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`augmentedOrdinalCard`

```lean
abbrev augmentedOrdinalCard : AugmentedSimplexCategory → ℕ
```

主宣言：`augmentedOrderHom_comp`

```lean
@[simp] lemma augmentedOrderHom_comp {X Y Z : AugmentedSimplexCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    augmentedOrderHom (f ≫ g) = (augmentedOrderHom g).comp (augmentedOrderHom f)
```

#### [AugmentedOrdinalTensorMaps.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/AugmentedOrdinalTensorMaps.lean)

混合Homで使う増大単体圏の順序和を、有限単調射の順序和と照合する。（149行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の残る混合水平結合則。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`ordinalAppendNonempty_heq`

```lean
lemma ordinalAppendNonempty_heq {m n p q : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin p →o Fin q) : HEq (ordinalAppendNonempty f g) (ordinalAppend f g)
```

主宣言：`augmentedOrderHom_tensor`

```lean
lemma augmentedOrderHom_tensor {A B C D : AugmentedSimplexCategory}
    (f : A ⟶ B) (g : C ⟶ D) :
    HEq (augmentedOrderHom (f ⊗ₘ g))
      (ordinalAppend (augmentedOrderHom f) (augmentedOrderHom g))
```

#### [EndpointOrdinalActions.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/EndpointOrdinalActions.lean)

walking adjunction の混合Homの、増大単体圏による二つの水平合成。（225行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の Δ₊×Δ∞→Δ∞、Δ−∞×Δ₊→Δ−∞。Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`topOrdinalPrefix`

```lean
def topOrdinalPrefix : SimplexCategory ⥤ TopSimplexCategory ⥤ TopSimplexCategory
```

主宣言：`topOppositeOrdinalAction`

```lean
def topOppositeOrdinalAction :
    TopSimplexCategory × AugmentedSimplexCategoryᵒᵖ ⥤ TopSimplexCategory
```

#### [EndpointSimplex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/EndpointSimplex.lean)

walking adjunction の混合Homに用いる端点保存の単体圏を構成する。（151行）

原典・利用箇所：HA Proposition 4.7.3.3 の全拡張の添字、Riehl–Verity Observation 3.3.6・ Remark 3.3.8 の混合Hom。Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`simplexPreservesBottom`

```lean
def simplexPreservesBottom : MorphismProperty SimplexCategory
```

主宣言：`endpointSimplexEquivalence`

```lean
def endpointSimplexEquivalence : BottomSimplexCategory ≌ TopSimplexCategoryᵒᵖ
```

#### [OrdinalAdjoinTop.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalAdjoinTop.lean)

空を含む有限順序集合の射への最大元の付加と、その制限の逆変換。（145行）

原典・利用箇所：HA Proposition 4.7.3.3 のwalking adjunctionの区間表示、 Riehl–Verity Remark 3.3.8、Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`ordinalAdjoinTop`

```lean
variable {m n k : ℕ}

def ordinalAdjoinTop (f : Fin m →o Fin n) : Fin (m + 1) →o Fin (n + 1)
```

主宣言：`ordinalAdjoinTop_remove`

```lean
variable {m n k : ℕ}

lemma ordinalAdjoinTop_remove (g : Fin (m + 1) →o Fin (n + 1))
    (hg : ∀ i, g i = Fin.last n ↔ i = Fin.last m)
    (ht : g (Fin.last m) = Fin.last n) :
    ordinalAdjoinTop (ordinalRemoveTop g hg) = g
```

#### [OrdinalAdjoints.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalAdjoints.lean)

端点を保つ有限順序集合の射のGalois随伴を実際に構成する。（247行）

原典・利用箇所：HA Proposition 4.7.3.3 の全拡張の添字となるwalking adjunctionの混合Hom。 Riehl–Verity Observation 3.3.6・Remark 3.3.8、Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`ordinalLowerFiber`

```lean
variable {m n k : ℕ}

def ordinalLowerFiber (f : Fin (m + 1) →o Fin (n + 1)) (j : Fin (n + 1)) :
    Finset (Fin (m + 1))
```

主宣言：`ordinalLeftAdjoint_comp`

```lean
variable {m n k : ℕ}

lemma ordinalLeftAdjoint_comp (f : Fin (n + 1) →o Fin (m + 1))
    (g : Fin (k + 1) →o Fin (n + 1))
    (hf : f (Fin.last n) = Fin.last m) (hg : g (Fin.last k) = Fin.last n) :
    ordinalLeftAdjoint (f.comp g) (by change f (g (Fin.last k)) = Fin.last m; rw [hg, hf]) =
      (ordinalLeftAdjoint g hg).comp (ordinalLeftAdjoint f hf)
```

#### [OrdinalAppendVariation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalAppendVariation.lean)

有限単調射の順序和は実像の個数と変化量について加法的である。（88行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の実生成射の前置の幅、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の最後の深さの実親の幅。

主宣言：`ordinalMapVariation_heq`

```lean
lemma ordinalMapVariation_heq {a b c d : ℕ} (ha : a = c) (hb : b = d)
    (f : Fin a →o Fin b) (g : Fin c →o Fin d) (h : HEq f g) :
    ordinalMapVariation f = ordinalMapVariation g
```

主宣言：`ordinalMapVariation_append`

```lean
lemma ordinalMapVariation_append {m n p q : ℕ} (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    ordinalMapVariation (ordinalAppend f g) = ordinalMapVariation f + ordinalMapVariation g
```

#### [OrdinalBottomMerge.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalBottomMerge.lean)

有限順序集合の最初の二点を併合する実射と、その切断・因子化を構成する。（100行）

原典・利用箇所：Riehl–Verity §4.1–§4.2のfillableな原子の親の実構成、 HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の実区間の細分。

主宣言：`ordinalBottomMerge`

```lean
def ordinalBottomMerge (m : ℕ) : Fin (m + 2) →o Fin (m + 1)
```

主宣言：`ordinalBottomMerge_residual_boundary`

```lean
lemma ordinalBottomMerge_residual_boundary {m n : ℕ} (Y : WalkingAdjunctionPoint)
    (f : Fin (m + 2) →o Fin n) (hf : WalkingAdjunctionOrderBoundary .minus Y f)
    (h1 : (f (0 : Fin (m + 1)).succ).val = 0) :
    WalkingAdjunctionOrderBoundary .minus Y (f.comp (ordinalBottomMergeSection m))
```

#### [OrdinalBottomMergeVariation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalBottomMergeVariation.lean)

先行辺の像が値1を欠くと、底併合との合成は変化量を1減らす。（76行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の指定直前の面の幅、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの厳密な減少。

主宣言：`ordinalImageCard_comp_bottomMerge_of_no_one`

```lean
lemma ordinalImageCard_comp_bottomMerge_of_no_one {a b c : ℕ}
    (f : Fin a →o Fin b) (g : Fin b →o Fin c)
    (hf : ∀ i, (f i).val ≠ 1) (hg : ∀ i, (g i).val = i.val - 1) :
    ordinalImageCard (g.comp f) = ordinalImageCard f
```

主宣言：`ordinalMapVariation_comp_bottomMerge_of_no_one`

```lean
lemma ordinalMapVariation_comp_bottomMerge_of_no_one {a b c : ℕ}
    (f : Fin a →o Fin b) (g : Fin b →o Fin c) (hbc : c + 1 = b)
    (hf : ∀ i, (f i).val ≠ 1) (hg : ∀ i, (g i).val = i.val - 1) :
    ordinalMapVariation (g.comp f) + 1 = ordinalMapVariation f
```

#### [OrdinalConcatenation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalConcatenation.lean)

水平合成の有限順序射を、順序和と端点共有の貼り合わせの値で比較する。（140行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の残る混合水平結合則。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`ordinalAppend`

```lean
variable {m n p q r s : ℕ}

def ordinalAppend (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    Fin (m + p) →o Fin (n + q)
```

主宣言：`ordinalHom_hext`

```lean
variable {m n p q r s : ℕ}

lemma ordinalHom_hext {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (f : Fin a →o Fin b) (g : Fin c →o Fin d)
    (h : ∀ (i : Fin a) (j : Fin c), i.val = j.val → (f i).val = (g j).val) : HEq f g
```

#### [OrdinalConcatenationCancellation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalConcatenationCancellation.lean)

有限単調射の順序和と端点共有の表示から、二つの因子の射を回収する。（91行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Proposition 3.1.10・Remark 3.3.8、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な分解の一意性。

主宣言：`ordinalAppend_inj`

```lean
lemma ordinalAppend_inj {m n p q : ℕ}
    {f f' : Fin m →o Fin n} {g g' : Fin p →o Fin q}
    (h : ordinalAppend f g = ordinalAppend f' g') : f = f' ∧ g = g'
```

主宣言：`ordinalGlue_inj`

```lean
lemma ordinalGlue_inj {m n p q : ℕ}
    {f f' : Fin (m + 1) →o Fin (n + 1)} {g g' : Fin (p + 1) →o Fin (q + 1)}
    (hg : g 0 = 0) (hg' : g' 0 = 0)
    (h : ordinalGlue f g = ordinalGlue f' g') : f = f' ∧ g = g'
```

#### [OrdinalConcatenationLaws.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalConcatenationLaws.lean)

順序和と端点共有の貼り合わせの二つの全結合則を値で示す。（122行）

原典・利用箇所：HA Proposition 4.7.3.3、 Riehl–Verity Remark 3.3.8 の残る混合水平結合則。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`ordinalAppendNonempty`

```lean
variable {m n p q r s : ℕ}

def ordinalAppendNonempty (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin p →o Fin q) : Fin (m + p + 1) →o Fin (n + q + 1)
```

主宣言：`ordinalGlue_append_assoc`

```lean
variable {m n p q r s : ℕ}

lemma ordinalGlue_append_assoc (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (h : Fin r →o Fin s) :
    HEq (ordinalAppendNonempty (ordinalGlue f g) h)
      (ordinalGlue f (ordinalAppendNonempty g h))
```

#### [OrdinalCutComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalCutComparison.lean)

順序和の切れ目と端点共有の共有点を有限単調射の表示から回収する。（115行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、 HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の分解の一意性。

主宣言：`ordinalCut_ext`

```lean
lemma ordinalCut_ext {m : ℕ} (a b : Fin (m + 1))
    (h : ∀ i : Fin m, i.val < a.val ↔ i.val < b.val) : a = b
```

主宣言：`ordinalCut_of_glue_profile`

```lean
lemma ordinalCut_of_glue_profile {a b m n p q : ℕ}
    (ha : a = m + p + 1) (hb : b = n + q + 1)
    (H : Fin a →o Fin b) (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n)
    (h : HEq H (ordinalGlue f g)) (c : Fin a) (d : Fin b)
    (hc : c.val = m) (hd : d.val = n) : H c = d
```

#### [OrdinalGlueGalois.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalGlueGalois.lean)

区間表示の端点共有と、順序和のGalois随伴の射の比較。（129行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の混合水平合成の比較。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`ordinalGlue_interval_gc`

```lean
variable {m n p q : ℕ}

lemma ordinalGlue_interval_gc (f : Fin n →o Fin m)
    (g : Fin (p + 1) →o Fin (q + 1)) (hg : g 0 = 0) :
    GaloisConnection (ordinalGlue (ordinalIntervalMap f) g)
      (ordinalAppend (m := n) (n := m) (p := q + 1) (q := p + 1)
        f (ordinalRightAdjoint g hg))
```

主宣言：`ordinalIntervalMap_rightAdjoint`

```lean
variable {m n p q : ℕ}

lemma ordinalIntervalMap_rightAdjoint (g : Fin (p + 1) →o Fin (q + 1)) (hg : g 0 = 0) :
    ordinalIntervalMap (ordinalRightAdjoint g hg) = ordinalAdjoinTop g
```

#### [OrdinalGlueVariation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalGlueVariation.lean)

端点を共有する実単調射の貼り合わせの変化量は、左右の変化量の和。（126行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の実水平合成の幅、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実原子分解の幅の法則。

主宣言：`ordinalImageCard_glue`

```lean
lemma ordinalImageCard_glue {m n p q : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) (hg : g 0 = 0) :
    ordinalImageCard (ordinalGlue f g) + 1 = ordinalImageCard f + ordinalImageCard g
```

主宣言：`ordinalMapVariation_glue`

```lean
lemma ordinalMapVariation_glue {m n p q : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) (hg : g 0 = 0) :
    ordinalMapVariation (ordinalGlue f g) = ordinalMapVariation f + ordinalMapVariation g
```

#### [OrdinalImageCard.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalImageCard.lean)

有限単調射の実像の個数と、合成した実像の個数の上下を比較する。（104行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の幅の実順序表示、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの個数の照合。

主宣言：`ordinalImageCard`

```lean
def ordinalImageCard {m n : ℕ} (f : Fin m →o Fin n) : ℕ
```

主宣言：`ordinalImageCard_comp_of_surjective`

```lean
lemma ordinalImageCard_comp_of_surjective {a b c : ℕ} (f : Fin a →o Fin b)
    (g : Fin b →o Fin c) (hf : Function.Surjective f) :
    ordinalImageCard (g.comp f) = ordinalImageCard g
```

#### [OrdinalIntervalConcatenation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalIntervalConcatenation.lean)

区間表示が順序和を端点共有の射へ送ることを全射で示す。（131行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の混合水平合成の比較。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`ordinalAppend_adjoinTop`

```lean
variable {m n p q : ℕ}

lemma ordinalAppend_adjoinTop (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    ordinalAdjoinTop (ordinalAppend f g) =
      ordinalAppend (m := m) (n := n) (p := p + 1) (q := q + 1) f (ordinalAdjoinTop g)
```

主宣言：`simplexTensorHomOf_append`

```lean
variable {m n p q : ℕ}

lemma simplexTensorHomOf_append {X Y Z W : SimplexCategory} (f : X ⟶ Y) (g : Z ⟶ W) :
    (AugmentedSimplexCategory.tensorHomOf f g).toOrderHom =
      ordinalAppendNonempty f.toOrderHom g.toOrderHom
```

#### [OrdinalIntervalFunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalIntervalFunctor.lean)

増大単体圏の反対と、両端点保存の単体圏の実同値。（162行）

原典・利用箇所：HA Proposition 4.7.3.3 のwalking adjunctionの混合Hom同士の合成。 Riehl–Verity Remark 3.3.8 の区間表示、Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`simplexPreservesEndpoints`

```lean
def simplexPreservesEndpoints : MorphismProperty SimplexCategory
```

主宣言：`mixedTopBottomOrdinal`

```lean
def mixedTopBottomOrdinal :
    TopSimplexCategory × BottomSimplexCategory ⥤ AugmentedSimplexCategory
```

#### [OrdinalIntervalHom.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalIntervalHom.lean)

有限順序射と、両端点を保つ逆向きの区間の射の相互変換。（139行）

原典・利用箇所：HA Proposition 4.7.3.3 のwalking adjunctionの残る水平合成の区間表示、 Riehl–Verity Remark 3.3.8、Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`ordinalIntervalMap`

```lean
variable {m n k : ℕ}

def ordinalIntervalMap (f : Fin m →o Fin n) : Fin (n + 1) →o Fin (m + 1)
```

主宣言：`ordinalIntervalMap_comp`

```lean
variable {m n k : ℕ}

lemma ordinalIntervalMap_comp (f : Fin m →o Fin n) (g : Fin n →o Fin k) :
    ordinalIntervalMap (g.comp f) = (ordinalIntervalMap f).comp (ordinalIntervalMap g)
```

#### [OrdinalIntervalLaws.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalIntervalLaws.lean)

区間表示の逆関手を含む往復を、同じ骨格上の関手の等式にする。（182行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の walking adjunctionの水平合成の法則。Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`augmentedOrdinalOfCard_card`

```lean
@[simp] lemma augmentedOrdinalOfCard_card (X : AugmentedSimplexCategory) :
    augmentedOrdinalOfCard (augmentedOrdinalCard X) = X
```

主宣言：`mixedTopBottomOrdinal_obj`

```lean
lemma mixedTopBottomOrdinal_obj (X : TopSimplexCategory) (Y : BottomSimplexCategory) :
    mixedTopBottomOrdinal.obj (X, Y) =
      augmentedOrdinalOfCard (X.obj.len + Y.obj.len + 1)
```

#### [OrdinalMapVariation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalMapVariation.lean)

有限実辺の両端と像の個数から定まる変化量を、合成と実同型の検収に使う。（103行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の実filtrationの幅の表示、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実面と実親の幅の法則。

主宣言：`ordinalMapVariation`

```lean
def ordinalMapVariation {m n : ℕ} (f : Fin m →o Fin n) : ℕ
```

主宣言：`ordinalMapVariation_target_le`

```lean
lemma ordinalMapVariation_target_le {m n : ℕ} (f : Fin m →o Fin n) :
    n ≤ m + ordinalMapVariation f
```

#### [OrdinalMixedAdjoints.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalMixedAdjoints.lean)

既存の水平合成に使う有限Galois随伴と、端点共有の射を照合する。（92行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の混合水平合成。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`ordinalAppendNonempty_zero`

```lean
variable {m n p q : ℕ}

lemma ordinalAppendNonempty_zero (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin p →o Fin q) (hf : f 0 = 0) : ordinalAppendNonempty f g 0 = 0
```

主宣言：`ordinalRecoverMap_append_glue`

```lean
variable {m n p q : ℕ}

lemma ordinalRecoverMap_append_glue (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) (hg : g 0 = 0)
    (h₀ : ordinalAppendNonempty (ordinalLeftAdjoint f hf) (ordinalRightAdjoint g hg) 0 = 0)
    (h₁ : ordinalAppendNonempty (ordinalLeftAdjoint f hf) (ordinalRightAdjoint g hg)
      (Fin.last (n + q + 1)) = Fin.last (m + p + 1)) :
    ordinalRecoverMap
        (ordinalAppendNonempty (ordinalLeftAdjoint f hf) (ordinalRightAdjoint g hg)) h₀ h₁ =
      ordinalGlue f g
```

#### [OrdinalOrderTransport.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalOrderTransport.lean)

有限単調射の個数の等式に沿う輸送と、端点・恒等射・全合成との両立。（68行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10、 HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの実関手の型の輸送。

主宣言：`ordinalOrderHomTransport`

```lean
def ordinalOrderHomTransport {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (f : Fin a →o Fin b) : Fin c →o Fin d
```

主宣言：`ordinalOrderHomTransport_comp`

```lean
lemma ordinalOrderHomTransport_comp {a b c a' b' c' : ℕ}
    (ha : a = a') (hb : b = b') (hc : c = c') (f : Fin a →o Fin b) (g : Fin b →o Fin c) :
    ordinalOrderHomTransport ha hc (g.comp f) =
      (ordinalOrderHomTransport hb hc g).comp (ordinalOrderHomTransport ha hb f)
```

#### [OrdinalRestriction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalRestriction.lean)

有限単調射を、指定した区間の間の実単調射へ制限する。（110行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの水平因子の射。

主宣言：`ordinalSegmentInclusion`

```lean
def ordinalSegmentInclusion (m a r : ℕ) (h : a + r ≤ m) : Fin r →o Fin m
```

主宣言：`ordinalRestrict_comp`

```lean
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
```

#### [OrdinalSmallSourceInjective.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalSmallSourceInjective.lean)

二点以下からの実有限単調射が底を保ち併合しなければ単射となる。（42行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の先頭の実境界面、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの幅の保存。

主宣言：`ordinalInjective_of_le_two_bottom_no_one`

```lean
lemma ordinalInjective_of_le_two_bottom_no_one {a b : ℕ} (f : Fin a →o Fin b)
    (ha : a ≤ 2) (h0 : ∀ i, i.val = 0 → (f i).val = 0)
    (hno : ∀ i, i.val = 1 → (f i).val ≠ 0) : Function.Injective f
```

#### [OrdinalSumFunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalSumFunctor.lean)

walking adjunction の水平合成に使う非空有限順序集合の順序和。（106行）

原典・利用箇所：HA Proposition 4.7.3.3 の全拡張の添字、Riehl–Verity Remark 3.3.8 の水平合成。 Kerodon Remark 6.2.1.4（Tag 02EN）のホモトピー双圏へ移る前の合成。

主宣言：`simplexOrdinalSum`

```lean
def simplexOrdinalSum : SimplexCategory × SimplexCategory ⥤ SimplexCategory
```

主宣言：`simplexOrdinalSum_preservesTop`

```lean
lemma simplexOrdinalSum_preservesTop {x₁ x₂ y₁ y₂ : SimplexCategory}
    (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) (hg : simplexPreservesTop g) :
    simplexPreservesTop (tensorHomOf f g)
```

### 3. walking adjunctionの四Hom・水平合成・実豊穣圏

#### [IntervalInverseMapProfiles.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/IntervalInverseMapProfiles.lean)

実区間同値の逆と二つの混合合成の全射を有限区間の射で照合する。（111行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の全水平結合則。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`intervalOrderHom_functor_map_heq`

```lean
lemma intervalOrderHom_functor_map_heq {I : Type u} [Category.{v} I]
    {F G : I ⥤ IntervalSimplexCategory} (h : F = G) {X Y : I} (f : X ⟶ Y) :
    HEq (F.map f).hom.toOrderHom (G.map f).hom.toOrderHom
```

主宣言：`mixedTopBottomOrdinal_map_heq`

```lean
lemma mixedTopBottomOrdinal_map_heq {X₁ X₂ : TopSimplexCategory}
    {Y₁ Y₂ : BottomSimplexCategory} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    HEq (augmentedOrderHom
        (mixedTopBottomOrdinal.map (X := (X₁, Y₁)) (Y := (X₂, Y₂)) (f, g)))
      (ordinalGlue f.hom.toOrderHom g.hom.toOrderHom)
```

#### [IntervalMixedBalancing.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/IntervalMixedBalancing.lean)

二つの混合Homの間に自己Homを挟む水平合成の全結合則。（112行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 のwalking adjunction。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`mixedBottomTopOrdinal_representation`

```lean
lemma mixedBottomTopOrdinal_representation :
    mixedBottomTopOrdinal ⋙ ordinalIntervalRepresentation = bottomTopIntervalSum
```

主宣言：`mixedTopBottomFunctor_balance`

```lean
variable {I : Type u} [Category.{v} I]

lemma mixedTopBottomFunctor_balance (F : I ⥤ TopSimplexCategory)
    (G : I ⥤ AugmentedSimplexCategoryᵒᵖ) (H : I ⥤ BottomSimplexCategory) :
    ((F.prod' G ⋙ topOppositeOrdinalAction).prod' H ⋙ mixedTopBottomOrdinal) =
      (F.prod' (G.prod' H ⋙ bottomOppositeOrdinalAction) ⋙ mixedTopBottomOrdinal)
```

#### [OppositeOrdinalActionLaws.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OppositeOrdinalActionLaws.lean)

Galois双対で、反対側の自己Homの積と端点保存の作用の全結合則を移す。（139行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 のwalking adjunction。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`topToBottomOp_source_roundtrip`

```lean
lemma topToBottomOp_source_roundtrip :
    topToBottomOpEquivalence.functor ⋙ topToBottomOpEquivalence.inverse =
      𝟭 TopSimplexCategory
```

主宣言：`topOppositeOrdinalActionFunctor_assoc`

```lean
variable {I : Type u} [Category.{v} I]

lemma topOppositeOrdinalActionFunctor_assoc (F : I ⥤ TopSimplexCategory)
    (G H : I ⥤ AugmentedSimplexCategoryᵒᵖ) :
    ((F.prod' G ⋙ topOppositeOrdinalAction).prod' H ⋙ topOppositeOrdinalAction) =
      (F.prod' (G.prod' H ⋙ walkingAdjunctionHorizontal .minus .minus .minus) ⋙
        topOppositeOrdinalAction)
```

#### [OppositeOrdinalActionMapProfiles.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OppositeOrdinalActionMapProfiles.lean)

反対側の二つの水平作用の全射を端点共有の有限単調射として照合する。（72行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の全水平結合則。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`topOppositeOrdinalAction_map_heq`

```lean
lemma topOppositeOrdinalAction_map_heq {A B : AugmentedSimplexCategoryᵒᵖ}
    {X Y : TopSimplexCategory} (f : X ⟶ Y) (g : A ⟶ B) :
    HEq (topOppositeOrdinalAction.map (X := (X, A)) (Y := (Y, B)) (f, g)).hom.toOrderHom
      (ordinalGlue f.hom.toOrderHom (ordinalIntervalMap (augmentedOrderHom g.unop)))
```

主宣言：`bottomOppositeOrdinalAction_map_heq`

```lean
lemma bottomOppositeOrdinalAction_map_heq {A B : AugmentedSimplexCategoryᵒᵖ}
    {X Y : BottomSimplexCategory} (f : A ⟶ B) (g : X ⟶ Y) :
    HEq (bottomOppositeOrdinalAction.map (X := (A, X)) (Y := (B, Y)) (f, g)).hom.toOrderHom
      (ordinalGlue (ordinalIntervalMap (augmentedOrderHom f.unop)) g.hom.toOrderHom)
```

#### [OrdinalActionComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalActionComparison.lean)

端点保存の水平作用を増大単体圏の順序和と同じ射で比較する。（168行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の水平結合則。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`endpointAugmentedForget`

```lean
def endpointAugmentedForget (P : MorphismProperty SimplexCategory) [P.IsMultiplicative] :
    WideSubcategory P ⥤ AugmentedSimplexCategory
```

主宣言：`bottomOrdinalActionFunctor_assoc`

```lean
variable {I : Type u} [Category.{v} I]

lemma bottomOrdinalActionFunctor_assoc (F : I ⥤ BottomSimplexCategory)
    (G H : I ⥤ AugmentedSimplexCategory) :
    ((F.prod' G ⋙ bottomOrdinalAction).prod' H ⋙ bottomOrdinalAction) =
      (F.prod' (G.prod' H ⋙ tensor AugmentedSimplexCategory) ⋙ bottomOrdinalAction)
```

#### [OrdinalActionMapProfiles.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/OrdinalActionMapProfiles.lean)

水平作用の全射を順序和の有限単調射の表示へ移す。（113行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の全水平結合則。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`augmentedOrderHom_functor_map_heq`

```lean
lemma augmentedOrderHom_functor_map_heq {I : Type u} [Category.{v} I]
    {F G : I ⥤ AugmentedSimplexCategory} (h : F = G) {X Y : I} (f : X ⟶ Y) :
    HEq (augmentedOrderHom (F.map f)) (augmentedOrderHom (G.map f))
```

主宣言：`bottomOrdinalAction_map_heq`

```lean
lemma bottomOrdinalAction_map_heq {A B : AugmentedSimplexCategory}
    {X Y : BottomSimplexCategory} (f : X ⟶ Y) (g : A ⟶ B) :
    HEq (bottomOrdinalAction.map (X := (X, A)) (Y := (Y, B)) (f, g)).hom.toOrderHom
      (ordinalAppend f.hom.toOrderHom (augmentedOrderHom g))
```

#### [WalkingAdjunctionComposition.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionComposition.lean)

walking adjunctionの二対象・四つのHom圏・八つの水平合成を同時に指定する。（219行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8。 Kerodon Remark 6.2.1.4（Tag 02EN）。この段階では豊穣圏のinstanceを宣言しない。

主宣言：`WalkingAdjunctionPoint`

```lean
inductive WalkingAdjunctionPoint where
  /-- モナドが作用する側。 -/
  | plus
  /-- 自由対象が入る側。 -/
  | minus
  deriving DecidableEq
```

主宣言：`walkingAdjunctionHom`

```lean
def walkingAdjunctionHom : WalkingAdjunctionPoint → WalkingAdjunctionPoint → Type
```

主宣言：`walkingAdjunctionHorizontal`

```lean
def walkingAdjunctionHorizontal : (X Y Z : WalkingAdjunctionPoint) →
    walkingAdjunctionHom X Y × walkingAdjunctionHom Y Z ⥤ walkingAdjunctionHom X Z
```

#### [WalkingAdjunctionEndpointSizes.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionEndpointSizes.lean)

実全単体の正の長さと、始頂点・終頂点の有限点の個数の境界を照合する。（114行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の有限端点による表示。

主宣言：`walkingAdjunctionVertexLength_card`

```lean
lemma walkingAdjunctionVertexLength_card (X Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X Y) :
    walkingAdjunctionVertexLength X Y A + walkingAdjunctionTargetCorrection X +
      walkingAdjunctionTargetCorrection Y = 2 * walkingAdjunctionOrdinalCard X Y A
```

主宣言：`walkingAdjunctionSize_pos_of_endpoint_cards`

```lean
lemma walkingAdjunctionSize_pos_of_endpoint_cards {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hfirst : walkingAdjunctionOrdinalCard X Y (H.obj 0) =
      walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y)
    (hlast : walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 1) :
    0 < walkingAdjunctionLevelSize H
```

#### [WalkingAdjunctionEnrichment.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionEnrichment.lean)

二対象と全水平合成から実際の単体的豊穣walking adjunctionを構成する。（73行）

原典・利用箇所：HA §4.7.2–§4.7.3・Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8。 Kerodon Remark 6.2.1.4（Tag 02EN）への忘却前の全随伴の表示。

主宣言：`WalkingAdjunctionHomShape`

```lean
abbrev WalkingAdjunctionHomShape (X Y : WalkingAdjunctionPoint) : SSet.{u}
```

主宣言：`walkingAdjunctionComposition`

```lean
def walkingAdjunctionComposition (X Y Z : WalkingAdjunctionPoint) :
    WalkingAdjunctionHomShape.{u} X Y ⊗ WalkingAdjunctionHomShape.{u} Y Z ⟶
      WalkingAdjunctionHomShape.{u} X Z
```

主宣言：`walkingAdjunctionEnrichedCategory`

```lean
instance walkingAdjunctionEnrichedCategory : EnrichedCategory SSet.{u} WalkingAdjunctionPoint
```

#### [WalkingAdjunctionHorizontalFaithful.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionHorizontalFaithful.lean)

全八水平合成は、因子の対象を固定すれば射の等式を反映する。（149行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な語の一意性。

主宣言：`walkingAdjunctionOutgoingMap_zero`

```lean
lemma walkingAdjunctionOutgoingMap_zero {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) :
    walkingAdjunctionOutgoingMap (Y := Y) f 0 = 0
```

主宣言：`walkingAdjunctionHorizontal_functor_inj`

```lean
lemma walkingAdjunctionHorizontal_functor_inj {I : Type*} [Category I]
    (X Y Z : WalkingAdjunctionPoint)
    (F F' : I ⥤ walkingAdjunctionHom X Y) (G G' : I ⥤ walkingAdjunctionHom Y Z)
    (hF : ∀ i, F.obj i = F'.obj i) (hG : ∀ i, G.obj i = G'.obj i)
    (h : F.prod' G ⋙ walkingAdjunctionHorizontal X Y Z =
      F'.prod' G' ⋙ walkingAdjunctionHorizontal X Y Z) : F = F' ∧ G = G'
```

#### [WalkingAdjunctionMapRepresentation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionMapRepresentation.lean)

walking adjunctionの四Homの全射を共通の有限単調射の表示で照合する。（235行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の全水平結合則。 Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`walkingAdjunctionOrdinalCard`

```lean
def walkingAdjunctionOrdinalCard : (X Y : WalkingAdjunctionPoint) → walkingAdjunctionHom X Y → ℕ
```

主宣言：`walkingAdjunctionOrderHom_comp_minus`

```lean
lemma walkingAdjunctionOrderHom_comp_minus (X Z : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X .minus} {B B' : walkingAdjunctionHom .minus Z}
    (f : A ⟶ A') (g : B ⟶ B') :
    HEq (walkingAdjunctionOrderHom (X := X) (Y := Z)
        ((walkingAdjunctionHorizontal X .minus Z).map (X := (A, B)) (Y := (A', B')) (f, g)))
      (ordinalGlue (walkingAdjunctionIncomingMap (X := X) f)
        (walkingAdjunctionOutgoingMap (Y := Z) g))
```

#### [WalkingAdjunctionMixedAssociativity.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionMixedAssociativity.lean)

walking adjunctionの混合した三重水平合成の結合則を証明する。（202行）

原典・利用箇所：HA Proposition 4.7.3.3、 Riehl–Verity Remark 3.3.8、Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`ordinalAppend_heq`

```lean
lemma ordinalAppend_heq {m n p q m' n' p' q' : ℕ}
    (hm : m = m') (hn : n = n') (hp : p = p') (hq : q = q')
    {f : Fin (m) →o Fin (n)} {f' : Fin (m') →o Fin (n')}
    {g : Fin (p) →o Fin (q)} {g' : Fin (p') →o Fin (q')}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (ordinalAppend f g) (ordinalAppend f' g')
```

主宣言：`walkingAdjunctionHorizontal_assoc`

```lean
variable {I : Type*} [Category I]

lemma walkingAdjunctionHorizontal_assoc (W X Y Z : WalkingAdjunctionPoint)
    (F : I ⥤ walkingAdjunctionHom W X) (G : I ⥤ walkingAdjunctionHom X Y)
    (H : I ⥤ walkingAdjunctionHom Y Z) :
    ((F.prod' G ⋙ walkingAdjunctionHorizontal W X Y).prod' H ⋙
        walkingAdjunctionHorizontal W Y Z) =
      (F.prod' (G.prod' H ⋙ walkingAdjunctionHorizontal X Y Z) ⋙
        walkingAdjunctionHorizontal W X Z)
```

#### [WalkingAdjunctionOrderProfiles.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOrderProfiles.lean)

端点の条件を満たす有限単調射から、四Homの実際の射を回収する。（182行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの水平因子の構成。

主宣言：`WalkingAdjunctionOrderBoundary`

```lean
def WalkingAdjunctionOrderBoundary (X Y : WalkingAdjunctionPoint)
    {m n : ℕ} (f : Fin m →o Fin n) : Prop
```

主宣言：`walkingAdjunctionOrderProfileEquiv`

```lean
def walkingAdjunctionOrderProfileEquiv {X Y : WalkingAdjunctionPoint}
    (A B : walkingAdjunctionHom X Y) :
    (A ⟶ B) ≃ {f : Fin (walkingAdjunctionOrdinalCard X Y A) →o
      Fin (walkingAdjunctionOrdinalCard X Y B) // WalkingAdjunctionOrderBoundary X Y f}
```

#### [WalkingAdjunctionUnits.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionUnits.lean)

walking adjunctionの八つの水平合成の全単位則を実関手の等式で示す。（137行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の全随伴の添字。 Kerodon Remark 6.2.1.4（Tag 02EN）への忘却より前の単位則。

主宣言：`topOrdinalAction_leftUnit`

```lean
variable {I : Type u} [Category.{v} I]

lemma topOrdinalAction_leftUnit (F : I ⥤ TopSimplexCategory) :
    (((Functor.const I).obj WithInitial.star).prod' F ⋙ topOrdinalAction) = F
```

主宣言：`walkingAdjunctionHorizontal_rightUnit`

```lean
variable {I : Type u} [Category.{v} I]

lemma walkingAdjunctionHorizontal_rightUnit (X Y : WalkingAdjunctionPoint)
    (F : I ⥤ walkingAdjunctionHom X Y) :
    (F.prod' ((Functor.const I).obj (walkingAdjunctionIdentity Y)) ⋙
      walkingAdjunctionHorizontal X Y Y) = F
```

### 4. 零次元の生成射と自由な道・評価

#### [WalkingAdjunctionVertexEvaluation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionVertexEvaluation.lean)

指定した二つの射を、walking adjunctionの全頂点へ自由に延長する。（112行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Proposition 3.1.10・Theorem 4.3.9、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の指定F・Uの保持。

主宣言：`walkingAdjunctionVertexToPath`

```lean
def walkingAdjunctionVertexToPath : WalkingAdjunctionVertex ⥤ Paths WalkingAdjunctionPoint
```

主宣言：`walkingAdjunctionVertexEvaluation_right`

```lean
variable {D : Type u} [Category.{v} D]

lemma walkingAdjunctionVertexEvaluation_right (C E : D) (F : C ⟶ E) (U : E ⟶ C) :
    (walkingAdjunctionVertexEvaluation C E F U).map
      (X := ⟨.minus⟩) (Y := ⟨.plus⟩) (walkingAdjunctionGeneratorVertex .minus) = U
```

#### [WalkingAdjunctionVertexPaths.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionVertexPaths.lean)

零次元の実walking adjunctionの射は二つの生成射の道と一対一に対応する。（133行）

原典・利用箇所：HA Proposition 4.7.3.3、 Riehl–Verity Proposition 3.1.10・Theorem 4.3.9、Kerodon Remark 6.2.1.4（Tag 02EN）。

主宣言：`walkingAdjunctionGeneratingArrow`

```lean
def walkingAdjunctionGeneratingArrow (X : WalkingAdjunctionPoint) :
    X ⟶ walkingAdjunctionOther X
```

主宣言：`walkingAdjunctionPathFunctor_full`

```lean
instance walkingAdjunctionPathFunctor_full : walkingAdjunctionPathFunctor.Full
```

#### [WalkingAdjunctionVertices.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionVertices.lean)

walking adjunctionの頂点の圏と、二つの生成射からの自由な交互合成を照合する。（178行）

原典・利用箇所：HA Proposition 4.7.3.3、Riehl–Verity Proposition 3.1.10・Theorem 4.3.9。 Kerodon Remark 6.2.1.4（Tag 02EN）の前の全随伴の生成射。

主宣言：`WalkingAdjunctionVertex`

```lean
structure WalkingAdjunctionVertex where
  point : WalkingAdjunctionPoint
```

主宣言：`walkingAdjunctionPathFunctor_length`

```lean
lemma walkingAdjunctionPathFunctor_length {X Y : WalkingAdjunctionPoint} (p : Quiver.Path X Y) :
    walkingAdjunctionVertexLength X Y (walkingAdjunctionPathFunctor.map p) = p.length
```

### 5. 全次数の分解・切れ目・残余・区間

#### [WalkingAdjunctionBottomPointCut.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionBottomPointCut.lean)

実併合がないminus始点の全鎖から、最初の一点の実水平因子を切り出す。（106行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の始点plusの実因子の回収。

主宣言：`walkingAdjunctionBottomPointCut`

```lean
def walkingAdjunctionBottomPointCut {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0) : WalkingAdjunctionPlusCut H
```

主宣言：`walkingAdjunctionBottomPointFactorization_left_card`

```lean
lemma walkingAdjunctionBottomPointFactorization_left_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2)
    (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard .minus .plus
      ((walkingAdjunctionBottomPointFactorization H hno hlast).left.obj i) = 1
```

#### [WalkingAdjunctionCutBoundaryEquality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionCutBoundaryEquality.lean)

端点の指定された値を持つ切れ目を左右の外端の実切れ目と照合する。（83行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の境界。

主宣言：`WalkingAdjunctionPlusCut.eq_source_of_last_zero`

```lean
lemma WalkingAdjunctionPlusCut.eq_source_of_last_zero {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom .plus Y} (a : WalkingAdjunctionPlusCut H)
    (hz : (a.value (Fin.last n)).val = 0) : a = walkingAdjunctionSourceCut H
```

主宣言：`WalkingAdjunctionMinusCut.eq_target_of_first_top`

```lean
lemma WalkingAdjunctionMinusCut.eq_target_of_first_top {n : ℕ} {X : WalkingAdjunctionPoint}
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom X .minus} (a : WalkingAdjunctionMinusCut H)
    (ht : (a.value 0).val + 1 = walkingAdjunctionOrdinalCard X .minus (H.obj 0)) :
    a = walkingAdjunctionTargetCut H
```

#### [WalkingAdjunctionCutBounds.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionCutBounds.lean)

切れ目が実分解を与える外端の間の条件を有限端点の条件へ移す。（110行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の有限端点による表示。

主宣言：`walkingAdjunctionTargetCut_rank_card`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma walkingAdjunctionTargetCut_rank_card (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (i : Fin (n + 1)) :
    walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i +
        walkingAdjunctionTargetCorrection Y = 2 * walkingAdjunctionOrdinalCard X Y (H.obj i)
```

主宣言：`WalkingAdjunctionPlusCut.le_target`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma WalkingAdjunctionPlusCut.le_target (a : WalkingAdjunctionPlusCut H)
    (hr : Y = .minus → (a.value (Fin.last n)).val <
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n))) :
    ∀ i, walkingAdjunctionCutRank (M := .plus) a i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i
```

#### [WalkingAdjunctionCutChains.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionCutChains.lean)

全単体のplusの切れ目とminusの共有点を追跡し、全次数でそれらを比較する。（144行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な分解の一意性。

主宣言：`WalkingAdjunctionPlusCut`

```lean
structure WalkingAdjunctionPlusCut {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) where
  value (i : Fin (n + 1)) : Fin (walkingAdjunctionOrdinalCard X Y (F.obj i) + 1)
  naturality {i j : Fin (n + 1)} (h : i ≤ j) :
    ordinalIntervalMap (walkingAdjunctionOrderHom (F.map (homOfLE h))) (value j) = value i
```

主宣言：`walkingAdjunctionCut_mixed_total`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma walkingAdjunctionCut_mixed_total (a : WalkingAdjunctionPlusCut F)
    (b : WalkingAdjunctionMinusCut F) :
    (∀ i, (b.value i).val < (a.value i).val) ∨
      (∀ i, (a.value i).val ≤ (b.value i).val)
```

#### [WalkingAdjunctionCutComposition.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionCutComposition.lean)

隣り合う二つの切れ目の区間を水平合成すると全区間に戻る。（202行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実因子の合成則。

主宣言：`walkingAdjunctionCutFunctor_square_val`

```lean
variable {n : ℕ} {X Y M N P : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

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
```

主宣言：`walkingAdjunctionCutIntervalFunctor_comp`

```lean
variable {n : ℕ} {X Y M N P : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma walkingAdjunctionCutIntervalFunctor_comp
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (c : WalkingAdjunctionCut H P)
    (hab : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (hbc : ∀ i, walkingAdjunctionCutRank b i ≤ walkingAdjunctionCutRank c i) :
    (walkingAdjunctionCutIntervalFunctor a b hab).prod'
        (walkingAdjunctionCutIntervalFunctor b c hbc) ⋙ walkingAdjunctionHorizontal M N P =
      walkingAdjunctionCutIntervalFunctor a c (fun i => (hab i).trans (hbc i))
```

#### [WalkingAdjunctionCutEndpoints.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionCutEndpoints.lean)

plusの切れ目を終頂点、minusの共有点を始頂点から実際に構成する。（110行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の切れ目の表示。

主宣言：`WalkingAdjunctionPlusCut.ofLast`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)

def WalkingAdjunctionPlusCut.ofLast
    (t : Fin (walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) + 1)) :
    WalkingAdjunctionPlusCut H
```

主宣言：`WalkingAdjunctionMinusCut.firstEquiv`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)

def WalkingAdjunctionMinusCut.firstEquiv : WalkingAdjunctionMinusCut H ≃
    Fin (walkingAdjunctionOrdinalCard X Y (H.obj 0))
```

#### [WalkingAdjunctionCutFactorization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionCutFactorization.lean)

両外端の間の切れ目から左右の実因子を構成し、切れ目と分解の往復を証明する。（98行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の切れ目による実分解。

主宣言：`walkingAdjunctionFactorizationOfCut`

```lean
variable {n : ℕ} {X Y M : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

def walkingAdjunctionFactorizationOfCut (a : WalkingAdjunctionCut H M)
    (hl : ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank a i)
    (hr : ∀ i, walkingAdjunctionCutRank a i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i) :
    WalkingAdjunctionFactorization H
```

主宣言：`WalkingAdjunctionFactorization.ofCut_roundtrip`

```lean
variable {n : ℕ} {X Y M : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma WalkingAdjunctionFactorization.ofCut_roundtrip (a : WalkingAdjunctionFactorization H) :
    walkingAdjunctionFactorizationOfCut a.cut a.sourceCut_le a.le_targetCut = a
```

#### [WalkingAdjunctionCutFibers.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionCutFibers.lean)

再添字付けの同じ頂点へ写る点で、水平分解の切れ目と左右の長さを照合する。（108行）

原典・利用箇所：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の退化と原子性の両立。

主宣言：`walkingAdjunctionOrderHom_eqToHom_heq`

```lean
lemma walkingAdjunctionOrderHom_eqToHom_heq {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (h : A = B) :
    HEq (walkingAdjunctionOrderHom (eqToHom h))
      (OrderHom.id : Fin (walkingAdjunctionOrdinalCard X Y A) →o
        Fin (walkingAdjunctionOrdinalCard X Y A))
```

主宣言：`WalkingAdjunctionFactorization.right_length_eq_of_reindex_fiber`

```lean
lemma WalkingAdjunctionFactorization.right_length_eq_of_reindex_fiber {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (a : WalkingAdjunctionFactorization (P ⋙ F))
    {i j : Fin (m + 1)} (he : P.obj i = P.obj j) :
    walkingAdjunctionVertexLength a.middle Y (a.right.obj i) =
      walkingAdjunctionVertexLength a.middle Y (a.right.obj j)
```

#### [WalkingAdjunctionCutFunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionCutFunctor.lean)

比較された任意の二つの切れ目の間に元の四Homの実関手を作る。（127行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前のcoherentな随伴の入力。

主宣言：`walkingAdjunctionCutIntervalObject`

```lean
variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

def walkingAdjunctionCutIntervalObject
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1)) : walkingAdjunctionHom M N
```

主宣言：`walkingAdjunctionCutIntervalFunctor`

```lean
variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

def walkingAdjunctionCutIntervalFunctor
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) :
    Fin (n + 1) ⥤ walkingAdjunctionHom M N
```

#### [WalkingAdjunctionCutInclusions.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionCutInclusions.lean)

任意の比較された切れ目の間の実関手を、元の全単体の区間へ入れる。（89行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の区間の照合。

主宣言：`walkingAdjunctionCutFunctorInclusion`

```lean
variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

def walkingAdjunctionCutFunctorInclusion
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    (i : Fin (n + 1)) :
    Fin (walkingAdjunctionOrdinalCard M N ((walkingAdjunctionCutIntervalFunctor a b h).obj i)) →o
      Fin (walkingAdjunctionOrdinalCard X Y (H.obj i))
```

主宣言：`walkingAdjunctionCutFunctor_square`

```lean
variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma walkingAdjunctionCutFunctor_square
    (a : WalkingAdjunctionCut H M) (b : WalkingAdjunctionCut H N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    (walkingAdjunctionCutFunctorInclusion a b h j).comp
        (walkingAdjunctionOrderHom ((walkingAdjunctionCutIntervalFunctor a b h).map f)) =
      (walkingAdjunctionOrderHom (H.map f)).comp
        (walkingAdjunctionCutFunctorInclusion a b h i)
```

#### [WalkingAdjunctionCutIntervals.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionCutIntervals.lean)

二つの比較済みの切れ目の間へ、実単体の有限単調射を制限する。（154行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの水平因子の全射。

主宣言：`walkingAdjunctionCutIntervalSize`

```lean
variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

def walkingAdjunctionCutIntervalSize (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N) (i : Fin (n + 1)) : ℕ
```

主宣言：`walkingAdjunctionCutIntervalMap`

```lean
variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

def walkingAdjunctionCutIntervalMap (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    Fin (walkingAdjunctionCutIntervalSize a b i) →o
      Fin (walkingAdjunctionCutIntervalSize a b j)
```

#### [WalkingAdjunctionCutRank.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionCutRank.lean)

plusの切れ目とminusの共有点を一つの順位で比較し、同じ単体への輸送と両立させる。（113行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、 HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の分解の一意性。

主宣言：`WalkingAdjunctionCut`

```lean
def WalkingAdjunctionCut {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) : WalkingAdjunctionPoint → Type
```

主宣言：`walkingAdjunctionCutRank_total`

```lean
variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {F G : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma walkingAdjunctionCutRank_total (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N) :
    (∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) ∨
      (∀ i, walkingAdjunctionCutRank b i ≤ walkingAdjunctionCutRank a i)
```

#### [WalkingAdjunctionFactorCuts.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionFactorCuts.lean)

実際の全水平分解から、比較可能な切れ目の追跡データを構成する。（80行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の分解の一意性。

主宣言：`walkingAdjunctionPlusFactorCut`

```lean
def walkingAdjunctionPlusFactorCut {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X .plus)
    (G : Fin (n + 1) ⥤ walkingAdjunctionHom .plus Y) :
    WalkingAdjunctionPlusCut (F.prod' G ⋙ walkingAdjunctionHorizontal X .plus Y)
```

主宣言：`walkingAdjunctionMinusFactorCut`

```lean
def walkingAdjunctionMinusFactorCut {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X .minus)
    (G : Fin (n + 1) ⥤ walkingAdjunctionHom .minus Y) :
    WalkingAdjunctionMinusCut (F.prod' G ⋙ walkingAdjunctionHorizontal X .minus Y)
```

#### [WalkingAdjunctionFactorOrder.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionFactorOrder.lean)

同じ全単体の水平分解を全頂点の左因子の長さで比較する。（158行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な分解の一意性。

主宣言：`WalkingAdjunctionFactorization`

```lean
structure WalkingAdjunctionFactorization {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) where
  middle : WalkingAdjunctionPoint
  left : Fin (n + 1) ⥤ walkingAdjunctionHom X middle
  right : Fin (n + 1) ⥤ walkingAdjunctionHom middle Y
  fac : left.prod' right ⋙ walkingAdjunctionHorizontal X middle Y = H

variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}
```

主宣言：`WalkingAdjunctionFactorization.ext_prefix_length`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma WalkingAdjunctionFactorization.ext_prefix_length (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) =
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) : a = b
```

#### [WalkingAdjunctionIntervalLaws.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionIntervalLaws.lean)

二つの切れ目の間の射が、端点・恒等射・全合成を保持することを証明する。（183行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、 HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの実関手。

主宣言：`walkingAdjunctionCutIntervalInclusion`

```lean
variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

def walkingAdjunctionCutIntervalInclusion (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) (i : Fin (n + 1)) :
    Fin (walkingAdjunctionCutIntervalSize a b i) →o
      Fin (walkingAdjunctionOrdinalCard X Y (F.obj i))
```

主宣言：`walkingAdjunctionCutIntervalMap_boundary`

```lean
variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma walkingAdjunctionCutIntervalMap_boundary (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    WalkingAdjunctionOrderBoundary M N (walkingAdjunctionCutIntervalMap a b h hij)
```

#### [WalkingAdjunctionLevels.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionLevels.lean)

全次元のwalking adjunctionの射の圏と、その分解で使う有限の長さを構成する。（116行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Theorem 4.3.9、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の全coherenceの構成。

主宣言：`WalkingAdjunctionLevel`

```lean
structure WalkingAdjunctionLevel (n : ℕ) where
  point : WalkingAdjunctionPoint
```

主宣言：`walkingAdjunctionLevelSize_zero_eq_id`

```lean
lemma walkingAdjunctionLevelSize_zero_eq_id {n : ℕ} {X : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X X) (h : walkingAdjunctionLevelSize F = 0) :
    F = (Functor.const _).obj (walkingAdjunctionIdentity X)
```

#### [WalkingAdjunctionOuterCuts.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOuterCuts.lean)

全単体の左右の単位分解から外端の切れ目を取り出す。（134行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の区間の境界。

主宣言：`walkingAdjunctionSourceFactorization`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}

def walkingAdjunctionSourceFactorization (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionFactorization H
```

主宣言：`WalkingAdjunctionFactorization.le_targetCut`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}

lemma WalkingAdjunctionFactorization.le_targetCut
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y} (a : WalkingAdjunctionFactorization H) :
    ∀ i, walkingAdjunctionCutRank a.cut i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i
```

#### [WalkingAdjunctionPrefixInclusions.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPrefixInclusions.lean)

実水平分解の左因子を先頭区間として全体へ入れ、その全射の可換性を証明する。（121行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、 HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの因子の照合。

主宣言：`WalkingAdjunctionFactorization.prefixInclusion`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

def WalkingAdjunctionFactorization.prefixInclusion (a : WalkingAdjunctionFactorization H)
    (i : Fin (n + 1)) :
    Fin (walkingAdjunctionOrdinalCard X a.middle (a.left.obj i)) →o
      Fin (walkingAdjunctionOrdinalCard X Y (H.obj i))
```

主宣言：`WalkingAdjunctionFactorization.prefix_square`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma WalkingAdjunctionFactorization.prefix_square (a : WalkingAdjunctionFactorization H)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    (a.prefixInclusion j).comp (walkingAdjunctionOrderHom (a.left.map f)) =
      (walkingAdjunctionOrderHom (H.map f)).comp (a.prefixInclusion i)
```

#### [WalkingAdjunctionResidualFactorization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionResidualFactorization.lean)

残りの実関手と元の因子の水平合成が、元の分解へ全関手として戻ることを証明する。（211行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、 HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な語の一意性。

主宣言：`WalkingAdjunctionFactorization.residual_prefix`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma WalkingAdjunctionFactorization.residual_prefix (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) :
    a.left.prod' (a.residualFunctor b h) ⋙ walkingAdjunctionHorizontal X a.middle b.middle =
      b.left
```

主宣言：`WalkingAdjunctionFactorization.exists_refinement`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma WalkingAdjunctionFactorization.exists_refinement (a b : WalkingAdjunctionFactorization H) :
    (∃ T : Fin (n + 1) ⥤ walkingAdjunctionHom a.middle b.middle,
      a.left.prod' T ⋙ walkingAdjunctionHorizontal X a.middle b.middle = b.left ∧
      T.prod' b.right ⋙ walkingAdjunctionHorizontal a.middle b.middle Y = a.right) ∨
    (∃ T : Fin (n + 1) ⥤ walkingAdjunctionHom b.middle a.middle,
      b.left.prod' T ⋙ walkingAdjunctionHorizontal X b.middle a.middle = a.left ∧
      T.prod' a.right ⋙ walkingAdjunctionHorizontal b.middle a.middle Y = b.right)
```

#### [WalkingAdjunctionResidualFunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionResidualFunctor.lean)

同じ全単体の二つの水平分解の間の残りの実関手を構成する。（112行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な分解の一意性。

主宣言：`WalkingAdjunctionFactorization.residualMap`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

def WalkingAdjunctionFactorization.residualMap (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    walkingAdjunctionResidualObject (a.left.obj i) (b.left.obj i) (h i) ⟶
      walkingAdjunctionResidualObject (a.left.obj j) (b.left.obj j) (h j)
```

主宣言：`WalkingAdjunctionFactorization.residualFunctor`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

def WalkingAdjunctionFactorization.residualFunctor (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) :
    Fin (n + 1) ⥤ walkingAdjunctionHom a.middle b.middle
```

#### [WalkingAdjunctionResidualInclusions.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionResidualInclusions.lean)

残りの実関手を元の全単体の区間へ入れ、その全射の可換性を証明する。（92行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの因子の合成の照合。

主宣言：`WalkingAdjunctionFactorization.residualInclusion`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

def WalkingAdjunctionFactorization.residualInclusion (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i)) (i : Fin (n + 1)) :
    Fin (walkingAdjunctionOrdinalCard a.middle b.middle ((a.residualFunctor b h).obj i)) →o
      Fin (walkingAdjunctionOrdinalCard X Y (H.obj i))
```

主宣言：`WalkingAdjunctionFactorization.residual_square`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma WalkingAdjunctionFactorization.residual_square (a b : WalkingAdjunctionFactorization H)
    (h : ∀ i, walkingAdjunctionVertexLength X a.middle (a.left.obj i) ≤
      walkingAdjunctionVertexLength X b.middle (b.left.obj i))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    (a.residualInclusion b h j).comp (walkingAdjunctionOrderHom ((a.residualFunctor b h).map f)) =
      (walkingAdjunctionOrderHom (H.map f)).comp (a.residualInclusion b h i)
```

#### [WalkingAdjunctionResidualObjects.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionResidualObjects.lean)

二つの左因子の長さの比較から、残りの水平因子の各頂点を実際に作る。（127行）

原典・利用箇所：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の分解の一意性。

主宣言：`walkingAdjunctionObjectOfWeight`

```lean
def walkingAdjunctionObjectOfWeight (X Y : WalkingAdjunctionPoint) (w : ℕ)
    (_h : X = .minus → Y = .plus → 0 < w) : walkingAdjunctionHom X Y
```

主宣言：`walkingAdjunctionResidualObject_suffix`

```lean
lemma walkingAdjunctionResidualObject_suffix {X M N Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (C : walkingAdjunctionHom M Y) (D : walkingAdjunctionHom N Y)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B)
    (hc : (walkingAdjunctionHorizontal X M Y).obj (A, C) =
      (walkingAdjunctionHorizontal X N Y).obj (B, D)) :
    (walkingAdjunctionHorizontal M N Y).obj (walkingAdjunctionResidualObject A B h, D) = C
```

#### [WalkingAdjunctionWholeInterval.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionWholeInterval.lean)

左右の外端の間の実区間関手は元の全単体そのもの。（75行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の元の単体との比較。

主宣言：`walkingAdjunctionWholeInterval_obj`

```lean
lemma walkingAdjunctionWholeInterval_obj {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (i : Fin (n + 1)) :
    (walkingAdjunctionCutIntervalFunctor (walkingAdjunctionSourceCut H)
      (walkingAdjunctionTargetCut H) (walkingAdjunctionOuterCuts_le H)).obj i = H.obj i
```

主宣言：`walkingAdjunctionWholeInterval`

```lean
lemma walkingAdjunctionWholeInterval {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    walkingAdjunctionCutIntervalFunctor (walkingAdjunctionSourceCut H)
      (walkingAdjunctionTargetCut H) (walkingAdjunctionOuterCuts_le H) = H
```

### 6. 原子的な語・自由な道・相互逆な表示

#### [WalkingAdjunctionAtomicBoundaries.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicBoundaries.lean)

原子的な全単体の分解を左右の単位分解の二つに照合する。（90行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の切れ目の判定。

主宣言：`WalkingAdjunctionFactorization.left_size_zero_iff`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma WalkingAdjunctionFactorization.left_size_zero_iff
    (a : WalkingAdjunctionFactorization H) : walkingAdjunctionLevelSize a.left = 0 ↔
      a = walkingAdjunctionSourceFactorization H
```

主宣言：`walkingAdjunctionLevelIsAtomic_iff_boundary_factorizations`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma walkingAdjunctionLevelIsAtomic_iff_boundary_factorizations
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ↔
      0 < walkingAdjunctionLevelSize H ∧ ∀ a : WalkingAdjunctionFactorization H,
        a = walkingAdjunctionSourceFactorization H ∨
          a = walkingAdjunctionTargetFactorization H
```

#### [WalkingAdjunctionAtomicCancellation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicCancellation.lean)

同じ全単体の原子的な左因子と、その残りは一意である。（95行）

原典・利用箇所：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な語の一意性。

主宣言：`WalkingAdjunctionFactorization.eq_of_atomic_refinement`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma WalkingAdjunctionFactorization.eq_of_atomic_refinement
    (a b : WalkingAdjunctionFactorization H)
    (T : Fin (n + 1) ⥤ walkingAdjunctionHom a.middle b.middle)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨a.middle⟩) a.left)
    (hb : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨b.middle⟩) b.left)
    (hp : a.left.prod' T ⋙ walkingAdjunctionHorizontal X a.middle b.middle = b.left)
    (hq : T.prod' b.right ⋙ walkingAdjunctionHorizontal a.middle b.middle Y = a.right) : a = b
```

主宣言：`walkingAdjunctionAtomicLeftCancellation`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

lemma walkingAdjunctionAtomicLeftCancellation {A B C D : WalkingAdjunctionLevel n}
    (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D)
    (hf : WalkingAdjunctionLevelIsAtomic f) (hg : WalkingAdjunctionLevelIsAtomic g)
    (h : f ≫ u = g ≫ v) : ∃ _hBC : B = C, HEq f g ∧ HEq u v
```

#### [WalkingAdjunctionAtomicCuts.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicCuts.lean)

原子性を、両外端の間の切れ目が二つの外端だけである条件へ移す。（84行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の有限表示。

主宣言：`walkingAdjunctionLevelIsAtomic_iff_boundary_cuts`

```lean
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

#### [WalkingAdjunctionAtomicFaithful.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicFaithful.lean)

全次数の原子的な射の自由な道と実全射の比較は忠実である。（147行）

原典・利用箇所：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の全随伴の自由な生成。

主宣言：`walkingAdjunctionAtomicPathFunctor_map_injective`

```lean
variable {n : ℕ}

lemma walkingAdjunctionAtomicPathFunctor_map_injective
    {A B : WalkingAdjunctionAtomicVertex n} (p q : Quiver.Path A B)
    (h : (walkingAdjunctionAtomicPathFunctor n).map p =
      (walkingAdjunctionAtomicPathFunctor n).map q) : p = q
```

主宣言：`walkingAdjunctionAtomicPathFunctor_faithful`

```lean
variable {n : ℕ}

instance walkingAdjunctionAtomicPathFunctor_faithful (n : ℕ) :
    (walkingAdjunctionAtomicPathFunctor n).Faithful
```

#### [WalkingAdjunctionAtomicPaths.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicPaths.lean)

全次数の原子的な射のquiverと、自由な道から実射への全射的な比較を構成する。（84行）

原典・利用箇所：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の全coherenceの構成。

主宣言：`WalkingAdjunctionAtomicVertex`

```lean
structure WalkingAdjunctionAtomicVertex (n : ℕ) where
  level : WalkingAdjunctionLevel n
```

主宣言：`walkingAdjunctionAtomicPathFunctor`

```lean
def walkingAdjunctionAtomicPathFunctor (n : ℕ) :
    Paths (WalkingAdjunctionAtomicVertex n) ⥤ WalkingAdjunctionLevel n
```

主宣言：`walkingAdjunctionAtomicPathFunctor_full`

```lean
instance walkingAdjunctionAtomicPathFunctor_full (n : ℕ) :
    (walkingAdjunctionAtomicPathFunctor n).Full
```

#### [WalkingAdjunctionAtomicPresentation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicPresentation.lean)

原子的な自由な道と各次数の実全射の圏の相互逆な実関手を構成する。（81行）

原典・利用箇所：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の全随伴の各次数の自由な表示。

主宣言：`walkingAdjunctionAtomicInverse`

```lean
def walkingAdjunctionAtomicInverse (n : ℕ) :
    WalkingAdjunctionLevel n ⥤ Paths (WalkingAdjunctionAtomicVertex n)
```

主宣言：`walkingAdjunctionAtomic_path_roundtrip`

```lean
lemma walkingAdjunctionAtomic_path_roundtrip (n : ℕ) :
    walkingAdjunctionAtomicPathFunctor n ⋙ walkingAdjunctionAtomicInverse n =
      𝟭 (Paths (WalkingAdjunctionAtomicVertex n))
```

主宣言：`walkingAdjunctionAtomic_level_roundtrip`

```lean
lemma walkingAdjunctionAtomic_level_roundtrip (n : ℕ) :
    walkingAdjunctionAtomicInverse n ⋙ walkingAdjunctionAtomicPathFunctor n =
      𝟭 (WalkingAdjunctionLevel n)
```

#### [WalkingAdjunctionAtomicWords.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicWords.lean)

全次数の射を有限個の原子的な射の語へ分解する。（84行）

原典・利用箇所：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の全coherenceの構成。

主宣言：`WalkingAdjunctionLevelIsAtomic`

```lean
def WalkingAdjunctionLevelIsAtomic {n : ℕ} {X Y : WalkingAdjunctionLevel n} (F : X ⟶ Y) : Prop
```

主宣言：`WalkingAdjunctionAtomicWord`

```lean
inductive WalkingAdjunctionAtomicWord (n : ℕ) :
    {X Y : WalkingAdjunctionLevel n} → (X ⟶ Y) → Type
  | nil (X : WalkingAdjunctionLevel n) : WalkingAdjunctionAtomicWord n (𝟙 X)
  | atom {X Y : WalkingAdjunctionLevel n} (F : X ⟶ Y) (h : WalkingAdjunctionLevelIsAtomic F) :
      WalkingAdjunctionAtomicWord n F
  | comp {X Y Z : WalkingAdjunctionLevel n} {F : X ⟶ Y} {G : Y ⟶ Z}
      (a : WalkingAdjunctionAtomicWord n F) (b : WalkingAdjunctionAtomicWord n G) :
      WalkingAdjunctionAtomicWord n (F ≫ G)
```

主宣言：`walkingAdjunctionAtomicWord_nonempty`

```lean
lemma walkingAdjunctionAtomicWord_nonempty {n : ℕ} {X Y : WalkingAdjunctionLevel n}
    (F : X ⟶ Y) : Nonempty (WalkingAdjunctionAtomicWord n F)
```

### 7. 有限鎖の挿入・細分・面・非退化性の一般補題

#### [ComposableArrowAppend.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowAppend.lean)

実有限鎖の終点へ一つの実射を挿入し、一つ高次の全実関手を構成する。（84行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の始点plusの実親、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の終端の実射の挿入。

主宣言：`composableArrowAppendData`

```lean
variable {C : Type u} [Category.{v} C]

def composableArrowAppendData :
    ∀ (n : ℕ) (F : ComposableArrows C n) (B : C) (_f : F.obj (Fin.last n) ⟶ B),
      {G : ComposableArrows C (n + 1) // G.obj 0 = F.obj 0 ∧
        G.obj (Fin.last (n + 1)) = B}
```

主宣言：`composableArrowAppend_succ`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrowAppend_succ {n : ℕ} (F : ComposableArrows C (n + 1)) (B : C)
    (f : F.obj (Fin.last (n + 1)) ⟶ B) :
    composableArrowAppend F B f = (composableArrowAppend F.δ₀ B f).precomp
      (F.map' 0 1 ≫ eqToHom (composableArrowAppend_first F.δ₀ B f).symm)
```

#### [ComposableArrowAppendFaces.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowAppendFaces.lean)

実終端射を挿入した実全鎖の最後の面は元の全鎖。（68行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の最後の深さでの実親、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実指定面の照合。

主宣言：`composableArrowAppend_face_last`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrowAppend_face_last :
    ∀ (n : ℕ) (F : ComposableArrows C n) (B : C) (f : F.obj (Fin.last n) ⟶ B),
      finiteChainFace (composableArrowAppend F B f) (Fin.last (n + 1)) = F
```

#### [ComposableArrowAppendPositions.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowAppendPositions.lean)

終端へ挿入した実射と、それ以前の全実対象・辺を元の実鎖から回収する。（79行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の最後の深さの親、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の非退化性の検収。

主宣言：`composableArrowAppend_last_edge`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrowAppend_last_edge :
    ∀ (n : ℕ) (F : ComposableArrows C n) (B : C) (f : F.obj (Fin.last n) ⟶ B),
      HEq ((composableArrowAppend F B f).map
        (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) f
```

主宣言：`composableArrowAppend_before_edge`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrowAppend_before_edge {n : ℕ} (F : ComposableArrows C (n + 1)) (B : C)
    (f : F.obj (Fin.last (n + 1)) ⟶ B) (j : Fin (n + 1)) :
    HEq ((composableArrowAppend F B f).map
      (homOfLE (Fin.castSucc_le_succ j.castSucc)))
      (F.map (homOfLE (Fin.castSucc_le_succ j)))
```

#### [ComposableArrowEpiFaceRigidity.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowEpiFaceRigidity.lean)

挿入左辺がepiなら、指定面・挿入対象・左辺だけで実親を回収する。（81行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の実親の一意性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分の照合。

主宣言：`rightFactor_heq_of_epi_comp_heq`

```lean
variable {C : Type u} [Category.{v} C]

lemma rightFactor_heq_of_epi_comp_heq {A B D A' B' D' : C}
    (hA : A = A') (hB : B = B') (hD : D = D')
    (q : A ⟶ B) (q' : A' ⟶ B') (g : B ⟶ D) (g' : B' ⟶ D')
    [Epi q] (hq : HEq q q') (hc : HEq (q ≫ g) (q' ≫ g')) : HEq g g'
```

主宣言：`composableArrow_eq_of_face_and_epi_left`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrow_eq_of_face_and_epi_left {n : ℕ}
    {F G : ComposableArrows C (n + 2)} (k : Fin (n + 1))
    (hface : finiteChainFace F k.succ.castSucc = finiteChainFace G k.succ.castSucc)
    (hmid : F.obj k.succ.castSucc = G.obj k.succ.castSucc)
    (hleft : HEq (F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))
      (G.map (homOfLE (Fin.castSucc_le_succ k.castSucc))))
    [Epi (F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))] : F = G
```

#### [ComposableArrowFaceRigidity.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowFaceRigidity.lean)

同じ指定面を持つ実鎖の全対象と、挿入頂点に接する二辺から元の全関手を回収する。（92行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の実親の一意性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分の照合。

主宣言：`finiteChainFace_obj_eq`

```lean
variable {C : Type u} [Category.{v} C]

lemma finiteChainFace_obj_eq {n : ℕ} {F G : ComposableArrows C (n + 1)}
    (p : Fin (n + 2)) (h : finiteChainFace F p = finiteChainFace G p)
    (i : Fin (n + 2)) (hi : i ≠ p) : F.obj i = G.obj i
```

主宣言：`composableArrow_eq_of_face_and_incident_edges`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrow_eq_of_face_and_incident_edges {n : ℕ}
    {F G : ComposableArrows C (n + 2)} (k : Fin (n + 1))
    (hface : finiteChainFace F k.succ.castSucc = finiteChainFace G k.succ.castSucc)
    (hmid : F.obj k.succ.castSucc = G.obj k.succ.castSucc)
    (hleft : HEq (F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))
      (G.map (homOfLE (Fin.castSucc_le_succ k.castSucc))))
    (hright : HEq (F.map (homOfLE (Fin.castSucc_le_succ k.succ)))
      (G.map (homOfLE (Fin.castSucc_le_succ k.succ)))) : F = G
```

#### [ComposableArrowFaces.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowFaces.lean)

有限実鎖の面を実順序関手で構成し、尾部・先頭の挿入との合成則を照合する。（106行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の指定面、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分と面の照合。

主宣言：`finiteChainFaceIndex`

```lean
def finiteChainFaceIndex {n : ℕ} (k : Fin (n + 2)) : Fin (n + 1) ⥤ Fin (n + 2)
```

主宣言：`finiteChainFace_precomp_pair`

```lean
variable {C : Type u} [Category.{v} C]

lemma finiteChainFace_precomp_pair {n : ℕ} (F : ComposableArrows C n)
    {A B : C} (q : A ⟶ B) (g : B ⟶ F.left) :
    finiteChainFace ((F.precomp g).precomp q) (1 : Fin (n + 3)) = F.precomp (q ≫ g)
```

#### [ComposableArrowInnerFace.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowInnerFace.lean)

内側の実面の全対象と辺を、元の鎖と指定した二辺の合成から回収する。（118行）

原典・利用箇所：Riehl–Verity Lemma 4.1.3の実親の逆方向、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の内側の実面の検収。

主宣言：`finiteChainFace_map_heq_of_indices`

```lean
variable {C : Type u} [Category.{v} C]

lemma finiteChainFace_map_heq_of_indices {n : ℕ} (F : ComposableArrows C (n + 1))
    (p : Fin (n + 2)) {a b : Fin (n + 1)} {a' b' : Fin (n + 2)}
    (ha : p.succAbove a = a') (hb : p.succAbove b = b') (hab : a ≤ b) (hab' : a' ≤ b') :
    HEq ((finiteChainFace F p).map (homOfLE hab)) (F.map (homOfLE hab'))
```

主宣言：`finiteChainFace_inner_last`

```lean
variable {C : Type u} [Category.{v} C]

lemma finiteChainFace_inner_last {n : ℕ} (F : ComposableArrows C (n + 2)) (k : Fin (n + 1)) :
    (finiteChainFace F k.succ.castSucc).obj (Fin.last (n + 1)) = F.obj (Fin.last (n + 2))
```

#### [ComposableArrowLastFace.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowLastFace.lean)

最後の実面は、最後の頂点より前の実対象と実射をそのまま回収する。（55行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実最終面の照合。

主宣言：`finiteChainFaceIndex_last`

```lean
variable {C : Type u} [Category.{v} C]

lemma finiteChainFaceIndex_last (n : ℕ) :
    finiteChainFaceIndex (Fin.last (n + 1)) = Fin.castSuccFunctor (n + 1)
```

主宣言：`finiteChainFace_last_edge`

```lean
variable {C : Type u} [Category.{v} C]

lemma finiteChainFace_last_edge {n : ℕ} (F : ComposableArrows C (n + 2)) (j : Fin (n + 1)) :
    HEq ((finiteChainFace F (Fin.last (n + 2))).map
      (homOfLE (Fin.castSucc_le_succ j)))
      (F.map (homOfLE (Fin.castSucc_le_succ j.castSucc)))
```

#### [ComposableArrowRefinement.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowRefinement.lean)

実有限鎖の指定した一辺へ二つの実射と中間対象を挿入する。（79行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の実全単体、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実射の細分の挿入。

主宣言：`composableArrowRefinementData`

```lean
variable {C : Type u} [Category.{v} C]

def composableArrowRefinementData :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (_q : F.obj k.castSucc ⟶ B) (_g : B ⟶ F.obj k.succ),
      {G : ComposableArrows C (n + 2) //
        G.obj 0 = F.obj 0 ∧ G.obj (Fin.last (n + 2)) = F.obj (Fin.last (n + 1))}
```

主宣言：`composableArrowRefinement_last`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrowRefinement_last {n : ℕ} (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
    (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ) :
    (composableArrowRefinement F k B q g).obj (Fin.last (n + 2)) = F.obj (Fin.last (n + 1))
```

#### [ComposableArrowRefinementFaces.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowRefinementFaces.lean)

実細分の挿入した頂点を除く指定面は、元の実全鎖へ戻る。（117行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の指定面、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の面の検収。

主宣言：`composableArrowRefinement_zero`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrowRefinement_zero {n : ℕ} (F : ComposableArrows C (n + 1))
    (B : C) (q : F.obj (0 : Fin (n + 1)).castSucc ⟶ B)
    (g : B ⟶ F.obj (0 : Fin (n + 1)).succ) :
    composableArrowRefinement F 0 B q g = (F.δ₀.precomp g).precomp q
```

主宣言：`composableArrowRefinement_face`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrowRefinement_face :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ),
      q ≫ g = F.map (homOfLE (Fin.castSucc_le_succ k)) →
        finiteChainFace (composableArrowRefinement F k B q g) k.succ.castSucc = F
```

#### [ComposableArrowRefinementNondegenerate.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowRefinementNondegenerate.lean)

非退化な実全鎖の細分は、左対象が異なり右因子が非同型なら非退化。（87行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前のcoherentな随伴の実構成。

主宣言：`composableArrowRefinement_nondegenerate`

```lean
lemma composableArrowRefinement_nondegenerate {C : Type u} [Category.{v} C] {n : ℕ}
    (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
    (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ)
    (fac : q ≫ g = F.map (homOfLE (Fin.castSucc_le_succ k)))
    (hnd : ULift.up F ∈ (SSet.uliftFunctor.{w, max u v}.obj (nerve C)).nonDegenerate (n + 1))
    (hq : F.obj k.castSucc ≠ B) (hg : ¬ IsIso g) :
    ULift.up (composableArrowRefinement F k B q g) ∈
      (SSet.uliftFunctor.{w, max u v}.obj (nerve C)).nonDegenerate (n + 2)
```

#### [ComposableArrowRefinementPositions.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowRefinementPositions.lean)

実細分で挿入した対象と、その右の実射を全実鎖から取り出す。（82行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分の退化の排除。

主宣言：`composableArrowRefinement_middle`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrowRefinement_middle :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ),
      (composableArrowRefinement F k B q g).obj k.succ.castSucc = B
```

主宣言：`composableArrowRefinement_right_edge`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrowRefinement_right_edge :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ),
      HEq ((composableArrowRefinement F k B q g).map
        (homOfLE (Fin.castSucc_le_succ k.succ))) g
```

#### [ComposableArrowRefinementPrefix.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/ComposableArrowRefinementPrefix.lean)

実細分の指定位置より前の実対象・辺と、挿入した左の実射を回収する。（110行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の最初の折り返しの保存、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の検収。

主宣言：`composableArrowRefinement_before_obj`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrowRefinement_before_obj {n : ℕ} (F : ComposableArrows C (n + 1))
    (k : Fin (n + 1)) (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ)
    (fac : q ≫ g = F.map (homOfLE (Fin.castSucc_le_succ k)))
    (i : Fin (n + 2)) (hi : i.val ≤ k.val) :
    (composableArrowRefinement F k B q g).obj i.castSucc = F.obj i
```

主宣言：`composableArrowRefinement_before_edge`

```lean
variable {C : Type u} [Category.{v} C]

lemma composableArrowRefinement_before_edge :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ)
      (j : Fin (n + 1)), j < k →
      HEq ((composableArrowRefinement F k B q g).map
        (homOfLE (Fin.castSucc_le_succ j.castSucc)))
          (F.map (homOfLE (Fin.castSucc_le_succ j)))
```

#### [FiniteFunctorObjects.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/FiniteFunctorObjects.lean)

有限な対象の範囲に値を持つ有限圏からの実関手は有限個である。（54行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の各幅での実関手の有限性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの有限性。

主宣言：`finite_functors_of_objectwise_finite`

```lean
lemma finite_functors_of_objectwise_finite {I : Type u₁} {D : Type u₂}
    [Category.{v₁} I] [Category.{v₂} D] [Finite I]
    [∀ i j : I, Finite (i ⟶ j)] [∀ A B : D, Finite (A ⟶ B)]
    (P : D → Prop) [Finite {A : D // P A}] :
    Finite {F : I ⥤ D // ∀ i, P (F.obj i)}
```

#### [NerveCollapsedEdges.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/NerveCollapsedEdges.lean)

実鎖の一辺が恒等射の輸送なら、元のnerveでその辺を退化として縮約できる。（93行）

原典・利用箇所：Riehl–Verity §3.1・§4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の同型な実辺の検出。

主宣言：`nerve_sigma_delta_of_eqToHom_edge`

```lean
lemma nerve_sigma_delta_of_eqToHom_edge {C : Type u} [Category.{v} C] {n : ℕ}
    (F : ComposableArrows C (n + 1)) (j : Fin (n + 1))
    (hobj : F.obj j.castSucc = F.obj j.succ)
    (hedge : F.map (homOfLE (Fin.castSucc_le_succ j)) = eqToHom hobj) :
    (nerve C).σ j ((nerve C).δ j.castSucc F) = F
```

主宣言：`uliftNerve_degenerate_of_eqToHom_edge`

```lean
lemma uliftNerve_degenerate_of_eqToHom_edge {C : Type u} [Category.{v} C] {n : ℕ}
    (F : ComposableArrows C (n + 1)) (j : Fin (n + 1))
    (hobj : F.obj j.castSucc = F.obj j.succ)
    (hedge : F.map (homOfLE (Fin.castSucc_le_succ j)) = eqToHom hobj) :
    ULift.up F ∈ (SSet.uliftFunctor.{w, max u v}.obj (nerve C)).degenerate (n + 1)
```

#### [NerveDegeneracyEdges.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/NerveDegeneracyEdges.lean)

元のnerveの退化で重なる辺は同型であり、対象と射の照合に沿って同型性を戻せる。（54行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の退化の排除。

主宣言：`isIso_of_equal_objects_hom_heq`

```lean
variable {C : Type u} [Category.{v} C]

lemma isIso_of_equal_objects_hom_heq {A B A' B' : C} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) [IsIso f] : IsIso g
```

主宣言：`nerve_degeneracy_edge_isIso`

```lean
variable {C : Type u} [Category.{v} C]

lemma nerve_degeneracy_edge_isIso {n : ℕ} (F : ComposableArrows C n) (j : Fin (n + 1)) :
    IsIso (((nerve C).σ j F).map (homOfLE (Fin.castSucc_le_succ j)))
```

#### [NondegenerateFaceDegeneracy.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/NondegenerateFaceDegeneracy.lean)

非退化な面を持つ単体の退化は、その面の両隣の位置にしか現れない。（80行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前のcoherentな随伴の実構成。

主宣言：`degeneracy_over_nondegenerate_face`

```lean
lemma degeneracy_over_nondegenerate_face {X : SSet.{u}} {n : ℕ}
    (z : X _⦋n + 2⦌) (k : Fin (n + 3)) (j : Fin (n + 2)) (t : X _⦋n + 1⦌)
    (hdeg : X.σ j t = z) (hnd : X.δ k z ∈ X.nonDegenerate (n + 1)) :
    (k = j.castSucc ∨ k = j.succ) ∧ X.σ j (X.δ k z) = z
```

主宣言：`nondegenerate_of_face_and_no_adjacent_degeneracy`

```lean
lemma nondegenerate_of_face_and_no_adjacent_degeneracy {X : SSet.{u}} {n : ℕ}
    (z : X _⦋n + 2⦌) (k : Fin (n + 3))
    (hnd : X.δ k z ∈ X.nonDegenerate (n + 1))
    (hno : ∀ j : Fin (n + 2), (k = j.castSucc ∨ k = j.succ) → X.σ j (X.δ k z) ≠ z) :
    z ∈ X.nonDegenerate (n + 2)
```

### 8. 原子の端点・有限順序の幅・有限性・再添字

#### [WalkingAdjunctionAtomicEndpointBounds.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicEndpointBounds.lean)

原子的な全単体の始頂点と終頂点の有限個数を決定する。（96行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の有限端点による表示。

主宣言：`walkingAdjunctionAtomic_last_card_le_one`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)

lemma walkingAdjunctionAtomic_last_card_le_one
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) ≤ 1
```

主宣言：`walkingAdjunctionAtomic_endpoint_cards`

```lean
variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)

lemma walkingAdjunctionAtomic_endpoint_cards
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard X Y (H.obj 0) =
        walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y ∧
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 1
```

#### [WalkingAdjunctionAtomicEndpoints.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicEndpoints.lean)

元の実全単体の原子性を始頂点と終頂点の二つの有限個数で判定する。（110行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の有限端点による表示。

主宣言：`walkingAdjunctionAtomic_of_endpoint_cards`

```lean
lemma walkingAdjunctionAtomic_of_endpoint_cards {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hfirst : walkingAdjunctionOrdinalCard X Y (H.obj 0) =
      walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y)
    (hlast : walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 1) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H
```

主宣言：`walkingAdjunctionLevelIsAtomic_iff_endpoint_cards`

```lean
lemma walkingAdjunctionLevelIsAtomic_iff_endpoint_cards {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H ↔
      walkingAdjunctionOrdinalCard X Y (H.obj 0) =
          walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y ∧
        walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 1
```

#### [WalkingAdjunctionAtomicFactorWidth.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicFactorWidth.lean)

非原子的な実全鎖の原子分解に現れる任意の実原子の幅は、全体の幅より小さい。（91行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の境界面の実原子分解、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの幅の比較。

主宣言：`walkingAdjunctionAtomicPath_atomic_of_length_one`

```lean
lemma walkingAdjunctionAtomicPath_atomic_of_length_one {n : ℕ}
    {A B : WalkingAdjunctionAtomicVertex n} (p : Quiver.Path A B) (hp : p.length = 1) :
    WalkingAdjunctionLevelIsAtomic ((walkingAdjunctionAtomicPathFunctor n).map p)
```

主宣言：`walkingAdjunctionAtomicFactor_width_lt`

```lean
lemma walkingAdjunctionAtomicFactor_width_lt {n : ℕ}
    {A B C D : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path A B) (e : B ⟶ C) (r : Quiver.Path C D)
    (ha : ¬ WalkingAdjunctionLevelIsAtomic
      ((walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)))) :
    walkingAdjunctionOrdinalWidth e.val < walkingAdjunctionOrdinalWidth
      ((walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)))
```

#### [WalkingAdjunctionAtomicNondegenerateCore.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicNondegenerateCore.lean)

全実原子を、同じ実幅を持つ非退化な実原子と単体圏の実全射から回収する。（53行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の退化した実原子因子の処理、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの非退化生成元。

主宣言：`walkingAdjunctionAtomic_nondegenerate_core`

```lean
lemma walkingAdjunctionAtomic_nondegenerate_core {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    ∃ (m : ℕ) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f)
      (K : ComposableArrows (walkingAdjunctionHom X Y) m),
      WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) K ∧
      ULift.up K ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate m ∧
      walkingAdjunctionOrdinalWidth K = walkingAdjunctionOrdinalWidth H ∧
      H = walkingAdjunctionSimplexFunctor f ⋙ K ∧ m ≤ n
```

#### [WalkingAdjunctionAtomicReindexing.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicReindexing.lean)

切断を持つ有限順序関手での再添字付けは原子性を保つ。（92行）

原典・利用箇所：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の退化と原子性の両立。

主宣言：`WalkingAdjunctionFactorization.left_size_zero_of_section_zero`

```lean
lemma WalkingAdjunctionFactorization.left_size_zero_of_section_zero {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (Q : Fin (n + 1) ⥤ Fin (m + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hQP : Q ⋙ P = 𝟭 (Fin (n + 1))) (a : WalkingAdjunctionFactorization (P ⋙ F))
    (ha : walkingAdjunctionLevelSize (Q ⋙ a.left) = 0) : walkingAdjunctionLevelSize a.left = 0
```

主宣言：`walkingAdjunctionLevelIsAtomic_precomp_of_split`

```lean
lemma walkingAdjunctionLevelIsAtomic_precomp_of_split {m n : ℕ}
    {X Y : WalkingAdjunctionPoint} (P : Fin (m + 1) ⥤ Fin (n + 1))
    (Q : Fin (n + 1) ⥤ Fin (m + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hQP : Q ⋙ P = 𝟭 (Fin (n + 1)))
    (hf : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) F) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) (P ⋙ F)
```

#### [WalkingAdjunctionAtomicWordWidth.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicWordWidth.lean)

実原子分解の全因子の幅の和を、元の全実鎖の有限順序の幅へ戻す。（95行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの因子の幅の境界。

主宣言：`WalkingAdjunctionAtomicWord.ordinalWidth`

```lean
def WalkingAdjunctionAtomicWord.ordinalWidth {n : ℕ} {X Y : WalkingAdjunctionLevel n}
    {F : X ⟶ Y} (a : WalkingAdjunctionAtomicWord n F) : ℕ
```

主宣言：`WalkingAdjunctionFactorization.right_ordinalWidth_le`

```lean
lemma WalkingAdjunctionFactorization.right_ordinalWidth_le {n : ℕ}
    {X Y : WalkingAdjunctionPoint} {H : ComposableArrows (walkingAdjunctionHom X Y) n}
    (a : WalkingAdjunctionFactorization H) :
    walkingAdjunctionOrdinalWidth a.right ≤ walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionBoundedChains.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionBoundedChains.lean)

重みを有限範囲に制限した全実鎖の全体は有限である。（64行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の各幅での有限性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの有限な範囲。

主宣言：`walkingAdjunctionHom_finite`

```lean
lemma walkingAdjunctionHom_finite (X Y : WalkingAdjunctionPoint) (A B : walkingAdjunctionHom X Y) :
    Finite (A ⟶ B)
```

主宣言：`walkingAdjunctionBoundedChains_finite`

```lean
lemma walkingAdjunctionBoundedChains_finite (n : ℕ) (X Y : WalkingAdjunctionPoint) (w : ℕ) :
    Finite {H : ComposableArrows (walkingAdjunctionHom X Y) n //
      ∀ i, walkingAdjunctionWeight X Y (H.obj i) ≤ w}
```

#### [WalkingAdjunctionDegeneracies.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionDegeneracies.lean)

実際の退化写像の有限順序関手を構成し、全随伴の原子性の保存を証明する。（104行）

原典・利用箇所：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の全随伴のsimplicial computadの条件。

主宣言：`walkingAdjunctionSimplexFunctor`

```lean
def walkingAdjunctionSimplexFunctor {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    Fin (m + 1) ⥤ Fin (n + 1)
```

主宣言：`walkingAdjunctionHomShape_degeneracy_atomic`

```lean
lemma walkingAdjunctionHomShape_degeneracy_atomic {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (i : Fin (n + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hf : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) F) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩)
      ((((WalkingAdjunctionHomShape.{u} X Y).map (SimplexCategory.σ i).op) (ULift.up F)).down)
```

#### [WalkingAdjunctionDegenerateInnerWidth.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionDegenerateInnerWidth.lean)

非退化な実全鎖の内側面が退化すれば、その幅は真に小さくなる。（90行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の退化面の順序づけ、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの幅の比較。

主宣言：`walkingAdjunctionInnerFace_nondegenerate_iff_not_isIso`

```lean
lemma walkingAdjunctionInnerFace_nondegenerate_iff_not_isIso {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2))
    (k : Fin (n + 1))
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 2)) :
    (ULift.up (finiteChainFace H k.succ.castSucc) ∈
      (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1)) ↔
    ¬ IsIso (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
      H.map (homOfLE (Fin.castSucc_le_succ k.succ)))
```

主宣言：`walkingAdjunctionOrdinalWidth_inner_lt_of_not_nondegenerate`

```lean
lemma walkingAdjunctionOrdinalWidth_inner_lt_of_not_nondegenerate {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2))
    (k : Fin (n + 1))
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 2))
    (hf : ULift.up (finiteChainFace H k.succ.castSucc) ∉
      (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1)) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H k.succ.castSucc) <
      walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionEpiAtomicity.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionEpiAtomicity.lean)

任意の単体圏の実全射は端点を保ち、再添字付けによる実原子性の同値を与える。（60行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の非退化な実原子への輸送、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの退化因子。

主宣言：`walkingAdjunctionSimplexFunctor_epi_endpoints`

```lean
lemma walkingAdjunctionSimplexFunctor_epi_endpoints {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) [Epi f] :
    (walkingAdjunctionSimplexFunctor f).obj 0 = 0 ∧
      (walkingAdjunctionSimplexFunctor f).obj (Fin.last m) = Fin.last n
```

主宣言：`walkingAdjunctionLevelIsAtomic_epi_iff`

```lean
lemma walkingAdjunctionLevelIsAtomic_epi_iff {m n : ℕ} {X Y : WalkingAdjunctionPoint}
    (f : ⦋m⦌ ⟶ ⦋n⦌) [Epi f] (H : ComposableArrows (walkingAdjunctionHom X Y) n) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionSimplexFunctor f ⋙ H) ↔
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H
```

#### [WalkingAdjunctionEpiWidth.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionEpiWidth.lean)

任意の単体圏の実全射による再添字付けは有限順序の幅を保つ。（57行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の退化因子から非退化な元への幅の輸送、 HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtration。

主宣言：`walkingAdjunctionOrdinalWidth_epi`

```lean
lemma walkingAdjunctionOrdinalWidth_epi {X Y : WalkingAdjunctionPoint} :
    ∀ (m n : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌) [Epi f]
      (H : ComposableArrows (walkingAdjunctionHom X Y) n),
      walkingAdjunctionOrdinalWidth (walkingAdjunctionSimplexFunctor f ⋙ H) =
        walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionFirstFaceWidth.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionFirstFaceWidth.lean)

先頭面の幅の欠損を始点と実像から計算し、最初の併合より前では幅の保存を示す。（109行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の先頭の実境界面、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの実幅の比較。

主宣言：`walkingAdjunctionOrdinalWidth_first_face_defect`

```lean
lemma walkingAdjunctionOrdinalWidth_first_face_defect {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) :
    walkingAdjunctionOrdinalWidth H = walkingAdjunctionOrdinalWidth H.δ₀ +
      2 * (walkingAdjunctionOrdinalCard X Y (H.obj 0) -
        ordinalImageCard (walkingAdjunctionOrderHom (H.map' 0 1)))
```

主宣言：`walkingAdjunctionFirstFace_width_and_not_atomic`

```lean
lemma walkingAdjunctionFirstFace_width_and_not_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ 0) :
    walkingAdjunctionOrdinalWidth H.δ₀ = walkingAdjunctionOrdinalWidth H ∧
      ¬ WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H.δ₀
```

#### [WalkingAdjunctionIsoDegeneracy.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionIsoDegeneracy.lean)

元の四Homの同型は恒等射の輸送であり、非退化な全単体の全隣接辺は非同型。（83行）

原典・利用箇所：Riehl–Verity §3.1・§4.1–§4.2の実親の一意性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の同型な実辺の検出。

主宣言：`walkingAdjunctionIsIso_eqToHom`

```lean
lemma walkingAdjunctionIsIso_eqToHom {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) [IsIso f] :
    ∃ h : A = B, f = eqToHom h
```

主宣言：`walkingAdjunctionHomShape_nondegenerate_iff_no_isIso`

```lean
lemma walkingAdjunctionHomShape_nondegenerate_iff_no_isIso {n : ℕ}
    {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) :
    ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1) ↔
      ∀ j : Fin (n + 1), ¬ IsIso (H.map (homOfLE (Fin.castSucc_le_succ j)))
```

#### [WalkingAdjunctionIsomorphismProfiles.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionIsomorphismProfiles.lean)

元の実Homの同型は共通の有限順序の同型を与え、その点の値を保つ。（63行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の最初の併合の厳密な表示、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の退化の検出。

主宣言：`walkingAdjunctionOrderIsoOfIsIso`

```lean
def walkingAdjunctionOrderIsoOfIsIso {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) [IsIso f] :
    Fin (walkingAdjunctionOrdinalCard X Y A) ≃o Fin (walkingAdjunctionOrdinalCard X Y B)
```

主宣言：`walkingAdjunctionOrderHom_val_of_isIso`

```lean
lemma walkingAdjunctionOrderHom_val_of_isIso {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B) [IsIso f]
    (i : Fin (walkingAdjunctionOrdinalCard X Y A)) :
    (walkingAdjunctionOrderHom f i).val = i.val
```

#### [WalkingAdjunctionOrdinalWidth.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOrdinalWidth.lean)

実辺の像の個数から全鎖の幅の有限順序表示を作り、非退化な原子の次元を押さえる。（117行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の実filtrationの順序づけ、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実非退化原子の有限の境界。

主宣言：`walkingAdjunctionOrdinalWidth`

```lean
def walkingAdjunctionOrdinalWidth {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) : ℕ
```

主宣言：`walkingAdjunctionOrdinalWidth_dimension_lt`

```lean
lemma walkingAdjunctionOrdinalWidth_dimension_lt {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate n) :
    n < walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionOrdinalWidthAppend.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOrdinalWidthAppend.lean)

実全鎖の終端へ実射を挿入したときの、有限順序の幅の変化を計算する。（87行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の最後の深さの実親の幅、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実挿入の幅の法則。

主宣言：`walkingAdjunctionAppend_before_variation`

```lean
lemma walkingAdjunctionAppend_before_variation {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (B : walkingAdjunctionHom X Y)
    (f : H.obj (Fin.last n) ⟶ B) (j : Fin n) :
    ordinalMapVariation (walkingAdjunctionOrderHom ((composableArrowAppend H B f).map
      (homOfLE (Fin.castSucc_le_succ j.castSucc)))) =
    ordinalMapVariation (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j))))
```

主宣言：`walkingAdjunctionOrdinalWidth_append`

```lean
lemma walkingAdjunctionOrdinalWidth_append {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (B : walkingAdjunctionHom X Y)
    (f : H.obj (Fin.last n) ⟶ B) :
    walkingAdjunctionOrdinalWidth (composableArrowAppend H B f) +
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) =
    walkingAdjunctionOrdinalWidth H + walkingAdjunctionOrdinalCard X Y B +
      ordinalMapVariation (walkingAdjunctionOrderHom f)
```

#### [WalkingAdjunctionOrdinalWidthDegeneracy.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOrdinalWidthDegeneracy.lean)

元のnerveの全実退化は有限順序の幅を保つ。（109行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの退化の法則。

主宣言：`finPredAbove_other_edge`

```lean
lemma finPredAbove_other_edge {n : ℕ} (j : Fin (n + 1)) (i : Fin n) :
    j.predAbove (j.succAbove i).castSucc = i.castSucc ∧
      j.predAbove (j.succAbove i).succ = i.succ
```

主宣言：`walkingAdjunctionOrdinalWidth_degeneracy`

```lean
lemma walkingAdjunctionOrdinalWidth_degeneracy {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (j : Fin (n + 1)) :
    walkingAdjunctionOrdinalWidth ((nerve (walkingAdjunctionHom X Y)).σ j H) =
      walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionOrdinalWidthFaces.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOrdinalWidthFaces.lean)

元の全実鎖に任意の面を取ると、有限順序の幅は増えない。（159行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の実面とfiltration、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実幅の比較。

主宣言：`walkingAdjunctionOrdinalWidth_zero`

```lean
lemma walkingAdjunctionOrdinalWidth_zero {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) 0) :
    walkingAdjunctionOrdinalWidth H =
      walkingAdjunctionOrdinalCard X Y (H.obj 0) + walkingAdjunctionOrdinalCard X Y (H.obj 0) -
        (walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y)
```

主宣言：`walkingAdjunctionOrdinalWidth_face_le`

```lean
lemma walkingAdjunctionOrdinalWidth_face_le {X Y : WalkingAdjunctionPoint} :
    ∀ (n : ℕ) (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) (p : Fin (n + 2)),
      walkingAdjunctionOrdinalWidth (finiteChainFace H p) ≤ walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionOrdinalWidthFinite.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOrdinalWidthFinite.lean)

有限順序の幅を固定した非退化な実原子は、全次数と四Homを合わせても有限個。（127行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の実filtrationの各幅の有限性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の有限の実範囲。

主宣言：`walkingAdjunctionAllAtomicWidth_set_finite`

```lean
lemma walkingAdjunctionAllAtomicWidth_set_finite (w : ℕ) :
    {p : Σ X : WalkingAdjunctionPoint, Σ Y : WalkingAdjunctionPoint,
        Σ n : ℕ, ComposableArrows (walkingAdjunctionHom X Y) n |
      WalkingAdjunctionLevelIsAtomic (X := ⟨p.1⟩) (Y := ⟨p.2.1⟩) p.2.2.2 ∧
        ULift.up p.2.2.2 ∈
          (WalkingAdjunctionHomShape.{u} p.1 p.2.1).nonDegenerate p.2.2.1 ∧
            walkingAdjunctionOrdinalWidth p.2.2.2 = w}.Finite
```

主宣言：`walkingAdjunctionAllAtomicWidth_le_set_finite`

```lean
lemma walkingAdjunctionAllAtomicWidth_le_set_finite (w : ℕ) :
    {p : Σ X : WalkingAdjunctionPoint, Σ Y : WalkingAdjunctionPoint,
        Σ n : ℕ, ComposableArrows (walkingAdjunctionHom X Y) n |
      WalkingAdjunctionLevelIsAtomic (X := ⟨p.1⟩) (Y := ⟨p.2.1⟩) p.2.2.2 ∧
        ULift.up p.2.2.2 ∈
          (WalkingAdjunctionHomShape.{u} p.1 p.2.1).nonDegenerate p.2.2.1 ∧
            walkingAdjunctionOrdinalWidth p.2.2.2 ≤ w}.Finite
```

#### [WalkingAdjunctionOrdinalWidthHorizontal.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOrdinalWidthHorizontal.lean)

実水平合成は全実辺の変化量と有限順序の幅について加法的である。（134行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の実原子分解の幅、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの幅の照合。

主宣言：`walkingAdjunctionOrdinalCard_comp_correction`

```lean
lemma walkingAdjunctionOrdinalCard_comp_correction (X M Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom M Y) :
    walkingAdjunctionOrdinalCard X Y ((walkingAdjunctionHorizontal X M Y).obj (A, B)) +
      walkingAdjunctionTargetCorrection M =
    walkingAdjunctionOrdinalCard X M A + walkingAdjunctionOrdinalCard M Y B
```

主宣言：`WalkingAdjunctionFactorization.ordinalWidth`

```lean
lemma WalkingAdjunctionFactorization.ordinalWidth {n : ℕ} {X Y : WalkingAdjunctionPoint}
    {H : ComposableArrows (walkingAdjunctionHom X Y) n} (a : WalkingAdjunctionFactorization H) :
    walkingAdjunctionOrdinalWidth H =
      walkingAdjunctionOrdinalWidth a.left + walkingAdjunctionOrdinalWidth a.right
```

#### [WalkingAdjunctionOrdinalWidthInnerFace.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOrdinalWidthInnerFace.lean)

内側の実面の幅の変化を、合成する二辺の変化量の差として計算する。（148行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の厳密な幅の減少、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの面の比較。

主宣言：`walkingAdjunctionOrdinalWidth_first_inner_defect`

```lean
lemma walkingAdjunctionOrdinalWidth_first_inner_defect {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H (1 : Fin (n + 3))) +
      ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1)) +
      ordinalMapVariation (walkingAdjunctionOrderHom (H.δ₀.map' 0 1)) =
    walkingAdjunctionOrdinalWidth H + ordinalMapVariation
      (walkingAdjunctionOrderHom (H.map' 0 1 ≫ H.δ₀.map' 0 1))
```

主宣言：`walkingAdjunctionOrdinalWidth_inner_lt`

```lean
lemma walkingAdjunctionOrdinalWidth_inner_lt {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) (k : Fin (n + 1))
    (hv : ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
          H.map (homOfLE (Fin.castSucc_le_succ k.succ)))) <
      ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))) +
      ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.succ))))) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H k.succ.castSucc) <
      walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionOrdinalWidthPositive.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOrdinalWidthPositive.lean)

有限順序の幅0は実単位を検出し、非自明な実因子の幅は元の幅より小さい。（91行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の実filtration、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子分解の厳密な幅の境界。

主宣言：`WalkingAdjunctionAtomicWord.size_zero_of_ordinalWidth_zero`

```lean
lemma WalkingAdjunctionAtomicWord.size_zero_of_ordinalWidth_zero {n : ℕ}
    {X Y : WalkingAdjunctionLevel n} {F : X ⟶ Y} (a : WalkingAdjunctionAtomicWord n F)
    (h : walkingAdjunctionOrdinalWidth F = 0) : walkingAdjunctionLevelSize F = 0
```

主宣言：`WalkingAdjunctionFactorization.right_ordinalWidth_lt`

```lean
lemma WalkingAdjunctionFactorization.right_ordinalWidth_lt {n : ℕ}
    {X Y : WalkingAdjunctionPoint} {H : ComposableArrows (walkingAdjunctionHom X Y) n}
    (a : WalkingAdjunctionFactorization H) (h : 0 < walkingAdjunctionLevelSize a.left) :
    walkingAdjunctionOrdinalWidth a.right < walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionOrdinalWidthPrecomp.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOrdinalWidthPrecomp.lean)

実全鎖の先頭へ実射を挿入したときの、有限順序の幅の変化を計算する。（100行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の実親の幅の法則、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの計算。

主宣言：`walkingAdjunctionMapVariation_heq`

```lean
lemma walkingAdjunctionMapVariation_heq {X Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom X Y} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    ordinalMapVariation (walkingAdjunctionOrderHom f) =
      ordinalMapVariation (walkingAdjunctionOrderHom g)
```

主宣言：`walkingAdjunctionOrdinalWidth_precomp`

```lean
lemma walkingAdjunctionOrdinalWidth_precomp {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) {A : walkingAdjunctionHom X Y}
    (f : A ⟶ H.left) :
    walkingAdjunctionOrdinalWidth (H.precomp f) + walkingAdjunctionOrdinalCard X Y H.left =
      walkingAdjunctionOrdinalWidth H + walkingAdjunctionOrdinalCard X Y A +
        ordinalMapVariation (walkingAdjunctionOrderHom f)
```

#### [WalkingAdjunctionOrdinalWidthRefinement.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOrdinalWidthRefinement.lean)

最初の実併合による実細分は有限順序の幅を保つ。（130行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の実親の幅の照合、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの法則。

主宣言：`walkingAdjunctionOrdinalWidth_refinement_zero`

```lean
lemma walkingAdjunctionOrdinalWidth_refinement_zero {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) (B : walkingAdjunctionHom X Y)
    (q : H.obj (0 : Fin (n + 1)).castSucc ⟶ B)
    (g : B ⟶ H.obj (0 : Fin (n + 1)).succ)
    (hv : ordinalMapVariation (walkingAdjunctionOrderHom q) +
      ordinalMapVariation (walkingAdjunctionOrderHom g) =
        ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1))) :
    walkingAdjunctionOrdinalWidth (composableArrowRefinement H 0 B q g) =
      walkingAdjunctionOrdinalWidth H
```

主宣言：`walkingAdjunctionFirstRefinement_ordinalWidth`

```lean
lemma walkingAdjunctionFirstRefinement_ordinalWidth {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement H ha hnd) =
      walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionOrdinalWidthVertices.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOrdinalWidthVertices.lean)

実全鎖の各頂点の個数と重みを、有限順序の幅で押さえる。（81行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の各幅での有限性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの有限の境界。

主宣言：`walkingAdjunctionVertexCard_le_first_add_variation`

```lean
lemma walkingAdjunctionVertexCard_le_first_add_variation {X Y : WalkingAdjunctionPoint} :
    ∀ (n : ℕ) (H : ComposableArrows (walkingAdjunctionHom X Y) n) (i : Fin (n + 1)),
      walkingAdjunctionOrdinalCard X Y (H.obj i) ≤
        walkingAdjunctionOrdinalCard X Y (H.obj 0) +
          ∑ j : Fin n, ordinalMapVariation
            (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j))))
```

主宣言：`walkingAdjunctionOrdinalWidth_vertex_weight_le`

```lean
lemma walkingAdjunctionOrdinalWidth_vertex_weight_le {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) (i : Fin (n + 1)) :
    walkingAdjunctionWeight X Y (H.obj i) ≤ walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionPlusParentWidth.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPlusParentWidth.lean)

始点plusから構成した実親の有限順序の幅は、元の幅より1大きい。（119行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4・Proposition 4.2.15の実親の幅、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの照合。

主宣言：`walkingAdjunctionPlusParentPrefix_variation`

```lean
lemma walkingAdjunctionPlusParentPrefix_variation {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n) (j : Fin n) :
    ordinalMapVariation (walkingAdjunctionOrderHom ((walkingAdjunctionPlusParentPrefix H).map
      (homOfLE (Fin.castSucc_le_succ j)))) =
      ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ j))))
```

主宣言：`walkingAdjunctionPlusParent_ordinalWidth`

```lean
lemma walkingAdjunctionPlusParent_ordinalWidth {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent H ha) =
      walkingAdjunctionOrdinalWidth H + 1
```

#### [WalkingAdjunctionReindexing.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionReindexing.lean)

各次数の全射の圏を有限順序関手で再添字付けする。（65行）

原典・利用箇所：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の退化と原子性の両立。

主宣言：`walkingAdjunctionLevelReindex`

```lean
def walkingAdjunctionLevelReindex {m n : ℕ} (P : Fin (m + 1) ⥤ Fin (n + 1)) :
    WalkingAdjunctionLevel n ⥤ WalkingAdjunctionLevel m
```

主宣言：`walkingAdjunctionLevelSize_precomp_zero`

```lean
lemma walkingAdjunctionLevelSize_precomp_zero {m n : ℕ} {X Y : WalkingAdjunctionPoint}
    (P : Fin (m + 1) ⥤ Fin (n + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (h : walkingAdjunctionLevelSize F = 0) : walkingAdjunctionLevelSize (P ⋙ F) = 0
```

### 9. 最初の併合・minus側の親・内側の子

#### [WalkingAdjunctionAtomicRefinement.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicRefinement.lean)

実射の細分を全随伴の実全単体へ挿入し、その原子性を証明する。（72行）

原典・利用箇所：Riehl–Verity §4.1–§4.2のfillableな原子の親の実構成、 HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分の全次元への挿入。

主宣言：`walkingAdjunctionBottomMergeRefinement`

```lean
def walkingAdjunctionBottomMergeRefinement {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)
```

主宣言：`walkingAdjunctionBottomMergeRefinement_atomic`

```lean
lemma walkingAdjunctionBottomMergeRefinement_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionBottomMergeRefinement H k m hA h1)
```

#### [WalkingAdjunctionBottomMerge.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionBottomMerge.lean)

最初の二点の併合による因子化を元のminusからの実Homの射へ戻す。（141行）

原典・利用箇所：Riehl–Verity §4.1–§4.2のfillableな原子の親の実構成、 HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の実単体の細分。

主宣言：`walkingAdjunctionBottomMergeObject`

```lean
def walkingAdjunctionBottomMergeObject (Y : WalkingAdjunctionPoint) (m : ℕ) :
    walkingAdjunctionHom .minus Y
```

主宣言：`walkingAdjunctionBottomMerge_factor`

```lean
lemma walkingAdjunctionBottomMerge_factor {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0) :
    walkingAdjunctionBottomMergeArrow A m hA ≫ walkingAdjunctionBottomMergeResidual f m hA h1 =
      f
```

#### [WalkingAdjunctionBottomMergeLaws.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionBottomMergeLaws.lean)

実併合射の異なる両対象と、右合成の消去・残余射の一意性を照合する。（100行）

原典・利用箇所：Riehl–Verity §4.1–§4.2のfillableな原子の親の実構成、 HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分の照合。

主宣言：`ordinalBottomMerge_surjective`

```lean
lemma ordinalBottomMerge_surjective (m : ℕ) : Function.Surjective (ordinalBottomMerge m)
```

主宣言：`walkingAdjunctionBottomMergeResidual_unique`

```lean
lemma walkingAdjunctionBottomMergeResidual_unique {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0)
    (g : walkingAdjunctionBottomMergeObject Y m ⟶ B)
    (hg : walkingAdjunctionBottomMergeArrow A m hA ≫ g = f) :
    g = walkingAdjunctionBottomMergeResidual f m hA h1
```

#### [WalkingAdjunctionBottomMergePositions.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionBottomMergePositions.lean)

終頂点が一点の非退化な実全単体には最初の二点を併合する隣接辺が存在する。（130行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の最初の併合の選択、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の構成。

主宣言：`WalkingAdjunctionBottomMergeAt`

```lean
def WalkingAdjunctionBottomMergeAt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y) (k : Fin (n + 1)) : Prop
```

主宣言：`WalkingAdjunctionBottomMergeAt.one_zero`

```lean
lemma WalkingAdjunctionBottomMergeAt.one_zero {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y} {k : Fin (n + 1)}
    (h : WalkingAdjunctionBottomMergeAt H k) :
    ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)), i.val = 1 →
      (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val = 0
```

#### [WalkingAdjunctionBottomMergePurity.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionBottomMergePurity.lean)

実併合の残余射の同型性を、一つだけの最初の併合という全点の条件へ照合する。（120行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の厳密な併合の表示。

主宣言：`walkingAdjunctionBottomMergeArrow_val`

```lean
lemma walkingAdjunctionBottomMergeArrow_val {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (i : Fin (walkingAdjunctionOrdinalCard .minus Y A)) :
    (walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA) i).val = i.val - 1
```

主宣言：`walkingAdjunctionBottomMerge_residual_isIso_iff_pure`

```lean
lemma walkingAdjunctionBottomMerge_residual_isIso_iff_pure {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0) :
    IsIso (walkingAdjunctionBottomMergeResidual f m hA h1) ↔
      walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
        ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
          (walkingAdjunctionOrderHom f i).val = i.val - 1
```

#### [WalkingAdjunctionBottomMergeRigidity.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionBottomMergeRigidity.lean)

一つだけの実併合の全点条件と指定面は実細分の全関手を一意に定める。（125行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の実親の一意性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の厳密な細分の照合。

主宣言：`walkingAdjunctionPureBottomMerge_rigidity`

```lean
lemma walkingAdjunctionPureBottomMerge_rigidity {Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom .minus Y} (hA : A = A')
    (f : A ⟶ B) (g : A' ⟶ B') (m : ℕ)
    (hf : walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
        (walkingAdjunctionOrderHom f i).val = i.val - 1)
    (hg : walkingAdjunctionOrdinalCard .minus Y B' = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A'),
        (walkingAdjunctionOrderHom g i).val = i.val - 1) :
    B = B' ∧ HEq f g
```

主宣言：`walkingAdjunctionBottomMergeRefinement_unique`

```lean
lemma walkingAdjunctionBottomMergeRefinement_unique {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (hface : finiteChainFace P k.succ.castSucc = H)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) :
    P = walkingAdjunctionBottomMergeRefinement H k m hA h1
```

#### [WalkingAdjunctionBottomMergeTransport.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionBottomMergeTransport.lean)

併合の実点の条件と一つだけの併合の全点条件を、実射の異種等式に沿って移す。（57行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の最初の併合の保存、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の検収。

主宣言：`walkingAdjunctionMergesBottom_heq`

```lean
lemma walkingAdjunctionMergesBottom_heq {Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom .minus Y} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    (∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y A), i.val = 1 ∧
      (walkingAdjunctionOrderHom f i).val = 0) ↔
    (∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y A'), i.val = 1 ∧
      (walkingAdjunctionOrderHom g i).val = 0)
```

主宣言：`walkingAdjunctionPureBottomMerge_heq`

```lean
lemma walkingAdjunctionPureBottomMerge_heq {Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom .minus Y} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) (m : ℕ) :
    (walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
        (walkingAdjunctionOrderHom f i).val = i.val - 1) ↔
    (walkingAdjunctionOrdinalCard .minus Y B' = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A'),
        (walkingAdjunctionOrderHom g i).val = i.val - 1)
```

#### [WalkingAdjunctionFirstBottomMerge.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionFirstBottomMerge.lean)

非退化な実全単体に存在する併合の位置から最小の位置を実際に選ぶ。（75行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の最初の併合の選択、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の構成。

主宣言：`walkingAdjunctionFirstBottomMergeData`

```lean
def walkingAdjunctionFirstBottomMergeData {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    {k : Fin (n + 1) // WalkingAdjunctionBottomMergeAt H k ∧
      ∀ j, WalkingAdjunctionBottomMergeAt H j → k ≤ j}
```

主宣言：`walkingAdjunctionFirstBottomMergeIndex_minimal`

```lean
lemma walkingAdjunctionFirstBottomMergeIndex_minimal {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    {j : Fin (n + 1)} (hj : WalkingAdjunctionBottomMergeAt H j) :
    walkingAdjunctionFirstBottomMergeIndex H hlast hnd ≤ j
```

#### [WalkingAdjunctionFirstRefinement.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionFirstRefinement.lean)

元の非退化な原子から最初の併合を選び、一つ高次の原子的な実全単体を構成する。（80行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の実候補、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の全coherentな随伴の入力。

主宣言：`walkingAdjunctionFirstRefinement`

```lean
def walkingAdjunctionFirstRefinement {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)
```

主宣言：`walkingAdjunctionFirstRefinement_nerve_face`

```lean
lemma walkingAdjunctionFirstRefinement_nerve_face {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    (((WalkingAdjunctionHomShape.{u} .minus Y).map (SimplexCategory.δ
      (walkingAdjunctionFirstBottomMergeIndex H
        (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd).succ.castSucc).op)
          (ULift.up (walkingAdjunctionFirstRefinement H ha hnd))).down = H
```

#### [WalkingAdjunctionFirstRefinementIndex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionFirstRefinementIndex.lean)

構成した実最初の細分の最小の併合添字を、元の実最小元そのものへ戻す。（44行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の実親の深さ、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの深さの照合。

主宣言：`walkingAdjunctionFirstRefinement_first_index`

```lean
lemma walkingAdjunctionFirstRefinement_first_index {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hp : ULift.up (walkingAdjunctionFirstRefinement H ha hnd) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)) :
    walkingAdjunctionFirstBottomMergeIndex (walkingAdjunctionFirstRefinement H ha hnd)
      (walkingAdjunctionAtomic_endpoint_cards _
        (walkingAdjunctionFirstRefinement_atomic H ha hnd)).2
      hp = (walkingAdjunctionFirstBottomMergeIndex H
        (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd).castSucc
```

#### [WalkingAdjunctionInnerFaceFirstMerge.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionInnerFaceFirstMerge.lean)

内側の面の最初の実併合の位置を、元の実親の最初の位置から回収する。（97行）

原典・利用箇所：Riehl–Verity Lemma 4.1.3の実親の逆方向、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の最初の実位置の照合。

主宣言：`walkingAdjunctionInnerFace_first_merge`

```lean
lemma walkingAdjunctionInnerFace_first_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = k.castSucc) :
    WalkingAdjunctionBottomMergeAt P k.castSucc
```

主宣言：`walkingAdjunctionInnerFace_first_index`

```lean
lemma walkingAdjunctionInnerFace_first_index {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = k.castSucc) :
    walkingAdjunctionFirstBottomMergeIndex (finiteChainFace P k.succ.castSucc)
      (walkingAdjunctionAtomic_endpoint_cards _ (walkingAdjunctionInnerFace_atomic P k ha)).2
      (walkingAdjunctionInnerFace_nondegenerate P k hnd
        (walkingAdjunctionInnerFace_first_merge P k ha hnd hidx)) = k
```

#### [WalkingAdjunctionInnerFaceNondegenerate.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionInnerFaceNondegenerate.lean)

内側の実親の指定面は原子的・非退化で、指定辺は実際に底の二点を併合する。（105行）

原典・利用箇所：Riehl–Verity Lemma 4.1.3の実親の逆方向、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実子の検収。

主宣言：`WalkingAdjunctionBottomMergeAt.not_isIso`

```lean
lemma WalkingAdjunctionBottomMergeAt.not_isIso {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)} {k : Fin (n + 1)}
    (h : WalkingAdjunctionBottomMergeAt H k) :
    ¬ IsIso (H.map (homOfLE (Fin.castSucc_le_succ k)))
```

主宣言：`walkingAdjunctionInnerFace_nondegenerate`

```lean
lemma walkingAdjunctionInnerFace_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hm : WalkingAdjunctionBottomMergeAt P k.castSucc) :
    ULift.up (finiteChainFace P k.succ.castSucc) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)
```

#### [WalkingAdjunctionInnerParentReconstruction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionInnerParentReconstruction.lean)

内側の純粋な実併合の親は、その指定面の実細分として全関手に復元される。（115行）

原典・利用箇所：Riehl–Verity Lemma 4.1.3の実親の逆方向、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親と子の照合。

主宣言：`walkingAdjunctionInnerFace_source_card`

```lean
lemma walkingAdjunctionInnerFace_source_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hm : WalkingAdjunctionBottomMergeAt P k.castSucc) :
    walkingAdjunctionOrdinalCard .minus Y
      ((finiteChainFace P k.succ.castSucc).obj k.castSucc) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 2
```

主宣言：`walkingAdjunctionInnerFace_firstRefinement`

```lean
lemma walkingAdjunctionInnerFace_firstRefinement {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = k.castSucc)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) :
    walkingAdjunctionFirstRefinement (finiteChainFace P k.succ.castSucc)
      (walkingAdjunctionInnerFace_atomic P k ha)
      (walkingAdjunctionInnerFace_nondegenerate P k hnd
        (walkingAdjunctionInnerFace_first_merge P k ha hnd hidx)) = P
```

#### [WalkingAdjunctionRefinementFaces.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionRefinementFaces.lean)

実併合で細分した全単体の指定面を、元のnerveの実面として検収する。（73行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の親の指定面、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前のcoherentな随伴の実面。

主宣言：`finiteChainFaceIndex_simplex`

```lean
lemma finiteChainFaceIndex_simplex {n : ℕ} (k : Fin (n + 2)) :
    finiteChainFaceIndex k = walkingAdjunctionSimplexFunctor (SimplexCategory.δ k)
```

主宣言：`walkingAdjunctionBottomMergeRefinement_nerve_face`

```lean
lemma walkingAdjunctionBottomMergeRefinement_nerve_face {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    (((WalkingAdjunctionHomShape.{u} .minus Y).map
      (SimplexCategory.δ k.succ.castSucc).op)
        (ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1))).down = H
```

#### [WalkingAdjunctionRefinementFirstMerge.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionRefinementFirstMerge.lean)

実併合による細分で最初の併合位置を保ち、その辺の厳密な全点条件を証明する。（205行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の実親の最初の折り返し、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前のfillable条件の検収。

主宣言：`walkingAdjunctionBottomMergeRefinement_at`

```lean
lemma walkingAdjunctionBottomMergeRefinement_at {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    WalkingAdjunctionBottomMergeAt (walkingAdjunctionBottomMergeRefinement H k m hA h1)
      k.castSucc
```

主宣言：`walkingAdjunctionFirstRefinement_nondegenerate_of_not_pure`

```lean
lemma walkingAdjunctionFirstRefinement_nondegenerate_of_not_pure
    {n : ℕ} {Y : WalkingAdjunctionPoint} (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hp :
      let k := walkingAdjunctionFirstBottomMergeIndex H
        (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd
      let m := walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) - 2
      ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
        ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
          (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
            i.val - 1)) :
    ULift.up (walkingAdjunctionFirstRefinement H ha hnd) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)
```

#### [WalkingAdjunctionRefinementNondegenerate.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionRefinementNondegenerate.lean)

実併合の右残余射が非同型の場合に細分した全単体の非退化性を証明する。（70行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前のcoherentな随伴の実構成。

主宣言：`walkingAdjunctionBottomMergeRefinement_nondegenerate`

```lean
lemma walkingAdjunctionBottomMergeRefinement_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hg : ¬ IsIso (walkingAdjunctionBottomMergeResidual
      (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1)) :
    ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)
```

主宣言：`walkingAdjunctionBottomMergeRefinement_nondegenerate_of_not_pure`

```lean
lemma walkingAdjunctionBottomMergeRefinement_nondegenerate_of_not_pure
    {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hp : ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
          i.val - 1)) :
    ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)
```

#### [WalkingAdjunctionRefinementNondegenerateIff.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionRefinementNondegenerateIff.lean)

実併合による細分の非退化性を、一つだけの併合でないという全点条件と同値にする。（102行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の実親の検収、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の厳密な併合と退化の照合。

主宣言：`walkingAdjunctionBottomMergeResidual_not_isIso_of_nondegenerate`

```lean
lemma walkingAdjunctionBottomMergeResidual_not_isIso_of_nondegenerate
    {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)) :
    ¬ IsIso (walkingAdjunctionBottomMergeResidual
      (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1)
```

主宣言：`walkingAdjunctionFirstRefinement_nondegenerate_iff_not_pure`

```lean
lemma walkingAdjunctionFirstRefinement_nondegenerate_iff_not_pure
    {n : ℕ} {Y : WalkingAdjunctionPoint} (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    let k
```

#### [WalkingAdjunctionUniqueRefinementParent.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionUniqueRefinementParent.lean)

非退化な指定面を持つ純粋な併合の実親の存在・一意性を非純粋性と照合する。（63行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の親の対応、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分の照合。

主宣言：`walkingAdjunctionBottomMergeRefinement_existsUnique_nondegenerate_iff`

```lean
lemma walkingAdjunctionBottomMergeRefinement_existsUnique_nondegenerate_iff
    {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    (∃! P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2),
      ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2) ∧
      finiteChainFace P k.succ.castSucc = H ∧
      walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) ↔
    ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
          i.val - 1)
```

#### [WalkingAdjunctionZeroReflection.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionZeroReflection.lean)

隣接する全実辺で底の二点の併合がなければ、全実射が0の逆像を反映する。（75行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の一点の実因子の回収。

主宣言：`walkingAdjunctionReflectsZeroToLast_of_no_bottom_merge`

```lean
lemma walkingAdjunctionReflectsZeroToLast_of_no_bottom_merge {n : ℕ}
    {Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0) :
    ∀ (i : Fin (n + 1)) (a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj i))),
      (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.le_last i))) a).val = 0 → a.val = 0
```

主宣言：`walkingAdjunctionReflectsZeroMap_of_no_bottom_merge`

```lean
lemma walkingAdjunctionReflectsZeroMap_of_no_bottom_merge {n : ℕ}
    {Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    {i j : Fin (n + 1)} (hij : i ≤ j)
    (a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj i)))
    (ha : (walkingAdjunctionOrderHom (H.map (homOfLE hij)) a).val = 0) : a.val = 0
```

### 10. plus側の親・最後の子・前置の回収

#### [WalkingAdjunctionLastFaceData.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionLastFaceData.lean)

最初の実併合が純粋な最後の辺である原子から、最後の面の回収条件を供給する。（94行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の最後の実面の検収。

主宣言：`walkingAdjunctionNoMerge_before_last_of_first_last`

```lean
lemma walkingAdjunctionNoMerge_before_last_of_first_last {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n) (j : Fin n) :
    ¬ WalkingAdjunctionBottomMergeAt P j.castSucc
```

主宣言：`walkingAdjunctionLastFace_card_two_of_first_last_pure`

```lean
lemma walkingAdjunctionLastFace_card_two_of_first_last_pure {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1) :
    walkingAdjunctionOrdinalCard .minus Y
      ((finiteChainFace P (Fin.last (n + 1))).obj (Fin.last n)) = 2
```

#### [WalkingAdjunctionLastParentUniqueness.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionLastParentUniqueness.lean)

最後の実面と一点の終点を持つ実全鎖は全関手として一意。（59行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の元の実親の回収。

主宣言：`walkingAdjunction_eq_of_last_face_and_card_one`

```lean
lemma walkingAdjunction_eq_of_last_face_and_card_one {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F G : ComposableArrows (walkingAdjunctionHom X Y) (n + 1))
    (hface : finiteChainFace F (Fin.last (n + 1)) = finiteChainFace G (Fin.last (n + 1)))
    (hf : walkingAdjunctionOrdinalCard X Y (F.obj (Fin.last (n + 1))) = 1)
    (hg : walkingAdjunctionOrdinalCard X Y (G.obj (Fin.last (n + 1))) = 1) : F = G
```

#### [WalkingAdjunctionPlusChild.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPlusChild.lean)

最初の実併合が純粋な最後の辺である実親から、始点plusの非退化な原子を回収する。（180行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の対応。

主宣言：`walkingAdjunctionPlusChild`

```lean
def walkingAdjunctionPlusChild {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1) :
    ComposableArrows (walkingAdjunctionHom .plus Y) n
```

主宣言：`walkingAdjunctionPlusChild_parent`

```lean
lemma walkingAdjunctionPlusChild_parent {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1) :
    walkingAdjunctionPlusParent (walkingAdjunctionPlusChild P ha hnd hidx hp)
      (walkingAdjunctionPlusChild_atomic P ha hnd hidx hp) = P
```

#### [WalkingAdjunctionPlusParent.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPlusParent.lean)

始点plusの原子的な実全単体に生成射を前置し、終端の実併合を挿入する。（108行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の最後の深さの親、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の始点plusの実構成。

主宣言：`walkingAdjunctionPlusParentPrefix`

```lean
def walkingAdjunctionPlusParentPrefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n) :
    ComposableArrows (walkingAdjunctionHom .minus Y) n
```

主宣言：`walkingAdjunctionPlusParent_atomic`

```lean
lemma walkingAdjunctionPlusParent_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionPlusParent H ha)
```

#### [WalkingAdjunctionPlusParentChildRoundtrip.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPlusParentChildRoundtrip.lean)

始点plusの実原子から作った親と回収した子の実全関手の往復を照合する。（75行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の実親の対応、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親と実子の検収。

主宣言：`walkingAdjunctionPlusParent_before_last_card`

```lean
lemma walkingAdjunctionPlusParent_before_last_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard .minus Y
      ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).castSucc) = 2
```

主宣言：`walkingAdjunctionPlusParent_child`

```lean
lemma walkingAdjunctionPlusParent_child {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate n) :
    walkingAdjunctionPlusChild (walkingAdjunctionPlusParent H ha)
      (walkingAdjunctionPlusParent_atomic H ha) (walkingAdjunctionPlusParent_nondegenerate H ha hnd)
      (walkingAdjunctionPlusParent_first_index H ha hnd)
      (walkingAdjunctionPlusParent_last_pure_with_source H ha) = H
```

#### [WalkingAdjunctionPlusParentNondegenerate.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPlusParentNondegenerate.lean)

始点plusの非退化な原子から構成した実親は元のHomのnerveで非退化。（79行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の最後の深さの親、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実非退化性の検収。

主宣言：`walkingAdjunctionPlusParent_nondegenerate`

```lean
lemma walkingAdjunctionPlusParent_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate n) :
    ULift.up (walkingAdjunctionPlusParent H ha) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)
```

#### [WalkingAdjunctionPlusParentPositions.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPlusParentPositions.lean)

始点plusから構成した実親の最初の併合は、純粋な最後の挿入辺である。（121行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の最後の深さ、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の位置の検収。

主宣言：`walkingAdjunctionPlusParent_no_before_merge`

```lean
lemma walkingAdjunctionPlusParent_no_before_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) (j : Fin n) :
    ¬ WalkingAdjunctionBottomMergeAt (walkingAdjunctionPlusParent H ha) j.castSucc
```

主宣言：`walkingAdjunctionPlusParent_first_index`

```lean
lemma walkingAdjunctionPlusParent_first_index {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate n) :
    walkingAdjunctionFirstBottomMergeIndex (walkingAdjunctionPlusParent H ha)
      (walkingAdjunctionAtomic_endpoint_cards _ (walkingAdjunctionPlusParent_atomic H ha)).2
      (walkingAdjunctionPlusParent_nondegenerate H ha hnd) = Fin.last n
```

#### [WalkingAdjunctionPrefixBottomMerge.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPrefixBottomMerge.lean)

実生成射を前置した全鎖の辺では二番目の実点は0へ送られない。（50行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の最後の折り返し、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の最初の実併合の位置。

主宣言：`walkingAdjunctionPlusParentPrefix_no_bottom_merge`

```lean
lemma walkingAdjunctionPlusParentPrefix_no_bottom_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) (n + 1)) (j : Fin (n + 1)) :
    ¬ WalkingAdjunctionBottomMergeAt (walkingAdjunctionPlusParentPrefix H) j
```

#### [WalkingAdjunctionPrefixIsomorphisms.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPrefixIsomorphisms.lean)

minusからplusへの固定した実対象の前置は同型と実全単体の非退化性を反映する。（78行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の始点plusの親、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実非退化性。

主宣言：`walkingAdjunctionPrefix_reflectsIsIso`

```lean
lemma walkingAdjunctionPrefix_reflectsIsIso {Y : WalkingAdjunctionPoint}
    (U : walkingAdjunctionHom .minus .plus) {A B : walkingAdjunctionHom .plus Y} (f : A ⟶ B)
    [IsIso ((walkingAdjunctionHorizontal .minus .plus Y).map
      (X := (U, A)) (Y := (U, B)) (𝟙 U, f))] : IsIso f
```

主宣言：`walkingAdjunctionPlusParentPrefix_nondegenerate`

```lean
lemma walkingAdjunctionPlusParentPrefix_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) (n + 1))
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate (n + 1)) :
    ULift.up (walkingAdjunctionPlusParentPrefix H) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)
```

#### [WalkingAdjunctionRemoveBottomPrefix.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionRemoveBottomPrefix.lean)

最初の一点の実因子を生成射の定値関手へ照合し、残りの始点plusの実関手を回収する。（156行）

原典・利用箇所：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実始点plus因子の回収。

主宣言：`walkingAdjunctionRemoveBottomPrefix`

```lean
def walkingAdjunctionRemoveBottomPrefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2) :
    ComposableArrows (walkingAdjunctionHom .plus Y) n
```

主宣言：`walkingAdjunctionRemoveBottomPrefix_roundtrip`

```lean
lemma walkingAdjunctionRemoveBottomPrefix_roundtrip {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionRemoveBottomPrefix (walkingAdjunctionPlusParentPrefix H)
      (walkingAdjunctionPlusParentPrefix_no_one H)
      (walkingAdjunctionPlusParentPrefix_last_card H ha) = H
```

### 11. 非指定面・幅と深さの減少・境界の例外

#### [WalkingAdjunctionBoundaryFactorWidth.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionBoundaryFactorWidth.lean)

非原子的な実境界面の原子分解に現れる任意の因子は、元の実鎖より幅が小さい。（67行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の境界面の全原子分解、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの順序づけ。

主宣言：`walkingAdjunctionLastFace_atomicFactor_width_lt`

```lean
lemma walkingAdjunctionLastFace_atomicFactor_width_lt {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1))
    {B C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨X⟩⟩ : WalkingAdjunctionAtomicVertex n) B) (e : B ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) =
      finiteChainFace H (Fin.last (n + 1))) :
    walkingAdjunctionOrdinalWidth e.val < walkingAdjunctionOrdinalWidth H
```

主宣言：`walkingAdjunctionFirstFace_atomicFactor_width_lt`

```lean
lemma walkingAdjunctionFirstFace_atomicFactor_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ 0)
    {B C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex n) B) (e : B ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) = H.δ₀) :
    walkingAdjunctionOrdinalWidth e.val < walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionBoundaryMinusParentWidth.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionBoundaryMinusParentWidth.lean)

非原子的な実境界面のminus始点の非退化原子因子では、実細分の幅も元より小さい。（68行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の境界因子の実親、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの実幅の比較。

主宣言：`walkingAdjunctionLastFace_minusFactor_parent_width_lt`

```lean
lemma walkingAdjunctionLastFace_minusFactor_parent_width_lt {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 2))
    {C : WalkingAdjunctionAtomicVertex (n + 1)}
    (q : Quiver.Path (⟨⟨X⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)) ⟨⟨.minus⟩⟩)
    (e : (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)))
    (hfac : (walkingAdjunctionAtomicPathFunctor (n + 1)).map (q.comp (e.toPath.comp r)) =
      finiteChainFace H (Fin.last (n + 2)))
    (he : ULift.up e.val ∈
      (WalkingAdjunctionHomShape.{u} .minus C.level.point).nonDegenerate (n + 1)) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement e.val e.property he) <
      walkingAdjunctionOrdinalWidth H
```

主宣言：`walkingAdjunctionFirstFace_minusFactor_parent_width_lt`

```lean
lemma walkingAdjunctionFirstFace_minusFactor_parent_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ 0)
    {C : WalkingAdjunctionAtomicVertex (n + 1)}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)) ⟨⟨.minus⟩⟩)
    (e : (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex (n + 1)))
    (hfac : (walkingAdjunctionAtomicPathFunctor (n + 1)).map (q.comp (e.toPath.comp r)) = H.δ₀)
    (he : ULift.up e.val ∈
      (WalkingAdjunctionHomShape.{u} .minus C.level.point).nonDegenerate (n + 1)) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement e.val e.property he) <
      walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionBoundaryPlusParentWidth.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionBoundaryPlusParentWidth.lean)

指定面以外の実境界面の始点plusの全原子因子について、実親の幅も元より小さい。（78行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の境界因子の親、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの実幅の比較。

主宣言：`walkingAdjunctionLastFace_plusFactor_parent_width_lt`

```lean
lemma walkingAdjunctionLastFace_plusFactor_parent_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ Fin.last n)
    {C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟨⟨.plus⟩⟩)
    (e : (⟨⟨.plus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) =
      finiteChainFace H (Fin.last (n + 1))) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent e.val e.property) <
      walkingAdjunctionOrdinalWidth H
```

主宣言：`walkingAdjunctionFirstFace_plusFactor_parent_width_lt`

```lean
lemma walkingAdjunctionFirstFace_plusFactor_parent_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ 0)
    {C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟨⟨.plus⟩⟩)
    (e : (⟨⟨.plus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) = H.δ₀) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent e.val e.property) <
      walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionFaceFirstIndex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionFaceFirstIndex.lean)

指定の併合の二辺に触れない内側の実面で、実最初の併合位置を計算する。（125行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の深さの比較、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの順序づけ。

主宣言：`walkingAdjunctionInnerFace_first_index_after`

```lean
lemma walkingAdjunctionInnerFace_first_index_after {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hjk : j < k)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 2))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H hlast hnd = j.castSucc)
    (hface : ULift.up (finiteChainFace H k.succ.castSucc) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    walkingAdjunctionFirstBottomMergeIndex (finiteChainFace H k.succ.castSucc)
      (by rw [finiteChainFace_inner_last]; exact hlast) hface = j
```

主宣言：`walkingAdjunctionInnerFace_first_index_before`

```lean
lemma walkingAdjunctionInnerFace_first_index_before {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hkj : k < j)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 2))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H hlast hnd = j.succ)
    (hface : ULift.up (finiteChainFace H k.succ.castSucc) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    walkingAdjunctionFirstBottomMergeIndex (finiteChainFace H k.succ.castSucc)
      (by rw [finiteChainFace_inner_last]; exact hlast) hface = j
```

#### [WalkingAdjunctionFaceMergeEdges.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionFaceMergeEdges.lean)

内側の実面の全辺について、底の二点の併合を元の辺へ戻す。（83行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の深さの比較、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの面の法則。

主宣言：`ordinalNoOneZero_comp`

```lean
lemma ordinalNoOneZero_comp {a b c : ℕ} (f : Fin a →o Fin b) (g : Fin b →o Fin c)
    (hf : ∀ i : Fin a, i.val = 1 → (f i).val ≠ 0)
    (hg : ∀ i : Fin b, i.val = 1 → (g i).val ≠ 0) :
    ∀ i : Fin a, i.val = 1 → (g.comp f i).val ≠ 0
```

主宣言：`walkingAdjunctionInnerFace_no_merged_merge`

```lean
lemma walkingAdjunctionInnerFace_no_merged_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hf : ¬ WalkingAdjunctionBottomMergeAt H k.castSucc)
    (hg : ¬ WalkingAdjunctionBottomMergeAt H k.succ) :
    ¬ WalkingAdjunctionBottomMergeAt (finiteChainFace H k.succ.castSucc) k
```

#### [WalkingAdjunctionFaceMergePurity.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionFaceMergePurity.lean)

指定した二辺に触れない内側の実面は、一つだけの底併合の全点条件を保つ。（62行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15のfillableな面、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの面の照合。

主宣言：`walkingAdjunctionInnerFace_before_pure_iff`

```lean
lemma walkingAdjunctionInnerFace_before_pure_iff {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hj : j < k) (m : ℕ) :
    let F
```

主宣言：`walkingAdjunctionInnerFace_after_pure_iff`

```lean
lemma walkingAdjunctionInnerFace_after_pure_iff {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hj : k < j) (m : ℕ) :
    let F
```

#### [WalkingAdjunctionFaceWidthGap.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionFaceWidthGap.lean)

実併合の直前の辺の像が値1を欠く場合、対応する内側面の幅は2減る。（58行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の指定直前の実面、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前のfiltrationの幅の減少。

主宣言：`ordinalNoOneImage_of_bottom_and_gt_one`

```lean
lemma ordinalNoOneImage_of_bottom_and_gt_one {a b : ℕ} (f : Fin a →o Fin b)
    (h0 : ∀ i, i.val = 0 → (f i).val = 0)
    (h1 : ∀ i, i.val = 1 → 1 < (f i).val) : ∀ i, (f i).val ≠ 1
```

主宣言：`walkingAdjunctionOrdinalWidth_inner_gap_two`

```lean
lemma walkingAdjunctionOrdinalWidth_inner_gap_two {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) (k : Fin (n + 1))
    (hcard : walkingAdjunctionOrdinalCard X Y (H.obj k.succ.succ) + 1 =
      walkingAdjunctionOrdinalCard X Y (H.obj k.succ.castSucc))
    (hmiss : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val ≠ 1)
    (hpure : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.succ))) i).val = i.val - 1) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H k.succ.castSucc) + 2 =
      walkingAdjunctionOrdinalWidth H
```

#### [WalkingAdjunctionInitialPureBoundary.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionInitialPureBoundary.lean)

最初の純粋な実併合が先頭なら、次数1のminus自己Homで先頭面は実単位となる。（72行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の余単位の場合、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の先頭の実境界面の検収。

主宣言：`walkingAdjunctionTarget_minus_of_first_index_zero`

```lean
lemma walkingAdjunctionTarget_minus_of_first_index_zero {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = 0) : Y = .minus
```

主宣言：`walkingAdjunctionInitialPureBoundary_control`

```lean
lemma walkingAdjunctionInitialPureBoundary_control {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = 0)
    (hp : walkingAdjunctionOrdinalCard .minus Y (H.obj 1) =
      walkingAdjunctionOrdinalCard .minus Y (H.obj 0) - 2 + 1) :
    Y = .minus ∧ n = 0 ∧ walkingAdjunctionLevelSize H.δ₀ = 0
```

#### [WalkingAdjunctionLastFaceAtomicity.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionLastFaceAtomicity.lean)

非退化な実原子の最後の境界面は原子的ではない。（63行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の最後の実境界面、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実境界面の原子分解。

主宣言：`walkingAdjunctionHom_isIso_of_card_one`

```lean
lemma walkingAdjunctionHom_isIso_of_card_one {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B)
    (ha : walkingAdjunctionOrdinalCard X Y A = 1)
    (hb : walkingAdjunctionOrdinalCard X Y B = 1) : IsIso f
```

主宣言：`walkingAdjunctionLastFace_not_atomic`

```lean
lemma walkingAdjunctionLastFace_not_atomic {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1)) :
    ¬ WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩)
      (finiteChainFace H (Fin.last (n + 1)))
```

#### [WalkingAdjunctionOnePointDegeneracy.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOnePointDegeneracy.lean)

全頂点が一点の実全単体は定値で、正の次元では元のnerveで退化する。（92行）

原典・利用箇所：Riehl–Verity §4.1–§4.2の原子の最初の併合の選択、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の構成。

主宣言：`walkingAdjunctionConst_of_card_one`

```lean
lemma walkingAdjunctionConst_of_card_one {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hc : ∀ i, walkingAdjunctionOrdinalCard X Y (H.obj i) = 1) :
    H = (Functor.const _).obj (H.obj 0)
```

主宣言：`walkingAdjunctionHomShape_exists_large_vertex`

```lean
lemma walkingAdjunctionHomShape_exists_large_vertex {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (h : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    ∃ i, 2 ≤ walkingAdjunctionOrdinalCard .minus Y (H.obj i)
```

#### [WalkingAdjunctionOnePointSource.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionOnePointSource.lean)

minus自己Homの一点の実対象から出る実鎖は、実単位の定値関手となる。（69行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の先頭の純粋な実併合の境界、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実単位の回収。

主宣言：`walkingAdjunctionMinusHom_target_card_one`

```lean
lemma walkingAdjunctionMinusHom_target_card_one
    {A B : walkingAdjunctionHom .minus .minus} (f : A ⟶ B)
    (ha : walkingAdjunctionOrdinalCard .minus .minus A = 1) :
    walkingAdjunctionOrdinalCard .minus .minus B = 1
```

主宣言：`walkingAdjunctionMinusChain_dimension_zero_of_second_card_one`

```lean
lemma walkingAdjunctionMinusChain_dimension_zero_of_second_card_one {n : ℕ}
    (H : ComposableArrows (walkingAdjunctionHom .minus .minus) (n + 1))
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus .minus).nonDegenerate (n + 1))
    (hc : walkingAdjunctionOrdinalCard .minus .minus (H.obj 1) = 1) : n = 0
```

#### [WalkingAdjunctionPlusFactorParentWidth.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPlusFactorParentWidth.lean)

生成射を前置した単独の原子でない実鎖では、始点plusの任意の原子因子の実親も幅が小さい。（79行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の境界因子の実親、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の幅が1増える実親の比較。

主宣言：`walkingAdjunctionPlusFactor_parent_width_lt`

```lean
lemma walkingAdjunctionPlusFactor_parent_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (F : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    {C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟨⟨.plus⟩⟩)
    (e : (⟨⟨.plus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) = F)
    (hno : ∀ E : ComposableArrows (walkingAdjunctionHom .plus Y) n,
      WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) E →
        F ≠ walkingAdjunctionPlusParentPrefix E) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent e.val e.property) <
      walkingAdjunctionOrdinalWidth F
```

#### [WalkingAdjunctionPrefixBoundaryRecognition.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPrefixBoundaryRecognition.lean)

実生成射の前置になっている最後の境界面から、最後の深さの実親を回収する。（64行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の境界で親の幅が一致する場合、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の識別。

主宣言：`walkingAdjunction_eq_plusParent_of_last_face_prefix`

```lean
lemma walkingAdjunction_eq_plusParent_of_last_face_prefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (E : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) E)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hface : finiteChainFace H (Fin.last (n + 1)) = walkingAdjunctionPlusParentPrefix E) :
    H = walkingAdjunctionPlusParent E ha
```

主宣言：`walkingAdjunctionFirstIndex_last_of_last_face_prefix`

```lean
lemma walkingAdjunctionFirstIndex_last_of_last_face_prefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (E : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hface : finiteChainFace H (Fin.last (n + 1)) = walkingAdjunctionPlusParentPrefix E) :
    walkingAdjunctionFirstBottomMergeIndex H hlast hnd = Fin.last n
```

#### [WalkingAdjunctionPreviousFace.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPreviousFace.lean)

最初の純粋な併合の直前を合成し、値1が先行辺の像に入る場合の実面を検収する。（105行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の指定直前の面、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの深さの比較。

主宣言：`walkingAdjunctionPreviousFace_control`

```lean
lemma walkingAdjunctionPreviousFace_control {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 2))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H hlast hnd = k.succ)
    (hbc : walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.succ) + 1 =
      walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.castSucc))
    (hg : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.succ))) i).val = i.val - 1)
    (hthrough : ∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc.castSucc)),
      i.val = 1 ∧ (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = 1) :
    let F
```

#### [WalkingAdjunctionPreviousFaceDichotomy.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPreviousFaceDichotomy.lean)

最初の純粋な実併合の直前の面を、幅の欠損2と深さが減る実親へ分ける。（88行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の指定直前の面の二つの場合、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの実順序づけ。

主宣言：`ordinalNoOneImage_or_through_one`

```lean
lemma ordinalNoOneImage_or_through_one {a b : ℕ} (f : Fin a →o Fin b)
    (h0 : ∀ i, i.val = 0 → (f i).val = 0)
    (hf : ∀ i, i.val = 1 → (f i).val ≠ 0) :
    (∀ i, (f i).val ≠ 1) ∨ ∃ i, i.val = 1 ∧ (f i).val = 1
```

主宣言：`walkingAdjunctionPreviousFace_dichotomy`

```lean
lemma walkingAdjunctionPreviousFace_dichotomy {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = k.succ)
    (hbc : walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.succ) + 1 =
      walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.castSucc))
    (hg : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.succ))) i).val = i.val - 1) :
    let F
```

#### [WalkingAdjunctionPreviousFaceParent.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPreviousFaceParent.lean)

指定直前の非純粋な実面の実親は、元より深さが小さく、幅は元以下となる。（80行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の指定直前の面の実親、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの順序づけ。

主宣言：`walkingAdjunctionPreviousFace_parent_control`

```lean
lemma walkingAdjunctionPreviousFace_parent_control {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = k.succ)
    (hbc : walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.succ) + 1 =
      walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.castSucc))
    (hg : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.succ))) i).val = i.val - 1)
    (hthrough : ∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc.castSucc)),
      i.val = 1 ∧ (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = 1) :
    let F
```

#### [WalkingAdjunctionPureMergeCancellation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionPureMergeCancellation.lean)

先行辺が底の二点を併合せず、底併合との合成が純粋なら、その先行辺は同型。（70行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の指定直前の非fillableな面、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの深さの減少。

主宣言：`ordinalVal_eq_of_bottomMerge_comp_pure`

```lean
lemma ordinalVal_eq_of_bottomMerge_comp_pure {a b c : ℕ}
    (f : Fin a →o Fin b) (g : Fin b →o Fin c)
    (h0 : ∀ i, i.val = 0 → (f i).val = 0)
    (hf : ∀ i, i.val = 1 → (f i).val ≠ 0)
    (hg : ∀ i, (g i).val = i.val - 1)
    (hcomp : ∀ i, (g.comp f i).val = i.val - 1) : ∀ i, (f i).val = i.val
```

主宣言：`walkingAdjunctionIsIso_of_pure_bottomMerge_comp`

```lean
lemma walkingAdjunctionIsIso_of_pure_bottomMerge_comp {Y : WalkingAdjunctionPoint}
    {A B C : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (g : B ⟶ C)
    (ha : 2 ≤ walkingAdjunctionOrdinalCard .minus Y A)
    (hbc : walkingAdjunctionOrdinalCard .minus Y C + 1 =
      walkingAdjunctionOrdinalCard .minus Y B)
    (hf : ∀ i, i.val = 1 → (walkingAdjunctionOrderHom f i).val ≠ 0)
    (hg : ∀ i, (walkingAdjunctionOrderHom g i).val = i.val - 1)
    (hp : walkingAdjunctionOrdinalCard .minus Y C =
        walkingAdjunctionOrdinalCard .minus Y A - 2 + 1 ∧
      ∀ i, (walkingAdjunctionOrderHom (f ≫ g) i).val = i.val - 1) : IsIso f
```

#### [WalkingAdjunctionWidthOneBoundary.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionWidthOneBoundary.lean)

幅1の実因子が前置された境界面は、元の最初の併合がその境界にある場合に限られる。（102行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の境界因子の親、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの例外の除去。

主宣言：`walkingAdjunctionLastFace_widthOne_prefix_control`

```lean
lemma walkingAdjunctionLastFace_widthOne_prefix_control {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (Q : ComposableArrows (walkingAdjunctionHom .minus .plus) n)
    (E : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) E)
    (hq : walkingAdjunctionOrdinalWidth Q = 1)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hface : finiteChainFace H (Fin.last (n + 1)) =
      Q.prod' E ⋙ walkingAdjunctionHorizontal .minus .plus Y) :
    H = walkingAdjunctionPlusParent E ha ∧
      walkingAdjunctionFirstBottomMergeIndex H hlast hnd = Fin.last n
```

主宣言：`walkingAdjunctionFirstIndex_zero_of_first_face_widthOne_prefix`

```lean
lemma walkingAdjunctionFirstIndex_zero_of_first_face_widthOne_prefix {n : ℕ}
    {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (Q : ComposableArrows (walkingAdjunctionHom .minus .plus) n)
    (E : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hea : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) E)
    (hq : walkingAdjunctionOrdinalWidth Q = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hface : H.δ₀ = Q.prod' E ⋙ walkingAdjunctionHorizontal .minus .plus Y) :
    walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = 0
```

#### [WalkingAdjunctionWidthOneGenerator.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionWidthOneGenerator.lean)

minusからplusへの幅1の実全鎖は実生成射の定値関手そのものである。（52行）

原典・利用箇所：Riehl–Verity Proposition 4.2.15の親の幅が一致する境界の場合、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実生成射の回収。

主宣言：`walkingAdjunctionWidthOne_minus_plus_generator`

```lean
lemma walkingAdjunctionWidthOne_minus_plus_generator {n : ℕ}
    (H : ComposableArrows (walkingAdjunctionHom .minus .plus) n)
    (hw : walkingAdjunctionOrdinalWidth H = 1) :
    H = (Functor.const (Fin (n + 1))).obj (walkingAdjunctionGeneratorVertex .minus)
```

### 12. 実原子の型・実親子・全単射

#### [WalkingAdjunctionAtomicCellChild.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicCellChild.lean)

全ての正の次数の純粋な実生成元から、非純粋な実子を同じ型で回収する。（142行）

原典・利用箇所：Riehl–Verity Definition 4.2.1、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親子の対応。

主宣言：`WalkingAdjunctionAtomicCell.child`

```lean
def WalkingAdjunctionAtomicCell.child {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y) (hfill : p.NativeFillable) :
    Σ X : WalkingAdjunctionPoint,
      {a : WalkingAdjunctionAtomicCell.{u} n X Y // ¬ a.NativeFillable}
```

主宣言：`WalkingAdjunctionAtomicCell.child_parent`

```lean
lemma WalkingAdjunctionAtomicCell.child_parent {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y) (hfill : p.NativeFillable) :
    ((p.child hfill).2.val.parent (p.child hfill).2.property) = p
```

#### [WalkingAdjunctionAtomicCellChildren.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicCellChildren.lean)

純粋な実親から、最後の場合と内側の場合の非純粋な実子を生成元の型で回収する。（104行）

原典・利用箇所：Riehl–Verity Definition 4.2.1、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親子の対応。

主宣言：`WalkingAdjunctionAtomicCell.lastChild`

```lean
def WalkingAdjunctionAtomicCell.lastChild {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y)
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate = Fin.last n)
    (hfill : p.NativeFillable) :
    {a : WalkingAdjunctionAtomicCell.{u} n .plus Y // ¬ a.NativeFillable}
```

主宣言：`WalkingAdjunctionAtomicCell.innerChild`

```lean
def WalkingAdjunctionAtomicCell.innerChild {n : ℕ} {Y : WalkingAdjunctionPoint}
    (p : WalkingAdjunctionAtomicCell.{u} (n + 2) .minus Y) (k : Fin (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex p.chain
      (walkingAdjunctionAtomic_endpoint_cards p.chain p.atomic).2 p.nondegenerate = k.castSucc)
    (hfill : p.NativeFillable) :
    {a : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y // ¬ a.NativeFillable}
```

#### [WalkingAdjunctionAtomicCellPairing.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicCellPairing.lean)

有限順序模型の非純粋な実生成元と、正の次数の純粋な実親の対応をまとめる。（99行）

原典・利用箇所：Riehl–Verity Definition 4.2.1、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの親子の組。

主宣言：`WalkingAdjunctionAtomicCell.parent_child`

```lean
lemma WalkingAdjunctionAtomicCell.parent_child {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    (a.parent hnf).child (a.parent_nativeFillable hnf) = ⟨X, ⟨a, hnf⟩⟩
```

主宣言：`walkingAdjunctionAtomicCellParentEquiv`

```lean
def walkingAdjunctionAtomicCellParentEquiv (n : ℕ) (Y : WalkingAdjunctionPoint) :
    (Σ X : WalkingAdjunctionPoint,
      {a : WalkingAdjunctionAtomicCell.{u} n X Y // ¬ a.NativeFillable}) ≃
    {p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y // p.NativeFillable}
```

#### [WalkingAdjunctionAtomicCellParentLaws.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicCellParentLaws.lean)

まとめた実親について、幅と指定面の実添字・元の全関手の等式を保持する。（80行）

原典・利用箇所：Riehl–Verity Definition 4.2.1・Proposition 4.2.15、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実付着の指定面。

主宣言：`WalkingAdjunctionAtomicCell.parentFaceIndex`

```lean
def WalkingAdjunctionAtomicCell.parentFaceIndex {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) : Fin (n + 2)
```

主宣言：`WalkingAdjunctionAtomicCell.parent_face`

```lean
lemma WalkingAdjunctionAtomicCell.parent_face {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    finiteChainFace (a.parent hnf).chain (a.parentFaceIndex hnf) = a.parentChildImage
```

#### [WalkingAdjunctionAtomicCellParentPositions.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicCellParentPositions.lean)

まとめた実親の指定面は先頭でなく、minus始点では内側、plus始点では最後となる。（68行）

原典・利用箇所：Riehl–Verity Lemma 4.2.10、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実付着の位置。

主宣言：`WalkingAdjunctionAtomicCell.parentFaceIndex_ne_zero`

```lean
lemma WalkingAdjunctionAtomicCell.parentFaceIndex_ne_zero {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (a : WalkingAdjunctionAtomicCell.{u} n X Y)
    (hnf : ¬ a.NativeFillable) : a.parentFaceIndex hnf ≠ 0
```

主宣言：`WalkingAdjunctionAtomicCell.parentFaceIndex_lt_last_iff`

```lean
lemma WalkingAdjunctionAtomicCell.parentFaceIndex_lt_last_iff {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (a : WalkingAdjunctionAtomicCell.{u} n X Y)
    (hnf : ¬ a.NativeFillable) : a.parentFaceIndex hnf < Fin.last (n + 1) ↔ X = .minus
```

#### [WalkingAdjunctionAtomicCells.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/SerrePositivity/InfinityCategories/HA/Monads/WalkingAdjunctionAtomicCells.lean)

非退化な実原子の生成元をまとめ、有限順序模型の純粋性の条件と実親を一つの型で保持する。（128行）

原典・利用箇所：Riehl–Verity Definition 4.1.1・4.2.1、HA Proposition 4.7.3.3、 Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの生成元の型。

主宣言：`WalkingAdjunctionAtomicCell`

```lean
structure WalkingAdjunctionAtomicCell (n : ℕ) (X Y : WalkingAdjunctionPoint) where
  chain : ComposableArrows (walkingAdjunctionHom X Y) n
  atomic : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) chain
  nondegenerate : ULift.up chain ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate n
```

主宣言：`WalkingAdjunctionAtomicCell.NativeFillable`

```lean
def WalkingAdjunctionAtomicCell.NativeFillable {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) : Prop
```

主宣言：`WalkingAdjunctionAtomicCell.parent`

```lean
def WalkingAdjunctionAtomicCell.parent {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y
```

主宣言：`WalkingAdjunctionAtomicCell.parent_nativeFillable`

```lean
lemma WalkingAdjunctionAtomicCell.parent_nativeFillable {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    (a.parent hnf).NativeFillable
```

## G01〜G15の到達点と残り（報告§131との対応）

**主出力の完成は0/15**。現在の179ファイルはG01の源・補助構成の到達点である。
「部品がある」ことと一覧の主出力の完成を分ける。以下の未構成名は§131の紙上の仕様。
一般部分と旧BE適用の残量は [⑤d報告§131–§132](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/formalization-plans/bhatt-scholze/reports/report-codex-m15.md) の型つき一覧・係数2の表を参照する。
数値は打ち切り前の再見積もりであり、今回の目録による新たな実装枠ではない。

| ID | 済んだ部分 | 残る主出力・検収型 |
|---|---|---|
| G01 | 全自己関手の合成、walking monad、`NativeMonad`の型・単位の辺、指定随伴の単位・余単位の代表。実walking adjunction豊穣圏・全次数の自由な道・幅と面・実親子の全単射 | `inducedNativeMonad a : NativeMonad C`と同じ`F ≫ U`への`FunctorIso`。原典の文字列条件・向きとの全比較、parental subcomputadと全付着・filtration、元の随伴からのcoherent延長、同じ単位・余単位・HA表示の検収 |
| G02 | 構成先のモナド型まで | `EM(T)`という実準圏、`U_T : EM(T) ⟶ C`、全作用、同じ宇宙。RV 6.1.7–9の重み付き極限は未構成 |
| G03 | この項目の主出力なし | 実自由関手`F_T`、`QCatAdjunction F_T U_T`、`FunctorIso (F_T ≫ U_T) T.endofunctor`。旧BE自由関手との比較は適用側 |
| G04 | 既存の厳密barはMonads外の入力部品 | 元の随伴の全coherent増大barを実全関手として作り、旧BE経路なら厳密barの像と比較 |
| G05 | 個々の単位・合成の法則まで | 全増大・追加退化を持つ`IsUSplit U (nativeBar a X).underlying`と元の分裂との比較 |
| G06 | この項目の主出力なし | EM側のU-split実現の創出、および旧BE経路では任意native U-split図式の実現の存在・Uによる保存。厳密図式の像だけの主張では足りない |
| G07 | 比較の源となる型の部品まで | `q_a : B ⟶ EM(inducedNativeMonad a)`と`FunctorIso (q_a ≫ U_T) U` |
| G08 | この項目の主出力なし | 保守性・U-split実現条件から同じ`q_a`の実完全忠実性。全写像空間の検収 |
| G09 | この項目の主出力なし | 同じ比較の本質的全射性・`IsQCatEquivalence q_a`。Barr–Beckの途中取り込み点には未到達 |
| G10 | 普通のdg側の既存部品はMonads外 | 共通のregular κ、同じnativeなUとTのκ-filtered保存。普通のaccessibilityをnative条件へ読み替えるだけでは不可 |
| G11 | 一般のaccessibility基盤はMonads外に存在 | accessibleなTについて`IsAccessible (EM(T))`。実代数準圏との全比較を含む |
| G12 | この項目の主出力なし | accessibleなTについて`HasSmallColimits (EM(T))`、任意小図式の全余錐。Tに全余極限保存を仮定する主張へ変更しない |
| G13 | 一般の同値によるaccessibility移送は既存・Monads外 | 旧BEの同じ`CAlg_R A`への具体的な移送は未実施 |
| G14 | 一般の`HasSmallColimits.of_equivalence`は既存・Monads外 | 旧BEの同じ圏へ全小余極限・指定余錐を戻す適用は未実施 |
| G15 | `IsPresentable`の一般の定義・同値移送は既存・Monads外 | 旧`barrattEcclesCore.CAlg`の同じ欄への適用は未実施。D81のHA-CAlgのpresentabilityとも未同定 |

G01で残る付着の普遍性は、RV Lemma 4.2.10の二種類のセルと任意の標的への実豊穣関手の延長・往復である。
既存の全単射や非指定面の幅の不等式だけからその普遍性は出ない。
また、現在の`NativeMonad`は全単体作用のデータを持つが、HAの`Alg(End(C))`との全同値や
任意の指定随伴からのそのデータの構成を持っていない。

## HAの道で使える範囲とBE固有の範囲

| 区分 | ファイル群・成果 | 再利用の仕方と境界 |
|---|---|---|
| 一般の単体集合・有限鎖の補助 | 役割2・7の有限順序、挿入、面、細分、非退化性、有限性 | BEを入力に取らない。HA側の具体的な単体的計算・RV表示に再利用候補。採用する模型の向き・記法との照合は必要 |
| 一般の自己関手・全作用 | 役割1の`EndofunctorComposition`、`WalkingMonad`、`NativeMonad`、`AdjunctionRepresentatives` | 任意の準圏・指定随伴が入力。HA 4.7の周囲の合成・coherent作用の参照。単位・余単位の辺の選択だけで全coherent延長を得たとはしない |
| walking adjunctionの具体的な源 | 役割3〜6の実豊穣圏、頂点、分解・切れ目、原子的な自由な道 | RVの有限順序模型の計算部品。HA 4.7との比較を進める場合の源。HA 2〜3章の∞-operadやCAlgを定義したものではない |
| 親子・幅・境界の計算 | 役割8〜12 | RV §4.1–§4.2の延長の証明で使う候補。模型内の親子の全単射まで完成。原典との全比較とfiltration・全付着は未完 |
| BEの模型CAlg_Rに固有の実装 | **179ファイル内にはない** | ファイルの直接importと宣言の引数を確認した範囲で、BE・`EInfinity`・`CAlg_R`への直接依存はない。一般部品をBEへ適用する予定だったことと、部品自体がBE固有であることを分ける |
| 旧BE適用の計画・既存入力 | §131の各右欄、既存`cAlgFreeForgetDerivedAdjunction`、厳密bar、BE忘却の保守性・極限保存等（Monads外） | 旧G12の未完成の適用。D81で採否を見直す対象。これらの既存宣言があることだけでは、EM比較・native sifted保存・presentabilityを供給したことにならない |
| HA 2〜3章のBS本経路 | ∞-operad、対称モノイダルD(A)、`CAlg(D(A))`、HA 3.2.2–3.2.3 | この179ファイルの完成物ではない。HA 3.2.3.2・3.2.3.5の直接経路は旧G12の完成を必須としない。整流の同値なしにHA-CAlgとBE-CAlgを読み替えない |

特に`MonObj (EndofunctorSpace C)`は通常の単体集合のモノイダル圏での構造であり、
HAの対称モノイダル∞圏の基盤を構築したという意味ではない。
`walkingMonadEnrichedCategory`や`walkingAdjunctionEnrichedCategory`もMathlibの単体的豊穣圏の構造である。
HAの∞-operadによる定義への接続は別の検収対象となる。

D81に従って打ち切りは維持する。5a-4・S7の別経路（HAのCAlgで直接、モノイダルな層化、
filtered保存と具体的層化の反復、極限保存だけでは不足する点）は [⑤d報告§131–§132](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/formalization-plans/bhatt-scholze/reports/report-codex-m15.md) に記録済み。
M15はD81の下の判断を待つ停止中であり、この目録作成で再開していない。

## この目録の確認範囲

179ファイルを役割に重複なく割り当て、各ファイルの一行説明、主宣言の実ヘッダー、
module docstringの原典・利用箇所を記録した。主宣言の抜粋は351本。
ソースとの照合、ファイル数・18,959行の再集計、基準mainからの差分がこのREADMEだけであることを確認した。
この確認は文書の整合性確認であり、Leanのビルド・公理監査を再実行するものではない。

# BS-D6 作業報告

基準は main `95c78fa64`。段 G 停止点 1 の連絡三件を drafts に反映した。確認はソースと差分による。`lake build`、`lake env lean` は実行していない。

## 変更した宣言と新設した宣言

| ファイル | 変更 | 新設 |
| --- | --- | --- |
| `Shared/Descendable.lean` | `IsThickTensorIdeal.tensor` を任意の M との導来テンソルの閉性にした。`unitAlgebra` を初出の前へ移し、`IsDescendable A B` を「B の忘却像が生成する thick ⊗-ideal が単位の忘却像を含む」と定義した。`isDescendable_complete` は台の導来完備性を引数に取る離散底の定理にした。 | `IsThickCompleteTensorIdeal`、`IsDescendableComplete`。完備版はテンソルの後に `Derived.completion A s` を合成し、完備化した単位の所属を調べる。 |
| `Sheaves/GlobalSections.lean` | `sheafification_exists` は生成辺を取り出し、反射の補題を適用する。既存の安定性引数は保持した。 | `sheafification_of_generatingEdges`、`exists_sheafGeneratingEdges`。どちらも係数の安定性を仮定しない。 |
| `Sheaves/SpaceValued.lean` | `sheafification_exists_spaces` は既存引数 h𝒮（`F2.Presentable.space_isPresentable` で供給可）を二補題に渡す。`discretePresheafInclusion` は従来の Kan 値図式による射を使い、辺の仕様を各 U での等式にした。 | `discretePresheaf_vertex`、`discretePresheafInclusion_edge`、`is0Truncated_iff_pointwise`。従来の構成は非公開の `kanDiscretePresheafInclusion` に置いた。 |
| `Sheaves/CAlgValued.lean` | `sheafification_exists_cAlg` は hA を同じ二補題に渡す。 | — |

S4 の反射の証明には `F2.Presentable.functor_isPresentable`（`F2/Presentable/FunctorPresentable.lean`）と `F2.Presentable.Localization.bousfield_isReflectiveSubcategory`（`F2/Presentable/Localization/BousfieldReflection.lean`）を使った。`hW` を述語の等号にして局所対象を層に移す。S4 で残した `sorry` は生成辺の存在である。被覆篩 S と表現可能前層 h_U に対し、G8 の写像空間の公式の右辺 Γ(X,F) が `sectionsOfDiagram X F` の極限に対応すれば、S ⊗ M → h_U ⊗ M による判定に使える。

## ∞ レーンとの型の照合

三つの名前は基準の `SerrePositivity/` に宣言がなく、使用先に `要確認（IF-G1 …）` を付けた。

| 仮名 | 使用箇所（drafts 内） | 供給側に必要な型・計算 |
| --- | --- | --- |
| `tensorWith` | `Shared/Descendable.lean` 66、291 行 | M を右因子とする D(A) の自己関手。A は M から推論し、結果は同じ D(A) 上の `Derived.completion A s` と合成できる型。 |
| `discreteSpaceInclusion` | `Sheaves/SpaceValued.lean` 70、88、99 行 | `nerve (Type u) ⟶ SpaceInfinity.{u}`。頂点は既存の `setsToKan` の離散 Kan 複体と等しく、集合の写像に対応する一単体はその Kan 値図式の辺の評価と等しいことが必要。完全忠実性だけからこの二つの厳密な等号は出ないため、実装での計算式を希望する。 |
| `Is0TruncatedSpace` | `Sheaves/SpaceValued.lean` 109 行 | `SpaceInfinity.{u} _⦋0⦌ → Prop`。点ごとの特徴づけの証明には、この述語が離散埋め込みの本質像を表すことが必要。 |

G13 の辺の両辺は `.edge` で同じ空間の一単体として比較する。これで両端の表示の違いに依存せず、既存の `kanDiagramNaturalTransformationEdge_at` と同じ粒度で式を書ける。頂点・辺と切り捨ての比較の証明は G13 待ち。離散底の `isDescendable_complete` の証明は予定どおり `sorry`。一般底の `isDescendableOver_complete` は Mod_R の相対完備テンソル（M15）待ちで、理由の注記のみ更新した。`hasDescentIndexLE_two_of_rhom` と `hasDescentIndexLEOver_two_of_rhom` は各底の内部 Hom 待ち。

## 呼び出しと確認範囲

- A2 と A5 の `sheafification_exists_cAlg J A hA`、A5 の `IsDescendableOver`、A6 の `sectionsOf` の引数は従来どおり。A0〜A9 に `isDescendable_complete`、変更した `tensor` 欄、`discretePresheafInclusion` の辺の仕様の直接利用は見当たらなかった。
- `unitAlgebra`、`cAlgForgetDerived`、`Derived.IsDerivedComplete`、`Derived.completion`、S4 の二つの既存補題、`HomotopyLimits.IsLocalObject`、`evaluateFunctorAt` と Kan 値図式の辺の評価補題を `rg` で照合した。対象四ファイルの実際の import 先は `ls` で確認した。
- 差分は drafts の四ファイルと本報告のみ。新しい `axiom` はなく、設計書・入口表・A0〜A9・`SerrePositivity/` への変更はない。Lean による型検査は未実施。

# SC-W1：I03 の実装前の照合メモ

2026-11-14。B4 の共有鍵を待つ間の紙の照合。I03 は既に型と見込みを記録した、A07 内の整拡大の有限・有限表示模型の実際の filtered colimit の証明。新しい主項目を追加せず、2g の Lean の先行実装も行わない。

一覧：済み 7／全体 12（うち追加 3）。

## 出口

既存の変数 R・B と R-algebra 構造について、`[Algebra.IsIntegral R B]` の下で、`IsColimit (integralModelSmallCocone R B)` を証明する。始域の模型の各構造射・環構造・小さい添字・filtered 性は I01・I02 の実際の構成を使う。単なる任意の集合の表示や、同型の存在だけへ出口を弱めない。

## 台の型での普遍性

Mathlib `CategoryTheory.Limits.Types.FilteredColimit.isColimitOf'` は、cocone t に対して次の二条件を要求する。

- `∀ x : t.pt, ∃ i xi, x = t.ι.app i xi`。
- `∀ i x y, t.ι.app i x = t.ι.app i y → ∃ k (f : i ⟶ k), F.map f x = F.map f y`。

前者は I01 の `exists_finite_finitePresentation_model_of_integral_family` を n=1 に適用する。得られた大きい模型 X を、`E := equivSmallModel (IntegralModelCategory R B)` の `E.functor.obj X` へ送り、`E.unitIso.hom.app X : X ⟶ E.inverse.obj (E.functor.obj X)` で代表元を運ぶ。cocone の自然性で元の B の元を表すことを確認する。

後者は、同じ大きい模型 C の x,y が B で一致したとき、`J := Ideal.span {x-y}` で割る。J は有限生成で、模型の B への射の核に含まれる。I02 の `IntegralModelCoequalizer` と同じ `Algebra.FinitePresentation.quotient`、`Ideal.Quotient.mkₐ`、`Ideal.Quotient.liftₐ` を使う。商は R 上有限かつ有限表示で、B への射を持ち、x と y の像が一致する。模型の射 f:X→Z を `f ≫ E.unitIso.hom.app Z` へ送り、E.inverse の充満性で小さい添字の射として持ち上げる。`map_preimage` と商の等式により、上の hinj を満たす。B に忠実平坦性・Noether 性を追加しない。

## 可換環への反映

手元の Mathlib で次をソースから確認した。

- `Algebra/Category/Ring/FilteredColimits.lean` の `CommRingCat.FilteredColimits.forget_preservesFilteredColimits`：forget CommRingCat は filtered colimit を保つ。
- `Algebra/Category/Ring/Basic.lean` の CommRingCat の `forgetReflectIsos`：同じ forget は同型を反映する。
- `Algebra/Category/Ring/Colimits.lean` の `hasColimits_commRingCat`：小さい添字の colimit が存在する。
- `CategoryTheory/Limits/Preserves/Basic.lean` の `reflectsColimitsOfShape_of_reflectsIsomorphisms`：上の三条件から shape ごとの colimit の反映を得る。

したがって、小さい模型の添字についてこの ReflectsColimitsOfShape を局所 instance にし、台の型の IsColimit から `isColimitOfReflects (forget CommRingCat)` で実際の環の cocone の IsColimit を得る。型で作った desc に対して環演算の保存をもう一度手作業で実装することは第一案にしない。

これはソース照合に基づく実装案であり、この instance の合成と SmallModel を介する式はまだ Lean で検証していない。見込みは既報の I03 の 400〜1,000 行を維持する。I04 では、この環の colimit を Spec の逆極限へ渡し、各有限・有限表示段の有限性と、元の Spec の全射性から各段の全射性を実際の因子化で示す。G2 の一般の固有模型の構成を、ここで既に得たことにはしない。

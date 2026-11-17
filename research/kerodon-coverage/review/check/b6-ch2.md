# KB-W1 / B6 第2章

原文の項目と現在のソースの型による紙の再照合。Lean・ビルド・鍵は使っていない。

対象 154行。none 74、partial 80。判定後：none 121、partial 33。

既存 own・both・mathlib 59行の全既存フィールドは変更なし。既存7列の末尾に partial_kind を追加し、対象外行は空欄とした。区切り・改行と対象外行の既存引用符を保存した。verdict・axioms・check も変更していない。古いcheck欄は今回のkernel検査結果ではない。

## 全対象行の判定・変更一覧

状態不変でも型/原文の再判定を記録した。各 reason の詳細はCSVと同じ。原文全文・候補の型・検索はgit外の章別証拠。

| 番号 | 旧→新 | partial_kind | 理由 |
| --- | --- | --- | --- |
| 2.1.1.1 | none → none |  | B6：現本体・固定Mathlibを再検索。単位を持たない厳密なテンソルの定義は未発見。厳密双圏の型は別。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.1.5 | none → partial | stronger-hyp | B6：MonoidalCategory のテンソル関手・associator（原文の向きには逆同型）・自然性・pentagon を忘却すると原文の非単位モノイダル構造を直接得る。単位対象と単位則も持つ圏に仮定を強めた場合。 |
| 2.1.2.1 | none → none |  | B6：現本体・固定Mathlibを再検索。Mathlib の MonoidalCategory は結合子・単位子が同型で、対象と射の厳密な等式を要求しない。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.2.3 | none → none |  | B6：現本体・固定Mathlibを再検索。単位を仮定した冪等元の等式はあるが、半群で冪等かつ左乗法が単射という特徴づけは未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.2.4 | none → none |  | B6：現本体・固定Mathlibを再検索。半群で左右の消去性と冪等性から両側単位を特徴づける宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.2.5 | none → none |  | B6：現本体・固定Mathlibを再検索。単位なし圏の候補 (1, υ) を両側テンソルの充満忠実性で定義する型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.2.9 | none → none |  | B6：現本体・固定Mathlibを再検索。二つの (1, υ) の間の乗法を保存する一意な同型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.2.10 | partial → partial | component | B6：MonoidalCategory の tensorObj・tensorHom と associator の逆同型・pentagon が非単位部分を直接与える。原文の単位 (1,υ) と完全忠実性による提示との比較は含めない。 |
| 2.1.2.17 | partial → none |  | B6：leftUnitor/rightUnitor は選ばれた構造の場。原文は与えられた υ から特定の可換図式を満たす同型を一意に構成する主張で、その υ と場を結ぶ宣言がなく、型の一致だけでは直接の部分結論にならない。 |
| 2.1.2.21 | partial → partial | component | B6：unitors_equal は単位対象上で λ.hom=ρ.hom を直接述べる。原文の三者一致のうち λ=ρ の成分。別に指定した υ との一致は含めない。 |
| 2.1.4.1 | none → none |  | B6：現本体・固定Mathlibを再検索。単位なしのテンソルを対象と射で厳密に保存する関手の定義は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.4.3 | partial → partial | stronger-hyp | B6：LaxMonoidal の μ・naturality・associativity は原文の非単位 lax 構造を直接与える。単位つき圏と ε・単位則まで持つ関手に仮定を強めた場合。 |
| 2.1.4.4 | partial → partial | stronger-hyp | B6：Monoidal の μ/δ と μ_δ・δ_μ は原文の tensorator の可逆性を直接与える。圏も関手も単位つきという追加仮定がある。 |
| 2.1.4.10 | partial → partial | stronger-hyp | B6：IsMonoidal.tensor は原文のテンソル可換正方形そのもの。単位つき lax 関手と単位整合まで仮定した場合に限り、非単位変換の条件を得る。 |
| 2.1.4.16 | partial → partial | stronger-hyp | B6：OplaxMonoidal の δ と自然性・結合則から非単位 colax 構造を直接忘却できる。単位対象・余単位・単位則を持つ場合だけ。 |
| 2.1.4.17 | partial → partial | stronger-hyp | B6：LaxMonoidal.comp の μ X Y=μ G _ _≫G.map(μ F X Y) は原文の合成式。単位つき lax 関手に限る追加仮定がある。 |
| 2.1.4.21 | none → none |  | B6：現本体・固定Mathlibを再検索。Comma の構成はあるが、射影を厳密モノイダルにする構造との全単射は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.5.1 | partial → partial | special | B6：MonObj の one_mul・mul_one は選ばれた m=mul、ε=one について左・右単位の式を与える（unitor の逆を前合成）。任意の非単位代数の任意の候補 ε の述語ではない。 |
| 2.1.5.2 | partial → partial | special | B6：LaxMonoidal の left/right_unitality は ε=ε F として原文の左右の単位式を直接与える。独立に指定する任意の ε を特徴づける定義ではない。 |
| 2.1.5.4 | none → none |  | B6：現本体・固定Mathlibを再検索。別々の左単位射・右単位射の一致を示す宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.5.5 | none → none |  | B6：現本体・固定Mathlibを再検索。独立な左右の単位の存在と両側単位の一意存在の同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.5.6 | none → none |  | B6：現本体・固定Mathlibを再検索。左右の単位条件をコンマ圏上の単位子で特徴づける宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.5.7 | none → none |  | B6：現本体・固定Mathlibを再検索。単位射の条件とコンマ圏の (1, υ) の条件の同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.5.10 | none → none |  | B6：現本体・固定Mathlibを再検索。lax 構造とコンマ圏のモノイダル構造の全単射は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.5.13 | none → none |  | B6：現本体・固定Mathlibを再検索。左単位の性質を単位対象での乗法整合と比較射のモノ性で特徴づける宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.5.23 | none → none |  | B6：現本体・固定Mathlibを再検索。代数の単位射の可逆性・対象のテンソル可逆性・左テンソルの充満忠実性の三条件の同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.1.6.9 | partial → partial | component | B6：IsMonoidal の unit/tensor の二場は、強モノイダル関手間でも原文の射の二条件を直接与える。強関手を対象とする指定の充満部分圏の構成までは含まない。 |
| 2.1.7.1 | partial → partial | component | B6：EnrichedCategory.Hom と id は原文のデータ (2),(4) を直接持つ。comp のテンソル順は原文と逆なので、一般の V での合成則・結合則の一致は数えない。 |
| 2.1.7.10 | partial → partial | component | B6：EnrichedFunctor の obj・map・map_id は原文の対象写像・Hom 写像・恒等射保存を直接与える。非対称な V では合成のテンソル順が逆のため map_comp の原文との比較は未確認。 |
| 2.1.7.11 | partial → none |  | B6：EnrichedCat は逆順の合成規約の豊穣圏の束であり、用意されるのは双圏。原文の豊穣関手を射とする普通圏とその圏則は引用の型から直接得られない。 |
| 2.2.1.7 | none → none |  | B6：現本体・固定Mathlibを再検索。原文は対象・1射・2射を表す文字の慣例。Bicategory は双圏の型で、文字の使い分けに対応する宣言はない。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.2.1.10 | partial → none |  | B6：Bicategory の unitor の場は原文の υ に依存する一意構成・可換図式を述べない。選択された別提示の場の型だけを構成の一部とは数えない。 |
| 2.2.1.14 | partial → partial | component | B6：unitors_equal は恒等1射上の λ.hom=ρ.hom を直接述べる。原文の三者一致のうちこの二者の一致のみで、別に与える υ との一致は含まない。 |
| 2.2.3.4 | none → none |  | B6：現本体・固定Mathlibを再検索。1射を保って2射だけを反転する構成は Opposites の TODO。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.2.4.17 | partial → partial | component | B6：StrictlyUnitaryLaxFunctor.map_id と mapId_eq_eqToHom は原文の strictly unital の定義を直接与える。unital だけを要求する前半の一般の述語は含まない。 |
| 2.2.5.5 | partial → partial | component | B6：id と comp は原文で指定された各種関手の恒等射・合成という構成成分を直接与える。双圏を対象として束ねた普通圏とその厳密な圏則は未確認。 |
| 2.2.6.1 | none → none |  | B6：現本体・固定Mathlibを再検索。双圏間の擬関手が等式で両側逆を持つという2Catでの同型の定義は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.2.6.6 | none → none |  | B6：現本体・固定Mathlibを再検索。lax 関手の厳密な逆から比較2射の可逆性を導く命題は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.2.6.7 | none → none |  | B6：現本体・固定Mathlibを再検索。合成する各1射対にその合成の自己同型を与える twisting cochain の型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.2.6.8 | none → none |  | B6：現本体・固定Mathlibを再検索。twisting cochain による横合成と構造2射の取り替えは未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.2.7.1 | partial → partial | stronger-hyp | B6：Strict の id_comp/comp_id と left/rightUnitor_eqToIso から原文の厳密単位性が直接得られる。associator も等式由来とする追加仮定がある。 |
| 2.2.7.2 | none → none |  | B6：現本体・固定Mathlibを再検索。厳密単位性と、恒等1射の等式・υ・恒等を二つ含む結合子の三条件の同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.2.7.7 | none → none |  | B6：現本体・固定Mathlibを再検索。任意の双圏から厳密単位的な双圏への、単位も厳密な同型の構成は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.2.8.1 | none → none |  | B6：現本体・固定Mathlibを再検索。局所離散な双圏への関手はあるが、それを表現する粗ホモトピー圏の普遍性は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.2.8.2 | none → none |  | B6：現本体・固定Mathlibを再検索。各 Hom 圏の全2射に沿う連結成分で1射を割った普通圏は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.2.8.3 | none → none |  | B6：現本体・固定Mathlibを再検索。粗ホモトピー圏の指定の射影に沿う関手の一意因子化は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.2.8.4 | none → none |  | B6：現本体・固定Mathlibを再検索。局所離散化に対する粗ホモトピー圏の左随伴は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.2.8.12 | partial → none |  | B6：Pith と inclusion は可逆2射に制限する双圏であり、原文の1射の同型類を Hom とする普通圏 hPith ではない。商と合成の降下が別に要る。 |
| 2.2.8.17 | partial → partial | stronger-hyp | B6：Equivalence の hom に対して inv・unit・counit が原文の両側ホモトピー逆を直接与える。指定1射をこのデータの hom とし、triangle も持つ場合に限る。hPith の IsIso との iff は含めない。 |
| 2.2.8.24 | partial → partial | component | B6：IsLocallyGroupoid の ∀b c, IsGroupoid(b⟶c) は原文の全2射が可逆という結論成分。全1射が同値である条件は含まない。 |
| 2.2.8.27 | none → none |  | B6：現本体・固定Mathlibを再検索。Pith は可逆2射のみの制限。1射も同値に制限する core 双圏は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.1.1 | none → none |  | B6：現本体・固定Mathlibを再検索。厳密単位的 lax 関手の型はあるが、双圏に対する Duskin nerve の単体集合は TODO。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.1.9 | none → none |  | B6：現本体・固定Mathlibを再検索。対象・辺・2射と四頂点での整合から Duskin 単体を一意に組み立てる宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.1.10 | none → none |  | B6：現本体・固定Mathlibを再検索。Duskin nerve の境界制限が次元4以上で全単射、次元3で単射という宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.2.1 | none → none |  | B6：現本体・固定Mathlibを再検索。局所亜群性の型はあるが、Duskin nerve の準圏性との同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.2.3 | none → none |  | B6：現本体・固定Mathlibを再検索。指定の連続3頂点上で固定した2単体に対する内角充填の述語は未発見。Quiver.IsThin は Hom の高々一意性。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.2.5 | none → none |  | B6：現本体・固定Mathlibを再検索。Duskin nerve の2単体の薄さと対応2射の可逆性の同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.2.7 | none → none |  | B6：現本体・固定Mathlibを再検索。Duskin nerve の退化2単体の薄さを示す宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.2.8 | none → none |  | B6：現本体・固定Mathlibを再検索。双圏の擬関手による Duskin nerve の薄い2単体の保存は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.3.1 | none → none |  | B6：現本体・固定Mathlibを再検索。指定2面の可逆2射から Duskin の内角の一意充填を得る宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.3.2 | none → none |  | B6：現本体・固定Mathlibを再検索。次元3・4の指定内角の充填から比較2射の可逆性を導く宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.4.1 | none → none |  | B6：現本体・固定Mathlibを再検索。Duskin nerve の単体写像と厳密単位的 lax 関手の全単射は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.4.5 | none → none |  | B6：現本体・固定Mathlibを再検索。薄い2単体を保つ nerve 写像と擬関手の全単射は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.4.6 | none → none |  | B6：現本体・固定Mathlibを再検索。Duskin nerve のホモトピー圏と粗ホモトピー圏との比較は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.5.1 | partial → none |  | B6：Path は任意 LinearOrder の端点付き部分集合で有限性を要求せず、射も包含で原文の逆包含と反対。compFunctor の和集合は類似模型の部品であり原文の有限鎖双圏を直接構成しない。 |
| 2.3.5.4 | none → none |  | B6：現本体・固定Mathlibを再検索。各比較可能対を端点だけの鎖に送り、逆包含を合成制約に使う指定の lax 関手は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.5.6 | none → none |  | B6：現本体・固定Mathlibを再検索。T_Q に沿う制限による厳密関手と厳密単位的 lax 関手の全単射は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.3.5.7 | none → none |  | B6：現本体・固定Mathlibを再検索。局所的 nerve を取った双圏の coherent nerve と Duskin nerve の同型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.1.3 | partial → partial | special | B6：homEquiv' は n=0 で Hom 集合を sHom の0単体に同一視する成分を直接与える。全次数での圏と単体的演算の一式は未確認。 |
| 2.4.1.6 | partial → partial | component | B6：sHom の0単体を homEquiv' で指定し Edge を取ると、d₁=f,d₀=g という原文のホモトピーのデータを直接表す。専用の名前付き述語や合成法は含まない。 |
| 2.4.1.8 | partial → none |  | B6：simplicialNerve_quasicategory は局所 Kan 性を入力仮定として使う定理。その仮定から局所 Kan の定義を表す宣言を取り出せるわけではなく、結論は nerve の準圏性という別の主張。 |
| 2.4.1.13 | none → none |  | B6：現本体・固定Mathlibを再検索。一般の EnrichedCat は双圏。Cat_Δ の小極限と小余極限のインスタンスは未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.3.1 | partial → none |  | B6：原文は逆包含順の有限鎖の nerve。SimplicialThickening と pathInteriorEquiv は包含順の別模型で、次数・合成を保つ原文との比較がないため、その模型の同型だけでは partial にしない。 |
| 2.4.3.5 | partial → none |  | B6：SimplicialNerve の定義域は包含順の thickening。原文の逆包含 Path による関手集合との比較が単体構造まで必要で、似た nerve の定義だけでは原文の構成を直接得ない。 |
| 2.4.4.1 | none → none |  | B6：現本体・固定Mathlibを再検索。S から coherent nerve への写像を表現する path 圏の普遍性の型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.4.2 | none → none |  | B6：現本体・固定Mathlibを再検索。任意の単体集合 S からの Path[S] の構成は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.4.3 | none → none |  | B6：現本体・固定Mathlibを再検索。任意 S の path 圏の存在は未発見。coherentResolution の値域は SSet。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.4.4 | none → none |  | B6：現本体・固定Mathlibを再検索。coherent nerve の左随伴 ℭ : SSet → Cat_Δ は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.4.7 | none → none |  | B6：現本体・固定Mathlibを再検索。自由パス圏はあるが、グラフから定数単体圏への指定写像が path 圏の普遍性を満たす宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.4.9 | none → none |  | B6：現本体・固定Mathlibを再検索。非退化単体と端点を指定した減少部分集合列の組 E(S,m) は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.4.10 | none → none |  | B6：現本体・固定Mathlibを再検索。任意 S の path 圏からの豊穣関手を E(S,m) によるデータで特徴づける定理は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.4.13 | none → none |  | B6：現本体・固定Mathlibを再検索。1骨格からの因子化と、自由パス圏から Path[S]₀ への同型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.4.15 | none → none |  | B6：現本体・固定Mathlibを再検索。一般の半順序 Q の Path[Q] が N(Q) に対し普遍性を満たす定理は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.4.16 | partial → none |  | B6：pathPrefix/pathSuffix は経路の部分集合の切り分けという証明部品。原文は指定の u が三つの条件を満たす主張で、いずれの条件もこれらの型の結論ではない。 |
| 2.4.4.18 | none → none |  | B6：現本体・固定Mathlibを再検索。途中点の上下の path 圏からの豊穣圏の押し出しの比較は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.4.20 | none → none |  | B6：現本体・固定Mathlibを再検索。上下の押し出しを Path[Q] に入れる関手の一意な左逆は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.5.4 | partial → none |  | B6：pathInteriorNerveIso は包含順の path と内部点集合の包含順の nerve の同型。原文の逆包含から補集合で得る特定同型・合成式との比較を含まないため別模型として none。 |
| 2.4.5.5 | partial → partial | component | B6：cubeBoundary の一定座標条件は全ての面の和という原文の境界を直接表す。hollowCube は指定座標の下面を欠く側だけで、二種類の hollow cube の両方は含まない。 |
| 2.4.5.8 | partial → none |  | B6：pathThrough/pathFaceIso は包含順の経路部分の部品で、hornHollowHom_extension の結論も Hom への延長。原文の Path[Λ]→Path[Δ] という特定関手の (a)〜(c) は直接述べない。 |
| 2.4.5.9 | partial → none |  | B6：hornCompositionHom_composition_overlap は内角から作る Hom の面の整合性。任意の E と D の豊穣関手の延長集合の全単射とは対象・結論が異なる証明部品。 |
| 2.4.5.10 | partial → none |  | B6：hornFilledFunctor と面の等式は包含順模型の充填関手を作るが、逆包含模型の指定の λ₀ とその制限条件を同一視する宣言がない。原文の全単射の方向とはまだ数えない。 |
| 2.4.5.11 | partial → partial | direction | B6：intervalEndpoint_zero_trivialKanFibration と kanIntervalEvaluation_trivialKanFibration は Kan X から各端点評価が自明 Kan fibration となる向き。各評価の性質から Kan 性を得る逆向きは含まない。 |
| 2.4.5.12 | partial → partial | component | B6：hollowCube_extension は指定座標の下面を欠く hollow cube から Kan X への任意の写像の延長を直接与える。原文の二つの延長のうち上面を含む側のみ。 |
| 2.4.6.1 | none → none |  | B6：現本体・固定Mathlibを再検索。個々の sHom の π₀ は使われるが、それらを Hom とする単体圏のホモトピー圏の構成は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.6.7 | none → none |  | B6：現本体・固定Mathlibを再検索。成分の比較補題はあるが、離散的な単体圏への関手を hC で一意に因子化する宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.6.8 | none → none |  | B6：現本体・固定Mathlibを再検索。普通圏を定数単体圏とする包含への左随伴 h は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.6.9 | partial → none |  | B6：頂点・辺の全単射とホモトピー類の等式は比較を作る材料だが、原文の特定の U による圏同型の部分結論ではない。包含順/逆包含の nerve の比較も必要。 |
| 2.4.6.10 | partial → none |  | B6：coherentTriangleMappingEdge は長辺 h から合成 f≫g への辺で、原文は合成から h へのホモトピー。一般の Hom は Kan とも仮定しないので向きを反転できず、定値合成三角形だけも指定全単射を与えない。 |
| 2.4.6.12 | none → none |  | B6：現本体・固定Mathlibを再検索。内角の空洞立方体の補題はあるが、境界包含に沿う Path の全 Hom と境界立方体の表示は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.6.13 | partial → none |  | B6：次元2の候補も長辺から合成への逆向きの辺であり、原文の立方体境界の特定の λ₀ に沿う延長と同一視できない。次元特殊化だけではこの差は解消しない。 |
| 2.4.6.16 | none → none |  | B6：現本体・固定Mathlibを再検索。豊穣 Hom のホモトピー圏を Hom 圏とする h₂C は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.6.21 | none → none |  | B6：現本体・固定Mathlibを再検索。h₂C の指定写像に沿う単体関手の一意因子化は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.7.5 | none → none |  | B6：現本体・固定Mathlibを再検索。Coxeter 群内の braid word の等式はあるが、二乗関係を外した Artin 群と正モノイドの構成は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.7.6 | none → none |  | B6：現本体・固定Mathlibを再検索。非単位元の自由モノイドに、積と長さの加法性で決まる細分順序を入れた単体モノイドは未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.7.9 | none → none |  | B6：現本体・固定Mathlibを再検索。有限 Coxeter 系の正 braid モノイドに対する Deligne の主張は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.7.10 | none → none |  | B6：現本体・固定Mathlibを再検索。群の普通 nerve はあるが、長さ加法性で切り出した B°W は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.7.11 | none → none |  | B6：現本体・固定Mathlibを再検索。長さ加法的な語を区間ごとの積へ送り、BM(W) の coherent nerve に入れる写像は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.7.12 | none → none |  | B6：現本体・固定Mathlibを再検索。BM(W) が B°W の path 圏を表す普遍性は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.4.7.13 | none → none |  | B6：現本体・固定Mathlibを再検索。Path[B°W] の自己射単体モノイドと正 braid モノイドの弱ホモトピー同値は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.5.0.10 | partial → none |  | B6：Cochain と linearHomComplex は余鎖規約、homComplex もその別名。鎖規約の符号付き微分との次数反転の比較がなく、原文の mapping chain complex を直接得ない。 |
| 2.5.1.1 | partial → none |  | B6：IsStrictlyGE/LE の引用は余鎖複体についての述語。鎖複体への再添字の比較を欠くため原文の二つの充満部分圏の直接の部分構成とは数えない。 |
| 2.5.1.3 | partial → partial | component | B6：HomologicalComplex.cycles は指定次数の outgoing 微分の核を直接構成し、鎖規約でも原文の Z_n を与える。image による B_n とその包含の一式は引用に含まない。 |
| 2.5.1.10 | none → none |  | B6：現本体・固定Mathlibを再検索。各項射影かつ有界の複体の K 射影性はあるが、非輪状の場合に複体圏の全エピに切断を与える宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.5.1.12 | partial → none |  | B6：tensorObj の複体性と d_eq=D₁+D₂ だけでは、原文の任意の x,y 上の指定 Leibniz 式を満たすという存在の結論を直接述べない。一意性の証明部品でもあるため none。 |
| 2.5.3.1 | partial → none |  | B6：Simplex/SimplexData は HA の余鎖符号規約。原文の削除項と合成項の符号方程式を満たす組への変換がなく、raw データの射影だけは原文の単体集合の構成成分としない。 |
| 2.5.3.7 | partial → none |  | B6：dgNerve は HA 規約の Simplex の単体集合。原文の方程式に従う N_n と各単体写像の比較がないため、別規約の nerve を直接の部分結論としない。 |
| 2.5.4.10 | partial → none |  | B6：equivalence/toH0 は現行 HA 規約の dg nerve と H⁰ の比較。原文の符号規約での nerve と対応づける宣言を欠き、圏同値を圏同型の component と数える前に対象の比較が要る。 |
| 2.5.5.1 | partial → partial | special | B6：alternatingFaceMapComplex は全ての面の交代和を微分とする ChainComplex を直接構成する。半単体対象一般ではなく、退化も持つ単体アーベル群に入力を制限した場合。 |
| 2.5.5.5 | partial → none |  | B6：degenerateIntegralChains は Q∞ の像という構成。原文の退化写像の像で生成した subgroup との同一視は annihilates_iff だけでは直接の型の結論でなく、比較の議論が要る。 |
| 2.5.5.6 | partial → none |  | B6：Q∞ の像が複体という事実はあるが、原文の指定部分群 D_n の微分による保存と、像模型の比較がない。退化部分を表す別構成の複体性だけは数えない。 |
| 2.5.5.7 | partial → none |  | B6：normalizedMooreComplex は高次面の核の共通部分を用いる第二構成。原文の指定の商 C/D と同じ対象とする宣言なしに第一構成の partial としない。 |
| 2.5.5.11 | partial → none |  | B6：homotopyPInftyToId と正規化ホモトピー同値は核型正規化の模型についての結果。原文の商射 C→C/D と同一の射である比較がなく、その擬同型性の直接の一部ではない。 |
| 2.5.5.15 | partial → partial | component | B6：SSetPair.chainComplexFunctor は原文の相対非正規化鎖複体 C(S,S′;Z) の構成成分を与える。核型の正規化相対複体とのホモロジー比較や商型の N の同定は含めない。 |
| 2.5.6.3 | partial → none |  | B6：Γ は非負次数複体上の別の Dold–Kan 模型。StandardSimplex も dg Hom に限定した鎖写像模型であり、原文の任意 M に対する指定鎖写像 Hom からの K の構成との比較がない。 |
| 2.5.6.9 | partial → partial | special | B6：const は任意の集合 G に対して原文が明記する K(G,0) を、nerve(SingleObj G) は群 G に対して明記する K(G,1) を直接構成する。一般の可換群の全 n は含まない。 |
| 2.5.6.10 | partial → none |  | B6：standardSimplexEquiv は dg Hom の単体の表現の同値。最上生成元の評価による v、退化の消滅、商への因子化という原文の余単位の結論を型に持たない。 |
| 2.5.6.11 | partial → none |  | B6：DoldKan.equivalence の抽象 Hom 全単射は核型 N と Γ のもの。原文の指定 K・指定余単位 v と比較されていないので、非負次数への限定だけでは同じ θ の主張にならない。 |
| 2.5.6.12 | partial → none |  | B6：DoldKan.equivalence は核型 N と Γ の同値。原文の鎖写像 Hom による K と一致させる宣言がなく、指定 K を右随伴とする主張の特殊化とは数えない。 |
| 2.5.6.13 | none → none |  | B6：現本体・固定Mathlibを再検索。単体集合の正規化鎖複体と Dold–Kan の部品はあるが、ℤ 次数の K を右随伴として組んだ宣言は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.5.6.16 | partial → none |  | B6：Γ₀.splitting の summand は構成から選んだ成分。原文の高次面の核 Ñ_m とその包含を退化写像で送る特定 f との同一視が必要で、Splitting の型だけは別模型の材料。 |
| 2.5.6.17 | partial → none |  | B6：splitMonoInclusionOfMooreComplexMap は核型 Ñ→C の分裂単射。原文の指定の合成 Ñ→C→C/D が同型、あるいは C=Ñ⊕D という補空間の同定を直接述べない。 |
| 2.5.6.21 | partial → partial | component | B6：homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex は原文の核型 Ñ と C の包含を hom とするホモトピー同値。そこから包含のホモロジー同型という第二の結論成分が直接得られる。商射・一般の D の非輪状性は含まない。 |
| 2.5.6.23 | partial → none |  | B6：equivalence と connectiveHomComplex の各次数同型は指定の余単位 v についての主張ではない。K の模型と v の比較を欠くため同型の存在だけを原文の component にしない。 |
| 2.5.7.1 | partial → none |  | B6：normalizedShuffle は核型正規化での鎖写像。原文の商型正規化の指定の shuffle と比較されず、射の存在だけでは原文の一意性・自然性・次数0条件の一部を直接得ない。 |
| 2.5.7.8 | partial → none |  | B6：σ_rawBilinear_left/right は単体集合由来の shuffle が正規化への射影後に消える式。原文の C(A⊗B) における退化部分群への所属を結論せず、対象と商の比較が必要。 |
| 2.5.7.9 | partial → none |  | B6：normalizedShuffle は核型 Ñ に非正規化 shuffle を挟んだ射。商型 N と指定の商射の可換図式を比較する宣言がなく、同じ主張の部分構成とは数えない。 |
| 2.5.7.10 | partial → none |  | B6：projectedRingShuffleProduct は shuffle を環の乗法で合成した内部積。原文の A⊗B への外部積の結合・対称・単位則を直接述べず、Barratt–Eccles の限られた対象の式も対象比較が必要。 |
| 2.5.7.14 | partial → none |  | B6：normalizedEZHomotopy/ezHomotopy は AW≫shuffle の合成のホモトピー。一方の合成だけの式は指定 EZ 自身のホモロジー同型性を直接与えず、核型/商型の比較も必要。 |
| 2.5.7.15 | partial → none |  | B6：chainMap は EZ の候補鎖写像の構成で、擬同型性の結論成分を持たない。原文の命題の証明部品にとどまる。 |
| 2.5.7.17 | none → none |  | B6：現本体・固定Mathlibを再検索。相対鎖複体と絶対 shuffle はあるが、指定の積の対への相対 EZ 擬同型は未発見。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.5.8.4 | partial → partial | component | B6：alexanderWhitney_naturality は単体 Z 加群の二変数に関する原文の非正規化 AW の自然性を直接述べる。colax 構造の自然性成分のみで、一般の余単位・余結合は含まない。 |
| 2.5.8.5 | partial → none |  | B6：aw_degeneracy_not_mono は切断した単体写像のいずれかが退化する組合せ補題。restrictToNormalized も核型への制限であり、原文の指定 K_* への像の所属を直接述べない。 |
| 2.5.8.6 | partial → none |  | B6：normalizedAlexanderWhitney は核型正規化による射。原文の商射による可換図式とその一意性を述べず、商型 N への対象比較が必要。 |
| 2.5.8.7 | partial → none |  | B6：normalizedAlexanderWhitney_naturality は核型 Ñ での式、diagonal の余結合・余単位は対角を合成した別の射の式。原文の商型 N の一般の colax 構造の直接の成分とは数えない。 |
| 2.5.8.9 | none → none |  | B6：現本体・固定Mathlibを再検索。原文は shuffle の後の AW が厳密に恒等。normalizedEZHomotopy は逆順の合成のホモトピーなので関連引用を除く。 関連する一般構成だけから原文の指定対象・射の結論を直接得る宣言は未確認。 |
| 2.5.8.11 | partial → none |  | B6：normalizedEZHomotopy は合成 AW≫shuffle のホモトピーだけで、指定 AW 自身の擬同型性を直接述べない。別の合成の逆性と商型への比較が必要。 |
| 2.5.9.1 | partial → none |  | B6：standardAW と awData_assoc/unit は dg Hom を合成先とする演算とその法則。原文の K(X)×K(Y)→K(X⊠Y) とは値域も異なり、任意の鎖複体の lax 構造の直接の部分結論ではない。 |
| 2.5.9.6 | partial → partial | component | B6：cubeFlag は番号付けた有限集合で空集合から1点ずつ増やす最大旗の単体を直接構成する。原文に記された旗の構成成分のみで、正規化整数基本鎖と自由推移性の一式は含まない。 |
| 2.5.9.9 | partial → none |  | B6：coherentCubeHom/Component は包含順 path の Hom からの評価。原文の逆包含と補集合の座標での基本鎖の向きとの比較を欠き、同じ σ の評価とは直接いえない。 |
| 2.5.9.10 | partial → none |  | B6：coherentComparison は HA 符号規約の dg nerve と包含順 nerve の比較。原文の両模型への自然な比較を欠くため、対象の一致だけを指定 Z の一意存在の component としない。 |
| 2.5.9.12 | partial → partial | component | B6：cubeFaceMap は指定座標を0/1に固定する原文の二つの面の包含を直接構成する。原文の基本鎖をこれで送った整数鎖としての比較は含まない。 |
| 2.5.9.13 | partial → partial | special | B6：cubeFlag_boundary_sum は任意の加法可換群値 F に対する符号和。F を正規化自由鎖への生成元写像に取ると原文の境界式が直接得られる。型の card=n+2、すなわち次元2以上に限り、0・1次元は含まない。 |
| 2.5.9.16 | partial → none |  | B6：cubeEvaluation_AW_comp は dg 合成後の評価の等式。原文の普遍的な正規化整数鎖内の AW の等式と異なり、合成評価から元のテンソル鎖の等式を回収する宣言がない。 |
| 2.5.9.18 | partial → none |  | B6：coherentComparison の準圏同値・充満忠実性は HA/包含順模型の射についての主張。原文の特定の Z との比較が未確認で、自明 Kan fibration の部分としても数えない。 |

## 検査

原文は Kerodon 公式小節の各項目Tagで照合。none は現本体・ロックしたMathlibを再検索し、近隣項目のソース・双対/限定版の候補も照合した。Archiveの宣言をown・partialの根拠にはしていない。宣言の存在と型はソースでの確認で、kernel確認ではない。

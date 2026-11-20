-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Grothendieck
import SerrePositivity.CategoryTheory.Enriched.TensorCotensor
import SerrePositivity.HomotopicalAlgebra.Enriched.DerivedMapping
import SerrePositivity.HomotopicalAlgebra.Enriched.TensorCotensor
import SerrePositivity.HomotopicalAlgebra.Localization.EnrichedExistence
import SerrePositivity.HomotopicalAlgebra.Localization.ModelComparison
import SerrePositivity.HomotopicalAlgebra.Localization.ModelExistence
import SerrePositivity.HomotopicalAlgebra.Localization.QuillenCriterion
import SerrePositivity.HomotopicalAlgebra.Localization.UniversalProperty
import SerrePositivity.HomotopicalAlgebra.Monoidal.ModelCategory
import SerrePositivity.HomotopicalAlgebra.Monoidal.QuillenBifunctor
import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction
import SerrePositivity.HomotopicalAlgebra.Quillen.FibrantCriterion
import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT A.3 Simplicial Categories" =>
%%%
number := false
tag := "htt-A-3"
%%%

HTT A.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

*05-gamma-bridges.html — 4. γ4：Quillen 随伴 ⇒ ∞ 随伴*

設定：simplicial モデル圏 $`\mathcal C,\mathcal D`（SM7 を固定）と、豊穣 Hom の同型と合成の両立を明示した simplicial Quillen 随伴 $`F\dashv G`。cofibrant かつ fibrant な対象（cf 対象）がなす単体的圏は SM7 により局所 Kan なので、γ1 によりその coherent nerve $`N^{hc}(\mathcal C^{cf})` は quasicategory になる。

\`\`\`text
lemma quillenCfDerivedAdjunction\_exists :
    ∃ H : SSet.Homotopy (𝟙 (SimplicialNerve (CofibrantFibrantObjects C)))
      (quillenCfLeftDerived R adj fibD e SC SD ≫ quillenCfRightDerived R adj SC SD cofC),
      ∃ a : QCatAdjunction (quillenCfLeftDerived ...) (quillenCfRightDerived ...),
        a.unitHom = SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)
\`\`\`

場所：HomotopyLimits/QuillenCfDerivedAdjunction。導来関手 $`\mathbb LF`、$`\mathbb RG` が cf nerve の間の ∞ 随伴（第 4 章の \`QCatAdjunction\`）をなし、その単位は指定したホモトピーから来る。系として、右導来関手は ∞ 極限を保つ（\`quillenCfRightDerived\_hasLimit\_postcomp\`、HomotopyLimits/QuillenCfDerivedLimits。一般の「右随伴は極限を保つ」\`hasLimit\_postcomp\_of\_adjunction\` の適用）。

*証明の方針*（HTT 5.2.4.6）：$`\Delta^1` 上の「cf 対応圏」を作る。両端の fiber が $`\mathcal C^{cf}` と $`\mathcal D^{cf}` で、二つをつなぐ混合 Hom は $`\mathrm{Map}(FX,Y)\cong\mathrm{Map}(X,GY)` である。その coherent nerve $`\to\Delta^1` が cocartesian かつ cartesian な fibration であることを示し（HomotopyLimits/QuillenCfBifibration）、cocartesian 辺に沿った transport と cartesian 辺に沿った transport を導来関手と比較する。そのうえで、写像空間の同値から随伴を組み立てる（Quillen\*、34 ファイル）。

# A.3.1 Enriched and Monoidal Model Categories

%%%
number := false
tag := "htt-A-3-1"
%%%

:::definition "htt_A_3_1_1" (lean := "SerrePositivity.Quillen.IsQuillenBifunctor")
*HTT 定義 A.3.1.1*　左キレン双関手の押出し積条件（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=869)）。対応表の状態：一部（component）。

*主張*　左 Quillen 二変数関手は、各変数で小余極限を保ち、二つの余ファイブレーションから作る押し出し積を余ファイブレーションに移す。

KB-W2原文・型再照合：仮定：三つの抽象モデル圏と二変数 functor（HTT と一致）。結論：cofibration 二つの pushout-product が cofibration で、片方が trivial なら trivial という (a) を正確に表す。IsQuillenBifunctor 自体は (b) の各変数での小余極限保存を課さず、その条件は別の adjunction/PreservesColimits として渡す必要がある。

押し出し積の始域は $`F(A',B)\sqcup_{F(A,B)}F(A,B')`、終域は $`F(A',B')` である。入力のどちらか一方が自明なら、この比較射も弱同値となる。

:::

:::definition "htt_A_3_1_2" (lean := "SerrePositivity.Quillen.MonoidalModelCategory, SerrePositivity.Quillen.unitAxiom_of_cofibrant_unit")
*HTT 定義 A.3.1.2*　閉モノイダル模型と単位公理（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=869)）。対応表の状態：一部（component）。

*主張*　モノイダルモデル圏は、テンソルが左 Quillen 二変数関手で、単位が余ファイブラントであり、テンソルが両側で閉じているモデル圏である。

KB-W2原文・型再照合：仮定：閉モノイダル構造を外から与え、さらに原典どおり単位の cofibrancy を指定（HTT と一致）。結論：tensor の Quillen 条件と単位の identity replacement による弱い unit axiom を得る。native MonoidalModelCategory という一つの class は閉性も単位 cofibrancy も要求せず、原典の三条件をそのまま束ねた定義ではない。tensor の Quillen 条件の成分と、元の強い単位条件から弱い条件への方向を記録する。

閉性で二種類の内部 Hom が得られる。テンソルと内部 Hom の随伴を使うと、押し出し積条件をファイブレーションの条件に移し替えられる。

:::

:::proposition "htt_A_3_1_3" (lean := "SerrePositivity.Quillen.HasUnitAxiom, SerrePositivity.Quillen.UnitReplacementAxiom")
*HTT 注意 A.3.1.3*　弱めた単位公理という別の慣習（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=869)）。対応表の状態：本体にある。

*主張*　モノイダルモデル圏の定義で、単位の余ファイブラント性を弱める流儀もある。

仮定：モノイダルモデル圏の単位に cofibrant replacement を指定（原典で触れる弱めた規約）。結論：cofibrant な X への左右の tensor が弱同値になる条件を定義する。unit 自体の cofibrancy を要求しない規約の具体形に一致する。

この本の定義は、単位対象自身が余ファイブラントであることを要求する。単位について条件が異なる文献を使うときには、どちらの定義かを確認する。

:::

:::proposition "htt_A_3_1_4" (lean := "SerrePositivity.SimplicialModel.simplicial_monoidalModel, SerrePositivity.SimplicialModel.simplicial_isQuillenBifunctor")
*HTT 例 A.3.1.4*　単体集合のモノイダル模型の整合性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=869)）。対応表の状態：一部（stronger-hyp）。

*主張*　単体集合は、直積と Kan モデル構造によってモノイダルモデル圏になる。

KB-W2原文・型再照合：仮定：ModelCategory SSet と cofibrations=mono、fibrations=horn-RLP を追加（証明済みの具体的 instance なし。HT-KQ の引用モデルは sorryAx を含む）。結論：同じ Cartesian tensor の Quillen 条件と unit axiom を得る。モデル存在からの無条件な assertion にはならない。

単位は $`\Delta^0` で余ファイブラントであり、内部 Hom は単体集合の冪対象で与えられる。このテンソルに押し出し積条件を適用できる。

:::

:::definition "htt_A_3_1_5" (lean := "SerrePositivity.Enriched.TensorCotensor, SerrePositivity.Quillen.IsQuillenBifunctor")
*HTT 定義 A.3.1.5*　豊穣模型の tensor と cotensor（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=869)）。対応表の状態：本体にある。

*主張*　モノイダルモデル圏 $`S` 上の豊穣モデル圏は、$`S` によるテンソルと余テンソルを備え、テンソル $`A\times S\to A` が左 Quillen 二変数関手となる豊穣圏である。

仮定：既存の S-enriched ordinary category A とそれぞれの抽象モデル構造（HTT と一致）。結論：TensorCotensor の二つの parametrized adjunction は HomA(S⊗X,Y)≃HomS(S,Map(X,Y))≃HomA(X,Y\^S) を与え、tensor に IsQuillenBifunctor を課すと原典の二条件になる。S のモノイダルモデル条件は外から指定する。

基礎にモデル構造を備えた上で豊穣構造との両立を要求する。$`S` が Kan モデル構造を持つ単体集合の圏の場合を単体的モデル圏という。

:::

:::proposition "htt_A_3_1_6" (lean := "SerrePositivity.Enriched.tensor_iff_cotensor_model, SerrePositivity.Enriched.tensor_iff_mapping_model")
*HTT 注意 A.3.1.6*　豊穣 tensor の二つの持上げ判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=869)）。対応表の状態：本体にある。

*主張*　豊穣モデル圏のテンソルの Quillen 条件は、豊穣写像対象の相対比較射、または余テンソルの相対比較射がファイブレーションとなることでも表せる。

仮定：同じ tensor/cotensor と Hom の表現随伴、および抽象モデル構造（HTT と一致）。結論：tensor の pushout-product 条件 iff mapping pullback-Hom 条件、および iff cotensor pullback 条件をそれぞれ得る。二つの (2′)(2″) と一致。

それぞれ一方の入力に余ファイブレーション、もう一方にファイブレーションを取る。出力は対応する二つの写像を底で合わせた引き戻しへの射であり、どちらかの入力が自明なら出力も自明になる。

:::

:::proposition "htt_A_3_1_8" (lean := "SerrePositivity.Enriched.mapping_isFibrant")
*HTT 注意 A.3.1.8*　cofibrant 源と fibrant 標的の写像対象（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=872)）。対応表の状態：一部（component）。

*主張*　単体的モデル圏で余ファイブラントな $`X` とファイブラントな $`Y` の間の単体的写像対象は Kan 複体で、その連結成分はホモトピー圏の射に対応する。

KB-W2原文・型再照合：仮定：TensorCotensor SSet C と Quillen compatibility、ModelCategory SSet が標準 horn-RLP を fibrations とする（証明済み具体的 instance なし）。結論：X cofibrant,Y fibrant なら元の enriched mapping object は fibrant、標準 fibrations の下では Kan になるという最初の成分に一致。π0 Map(X,Y) と同じ hC の Hom の指定全単射はこの型に含まない。

終対象へのファイブレーションと始対象からの余ファイブレーションを相対写像対象の条件に入れると、Kan 性が得られる。道で同一視することで導来射の集合になる。

:::

# A.3.3 Model Structures on Diagram Categories

%%%
number := false
tag := "htt-A-3-3"
%%%

:::proposition "htt_A_3_3_11" (lean := "CategoryTheory.enrichedFunctorTypeEquivFunctor")
*HTT 注意 A.3.3.11*　集合豊穣関手と通常関手の同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=894)）。対応表の状態：一部（special）。

*主張*　通常圏の Hom 集合を単位の余積で豊穣化すれば、通常の図式圏はその豊穣関手圏と同一視でき、この比較は入射的モデル構造とホモトピー右 Kan 拡張を保つ。

KB-W2原文・型再照合：仮定：S=Type、通常圏 C の Hom による集合豊穣構造に限定（Lean が強い特殊形）。結論：Type-enriched functor と 集合豊穣構造が定める通常圏上の functor の実際の equivalence を構成する。原典の通常関手と自由 S-enrichment からの enriched functor の対応の集合値部分に一致するが、任意の S の copower 基底変更および injective model の比較はない。

対象はそのままとし、各 Hom 集合 $`T` を $`\coprod_{t\in T}1_S` に移す。こうすると通常の図式の自然性が豊穣側の条件に対応する。

:::

# A.3.5 Homotopy Colimits of S-Enriched Categories

%%%
number := false
tag := "htt-A-3-5"
%%%

:::definition "htt_A_3_5_11" (lean := "CategoryTheory.Grothendieck, CategoryTheory.Grothendieck.Hom, CategoryTheory.Grothendieck.toTransport, CategoryTheory.Grothendieck.forget")
*HTT 定義 A.3.5.11*　集合豊穣の場合の Grothendieck 構成（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=913)）。対応表の状態：一部（special）。

*主張*　半順序で添字付けた豊穣圏の図式の Grothendieck 構成では、対象は $`(a,c)` で、$`a\le b` の場合の写像対象は $`c` を $`b` に移した後の写像対象である。

KB-W2原文・型再照合：仮定：S=Type、通常圏の Hom による集合豊穣と半順序 A に限定（Lean が強い特殊形）。結論：対象は (a,C)、Hom は a→a′ と MapCa′(p(C),C′) の組、半順序の基底射は一意なので原典の二場合の式に一致。toTransport は identity fiber の W(p) の射、forget は r を与える。一般の S の enrichment と後段の反転比較は含まない。

$`a\le b` が成り立たない場合には写像対象を始対象とする。移送先の恒等射による標準射を反転するための類 $`W(p)` を指定でき、各 $`a` 以下の部分から $`C_a` への比較はこの類を恒等射に移す。

:::

# A.3.7 Localizations of Simplicial Model Categories

%%%
number := false
tag := "htt-A-3-7"
%%%

:::corollary "htt_A_3_7_2" (lean := "SerrePositivity.Quillen.IsLeftQuillen.map_cofibrations, SerrePositivity.Quillen.isRightQuillen_of_isLeftQuillen, SerrePositivity.Quillen.isFibrant_obj")
*HTT 系 A.3.7.2*　キレン随伴からの cofibration と fibrant 保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=926)）。対応表の状態：一部（direction）。

*主張*　終域が左固有な単体的モデル圏の間の単体的随伴は、左随伴が余ファイブレーションを保ち、右随伴がファイブラント対象を保つとき、かつそのときに限って Quillen 随伴である。

KB-W2原文・型再照合：仮定：抽象モデル圏の実際の随伴 L⊣R と left Quillen L（元の (1)、simplicial 条件を不要にする弱い仮定）。結論：L の cofibration 保存と R の fibrant object 保存を得るので (1)⇒(2) に一致。逆向きは native isLeftQuillen\_of\_fibrant\_test が fibrant 対象間の fibration 保存も要求し、fibrant objects 保存のみからは証明していない。

単体的な随伴なので、豊穣写像対象によるファイブレーションの判定を左右で比較できる。判定には右随伴による全ファイブレーションの保存を直接仮定せず、対象での保存を使う。

:::

:::proposition "htt_A_3_7_3" (lean := "SerrePositivity.Bousfield.exists_modelPresentation, SerrePositivity.Bousfield.ModelPresentation.isLocalizationModel, SerrePositivity.Bousfield.ModelPresentation.leftProper, SerrePositivity.Bousfield.exists_enriched_localization")
*HTT 命題 A.3.7.3*　左 Bousfield 局所化のモデルの構成（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=926)）。対応表の状態：一部（stronger-hyp）。

*主張*　左固有な組合せ的単体モデル圏は、小さい余ファイブレーションの集合 $`S` に沿って左 Bousfield 局所化でき、弱同値は $`S`-同値、余ファイブレーションは元のままである。

KB-W2原文・型再照合：仮定：Mathlib locally presentable で生成 I,J と左固有性を持つ A、小さい S、複数宇宙の ModelCategory SSet と標準 mono/horn-RLP/W の比較を追加（証明済み具体的 instance なし、HT-KQ は sorryAx の引用入力）。豊穣構造の保存にはさらに generating endpoints の tensor compatibility hcompat と unit axiom を要求する。結論：同じ A に実際の ModelCategory を構成し、Cof を保ち、W=RMap による S-local equivalences、fibrant iff 元の fibrant∧S-local、左固有性と小さい generators、追加 hcompat 下の enriched SM7 を得る。結論は対応するが原典より仮定が強い。

局所化後も左固有・組合せ的・単体的である。そのファイブラント対象は、元の圏でファイブラントかつ $`S`-局所なものにちょうど一致する。

:::

:::proposition "htt_A_3_7_4" (lean := "SerrePositivity.Bousfield.IsLocalizationModel.classes_eq_of_localObjects_eq")
*HTT 命題 A.3.7.4*　局所対象が一致する局所化の三射類の一致（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=928)）。対応表の状態：一部（direction）。

*主張*　左固有な組合せ的単体モデル圏の任意の組合せ的局所化は、小さい余ファイブレーションの集合で得られ、二つの局所化の一致は局所対象の一致で判定できる。

KB-W2原文・型再照合：仮定：同じ A に S,T の実際の IsLocalizationModel certificates と補助 ModelCategory SSet を指定（証明済み具体的 instance なし、Lean の追加仮定）。結論：S-local と T-local の対象述語が等しければ cofibrations・weak equivalences・fibrations の三射類が等しいという (2) の十分方向を得る。全ての combinatorial localization が小さい S から出る (1) と、hA の本質像としての逆方向の比較は含まない。

局所対象の類を比較する場所は元のモデル圏のホモトピー圏である。具体的な生成射の選択が違っても、そこに現れる局所対象で局所化が決まる。

:::

:::proposition "htt_A_3_7_9" (lean := "SerrePositivity.Bousfield.IsLocalizationModel.leftQuillen_iff_rightAdjoint_local, SerrePositivity.Bousfield.IsLocalizationModel.leftQuillen_iff_derived_inverts, SerrePositivity.Quillen.isFibrant_obj")
*HTT 命題 A.3.7.9*　局所化後の随伴と右随伴の局所対象判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=930)）。対応表の状態：一部（component）。

*主張*　左固有な組合せ的単体モデル圏の間の単体的 Quillen 随伴が始域の Bousfield 局所化に降りることは、左導来関手が局所化同値を同型に移すことと同値である。

KB-W2原文・型再照合：仮定：元の実際の Quillen 随伴、同じ A の IsLocalizationModel S m、標準 mono/horn-RLP を持つ補助 ModelCategory SSet（証明済み具体的 instance なし）。結論：局所化後の left Quillen 性 iff 全ての fibrant Y に対し RY が S-local、元の right Quillen 性で RY は元でも fibrant なので (1)⇔(3) に一致。derived criterion は生成 S を LF が反転するという形であり、原典 (2) の全ての新弱同値に対する記述との比較は含まない。

同値な右随伴側の判定は、終域のファイブラント対象の像が始域の局所化後もファイブラントになることである。両判定は同じ随伴が局所化のモデル構造に適合することを表す。

:::


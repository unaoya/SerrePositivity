import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.KanCharacterization

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 3.3 Modules over ∞-Operads" =>
%%%
number := false
tag := "ha-3-3"
%%%

HA 3.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

*monoidal-prl.html — 3. 代数と加群*

対称モノイダル ∞ 圏 $`\mathcal V` の中で、可換代数 $`\mathrm{CAlg}(\mathcal V)` と加群 $`\mathrm{Mod}_R(\mathcal V)` が定義される（operad の写像、あるいは $`\mathrm{Fin}_*` 上の切断として）。

- 対象　／　意味
- $`\mathrm{CAlg}(\mathrm{Pr}^L)`　／　presentably 対称モノイダル ∞ 圏（$`\otimes` が各変数ごとに余極限を保つ）。$`D(X)`、$`\mathrm{Sp}`、$`\mathrm{Mod}_R` など。内部 Hom は随伴関手定理で自動的に存在
- $`\mathrm{CAlg}(\mathrm{Pr}^L)` の射　／　対称モノイダルな左随伴（$`f^*`）
- $`\mathrm{Mod}_{\mathrm{Sp}}(\mathrm{Pr}^L)`　／　presentable 安定 ∞ 圏 $`\mathrm{Pr}^L_{\mathrm{st}}`
- $`\mathrm{Mod}_{D(\Lambda)}(\mathrm{Pr}^L)`　／　$`\Lambda` 線形な presentable 安定 ∞ 圏。係数の変更もテンソル積で扱える

- *冪等代数*：$`\mathrm{Sp}\otimes\mathrm{Sp}\simeq\mathrm{Sp}` なので、$`\mathrm{Sp}` 上の加群構造は高々一通りで、持つかどうかは性質になる。「安定性は構造ではなく性質」の正確な形。

- *随伴とモノイダル性*：対称モノイダルな左随伴 $`f^*` の右随伴 $`f_*` は自動的に lax 対称モノイダル（$`f_*A\otimes f_*B\to f_*(A\otimes B)`）。射影公式は、ある自然な構造射が同値であるという条件として述べられる。

# 3.3.1 Coherent ∞-Operads

%%%
number := false
tag := "ha-3-3-1"
%%%

:::proposition "ha_3_3_1_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_of_isGroupoid")
*HA 注意 3.3.1.5*　Coherent ∞-Operads (p. 377)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=377)）。対応表の状態：一部（stronger-hyp）。

*主張*　色の圏 $`O` が Kan 複体なら、活性図式の指定の拡張を集めた $`\operatorname{Ext}(\sigma,S)` も Kan 複体となる。

同じExt(σ,S)について、その全辺が同値（hExtがgroupoid）であることを追加すればkanComplex\_of\_isGroupoidは同じExtのKan性を直接返す。原文のOがKanという仮定からこの追加条件を導く部分は含まない。

拡張の圏の全ての射が同値であることを色の圏で検査する。準圏のうち全ての射が可逆なものは Kan 複体である。

:::

:::definition "ha_3_3_1_9" (lean := "SSet.KanComplex") (uses := "htt_1_1_2_1, htt_1_1_2_4")
*HA 定義 3.3.1.9*　Coherent ∞-Operads (p. 378)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=378)）。対応表の状態：一部（component）。

*主張*　コヒーレントな ∞ オペラッドは、単位的で色の圏が Kan 複体であり、二つの活性射と中間の恒等射から得る拡張空間の指定四角形がホモトピー押し出しとなる。

原文のcoherent条件(2)は同じ基礎∞圏OがKan complexであること。KanComplex Oはこの成分を直接表す。unital性とExtのhomotopy pushout条件・coherence全体は含まない。

退化した三単体の拡張から、頂点集合 $`\{0,1,3\}`、$`\{0,2,3\}`、$`\{0,3\}` への制限を取る。各頂点で拡張を許す初期部分はそれぞれ $`\{0,1\}`、$`\{0\}`、$`\{0\}` であり、制限射で作る四角形に条件を課す。

:::

# 3.3.3 Module Objects

%%%
number := false
tag := "ha-3-3-3"
%%%

:::proposition "ha_3_3_3_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory")
*HA 注意 3.3.3.13*　Module Objects (p. 391)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=391)）。対応表の状態：一部（component）。

*主張*　単位的な $`O^\otimes` の上の代数の族のうち、指定の関手が慣性辺を保つものを取った充満部分圏は準圏であり、その射影は圏論的ファイブレーションである。

KB-W2型再照合：仮定：準圏 X と頂点条件 P（HA の相対 Alg の全体が準圏という先行結果を用い、P を inert 保存に取る）。結論：頂点条件による充満部分複体が準圏となる（この成分は一致）。O⊗ への categorical fibration 性は型に含まれない。

慣性辺保存は対象の同値で保たれるので、代数の族を含む親の圏のファイブレーションをこの充満部分圏に制限できる。この部分圏は $`O^\otimes` と通常の代数の圏の積に圏論的同値である。

:::


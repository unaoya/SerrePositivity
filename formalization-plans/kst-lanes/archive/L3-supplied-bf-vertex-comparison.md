# K-S•-S3 の実 BF 二頂点と固定 K の接続（設計補足案・未採用）

概要：実供給された新 BF 模型を固定 K の実構造辺へ戻す、二頂点だけの比較仕様。
方針：元の実核と実商の二つについて、旧 kOmegaSpectrum と実供給 BF 模型の Sp 頂点同型を使う。
規約：ユーザー判断待ち。新しい存在仮定を本体には追加せず、一般 BF 整流・StableInfinity 上の K 関手化は再開しない。固定 S・ν・K、I・P は保持する。
使われ方：旧実核 K → 新実核 BF → Ω(新実商 BF) → Ω(旧実商 K) を経て、既存の同じ Yoneda・P 比較で固定 K の構造辺へ戻す。

- 届いた `dgKappaNativeCoherentBFSquare` は新しい `dgKappaNativeBFFiniteOmegaSpectrum` 四対象を持つ。`dgKappaNativeCoherentBFArrow_homotopyMap_eq` は、旧・新の指定整数群同型を介した可換式。旧 BF 四対象との厳密等式ではない。
- 旧 `DGKappaNativeBFBoundaryInput` は旧四対象を固定しており、そのまま実供給を代入できない。既存の条件付き定理は保持する。
- K-B の `DGKappaSuppliedBFSquare` は実 Φ と全正段の全 S• 比較、および指定群同型を介した旧 K-cof への接続を消費する。`DGKappaSuppliedBFZero`・`DGKappaSuppliedBFFiberComparison`・`DGKappaSuppliedBFOneStage` は hBF の存在仮定なしで同じ実零角・実 fiber 比較・一回の S• fibration に条件付きの非負次数 π 同型を与える。
- 同じ cone の実零性も、旧 K の全整数消滅と指定整数群同型から認証する。新旧スペクトルの Sp 同型を整数群の抽象同型だけから推論しない。
- 補足案：実核（c=0）と実商（c=3）だけの実 Sp 頂点同型を K-S• 正本へ依頼する。中央 cone と零角には不要。四辺の旧・新の Sp 写像空間比較も要求しない。
- 採用時：届くまでは下記命題を明示定理引数に取る同じ二頂点の受け渡しを構成し、実供給の構造辺と固定 K を接続する。実証明は K-S• へコーディネータ経由で依頼する。
- 不採用時：供給済み新 BF 模型上の fiber 比較・構造辺と旧 K-cof の群作用の接続を保持し、固定 K の実構造辺への戻しには別の実スペクトル比較が必要。
- 下記の全型は `lake env lean /tmp/kb-s3-vertex-iso-request.lean` で型検査済み。命題の証明・存在は主張しない。

```lean
import SerrePositivity.KST.SConstruction.DGKappaNativeCoherentBFArrowComparison
open CategoryTheory
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.NonConnective SerrePositivity.KST.Fibration
noncomputable section
universe u v w
local instance : SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

def kbNativeBFVertexComparisonRequest : Prop :=
  ∀ (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
    {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (c : Fin 4) (_ : c = 0 ∨ c = 3),
    let C := dgKappaNativeBFFiniteNativeObject R D I c
    Nonempty (VertexIso (coherentNerveVertex (kOmegaSpectrum (sInputModel C.obj)))
      (coherentNerveVertex (dgKappaNativeBFFiniteOmegaSpectrum R D I C)))
```

# K-S•-S3 の実 BF 二頂点と固定 K の接続（採用済み設計補足）

概要：実供給された新 BF 模型を固定 K の実構造辺へ戻す、二頂点だけの比較仕様。
方針：元の実核と実商の二つについて、旧 kOmegaSpectrum と実供給 BF 模型の Sp 頂点同型を使う。
規約：ユーザー採用、K-S• の実供給を代入済み。一般 BF 整流・StableInfinity 上の K 関手化は再開しない。固定 S・ν・K、I・P は保持する。
使われ方：旧実核 K → 新実核 BF → Ω(新実商 BF) → Ω(旧実商 K) を経て、既存の同じ Yoneda・P 比較で固定 K の構造辺へ戻す。

- 届いた `dgKappaNativeCoherentBFSquare` は新しい `dgKappaNativeBFFiniteOmegaSpectrum` 四対象を持つ。`dgKappaNativeCoherentBFArrow_homotopyMap_eq` は、旧・新の指定整数群同型を介した可換式。旧 BF 四対象との厳密等式ではない。
- 旧 `DGKappaNativeBFBoundaryInput` は旧四対象を固定しており、そのまま実供給を代入できない。既存の条件付き定理は保持する。
- K-B の `DGKappaSuppliedBFSquare` は実 Φ と全正段の全 S• 比較、および指定群同型を介した旧 K-cof への接続を消費する。`DGKappaSuppliedBFZero`・`DGKappaSuppliedBFFiberComparison`・`DGKappaSuppliedBFOneStage` は hBF の存在仮定なしで同じ実零角・実 fiber 比較・一回の S• fibration に条件付きの非負次数 π 同型を与える。
- 同じ cone の実零性も、旧 K の全整数消滅と指定整数群同型から認証する。新旧スペクトルの Sp 同型を整数群の抽象同型だけから推論しない。
- 採用済み補足：実核（c=0）と実商（c=3）だけの実 Sp 頂点同型は K-S• 正本から供給済み。中央 cone と零角には不要。四辺の旧・新の Sp 写像空間比較も要求しない。
- 採用経路：K-S• の 8b9bb13d2 の dgKappaNativeBFKernelQuotientVertexIso を同じ I に代入し、実供給構造辺を固定 K へ接続した。二頂点比較の仮定は不要。DGKappaSuppliedBFFixedStructure と DGSuspensionSuppliedBFSequence が固定 K の実構造辺・実余極限候補・連結比較へ消費する。全入力自然性は主張しない。
- 下記の全型は `lake env lean /tmp/kb-s3-vertex-iso-request.lean` で型検査済み。当初の供給仕様を保持し、現在は公開定理で放電済み。

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

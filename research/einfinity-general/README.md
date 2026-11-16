# EInfinityから分離する一般のホモトピー論・∞圏論の部品目録

OE-W1、2026-11-16。基準main `30ae8948f339beec42d9340feb02f2031c22c72b`。

対象は **489ファイル・36,258原Lean行**。

## 状態・検証の出所

ここにまとめるのは一般の図式・重み・frame・局所化の部品。SSetのモデル構造を全域で仮定するという意味ではなく、各型の仮定に従う。一般の複体・模型圏の定理と、具体的なBE値の比較を区別する。

**準備中**：現在の抜粋は基準ソースの実際の宣言ヘッダー。移動後の対象ビルド・v3b・引用／タグ・root・正式全監査・verifyは未検収。最終の検査結果はreport-organize-einfinity.mdを正本とし、完了を先取りしない。

## 読み方・原典・入力

各ファイルの概要・方針・規約・利用箇所はmodule docstringから抜き出した。原典番号は利用箇所の説明であり、その一般定理の完成を意味しない。型は最初の名前つき公開宣言から証明本体を除いた抜粋。局所のuniverse・variable文脈を併記するが、open・記法・local instance・import・sectionの範囲はリンク先を参照する。ここを連結してLeanへ貼る用途ではない。

配置上の対応：Kerodonはタグに対応する章・節、HA §1.3.4は模型圏の局所化、HomotopicalAlgebraは図式の重みとホモトピー関数複体。HA Monadsの179本は今回移動せず、既存の research/g12-monad-route/README.md を参照する。

## 役割別の集計

| 束 | ファイル | 原Lean行 |
|---|---:|---:|
| OE01 | 132 | 8,821 |
| OE02 | 61 | 4,697 |
| OE03 | 144 | 10,729 |
| OE04 | 152 | 12,011 |

## ファイルごとの構成と型

### [BousfieldKanDegenerate.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/HomotopicalAlgebra/Diagram/BousfieldKanDegenerate.lean)

OE01、68原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanDegenerate`。

概要：BK単体の退化性は、最後の射を除いた元の射列の退化性そのもの。
方針：忘却は退化を保ち、逆向きは同じ退化と面によって最後の構造射を固定して復元。
規約：IS-W2 R03aの自由境界細胞の証明分割。圏の射が単射とは仮定しない。
使われ方：非退化な射列で添字付けた自由図式の細胞。

主宣言（基準の完全名）：`SerrePositivity.DiagramModel.BousfieldKanCells.sigma_delta_eq_of_base`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

theorem sigma_delta_eq_of_base {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) (n+1)) (k : Fin (n+1))
    (t : ComposableArrows I n)
    (ht : (nerve I).σ k t = s ⋙ Over.forget i) :
    (nerve (Over i)).σ k ((nerve (Over i)).δ k.castSucc s) = s
```

### [BousfieldKanFreeCells.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/HomotopicalAlgebra/Diagram/BousfieldKanFreeCells.lean)

OE01、78原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanFreeCells`。

概要：BK重みの各次数の非退化単体は、元の非退化射列上の自由図式。
方針：全単体の分解を非退化部分に制限し、最後の射への後合成で自然性を示す。
規約：IS-W2 R03aの細胞表示の証明分割。元の圏に余分な仮定を付けない。
使われ方：自由境界によるBK重みの骨格の付着。

主宣言（基準の完全名）：`SerrePositivity.DiagramModel.BousfieldKanCells.NondegenerateData`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

abbrev NondegenerateData (n : ℕ) (i : I)
```

### [BousfieldKanRepresentableCells.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/HomotopicalAlgebra/Diagram/BousfieldKanRepresentableCells.lean)

OE01、58原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanRepresentableCells`。

概要：BKの非退化自由細胞の図式は、終頂点の共変表現可能図式の余積。
方針：同じ射列と最後の射の対で余積の包含・降下射を記述し、全射で自然性を検証。
規約：IS-W2 R03aの自由境界細胞の証明分割。型値図式の同じ普遍性。
使われ方：BK骨格の付着を自由評価随伴の境界生成族に同定する。

主宣言（基準の完全名）：`SerrePositivity.DiagramModel.BousfieldKanCells.cellRepresentables`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

abbrev cellRepresentables (n : ℕ) (c : (nerve I).nonDegenerate n) : I ⥤ Type u
```

### [BousfieldKanSimplex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/HomotopicalAlgebra/Diagram/BousfieldKanSimplex.lean)

OE01、84原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanSimplex`。

概要：BK重みの単体を元の射列と終頂点から評価先への射に分解する。
方針：over圏の射列の台を忘れ、終頂点の構造射を取り出して厳密に往復する。
規約：IS-W2 R03aの細胞表示の証明分割。モデル構造を仮定しない。
使われ方：最後の射について自由な境界細胞による射影cofibrancy。

主宣言（基準の完全名）：`SerrePositivity.DiagramModel.BousfieldKanCells.SimplexData`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

abbrev SimplexData (n : ℕ) (i : I)
```

### [FrameWeightUnitNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/HomotopicalAlgebra/Diagram/FrameWeightUnitNaturality.lean)

OE01、26原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightUnitNaturality`。

概要：元の重み付き実現随伴の単位の係数frameに関する自然性。
方針：同じmateのHom同値の自然性を恒等射で評価する。
規約：既存構成の単位則。重み・frame・実現関手を変更しない。
使われ方：BE Totの普遍重み付き錐の全図式射に対する照合。

主宣言（基準の完全名）：`SerrePositivity.DiagramModel.FrameWeightRealization.unit_frame_naturality`。

```lean
universe w u
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{w} C]
  [HasColimitsOfSize.{w,w} C]

theorem unit_frame_naturality {B B' : K ⥤ SimplexCategory ⥤ C}
    (a : B ⟶ B') (W : Kᵒᵖ ⥤ SSet.{w}) :
    (adjunction K B').unit.app W ≫ ((homFamily K).map a.op).app ((functor K B').obj W) =
      (adjunction K B).unit.app W ≫ (hom K B).map ((map K a).app W)
```

### [SimplicialCellSkeleton.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/HomotopicalAlgebra/Diagram/SimplicialCellSkeleton.lean)

OE01、45原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.SimplicialCellSkeleton`。

概要：非退化単体の境界は、元の直前の骨格をちょうど引き戻す。
方針：空の部分複体からの既存の相対細胞分解を同じ単体に適用する。
規約：IS-W2 R03aの骨格の貼り合わせの証明分割。
使われ方：自由なBK細胞の境界射と旧骨格との厳密な照合。

主宣言（基準の完全名）：`SerrePositivity.DiagramModel.SimplicialDiagramSkeleton.nondegenerate_preimage_skeleton`。

```lean
universe u

theorem nondegenerate_preimage_skeleton {X : SSet.{u}} {n : ℕ}
    (c : X.nonDegenerate n) :
    (X.skeleton n).preimage (yonedaEquiv.symm c.val) = ∂Δ[n]
```

### [SimplicialDiagramSkeleton.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/HomotopicalAlgebra/Diagram/SimplicialDiagramSkeleton.lean)

OE01、102原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.SimplicialDiagramSkeleton`。

概要：単体集合値図式の骨格を元の評価先の全射で自然な図式として組み立てる。
方針：各単体集合の同じ骨格に射を制限し、自然な骨格の塔と元の図式への余錐を取る。
規約：IS-W2 R03aの境界細胞の証明分割。元の図式の単体を変更しない。
使われ方：自由境界の段階的な付着と全体への余極限。

主宣言（基準の完全名）：`SerrePositivity.DiagramModel.SimplicialDiagramSkeleton.skeleton_image_le`。

```lean
universe u

theorem skeleton_image_le {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (X.skeleton n).image f ≤ Y.skeleton n
```

### [DiagonalLeftAnodyne.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/HomotopicalAlgebra/Simplicial/DiagonalLeftAnodyne.lean)

OE01、47原行。配置：`SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLeftAnodyne`。

概要：二重単体集合の対角はReedy left anodyne射をleft anodyne射へ送る。
方針：対角の右随伴の相対matching射を、境界内部Homのleft fibrationへ同定する。
規約：全ホーンのanodyne性への置き換えも、単体集合のモデル構造の仮定も用いない。
使われ方：IS-W2 R03f.2のsimplicial replacementの係数比較。

主宣言（基準の完全名）：`SerrePositivity.BisimplicialModel.relativeMatching_leftFibrations`。

```lean
universe u

theorem relativeMatching_leftFibrations {E B : SSet.{u}} (p : E ⟶ B)
    (hp : leftFibrations p) (n : ℕ) :
    leftFibrations (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
      (internalHomRight.map p))
```

### [TransportSimplexFirstVertexZero.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/TransportSimplexFirstVertexZero.lean)

OE01、48原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexFirstVertexZero`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_ulift_zero_vertex`。

```lean
universe u

lemma transportSimplexFirstVertexMap_ulift_zero_vertex {B : SSet.{u}} (b : B _⦋0⦌) :
    ((SSet.uliftFunctor.{u+1,u}).map (transportSimplexFirstVertexMap B)).app
      (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (transportSimplexIndex b))) = ULift.up b
```

### [LeftFibrationFiberEvaluationEdge.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftFibrationFiberEvaluationEdge.lean)

OE01、61原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationFiberEvaluationEdge`。

概要：同じ底上の射のfiber評価のcoherentな像は、元の実際のfiber射。
方針：元の豊穣Homの零次元の作用とcoherentな辺の自然性を適用する。
規約：全空間・射・底の等式を保持し、弱同値を仮定しない。
使われ方：元の全straightening比較の指定単位の評価。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation_edge`。

```lean
universe u

lemma leftFibrationInfinityFiberEvaluation_edge {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    (leftFibrationInfinityFiberEvaluation b).app (Opposite.op ⦋1⦌)
        (leftFibrationInfinityEdge p q f hf).edge =
      (coherentNerveEdge (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
          leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b)).edge
```

### [LeftStraighteningDiagramFiberComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningDiagramFiberComparison.lean)

OE01、55原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramFiberComparison`。

概要：元の全評価同型の成分を、元の図式の値と同じ実fiberの頂点へ合わせる。
方針：元の図式の頂点の等式と同じcoherentなfiber評価の頂点の等式を合成する。
規約：元の指定評価同型を使い、新しい同値を選ばない。
使われ方：同じ全変換を実際のfiber射へ厳密に照合する。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_fiber_vertex`。

```lean
universe u

lemma leftStraighteningInfinityDiagram_fiber_vertex {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    (leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up b) =
      (leftStraighteningInfinityMap B ≫ evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b)).app
        (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p)
```

### [LeftStraighteningDiagramFiberNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningDiagramFiberNaturality.lean)

OE01、79原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramFiberNaturality`。

概要：元の全図式の射の評価は、元の指定評価同型で共役した実際のfiber射。
方針：元の全自然性に実際のfiber射の像を代入し、同じ両端の等式で正規化する。
規約：結論は同じホモトピー圏の射の厳密な等式であり、任意の底上の射を扱う。
使われ方：元の二変数native比較の同じ全射と指定単位の評価。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagramHom_actualFiber_arrow`。

```lean
universe u v

lemma leftStraighteningInfinityDiagramHom_actualFiber_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagramHom p q f hf) (ULift.up b)) =
      Arrow.mk ((leftStraighteningInfinityDiagram_fiberIso p b).hom ≫
        HomotopyCategory.homMk (coherentNerveEdge
          (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
            leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q f hf b)) ≫
        (leftStraighteningInfinityDiagram_fiberIso q b).inv)
```

### [LeftStraighteningDiagramHom.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningDiagramHom.lean)

OE01、38原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramHom`。

概要：元の全 straightening が同じ底上の射へ与える全図式間の射。
方針：既存の全 straightening 関手による同じ底上の射の像を使う。
規約：元の射と指定された射影を保つ。弱同値の仮定は追加しない。
使われ方：IS-W2 R03d の全関手同型を構成するための、同じ全変換の射。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagramHom`。

```lean
universe u

def leftStraighteningInfinityDiagramHom {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    FunctorHom (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q)
```

### [LeftStraighteningDiagramHomArrow.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningDiagramHomArrow.lean)

OE01、60原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramHomArrow`。

概要：元の全分類が同じ底上の射へ与える像の端点の正規化を照合する。
方針：定義に含まれる同じ二つのEq.mpを外し、端点を含むArrowの等式へ戻す。
規約：元のleftStraighteningInfinityDiagramHomそのものを使う。
使われ方：同じ全変換の単位評価と実際のfiber射の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagramHom_heq`。

```lean
universe u v

lemma leftStraighteningInfinityDiagramHom_heq {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    HEq (leftStraighteningInfinityDiagramHom p q f hf)
      ((hoFunctor.map (leftStraighteningInfinityMap B)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated))
```

### [LeftStraighteningDiagramHomEvaluation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningDiagramHomEvaluation.lean)

OE01、84原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramHomEvaluation`。

概要：元の全図式の同じ射を、元の指定評価同型と同じfiber評価へ照合する。
方針：同じ評価関手の像を正規化し、元の全評価同型の自然性へ同じ辺を代入する。
規約：射も評価同型も選び直さず、任意の底上の射を扱う。
使われ方：同じnative全比較の指定単位の評価。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagramHom_evaluate_arrow`。

```lean
universe u

lemma leftStraighteningInfinityDiagramHom_evaluate_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    Arrow.mk (functorHomEvaluate (leftStraighteningInfinityDiagramHom p q f hf) (ULift.up b)) =
      Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b))).toFunctor.map
        ((hoFunctor.map (leftStraighteningInfinityMap B)).toFunctor.map
          (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)))
```

### [LeftStraighteningRepresentationRestriction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningRepresentationRestriction.lean)

OE01、68原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentationRestriction`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_representationIso_precomp`。

```lean
universe u

lemma leftStraighteningInfinityDiagram_representationIso_precomp {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
    let k
```

### [LeftStraighteningRepresentationZeroEvaluation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningRepresentationZeroEvaluation.lean)

OE01、54原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentationZeroEvaluation`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_representationIso_zero_evaluate_arrow`。

```lean
universe u

lemma leftStraighteningInfinityDiagram_representationIso_zero_evaluate_arrow {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) (b : B _⦋0⦌) :
    let k
```

### [NativeNerveStraighteningComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/NativeNerveStraighteningComparison.lean)

OE01、41原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativeNerveStraighteningComparison`。

概要：通常のnerve上の同じ射影のnative分類とstrict transportの分類を比較する。
方針：同じ既存の相対表現への二つの全関手同型を合成する。
規約：点ごとのfiber同値を全図式の自然性の代用にしない。
使われ方：Grothendieck–Kanの全分類から元のKan係数への復元。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_nerveCandidateIso`。

```lean
universe u

def leftStraighteningInfinityDiagram_nerveCandidateIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningCandidate p)
```

### [NativeNerveUnitNormalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/NativeNerveUnitNormalization.lean)

OE01、85原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativeNerveUnitNormalization`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_nerveCandidateIso_normalized`。

```lean
universe u

lemma leftStraighteningInfinityDiagram_nerveCandidateIso_normalized {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    leftStraighteningInfinityDiagram_nerveCandidateIso p =
      leftStraighteningInfinityDiagram_representationIso p (nerveLeftTransportRepresentation p) ≪≫
        (leftStraighteningCoherentMap_oppositeVertexIso p).symm
```

### [TransportRepresentationSelfComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/TransportRepresentationSelfComparison.lean)

OE01、62原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportRepresentationSelfComparison`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallFiberTransportRepresentationVertexIso_self`。

```lean
universe u

lemma smallFiberTransportRepresentationVertexIso_self {E B : SSet.{u+1}} (p : E ⟶ B) [LeftFibration p]
    (hp : HasSmallSimplexFibers p) (R : LeftTransportRepresentation p) :
    smallFiberTransportRepresentationVertexIso p hp R R = Iso.refl (HomotopyCategory.mk (transportWitnessVertex R))
```

### [ElementsOppositeUniverseIso.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/ElementsOppositeUniverseIso.lean)

OE01、63原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ElementsOppositeUniverseIso`。

概要：宇宙を持ち上げた通常の要素圏の反対nerveを、元の反対要素圏のnerveへ戻す。
方針：同じ単体のULiftとHomのULiftを上下し、両方の厳密な往復を照合する。
規約：元の次数と全単体作用素を保持する。一般の大きい単体集合を小さくする構成ではない。
使われ方：元のnative fiberの反対要素圏から、元のleft-roof比較の入力への係数移送。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.elementsOppositeUniverseIndex`。

```lean
universe w v
variable (K : SSet.{v})

def elementsOppositeUniverseIndex :
    (ULiftHom.{max w v} ((SSet.uliftFunctor.{w,v}).obj K).Elements)ᵒᵖ ⥤
      ULiftHom.{max w v} K.Elementsᵒᵖ
```

### [GrothendieckFiberUnit.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckFiberUnit.lean)

OE01、111原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckFiberUnit`。

概要：元のGrothendieck置換単位を、同じ係数の指定fiberへ制限する。
方針：元のstrictなweighted nerve同型と定値fiber包含を通して元の単位を使う。
規約：同じ単位・比較射・全単体を保持する。
使われ方：BEの元の全要素圏の置換fiberと元のroof比較の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothendieckReplacement`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

abbrev grothendieckReplacement : Over (nerve I)
```

### [GrothendieckKanBarLeftAnodyne.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckKanBarLeftAnodyne.lean)

OE01、29原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanBarLeftAnodyne`。

概要：元のCat図式のEx∞係数単位のbar上のleft anodyne性。
方針：元の同じ単位の各成分にR03f.2を適用する。
規約：係数関手・単位・simplicialReplacementMapを変更しない。
使われ方：IS-W2 R03fの元の相対延長の比較。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothendieckKanCoefficientBarMap_leftAnodyne`。

```lean
universe u

theorem grothendieckKanCoefficientBarMap_leftAnodyne
    {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u}) :
    leftAnodyneExtensions (simplicialReplacementMap (grothendieckKanCoefficientUnit F))
```

### [GrothendieckKanClassification.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckKanClassification.lean)

OE01、87原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanClassification`。

概要：元のGrothendieck–Kan比較を底全体の分類の関手同型へ送る。
方針：指定単位を固定する一つの比較射を選び、既存の同じ底上の分類の移送を適用する。
規約：一点ごとの同型から全図式の同型を推論しない。
使われ方：IS-W2 R03dの両変数の比較の組み立て。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothendieckKanCoefficientComparison`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

def grothendieckKanCoefficientComparison :
    ((continuousLeftFibrationReplacement (nerve I)).obj
      (Over.mk (nerveMap (Grothendieck.forget F)))).left ⟶
        weightedNerve (grothendieckKanCoefficients F)
```

### [GrothendieckKanCoefficientComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckKanCoefficientComparison.lean)

OE01、50原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanCoefficientComparison`。

概要：元のGrothendieck–Kan比較を同じ置換単位を固定して前合成同値へ延長する。
方針：元の相対延長のcofinal性を、同じ底上のleft fibrationsの検出へ渡す。
規約：元の底、射影、比較射、置換単位の厳密な等式を保つ。
使われ方：IS-W2 R03fと全分類の比較。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothendieckKanCoefficientLift_isPrecompositionEquivalence`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

theorem grothendieckKanCoefficientLift_isPrecompositionEquivalence :
    let P : Over (nerve I)
```

### [GrothendieckKanCoefficientLift.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckKanCoefficientLift.lean)

OE01、69原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanCoefficientLift`。

概要：元のGrothendieck射列の比較を、元の置換単位を固定してKan係数へ延長する。
方針：係数のEx∞単位によるweighted mapと、既存の相対left-anodyne延長を使う。
規約：延長の存在と二つの厳密な等式だけを主張する。前合成同値性は別の検収。
使われ方：IS-W2 R03dの指定された元の射を保つ比較の組み立て。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothendieckKanCoefficients`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

abbrev grothendieckKanCoefficients : I ⥤ SSet.{u}
```

### [GrothendieckKanComparisonCofinality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckKanComparisonCofinality.lean)

OE01、57原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanComparisonCofinality`。

概要：元のKan係数の比較と同じ置換単位を固定する延長のleft cofinal性。
方針：同じbar/scaffold正方形の可換性と既存の合成・消去則を使う。
規約：cofinal性だけから元の延長の前合成同値性は主張しない。
使われ方：IS-W2 R03fの最後の全空間の比較の検収。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothendieckKanCoefficientMap_isLeftCofinal`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

theorem grothendieckKanCoefficientMap_isLeftCofinal :
    IsLeftCofinal (grothendieckKanCoefficientMap F)
```

### [GrothendieckKanScaffold.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckKanScaffold.lean)

OE01、59原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanScaffold`。

概要：元のCat係数のtaut scaffoldを同じGrothendieck射列へ接続する。
方針：R03eの逆射を後合成し、元の係数の単位との可換性をscaffold自然性から得る。
規約：nerve係数のquasicategory性を用い、Kan性を仮定しない。
使われ方：IS-W2 R03fの元の射を保つbar/scaffold比較。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothendieckNerveScaffold`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

def grothendieckNerveScaffold :
    simplicialReplacement (F ⋙ nerveFunctor) ⟶ nerve (Grothendieck F)
```

### [GrothendieckWeightedNerveClassification.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNerveClassification.lean)

OE01、36原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveClassification`。

概要：同じ底のGrothendieck・weighted nerve置換の全分類を比較する。
方針：検証済みのOver同型を忘却し、既存のleftClassification_overIsoを使う。
規約：分類は底全体のFunctorIso。元の係数とのKan比較はまだ主張しない。
使われ方：IS-W2 R03dの相対分類の比較の一方の端。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothendieckWeightedNerveReplacementClassificationIso`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

def grothendieckWeightedNerveReplacementClassificationIso :
    FunctorIso
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (weightedNerveProjection (F ⋙ nerveFunctor)))).hom)
```

### [GrothendieckWeightedNerveCoefficients.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNerveCoefficients.lean)

OE01、43原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveCoefficients`。

概要：同じGrothendieck射列の全prefixを、元のweighted nerveの係数として束ねる。
方針：既存Yonedaの自然性で、同じfiber prefixの全自然性を移す。
規約：IS-W2 R03eの前向きの単体。元の射列と同じ係数を使い、宇宙の置換を増やさない。
使われ方：Grothendieckのnerveからweighted nerveへの前向きの全写像。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothWeightedNerveCoefficients`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (σ : ComposableArrows (Grothendieck F) n)

def grothWeightedNerveCoefficients :
    simplexPrefixWeight n ⟶ (σ ⋙ Grothendieck.forget F) ⋙ (F ⋙ nerveFunctor)
```

### [GrothendieckWeightedNerveForward.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNerveForward.lean)

OE01、66原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveForward`。

概要：元のprefix係数を、Grothendieckのnerveからweighted nerveへの全写像にする。
方針：全順序射のprefix制限を同じtransportへ送り、元の重み係数の制限と合わせる。
規約：IS-W2 R03eの前向きの全写像。元の底の射列を厳密に保持する。
使われ方：同じweighted nerve比較同型の前向きの射。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothWeightedPrefixArrow_reindex`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

theorem grothWeightedPrefixArrow_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (Grothendieck F) n.len) (i : Fin (m.len+1)) :
    grothWeightedPrefixArrow F (α.toOrderHom.monotone.functor ⋙ σ) i =
      (simplexPrefixRestriction α i).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixArrow F σ (α.toOrderHom i)
```

### [GrothendieckWeightedNerveInverseData.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNerveInverseData.lean)

OE01、65原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveInverseData`。

概要：元のweighted nerveの係数から、同じGrothendieck射列の対象と射を回収する。
方針：各prefixの最終対象と、元の係数の自然性からの型の移送を使う。
規約：IS-W2 R03eの逆向きの単体の部分。新しいfiber対象や脚は選ばない。
使われ方：同じ厳密な比較同型の逆射と両往復の検査。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothWeightedNerveFiberChain`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (s : weightedNerveSimplex (F ⋙ nerveFunctor) n)

def grothWeightedNerveFiberChain (i : Fin (n+1)) : ComposableArrows (F.obj (s.1.obj i)) i.val
```

### [GrothendieckWeightedNerveInverseFunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNerveInverseFunctor.lean)

OE01、53原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveInverseFunctor`。

概要：元のweighted係数から回収した同じ対象と射を、Grothendieckの全射列にする。
方針：元の係数の全自然性でfiber射の合成を合わせ、Grothendieckの合成則を使う。
規約：IS-W2 R03eの逆向きの単体の関手性。元の基底とfiber射を保つ。
使われ方：同じ厳密な比較同型の逆射。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothWeightedNerveInverseMap_id`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (s : weightedNerveSimplex (F ⋙ nerveFunctor) n)

theorem grothWeightedNerveInverseMap_id (i : Fin (n+1)) :
    grothWeightedNerveInverseMap F s (𝟙 i) = 𝟙 (grothWeightedNerveInverseObj F s i)
```

### [GrothendieckWeightedNerveIso.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNerveIso.lean)

OE01、40原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveIso`。

概要：Grothendieck射列とprefix重み付きnerveの、同じ底上の厳密な同型。
方針：既存の前向き全写像の各次数の両往復から、その同じ写像を可逆にする。
規約：IS-W2 R03e。新しい逆写像の自然性を仮定しない。
使われ方：要素圏のnerveと同じ重み付きnerveの比較。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothWeightedNerveForward_bijective`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

theorem grothWeightedNerveForward_bijective (n : ℕ) :
    Function.Bijective (grothWeightedNerveSimplex F (n := n))
```

### [GrothendieckWeightedNerveOver.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNerveOver.lean)

OE01、45原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveOver`。

概要：同じweighted nerve比較を底上の同型とし、指定されたleft fibration置換へ送る。
方針：射影の厳密な等式をOver.isoMkに渡し、既存の置換関手と単位の自然性を使う。
規約：元の置換と単位を保持する。元の係数とのKan分類を主張しない。
使われ方：IS-W2 R03dの同じ底上の比較の組み立て。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothendieckWeightedNerveOverIso`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

def grothendieckWeightedNerveOverIso :
    Over.mk (nerveMap (Grothendieck.forget F)) ≅ Over.mk (weightedNerveProjection (F ⋙ nerveFunctor))
```

### [GrothendieckWeightedNervePrefix.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNervePrefix.lean)

OE01、65原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNervePrefix`。

概要：元のGrothendieck射列の初区間を、同じ最終基底のfiberへ送る。
方針：元の最終基底への脚をCostructuredArrowに記録し、既存のtransportを使う。
規約：IS-W2 R03eの前向きの単体の部分。元の基底・fiber対象・射を保持する。
使われ方：Grothendieckのnerveからweighted nerveへの同じprefix係数。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothWeightedPrefixIndex`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (σ : ComposableArrows (Grothendieck F) n)

def grothWeightedPrefixIndex (i : Fin (n+1)) (k : Fin (i.val+1)) : Fin (n+1)
```

### [GrothendieckWeightedNervePrefixNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNervePrefixNaturality.lean)

OE01、55原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNervePrefixNaturality`。

概要：同じGrothendieck射列のprefixは、初区間の包含と元の基底の射に自然。
方針：元のCostructuredArrowの脚の合成を照合し、既存transport_naturalityを使う。
規約：IS-W2 R03eの前向きの単体の自然性・合成則。脚や対象を選び直さない。
使われ方：全prefixを同じsimplexPrefixWeightからの自然変換へ束ねる。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothWeightedPrefixArrow_naturality`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (σ : ComposableArrows (Grothendieck F) n)

theorem grothWeightedPrefixArrow_naturality {i j : Fin (n+1)} (f : i ⟶ j) :
    grothWeightedPrefixArrow F σ i ⋙ CostructuredArrow.map (S := Grothendieck.forget F) (σ.map f).base =
      (simplexPrefixInclusion i.val j.val (leOfHom f)).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixArrow F σ j
```

### [GrothendieckWeightedNerveRecovery.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNerveRecovery.lean)

OE01、63原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveRecovery`。

概要：weighted係数から回収した射列のprefixは、元の同じ係数の射列に戻る。
方針：対象は係数の自然性、射はその同じ関手等式の射への評価で照合する。
規約：IS-W2 R03eの右往復の部分。元の係数と同じ底を保つ。
使われ方：厳密なweighted nerve比較の全単体での全射性。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothWeightedPrefixFiber_inverse_obj`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (s : weightedNerveSimplex (F ⋙ nerveFunctor) n)

theorem grothWeightedPrefixFiber_inverse_obj (i : Fin (n+1)) (k : Fin (i.val+1)) :
    (grothWeightedPrefixFiber F (grothWeightedNerveInverseSimplex F s) i).obj k =
      (grothWeightedNerveFiberChain F s i).obj k
```

### [GrothendieckWeightedNerveRetraction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNerveRetraction.lean)

OE01、82原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveRetraction`。

概要：元のGrothendieck射列の係数から、同じ対象と射列を回収する。
方針：Yonedaの往復とprefixの最終対象・最終射の評価を使う。
規約：IS-W2 R03eの左往復。元の射列の対象を変えない。
使われ方：厳密なweighted nerve比較の単射性。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothWeightedNerveFiberChain_forward`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (σ : ComposableArrows (Grothendieck F) n)

theorem grothWeightedNerveFiberChain_forward (i : Fin (n+1)) :
    grothWeightedNerveFiberChain F (grothWeightedNerveSimplex F σ) i =
      grothWeightedPrefixFiber F σ i
```

### [GrothendieckWeightedNerveVertex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNerveVertex.lean)

OE01、75原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveVertex`。

概要：Grothendieckのweighted nerve比較が元の指定頂点を厳密に保つ。
方針：次数零のprefixは元の同じfiber対象に戻り、そのYoneda表示を比較する。
規約：IS-W2 R03eの指定点付きの型。弱同値や成分への置換は行わない。
使われ方：元の指定点を持つ同じ底上の比較の入口。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothWeightedNerveForward_vertex`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

theorem grothWeightedNerveForward_vertex (i : I) (x : F.obj i) :
    (grothWeightedNerveForward F).app (Opposite.op ⦋0⦌)
      (nerveVertex (⟨i,x⟩ : Grothendieck F)) =
        (weightedNerveConstantLift (F ⋙ nerveFunctor) i).app
          (Opposite.op ⦋0⦌) (nerveVertex x)
```

### [SimplicialElementsClassification.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialElementsClassification.lean)

OE01、90原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsClassification`。

概要：同じ全要素圏の元の置換を、同じ全Grothendieck係数のnative分類へつなぐ。
方針：同じ底への圏同値のnerveを元の置換へ送り、その全分類を移送する。
規約：底と元の置換単位を保ち、固定始域のroofとの等式は別に確認する。
使われ方：全source frameの要素圏から両変数のnative Homへの接続。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialElementsGrothendieckOverMap`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

def simplicialElementsGrothendieckOverMap :
    Over.mk (nerveMap (simplicialTotalElementsProjection F)) ⟶
      Over.mk (nerveMap (Grothendieck.forget (simplicialElementsCatDiagram F)))
```

### [SimplicialElementsFiberFunctorLaws.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialElementsFiberFunctorLaws.lean)

OE01、41原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberFunctorLaws`。

概要：同じ fiber 包含の次数作用素と底の定値射影を回収する。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.sameSimplicialElementsFiberFunctor_degree`。

```lean
universe u

lemma sameSimplicialElementsFiberFunctor_degree {I : Type u} [SmallCategory I]
    (G : I ⥤ SSet.{u}) (i : I)
    {s t : (simplicialElementsCatDiagram G).obj i} (f : s ⟶ t) :
    ((simplicialElementsFiberFunctor G i).map f).hom.2 = f.down.hom
```

### [SimplicialElementsFiberInclusion.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialElementsFiberInclusion.lean)

OE01、116原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberInclusion`。

概要：元のfiber包含は通常のGrothendieck包含をnerveへ送った同じ射。
方針：元のweighted nerveの順射でprefix係数を照合し、同じ逆を消去する。
規約：fiberの包含とラベルを別の同値へ置き換えない。
使われ方：元のnative Homのfiber射を固定始域のroofの元のラベルへ照合する。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.grothWeightedNerveForward_fiberInclusion`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

theorem grothWeightedNerveForward_fiberInclusion (i : I) :
    nerveMap (Grothendieck.ι F i) ≫ grothWeightedNerveForward F =
      weightedNerveConstantLift (F ⋙ nerveFunctor) i
```

### [SimplicialElementsFiberMap.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialElementsFiberMap.lean)

OE01、43原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberMap`。

概要：元の全要素圏から底上の全写像を、同じ元のfiber包含へ制限する。
方針：元の単位を固定した延長の三角形を、その同じfiberへの制限へ移す。
規約：充填性や同値性を仮定せず、元の写像の厳密な等式だけを記録する。
使われ方：同じnative Hom比較射のfiberを元の全要素上の実射へ照合する。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialElementsFiberMap`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

def simplicialElementsFiberMap {E : SSet.{u}} (p : E ⟶ nerve I)
    (h : nerve (SimplicialTotalElements F) ⟶ E)
    (hh : h ≫ p = nerveMap (simplicialTotalElementsProjection F)) (i : I) :
    nerve ((simplicialElementsCatDiagram F).obj i) ⟶ vertexFiber p (nerveVertex i)
```

### [SimplicialElementsFiberUnit.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialElementsFiberUnit.lean)

OE01、100原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberUnit`。

概要：元の全要素圏の同じ置換単位の指定fiberへの制限を、同じGrothendieck表示で検査する。
方針：同じ二つの表示の厳密な往復と元の単位の自然性で、R03gの同じ写像へ移す。
規約：元の包含・置換・単位を保ち、別のfiber同値を選ばない。
使われ方：元のnative Hom写像のfiberの同値性とroof比較の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialElementsReplacement`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

abbrev simplicialElementsReplacement : Over (nerve I)
```

### [SimplicialElementsGrothendieck.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialElementsGrothendieck.lean)

OE01、148原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsGrothendieck`。

概要：全係数の要素圏と同じGrothendieck構成の係数表示を照合する。
方針：要素と底・単体次数を同じ順序に並べ、Homの宇宙だけを持ち上げる。
規約：元の底と係数の写像を保つ。
使われ方：元の全source frameの要素圏から同じ底上の分類への接続。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialElementsCatDiagram`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

def simplicialElementsCatDiagram : I ⥤ Cat.{u,u}
```

### [SimplicialReplacementDiagonal.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementDiagonal.lean)

OE01、69原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementDiagonal`。

概要：元のbarの二重単体集合の対角を、指定されたsimplicial replacementへ厳密に同定する。
方針：同じ基底射列を保持し、係数の単体のYoneda表示だけを変える。
規約：元の係数射の像についても同じ同型との自然性を示す。
使われ方：IS-W2 R03f.2の対角のleft anodyne性の移送。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementDiagonalHom`。

```lean
universe u
variable {I : Type u} [SmallCategory I]

def simplicialReplacementDiagonalHom (F : I ⥤ SSet.{u}) :
    diagonal.obj (simplicialReplacementRows F) ⟶ simplicialReplacement F
```

### [SimplicialReplacementLeftAnodyne.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementLeftAnodyne.lean)

OE01、30原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementLeftAnodyne`。

概要：simplicial replacementは各成分のleft anodyne性を元の全写像へ送る。
方針：元のbarのReedy left anodyne性を対角へ送り、指定された同じ写像へ全同型で運ぶ。
規約：元のsimplicialReplacementMapそのものの性質。条件の弱化や模型の変更をしない。
使われ方：IS-W2 R03f.2、元のEx∞係数の単位の相対的な比較。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap_leftAnodyne`。

```lean
universe u

theorem simplicialReplacementMap_leftAnodyne
    {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}}
    (η : F ⟶ G) (hη : ∀ i, leftAnodyneExtensions (η.app i)) :
    leftAnodyneExtensions (simplicialReplacementMap η)
```

### [SimplicialReplacementReedyLeftAnodyne.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementReedyLeftAnodyne.lean)

OE01、95原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementReedyLeftAnodyne`。

概要：barの元の相対latching射は、各係数射がleft anodyneならleft anodyneである。
方針：実際のpushoutの持ち上げ問題を、元の退化境界を固定する行の持ち上げへ戻す。
規約：元の相対latching射と両脚を保持する。別の射の条件つき判定に置き換えない。
使われ方：IS-W2 R03f.2の対角への移送。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowsMap_relative_leftAnodyne`。

```lean
universe u
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
  (hη : ∀ i, leftAnodyneExtensions (η.app i))

theorem simplicialReplacementRowsMap_relative_leftAnodyne (n : ℕ) :
    leftAnodyneExtensions (relativeLatchingMap simplexOp (Opposite.op ⦋n⦌)
      (simplicialReplacementRowsMap η))
```

### [SimplicialReplacementRowBoundaryComponents.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowBoundaryComponents.lean)

OE01、56原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowBoundaryComponents`。

概要：各基底射列で、指定された退化境界を保つ係数の持ち上げを作る。
方針：退化成分では元の境界値を使い、それ以外では同じ係数射のleft anodyne性で持ち上げる。
規約：元の二つの脚と、元の退化境界の値を厳密に保持する。
使われ方：IS-W2 R03f.2の相対latchingの直接の持ち上げ。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowBoundary_component`。

```lean
universe u
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
  (hη : ∀ i, leftAnodyneExtensions (η.app i)) (n : ℕ)
  {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (a : simplicialReplacementRow F n ⟶ E) (b : simplicialReplacementRow G n ⟶ B)
  (d : (simplicialReplacementDegenerateRow G n : SSet.{u}) ⟶ E)
  (sq : CommSq a (simplicialReplacementRowMap η n) p b)
  (hd : d ≫ p = (simplicialReplacementDegenerateRow G n).ι ≫ b)
  (ha : simplicialReplacementRowPartMap η n ((nerve I).degenerate n) ≫ d =
    (simplicialReplacementDegenerateRow F n).ι ≫ a)

theorem simplicialReplacementRowBoundary_component (σ : ComposableArrows I n) :
    ∃ l : G.obj (σ.obj 0) ⟶ E,
      η.app (σ.obj 0) ≫ l = simplicialReplacementRowInclusion F n σ ≫ a ∧
      l ≫ p = simplicialReplacementRowInclusion G n σ ≫ b ∧
      ∀ hσ : σ ∈ (nerve I).degenerate n,
        l = simplicialReplacementRowPartInclusion n G ((nerve I).degenerate n) σ hσ ≫ d
```

### [SimplicialReplacementRowBoundaryLift.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowBoundaryLift.lean)

OE01、60原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowBoundaryLift`。

概要：元の係数の持ち上げを、指定された退化境界を保つ行全体の射へ束ねる。
方針：元の各余積成分の射を降下させ、包含による検出で両脚と退化境界の一致を示す。
規約：元の行の射と指定境界を厳密に保持する。
使われ方：IS-W2 R03f.2の元の相対latching射のleft anodyne性。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowBoundary_lift`。

```lean
universe u
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
  (hη : ∀ i, leftAnodyneExtensions (η.app i)) (n : ℕ)
  {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (a : simplicialReplacementRow F n ⟶ E) (b : simplicialReplacementRow G n ⟶ B)
  (d : (simplicialReplacementDegenerateRow G n : SSet.{u}) ⟶ E)
  (sq : CommSq a (simplicialReplacementRowMap η n) p b)
  (hd : d ≫ p = (simplicialReplacementDegenerateRow G n).ι ≫ b)
  (ha : simplicialReplacementRowPartMap η n ((nerve I).degenerate n) ≫ d =
    (simplicialReplacementDegenerateRow F n).ι ≫ a)

theorem simplicialReplacementRowBoundary_lift :
    ∃ l : simplicialReplacementRow G n ⟶ E,
      simplicialReplacementRowMap η n ≫ l = a ∧ l ≫ p = b ∧
      (simplicialReplacementDegenerateRow G n).ι ≫ l = d
```

### [SimplicialReplacementRowCommonPresentation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowCommonPresentation.lean)

OE01、38原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowCommonPresentation`。

概要：同じ基底単体の任意の全射表示は、その同じ非退化表示を経由する。
方針：表示された単体も既存の非退化表示へ戻し、次元・単体・全射の一意性を順に使う。
規約：元の二つの表示の等式と全射の合成の等式を保持する。
使われ方：IS-W2 R03f.2のlatching余錐の一意性の検収。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement_common_nondegenerate_presentation`。

```lean
universe u

theorem simplicialReplacement_common_nondegenerate_presentation {X : SSet.{u}} {n m k : ℕ}
    (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] (τ : X.nonDegenerate m)
    (β : ⦋n⦌ ⟶ ⦋k⦌) [Epi β] (υ : X.obj (Opposite.op ⦋k⦌))
    (h : X.map α.op τ = X.map β.op υ) :
    ∃ (γ : ⦋k⦌ ⟶ ⦋m⦌) (_ : Epi γ), β ≫ γ = α ∧ X.map γ.op τ = υ
```

### [SimplicialReplacementRowDegeneracies.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowDegeneracies.lean)

OE01、42原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowDegeneracies`。

概要：barの退化作用素は、元の始点の係数を型の移送以外に変えない。
方針：全射の単調写像は零を零へ送り、元の係数の射はeqToHomとなる。
規約：任意の全射作用素を扱い、基本退化だけには制限しない。
使われ方：IS-W2 R03f.2の退化成分の相対latchingへの分離。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement_epi_zero`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

theorem simplicialReplacement_epi_zero {m n : SimplexCategory} (α : m ⟶ n) [Epi α] :
    α.toOrderHom 0 = 0
```

### [SimplicialReplacementRowEpiLifts.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowEpiLifts.lean)

OE01、49原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowEpiLifts`。

概要：基底射列の全射表示へ同じ係数を戻し、退化作用素の単射性を確認する。
方針：始点の等式の移送を打ち消し、全射の分裂を同じ行の関手で運ぶ。
規約：元の退化作用素とその元の係数の単体を保持する。
使われ方：IS-W2 R03f.2のlatching余錐の一意性。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowReindex_mono`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

theorem simplicialReplacementRowReindex_mono {m n : SimplexCategory} (α : m ⟶ n) [Epi α] :
    Mono (simplicialReplacementRowReindex F α)
```

### [SimplicialReplacementRowInclusionLaws.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowInclusionLaws.lean)

OE01、85原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowInclusionLaws`。

概要：同じ基底射列の余積包含と、指定部分への包含の係数射の法則。
方針：元の行の単体ごとの依存和を評価する。
規約：基底部分集合は任意。元の包含と係数射を厳密な等式で保持する。
使われ方：IS-W2 R03f.2の相対latchingの直接の境界付き持ち上げ。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowPartInclusion`。

```lean
universe u
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}} (n : ℕ)

def simplicialReplacementRowPartInclusion (F : I ⥤ SSet.{u}) (P : Set (ComposableArrows I n))
    (σ : ComposableArrows I n) (hσ : σ ∈ P) :
    F.obj (σ.obj 0) ⟶ simplicialReplacementRowPart F n P
```

### [SimplicialReplacementRowLatchingCocone.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowLatchingCocone.lean)

OE01、64原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowLatchingCocone`。

概要：barの外側のlatching図式から、同じ退化基底成分への余錐を作る。
方針：各真の退化作用素は、より低い次数の基底射列からの像であることを記録する。
規約：latchingとの同型性はここでは主張しない。元の全ての脚を保持する。
使われ方：IS-W2 R03f.2の退化部分と実際の相対latchingの同定。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowLatchingLeg`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u}) (n : ℕ)

def simplicialReplacementRowLatchingLeg (s : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    (simplicialReplacementRows F).obj s.obj.left ⟶ simplicialReplacementDegenerateRow F n
```

### [SimplicialReplacementRowLatchingColimit.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowLatchingColimit.lean)

OE01、97原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowLatchingColimit`。

概要：barの同じ退化部分への元のlatching余錐は、実際の余極限である。
方針：被覆する脚の任意の表示から値を取り、全表示での一致で自然性と一意性を示す。
規約：元の全係数と全てのlatchingの脚を保つ。
使われ方：IS-W2 R03f.2の相対latchingの退化・非退化による分離。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowLatching_exists_value`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u}) (n : ℕ)

theorem simplicialReplacementRowLatching_exists_value
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (s : (simplicialReplacementDegenerateRow F n : SSet.{u}).obj q) :
    ∃ v : c.pt.obj q, ∀ (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
      (x : ((simplicialReplacementRows F).obj j.obj.left).obj q),
      (simplicialReplacementRowLatchingLeg F n j).app q x = s → (c.ι.app j).app q x = v
```

### [SimplicialReplacementRowLatchingNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowLatchingNaturality.lean)

OE01、82原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowLatchingNaturality`。

概要：実際のlatchingと同じ退化部分の同型は、元の係数射と境界包含を保つ。
方針：全latchingの脚上で照合し、実際の余極限の一意性を使う。
規約：元のlatching評価関手と元の比較射そのものを使う。
使われ方：IS-W2 R03f.2の元の相対latchingから指定境界付き持ち上げへの接続。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowLatchingIso_hom`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (n : ℕ)

theorem simplicialReplacementRowLatchingIso_hom (F : I ⥤ SSet.{u}) :
    (simplicialReplacementRowLatchingIso F n).hom = simplicialReplacementLatchingToDegenerate F n
```

### [SimplicialReplacementRowLatchingRefinement.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowLatchingRefinement.lean)

OE01、46原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowLatchingRefinement`。

概要：同じ非退化表示から、元の任意のlatching表示への射と係数の持ち上げを作る。
方針：基底の全射表示の共通因子をOverの射にし、同じ係数を始点の等式で戻す。
規約：基底だけでなく元の係数の単体も実際のlatching作用素で回収する。
使われ方：IS-W2 R03f.2の任意の余錐に対する表示の独立性。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementLatchingRefinement`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u}) {n m : ℕ}

def simplicialReplacementLatchingRefinement (hm : m < n) (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α]
    (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) (γ : j.obj.left.unop ⟶ ⦋m⦌)
    (h : j.obj.hom.unop ≫ γ = α) : simplicialReplacementLatchingIndexOfEpi hm α ⟶ j
```

### [SimplicialReplacementRowLatchingSurjective.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowLatchingSurjective.lean)

OE01、46原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowLatchingSurjective`。

概要：元のlatching余錐の全ての脚は、同じ退化行を単体ごとに覆う。
方針：元の非退化表示をlatching対象へ戻し、係数を同じ始点の等式で移送する。
規約：基底射列と係数の双方を厳密に回収する。余極限性の一意性は別に検証する。
使われ方：IS-W2 R03f.2の退化行のlatching余極限の検収。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowLatching_jointly_surjective`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u}) (n : ℕ)

theorem simplicialReplacementRowLatching_jointly_surjective (q : SimplexCategoryᵒᵖ)
    (s : (simplicialReplacementDegenerateRow F n : SSet.{u}).obj q) :
    ∃ (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
      (x : ((simplicialReplacementRows F).obj j.obj.left).obj q),
      (simplicialReplacementRowLatchingLeg F n j).app q x = s
```

### [SimplicialReplacementRowLatchingValues.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowLatchingValues.lean)

OE01、70原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowLatchingValues`。

概要：元のlatching余錐の同じ退化単体の二表示は、任意の余錐で同じ値を持つ。
方針：同じ非退化表示へ係数ごと戻し、退化の単射性と余錐の自然性を使う。
規約：任意の単体次数、元の係数、元の余錐の全ての脚を保つ。
使われ方：IS-W2 R03f.2の退化行の余極限性。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowLatching_value_map`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u}) (n : ℕ)

theorem simplicialReplacementRowLatching_value_map
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) {j k : LatchingIndex simplexOp (Opposite.op ⦋n⦌)} (f : j ⟶ k)
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q)
    (y : ((simplicialReplacementRows F).obj k.obj.left).obj q)
    (h : ((simplicialReplacementRows F).map f.hom.left).app q x = y) :
    (c.ι.app j).app q x = (c.ι.app k).app q y
```

### [SimplicialReplacementRowMaps.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowMaps.lean)

OE01、47原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowMaps`。

概要：係数の自然変換を、同じ基底射列のbarの全行の射へ送る。
方針：各余積成分へ元の同じ係数射を適用し、面・退化とは元の自然性で合わせる。
規約：元の基底射列を全次数で保持する。
使われ方：IS-W2 R03f.2の元のsimplicialReplacementMapとの照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowMap`。

```lean
universe u
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}} (η : F ⟶ G)

def simplicialReplacementRowMap (n : ℕ) :
    simplicialReplacementRow F n ⟶ simplicialReplacementRow G n
```

### [SimplicialReplacementRowNormalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowNormalization.lean)

OE01、50原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowNormalization`。

概要：退化した元の基底射列を、真に低い次数の非退化射列からの全射表示にする。
方針：既存の非退化表示を用い、同次数の全射が恒等射であることから次数の狭義不等式を得る。
規約：係数や基底射列を選び直す同値ではなく、元の射列の表示の等式。
使われ方：IS-W2 R03f.2のlatchingの余極限性。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement_degenerate_presentation`。

```lean
universe u
variable {I : Type u} [SmallCategory I]

theorem simplicialReplacement_degenerate_presentation {n : ℕ}
    (σ : ComposableArrows I n) (hσ : σ ∈ (nerve I).degenerate n) :
    ∃ (m : ℕ) (_ : m < n) (α : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi α)
      (τ : (nerve I).nonDegenerate m), σ = (nerve I).map α.op τ
```

### [SimplicialReplacementRowParts.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowParts.lean)

OE01、64原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowParts`。

概要：barの一つの行を、基底射列の退化・非退化の部分へ分ける。
方針：内側の係数作用素は基底射列を変えないため、任意の基底部分集合が部分複体となる。
規約：基底の退化と係数の退化を区別する。外側のlatchingとの同定は別に示す。
使われ方：IS-W2 R03f.2の相対latchingの余積表示。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowPart`。

```lean
universe u
variable {I : Type u} [SmallCategory I]

def simplicialReplacementRowPart (F : I ⥤ SSet.{u}) (n : ℕ)
    (P : Set (ComposableArrows I n)) : (simplicialReplacementRow F n).Subcomplex
```

### [SimplicialReplacementRowReindex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRowReindex.lean)

OE01、69原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowReindex`。

概要：元の基底射列の行の面・退化作用を、同じ始点の係数の輸送で与える。
方針：任意の単調写像で基底射列を制限し、元の始点から新たな始点への射を適用する。
規約：係数の単体次数と基底射列の次数を独立に保つ。
使われ方：IS-W2 R03f.2の二重単体集合とその相対latchingの計算。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRowReindex`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

def simplicialReplacementRowReindex {m n : SimplexCategory} (α : m ⟶ n) :
    simplicialReplacementRow F n.len ⟶ simplicialReplacementRow F m.len
```

### [SimplicialReplacementRows.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementRows.lean)

OE01、71原行。配置：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRows`。

概要：barの各基底射列における係数を、同じ射列で添字づけた余積として表示する。
方針：単体ごとの依存和で行を構成し、同じ余積包含からの降下を直接与える。
規約：全添字と係数は同じ宇宙。各行の係数の次数を基底射列の次数から独立に保つ。
使われ方：IS-W2 R03f.2のbarの退化部分と相対latchingの分離。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementRow`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u}) (n : ℕ)

def simplicialReplacementRow : SSet.{u}
```

### [ExInfinityUnitLeftAnodyne.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheExInfinityFunctor/ExInfinityUnitLeftAnodyne.lean)

OE01、23原行。配置：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityUnitLeftAnodyne`。

概要：元のEx∞単位のleft anodyne性。
方針：検証済みのanodyne性とKan標的の一般補題を、元の同じ単位へ適用する。
規約：既存のEx∞関手と元の単位を変更しない。
使われ方：IS-W2 R03fの係数単位のbar上の相対比較。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_leftAnodyne`。

```lean
universe u

theorem exInfinityUnit_leftAnodyne (X : SSet.{u}) :
    leftAnodyneExtensions (exInfinityUnit.app X)
```

### [OppositeWeakHomotopyReflection.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/OppositeWeakHomotopyReflection.lean)

OE01、36原行。配置：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.OppositeWeakHomotopyReflection`。

概要：元のop反転は、元の射自身の弱ホモトピー同値性も反映する。
方針：既存の保存則を二度適用し、同じop自己同値の単位で元の射へ戻す。
規約：始域・終域のKan性を仮定しない。元の射を別の比較射へ置き換えない。
使われ方：反対要素圏で元のnative fiber射の弱同値性を検査する係数移送。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.opposite_map_isWeakHomotopyEquivalence_iff`。

```lean
universe u

theorem opposite_map_isWeakHomotopyEquivalence_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsWeakHomotopyEquivalence (SSet.opFunctor.map f) ↔ IsWeakHomotopyEquivalence f
```

### [ClassificationTransportHom.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/FinitaryFunctorsAndCompactObjects/ClassificationTransportHom.lean)

OE01、84原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ClassificationTransportHom`。

概要：既存の全分類同型の順射を、同じ元の底上の射と実fiberの像へ合わせる。
方針：元のasIsoの順射と同じ端点の係数移送を外して、全straighteningの評価則へ接続する。
規約：既存の分類同型と同じ射・底の等式・前合成同値の証拠を保持する。
使われ方：元のraw側の全分類同型の指定単位の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.leftClassification_of_precompositionEquivalence_value`。

```lean
universe u v

lemma leftClassification_of_precompositionEquivalence_value {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    HEq (leftClassification_of_precompositionEquivalence p q f hf ef)
      (VertexIso.map (leftFibrationInfinityVertexIsoOfPrecompositionEquivalence p q f hf ef)
        (leftStraighteningInfinityMap B))
```

### [ContinuousLeftFibrationEquivalenceMap.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/ContinuousLeftFibrationEquivalenceMap.lean)

OE01、46原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationEquivalenceMap`。

概要：元の連続left-fibration置換は、同じ底上のcofinal射を前合成同値へ送る。
方針：元の単位の自然性、cofinal性の合成・消去則と同じ底上の検出を合成する。
規約：元の置換関手とその単位を使い、比較を選び直さない。
使われ方：全要素圏の同じGrothendieck表示をnativeな全分類へ移す。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacement_map_isPrecompositionEquivalence_of_leftCofinal`。

```lean
universe u

theorem continuousLeftFibrationReplacement_map_isPrecompositionEquivalence_of_leftCofinal
    {B : SSet.{u}} [Quasicategory B] {X Y : Over B} (f : X ⟶ Y)
    (hc : IsLeftCofinal f.left) :
    IsPrecompositionEquivalence ((continuousLeftFibrationReplacement B).map f).left
```

### [FunctorIsoPairing.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/FunctorIsoPairing.lean)

OE01、46原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorIsoPairing`。

概要：二つの全関手同型を、同じパラメーターを持つ直積値の全関手同型にする。
方針：既存のh Funの二胞体の直積分解と合成則で、同じ順逆の二成分を組にする。
規約：元の二つの同型を保ち、パラメーターの充填性は要求しない。
使われ方：元の全source-frameの始域・標的の二つの比較をまとめる。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorIsoPair`。

```lean
universe u

def functorIsoPair {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : T ⟶ X} {h k : T ⟶ Y} (e : FunctorIso f g) (d : FunctorIso h k) :
    FunctorIso (lift f h) (lift g k)
```

### [FunctorIsoPairingProjections.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/FunctorIsoPairingProjections.lean)

OE01、55原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorIsoPairingProjections`。

概要：元の全関手同型の組の二射影は、元の同型そのもの。
方針：元の直積の全単射の順逆の公式を使う。
規約：端点と元の二つの同型を保持する。
使われ方：全補正比較の元の二つの端点同型の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorIsoPair_postcomp_fst`。

```lean
universe u

lemma functorIsoPair_postcomp_fst {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : T ⟶ X} {h k : T ⟶ Y} (e : FunctorIso f g) (d : FunctorIso h k) :
    (functorIsoPair e d).postcomp (fst X Y) = e
```

### [LeftFibrationComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/Cofinality/LeftFibrationComparison.lean)

OE01、74原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationComparison`。

概要：同じ底上のleft fibrationsの間では、cofinalな射が前合成同値になる。
方針：二つの相対関手空間で恒等射を戻し、Kan空間の充満忠実性で余単位を戻す。
規約：元の射と厳密な底上の等式を保つ。
使われ方：元のGrothendieck–Kan比較の指定延長の検出。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal.relativeFunctorOverPre_isQCatEquivalence`。

```lean
universe u

lemma IsLeftCofinal.relativeFunctorOverPre_isQCatEquivalence
    {T E F B : SSet.{u}} (r : T ⟶ B) [LeftFibration r]
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (hc : IsLeftCofinal f) :
    IsQCatEquivalence (relativeFunctorOverPre r (show Over.mk p ⟶ Over.mk q from Over.homMk f hf))
```

### [PrecompositionCofinality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/Cofinality/PrecompositionCofinality.lean)

OE01、28原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.PrecompositionCofinality`。

概要：quasicategoryを標的とする前合成同値を、既存のleft cofinalityの定義へ照合する。
方針：既存の相対関手空間の前合成同値を、同じfiberで定義されたcofinalFunctorPreへ適用する。
規約：定義域の充填性は要求しない。元の前合成射を保持する。
使われ方：IS-W2 R03fの元のscaffold正方形と相対延長の比較。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_precompositionEquivalence`。

```lean
universe u

theorem isLeftCofinal_of_precompositionEquivalence
    {X Y : SSet.{u}} [Quasicategory Y] (f : X ⟶ Y) (hf : IsPrecompositionEquivalence f) :
    IsLeftCofinal f
```

### [BousfieldKanUniverseSections.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/BousfieldKanUniverseSections.lean)

OE01、32原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanUniverseSections`。

概要：元のBK切断空間のULiftを、同じAsSmall添字とULift係数のBK切断空間へ同型にする。
方針：元の普遍評価による切断空間の同型に、指定downによるBK重み同型の制限を合成する。
規約：IS-W2 R02〜R03の既存構成の宇宙移送則。Kan性は要求しない。
使われ方：同じ普遍BK点を全Hom∞比較の宇宙へ送る。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanUniverseSectionsIso`。

```lean
universe u v
variable (I : Type u) [SmallCategory I] (H : I ⥤ SSet.{u})

def bousfieldKanUniverseSectionsIso :
    (SSet.uliftFunctor.{max u v,u}).obj (bousfieldKanHolim H) ≅
      bousfieldKanHolim ((AsSmall.down : AsSmall.{v} I ⥤ I) ⋙ H ⋙
        SSet.uliftFunctor.{max u v,u})
```

### [BousfieldKanUniverseWeight.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/BousfieldKanUniverseWeight.lean)

OE01、77原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanUniverseWeight`。

概要：元のBK重みのAsSmall・ULiftによる宇宙変更を、指定したdownを順射とする同型にする。
方針：同じover列を指定upで戻し、元の対象・射・構造射の両合成を確認する。
規約：IS-W2 R02〜R03の係数の宇宙移送則。小さい基底宇宙を0に固定しない。
使われ方：元のBK切断を、全Hom∞比較の同じ持ち上げた添字へ送る。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanUniverseOverLift`。

```lean
universe u v
variable (J : Type u) [SmallCategory J]

def bousfieldKanUniverseOverLift (j : AsSmall.{v} J) :
    Over ((AsSmall.down : AsSmall.{v} J ⥤ J).obj j) ⥤ Over j
```

### [ClassifiedFibrationFiberComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/ClassifiedFibrationFiberComparison.lean)

OE01、80原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedFibrationFiberComparison`。

概要：元の全分類同型による切断比較を、元の二つのfiberの同値と両立させる。
方針：共通の復元への二本のfiber同値を合成し、元の全切断三角形を余単位で戻す。
規約：IS-W2 R03c。元の切断比較との同じ全四角形を保持する。
使われ方：同じBK点から元のnative錐の脚のfiber比較へ戻る。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.classifiedFibrationFiberEquivalence`。

```lean
universe u
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
  (η : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))

def classifiedFibrationFiberEquivalence (b : B _⦋0⦌) :
    QCatEquivalence (vertexFiber p b) (vertexFiber q b)
```

### [ClassifiedFibrationTransport.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/ClassifiedFibrationTransport.lean)

OE01、49原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedFibrationTransport`。

概要：指定された全分類同型の同じ変換を、元の射影の共通の復元への実写像で保持する。
方針：元の復元射に、指定二胞体を回収する既存のunstraightening写像を合成する。
規約：IS-W2 R03bの証明分割。底上の同値だけで指定変換の代用にしない。
使われ方：切断比較の三角形と元の指定BK点の評価の追跡。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.classifiedFibrationTransport`。

```lean
universe u
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
  (η : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))

def classifiedFibrationTransport :
    E ⟶ smallLeftUnstraightening (leftStraighteningInfinityDiagram q)
```

### [ClassifiedSectionsComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/ClassifiedSectionsComparison.lean)

OE01、62原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedSectionsComparison`。

概要：同じ底上のleft fibrationの全分類同型を、元の切断空間の実際の同値へ戻す。
方針：共通の小さいunstraighteningへ厳密な底上の比較を二本作り、相対後合成の同値を合成する。
規約：IS-W2 R03b。底・二つの元の射影を固定し、fiberごとの分類で代用しない。
使われ方：元のBE TotのBK係数からnative錐の切断模型への移送。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSectionsMap_isQCatEquivalence_of_precompositionEquivalence`。

```lean
universe u

theorem simplicialSectionsMap_isQCatEquivalence_of_precompositionEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    IsQCatEquivalence (simplicialSectionsMap f hf)
```

### [ClassifiedSectionsFiberTriangle.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/ClassifiedSectionsFiberTriangle.lean)

OE01、50原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedSectionsFiberTriangle`。

概要：指定分類変換による全切断の三角形を、元の同じ底の各fiberで評価する。
方針：元の全三角形を同じfiber評価で後合成し、後合成と評価の厳密な自然性を使う。
規約：IS-W2 R02〜R03の評価・合成則。零単体だけに弱めない。
使われ方：元のBK点の像からnative錐の同じ脚のfiber比較への接続。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.classifiedLeftFibrationSectionsEquivalence_fiber_triangle`。

```lean
universe u
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
  (η : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))

def classifiedLeftFibrationSectionsEquivalence_fiber_triangle (b : B _⦋0⦌) :
    let r
```

### [ClassifiedSectionsTriangle.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/ClassifiedSectionsTriangle.lean)

OE01、45原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ClassifiedSectionsTriangle`。

概要：元の切断比較を共通の復元へ送ると、指定分類同型の同じ実写像による切断へ戻る。
方針：同じ後合成の同値の余単位を、元の切断の写像で前合成する。
規約：IS-W2 R03bの既存の余単位則。全単体的写像の関手同型を保持する。
使われ方：指定BK点の像・標準脚の同じ復元中での追跡。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.classifiedLeftFibrationSectionsEquivalence_triangle`。

```lean
universe u
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
  (η : FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q))

def classifiedLeftFibrationSectionsEquivalence_triangle :
    FunctorIso
      ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
        simplicialSectionsMap (leftStraighteningInfinityReconstruction q)
          (leftStraighteningInfinityReconstruction_projection q))
      (simplicialSectionsMap (classifiedFibrationTransport p q η)
        (classifiedFibrationTransport_projection p q η))
```

### [SectionFiberEvaluation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/SectionFiberEvaluation.lean)

OE01、48原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionFiberEvaluation`。

概要：元の切断空間の全パラメーターを、同じ底の指定頂点のfiberで評価する。
方針：元の普遍切断を底の定値頂点で制限し、指定fiberへ持ち上げる。
規約：IS-W2 R02〜R03の既存の評価・後合成則。充填性を仮定しない。
使われ方：同じBK点とnative錐の脚を、共通の復元のfiberで照合する。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSectionsFiberEvaluation`。

```lean
universe u
variable {E F B : SSet.{u}}

def simplicialSectionsFiberEvaluation (p : E ⟶ B) (b : B _⦋0⦌) :
    simplicialSections p ⟶ vertexFiber p b
```

### [WeightedDiagramUniverse.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/WeightedDiagramUniverse.lean)

OE01、72原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedDiagramUniverse`。

概要：同じ単体集合値図式をAsSmallとULiftで持ち上げ、同じテンソルを比較する。
方針：指定downの前合成と値のULiftの全忠実性を合わせ、各値の直積の同型を束ねる。
規約：IS-W2 R02〜R03の既存の係数宇宙移送の法則。元の添字射を保つ。
使われ方：同じBK切断空間全体の宇宙変更と指定点の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedDiagramUniverse`。

```lean
universe u v
variable (I : Type u) [SmallCategory I]

def weightedDiagramUniverse : (I ⥤ SSet.{u}) ⥤ (AsSmall.{v} I ⥤ SSet.{max u v})
```

### [WeightedSectionsUniverseComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/WeightedSectionsUniverseComparison.lean)

OE01、47原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionsUniverseComparison`。

概要：元の重み付き切断空間のULiftを、宇宙変更した同じ図式の切断へ送る。
方針：元の普遍評価を同じテンソルの指定同型で移し、nativeな転置を取る。
規約：IS-W2 R02〜R03の係数移送の法則。比較射を別の全単射で置き換えない。
使われ方：同じBK切断空間の宇宙変更と全標準脚の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUniverseEvaluation`。

```lean
universe u v
variable (I : Type u) [SmallCategory I] (W H : I ⥤ SSet.{u})

def weightedSectionsUniverseEvaluation :
    (weightedDiagramUniverse.{u,v} I).obj W ⊗
      (Functor.const (AsSmall.{v} I)).obj
        ((SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H)) ⟶
          (weightedDiagramUniverse.{u,v} I).obj H
```

### [WeightedSectionsUniverseHomEquiv.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/WeightedSectionsUniverseHomEquiv.lean)

OE01、42原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionsUniverseHomEquiv`。

概要：元の小さいパラメーターの切断と、同じパラメーターのULiftからの切断を全単射で合わせる。
方針：同じ指定比較を順写像とし、展開した族を図式の全忠実性で降ろして逆を作る。
規約：IS-W2 R02〜R03の係数移送の法則。Kan性は不要。
使われ方：標準単体による同じ切断空間の宇宙比較の同型性。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUniverseHomEquiv`。

```lean
universe u v
variable (I : Type u) [SmallCategory I] (W H : I ⥤ SSet.{u})

def weightedSectionsUniverseHomEquiv (A : SSet.{u}) :
    (A ⟶ weightedSections W H) ≃
      ((SSet.uliftFunctor.{max u v,u}).obj A ⟶
        weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
          ((weightedDiagramUniverse.{u,v} I).obj H))
```

### [WeightedSectionsUniverseIso.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/WeightedSectionsUniverseIso.lean)

OE01、62原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionsUniverseIso`。

概要：元の指定した重み付き切断空間の宇宙比較射が実同型であることを示す。
方針：同じHom全単射を標準単体に適用し、Yonedaによって元の比較射の各成分と照合する。
規約：IS-W2 R02〜R03の係数移送の法則。順射を選び直さない。
使われ方：同じBK切断の宇宙変更と標準脚の比較。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUniverseSimplexEquiv`。

```lean
universe u v
variable (I : Type u) [SmallCategory I] (W H : I ⥤ SSet.{u})

def weightedSectionsUniverseSimplexEquiv (n : ℕ) :
    ((SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H)) _⦋n⦌ ≃
      (weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
        ((weightedDiagramUniverse.{u,v} I).obj H)) _⦋n⦌
```

### [WeightedSectionsUniversePoints.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/WeightedSectionsUniversePoints.lean)

OE01、68原行。配置：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionsUniversePoints`。

概要：元の指定重み付き錐の零単体を、同じ切断空間の宇宙比較射で追跡する。
方針：標準零単体のYoneda写像を宇宙変更し、同じ普遍評価の転置を照合する。
規約：IS-W2 R02〜R03の係数移送の点での法則。π₀への弱化なし。
使われ方：同じ普遍BK点をHom∞比較の宇宙へ運ぶ。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedDiagramUniverseTensorIso_zero_fst`。

```lean
universe u v
variable (I : Type u) [SmallCategory I]

@[reassoc] theorem weightedDiagramUniverseTensorIso_zero_fst (W : I ⥤ SSet.{u}) :
    ((weightedDiagramUniverse.{u,v} I).obj W ◁ (Functor.const (AsSmall.{v} I)).map
      (uliftStdSimplexIso.{u,max u v} 0).inv) ≫
        (weightedDiagramUniverseTensorIso I W (Δ[0] : SSet.{u})).inv ≫
          (weightedDiagramUniverse I).map (fst W ((Functor.const I).obj (Δ[0] : SSet.{u}))) =
      fst ((weightedDiagramUniverse.{u,v} I).obj W)
        ((Functor.const (AsSmall.{v} I)).obj (Δ[0] : SSet.{max u v}))
```

### [NerveTransformationInversion.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/FullFaithfulAndEssentiallySurjectiveFunctors/NerveTransformationInversion.lean)

OE01、52原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.NerveTransformationInversion`。

概要：通常の自然変換を準圏に送った同じ全ホモトピーを、成分の可逆性から反転する。
方針：元のnerve円柱の各頂点の辺を照合し、既存の全関手圏の辺の判定を使う。
規約：IS-W2 R03dの既存の反転・自然性の法則。対象ごとの同型を選び直さない。
使われ方：全始域・全次数のaugmentationを一つの全関手同型として反転する。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.nerveTransformationPostHomotopy`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  {F G : I ⥤ C} (η : F ⟶ G) {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q)

def nerveTransformationPostHomotopy : SSet.Homotopy (nerveMap F ≫ L) (nerveMap G ≫ L)
```

### [VertexFiberEdgeProjectedArrow.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/IsomorphismsAndIsofibrations/VertexFiberEdgeProjectedArrow.lean)

OE01、40原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiberEdgeProjectedArrow`。

概要：元のfiber内の辺の底への像の類を、同じ底の頂点の恒等射へ合わせる。
方針：包含後の厳密な定値の式と元の恒等辺の式を評価する。
規約：底の後合成も保持し、quasicategory性を仮定しない。
使われ方：元のtwisted Homの左右射影の単位の計算。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_edge_projected_arrow`。

```lean
universe u

lemma vertexFiber_edge_projected_arrow {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D)
    {b : B _⦋0⦌} {v w : (vertexFiber p b) _⦋0⦌} (e : SSet.Edge v w) :
    Arrow.mk (HomotopyCategory.homMk ((e.map (vertexFiberι p b)).map (p ≫ g))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (g.app (Opposite.op ⦋0⦌) b)))
```

### [AnodyneKanTarget.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/LeftAndRightFibrations/AnodyneKanTarget.lean)

OE01、61原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.AnodyneKanTarget`。

概要：Kan標的へのanodyne射はleft anodyneである。
方針：left fibrationの持ち上げ問題をKan標的へ引き戻し、全ホーンの持ち上げ性を使う。
規約：単体集合のモデル構造の公理を仮定しない。元の射そのものの左持ち上げ性。
使われ方：IS-W2 R03f.1、係数のEx∞単位の相対的な比較。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_total_kanComplex`。

```lean
universe u

theorem leftFibration_total_kanComplex {E B : SSet.{u}} [KanComplex B]
    (p : E ⟶ B) [LeftFibration p] : KanComplex E
```

### [CosliceTwistedArrowTargetNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/TheSliceAndJoinConstructions/CosliceTwistedArrowTargetNaturality.lean)

OE01、42原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowTargetNaturality`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.twistedArrowOppositeSwap_naturality`。

```lean
universe u

lemma twistedArrowOppositeSwap_naturality {C D : SSet.{u}} (F : C ⟶ D) :
    edgewiseSubdivisionMap (SSet.opFunctor.map F) ≫ twistedArrowOppositeSwap D =
      twistedArrowOppositeSwap C ≫ edgewiseSubdivisionMap F
```

### [NerveLeftOpInput.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/TruncatedObjectsAndHigherHomotopyCategories/NerveLeftOpInput.lean)

OE01、31原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveLeftOpInput`。

概要：反変の通常関手の nerve 入力を同じ leftOp と二重反転で表す。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sameNerveLeftOp_input`。

```lean
universe u

lemma sameNerveLeftOp_input {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ Dᵒᵖ) :
    nerveMap F ≫ (nerveOppositeIso (C := D)).inv =
      (nerveMap (opOp C) ≫ (nerveOppositeIso (C := Cᵒᵖ)).inv) ≫
        SSet.opFunctor.map (nerveMap F.leftOp)
```

### [NerveOppositeConstant.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/TruncatedObjectsAndHigherHomotopyCategories/NerveOppositeConstant.lean)

OE01、52原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOppositeConstant`。

概要：元のnerveの反転同型の逆は、元の同じ対象の定値単体を保つ。
方針：元の計算できる反転射で同じ定値単体を計算し、同型の逆則で戻す。
規約：IS-W2 R02〜R03の既存反転・定値・逆の法則。追加の同型を選ばない。
使われ方：同じ二変数Hom∞入力の固定始域制限の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso_inv_constant`。

```lean
universe u
variable (C : Type u) [SmallCategory C]

theorem nerveOppositeIso_inv_constant (c : C) (n : ℕ) :
    ((nerveOppositeIso (C := C)).inv.app (Opposite.op ⦋n⦌))
      ((CategoryTheory.Functor.const (Fin (n+1))).obj (Opposite.op c)) =
        (CategoryTheory.Functor.const (Fin (n+1))).obj c
```

### [NerveOppositeEvaluation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/TruncatedObjectsAndHigherHomotopyCategories/NerveOppositeEvaluation.lean)

OE01、32原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOppositeEvaluation`。

概要：元のnerve反転同型の逆を、同じ射列の逆反転へ評価する。
方針：元の逆反転の往復等式を、同じ同型の逆で送る。
規約：IS-W2 R03dの既存の係数移送則。逆を選び直さない。
使われ方：twisted arrowの左射影を、元の反変の始域関手と厳密に合わせる。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso_inv_apply`。

```lean
universe u
variable {C : Type u} [SmallCategory C]

theorem nerveOppositeIso_inv_apply {n : ℕ} (σ : ComposableArrows Cᵒᵖ n) :
    (nerveOppositeIso (C := C)).inv.app (Opposite.op ⦋n⦌) σ =
      SSet.opObjEquiv.symm (nerveUnreverseChain σ)
```

### [NerveOppositeInverseNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/TruncatedObjectsAndHigherHomotopyCategories/NerveOppositeInverseNaturality.lean)

OE01、30原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOppositeInverseNaturality`。

概要：元のnerve反転同型の逆の自然性を、同じ全写像の等式として記録する。
方針：元の順写像の自然性を同じ二つの逆と合成する。
規約：全単体と元の関手を保つ。
使われ方：全source-frame augmentationの反転を元の端点の全図式へ引き戻す。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso_inv_naturality`。

```lean
universe u

theorem nerveOppositeIso_inv_naturality
    {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) :
    nerveMap F.op ≫ (nerveOppositeIso (C := D)).inv =
      (nerveOppositeIso (C := C)).inv ≫ SSet.opFunctor.map (nerveMap F)
```

### [NerveHomUniverseIso.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheLanguageOfInfinityCategories/InfinityCategories/NerveHomUniverseIso.lean)

OE01、55原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.NerveHomUniverseIso`。

概要：同じ宇宙内でHomだけを持ち上げた圏のnerveを元のnerveへ戻す。
方針：同じ全射列に元のULiftHomのup・downを適用する。
規約：元の対象・全射・全単体作用素を保ち、単体に外側のULiftを追加しない。
使われ方：全要素圏のGrothendieck係数を元の全要素nerveへ照合する。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.nerveHomUniverseIso`。

```lean
universe u v
variable (C : Type u) [Category.{v} C]

def nerveHomUniverseIso : nerve (ULiftHom.{max u v} C) ≅ nerve C
```

### [PointCosliceFamilyHomotopyNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/PointCosliceFamilyHomotopyNaturality.lean)

OE01、143原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PointCosliceFamilyHomotopyNaturality`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.pointCosliceFamilyHomotopy_precomp_h`。

```lean
universe u

lemma pointCosliceFamilyHomotopy_precomp_h {A C : SSet.{u}} (c : C _⦋0⦌)
    (a : A ⟶ sliceUnder (yonedaEquiv.symm c)) :
    (a ▷ (Δ[1] : SSet.{u})) ≫ (pointCosliceFamilyHomotopy (𝟙 (sliceUnder (yonedaEquiv.symm c)))).h =
      (pointCosliceFamilyHomotopy a).h
```

### [PointCosliceFiberIntervalFamily.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/PointCosliceFiberIntervalFamily.lean)

OE01、47原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PointCosliceFiberIntervalFamily`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cosliceFiber_intervalFamilyHom_arrow`。

```lean
universe u

lemma cosliceFiber_intervalFamilyHom_arrow {K C : SSet.{u}} {x y : C _⦋0⦌}
    (f : K ⟶ vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) y) :
    Arrow.mk (intervalFamilyHom (f ≫ cosliceFiberToIntervalMappingSpace x y)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy (f ≫ vertexFiberι _ y))))
```

### [CosliceTwistedHomVertexEdge.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/CosliceTwistedHomVertexEdge.lean)

OE01、68原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.CosliceTwistedHomVertexEdge`。

概要：元のcoslice比較の零単体が表す辺は、同じcoslice点の元の辺。
方針：零次元のcollapseを元の重みの同型に合わせ、同じ逆則を適用する。
規約：対象と元の比較・元の点・元の辺を保持し、quasicategory性は仮定しない。
使われ方：元のnative単位の辺の類を、同じHom空間の点の比較へ戻す。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceEdgewiseCollapse_zero`。

```lean
universe u

lemma cosliceEdgewiseCollapse_zero :
    cosliceEdgewiseCollapse.{u} ⦋0⦌ =
      (joinIso (stdSimplex.opIso ⦋0⦌) (Iso.refl (Δ[0] : SSet.{u}))).hom
```

### [TwistedArrowEdgeComposition.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedArrowEdgeComposition.lean)

OE01、170原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowEdgeComposition`。

概要：元の twisted-arrow の辺の四つの射影の合成則。
方針：同じ三単体の計算を元の実際の辺へ移し、同じ零次の包含で端点を保つ。
規約：任意の単体集合で述べ、Kan 性や模型構造は仮定しない。
使われ方：元の corrected pairing の指定成分の単位・合成の計算。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedSquare_composite_of_edge_coordinates`。

```lean
universe u

lemma twistedSquare_composite_of_edge_coordinates {C : SSet.{u}}
    (σ : (Δ[3] : SSet.{u}) ⟶ C)
    {q x y z : C _⦋0⦌} (p : SSet.Edge q x) (a : SSet.Edge x y)
    (r : SSet.Edge y z) (b : SSet.Edge q z)
    (hp : ((twistedSquareStdEdge 3 0 1 (by decide)).map σ).edge = p.edge)
    (ha : ((twistedSquareStdEdge 3 1 2 (by decide)).map σ).edge = a.edge)
    (hr : ((twistedSquareStdEdge 3 2 3 (by decide)).map σ).edge = r.edge)
    (hb : ((twistedSquareStdEdge 3 0 3 (by decide)).map σ).edge = b.edge) :
    HomotopyCategory.homMk p ≫ HomotopyCategory.homMk a ≫
      HomotopyCategory.homMk r = HomotopyCategory.homMk b
```

### [TwistedArrowHomComposition.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedArrowHomComposition.lean)

OE01、52原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHomComposition`。

概要：同じ twisted-arrow の左右射影の合成則をホモトピー圏の元の射で述べる。
方針：元の射の代表辺を取り、既存の反対ホモトピー圏の比較と三単体の計算を使う。
規約：結論は元の射自身についての等式で、新しい逆や成分を選ぶ結論ではない。
使われ方：元の corrected pairing の同じ指定関手同型の成分の合成則。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHom_composition`。

```lean
universe u

lemma twistedArrowHom_composition {C : SSet.{u}} [Quasicategory C]
    {a b : (TwistedArrow C) _⦋0⦌}
    (f : HomotopyCategory.mk a ⟶ HomotopyCategory.mk b) :
    ((homotopyOppositeEquivalence C).functor.map
      ((SSet.mapHomotopyCategory (edgewiseLeft C)).map f)).unop ≫
        HomotopyCategory.homMk (twistedArrowVertexEdge a) ≫
          (SSet.mapHomotopyCategory (edgewiseRight C)).map f =
            HomotopyCategory.homMk (twistedArrowVertexEdge b)
```

### [TwistedArrowThreeSimplexCoordinates.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedArrowThreeSimplexCoordinates.lean)

OE01、183原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowThreeSimplexCoordinates`。

概要：twisted-arrow の一辺を表す三単体の四つの辺を、同じ重みの座標で照合する。
方針：既存の左右の包含・面の座標と、三単体の三辺の合成則を使う。
規約：任意の単体集合で述べ、Kan 性や模型構造を仮定しない。
使われ方：同じ corrected pairing の元の単位と射影を計算するための前提の法則。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedSquareStdEdge`。

```lean
universe u

def twistedSquareStdEdge (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    SSet.Edge (X := (Δ[n] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm i) (stdSimplex.obj₀Equiv.symm j)
```

### [TwistedArrowVertexEdgeNerve.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedArrowVertexEdgeNerve.lean)

OE01、47原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowVertexEdgeNerve`。

概要：元の実射の twisted-arrow 頂点と nerve の同じ辺の合成の照合。
方針：同じ重みの逆と同じ合成三角形の像を計算する。
規約：始域と標的と元の実射を保ち、標的に模型構造を仮定しない。
使われ方：元の単位ラベルの original pairing の像の同じ二射の合成への照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowVertexEdge_nerve_arrow`。

```lean
universe u

lemma twistedArrowVertexEdge_nerve_arrow {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (F : nerve C ⟶ E) {x y : C} (g : x ⟶ y) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      ((edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm (ComposableArrows.mk₁ g) ≫ F))) =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk g).map F))
```

### [TwistedHomIdentityPoint.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedHomIdentityPoint.lean)

OE01、68原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomIdentityPoint`。

概要：元の始点固定の恒等点を同じ両端固定のHom空間へ制限する。
方針：元のfiber同型の包含則と元の恒等点の定値の式を適用する。
規約：元のtwistedArrowSourceIdentityそのものを使い、恒等点を選び直さない。
使われ方：元のnative単位点との同じHom空間での比較。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpaceIdentityPoint`。

```lean
universe u

def twistedArrowHomSpaceIdentityPoint {C : SSet.{u}} (x : C _⦋0⦌) :
    (twistedArrowHomSpace x x) _⦋0⦌
```

### [TwistedHomIntervalFamilyComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedHomIntervalFamilyComparison.lean)

OE01、70原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomIntervalFamilyComparison`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceFiberRightMappingEquivalence_interval_family`。

```lean
universe u

lemma cosliceFiberRightMappingEquivalence_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (f : K ⟶ vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) y) :
    intervalFamilyHom (f ≫ (cosliceFiberRightMappingEquivalence x y).hom ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (f ≫ cosliceFiberToIntervalMappingSpace x y)
```

### [TwistedHomOppositeIntervalFamilyComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedHomOppositeIntervalFamilyComparison.lean)

OE01、57原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomOppositeIntervalFamilyComparison`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomOppositePinchedEquivalence_interval_family`。

```lean
universe u

lemma twistedArrowHomOppositePinchedEquivalence_interval_family {K C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (g : K ⟶ (twistedArrowHomSpace x y).op) :
    intervalFamilyHom (g ≫ (twistedArrowHomOppositePinchedEquivalence x y).hom ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (g ≫ (isQCatEquivalence_of_trivialKanFibration
        (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
        edgewiseRight (twistedArrowHomSpace x y) ≫
        (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
        cosliceFiberToIntervalMappingSpace x y)
```

### [TwistedHomPinchedComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedHomPinchedComparison.lean)

OE01、73原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomPinchedComparison`。

概要：同じtwisted Homとその反転を、既存のcosliceとedgewiseの比較でpinched Homへ運ぶ。
方針：既存比較の指定された逆を合成し、同じ単位三角形を全関手同型で保持する。
規約：任意の準圏に対する既存比較の合成。単体集合のモデル構造を仮定しない。
使われ方：元のnative fiber射と基準roof射を同じ標的で照合する。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomPinchedEquivalence`。

```lean
universe u
variable {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌)

def twistedArrowHomPinchedEquivalence :
    QCatEquivalence (twistedArrowHomSpace x y) (Basic.pinchedHom x y)
```

### [TwistedHomVertexEdgeClasses.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedHomVertexEdgeClasses.lean)

OE01、70原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomVertexEdgeClasses`。

概要：同じ両端固定のtwisted Hom内の辺・頂点同型は、元の矢印の類を保持する。
方針：元の左右の定値射影を恒等射へ合わせ、同じ三辺の合成則へ適用する。
規約：元の点・元の辺・元の射影を使う。
使われ方：元のcoslice比較の同じ単位三角形を通す。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace_edge_arrow_eq`。

```lean
universe u

lemma twistedArrowHomSpace_edge_arrow_eq {C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} {v w : (twistedArrowHomSpace x y) _⦋0⦌}
    (e : SSet.Edge v w) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v.val)) =
      Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge w.val))
```

### [TwistedHomVertexIsoOfArrowEq.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedHomVertexIsoOfArrowEq.lean)

OE01、55原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomVertexIsoOfArrowEq`。

概要：同じHom空間の元の二点の矢印の類の一致を、元の二点の同型へ戻す。
方針：元のcoslice比較の同じ逆と単位三角形を通して既存のcosliceの判定を使う。
規約：元の二点と両端を保持し、頂点同型を新たな前提にはしない。
使われ方：IS-W2 R03i、同じnative単位点の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.nonempty_twistedArrowHomSpace_vertexIso_of_arrow_eq`。

```lean
universe u

lemma nonempty_twistedArrowHomSpace_vertexIso_of_arrow_eq {C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} {v w : (twistedArrowHomSpace x y) _⦋0⦌}
    (h : Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v.val)) =
      Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge w.val))) :
    Nonempty (VertexIso v w)
```

### [TwistedNerveOppositeSimplex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedNerveOppositeSimplex.lean)

OE01、181原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedNerveOppositeSimplex`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowOppositeSwap_nerve_reverse`。

```lean
universe u

lemma twistedArrowOppositeSwap_nerve_reverse {C : Type u} [Category.{u} C] (n : ℕ)
    (τ : (nerve C) _⦋n+n+1⦌) :
    (twistedArrowOppositeSwap (nerve C)).app (Opposite.op ⦋n⦌)
      ((edgewiseWeightIso n).hom ≫ SSet.yonedaEquiv.symm (nerveReverseChain τ) ≫
        (nerveOppositeIso (C := C)).inv) =
      (edgewiseWeightIso n).hom ≫ SSet.yonedaEquiv.symm τ
```

### [TwistedPairingCoordinates.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedPairingCoordinates.lean)

OE01、93原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingCoordinates`。

概要：元の長い単体の両半分を、同じedgewiseの頂点座標で照合する。
方針：左の二重反転と右の平行移動を計算し、同じ対象の移送を記録する。
規約：IS-W2 R03dの座標・自然性の法則。全単体の写像はここではまだ束ねない。
使われ方：同じtwisted arrowの両端の射影と全再添字付けの検査。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedPairingLeftVertex_lt`。

```lean
universe u

theorem twistedPairingLeftVertex_lt (n : ℕ) (i : Fin (n+1)) :
    (edgewiseLeftVertex n i).val < n+1
```

### [TwistedPairingCrossNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedPairingCrossNaturality.lean)

OE01、50原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingCrossNaturality`。

概要：元の射の可換四角形から、交差射の基点変更と全再添字付けの等式を得る。
方針：同じ交差射の両側の合成則と、元の同じ対角射の自然性を使う。
規約：IS-W2 R03dの合成・自然性の法則。零番以外の新しい射を選ばない。
使われ方：長い単体が任意の面・退化に厳密に自然であることの交差部分。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedPairingCross_diagonal`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
  (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j)
  {n : ℕ} (σ : Fin (n+1) ⥤ I)

theorem twistedPairingCross_diagonal (i : Fin (n+1)) :
    twistedPairingCross A B h σ i i = h (σ.obj i)
```

### [TwistedPairingFunctoriality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedPairingFunctoriality.lean)

OE01、41原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingFunctoriality`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedPairingNerveMap_precomp`。

```lean
universe u

lemma twistedPairingNerveMap_precomp {J I C : Type u} [Category.{u} J] [Category.{u} I]
    [Category.{u} C] (H : J ⥤ I) (A : I ⥤ Cᵒᵖ) (B : I ⥤ C)
    (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) :
    nerveMap H ≫ twistedPairingNerveMap A B h hh =
      twistedPairingNerveMap (H ⋙ A) (H ⋙ B) (fun i => h (H.obj i))
        (fun {_ _} f => hh (H.map f))
```

### [TwistedPairingNerve.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedPairingNerve.lean)

OE01、48原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingNerve`。

概要：同じ反変・共変の両端を持つ全射の要素を、一つのtwisted arrowの全写像へ送る。
方針：元の長い単体を同じedgewise重みの同型で戻し、全再添字付けの等式を使う。
規約：IS-W2 R03dの同じ射列の全自然性。点ごとの写像の選択ではない。
使われ方：元の全source frameの要素圏から正本Hom∞への表示された比較。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedPairingWeightIso_reindex`。

```lean
universe u

theorem twistedPairingWeightIso_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    edgewiseWeight.{u}.map α ≫ (edgewiseWeightIso n).hom =
      (edgewiseWeightIso m).hom ≫ stdSimplex.map
        (SimplexCategory.mkHom (edgewiseWeightReindexOrderHom.{u} α))
```

### [TwistedPairingOpposite.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedPairingOpposite.lean)

OE01、46原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingOpposite`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedPairingNerveMap_opposite_swap`。

```lean
universe u

lemma twistedPairingNerveMap_opposite_swap {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) :
    twistedPairingNerveMap (B ⋙ (opOpEquivalence C).inverse) A (fun i => (h i).op)
      (by
        intro i j f
        apply Quiver.Hom.unop_inj
        simp only [CategoryTheory.unop_comp, Quiver.Hom.unop_op, Category.assoc]
        change (A.map f).unop ≫ h i ≫ B.map f = h j
        exact hh f) ≫
      edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
        twistedArrowOppositeSwap (nerve C) = twistedPairingNerveMap A B h hh
```

### [TwistedPairingProjections.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedPairingProjections.lean)

OE01、67原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingProjections`。

概要：同じtwisted arrowの全写像の二射影は、元の両端の全関手そのもの。
方針：左右の標準区間の全制限と、同じnerve反転同型の逆の評価を合成する。
規約：IS-W2 R03dの全写像の自然性・係数移送則。頂点だけの照合ではない。
使われ方：元のsource frameの射を、同じ底の正本Hom∞へ送る比較の射影式。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedPairingNerveMap_right`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
  (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j)

theorem twistedPairingNerveMap_right :
    twistedPairingNerveMap A B h hh ≫ edgewiseRight (nerve C) = nerveMap B
```

### [TwistedPairingReindex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedPairingReindex.lean)

OE01、159原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingReindex`。

概要：同じ長い射列は、実際のedgewise重みの全再添字付けと厳密に両立する。
方針：元の左右の頂点座標で対象と実射を照合し、交差射の基点変更則を使う。
規約：IS-W2 R03dの同じ単体と自然性の法則。頂点ごとの比較で代用しない。
使われ方：全source frameの要素圏のnerveをtwisted arrowへ送る全写像。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedPairingLeftVertex_index`。

```lean
universe u

theorem twistedPairingLeftVertex_index {n : ℕ} (i : Fin (n+n+1+1)) (hi : i.val < n+1) :
    edgewiseLeftVertex n (twistedPairingLeftIndex i hi) = i
```

### [TwistedPairingRestrictions.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedPairingRestrictions.lean)

OE01、69原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingRestrictions`。

概要：同じ長い単体を左右の標準区間へ制限すると、元の両端の射列に戻る。
方針：元の頂点座標と同じ実射を、関手の全対象・全射で照合する。
規約：IS-W2 R03dの既存の係数移送・自然性。頂点の一致だけで代用しない。
使われ方：twisted arrowへの全写像の二射影を元の両端と厳密に合わせる。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedPairingLeftOrder_lt`。

```lean
universe u

theorem twistedPairingLeftOrder_lt (n : ℕ) (i : Fin (n+1)) :
    (joinLeftOrderHom n n i).val < n+1
```

### [TwistedPairingSimplex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedPairingSimplex.lean)

OE01、151原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingSimplex`。

概要：同じ反変・共変の両端を持つ射の列を、twisted arrowの一つの長い単体にする。
方針：左半分に始域の逆順、右半分に標的の順序を置き、元の零番の射でつなぐ。
規約：IS-W2 R03dの指定された射の全次数表示。新たな逆や単体充填は選ばない。
使われ方：全source frameの要素を正本のtwisted arrowへ送る写像の各単体。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedPairingLeftIndex`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)

def twistedPairingLeftIndex {n : ℕ} (i : Fin (n+n+1+1)) (hi : i.val < n+1) : Fin (n+1)
```

### [TwistedPairingZero.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/TwistedPairingZero.lean)

OE01、60原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingZero`。

概要：元の全 twisted pairing の零単体は元の実射そのもの。
方針：元の長い単体の零次の対象と射を計算し、同じ後合成を保つ。
規約：元の四角形の全自然性と同じモデル源を使い、新たな単体を選ばない。
使われ方：全 pairing の元の単位ラベルの像の計算。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedPairingSimplex_zero`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
    (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)

lemma twistedPairingSimplex_zero (i : I) :
    twistedPairingSimplex A B h (nerveVertex i) = ComposableArrows.mk₁ (h i)
```

### [ArrowMiddleIdentity.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Project/FibrationAuxiliaries/Categories/ArrowMiddleIdentity.lean)

OE01、37原行。配置：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.ArrowMiddleIdentity`。

概要：元の合成の左右が同じ恒等射のArrowなら、中央と全合成のArrowは一致する。
方針：同じ端点の等式を外し、元の左右の恒等射を簡約する。
規約：元の全射と端点を保持する。
使われ方：同じtwisted Homの元の辺の合成則。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.arrow_middle_eq_of_outer_identity_arrows`。

```lean
universe u v

lemma arrow_middle_eq_of_outer_identity_arrows {D : Type u} [Category.{v} D]
    {q x y z x₀ y₀ : D} (p : q ⟶ x) (a : x ⟶ y) (r : y ⟶ z) (b : q ⟶ z)
    (hp : Arrow.mk p = Arrow.mk (𝟙 x₀)) (hr : Arrow.mk r = Arrow.mk (𝟙 y₀))
    (h : p ≫ a ≫ r = b) : Arrow.mk a = Arrow.mk b
```

### [ArrowMiddleUnit.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Project/FibrationAuxiliaries/Categories/ArrowMiddleUnit.lean)

OE01、43原行。配置：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.ArrowMiddleUnit`。

概要：同じ合成の両端を同じ可逆射に合わせ、中央の射を元の恒等射へ戻す。
方針：Arrowの端点の等式を外して、同じ圏で左右の可逆射を相殺する。
規約：端点と元の射を保持する。
使われ方：元の補正単位の像の同じ三辺の合成則の計算。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.arrow_middle_unit_of_outer_arrow_equalities`。

```lean
universe u v

lemma arrow_middle_unit_of_outer_arrow_equalities {D : Type u} [Category.{v} D]
    {q x y z q₀ x₀ z₀ : D} (p : q ⟶ x) (a : x ⟶ y) (r : y ⟶ z) (b : q ⟶ z)
    (p₀ : q₀ ⟶ x₀) (r₀ : x₀ ⟶ z₀) [IsIso p] [IsIso r]
    (hp : Arrow.mk p = Arrow.mk p₀) (hr : Arrow.mk r = Arrow.mk r₀)
    (hb : Arrow.mk b = Arrow.mk (p₀ ≫ r₀)) (h : p ≫ a ≫ r = b) :
    Arrow.mk a = Arrow.mk (𝟙 x₀)
```

### [OppositeFunctorIsoEvaluation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Project/FibrationAuxiliaries/Categories/OppositeFunctorIsoEvaluation.lean)

OE01、86原行。配置：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIsoEvaluation`。

概要：元の反転 Hom 対応と指定された全同型の逆成分の一点評価。
方針：同じホモトピーの代表と反転した円柱の辺を比較し、既存の成分評価の式を使う。
規約：元の反転対応と同じ逆成分を保持する。模型構造と計算上限は増やさない。
使われ方：元の source-frame augmentation の逆成分を反転ホモトピー圏から戻す。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeHomotopyVertexEdge_unop`。

```lean
universe u

lemma oppositeHomotopyVertexEdge_unop {A D : SSet.{u}} {F G : A ⟶ D}
    (H : SSet.Homotopy F G) (x : A _⦋0⦌) :
    edgeUnop (X := D) (simplicialHomotopyVertexEdge (homotopyOpposite H)
      (SSet.opObjEquiv.symm x)).toTruncated =
        (simplicialHomotopyVertexEdge H x).toTruncated
```

### [OppositeFunctorIsoWhisker.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Project/FibrationAuxiliaries/Categories/OppositeFunctorIsoWhisker.lean)

OE01、120原行。配置：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIsoWhisker`。

概要：同じ関手同型の反転と前合成・端点輸送の両立。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.sameVertexIso_op_inv`。

```lean
universe u

lemma sameVertexIso_op_inv {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e : VertexIso x y) :
    e.op.inv = homotopyCategoryOpHomEquiv x y e.hom
```

### [FullyFaithfulFunctorIsoPrecomposition.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Project/FibrationAuxiliaries/FunctorCategories/FullyFaithfulFunctorIsoPrecomposition.lean)

OE01、59原行。配置：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoPrecomposition`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.fullyFaithfulPreimageFunctorIso_precomp`。

```lean
universe u

lemma fullyFaithfulPreimageFunctorIso_precomp {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (hi : IsFullyFaithful ((pre i).app X))
    {F G : B ⟶ X} (e : FunctorIso (i ≫ F) (i ≫ G)) :
    FunctorIso.precomp (f := F) (g := G)
      (hi.preimageVertexIso (x := functorVertex F) (y := functorVertex G) e) i = e
```

### [FunctorIsoConstantFamily.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Project/FibrationAuxiliaries/FunctorCategories/FunctorIsoConstantFamily.lean)

OE01、46原行。配置：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoConstantFamily`。

概要：元の関手同型の定値の全族を同じ頂点成分の像へ正規化する。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sameFunctorIso_constant_family`。

```lean
universe u

lemma sameFunctorIso_constant_family {K X : SSet.{u}} [Quasicategory K] [Quasicategory X]
    (T : SSet.{u}) {f g : K ⟶ X} (e : FunctorIso f g) (x : K _⦋0⦌) :
    (constantFunctorCompIso T x f).inv ≫
      (e.precomp (SSet.const x : T ⟶ K)).hom ≫
      (constantFunctorCompIso T x g).hom =
        constantFunctorHomMap T (e.app x).hom
```

### [FunctorHomEvaluationArrow.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Project/LocalizationAndKanExtensionAuxiliaries/FunctorCategories/FunctorHomEvaluationArrow.lean)

OE01、35原行。配置：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationArrow`。

概要：元の全二胞体の同じ点での評価を、元の評価関手の射の像と合わせる。
方針：同じ両端のeqToHomだけをArrowの式から外す。
規約：標的の準圏性を仮定せず、元の二胞体を保つ。
使われ方：元の全straighteningの同じ射の評価。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_arrow`。

```lean
universe u

lemma functorHomEvaluate_arrow {K X : SSet.{u}} {U V : K ⟶ X}
    (a : FunctorHom U V) (x : K _⦋0⦌) :
    Arrow.mk (functorHomEvaluate a x) =
      Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := X) x)).toFunctor.map a)
```

### [UnderCosliceCylinder.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Project/LocalizationAndKanExtensionAuxiliaries/NerveComparison/UnderCosliceCylinder.lean)

OE01、209原行。配置：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderCosliceCylinder`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderLift_pointCosliceFamilyHomotopy`。

```lean
universe u

lemma nerveUnderLift_pointCosliceFamilyHomotopy {I C : Type u} [Category.{u} I]
    [Category.{u} C] {c : C} {V : I ⥤ C} (η : (Functor.const I).obj c ⟶ V) :
    (pointCosliceFamilyHomotopy (nerveMap (Under.lift V η) ≫ nerveUnderMap c)).h =
      (nerveNatTransHomotopy η).h
```

### [UnderLiftTwistedPairing.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Project/LocalizationAndKanExtensionAuxiliaries/NerveComparison/UnderLiftTwistedPairing.lean)

OE01、46原行。配置：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderLiftTwistedPairing`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderLift_comp_cosliceTwistedArrowMap`。

```lean
universe u

lemma nerveUnderLift_comp_cosliceTwistedArrowMap {I C : Type u} [Category.{u} I]
    [Category.{u} C] {c : C} {V : I ⥤ C} (η : (Functor.const I).obj c ⟶ V) :
    nerveMap (Under.lift V η) ≫ nerveUnderMap c ≫ cosliceTwistedArrowMap (nervePoint c) =
      twistedPairingNerveMap ((Functor.const I).obj (Opposite.op c)) V (fun i => η.app i)
        (fun {_ _} f => by simpa using (η.naturality f).symm)
```

### [UnderOppositePairing.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Project/LocalizationAndKanExtensionAuxiliaries/NerveComparison/UnderOppositePairing.lean)

OE01、92原行。配置：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderOppositePairing`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderLift_opposite_pairing`。

```lean
universe u

lemma nerveUnderLift_opposite_pairing {I C : Type u} [Category.{u} I] [Category.{u} C]
    {c : C} {V : I ⥤ C} (η : V ⟶ (Functor.const I).obj c) :
    nerveMap (Under.lift (X := Opposite.op c) V.op (NatTrans.op η)) ≫ nerveUnderMap (Opposite.op c) ≫
      cosliceTwistedArrowMap (nervePoint (Opposite.op c)) ≫
        edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
          twistedArrowOppositeSwap (nerve C) =
      twistedPairingNerveMap V.op ((Functor.const Iᵒᵖ).obj c)
        (fun i => η.app i.unop) (by
          intro i j f
          change V.map f.unop ≫ η.app i.unop ≫ 𝟙 c = η.app j.unop
          calc
            _ = V.map f.unop ≫ η.app i.unop := congrArg (fun g => V.map f.unop ≫ g)
              (Category.comp_id (η.app i.unop))
            _ = η.app j.unop := (η.naturality f.unop).trans (Category.comp_id _))
```

### [UnderRightOpPairing.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Project/LocalizationAndKanExtensionAuxiliaries/NerveComparison/UnderRightOpPairing.lean)

OE01、87原行。配置：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderRightOpPairing`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderLift_rightOp_pairing`。

```lean
universe u

lemma nerveUnderLift_rightOp_pairing {I C : Type u} [Category.{u} I] [Category.{u} C]
    {c : C} {V : Iᵒᵖ ⥤ C} (η : V ⟶ (Functor.const Iᵒᵖ).obj c) :
    nerveMap (Under.lift (X := Opposite.op c) V.rightOp (NatTrans.rightOp η)) ≫ nerveUnderMap (Opposite.op c) ≫
      cosliceTwistedArrowMap (nervePoint (Opposite.op c)) ≫
        edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
          twistedArrowOppositeSwap (nerve C) =
      twistedPairingNerveMap V.rightOp ((Functor.const I).obj c)
        (fun i => η.app (Opposite.op i)) (by
          intro i j f
          change V.map f.op ≫ η.app (Opposite.op i) ≫ 𝟙 c = η.app (Opposite.op j)
          calc
            _ = V.map f.op ≫ η.app (Opposite.op i) := congrArg (fun g => V.map f.op ≫ g)
              (Category.comp_id (η.app (Opposite.op i)))
            _ = η.app (Opposite.op j) := (η.naturality f.op).trans (Category.comp_id _))
```

### [UnderTwistedPairing.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/InfinityCategories/Project/LocalizationAndKanExtensionAuxiliaries/NerveComparison/UnderTwistedPairing.lean)

OE01、148原行。配置：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderTwistedPairing`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveUnderMap_comp_cosliceTwistedArrowMap`。

```lean
universe u

lemma nerveUnderMap_comp_cosliceTwistedArrowMap {C : Type u} [Category.{u} C] (c : C) :
    nerveUnderMap c ≫ cosliceTwistedArrowMap (nervePoint c) =
      twistedPairingNerveMap ((Functor.const (Under c)).obj (Opposite.op c)) (Under.forget c)
        (fun i => i.hom) (fun {_ _} f => by simp)
```

### [BousfieldKanCellAttachment.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanCellAttachment.lean)

OE02、77原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellAttachment`。

概要：同じ自由BK細胞を、元の重みの二つの連続する骨格へ貼り付ける。
方針：終頂点の非退化単体のYoneda写像を自由生成元の降下射で束ねる。
規約：IS-W2 R03aの証明分割。骨格も単体も元のBK重みのもの。
使われ方：自由境界の押し出しによるBK重み全体の射影cofibrancy。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bkCellSimplex`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

def bkCellSimplex {n : ℕ} (c : (nerve I).nonDegenerate n) :
    (nerve (Over (c.val.obj (Fin.last n)))).nonDegenerate n
```

### [BousfieldKanCellCoproduct.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanCellCoproduct.lean)

OE02、70原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellCoproduct`。

概要：BK自由細胞の各評価は、元の非退化単体の自由表示で添字付けた余積。
方針：同じ成分への包含と全成分からの降下射を単体ごとに記述する。
規約：IS-W2 R03aの骨格押し出しの証明分割。
使われ方：既存の単体集合の骨格の押し出しとの厳密な照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bkCellComponentInclusion`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

def bkCellComponentInclusion {n : ℕ} {i : I} (s : NondegenerateData I n i)
    (X : SSet.{u}) : X ⟶ ((bkCellTensor I n).obj X).obj i
```

### [BousfieldKanCellEvaluation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanCellEvaluation.lean)

OE02、81原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellEvaluation`。

概要：自由細胞の各成分の貼り付け射を、元の非退化単体のYoneda写像に照合する。
方針：終頂点からの輸送の厳密な式と、同じYoneda写像の自然性を使う。
規約：IS-W2 R03aの同じ骨格押し出しの証明分割。
使われ方：既存の相対細胞の押し出しの四つの射との一致。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bkCellComponentInclusion_cellDesc`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

@[reassoc] theorem bkCellComponentInclusion_cellDesc {n : ℕ} {i : I}
    (s : NondegenerateData I n i) (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n))) :
    bkCellComponentInclusion I s X ≫ (bkCellDesc I X Z f).app i =
      f s.1 ≫ Z.map s.2
```

### [BousfieldKanCellLifting.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanCellLifting.lean)

OE02、58原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellLifting`。

概要：BKの同じ自由テンソル細胞は境界生成族の左持ち上げ性を保つ。
方針：各終頂点で元の境界の持ち上げを取り、同じ生成元の降下射で全射へ束ねる。
規約：IS-W2 R03aの自由境界付着の証明分割。SSetモデルの追加仮定なし。
使われ方：BK骨格の各付着の射影cofibration性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bkCellTensor_map_llp`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

theorem bkCellTensor_map_llp (n : ℕ) {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.modelCategoryQuillen.I f) :
    (boundaries I).rlp.llp ((bkCellTensor I n).map f)
```

### [BousfieldKanCellReindex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanCellReindex.lean)

OE02、75原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellReindex`。

概要：空の部分複体の相対細胞とBK自由細胞の添字を厳密に照合する。
方針：既存の相対細胞の非退化単体を自由表示に写し、余積の一意性で同型を作る。
規約：IS-W2 R03aの押し出しの証明分割。新たな重みは選ばない。
使われ方：Mathlibの同じ骨格の押し出しを自由図式の押し出しに移す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bkInitialCellEquiv`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

def bkInitialCellEquiv (n : ℕ) (i : I) :
    relativeCellComplexOfMono.Cell ((⊥ : (nerve (Over i)).Subcomplex).ι) n ≃
      NondegenerateData I n i
```

### [BousfieldKanCellTensor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanCellTensor.lean)

OE02、107原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellTensor`。

概要：BK自由細胞に任意の単体集合をテンソルし、終頂点の生成元で全射を表示する。
方針：同じ非退化射列の定値単体集合を使い、最後の射による輸送で降下射を記述。
規約：IS-W2 R03aの自由境界付着の証明分割。SSetのモデル構造を仮定しない。
使われ方：各自由境界の持ち上げを全BK細胞の持ち上げへ束ねる。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bkCellWeight`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

def bkCellWeight (n : ℕ) : I ⥤ SSet.{u}
```

### [BousfieldKanChosenComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanChosenComparison.lean)

OE02、57原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanChosenComparison`。

概要：元のBK重みから、指定された二重反対化した一点重みへの一つの全図式射を選ぶ。
方針：BKの射影cofibrancyと、指定された一点比較の各値の境界右持ち上げ性を使う。
規約：IS-W2 R03aの同じ比較射の構成。Kan係数ごとに選び直さない。
使われ方：全係数図式の切断空間に対する同じ制限写像。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.framedLimitWeightComparison`。

```lean
universe u
variable (J : Type u) [SmallCategory J]

abbrev framedLimitWeightComparison
```

### [BousfieldKanCofibrant.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanCofibrant.lean)

OE02、51原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCofibrant`。

概要：元のBK重みは、自由境界生成族に関して射影cofibrant。
方針：同じ骨格の押し出しと逐次余極限を、既存の左持ち上げ性の安定性へ渡す。
規約：IS-W2 R03aの細胞分解の証明分割。SSetモデル構造を仮定しない。
使われ方：指定された一点重みへの同じ比較射を選ぶ。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bkSkeletonZeroIsInitial`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

def bkSkeletonZeroIsInitial : IsInitial ((bkSkeleton I).obj 0)
```

### [BousfieldKanComparisonValues.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanComparisonValues.lean)

OE02、53原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanComparisonValues`。

概要：一つの指定BK比較射は、元の各値で弱ホモトピー同値。
方針：over圏の元の終対象と一点比較の境界右類から両方の増大の弱同値を得る。
規約：IS-W2 R03aの指定比較の照合。各値のKan性をBK重みに要求しない。
使われ方：射影cofibrant重みのHom不変性を同じ比較射へ適用する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bousfieldKanWeight_isWeaklyContractible`。

```lean
universe u

theorem bousfieldKanWeight_isWeaklyContractible (I : Type u) [SmallCategory I] (i : I) :
    IsWeaklyContractible ((bousfieldKanWeight I).obj i)
```

### [BousfieldKanExInfinityUnit.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanExInfinityUnit.lean)

OE02、53原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanExInfinityUnit`。

概要：同じBK切断に、元の係数のEx∞単位を適用する。
方針：Kan係数上の単位の弱同値性と既存のBK係数不変性を使う。
規約：IS-W2 R02〜R03の既存の係数移送則。元の指定点の等式を保持する。
使われ方：同じBE TotのBK錐を全Hom∞比較の第零図式へ送る。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bousfieldKanExInfinityCoefficientUnit`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

def bousfieldKanExInfinityCoefficientUnit (H : I ⥤ SSet.{u}) : H ⟶ H ⋙ exInfinity
```

### [BousfieldKanNativeFiberPoint.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanNativeFiberPoint.lean)

OE02、99原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanNativeFiberPoint`。

概要：元の指定BK点をweighted nerveの同じfiberで評価すると、恒等射での元の係数を回収する。
方針：元の切断の普遍評価とパラメーター自然性を用い、同じ零単体の初区間を計算する。
規約：IS-W2 R02〜R03の既存構成の評価・単位則。Kan性の追加なし。
使われ方：同じBE Totのnative錐の脚と、元の指定BK錐の係数での照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bousfieldKanSectionsMap_lift_evaluation`。

```lean
universe u
variable (I : Type u) [SmallCategory I] (H : I ⥤ SSet.{u})

theorem bousfieldKanSectionsMap_lift_evaluation {A : SSet.{u}}
    (η : bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) :
    (nerve I ◁ (weightedSectionsLift η ≫ bousfieldKanSectionsMap H)) ≫
      simplicialSectionsEvaluation (weightedNerveProjection H) =
        weightedNerveSectionFromTransform η
```

### [BousfieldKanSkeletonPushout.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanSkeletonPushout.lean)

OE02、81原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanSkeletonPushout`。

概要：元のBK重みの連続する骨格は、同じ自由境界細胞を付着する押し出し。
方針：各評価の相対細胞の押し出しを指定余積同型で輸送し、評価で反映する。
規約：IS-W2 R03aの細胞分解の証明分割。重みの置換は行わない。
使われ方：BK重み全体の射影cofibrancy。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bkSkeletonInitialIso`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

def bkSkeletonInitialIso (n : ℕ) (i : I) :
    (skeletonOfMono ((⊥ : (nerve (Over i)).Subcomplex).ι) n : SSet.{u}) ≅
      ((bkSkeleton I).obj n).obj i
```

### [BousfieldKanUniverseCoefficientPoint.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanUniverseCoefficientPoint.lean)

OE02、65原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanUniverseCoefficientPoint`。

概要：同じBK点のfiber評価を、元の宇宙変更とEx∞係数単位の前まで追跡する。
方針：指定downの恒等射での評価と元の係数単位の合成を計算する。
規約：IS-W2 R02〜R03の既存の宇宙変更・係数移送の評価則。
使われ方：BE Totのnative錐の脚を、同じ元のraw係数で照合する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bousfieldKanUniverseCone_identityVertex`。

```lean
universe u v
variable (I : Type u) [SmallCategory I] {H : I ⥤ SSet.{u}}

theorem bousfieldKanUniverseCone_identityVertex (s : bousfieldKanWeight I ⟶ H) (i : I) :
    ((bousfieldKanUniverseCone.{u,v} I s).app (AsSmall.up.obj i)).app (Opposite.op ⦋0⦌)
      (nerveVertex (Over.mk (𝟙 (((AsSmall.up : I ⥤ AsSmall.{v} I).obj i))))) =
        ULift.up ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i))))
```

### [BousfieldKanUniversePoints.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/BousfieldKanUniversePoints.lean)

OE02、43原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanUniversePoints`。

概要：同じBK重みの宇宙変更同型は、元の指定BK錐の同じ零単体を保つ。
方針：普遍評価による宇宙比較の点の式に、指定downによる重みの前合成則を合わせる。
規約：IS-W2 R02〜R03の既存の移送則。元の錐の自然変換を保持する。
使われ方：BE Totの指定BK点を全Hom∞比較の宇宙へ運ぶ。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.bousfieldKanUniverseCone`。

```lean
universe u v
variable (I : Type u) [SmallCategory I] {H : I ⥤ SSet.{u}}

def bousfieldKanUniverseCone (s : bousfieldKanWeight I ⟶ H) :
    bousfieldKanWeight (AsSmall.{v} I) ⟶ (weightedDiagramUniverse.{u,v} I).obj H
```

### [ConeInvariance.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ConeInvariance.lean)

OE02、45原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConeInvariance`。

# Kan 値図式の射影重みの錐のホモトピー不変性

概要：Hovey §5.4 の射影 cofibrant 重みの錐は各値の anodyne 局所化同値を保つ。
方針：境界の右類の保存を Kan 値図式の自然な Brown 分解へ渡す。
規約：単体集合とその図式圏の完全なモデル構造は仮定しない。
使われ方：始域 frame と右 frame の比較を重み付き錐へ移す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.coneSpace_map_isIso_of_pointwiseKan`。

```lean
universe u v w
variable (K : Type u) [SmallCategory K] (W : K ⥤ SSet.{u})
  (hW : (boundaries K).rlp.llp (initial.to W))

lemma coneSpace_map_isIso_of_pointwiseKan {F G : K ⥤ SSet.{u}} (f : F ⟶ G)
    (hF : ∀ k, SSet.KanComplex (F.obj k)) (hG : ∀ k, SSet.KanComplex (G.obj k))
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k)))
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map ((coneSpace K W).map f))
```

### [ConeLifting.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ConeLifting.lean)

OE02、120原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConeLifting`。

# 射影 cofibrant 重みの錐空間の持ち上げ

概要：Hovey §5 の重み付き錐は各頂点の境界の右類と Kan fibration を保つ。
方針：二変数随伴で持ち上げを移し、重みの射影 cofibrancy を使う。
規約：単体集合の完全なモデル構造は仮定しない。
使われ方：一般 homotopy 極限の写像空間の不変性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.coneSpace_map_boundary_rlp`。

```lean
universe u v w
variable (K : Type u) [SmallCategory K] (W : K ⥤ SSet.{u})
  (hW : (boundaries K).rlp.llp (initial.to W))

lemma coneSpace_map_boundary_rlp {F G : K ⥤ SSet.{u}} (p : F ⟶ G)
    (hp : ∀ k, SSet.modelCategoryQuillen.I.rlp (p.app k)) :
    SSet.modelCategoryQuillen.I.rlp ((coneSpace K W).map p)
```

### [ConePoints.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ConePoints.lean)

OE02、65原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConePoints`。

# 実際の重み付き錐の零単体とその類

概要：Hovey §5.4 の重み付き錐の族から同じ錐空間の零単体を構成する。
方針：零単体をテンソルした重みの同型と錐の随伴、Yoneda 同型を合成する。
規約：元の重みと元の族を保持する。
使われ方：通常の錐の類と両 frame の錐比較の正規化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.conePoint`。

```lean
universe u
variable (K : Type u) [SmallCategory K] (W : K ⥤ SSet.{u})

def conePoint {F : K ⥤ SSet.{u}} (s : W ⟶ F) :
    ((WeightedCones.coneSpace K W).obj F).obj (Opposite.op (SimplexCategory.mk 0))
```

### [ConeReindex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ConeReindex.lean)

OE02、55原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConeReindex`。

# 添字圏の同値による重み付き錐空間の移送

概要：Hovey §5.4 の重み付き錐の同じ空間を添字の同値で比較する。
方針：各値のテンソルと前合成の可換性から右随伴の一意性を使う。
規約：モデル構造は不要で、元の図式と重みをともに同じ同値で移す。
使われ方：E 代数の右 frame の二重反対圏表示と元の始域 frame の錐の照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.coneSpaceReindexAuxIso`。

```lean
universe u
variable {J K : Type u} [SmallCategory J] [SmallCategory K] (e : J ≌ K)
  (W : K ⥤ SSet.{u})

def coneSpaceReindexAuxIso :
    coneSpace J (e.functor ⋙ W) ≅
      (e.symm.congrLeft (E := SSet.{u})).inverse ⋙ coneSpace K W
```

### [ConeReindexPoints.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ConeReindexPoints.lean)

OE02、101原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConeReindexPoints`。

# 添字移送による元の錐の零単体の保存

概要：Hovey §5.4 の錐の添字移送で元の族とその連結成分を照合する。
方針：右随伴の一意性の単位保存から随伴の Hom 対応を計算する。
規約：元の比較同型を保持し、モデル構造を仮定しない。
使われ方：右 frame の錐と元の通常錐の比較の正規化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.coneSpaceReindexIso_homEquiv`。

```lean
universe u
variable {J K : Type u} [SmallCategory J] [SmallCategory K] (e : J ≌ K)
  (W : K ⥤ SSet.{u})

lemma coneSpaceReindexIso_homEquiv (X : SSet.{u}) (F : K ⥤ SSet.{u})
    (t : (tensorDiagram K W).obj X ⟶ F) :
    (WeightedCones.adjunction J (e.functor ⋙ W)).homEquiv X _
        (whiskerLeft e.functor t) ≫ (coneSpaceReindexIso e W).hom.app F =
      (WeightedCones.adjunction K W).homEquiv X F t
```

### [ConstantComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ConstantComparison.lean)

OE02、82原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConstantComparison`。

# 一点重みの各値の実現から元の定値図式への比較

概要：Hovey §5.4 の射影一点重みと frame から定値図式への弱同値を構成する。
方針：各値の一点比較を実現し、零次の augmentation へ続ける。
規約：比較は図式の射であり、頂点ごとの逆の選択には依存しない。
使われ方：一般 homotopy 極限の右導来普遍性の始域の置換。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.liftedZeroPointIso`。

```lean
universe u v

def liftedZeroPointIso : uliftYoneda.{u, 0, 0}.obj (SimplexCategory.mk 0) ≅ (⊤_ SSet.{u})
```

### [ConstantNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ConstantNaturality.lean)

OE02、105原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConstantNaturality`。

# 定値図式への実現比較の frame に関する自然性

概要：Hovey §5.4 の定値図式への比較を frame の族で自然に構成する。
方針：実際の Yoneda 拡張の単位と重みの一点比較の自然性を使う。
規約：実現の係数射は既存の Kan 拡張の関手的な射。
使われ方：定値図式の関手的な cofibrant 置換。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.realizationPointIso_naturality`。

```lean
universe u v
variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  {B B' : SimplexCategory ⥤ C}

lemma realizationPointIso_naturality (a : B ⟶ B') :
    (Realization.family.map a).app (⊤_ SSet.{u}) ≫ (realizationPointIso B').hom =
      (realizationPointIso B).hom ≫ a.app (SimplexCategory.mk 0)
```

### [DoubleOpposite.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/DoubleOpposite.lean)

OE02、49原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.DoubleOpposite`。

概要：右 frame に入力する重みの二重反対化を共有する。
方針：BarrattEccles と ComplexLimits の一致する宣言を、そのまま一箇所へ移す。
規約：小さい添字圏だけに依存し、値圏やモデル構造を引数に加えない。
使われ方：E 代数および複体の重み付き右 frame の end。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.doubleOpWeights`。

```lean
universe u
variable (K : Type u) [SmallCategory K]

abbrev doubleOpWeights : (K ⥤ SSet.{u}) ⥤ (Kᵒᵖᵒᵖ ⥤ SSet.{u})
```

### [FrameConeClasses.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/FrameConeClasses.lean)

OE02、73原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.FrameConeClasses`。

# 実現の普通の射が与える錐の類の正規化

概要：Hovey §5.4 の重み付き実現の随伴から作った錐の類は元の局所化射。
方針：同じ標準 frame の零次同型と二つの随伴の自然性を使う。
規約：実現対象と元の射をそのまま保持する。
使われ方：通常の錐から具体的な計算対象への射のクラス計算。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.tensorFrameHomIso_point`。

```lean
universe u v w t
variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u}) (B : K ⥤ SimplexCategory ⥤ C)

lemma tensorFrameHomIso_point {Y : C}
    (f : (FrameWeightRealization.functor K B).obj W ⟶ Y) :
    ((((tensorFrameHomIso K W B).app Y).hom).app (Opposite.op (SimplexCategory.mk 0)))
        ((tensorFrameZeroIso K W B).hom ≫ f) =
      conePoint Kᵒᵖ W ((FrameWeightRealization.adjunction K B).homEquiv W Y f)
```

### [FrameCones.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/FrameCones.lean)

OE02、146原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.FrameCones`。

# Frame の図式の重み付き Kan 錐

概要：Hovey §5 の frame Hom の重み付き錐に Kan 性と比較の不変性を与える。
方針：各頂点の frame の持ち上げを射影 cofibrant 重みで束ねる。
規約：重みは実際の射影境界の左類で、単体集合モデルは仮定しない。
使われ方：E 代数の重み付き右 frame の end の Hom 比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.frameCone`。

```lean
universe u v w t
variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u}) (hW : (boundaries Kᵒᵖ).rlp.llp (initial.to W))

abbrev frameCone (B : K ⥤ SimplexCategory ⥤ C) : C ⥤ SSet.{u}
```

### [FrameLifting.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/FrameLifting.lean)

OE02、53原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.FrameLifting`。

# 射影重みに対する frame の重み付き実現の持ち上げ

概要：Hovey §5.4 の重み付き実現が射影境界の左類を cofibration へ移すことを証明する。
方針：実際の随伴と各成分の境界持ち上げを使う。
規約：単体集合の完全なモデル構造は仮定しない。
使われ方：E 代数の重み付き右 frame の end の fibration 判定。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.realization_map_cofibration`。

```lean
universe u v
variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (B : K ⥤ SimplexCategory ⥤ C)
  (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))

lemma realization_map_cofibration {W W' : Kᵒᵖ ⥤ SSet.{u}} (i : W ⟶ W')
    (hi : (boundaries Kᵒᵖ).rlp.llp i) :
    cofibrations C ((FrameWeightRealization.functor K B).map i)
```

### [Generators.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/Generators.lean)

OE02、78原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Generators`。

# Homotopy 極限の重みの射影境界生成族

概要：Hovey §5 の小図式の単体的重みに対し、各頂点の自由境界生成族を構成する。
方針：境界の有限表示性と自由・評価随伴から小対象性を得る。
規約：単体集合の完全なモデル構造を仮定しない。
使われ方：定値一点重みの射影 cofibrant 置換。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.free`。

```lean
universe u
variable (K : Type u) [SmallCategory K]

abbrev free (k : K) : SSet.{u} ⥤ K ⥤ SSet.{u}
```

### [KanConeClasses.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/KanConeClasses.lean)

OE02、76原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.KanConeClasses`。

# 共通図式で一致する錐の類と比較同型

概要：Hovey §5.4 の両側の錐比較は共通図式で一致する元の錐の類を保つ。
方針：同じ Kan 置換単位の自然性と比較同型の可換三角形を使う。
規約：元の族を保持し、共通図式の Kan 性は要求しない。
使われ方：通常の錐の始域 frame と右 frame のクラス照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.kanDiagramUnit_naturality`。

```lean
universe u
variable (K : Type u) [SmallCategory K]

lemma kanDiagramUnit_naturality {F G : K ⥤ SSet.{u}} (f : F ⟶ G) :
    f ≫ kanDiagramUnit K G = kanDiagramUnit K F ≫ kanDiagramMap K f
```

### [KanConeComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/KanConeComparison.lean)

OE02、125原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.KanConeComparison`。

# 共通図式を介した Kan 錐の比較と自然性

概要：Hovey §5.4 の共通分解を、Kan 図式の重み付き錐の自然な比較へ移す。
方針：共通図式への二つの射を Kan 置換し、同型の積で比較する。
規約：共通図式に Kan 性を要求せず、元の錐を保持する。
使われ方：両 frame の錐の比較の自然性と元の比較射の追跡。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.coneComparisonArrow`。

```lean
universe u v w
variable (K : Type u) [SmallCategory K] (W : K ⥤ SSet.{u})
  (hW : (boundaries K).rlp.llp (initial.to W))
  {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

def coneComparisonArrow {F H : K ⥤ SSet.{u}} (f : F ⟶ H) :
    L.obj ((coneSpace K W).obj F) ⟶ L.obj ((coneSpace K W).obj (kanDiagram K H))
```

### [KanDiagramBrown.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/KanDiagramBrown.lean)

OE02、128原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.KanDiagramBrown`。

# Kan 値図式に対するモデル構造を使わない Brown 分解

概要：Hovey §1.1・§5 の積による Brown 分解を Kan 値図式に自然に構成する。
方針：ホーンの関手的小対象分解と Kan fibration の局所化同値の境界持ち上げを使う。
規約：単体集合にもその図式圏にも完全なモデル構造を置かない。
使われ方：射影 cofibrant 重みの錐の Kan 図式の不変性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.map_isIso_of_pointwiseKan`。

```lean
universe u v w
variable (K : Type u) [SmallCategory K]

lemma map_isIso_of_pointwiseKan {D : Type v} [Category.{w} D] (T : (K ⥤ SSet.{u}) ⥤ D)
    (hT : ∀ {F G : K ⥤ SSet.{u}} (p : F ⟶ G),
      (∀ k, SSet.modelCategoryQuillen.I.rlp (p.app k)) → IsIso (T.map p))
    {F G : K ⥤ SSet.{u}} (f : F ⟶ G)
    (hF : ∀ k, SSet.KanComplex (F.obj k)) (hG : ∀ k, SSet.KanComplex (G.obj k))
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k))) : IsIso (T.map f)
```

### [KanDiagramReplacement.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/KanDiagramReplacement.lean)

OE02、105原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.KanDiagramReplacement`。

# Kan 置換を介した重み付き錐の比較

概要：Hovey §5 の frame 比較の共通対象を関手的に Kan 置換する。
方針：実際のホーン小対象置換の単位の自然性と錐の Kan 図式不変性を使う。
規約：元の Kan 錐空間は変更せず、置換は比較の中間図式に使う。
使われ方：混合 Hom が Kan であるという追加仮定なしに両 frame の錐を比較する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.kanReplacement_map_isIso`。

```lean
universe u v w

lemma kanReplacement_map_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (AnodyneKanReplacement.functor.map f))
```

### [NativeWeightedPointMap.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/NativeWeightedPointMap.lean)

OE02、28原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.NativeWeightedPointMap`。

概要：元の指定重み付き錐の点を、同じ係数図式の射の後合成で追跡する。
方針：既存の転置の後合成則を標準零単体で評価する。
規約：IS-W2 R02〜R03の自然性の法則。元の自然変換の実際の後合成。
使われ方：右frameの係数同型による指定BK普遍点の輸送。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.nativeWeightedPoint_map`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

theorem nativeWeightedPoint_map {W F G : I ⥤ SSet.{u}} (s : W ⟶ F) (f : F ⟶ G) :
    ((weightedSectionsMap W f).app (Opposite.op ⦋0⦌)) (nativeWeightedPoint I s) =
      nativeWeightedPoint I (s ≫ f)
```

### [NativeWeightedPointRestriction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/NativeWeightedPointRestriction.lean)

OE02、46原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.NativeWeightedPointRestriction`。

概要：元の指定された重み付き錐の点を、同じ重みの射の前合成で追跡する。
方針：普遍評価の転置の前合成則を零単体に適用する。
規約：IS-W2 R02〜R03の同じ点の照合。π₀だけの等式ではない。
使われ方：元の普遍frame錐から同じBK切断の点を作る。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.nativeWeightedPoint`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

def nativeWeightedPoint {W H : I ⥤ SSet.{u}} (s : W ⟶ H) :
    (weightedSections W H) _⦋0⦌
```

### [NativeWeightedSectionPoints.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/NativeWeightedSectionPoints.lean)

OE02、67原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.NativeWeightedSectionPoints`。

概要：元の重み付き錐空間とnative切断の同型が、同じ指定錐の零単体を保つことを示す。
方針：右随伴の一意性のcounit則を同じHom同値へ戻し、標準零単体を評価する。
規約：IS-W2 R02〜R03の既存の比較の点での法則。新しい錐の頂点は選ばない。
使われ方：元の普遍錐の点を同じBK重み制限へ接続する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.coneSpaceNativeSectionsIso_homEquiv`。

```lean
universe u
variable (I : Type u) [SmallCategory I] (W : I ⥤ SSet.{u})

theorem coneSpaceNativeSectionsIso_homEquiv (X : SSet.{u}) (H : I ⥤ SSet.{u})
    (f : (WeightedCones.tensorDiagram I W).obj X ⟶ H) :
    (WeightedCones.adjunction I W).homEquiv X H f ≫ (coneSpaceNativeSectionsIso I W).hom.app H =
      weightedSectionsLift ((coneSpaceParameterIso I W).inv.app X ≫ f)
```

### [NativeWeightedSections.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/NativeWeightedSections.lean)

OE02、52原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.NativeWeightedSections`。

概要：既存の重み付き錐の右随伴を、元のnativeな重み付き切断のendと同定する。
方針：同じ二つのテンソルの順序をbraidingで合わせ、右随伴の一意性を使う。
規約：IS-W2 R03a.1の既存構成の照合法則。重みの頂点や脚は変更しない。
使われ方：射影cofibrancyから元の切断空間のKan性を得る。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.coneSpaceParameterIso`。

```lean
universe u
variable (I : Type u) [SmallCategory I] (W : I ⥤ SSet.{u})

def coneSpaceParameterIso : WeightedCones.tensorDiagram I W ≅ weightedParameterFunctor W
```

### [PointReplacement.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/PointReplacement.lean)

OE02、67原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointReplacement`。

# 定値一点重みの実際の射影 cofibrant 置換

概要：Hovey §5 の homotopy 極限に使う重みを境界の小対象分解から構成する。
方針：初期図式から定値一点への射を自由境界の左類と右類に分解する。
規約：任意の小圏、単体集合の完全なモデル構造を仮定しない。
使われ方：E 代数の右 frame の重み付き end に代入する標準重み。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.point`。

```lean
universe u
variable (K : Type u) [SmallCategory K]

def point : K ⥤ SSet.{u}
```

### [PointwiseConePoints.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/PointwiseConePoints.lean)

OE02、50原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwiseConePoints`。

# 各値の実現随伴から作った錐の零単体

概要：Hovey §5.4 の図式 frame の零次の Hom と元の錐の零単体を照合する。
方針：同じ零単体テンソル同型を二つの随伴の自然性で追跡する。
規約：元の図式・重み・係数 frame を保持する。
使われ方：通常の錐の始域 frame の類の正規化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorFrameHomIso_point`。

```lean
universe u v
variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  (W : K ⥤ SSet.{u}) (B : SimplexCategory ⥤ C)

lemma pointwiseTensorFrameHomIso_point {F : K ⥤ C}
    (f : (pointwiseRealization K B).obj W ⟶ F) :
    ((((pointwiseTensorFrameHomIso K W B).app F).hom).app (Opposite.op (SimplexCategory.mk 0)))
        ((pointwiseTensorFrameZeroIso K W B).hom ≫ f) =
      conePoint K W ((pointwiseRealizationAdjunction K B).homEquiv W F f)
```

### [PointwisePiZero.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/PointwisePiZero.lean)

OE02、98原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwisePiZero`。

# 始域 frame の重み付き錐と図式の局所化 Hom

概要：Hovey §5.4 の重み付き錐の連結成分で図式の導来 Hom を計算する。
方針：実際の図式 frame の Hom 同型・π₀ 比較・零次同型を合成する。
規約：元の置換図式を始域とし、単体集合のモデル構造は仮定しない。
使われ方：定値図式を始域とする一般 homotopy 極限の Hom 比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv`。

```lean
universe u v w t
variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  [ModelCategory C] [ModelCategory (K ⥤ C)]
  (W : K ⥤ SSet.{u}) (B : SimplexCategory ⥤ C)
  (hW : (boundaries K).rlp.llp (initial.to W))
  (hB : reedyLeft simplex (cofibrations C) (initial.to B))
  (htriv : ∀ {F G : K ⥤ C} (p : F ⟶ G), trivialFibrations (K ⥤ C) p →
    ∀ k, trivialFibrations C (p.app k))
  (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
  (hfib : ∀ {F G : K ⥤ C} (p : F ⟶ G), Fibration p → ∀ k, Fibration (p.app k))
  {D : Type w} [Category.{t} D] (Q : (K ⥤ C) ⥤ D)
  [Q.IsLocalization (weakEquivalences (K ⥤ C))]

def pointwiseWeightedHomPiZeroEquiv (F : K ⥤ C) [IsFibrant F] :
    SSet.π₀ ((pointwiseWeightedHom K W B).obj F) ≃
      (Q.obj ((pointwiseRealization K B).obj W) ⟶ Q.obj F)
```

### [PointwiseRealization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/PointwiseRealization.lean)

OE02、96原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwiseRealization`。

# 重みの各値を固定した frame で実現する関手

概要：Hovey §5.4 の frame の実現を小図式の各値に適用する。
方針：通常の随伴を関手圏へ移し、自由境界の右類を評価で判定する。
規約：単体集合のモデル構造や値圏の局所表示可能性は仮定しない。
使われ方：定値 E 代数図式の具体的な射影 cofibrant 置換。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.pointwiseRealization`。

```lean
universe u v
variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  (B : SimplexCategory ⥤ C)

abbrev pointwiseRealization : (K ⥤ SSet.{u}) ⥤ K ⥤ C
```

### [PointwiseTensorFrame.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/PointwiseTensorFrame.lean)

OE02、150原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwiseTensorFrame`。

# 射影重みを各値で実現した図式の余単体的 frame

概要：Hovey §5.4 の定値図式置換を図式圏の実際の frame へ拡張する。
方針：重みに標準単体をテンソルし、各値の実現と錐の随伴を合成する。
規約：図式の右類の評価での判定だけを使い、単体集合モデルは不要。
使われ方：定値図式からの局所化 Hom と始域 frame の重み付き錐の比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorRealization`。

```lean
universe u v
variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  (W : K ⥤ SSet.{u}) (B : SimplexCategory ⥤ C)

abbrev pointwiseTensorRealization : SSet.{u} ⥤ K ⥤ C
```

### [PointwiseTensorSource.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/PointwiseTensorSource.lean)

OE02、91原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwiseTensorSource`。

# 各値で実現した図式 frame の Hom 同型の係数自然性

概要：Hovey §5.4 の図式 frame Hom と重み付き始域 Hom の同型は係数に自然。
方針：同じ各値の実現随伴の自然性を重みのテンソル随伴と合成する。
規約：実現の射は元の Yoneda 拡張族の同じ射。
使われ方：元の定値図式からの局所化 Hom の始域自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.pointwiseRealization_homEquiv_source`。

```lean
universe u v
variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  {B B' : SimplexCategory ⥤ C} (a : B ⟶ B')

lemma pointwiseRealization_homEquiv_source (X : K ⥤ SSet.{u}) (F : K ⥤ C)
    (f : (pointwiseRealization K B').obj X ⟶ F) :
    (pointwiseRealizationAdjunction K B).homEquiv X F
        (((Functor.whiskeringRight K SSet.{u} C).map (Realization.family.map a)).app X ≫ f) =
      (pointwiseRealizationAdjunction K B').homEquiv X F f ≫
        ((Functor.whiskeringRight K C SSet.{u}).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a)).app F
```

### [ProjectiveBoundaryContraction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ProjectiveBoundaryContraction.lean)

OE02、78原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveBoundaryContraction`。

概要：各値で境界右類を持つ重みの射の同じ切断と、全自然な区間収縮を作る。
方針：元の射影cofibrancyで切断を取り、同じ基底を保つ境界を区間へ持ち上げる。
規約：IS-W2 R03a.1の証明分割。元の重みの全射を保持する。
使われ方：同じ指定重み比較の右射の制限の実際のホモトピー逆。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.weightIntervalProjection`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

def weightIntervalProjection (V : I ⥤ SSet.{u}) :
    V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ V
```

### [ProjectiveHornCorner.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ProjectiveHornCorner.lean)

OE02、50原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveHornCorner`。

概要：射影anodyneな重みの射とパラメーター単射の相対テンソルは、点ごとのfibrationを持ち上げる。
方針：同じ相対テンソルをpointwiseな二変数随伴へ渡し、各値の内部Homのfibration性を使う。
規約：IS-W2 R03a.1の証明分割。図式モデル構造は使わない。
使われ方：Kan係数への重み制限の全境界の持ち上げ。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.projectiveHorn_corner_lifting`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

theorem projectiveHorn_corner_lifting {V W F G : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : (horns I).rlp.llp j) {A B : SSet.{u}} (f : A ⟶ B) [Mono f]
    (p : F ⟶ G) (hp : ∀ i, Fibration (p.app i)) :
    HasLiftingProperty (weightedCorner j f).ι p
```

### [ProjectiveHornFactorization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ProjectiveHornFactorization.lean)

OE02、55原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveHornFactorization`。

概要：同じ重みの射を自由ホーンで分解し、元のcofibrancyと各値の性質を記録する。
方針：既存の小対象分解を選び、自由評価随伴でその二つの持ち上げ条件を読む。
規約：IS-W2 R03a.1の証明分割。重みの射と分解の等式を保つ。
使われ方：重みの成分ごとの弱同値を、制限の二種類のホモトピー同値へ分ける。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.projectiveHorn_cofibration`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

theorem projectiveHorn_cofibration {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : (horns I).rlp.llp j) : (boundaries I).rlp.llp j
```

### [ProjectiveHornGenerators.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ProjectiveHornGenerators.lean)

OE02、36原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveHornGenerators`。

概要：同じ単体集合図式圏の自由ホーン生成族を用意する。
方針：既存の自由評価随伴でホーンの小対象性と点ごとの右類を移す。
規約：IS-W2 R03a.1の証明分割。SSetモデル構造を仮定しない。
使われ方：同じ重み比較の射影anodyne・点ごとのfibration分解。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.horns`。

```lean
universe u
variable (K : Type u) [SmallCategory K]

abbrev horns : MorphismProperty (K ⥤ SSet.{u})
```

### [ProjectiveHornValues.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ProjectiveHornValues.lean)

OE02、62原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveHornValues`。

概要：自由ホーンで生成された左射は、各値で元のanodyneな射。
方針：自由射の各値は同じホーンの余積で、余積・押し出し・逐次合成・レトラクトで移す。
規約：IS-W2 R03a.1の証明分割。モデル構造や弱同値のクラスを入力しない。
使われ方：元の比較射の自由ホーン分解の成分ごとの性質。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.free_horn_anodyne`。

```lean
universe u
variable (K : Type u) [SmallCategory K]

theorem free_horn_anodyne (k l : K) {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.modelCategoryQuillen.J f) : SSet.anodyneExtensions (((free K k).map f).app l)
```

### [ProjectiveHornWeakFactorization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ProjectiveHornWeakFactorization.lean)

OE02、58原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveHornWeakFactorization`。

概要：各値がKanな標的への重みの弱同値の自由ホーン分解は、各値で境界の右類を持つ。
方針：左射のanodyne性、弱同値の二対三則、Kan Whiteheadと既存の相対充填を使う。
規約：IS-W2 R03a.1の証明分割。一般の非Kan標的の場合をこの補題で代用しない。
使われ方：重みのホーン置換後に元の右射の切断とホモトピーを得る。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.projectiveHornFactorization_i_weak`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

theorem projectiveHornFactorization_i_weak {V W : I ⥤ SSet.{u}} (j : V ⟶ W) (i : I) :
    IsWeakHomotopyEquivalence ((projectiveHornFactorization I j).i.app i)
```

### [ProjectiveWeightComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ProjectiveWeightComparison.lean)

OE02、74原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveWeightComparison`。

概要：射影cofibrantな元の重み間の成分ごとの弱同値は、Kan係数への制限でホモトピー同値。
方針：まずKan標的への自由ホーン分解を二つの既知の制限へ分け、一般標的は同じホーン置換で移す。
規約：IS-W2 R03a.1の型つきの中間定理。SSetモデル構造は仮定しない。
使われ方：元のBK重みと指定された一点重みの同じ一つの比較射。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.projectiveHornReplacement_kan`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

theorem projectiveHornReplacement_kan (W : I ⥤ SSet.{u}) (i : I) :
    SSet.KanComplex ((projectiveHornFactorization I (terminal.from W)).Z.obj i)
```

### [ProjectiveWeightRestriction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ProjectiveWeightRestriction.lean)

OE02、89原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveWeightRestriction`。

概要：元の重み制限の全境界の持ち上げを、同じ相対テンソルの延長へ転置する。
方針：既存のweightedCornerの二射の押し出しと元のcurry・uncurryを使う。
規約：IS-W2 R03a.1の既存の延長法則の証明分割。
使われ方：各値がKanの係数に対する射影anodyneな重み制限。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.weightedSectionsPre_trivialKanFibration_of_corner_extensions`。

```lean
universe u
variable {I : Type u} [SmallCategory I]

theorem weightedSectionsPre_trivialKanFibration_of_corner_extensions
    {W W' H : I ⥤ SSet.{u}} (j : W ⟶ W')
    (hcorner : ∀ n, ∀ a : (weightedCorner j (boundary n).ι).pt ⟶ H,
      ∃ b : W' ⊗ (Functor.const I).obj (Δ[n] : SSet.{u}) ⟶ H,
        (weightedCorner j (boundary n).ι).ι ≫ b = a) :
    TrivialKanFibration (weightedSectionsPre j H)
```

### [ProjectiveWeightTensorLifting.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/ProjectiveWeightTensorLifting.lean)

OE02、48原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveWeightTensorLifting`。

概要：射影cofibrant重みと単射パラメーターのテンソルは、点ごとの境界右類を持ち上げる。
方針：同じ二変数随伴に初期重みを入れ、単射のpushout-productの法則を移す。
規約：IS-W2 R03a.1の切断と区間収縮の証明分割。
使われ方：同じ元の重み全体の境界から区間への持ち上げ。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.projectiveWeight_tensor_lifting`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

theorem projectiveWeight_tensor_lifting (W : I ⥤ SSet.{u})
    (hW : (boundaries I).rlp.llp (initial.to W))
    {A B : SSet.{u}} (f : A ⟶ B) [Mono f] {F G : I ⥤ SSet.{u}} (p : F ⟶ G)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i)) :
    HasLiftingProperty ((weightedParameterFunctor W).map f) p
```

### [RealizationAugmentation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/RealizationAugmentation.lean)

OE02、73原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.RealizationAugmentation`。

# 実現の一点比較と元の frame augmentation の照合

概要：Hovey §5 の一点への実現比較は同じ augmentation の全単体を回収する。
方針：実際の随伴の単体の式、零単体の終対象性、Kan 拡張単位の自然性を使う。
規約：元の零次同型と augmentation を選び直さない。
使われ方：通常の錐の始域 frame の族の正規化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.realizationAugmentation_homEquiv`。

```lean
universe u v
variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  (B : SimplexCategory ⥤ C) {Y : C}

lemma realizationAugmentation_homEquiv (a : B ⟶ (Functor.const SimplexCategory).obj Y)
    (X : SSet.{u}) (t : X ⟶ ⊤_ SSet.{u}) (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    (((Realization.adjunction B).homEquiv X Y
      ((Realization.functor B).map t ≫ (realizationPointIso B).hom ≫
        a.app (SimplexCategory.mk 0))).app n) x = a.app n.unop
```

### [RealizationCoefficientMap.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/RealizationCoefficientMap.lean)

OE02、133原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.RealizationCoefficientMap`。

# 重み付き実現の元の係数射と Yoneda 拡張の係数射の一致

概要：Hovey §5.4 の実際の重み付き実現の射を同じ Kan 拡張の射で計算する。
方針：実現随伴の各単体の式から Hom の係数自然性を計算する。
規約：既存の mate による射を保持し、モデル構造を仮定しない。
使われ方：忘却後の同じ計算対象と重み付き end の比較の自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.realizationHomEquiv_app`。

```lean
universe u v
variable (K : Type u) [SmallCategory K] {C : Type v} [Category.{u} C]
  [HasColimitsOfSize.{u, u} C] (A : K ⥤ SimplexCategory ⥤ C)

lemma realizationHomEquiv_app (W : Kᵒᵖ ⥤ SSet.{u}) (Y : C)
    (f : (FrameWeightRealization.functor K A).obj W ⟶ Y)
    (k : Kᵒᵖ) (n : SimplexCategoryᵒᵖ) (x : (W.obj k).obj n) :
    ((((FrameWeightRealization.adjunction K A).homEquiv W Y f).app k).app n) x =
      (uliftYoneda.{u, u, u}.leftKanExtensionUnit (FrameWeightRealization.source K A)).app
        (k.unop, n.unop) ≫
      (FrameWeightRealization.presheafRealization K A).map (uliftYonedaEquiv.symm x) ≫ f
```

### [RealizationInvariance.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/RealizationInvariance.lean)

OE02、67原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.RealizationInvariance`。

# 射影 cofibrant 重みによる frame の実現の弱同値不変性

概要：Hovey §5.4 の重み付き実現は係数 frame の頂点ごとの弱同値を保つ。
方針：錐の π₀ の不変性を元の実現対象からの Hom の全単射へ移す。
規約：図式の射影 cofibrancy や単体集合のモデル構造は要求しない。
使われ方：実際の E 代数の一般 homotopy 極限の擬同型不変性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.realization_map_frame_weakEquivalence`。

```lean
universe u v
variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u}) (hW : (boundaries Kᵒᵖ).rlp.llp (initial.to W))

lemma realization_map_frame_weakEquivalence
    (fact : MorphismProperty.FunctorialFactorizationData
      (cofibrations C) (trivialFibrations C))
    {B B' : K ⥤ SimplexCategory ⥤ C} (a : B ⟶ B')
    (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))
    (hB' : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B'.obj k)))
    (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
      weakEquivalences C ((B.obj k).map f))
    (hconst' : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
      weakEquivalences C ((B'.obj k).map f))
    (ha : ∀ k n, weakEquivalences C ((a.app k).app n)) :
    weakEquivalences C ((FrameWeightRealization.map K a).app W)
```

### [Reindex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/Reindex.lean)

OE02、41原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Reindex`。

# 添字圏の同値に沿う重みの射影 cofibration

概要：Hovey §5 の射影境界の左類は添字圏の同値による前合成で保たれる。
方針：関手圏の同値の随伴で持ち上げを移し、右類を各頂点で判定する。
規約：通常の添字圏の同値を使い、単体集合のモデル構造は不要。
使われ方：二重反対圏へ移した cofibrant 重みを元の小圏の end に入力する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.reindex_cofibration`。

```lean
universe u
variable {J K : Type u} [SmallCategory J] [SmallCategory K]

lemma reindex_cofibration (e : J ≌ K) {W W' : K ⥤ SSet.{u}} (i : W ⟶ W')
    (hi : (boundaries K).rlp.llp i) :
    (boundaries J).rlp.llp
      (((Functor.whiskeringLeft J K SSet.{u}).obj e.functor).map i)
```

### [TensorConeUnitPoint.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/TensorConeUnitPoint.lean)

OE02、9原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorConeUnitPoint`。

概要：tensor frameの標準点の既存の正規化補題を再公開する互換入口。
方針：FrameConeClassesの既存tensorFrameHomIso_pointをそのまま使う。
規約：このファイルでは同名の宣言を追加しない。標的Yは既存補題の暗黙引数。
使われ方：IS-W2で既に記録したモジュール経路を維持する。

名前つき公開宣言のないimport／補助用モジュール。native所有元表で全宣言の有無を照合する。

### [TensorPiZero.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/TensorPiZero.lean)

OE02、100原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorPiZero`。

# 重み付き錐の連結成分と実現対象からの局所化 Hom

概要：Hovey §5.4 の重み付き錐の π₀ を元の実現対象からの Hom と同定する。
方針：標準 frame の零次を単位のテンソルと同定し、frame の π₀ 比較を移す。
規約：同じ重み・実現対象・局所化を保持し、単体集合モデルは仮定しない。
使われ方：一般 homotopy 極限の擬同型不変性の検出。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.unitTensorWeightIso`。

```lean
universe u v w t
variable (K : Type u) [SmallCategory K]

def unitTensorWeightIso (W : K ⥤ SSet.{u}) :
    (WeightedCones.tensorDiagram K W).obj (𝟙_ SSet.{u}) ≅ W
```

### [TensorPiZeroNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/TensorPiZeroNaturality.lean)

OE02、114原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorPiZeroNaturality`。

# 係数 frame の射に関する重み付き錐の π₀ 比較の自然性

概要：Hovey §5.4 の錐の連結成分の比較は実際の重み付き実現の前合成と両立する。
方針：二つの随伴の Hom 自然性と零次同型の自然性を使う。
規約：実現の射は既存の随伴の mate そのものを使う。
使われ方：係数の弱同値から一般 homotopy 極限の擬同型を検出する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.tensorRealization_homEquiv_frame_naturality`。

```lean
universe u v w t
variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u})

lemma tensorRealization_homEquiv_frame_naturality
    {B B' : K ⥤ SimplexCategory ⥤ C} (a : B ⟶ B') (X : SSet.{u}) (Y : C)
    (f : (tensorRealization K W B').obj X ⟶ Y) :
    (tensorRealizationAdjunction K W B).homEquiv X Y
        ((FrameWeightRealization.map K a).app ((WeightedCones.tensorDiagram Kᵒᵖ W).obj X) ≫ f) =
      (tensorRealizationAdjunction K W B').homEquiv X Y f ≫
        (WeightedCones.coneSpace Kᵒᵖ W).map
          (((FrameWeightRealization.homFamily K).map a.op).app Y)
```

### [TensorPiZeroTarget.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/TensorPiZeroTarget.lean)

OE02、59原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorPiZeroTarget`。

# 重み付き錐の π₀ 比較の終域自然性

概要：Hovey §5.4 の重み付き実現からの局所化 Hom 比較は終域の射に自然。
方針：同じ標準 frame の零単体の代表と Hom 同型の自然性を使う。
規約：モデル構造は元の値圏だけに置く。
使われ方：反対圏の右 frame から元の始域自然性を得る。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.frameConePiZeroLocalizationEquiv_target`。

```lean
universe u v w t
variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u}) (B : K ⥤ SimplexCategory ⥤ C)
  (hW : (boundaries Kᵒᵖ).rlp.llp (initial.to W))
  (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((B.obj k).map f))
  {D : Type w} [Category.{t} D] (Q : C ⥤ D) [Q.IsLocalization (weakEquivalences C)]

lemma frameConePiZeroLocalizationEquiv_target {Y Z : C} [IsFibrant Y] [IsFibrant Z]
    (f : Y ⟶ Z) (z : SSet.π₀ ((frameCone K W B).obj Y)) :
    frameConePiZeroLocalizationEquiv K W B hW hB hconst Q Z
        (SSet.mapπ₀ ((frameCone K W B).map f) z) =
      frameConePiZeroLocalizationEquiv K W B hW hB hconst Q Y z ≫ Q.map f
```

### [TensorRealization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/TensorRealization.lean)

OE02、121原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorRealization`。

# 重み付き frame の標準単体による実現

概要：Hovey §5.4 の重み付き実現に標準単体をテンソルして実際の frame を構成する。
方針：重みのテンソルと実現の随伴を合成し、錐の持ち上げを使う。
規約：単体集合のモデル構造は不要で、同じ重みと係数 frame を保持する。
使われ方：重み付き錐空間と実現対象への局所化 Hom の比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.tensorRealization`。

```lean
universe u v
variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u}) (B : K ⥤ SimplexCategory ⥤ C)

abbrev tensorRealization : SSet.{u} ⥤ C
```

### [Values.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/Values.lean)

OE02、72原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Values`。

# 選んだ homotopy 重みの各値は可縮な Kan 複体

概要：Hovey §5 の射影 cofibrant な一点重みの各値に切断と収縮を構成する。
方針：境界の右類をすべての単射の右類へ移し、切断と区間の持ち上げを使う。
規約：切断と収縮は各頂点ごとのもの。図式全体での自然な切断は主張しない。
使われ方：homotopy 極限の重みの各値を一点と比較する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.comparison_mono_rlp`。

```lean
universe u
variable (K : Type u) [SmallCategory K]

lemma comparison_mono_rlp (k : K) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((comparison K).app k)
```

### [WeightIntervalBoundary.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/WeightIntervalBoundary.lean)

OE02、92原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.WeightIntervalBoundary`。

概要：重みの同じ二つの射から区間境界の全自然な写像を作る。
方針：既存の境界の二成分の余極限と、その自然性を使う。
規約：IS-W2 R03a.1の境界持ち上げによる収縮の証明分割。
使われ方：元の重みの同じ切断を区間で恒等射へ結ぶ。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.weight_boundaryMap_naturality`。

```lean
universe u

theorem weight_boundaryMap_naturality {X Y E F : SSet.{u}} (r : X ⟶ Y) (t : E ⟶ F)
    (a b : X ⟶ E) (c d : Y ⟶ F) (ha : r ≫ c = a ≫ t) (hb : r ≫ d = b ≫ t) :
    (r ▷ (∂Δ[1] : SSet.{u})) ≫ boundaryMap c d = boundaryMap a b ≫ t
```

### [WeightedSourceHomotopy.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/HomotopyWeight/WeightedSourceHomotopy.lean)

OE02、145原行。配置：`SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.WeightedSourceHomotopy`。

概要：重みの同じパラメーター付きホモトピーを、元の切断制限のホモトピーへ移す。
方針：元の普遍評価を、重みと区間の同じパラメーターで前合成して転置する。
規約：IS-W2 R03a.1の重みの前合成の法則。成分ごとの別々の逆射ではない。
使われ方：境界右持ち上げ性を持つ重みの射の切断と収縮の輸送。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.HomotopyWeight.weightedSourceHomotopySection`。

```lean
universe u
variable (I : Type u) [SmallCategory I]

def weightedSourceHomotopySection {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W) (H : I ⥤ SSet.{u}) :
    V ⊗ (Functor.const I).obj (weightedSections W H ⊗ (Δ[1] : SSet.{u})) ⟶ H
```

### [ArrowSpanGrothendieck.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ArrowSpanGrothendieck.lean)

OE03、124原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ArrowSpanGrothendieck`。

# 三本矢の全図式と元の frame の比較の Grothendieck 表示

概要：Low 命題 3.7 の三本矢と元の全単体の比較を同じ全図式で表示する。
方針：両脚の comma と右脚に沿う Grothendieck 構成の明示的な順逆を合成する。
規約：元の frame の単体・両脚・中間射を変更しない。
使われ方：分解側の余終性と右脚の全図式の不変性を組み合わせる比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.ArrowSpan.rightDiagram`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (L R : MorphismProperty C) (X Y : C)

abbrev rightDiagram : R.Under ⊤ Y ⥤ Cat.{v, max u v}
```

### [AsSmallHammockHomFamily.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/AsSmallHammockHomFamily.lean)

OE03、71原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.AsSmallHammockHomFamily`。

概要：元の全標的 hammock Hom 図式を同じ AsSmall 表示に全自然に同定する。
方針：元の宇宙同型の合成保存を全自然性として使い、同じ Ex∞ へ送る。
規約：一つの実自然変換を構成してから coherent な比較にする。
使われ方：right frame 比較の終端と同じ Kan hammock 豊穣 Hom 図式の整合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.asSmallHammockHomFamilyIso`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative] (X : C)

def asSmallHammockHomFamilyIso :
    AsSmall.down ⋙ hammockHomFamily W X ≅
      hammockHomFamily (AsSmallComparison.weak W) (AsSmall.up.obj X)
```

### [AsSmallHammockHomNormalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/AsSmallHammockHomNormalization.lean)

OE03、76原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.AsSmallHammockHomNormalization`。

概要：同じ全図式の宇宙比較の順射・全評価成分・元の射の零単体を照合する。
方針：元の自然変換の実現した辺を保持し、原本の評価と同じ Ex∞ 単位公式を使う。
規約：全同型とは別の点ごとの同値を選ばない。
使われ方：同じ終端図式と Yoneda 比較を合成するときの零単体回収。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.asSmallKanHammockHomFamilyMap_app`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative] (X : C)

lemma asSmallKanHammockHomFamilyMap_app (Y : AsSmall.{max u v} C) :
    (asSmallKanHammockHomFamilyMap W X).app Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (AsSmallComparison.colimitIso W X (AsSmall.down.obj Y)).hom
```

### [BarInitialComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/BarInitialComparison.lean)

OE03、44原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarInitialComparison`。

# 始対象での定値図式から全図式の bar への比較

概要：全遷移が反転される図式に、元の始対象からの比較を与える。
方針：始対象の唯一の射を自然変換へ束ね、bar の成分不変性を適用する。
規約：始対象は明示的に指定する。単体集合モデルは要求しない。
使われ方：恒等右脚から全右脚への Hom 図式の比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.BarRows.fromInitial`。

```lean
universe v uD vD
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})
  {i : D} (hi : IsInitial i)

def fromInitial : (Functor.const D).obj (F.obj i) ⟶ F
```

### [BarPointwiseInvariance.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/BarPointwiseInvariance.lean)

OE03、99原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarPointwiseInvariance`。

# 各成分で反転可能な図式の比較の bar 不変性

## 概要
既存の bar 関手は、anodyne 局所化で各成分が可逆な自然変換を可逆にする。

## 方針（定義・証明）
転置した各行の余積表示に成分ごとの反転性を適用し、対角比較を使う。
二方向の交換の同型で元の bar の射そのものへ戻す。

## 規約と注意
添字・値の宇宙は独立。単体集合のモデル構造や図式の cofibrancy は仮定しない。

## 使われ方
固定右脚の Hom と、全右脚を走る bar の比較に使う。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.BarRows.rowMap`。

```lean
universe v uD vD
variable {D : Type uD} [Category.{vD} D] {F G : D ⥤ SSet.{v}}

abbrev rowMap (η : F ⟶ G) (n : SimplexCategoryᵒᵖ) : row F n ⟶ row G n
```

### [BarRowsCoproduct.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/BarRowsCoproduct.lean)

OE03、85原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRowsCoproduct`。

# bar の転置した行の余積表示

## 概要
元の bar の行を転置すると、基底の射列を添字とする値の余積になる。

## 方針（定義・証明）
要素圏の射列を基底の射列と最初のラベルから復元し、余積の普遍性を示す。

## 規約と注意
添字と値の宇宙を分ける。単体集合のモデル構造は仮定しない。

## 使われ方
固定右脚の Hom の不変性を bar 全体の不変性に移すために使う。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.BarRows.row`。

```lean
universe v uD vD
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

abbrev row (n : SimplexCategoryᵒᵖ) : SSet.{max uD vD v}
```

### [BarValueInclusion.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/BarValueInclusion.lean)

OE03、63原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarValueInclusion`。

# 全遷移が反転される図式の各値から bar への包含

概要：始対象を持つ添字圏では、全遷移が反転される図式の各値の包含も反転される。
方針：始対象の値の定値図式からの比較と、その定値 bar の値の包含を合成する。
規約：元の各値の零でない次数も全て同じ一定の基底射列へ送る。
使われ方：元の固定右脚の Hom から全右脚の bar への射の反転。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.BarRows.valueInclusion`。

```lean
universe v uD vD
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

def valueInclusion (d : D) : SSet.uliftFunctor.{max uD vD, v}.obj (F.obj d) ⟶
    (BarConstruction.functor D).obj F
```

### [CofinalAnodyneImage.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/CofinalAnodyneImage.lean)

OE03、64原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CofinalAnodyneImage`。

# 元の left cofinal な射の anodyne 反転後の可逆性

概要：Low 命題 3.7 の成分ごとの余終性を元の anodyne 局所化の反転性へ移す。
方針：元の left anodyne・trivial Kan 因子分解と全単射の右類の収縮を使う。
規約：元の射や両対象を置き換えず、単体集合モデルを要求しない。
使われ方：固定右脚の全比較の同じ局所化における反転性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.leftAnodyne_anodyne`。

```lean
universe u uH vH

lemma leftAnodyne_anodyne {A B : SSet.{u}} (i : A ⟶ B) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) :
    SSet.anodyneExtensions i
```

### [CommaNerveBarProjection.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/CommaNerveBarProjection.lean)

OE03、107原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerveBarProjection`。

# comma 図式の bar から元の圏の nerve への射影の反転

概要：任意の p : E → D で、CostructuredArrow p の nerve の bar を元の nerve E へ送る。
方針：各行で元の射列への射影と最後の頂点による収縮を使い、対角で反転性を得る。
規約：元の射列・構造射・全単体作用素を保つ。単体集合モデルは仮定しない。
使われ方：Thomason 比較の証明に挟む comma 図式の全体の射影。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.CommaNerve.projection`。

```lean
universe uE vE uD vD
variable {E : Type uE} [Category.{vE} E] {D : Type uD} [Category.{vD} D]
  (p : E ⥤ D) (n : ℕ)

def projection : nerve (values p n).Elements ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj
      (ULift.{max uD vD} (ComposableArrows E n))
```

### [CommaNerveContraction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/CommaNerveContraction.lean)

OE03、95原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerveContraction`。

# costructured arrow の射列を最後の頂点で収縮する

概要：CostructuredArrow p d の射列をラベルとする要素圏の各成分を収縮する。
方針：元の射列の最後の頂点の像を基底に選び、各頂点から最後への射で復元する。
規約：添字・値の宇宙を分け、元の全射列と構造射を保持する。
使われ方：Thomason 比較の証明に挟む comma 図式の各行の収縮。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.CommaNerve.values`。

```lean
universe uE vE uD vD
variable {E : Type uE} [Category.{vE} E] {D : Type uD} [Category.{vD} D]
  (p : E ⥤ D) (n : ℕ)

abbrev values
```

### [CommaPreLeftCofinality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/CommaPreLeftCofinality.lean)

OE03、70原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaPreLeftCofinality`。

# 元の左変数の余終性から全図式の比較の余終性

概要：Low 命題 3.7 の全図式の左変数の比較の nerve を反転する。
方針：各 comma の元の切断と収縮により、分解側の弱可縮な comma へ移す。
規約：元の比較射の全対象・全射を保持し、モデル構造を要求しない。
使われ方：固定右脚ごとの比較を全右脚の図式へ接続する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.CommaPreLeft.projection_localized_isIso`。

```lean
universe u
variable {K L C J : Type u} [Category.{u} K] [Category.{u} L]
  [Category.{u} C] [Category.{u} J]
  (P : K ⥤ L) (Q : L ⥤ C) (R : J ⥤ C)

lemma projection_localized_isIso (T : Comma Q R) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaPreLeftRetraction.projection P Q R T)))
```

### [ComonadResolutionFunctoriality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ComonadResolutionFunctoriality.lean)

OE03、113原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolutionFunctoriality`。

# Comonad 解像の冪と全作用素の係数自然性

概要：Dwyer–Kan の自由解像を係数の射に関手的にする一般界面を構成する。
方針：冪の射を反復し、余単位・対角の自然性を全ての面・退化へ移す。
規約：一般の圏と comonad のみを使い、モデル構造は要求しない。
使われ方：自由単体的局所化へ相対関手を送る。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.ComonadResolution.powerMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (G : Comonad C)

def powerMap {X Y : C} (f : X ⟶ Y) : (n : ℕ) → power G X n ⟶ power G Y n
  | 0 => f
  | n + 1 => G.map (powerMap f n)

/-- 概要：反復冪の射は恒等射を保つ（Dwyer–Kan）。
方針：同じ G の恒等則を反復する。
規約：全次数の厳密な等式。
使われ方：解像を係数に関して関手にする。 -/
lemma powerMap_id (X : C) (n : ℕ) : powerMap G (𝟙 X) n = 𝟙 (power G X n)
```

### [ComonadResolutionMap.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ComonadResolutionMap.lean)

OE03、149原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolutionMap`。

# Comonad の全単体的解像の係数関手

概要：Dwyer–Kan の解像に係数の射を全単体作用素と両立して送る。
方針：表示単体圏の生成射への自然性を帰納し、同じ通常の単体圏へ移す。
規約：元の解像と augmentation を保持する。
使われ方：相対関手を単体的局所化の間の関手へ送る。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.ComonadResolution.oppositeMap_naturality`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (G : Comonad C)

lemma oppositeMap_naturality {X Y : C} (f : X ⟶ Y)
    {n m : SimplexCategoryGenRel} (θ : n ⟶ m) :
    (ComonadResolutionPresentation.oppositeDiagram G Y).map θ ≫
        (powerMap G f (m.len + 1)).op =
      (powerMap G f (n.len + 1)).op ≫
        (ComonadResolutionPresentation.oppositeDiagram G X).map θ
```

### [ConstantBarAugmentation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ConstantBarAugmentation.lean)

OE03、97原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBarAugmentation`。

# 定値図式の bar から元の値への augmentation

概要：定値図式の元の bar を最初のラベルへ送る射は、始対象があれば反転される。
方針：各行の射影を自然変換へ束ね、同じ対角比較を適用する。
規約：元の bar の全作用素と値の宇宙拡大を保持する。単体集合モデルは不要。
使われ方：固定右脚の値と全右脚上の bar の比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.ConstantBar.labels`。

```lean
universe v uD vD
variable (D : Type uD) [Category.{vD} D] (K : SSet.{v})

abbrev labels (D : Type uD) [Category.{vD} D] (K : SSet.{v}) :
    SimplexCategoryᵒᵖ ⥤ SSet.{max uD vD v}
```

### [ConstantBarRows.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ConstantBarRows.lean)

OE03、94原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBarRows`。

# 定値図式の要素圏の各行の収縮

概要：定値図式の bar の各行を最初のラベルへ射影し、始対象で収縮する。
方針：ラベルを保って基底を始対象へ戻す関手と、その元の自然変換を使う。
規約：値と添字の宇宙は独立。単体集合のモデル構造は仮定しない。
使われ方：定値図式の bar の元の値への augmentation の反転性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.ConstantBar.values`。

```lean
universe v uD vD
variable (D : Type uD) [Category.{vD} D] (X : Type v)

abbrev values : D ⥤ Type v
```

### [CosimplicialHomCommaInvariance.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/CosimplicialHomCommaInvariance.lean)

OE03、58原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomCommaInvariance`。

# 元の Hom の不変性から小さい comma の不変性へ

概要：元の cosimplicial Hom で反転される右対象の射は、小さい comma でも反転。
方針：同じ反対要素圏の nerve の不変性・宇宙比較・元の自然な表示同値を合成。
規約：元の右対象の射を保持し、単体集合モデルや Hom の Kan 性は要求しない。
使われ方：元の分解の全右脚の小さい Cat 値図式の各遷移の不変性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.smallCommaMap_localized_isIso`。

```lean
universe u v w
variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C)

lemma smallCommaMap_localized_isIso {V W : C} (f : V ⟶ W)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap
      (CostructuredArrow.map (S := smallDiagram.{u, v, w} A) (AsSmall.up.map f))))
```

### [CosimplicialHomElements.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/CosimplicialHomElements.lean)

OE03、59原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements`。

# 元の cosimplicial Hom の反対要素圏と comma 圏

概要：同じ Hom の全単体と作用素を、元の cosimplicial 図式の comma 圏で表示する。
方針：単体の次数・元の射・元の単体作用素を取り出す明示的な順逆を作る。
規約：モデル構造・置換・cofibrancy は不要。反対を fiber の要素圏だけに取る。
使われ方：固定右脚の元の Hom と全右脚の分解の図式の接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.toComma`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C) (V : C)

def toComma : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj V).Elements)ᵒᵖ ⥤ CostructuredArrow A V
```

### [EnrichedHomFunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/EnrichedHomFunctor.lean)

OE03、71原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.EnrichedHomFunctor`。

概要：局所 Kan な単体的圏の同じ豊穣 Hom を空間値の豊穣関手に束ねる。
方針：元の合成の curry を作用とし、元の単位・結合律を使う。
規約：全高次 Hom の作用を保持し、頂点の比較だけから自然性を推論しない。
使われ方：hammock の strict Hom 図式と Yoneda 側の全比較の入力。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.enrichedHomFunctor`。

```lean
universe u v
variable {D : Type v} [Category.{u} D] [SimplicialCategory D]
  [∀ A B : D, KanComplex (SimplicialCategory.sHom A B)] (X : D)

def enrichedHomFunctor : EnrichedFunctor SSet.{u} D _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}
```

### [EnrichedHomRealization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/EnrichedHomRealization.lean)

OE03、77原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.EnrichedHomRealization`。

概要：元の豊穣 Hom 関手を小さい coherent nerve 全体で空間値に実現する。
方針：同じ豊穣関手を全単体で後合成し、通常の nerve の制限を全次数で照合する。
規約：宇宙持ち上げと元の全 Hom 作用を保持する。
使われ方：strict hammock Hom 図式から正本の共変 Hom 関手への全比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.enrichedHomCoherent`。

```lean
universe u
variable {D : Type u} [Category.{u} D] [SimplicialCategory D]
  [∀ A B : D, KanComplex (SimplicialCategory.sHom A B)] (X : D)

def enrichedHomCoherent : SSet.uliftFunctor.{u + 1, u}.obj (SimplicialNerve D) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}
```

### [EnrichedHomYoneda.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/EnrichedHomYoneda.lean)

OE03、48原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.EnrichedHomYoneda`。

概要：E2 の元の豊穣 Hom 実現へ正本の全 Yoneda 比較を代入する。
方針：元の豊穣関手の全作用を厳密に同定して原本の関手同型を使う。
規約：原本の複製や点ごとの比較による全図式同型の推測はしない。
使われ方：同じ hammock 終端から正本 Hom∞ への無条件の全比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.enrichedHomFunctor_eq_representableHomFunctor`。

```lean
universe u
variable {D : Type u} [Category.{u} D] [SimplicialCategory D]
  [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]

lemma enrichedHomFunctor_eq_representableHomFunctor (x : D) :
    enrichedHomFunctor x = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomFunctor x
```

### [FibrantFrameSpanComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FibrantFrameSpanComparison.lean)

OE03、126原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison`。

概要：fibrant な元の標的で source frame の全単体を全三本矢へ弱比較する。
方針：同じ固定 fiber、全解像図式、全左脚図式、元の三本矢の回収を合成する。
規約：全単体と元の射を保ち、全対象 fibrant の仮定を加えない。
使われ方：bifibrant 中継での実 frame と hammock の比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FibrantFrameSpanComparison.fiberNerveMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {X : C} (q : CofibrantResolution (C := C) simplex X) (Y : C) [IsFibrant Y]

def fiberNerveMap : nerve (AsSmall.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ)) ⟶
    nerve ((resolutionDiagram q Y).obj (smallInitial Y))
```

### [FibrantFrameSpanNormalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FibrantFrameSpanNormalization.lean)

OE03、111原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanNormalization`。

概要：全図式による弱比較を元の source frame の同じ三本矢の射へ戻す。
方針：全単体で元の脚と中間射を回収し、固定端点の恒等合成だけを消す。
規約：ホモトピーによる別射への置き換えをしない。
使われ方：元の二列 roof と hammock の実比較の弱同値性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FibrantFrameSpanNormalization.comparisonFunctor`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {X : C} (q : CofibrantResolution (C := C) simplex X) (Y : C)

def comparisonFunctor : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y
```

### [FibrantRightResolutionDiagram.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FibrantRightResolutionDiagram.lean)

OE03、118原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram`。

概要：fibrant な全右脚上で元の Reedy 解像と全左脚を比較する。
方針：同じ固定右対象の余終性と同じ終域の Hom 不変性を全図式に適用する。
規約：元のモデル圏の全対象 fibrant は仮定せず、右終域だけを制限する。
使われ方：一般モデル圏の frame から全三本矢への実比較の弱同値性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FibrantRightResolutionDiagram.smallRightForget`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {X : C} (q : CofibrantResolution (C := C) simplex X) (Y : C)

def smallRightForget : AsSmall.{max u v} (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Base Y) ⥤
    AsSmall.{max u v} C
```

### [FibrantSourceReducedComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FibrantSourceReducedComparison.lean)

OE03、89原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantSourceReducedComparison`。

概要：fibrant 標的への元の source frame 比較を同じ reduced hammock へ接続する。
方針：全要素圏の宇宙同型、同じ三本矢の包含と正規化を合成する。
規約：元の二列の射と全単体作用素を保持する。
使われ方：bifibrant 部分圏での実 right Kan 比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.frameElementSmallIso`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X) (Y : C)

def frameElementSmallIso :
    nerve (ULiftHom.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ)) ≅
      nerve (AsSmall.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ))
```

### [FibrantSourceReducedFirst.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FibrantSourceReducedFirst.lean)

OE03、68原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantSourceReducedFirst`。

概要：元の source frame から hammock への比較の第二分解入力を除く。
方針：弱な右脚の第一分解による特殊三本矢比較を代入する。
規約：同じ元の二列比較射と全単体を保持する。
使われ方：採用済みの第一関手的分解だけによる一般モデル圏の比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.resolutionLeftRoofColimitMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X) (Y : C)

def resolutionLeftRoofColimitMap
```

### [FixedRightGrothendieckInversion.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FixedRightGrothendieckInversion.lean)

OE03、82原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FixedRightGrothendieckInversion`。

# 分解から全左脚への右変数の全図式の比較の反転

概要：Low 命題 3.7 の元の Grothendieck 図式の比較を anodyne 反転後に可逆とする。
方針：元の comma 表示での比較との厳密な整合と全 comma の収縮を使う。
規約：元の全図式の比較関手を保持し、単体集合モデルは要求しない。
使われ方：元の Map^h から三本矢の全図式への比較の分解側の反転性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.fixedRightGrothendieckComparison_toComma`。

```lean
universe u
variable {K L C J : Type u} [Category.{u} K] [Category.{u} L]
  [Category.{u} C] [Category.{u} J]
  (P : K ⥤ L) (Q : L ⥤ C) (R : J ⥤ C)

lemma fixedRightGrothendieckComparison_toComma :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedRightGrothendieckComparison P Q R ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma Q R =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaGrothendieck.toComma (P ⋙ Q) R ⋙ Comma.preLeft P Q R
```

### [FrameArrowAugmentationLimits.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameArrowAugmentationLimits.lean)

OE03、64原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrowAugmentationLimits`。

# 元の augmentation を反転する関手の全矢図式の実極限

概要：元の augmentation の円柱を反転関手で送り、同じ値の定値図式へ比較する。
方針：全成分の可逆性で関手同型を作り、可縮な次数圏の実極限を移送する。
規約：任意 quasicategory 標的。対象ごとの同型の族で全関手同型を代用しない。
使われ方：source frame の右 Kan 局所図式へ移すための実極限の供給。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.augmentationHomotopy`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ C) {X : C} (p : A ⟶ (Functor.const I).obj X)
  {E : SSet.{u}} [SSet.Quasicategory E] (F : nerve C ⟶ E)
  (hp : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated)

def augmentationHomotopy : SSet.Homotopy (nerveMap A ≫ F)
    (SSet.const (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)))
```

### [FrameArrowCofinality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameArrowCofinality.lean)

OE03、46原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrowCofinality`。

# 元の恒等矢の包含の ∞ 圏的 left cofinal 性

概要：元の随伴の counit が指定する各 comma の終対象で Quillen A を検査する。
方針：通常の comma の nerve と既存の native slice の同型を使う。
規約：通常の initial 性だけで代用せず、元の nerve 写像自身の cofinal 性を証明する。
使われ方：source frame の全矢の局所極限を次数圏へ制限する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.nerveMap_leftAdjoint_isLeftCofinal`。

```lean
universe u

lemma nerveMap_leftAdjoint_isLeftCofinal {I D : Type u}
    [Category.{u} I] [Category.{u} D] {L : I ⥤ D} {R : D ⥤ I} (a : L ⊣ R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap L)
```

### [FrameArrowElements.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameArrowElements.lean)

OE03、62原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrowElements`。

# 元の frame Hom の全単体と固定終域の矢の照合

概要：元の反対要素圏を同じ frame の costructured arrow 圏と同値にする。
方針：元の単体・元の単体作用素をそのまま矢・可換三角形へ送る。
規約：固定終域と元の右脚を保持し、全矢の comma 圏への包含も厳密に供給する。
使われ方：既存 sourceFrameHom 比較の全体への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.elementsToCostructured`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C) (Y : C)

def elementsToCostructured : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y).Elements)ᵒᵖ ⥤
    CostructuredArrow A Y
```

### [FrameArrowLimits.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameArrowLimits.lean)

OE03、32原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrowLimits`。

# 元の frame の全矢の図式の極限を次数圏へ制限する

概要：全矢の終域図式の極限と元の frame 上の図式の極限を同値にする。
方針：元の恒等矢の包含の left cofinal 性と厳密な射影の式を使う。
規約：標的は任意の quasicategory。全極限の存在は要求しない。
使われ方：source frame による右 Kan 局所極限の構成。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.identityInclusion_nerve_target`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C)
  {E : SSet.{u}} [SSet.Quasicategory E] (F : nerve C ⟶ E)

lemma identityInclusion_nerve_target :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.identityInclusion A) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.target A) = nerveMap A
```

### [FrameArrowRightKan.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameArrowRightKan.lean)

OE03、76原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrowRightKan`。

# 元の frame の全矢から実右 Kan 形状への比較

概要：同じ augmentation の逆と元の右脚を、一つの全変換として coslice に実現する。
方針：元の関手同型と右脚の円柱の h Fun 類を合成し、全区間を持ち上げる。
規約：元の qX・始域射影・全右脚を保持する。left cofinal 性は別工程。
使われ方：source frame の実局所極限を右 Kan 図式へ移す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.totalAugmentation`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ C) {X : C} (p : A ⟶ (Functor.const I).obj X)
  {E : SSet.{u}} [SSet.Quasicategory E] (q : nerve C ⟶ E)
  (hp : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (p.app i)).map q).toTruncated)

def totalAugmentation : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.degree A ⋙ A ⟶ (Functor.const (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.Total A)).obj X
```

### [FrameAugmentationLimitLegs.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameAugmentationLimitLegs.lean)

OE03、52原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameAugmentationLimitLegs`。

# 可逆 augmentation の元の極限錐の全脚

概要：同じ全 augmentation を反転する関手の任意の実極限錐の脚を可逆とする。
方針：全錐の同型と指定された全評価ホモトピーの輸送を合成する。
規約：極限対象の同型だけで脚の可逆性を推論しない。
使われ方：実右 Kan 単位の同じ成分の可逆性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.augmentationLimitConeFunctorIso`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ C) {X : C} (p : A ⟶ (Functor.const I).obj X)
  {E : SSet.{u}} [Quasicategory E] (F : nerve C ⟶ E)
  (hp : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated)

def augmentationLimitConeFunctorIso (hI : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve I))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap A ≫ F)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.val (SSet.const (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)))
```

### [FrameElementSpans.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameElementSpans.lean)

OE03、82原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameElementSpans`。

# Frame Hom の全単体を三本矢へ送る図式

概要：Dwyer–Kan §7 の共通比較に、元の cosimplicial Hom の全単体を送る。
方針：各単体を同じ augmentation と右脚を持つ三本矢にし、全作用素を元の frame の射で送る。
規約：元の Hom の全単体と全作用素を保持し、モデル構造は要求しない。
使われ方：特殊な hammock の nerve と元の Map^h の高次比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.frameElementSpan`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (L R : MorphismProperty C)
  {X Y Z : C} (A : SimplexCategory ⥤ C) (p : A ⟶ (Functor.const SimplexCategory).obj X)
  (hp : ∀ n, L (p.app n)) (j : Y ⟶ Z) (hj : R j)

def frameElementSpan (s : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z).Elements)ᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L R X Y
```

### [FrameFunctorImage.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameFunctorImage.lean)

OE03、168原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameFunctorImage`。

概要：元の全 frame roof は相対関手の像の同じ全 frame roof に一致する。
方針：元の Hom の全単体と二列の全成分を関手で送る。
規約：元の augmentation・全作用素・全 hammock 比較射を保持する。
使われ方：bifibrant 部分圏の実比較を ambient モデル圏へ戻す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.frameFunctorImageHom`。

```lean
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative]
  {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) (A : SimplexCategory ⥤ C) (Y : C)

def frameFunctorImageHom : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y ⟶
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (A ⋙ F.functor)).obj (F.functor.obj Y)
```

### [FrameIndexAugmentation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameIndexAugmentation.lean)

OE03、80原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameIndexAugmentation`。

# 宇宙を揃えた反対要素圏の nerve の元の Hom への反転可能な射

概要：共通比較の実際の始域から元の単体集合の同じ宇宙持ち上げへの比較を構成する。
方針：元の射列の Hom の ULift の実同型と同じ終端 augmentation を合成する。
規約：元の単体・全作用素・augmentation を保持する。
使われ方：Dwyer–Kan §7 の同じ Map^h への共通比較の左射。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.liftedAugmentation`。

```lean
universe v w

def liftedAugmentation (K : SSet.{v}) :
    nerve (ULiftHom.{w} K.Elementsᵒᵖ) ⟶ SSet.uliftFunctor.{w, v}.obj K
```

### [FrameLeftRoof.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameLeftRoof.lean)

OE03、60原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLeftRoof`。

# 元の frame Hom の全単体を二列 roof へ送る

概要：同じ augmentation と元の Hom 単体を X←Aⁿ→Y の二列にする。
方針：全単体作用素を同じ frame の射で送り、全縦弱同値を保持する。
規約：元の終域と全単体・全作用素を保持する。
使われ方：恒等右脚の比較の全両端点自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.frameLeftRoofFunctor`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y : C} (A : SimplexCategory ⥤ C) (p : A ⟶ (Functor.const SimplexCategory).obj X)
  (hp : ∀ n, W (p.app n)) (hA : ∀ {i j} (a : i ⟶ j), W (A.map a))

def frameLeftRoofFunctor : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y).Elements)ᵒᵖ ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X Y
```

### [FrameLeftRoofPostcompose.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameLeftRoofPostcompose.lean)

OE03、89原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLeftRoofPostcompose`。

# 元の frame の二列比較の後合成の自然性

概要：元の終域射による全単体の後合成を同じ二列と連結語で照合する。
方針：元の同方向列の collapse と全縦射の回収を使う。
規約：元の frame・全単体作用素・同じ元の射を保持する。
使われ方：既存 Map^h と reduced hammock の終域自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.frameLeftRoofFunctor_postcompose`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y Z : C} (A : SimplexCategory ⥤ C) (p : A ⟶ (Functor.const SimplexCategory).obj X)
  (hp : ∀ n, W (p.app n)) (hA : ∀ {i j} (a : i ⟶ j), W (A.map a)) (g : Y ⟶ Z)

lemma frameLeftRoofFunctor_postcompose :
    (frameLeftRoofFunctor W A p hp hA (Y := Y)).prod'
        ((Functor.const _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) g)) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postCollapse =
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map g).mapElements.op ⋙ frameLeftRoofFunctor W A p hp hA
```

### [FrameLeftRoofPrecompose.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameLeftRoofPrecompose.lean)

OE03、63原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLeftRoofPrecompose`。

# 元の frame 比較による roof の始域自然性

概要：元の始域射を持つ frame の比較を四列ホモトピーへ代入する。
方針：同じ要素圏の射影から両 frame と全 augmentation を引き戻す。
規約：元の全単体・元の始域射・同じ frame を保持する。
使われ方：既存 Map^h の比較の始域自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.frameSpanSourceIndexMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X' X Y : C} (A' A : SimplexCategory ⥤ C)
  (p' : A' ⟶ (Functor.const SimplexCategory).obj X') (hp' : ∀ n, W (p'.app n))
  (p : A ⟶ (Functor.const SimplexCategory).obj X) (hp : ∀ n, W (p.app n))
  (hA' : ∀ {i j} (a : i ⟶ j), W (A'.map a))
  (hA : ∀ {i j} (a : i ⟶ j), W (A.map a)) (α : A' ⟶ A) (f : X' ⟶ X)
  (hα : α ≫ p = p' ≫ (Functor.const SimplexCategory).map f)

def frameSpanSourceIndexMap :
    ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y).Elements)ᵒᵖ ⥤
      ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A').obj Y).Elements)ᵒᵖ
```

### [FrameLiftComma.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameLiftComma.lean)

OE03、117原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLiftComma`。

# 分解の comma 圏と全持ち上げ単体の反対要素圏

概要：Low 命題 3.6 の分解の comma 圏を元の持ち上げ空間で表示する。
方針：元の fiber の全単体と可換三角形の全単射を全作用素へ拡張する。
規約：comma 圏の射は元の単体作用素と三角形の整合を保持する。
使われ方：分解から自明 fibration への comma 圏の可縮性の証明。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameLift.overFunctor`。

```lean
universe u v
variable {C : Type u} [Category.{v} C]
  (A : SimplexCategory ⥤ C) {X E B : C}
  (a : A ⟶ (Functor.const SimplexCategory).obj X) (p : E ⟶ B) (f : X ⟶ B)

def overFunctor : SimplexCategory ⥤ Over B
```

### [FrameLiftContraction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameLiftContraction.lean)

OE03、81原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLiftContraction`。

# 分解から自明 fibration への持ち上げ空間の実際の収縮

概要：Low 命題 3.6 の分解の asphericity に使う持ち上げ空間を収縮する。
方針：元の境界の持ち上げ性を同じ fiber へ引き戻し、単射の右類の収縮を使う。
規約：単体集合のモデル構造を仮定せず、元の LiftSpace と射影を保持する。
使われ方：共通比較の右射の分解側の comma 圏の可縮性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameLift.projection_mono_rlp`。

```lean
universe u v uH vH
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (A : SimplexCategory ⥤ C) {X : C}
  (a : A ⟶ (Functor.const SimplexCategory).obj X)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))
  {E B : C} (p : E ⟶ B) [Fibration p] [WeakEquivalence p] (f : X ⟶ B)

lemma projection_mono_rlp :
    (MorphismProperty.monomorphisms SSet.{v}).rlp (LiftSpace.projection A a p f)
```

### [FrameLiftSimplices.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameLiftSimplices.lean)

OE03、96原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLiftSimplices`。

# 元の持ち上げ空間の単体と実際の持ち上げ射

概要：Low 命題 3.6 の持ち上げ空間の全単体を元の可換三角形と同定する。
方針：既存の fiber の評価の引き戻し普遍性と点の単体の一意性を使う。
規約：別の fiber を定義せず、元の LiftSpace の包含を順写像に使う。
使われ方：全単体の反対要素圏と分解の comma 圏の比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameLift.evaluationPullback`。

```lean
universe u v
variable {C : Type u} [Category.{v} C]
  (A : SimplexCategory ⥤ C) {X E B : C}
  (a : A ⟶ (Functor.const SimplexCategory).obj X) (p : E ⟶ B) (f : X ⟶ B)

lemma evaluationPullback (n : SimplexCategoryᵒᵖ) :
    IsPullback ((LiftSpace.inclusion A a p f).app n) ((LiftSpace.projection A a p f).app n)
      (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p).app n) ((LiftSpace.point A a f).app n)
```

### [FrameRightKan.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRightKan.lean)

OE03、63原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRightKan`。

# 同じ frame augmentation の逆から実右 Kan 形状への比較

概要：元の全 augmentation を同時に反転し、同じ頂点からの coslice 図式へ実現する。
方針：一つの全関手同型の逆を実ホモトピーへ戻し、同じ全底で持ち上げる。
規約：元の qX・次数射影・全区間を保持する。cofinal 性は別に証明する。
使われ方：実屋根比較を用いる source frame の右 Kan 計算。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.frameRightKanHomotopy`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ C) {X : C} (p : A ⟶ (Functor.const I).obj X)
  {E : SSet.{u}} [SSet.Quasicategory E] (q : nerve C ⟶ E)
  (hp : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (p.app i)).map q).toTruncated)

def frameRightKanHomotopy : SSet.Homotopy
    (SSet.const (X := nerve I) (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))) (nerveMap A ≫ q)
```

### [FrameRightKanCanonical.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRightKanCanonical.lean)

OE03、51原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRightKanCanonical`。

# 同じ frame 次数比較による標準右 Kan 錐

概要：可逆な augmentation の元の coslice 実現から標準錐の極限性を得る。
方針：全 prism の後合成錐と標準錐の cofinal 制限を厳密に同定する。
規約：任意 quasicategory 標的と同じ全錐を保持する。
使われ方：元の局所化射による前合成の充満忠実性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.frameRightKanCanonicalCone_isLimit`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ C) {X : C} (p : A ⟶ (Functor.const I).obj X)
  {E : SSet.{u}} [Quasicategory E] (q : nerve C ⟶ E)
  (hp : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (p.app i)).map q).toTruncated)

lemma frameRightKanCanonicalCone_isLimit
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (frameRightKanMap A p q hp))
    (hI : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve I)) {Z : SSet.{u}} [Quasicategory Z] (G : E ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone q G (q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)))
```

### [FrameRoofComparisonInvariance.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofComparisonInvariance.lean)

OE03、75原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofComparisonInvariance`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.frameSpanSourceIndexMap_localized_isIso`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] {X Y : C}
  (A' A : SimplexCategory ⥤ C) (α : A' ⟶ A)

lemma frameSpanSourceIndexMap_localized_isIso
    (hα : IsIso (AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{max u v, v}.map
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Y)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (frameSpanSourceIndexMap (Y := Y) A' A α)))
```

### [FrameRoofCornerBaseProjection.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofCornerBaseProjection.lean)

OE03、39原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofCornerBaseProjection`。

# 元の corner 比較の正規化された Over 射影

概要：実 corner 比較を同じ Over n に射影すると元の次数モデルの第二射影になる。
方針：次数正規化の射影式を逆に解き、元の corner の第一射影を計算する。
規約：元の指定点・全単体・同じ次数同型を保つ。
使われ方：実評価の左脚を元の comma の評価自然変換へ戻す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap_inv_over`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)
  {S : SSet.{u}} (f : S ⟶ roofTarget A Y q)

lemma roofQuillenDegreeNormalizationMap_inv_over :
    inv (roofQuillenDegreeNormalizationMap A Y q b f) ≫
      pullback.fst _ _ ≫ (roofTargetDegreeSliceIso A Y q b).hom = pullback.snd _ _
```

### [FrameRoofCornerEvaluation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofCornerEvaluation.lean)

OE03、63原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofCornerEvaluation`。

# 元の実屋根 corner 全体から同じ次数の pinched Hom への弱評価

概要：元の全 corner を、指定次数の元の端点を持つ実写像空間へ送る。
方針：Over の恒等射上の fiber へ一つの全体評価を選び、その全底付き比較を保持する。
規約：元の点・元の q・全高次錐を保つ。Kan Hom 比較との照合は別工程。
使われ方：実 ProductCornerMap の弱同値性を元の写像空間の比較で検査する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofCornerTerminalEvaluation`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)
  [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (roofTargetProjection A Y q)]

def roofCornerTerminalEvaluation : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofTerminalEvaluation
    (roofCornerNormalizedProjection A Y q b) (roofCornerTerminal A Y q b)
```

### [FrameRoofCornerEvaluationPrism.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofCornerEvaluationPrism.lean)

OE03、73原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofCornerEvaluationPrism`。

# 元の corner 評価の同じ qY slice 内の実ホモトピー

概要：元の全錐から評価後の pinched 族まで、同じ slice 内の実円柱を保持する。
方針：元の全体評価の円柱を制限し、元の両 fiber 同型の射影式で終端を同定する。
規約：元の全時刻・全単体を保ち、辺ごとの比較で代用しない。
使われ方：実 ProductHomMap の全三角形の slice prism 表示。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofTargetSlicePointIso_projection`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)
  [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (roofTargetProjection A Y q)]

lemma roofTargetSlicePointIso_projection : (roofTargetSlicePointIso Y q).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y) ≫ q)
```

### [FrameRoofCornerEvaluationTriangle.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofCornerEvaluationTriangle.lean)

OE03、95原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofCornerEvaluationTriangle`。

# 元の corner 評価の任意パラメータ上の実合成三角形

概要：元の corner を任意の族で制限しても、同じ実 prism から全関手圏の三角形を得る。
方針：同じ qY slice の実ホモトピーと普遍錐評価を三辺の全円柱へ移す。
規約：全パラメータを保ち、左脚の標準自然変換との照合は別工程。
使われ方：実 ProductHomMap 側の全三角形の幾何的構成。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofCornerEvaluationRightHomotopy`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)
  [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (roofTargetProjection A Y q)]
  {S : SSet.{u}} (f : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (roofTargetProjection A Y q))

def roofCornerEvaluationRightHomotopy : SSet.Homotopy
    ((f ≫ roofCornerSourceSliceMap A Y q b) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))))
    (SSet.const (X := S) (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)))
```

### [FrameRoofCornerLeftBase.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofCornerLeftBase.lean)

OE03、47原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofCornerLeftBase`。

# 実 corner 評価の左円柱は同じ終対象 fiber の底円柱の像

概要：元の左円柱を Over n に射影した実評価の底円柱から回収する。
方針：二つの元の pullback.condition と点図式の等式輸送の射影式を接続する。
規約：同じ全円柱・選択済み評価・元の q を保つ。
使われ方：全関手圏での終対象性による標準左脚との比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofCornerEvaluationLeftHomotopy_h_base`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)
  [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (roofTargetProjection A Y q)]
  {S : SSet.{u}} (f : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b)
    (roofTargetProjection A Y q))

lemma roofCornerEvaluationLeftHomotopy_h_base :
    (roofCornerEvaluationLeftHomotopy A Y q b f).h =
      (terminalFiberBaseHomotopy (roofCornerNormalizedProjection A Y q b)
        (roofCornerTerminal A Y q b) (roofCornerTerminalEvaluation A Y q b)
        (f ≫ roofCornerNormalizationMap A Y q b)).h ≫
      nerveMap (Over.forget (roofTargetDegree A Y q b)) ≫ nerveMap A ≫ q
```

### [FrameRoofCornerNormalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofCornerNormalization.lean)

OE03、76原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofCornerNormalization`。

# 実屋根 corner の元の Over 次数による正規化

概要：元の指定点の全 corner を、同じ次数へ向かう矢の nerve 上で表示する。
方針：既存の全 slice 同型で引き戻しを同型にし、同じ恒等射上の fiber を回収する。
規約：元の点・元の屋根射影・元の次数を保つ。
使われ方：corner 全体から同じ指定次数の写像空間への実評価。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofCornerNormalized`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)

abbrev roofCornerNormalized
```

### [FrameRoofCornerProjectionLaws.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofCornerProjectionLaws.lean)

OE03、47原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofCornerProjectionLaws`。

# 元の corner 比較の始域射影と同じ標的内の全図式

概要：次数正規化の逆と corner 比較を通しても、元の始域と frame 図式を厳密に回収する。
方針：既存の同型の射影式を逆向きに解き、元の引き戻しの可換性を使う。
規約：元の比較射・元の点図式・全単体を保つ。
使われ方：実 ProductHomMap の幾何的三角形の始域を標準自然変換と同定する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofCornerSourceSliceMap_projection`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)

lemma roofCornerSourceSliceMap_projection : roofCornerSourceSliceMap A Y q b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))) =
      pullback.snd _ _ ≫ roofTargetProjection A Y q ≫ (nerveMap A ≫ q)
```

### [FrameRoofFiberPinched.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofFiberPinched.lean)

OE03、46原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofFiberPinched`。

# 元の実屋根の指定次数 fiber と同じ pinched Hom

概要：元の次数の fiber を、元の qA(n) と qY を結ぶ実写像空間と厳密に同定する。
方針：引き戻しの fiber 同型と、元の頂点・点図式の全写像の等式だけを使う。
規約：指定次数・元の q・元の全錐の単体を保ち、別の頂点を選ばない。
使われ方：屋根 corner の全体評価を既存の Kan Hom 比較へ接続する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofTargetFrameVertex`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E)

lemma roofTargetFrameVertex (n : I) :
    (nerveMap A ≫ q).app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n) = q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (A.obj n))
```

### [FrameRoofFiberPinchedProjection.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofFiberPinchedProjection.lean)

OE03、58原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofFiberPinchedProjection`。

# 元の屋根 fiber と pinched Hom の同型は全 slice 包含を保つ

概要：元の fiber 同型を同じ qY の全 slice に含めると元の屋根の錐を回収する。
方針：元の始点・点図式の等式輸送を全包含に移し、引き戻しの第一射影を計算する。
規約：全単体・元の点図式・元の q を保つ。
使われ方：実 corner 評価の prism の終端と元の pinched 族の照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofSliceFiberPointTransport_ι`。

```lean
universe u

lemma roofSliceFiberPointTransport_ι {E : SSet.{u}} {p p' : (Δ[0] : SSet.{u}) ⟶ E}
    (h : p = p') (x : E _⦋0⦌) :
    (eqToIso (congrArg (fun a => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection a) x) h)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p') x =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) x ≫ (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver h)).hom
```

### [FrameRoofQuillenSlice.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofQuillenSlice.lean)

OE03、72原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofQuillenSlice`。

# 元の実屋根の Quillen A slice を次数の Over 圏へ送る

概要：指定した実屋根の点と全高次 slice を、同じ次数へ向かう射の図式と照合する。
方針：slice の後合成・同じ点の厳密な輸送・元の nerve Over 同型を使う。
規約：元の指定点を保持し、全単体の射影式を証明する。
使われ方：sourceFrameHom×Δ[n] による元の全 Quillen A slice の比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofTargetOverBaseMap`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)

def roofTargetOverBaseMap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm b) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (roofTargetDegree A Y q b)))
```

### [FrameRoofSliceFibration.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofSliceFibration.lean)

OE03、93原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofSliceFibration`。

# 実屋根 slice の既存次数比較の Kan fibration 性

概要：実 Quillen A slice から同じ次数モデルへの元の射の全ホーンを充填する。
方針：元の相対 slice corner を指定点と Over の厳密同型で正規化する。
規約：元の指定点・次数・全錐・既存比較射を保つ。弱可縮性は別の主張。
使われ方：実 slice のホモトピー fiber 比較に必要な fibration 模型。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofTargetDegreeSliceIso`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)

def roofTargetDegreeSliceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm b ≫ roofTargetProjection A Y q) ≅
      nerve (Over (roofTargetDegree A Y q b))
```

### [FrameRoofSliceWeakContractibility.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofSliceWeakContractibility.lean)

OE03、66原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofSliceWeakContractibility`。

# 元の次数比較による実屋根 slice の弱可縮性の還元

概要：実 slice を相対始点評価の厳密な引き戻しとして保持する。
方針：既証の任意底の Kan 引き戻し不変性で、次数側の弱比較を全錐へ戻す。
規約：元の指定点・全高次錐を保つ。次数側の弱同値性自体は別途証明が必要。
使われ方：元の sourceFrameHom×Δ[n] の全単体比較から Quillen A の条件へ進む。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofQuillenDegreeCornerMap`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)
  {S : SSet.{u}} (f : S ⟶ roofTarget A Y q)

def roofQuillenDegreeCornerMap :
    pullback (f ≫ roofTargetProjection A Y q)
      (nerveMap (Over.forget (roofTargetDegree A Y q b))) ⟶
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (roofTargetProjection A Y q)
```

### [FrameRoofSource.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofSource.lean)

OE03、68原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofSource`。

# 元の frame の実屋根比較の始域を全固定終域の矢で表す

概要：元の native な slice 引き戻しを CostructuredArrow の nerve と厳密に同定する。
方針：元の左 Kan 形状比較と引き戻しの対称同型を合成する。
規約：次数射影・元の終域への矢・同じ q の屋根比較を保持する。
使われ方：sourceFrameHom の既存弱比較を実右 Kan cofinality へ接続する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofSource`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)

abbrev roofSource
```

### [FrameRoofSourceProjection.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofSourceProjection.lean)

OE03、53原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofSourceProjection`。

# 元の frame 屋根比較の全 slice 射影

概要：同じ実屋根比較の qY slice への射影を元の通常の右脚から回収する。
方針：元の pullback.lift の第一射影と Over nerve 同型の射影式を使う。
規約：元の q・元の点図式・全単体を保持する。
使われ方：実評価三角形の右脚と元の通常の自然変換との比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.frameRoofMap_over`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E)

lemma frameRoofMap_over : frameRoofMap A Y q ≫ pullback.fst _ _ =
    nerveMap (CostructuredArrow.toOver A Y) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso Y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) q
```

### [FrameRoofTarget.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameRoofTarget.lean)

OE03、66原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofTarget`。

# 元の frame の実屋根標的と次数射影

概要：実屋根標的を元の slice 引き戻しのまま扱い、右ファイブレーション性を供給する。
方針：元の射影を基底変換し、全 frame 射の反転から左側の充填性も得る。
規約：元の指定点・次数・全高次単体を保持し、頂点集合へ置き換えない。
使われ方：実屋根比較の Quillen A の全 slice の計算。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameArrows.roofTarget`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E)

abbrev roofTarget
```

### [FrameSpanNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameSpanNaturality.lean)

OE03、72原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameSpanNaturality`。

# Frame の比較と三本矢の全単体図式の自然性

概要：Dwyer–Kan §7 の共通図式を元の source frame と終域の比較に自然にする。
方針：元の比較射を三本矢の縦射へ送り、全単体作用素への自然性を照合する。
規約：同じ augmentation・右脚・元の単体写像を保持する。
使われ方：既存の関手的置換と共通比較の選択独立性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.frameSpanSourceComparison`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (L R : MorphismProperty C)
  {X Y Z Z' : C} {A A' : SimplexCategory ⥤ C}
  (p : A ⟶ (Functor.const SimplexCategory).obj X)
  (p' : A' ⟶ (Functor.const SimplexCategory).obj X)
  (hp : ∀ n, L (p.app n)) (hp' : ∀ n, L (p'.app n))
  (j : Y ⟶ Z) (hj : R j)

def frameSpanSourceComparison (α : A' ⟶ A) (hα : α ≫ p = p') :
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Z).mapElements.op ⋙ frameElementSpanFunctor L R A' p' hp' j hj ⟶
      frameElementSpanFunctor L R A p hp j hj
```

### [FrameSpanTargetHomotopy.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FrameSpanTargetHomotopy.lean)

OE03、81原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameSpanTargetHomotopy`。

# 元の frame の右脚比較の全単体の nerve ホモトピー

概要：同じ端点の右脚比較を元の要素圏の持ち上げからのホモトピーにする。
方針：元の自然変換の区間関手に全射列と区間パラメータを代入する。
規約：要素圏と元の圏の異なる Hom 宇宙を保持する。
使われ方：元の終域への frame Hom と既存 Map^h の比較の一致。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.frameSpanTargetIndexMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (L R : MorphismProperty C)
  {X Y Z Z' : C} (A : SimplexCategory ⥤ C)
  (p : A ⟶ (Functor.const SimplexCategory).obj X) (hp : ∀ n, L (p.app n))
  (j : Y ⟶ Z) (hj : R j) (j' : Y ⟶ Z') (hj' : R j')
  (β : Z ⟶ Z') (hβ : j ≫ β = j')

def frameSpanTargetIndexMap :
    ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z).Elements)ᵒᵖ ⥤
      ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z').Elements)ᵒᵖ
```

### [FullyFaithfulNerveRetraction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/FullyFaithfulNerveRetraction.lean)

OE03、87原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FullyFaithfulNerveRetraction`。

# 充満忠実な包含の自然な片側収縮から nerve の反転性

概要：充満忠実な包含が自然な単位または余単位を持つ戻しを持てば nerve を反転。
方針：包含先の自然変換を充満忠実性で包含元へ戻し、同じ二つのホモトピーを使う。
規約：随伴の三角恒等式や単体集合モデルは仮定しない。
使われ方：三本矢の各片脚の関手的置換による包含の反転性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FullyFaithfulNerveRetraction.liftUnit`。

```lean
universe u v
variable {A B : Type u} [Category.{v} A] [Category.{v} B]
  (I : A ⥤ B) [I.Full] [I.Faithful] (R : B ⥤ A)

def liftUnit (η : 𝟭 B ⟶ R ⋙ I) : 𝟭 A ⟶ I ⋙ R
```

### [GrothendieckCommaComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/GrothendieckCommaComparison.lean)

OE03、94原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.GrothendieckCommaComparison`。

# comma 全図式の忘却と元の移送の比較

概要：comma 全図式の忘却から、元の移送による全図式の比較への自然変換を作る。
方針：元の各脚の移送射を使い、Thomason 射の後の忘却を同じ bar 射影と照合。
規約：同じ宇宙の小圏。元の脚と全射を保持し、追加の比較を仮定しない。
使われ方：comma bar の射影の反転性を元の Thomason 射の反転性へ移す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.Thomason.commaTotalForget`。

```lean
universe u
variable {D : Type u} [Category.{u} D] (G : D ⥤ Cat.{u, u})

def commaTotalForget : Grothendieck (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaDiagram G) ⥤ Grothendieck G
```

### [GrothendieckCommaRetraction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/GrothendieckCommaRetraction.lean)

OE03、100原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.GrothendieckCommaRetraction`。

# 各 comma 圏から元の fiber への移送の反転性

概要：元の fiber を恒等脚で戻す包含と収縮を作り、移送の nerve を反転する。
方針：各脚の元の移送射を単位に使い、同じ恒等・合成則で可換性を照合する。
規約：同じ宇宙の小圏。fiber の包含の底に関する自然性は仮定しない。
使われ方：comma 図式から元の図式への bar の比較の成分不変性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.Thomason.fiberIntoComma`。

```lean
universe u
variable {D : Type u} [Category.{u} D] (G : D ⥤ Cat.{u, u}) (d : D)

def fiberIntoComma : G.obj d ⥤ CostructuredArrow (Grothendieck.forget G) d
```

### [GrothendieckFiberInvariance.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/GrothendieckFiberInvariance.lean)

OE03、36原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.GrothendieckFiberInvariance`。

# 不変な Cat 値図式の元の fiber 包含の反転

概要：始対象を持ち全遷移の nerve が反転される図式では、各 fiber の包含も反転。
方針：同じ bar の値の包含と Thomason 比較の厳密な因子分解を合成する。
規約：同じ宇宙の小圏。元の fiber の nerve の Kan 性は要求しない。
使われ方：元の固定右脚から全右脚の図式への比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.Thomason.fiberNerveMap_localized_isIso`。

```lean
universe u
variable {D : Type u} [Category.{u} D] (G : D ⥤ Cat.{u, u})

lemma fiberNerveMap_localized_isIso {i : D} (hi : IsInitial i)
    (hG : ∀ {d e : D} (f : d ⟶ e),
      IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (G.map f).toFunctor))) (d : D) :
    IsIso (AnodyneHomotopy.anodyneQ.map (fiberNerveMap G d))
```

### [HeterogeneousSmallComma.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/HeterogeneousSmallComma.lean)

OE03、128原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma`。

概要：異なる対象・Hom 宇宙を持つ二関手の comma を同じ小圏へ揃える。
方針：元の対象と射を up/down する明示的な順逆を使う。
規約：既存の SmallCommaGrothendieck は変更せず、宇宙一般化を別の葉とする。
使われ方：任意モデル圏の全左脚と fibrant な全右脚の図式の実回収。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.HeterogeneousSmallComma.liftFunctor`。

```lean
universe uK vK uJ vJ uC vC w
variable {K : Type uK} [Category.{vK} K] {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] (Q : K ⥤ C) (R : J ⥤ C)

abbrev liftFunctor (F : K ⥤ C) : AsSmall.{w} K ⥤ AsSmall.{w} C
```

### [HomInfinityEquivalenceTransport.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/HomInfinityEquivalenceTransport.lean)

OE03、69原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HomInfinityEquivalenceTransport`。

概要：指定同値と指定二胞体に沿って正本の共変 Hom の全図式を輸送する。
方針：原本の全共変 Hom 比較を合成し、元の二胞体の反転・持ち上げを co-Yoneda へ送る。
規約：原本は読み取り専用、元の全比較射と全二胞体を保持する。
使われ方：hammock の Yoneda 比較から指定局所化への全標的比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.homInfinityEquivalenceTransport`。

```lean
universe u

def homInfinityEquivalenceTransport {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A B) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant x)
      (SSet.uliftFunctor.{u + 1, u}.map e.hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (e.hom.app (op ⦋0⦌) x))
```

### [HomInfinityLocalizationTransport.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/HomInfinityLocalizationTransport.lean)

OE03、41原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HomInfinityLocalizationTransport`。

概要：同じ局所化比較と指定二胞体を保つ共変 Hom の全族輸送。
方針：同じ比較同値の全 Hom 関手性と同じ三角形の全図式比較を合成する。
規約：元の K と三角形を変更せず、頂点ごとの別の同型を選ばない。
使われ方：hammock の Yoneda 比較から指定局所化の Hom 関手への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.CoherentLocalizationComparison.homInfinityTransport`。

```lean
universe u
variable {A B D : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory D]
  {F : A ⟶ B} {G : A ⟶ D} (c : CoherentLocalizationComparison F G)

def CoherentLocalizationComparison.homInfinityTransport (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (SSet.uliftFunctor.{u + 1, u}.map F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (F.app (op ⦋0⦌) x))
      (SSet.uliftFunctor.{u + 1, u}.map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (G.app (op ⦋0⦌) x))
```

### [KanElementsFamily.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/KanElementsFamily.lean)

OE03、76原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.KanElementsFamily`。

概要：元の全要素圏のKan化を、同じ反対要素圏の終端augmentationへつなぐ。
方針：既存のnerve反転同型と全augmentationの自然性・反転性を合成する。
規約：底と全作用素を保ち、固定始域のroofとの等式は別に照合する。
使われ方：両変数のsource frameの全係数の規約の比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.simplexElementsNerveDiagram`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

abbrev simplexElementsNerveDiagram : I ⥤ SSet.{u}
```

### [KanHomFamily.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/KanHomFamily.lean)

OE03、64原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.KanHomFamily`。

概要：実 Hom 単体集合の全標的族を同じ Ex∞ により coherent な空間値図式にする。
方針：全族の一つの関手へ Ex∞ を後合成し、既存の Kan 図式の実現を使う。
規約：全標的と全作用素を保ち、弱自然変換を点ごとの逆へ置き換えない。
使われ方：right frame と hammock の全自然比較の coherent な実現。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.kanHomFamily`。

```lean
universe u v w
variable {C : Type u} [Category.{v} C]

def kanHomFamily (F : C ⥤ SSet.{w}) : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w}
```

### [KanHomFamilyOpposite.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/KanHomFamilyOpposite.lean)

OE03、75原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.KanHomFamilyOpposite`。

概要：同じ底全体でEx∞係数の反転を比較する。
方針：元のEx∞単位とその反転を、既存のKan係数のedgewise比較へつなぐ。
規約：反転するのは値であり、底とその全射はそのまま保つ。
使われ方：全要素圏と元の反対要素圏の係数規約の接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.kanHomFamilyUnit_isWeakHomotopyEquivalence`。

```lean
universe u

lemma kanHomFamilyUnit_isWeakHomotopyEquivalence (X : SSet.{u}) :
    IsWeakHomotopyEquivalence (exInfinityUnit.app X)
```

### [KanNerveOppositeFamily.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/KanNerveOppositeFamily.lean)

OE03、50原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.KanNerveOppositeFamily`。

概要：通常圏の全図式で、反対圏のnerveと元のnerveのKan係数を比較する。
方針：元のnerve反転同型の自然性を、既存のKan係数反転比較へ合成する。
規約：底とその全射を保ち、値の圏だけを反転する。
使われ方：元の全要素圏と反対要素圏の係数規約の照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.catNerveOppositeFamilyMap`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

def catNerveOppositeFamilyMap :
    (F ⋙ nerveFunctor) ⋙ SSet.opFunctor ⟶ (F ⋙ Cat.opFunctor) ⋙ nerveFunctor
```

### [LiftedResolutionLeftRoof.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/LiftedResolutionLeftRoof.lean)

OE03、43原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.LiftedResolutionLeftRoof`。

概要：元の持ち上げた通常のHom要素圏の反対nerveを、同じleft-roofの比較へ送る。
方針：同じ元の係数移送の厳密な同型と、元のresolutionLeftRoofColimitMapを合成する。
規約：弱同値性は元の実射についての既存定理から移す。新しい弱同値の仮定を置かない。
使われ方：元のnative fiberと同じ元の固定始域roofを照合する実際の基準射。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.liftedResolutionLeftRoofColimitMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X) (Y : C)

def liftedResolutionLeftRoofColimitMap :
    nerve (ULiftHom.{max u v}
      ((SSet.uliftFunctor.{max u v,v}).obj ((cosimplicialHom q.obj).obj Y)).Elements)ᵒᵖ ⟶
      SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
        (weakEquivalences C) X Y
```

### [LiftedSourceFrameElements.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/LiftedSourceFrameElements.lean)

OE03、52原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.LiftedSourceFrameElements`。

概要：同じ全source-frame係数の宇宙持ち上げの全要素を、元の射の全要素へ戻す。
方針：元のAsSmallのdownと係数のULift.downを全対象・全射で適用する。
規約：元の単体次数・ラベル・両変数の射を保つ。
使われ方：BEの同じ全source-frameの射を元のtwisted pairingへ送る。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.liftedSourceFrameIndex`。

```lean
universe u v
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)

abbrev liftedSourceFrameIndex
```

### [LiftedSourceFrameFiberRoof.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/LiftedSourceFrameFiberRoof.lean)

OE03、53原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.LiftedSourceFrameFiberRoof`。

概要：元の持ち上げたHomのfiber要素圏を、同じ固定標的のroofの反対圏へ戻す。
方針：Homの宇宙持ち上げ・単体のULift・既存のelements/costructured同値を合成する。
規約：通常の要素圏と反対の要素圏の向きを保持し、元の次数とラベルを回収する。
使われ方：同じnative fiber射と元の固定始域roofとの照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.liftedSourceFrameFiberRoofEquivalence`。

```lean
universe u v
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)

def liftedSourceFrameFiberRoofEquivalence (P : liftedSourceFrameIndex (C := C)) :
    (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P ≌
      (CostructuredArrow (Q.obj (AsSmall.down.obj P).1.unop)
        (R.obj (AsSmall.down.obj P).2))ᵒᵖ
```

### [LiftedSourceFramePairing.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/LiftedSourceFramePairing.lean)

OE03、64原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.LiftedSourceFramePairing`。

概要：同じ全source-frameの実射を、同じ元の両端を持つtwisted arrowへ送る。
方針：既存の全要素のdown・元の射・twisted pairingの全自然性を合成する。
規約：全射列・全単体作用素を保持する。augmentationの逆はまだ使わない。
使われ方：BEの元の同じ全要素から正本Homへのroof比較を組み立てる。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.liftedSourceFrameArrowDomain`。

```lean
universe u v
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)

def liftedSourceFrameArrowDomain :
    SimplicialTotalElements (liftedSourceFrameCoefficients Q R) ⥤ (AsSmall.{max u v} C)ᵒᵖ
```

### [LocalizationComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/LocalizationComparison.lean)

OE03、113原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.LocalizationComparison`。

概要：同じ辺集合の指定された二つの ∞ 局所化の Hom を実比較する。
方針：承認された一般局所化の一意性を読み取り専用で使い、同じ比較射を Hom に適用する。
規約：KST の暫定 import はこの葉に限る。dg 代数の KST モジュールは import しない。
使われ方：一般モデル側の比較を Sp の指定局所化へ移す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.localizationComparison_pinchedHom_isQCatEquivalence`。

```lean
universe u
variable {A Q D : SSet.{u}} [Quasicategory Q] [Quasicategory D]
  (F : A ⟶ Q) (G : A ⟶ D) (W : Set (A _⦋1⦌))
  (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G W)
  (K : Q ⟶ D) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ K) G)

lemma localizationComparison_pinchedHom_isQCatEquivalence (x y : Q _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap K x y)
```

### [MixedFrame.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/MixedFrame.lean)

OE03、117原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame`。

# 始域・終域の両 frame の実際の混合 Hom

概要：Hovey §5 の両側の frame の同次元の射を単体集合にする。
方針：二重 Hom の対角を取り、augmentation から二つの実際の比較射を作る。
規約：この段階ではモデル構造・弱同値性・Kan 性を仮定しない。
使われ方：始域 frame と右 frame の錐の自然な共通比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.MixedFrame.mixedFunctor`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C)

abbrev mixedFunctor : (SimplexCategoryᵒᵖ ⥤ C) ⥤ SSet.{v}
```

### [MixedFrameSource.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/MixedFrameSource.lean)

OE03、77原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrameSource`。

# 混合 Hom の始域 frame に関する自然な前合成

概要：Hovey §5.4 の混合 Hom の共同比較を始域 frame の射に自然にする。
方針：cosimplicial Hom と元の Hom の前合成を同じ対角へ移す。
規約：元の frame の射と augmentation の可換四角形を保持する。
使われ方：具体的な両錐比較の始域自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.MixedFrame.mixedSourceMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] {A B : SimplexCategory ⥤ C}

abbrev mixedSourceMap (a : A ⟶ B) : mixedFunctor B ⟶ mixedFunctor A
```

### [MixedNerveCoconePoint.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/MixedNerveCoconePoint.lean)

OE03、30原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveCoconePoint`。

概要：混合宇宙の実余錐 join は、指定された元の余錐頂点を厳密に回収する。
方針：同じ Hom 持ち上げの余錐の終端を取り、元の down の頂点評価へ戻す。
規約：点射全体の等式。使われ方：通常 augmentation の dg nerve 値余錐の固定条件。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.MixedNerve.coconeJoin_inr`。

```lean
universe u
variable {I C : Type (u + 1)} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

lemma coconeJoin_inr (c : Cocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (nerve I) (Δ[0] : SSet.{u + 1}) ≫ coconeJoin c = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c.pt
```

### [MixedNerveCoconePrism.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/MixedNerveCoconePrism.lean)

OE03、49原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveCoconePrism`。

概要：混合宇宙の通常余錐の全 join prism は、元の自然変換円柱そのものと一致する。
方針：既存の Hom 持ち上げ・同じ自然変換・同じ上下射を保持して余錐比較を移す。
規約：元の全単体の厳密な等式。使われ方：正規化 tensor の元の augmentation との比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.MixedNerve.liftedCocone`。

```lean
universe u
variable {I C : Type (u + 1)} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

def liftedCocone (c : Cocone F) : Cocone (lifted F)
```

### [MixedNerveConstant.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/MixedNerveConstant.lean)

OE03、28原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveConstant`。

概要：対象と Hom の宇宙が異なる通常圏の定値図式を同じ定値単体写像に同定する。
方針：元の nerve の全射列で定値関手の作用を比較する。
規約：元の指定頂点を保つ。使われ方：全正規化単体屋根の両端の定値図式への照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.MixedNerve.nerveMap_const`。

```lean
universe u
variable (I C : Type (u + 1)) [Category.{u} I] [Category.{u} C]

lemma nerveMap_const (x : C) :
    nerveMap ((Functor.const I).obj x) = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x)
```

### [MixedNerveConstantHom.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/MixedNerveConstantHom.lean)

OE03、118原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveConstantHom`。

概要：元の定値自然変換の全円柱を同じ成分辺の定値族へ同定する。
方針：全次数の通常円柱を計算し、元の成分辺の定値写像と照合する。
規約：元の自然変換・元の辺・全パラメータを保持する。
使われ方：元の自由単位の全図式制限を標準単位の定値族へ接続する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.MixedNerve.homotopy_const_h`。

```lean
universe u

lemma homotopy_const_h {I C : Type (u + 1)} [Category.{u} I] [Category.{u} C]
    {x y : C} (f : x ⟶ y) :
    (homotopy ((Functor.const I).map f)).h =
      snd (nerve I) (Δ[1] : SSet.{u + 1}) ≫ SSet.yonedaEquiv.symm (nerve.edgeMk f).edge
```

### [MixedNerveHomLiftIso.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/MixedNerveHomLiftIso.lean)

OE03、39原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveHomLiftIso`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.MixedNerve.up_down`。

```lean
universe u
variable (C : Type (u + 1)) [Category.{u} C]

lemma up_down : up C ≫ down C = 𝟙 _
```

### [MixedNerveHomRecovery.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/MixedNerveHomRecovery.lean)

OE03、68原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveHomRecovery`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.MixedNerve.down_up`。

```lean
universe u
variable (C : Type (u + 1)) [Category.{u} C]

lemma down_up : down C ≫ up C = 𝟙 _
```

### [MixedNerveNatTrans.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/MixedNerveNatTrans.lean)

OE03、93原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveNatTrans`。

# 対象と Hom の宇宙が異なる通常圏の元の自然変換円柱

概要：対象が大きい通常圏の同じ自然変換を全単体のホモトピーへ移す。
方針：Hom のみを上げた元の円柱を、そのまま元の nerve へ引き戻す。
規約：元の対象・元の射・指定自然変換を保持する。
使われ方：全代数の置換比較と離散入力の全関手比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.MixedNerve.up`。

```lean
universe u
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]

def up (C : Type (u + 1)) [Category.{u} C] : nerve C ⟶ nerve (ULiftHom.{u + 1} C)
```

### [MixedNerveNatTransFunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/MixedNerveNatTransFunctor.lean)

OE03、75原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveNatTransFunctor`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.MixedNerve.liftedFunctor`。

```lean
universe u
variable (C D : Type (u + 1)) [Category.{u} C] [Category.{u} D]

def liftedFunctor : (C ⥤ D) ⥤ (ULiftHom.{u + 1} C ⥤ ULiftHom.{u + 1} D)
```

### [NerveAsSmall.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/NerveAsSmall.lean)

OE03、91原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveAsSmall`。

# 対象と Hom の宇宙を同時に揃えた nerve の元の比較

概要：AsSmall の nerve を元の nerve の単体の ULift と実同型で比較する。
方針：元の射列の up・down と全作用素との交換を使う。
規約：元の対象・射・単体を保持し、圏の同値だけから同型を推論しない。
使われ方：分解の comma の可縮性を F1b の同じ宇宙の小圏へ移す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.NerveAsSmall.up_down`。

```lean
universe u v w
variable (C : Type u) [Category.{v} C]

lemma up_down : AsSmall.up.{v, u, w} (C := C) ⋙ AsSmall.down = 𝟭 C
```

### [NerveColumnComponentArrow.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/NerveColumnComponentArrow.lean)

OE03、52原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumnComponentArrow`。

概要：元の通常列の全関手射の評価を同じ成分辺の像へ比較する。
方針：元の自然変換円柱の成分式を同じ後合成へ送る。
規約：元の成分辺と両端表示を全 Arrow 等式で保持する。
使われ方：閉包内の全列自然性から実 U の指定成分正方形を回収する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.NerveColumn.hom_component_arrow`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C]

lemma hom_component_arrow {D : SSet.{u}} (q : nerve C ⟶ D)
    {V W : I ⥤ C} (a : V ⟶ W) (i : I) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (hom q a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk (a.app i)).map q).toTruncated)
```

### [NerveColumnNaturalityComponent.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/NerveColumnNaturalityComponent.lean)

OE03、44原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumnNaturalityComponent`。

概要：既存の全列自然性を元の指定通常射の成分正方形へ回収する。
方針：同じ指定射の定値列へ全列自然性を適用し、両経路を評価する。
規約：閉包内の全列比較を再利用し、元の成分射を保持する。
使われ方：実 U の全源比較と cofibrant 置換 augmentation の端点整合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.NerveColumn.hom_naturality_const_component`。

```lean
universe u

lemma hom_naturality_const_component {C : Type u} [Category.{u} C]
    {D : SSet.{u}} [Quasicategory D] {F G : nerve C ⟶ D}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) {x y : C} (f : x ⟶ y) :
    Arrow.mk (Truncated.HomotopyCategory.homMk ((nerve.edgeMk f).map F).toTruncated ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate e.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex y)) =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate e.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x) ≫
      Truncated.HomotopyCategory.homMk ((nerve.edgeMk f).map G).toTruncated)
```

### [NerveColumnRoofNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/NerveColumnRoofNaturality.lean)

OE03、133原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumnRoofNaturality`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.NerveColumn.hom`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  {E : SSet.{u}} [Quasicategory E]

def hom (F : nerve C ⟶ E) {V W : I ⥤ C} (a : V ⟶ W) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (nerveMap V ≫ F) (nerveMap W ≫ F)
```

### [NerveColumnWhiskering.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/NerveColumnWhiskering.lean)

OE03、102原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumnWhiskering`。

概要：元の通常変換と列の全同型の前合成・表示変更の法則。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.sameNerveTransformationPostIso_column`。

```lean
universe u

lemma sameNerveTransformationPostIso_column
    {I C : Type u} [Category.{u} I] [Category.{u} C]
    {F G : I ⥤ C} (η : F ⟶ G) {Q : SSet.{u}} [Quasicategory Q]
    (L : nerve C ⟶ Q)
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    (nerveTransformationPostIso η L hη).hom = NerveColumn.hom L η
```

### [NerveEquivalenceImage.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/NerveEquivalenceImage.lean)

OE03、52原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage`。

# 圏同値の元の nerve の射の anodyne 反転後の同型

概要：Low 命題 3.6 の comma 表示の圏同値を元の nerve の比較へ移す。
方針：同じ単位・余単位の自然変換のホモトピーから逆射の二つの法則を得る。
規約：単体集合モデルや nerve の Kan 性を仮定しない。
使われ方：持ち上げ空間の可縮性を実際の comma 圏へ移す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.NerveEquivalenceImage.imageIso`。

```lean
universe u v uH vH
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (e : C ≌ D) {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

def imageIso : L.obj (nerve C) ≅ L.obj (nerve D)
```

### [NerveOverRightPrism.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/NerveOverRightPrism.lean)

OE03、60原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveOverRightPrism`。

# 通常の Over 図式の実 slice 評価は元の右脚の円柱

概要：同じ qY slice への Over 図式を評価すると、元の余錐の自然変換の像を得る。
方針：点図式の等式輸送を消し、uncurry の自然性と全 nerve prism の一致を接続する。
規約：同じ q・元の全円柱を保持し、quasicategory 性は仮定しない。
使われ方：実 corner の幾何的右脚を元の標準右脚へ戻す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.sliceOverUncurry_pointTransport`。

```lean
universe u

lemma sliceOverUncurry_pointTransport {S X : SSet.{u}} {p p' : (Δ[0] : SSet.{u}) ⟶ X}
    (h : p = p') (f : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (f ≫ (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver h)).hom) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f
```

### [NerveQuillenA.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/NerveQuillenA.lean)

OE03、74原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveQuillenA`。

# 通常の comma の元の可縮性から nerve の余終性への接続

概要：元の comma 圏の終射の反転性から nerve の left cofinality を得る。
方針：F1b の comma と slice の実同型、弱可縮性の判定、Quillen A を使う。
規約：同じ宇宙の小圏で適用し、単体集合のモデル構造を要求しない。
使われ方：実際の分解の asphericity を右比較の余終性へ移す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.NerveQuillenA.nerveMap_isLeftCofinal_of_weaklyContractible_comma`。

```lean
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)

lemma nerveMap_isLeftCofinal_of_weaklyContractible_comma
    (h : ∀ d : D, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve (CostructuredArrow F d))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap F)
```

### [NerveTerminalImage.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/NerveTerminalImage.lean)

OE03、58原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveTerminalImage`。

# 終対象を持つ圏の nerve の元の終射の反転

概要：終対象の収縮により元の nerve の終射を anodyne 反転後に同型へ送る。
方針：恒等関手から同じ定値関手への自然変換の実際のホモトピーを使う。
規約：単体集合のモデル構造や群oid 条件を要求しない。
使われ方：反対要素圏の標準単体での終端 augmentation の反転性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.NerveTerminalImage.contraction`。

```lean
universe u v uH vH
variable {C : Type u} [Category.{v} C] {a : C} (ha : IsTerminal a)

def contraction : 𝟭 C ⟶ (Functor.const C).obj a
```

### [OppositeElementsInvariance.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/OppositeElementsInvariance.lean)

OE03、40原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.OppositeElementsInvariance`。

# 元の反対要素圏の nerve の不変性

概要：元の単体集合の比較が反転されれば、同じ反対要素圏の nerve の射も反転。
方針：既存の終端 augmentation の自然性と両成分の反転性を使う。
規約：通常の要素圏と反対要素圏を区別し、単体集合モデルは仮定しない。
使われ方：元の全右脚の Hom の不変性を全単体の圏の不変性へ移す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.map_localized_isIso`。

```lean
universe v

lemma map_localized_isIso {K L : SSet.{v}} (f : K ⟶ L)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap f.mapElements.op))
```

### [OverTerminalEvaluation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/OverTerminalEvaluation.lean)

OE03、63原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.OverTerminalEvaluation`。

# 元の Over 図式から恒等射への標準全ホモトピー

概要：元の Over 図式を恒等射へ送る唯一の自然変換と実円柱を保持する。
方針：Over の標準終対象から自然変換を作り、忘却像を元の余錐と同定する。
規約：全単体・元の構造射を保つ。
使われ方：実評価の底円柱と標準評価の全関手圏での比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.overTerminalTransformation`。

```lean
universe u
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (n : C) (T : I ⥤ Over n)

def overTerminalTransformation : T ⟶ (Functor.const I).obj (Over.mk (𝟙 n))
```

### [PinchedFamilyWeakDetection.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/PinchedFamilyWeakDetection.lean)

OE03、38原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.PinchedFamilyWeakDetection`。

# 全パラメータの区間族の射の一致による元の pinched 族の弱同値性

概要：全関手圏内の同じ射を表す二族の片方が弱同値なら、もう片方も弱同値となる。
方針：同じ区間模型で実ホモトピーを得て、既存の pinched 比較の弱同値性で反映する。
規約：パラメータ K は任意。各頂点上の π₀ の一致を入力とはしない。
使われ方：実 ProductHomMap と元の弱な基準射の高次比較の出口。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.pinchedFamily_weak_of_intervalFamilyHom_eq`。

```lean
universe u

lemma pinchedFamily_weak_of_intervalFamilyHom_eq {K X : SSet.{u}} [Quasicategory X]
    {x y : X.obj (Opposite.op (SimplexCategory.mk 0))} (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence g)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f
```

### [PointSliceCornerFibration.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/PointSliceCornerFibration.lean)

OE03、63原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.PointSliceCornerFibration`。

# 左ファイブレーションの指定点 slice の相対始点評価

概要：指定点への全錐から、元の始点と底の錐を保持する corner への射は Kan fibration。
方針：全ホーンと点の空境界の pushout join を、最後以外のホーンへ移す。
規約：元の指定点・元の底の全錐を保ち、モデル構造や Kan 全空間を仮定しない。
使われ方：実屋根 slice を次数図式上の始点評価の fiber として比較する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.joinHorn_point_leftAnodyne`。

```lean
universe u

lemma joinHorn_point_leftAnodyne (n : ℕ) (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn (n + 1) i) (⊥ : (Δ[0] : SSet.{u}).Subcomplex)).ι
```

### [ProductSimplexElementProjectionWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ProductSimplexElementProjectionWeak.lean)

OE03、66原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexElementProjectionWeak`。

# 元の積単体の反対要素圏から第一成分への弱射影

概要：元の全単体・全作用素を持つ nerve の射影自身が弱同値となる。
方針：同じ終端 augmentation の自然性と、元の積の収縮を宇宙持ち上げ後に使う。
規約：元の M・指定 n・Hom ULift と第一成分を保持する。
使われ方：屋根の ProductHomMap と保存済みの高次比較との照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.ProductSimplexLiftedOver.firstNerveMap`。

```lean
universe u
variable (M : SSet.{u}) (n : AsSmall.{u + 1} SimplexCategory)

def firstNerveMap : nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexLiftedOver.productElements M n) ⟶ nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexLiftedOver.elements M)
```

### [ProductSimplexUniverseProjectionWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ProductSimplexUniverseProjectionWeak.lean)

OE03、79原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexUniverseProjectionWeak`。

概要：元の積単体の次数 Over 表示と第一射影を任意の共通上限宇宙で扱う。
方針：元の全単体・作用素と up・down の往復を同じ max 宇宙で評価する。
規約：元の小さい単体集合と指定次数を保持する。
使われ方：一般モデル圏の実 roof 比較の積単体の次数表示。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.ProductSimplexUniverseOver.firstNerveMap`。

```lean
universe u w
variable (M : SSet.{u}) (n : AsSmall.{max u w} SimplexCategory)

def firstNerveMap : nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.productElements.{u, w} M n) ⟶ nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.elements.{u, w} M)
```

### [RealizationHomNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RealizationHomNaturality.lean)

OE03、69原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RealizationHomNaturality`。

# 実際の frame 実現随伴の係数自然性

概要：Hovey §5 の実際の Yoneda 拡張の Hom 随伴は frame の射に自然。
方針：随伴の各単体の式と同じ Kan 拡張の単位の自然性を使う。
規約：実現の射は既存の Realization.family の同じ射。
使われ方：各値の重み付き始域 Hom と図式 frame Hom の自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.realizationHomEquiv_app`。

```lean
universe u v
variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  {A B : SimplexCategory ⥤ C}

lemma realizationHomEquiv_app {X : SSet.{u}} {Y : C}
    (f : (Realization.functor A).obj X ⟶ Y) (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    (((Realization.adjunction A).homEquiv X Y f).app n) x =
      (Realization.unit A).app n.unop ≫
        (Realization.functor A).map (uliftYonedaEquiv.symm x) ≫ f
```

### [ResolutionAsphericity.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ResolutionAsphericity.lean)

OE03、98原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ResolutionAsphericity`。

# 自明 fibration の slice における実際の分解の asphericity

概要：Low 命題 3.6 の cosimplicial 分解側の全 comma 圏の可縮性を証明する。
方針：指定射の slice の充満包含を通して、同じ持ち上げ空間の収縮へ帰着する。
規約：分解の元の augmentation と全単体作用素を保持する。
使われ方：特殊な三本矢への右射の分解側のホモトピー余終性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.TrivialFibrationOver`。

```lean
universe u v uH vH
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}

abbrev TrivialFibrationOver (X : C)
```

### [ResolutionCofinality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ResolutionCofinality.lean)

OE03、64原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ResolutionCofinality`。

# 同じ分解の自明 fibration の slice への nerve の余終性

概要：Low 命題 3.6 の元の分解図式に F1b の Quillen A を適用する。
方針：全 comma の可縮性を同じ AsSmall の関手へ移し、native な slice を検査する。
規約：元の分解・augmentation・全作用素を保持し、単体集合モデルを要求しない。
使われ方：特殊な三本矢への共通比較の右射の分解側の余終性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.smallResolutionOverFunctor`。

```lean
universe u v w
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C] {X : C}

def smallResolutionOverFunctor (q : CofibrantResolution (C := C) simplex X) :
    AsSmall.{max w u v} SimplexCategory ⥤ AsSmall.{w} (TrivialFibrationOver X)
```

### [ResolutionCommaContraction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ResolutionCommaContraction.lean)

OE03、61原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ResolutionCommaContraction`。

# 分解から自明 fibration への comma 圏の可縮性

概要：Low 命題 3.6 の右 asphericity に現れる元の comma 圏の終射を反転する。
方針：全持ち上げ単体の反対要素圏との同値と同じ fiber の実際の収縮を使う。
規約：全次数の comma 圏を扱い、単体集合のモデル構造を要求しない。
使われ方：特殊な三本矢への共通比較の右射のホモトピー余終性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.FrameLift.commaTerminal_image_isIso`。

```lean
universe u v uH vH
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (A : SimplexCategory ⥤ C) {X E B : C}
  (a : A ⟶ (Functor.const SimplexCategory).obj X)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))
  (p : E ⟶ B) [Fibration p] [WeakEquivalence p] (f : X ⟶ B)

lemma commaTerminal_image_isIso {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow (overFunctor A a f) (Over.mk p)))))
```

### [ResolutionFixedRightComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ResolutionFixedRightComparison.lean)

OE03、91原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ResolutionFixedRightComparison`。

# 元の分解から各固定右脚への比較の余終性

概要：Low 命題 3.7 の中間 Hom の各固定終域で分解の余終性を証明する。
方針：同じ分解と左脚の slice の射影を AsSmall で揃えて元の comma の引き戻しへ渡す。
規約：元の分解と augmentation の全作用を保持し、単体集合モデルを要求しない。
使われ方：三本矢の右変数の全図式の成分ごとの比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.smallResolutionLeftForget`。

```lean
universe u v w
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]

def smallResolutionLeftForget (X : C) :
    AsSmall.{w} (TrivialFibrationOver X) ⥤ AsSmall.{w} C
```

### [RightFrameHammockCoherent.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameHammockCoherent.lean)

OE03、83原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHammockCoherent`。

概要：元の right frame Hom と同じ hammock Hom を全標的の coherent な関手同型で比較する。
方針：同じ六つの実弱自然変換を空間値の関手 ∞ 圏へ送り、同じ辺を順に反転する。
規約：指定 right frame と元の全図式を保持し、点ごとの逆の選択をしない。
使われ方：指定局所化の全 pinched Hom 族への接続と同じ二胞体の保持。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightFrameHammockCoherentDiagram`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C} [IsCofibrant X]
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

def rightFrameHammockCoherentDiagram (i : Fin 7) :
    SSet.uliftFunctor.{max u v + 1, max u v}.obj (nerve (AsSmall.{max u v} C)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max u v}
```

### [RightFrameHammockComponent.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameHammockComponent.lean)

OE03、109原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHammockComponent`。

概要：同じ全標的比較の六辺から元の right Hom と同じ全圏 hammock の実 pinched 同値を得る。
方針：同じ元の六つの Kan 比較・Ex∞ 単位・宇宙同型・coherent Hom 比較を合成する。
規約：coherent 全族の構成を保持し、hammock の局所化普遍性とは分ける。
使われ方：指定局所化への全比較の同じ成分と実 QCat 同値性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightFrameHammockKanEdgeEquivalence`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C} [IsCofibrant X]
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

def rightFrameHammockKanEdgeEquivalence (i : Fin 6) (Y : AsSmall.{max u v} C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      ((rightFrameHammockKanDiagram q r (rightFrameHammockEdgeSource i)).obj Y).obj
      ((rightFrameHammockKanDiagram q r (rightFrameHammockEdgeTarget i)).obj Y).obj
```

### [RightFrameHammockComponentImage.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameHammockComponentImage.lean)

OE03、70原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHammockComponentImage`。

概要：実 QCat 比較の選択した逆が同じ元の比較辺の反転と一致することを追跡する。
方針：同じ QCat 同値の指定単位を全ホモトピーとして anodyne 局所化へ送る。
規約：六辺の全自然比較を点ごとの任意の同値と切り離さない。
使われ方：同じ成分比較の単位・零単体公式の合成。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.qCatEquivalence_hom_inv_Q`。

```lean
universe u v w

lemma qCatEquivalence_hom_inv_Q {A B : SSet.{w}} [Quasicategory A] [Quasicategory B]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A B) :
    AnodyneHomotopy.anodyneQ.map e.hom ≫ AnodyneHomotopy.anodyneQ.map e.inv = 𝟙 _
```

### [RightFrameHammockFamily.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameHammockFamily.lean)

OE03、146原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHammockFamily`。

概要：実 right frame Hom と元の hammock Hom を全標的の自然同型で比較する。
方針：同じ混合 Hom・全要素 nerve・次数零置換を三つの全自然変換で接続する。
規約：anodyne 局所化での全族比較であり、指定 ∞ 局所化への完成定理と区別する。
使われ方：全 coherent 比較の構成と同じ実射の弱同値性の検出。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightFrameReplacementHomImageIso`。

```lean
universe u v uD vD
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

def rightFrameReplacementHomImageIso [IsCofibrant X] :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X ⋙ L ≅ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X ⋙ L
```

### [RightFrameHammockKanSpan.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameHammockKanSpan.lean)

OE03、125原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHammockKanSpan`。

概要：元の right frame と hammock の全比較を同じ六本の弱自然変換で露出する。
方針：混合 Hom・全要素 nerve・次数零置換の元の全図式を同じ宇宙で並べる。
規約：全比較は実射の自然変換であり、単に点ごとの同値を選ばない。
使われ方：関手 ∞ 圏の全同型と零単体正規化への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightFrameHammockFamilyDiagram`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

def rightFrameHammockFamilyDiagram : Fin 7 → C ⥤ SSet.{max u v}
  | 0 => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X ⋙ SSet.uliftFunctor.{max u v, v}
  | 1 => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X ⋙ SSet.uliftFunctor.{max u v, v}
  | 2 => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedFamily q r ⋙ SSet.uliftFunctor.{max u v, v}
  | 3 => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj ⋙ SSet.uliftFunctor.{max u v, v}
  | 4 => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ sourceFrameElementsFamily q
  | 5 => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ hammockHomFamily (weakEquivalences C) X
  | 6 => hammockHomFamily (weakEquivalences C) X

/-- 概要：元の六つの弱比較の始域添字。
方針：元の三つの逆向き比較を保持する。
規約：指定順序。使われ方：実比較の向きの保持。 -/
def rightFrameHammockEdgeSource : Fin 6 → Fin 7
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 4 | 5 => 6

/-- 概要：元の六つの弱比較の終域添字。
方針：元の混合 Hom と全要素比較を共通標的で読む。
規約：指定順序。使われ方：全自然変換の厳密な型。 -/
def rightFrameHammockEdgeTarget : Fin 6 → Fin 7
  | 0 => 1 | 1 => 2 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 5

/-- 概要：同じ六つの実弱比較を全標的の自然変換として公開する。
方針：元の単位・混合比較・要素 augmentation・roof を同じ順に使う。
規約：元の全単体の実射。使われ方：関手 ∞ 圏に移す比較辺。 -/
def rightFrameHammockFamilyEdge : (i : Fin 6) →
    rightFrameHammockFamilyDiagram q r (rightFrameHammockEdgeSource i) ⟶
      rightFrameHammockFamilyDiagram q r (rightFrameHammockEdgeTarget i)
  | 0 => Functor.whiskerRight
      (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X))
      SSet.uliftFunctor
  | 1 => Functor.whiskerRight
      (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedRight q r)) SSet.uliftFunctor
  | 2 => Functor.whiskerRight
      (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedLeft q r)) SSet.uliftFunctor
  | 3 => Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r) (sourceFrameElementsAugmentation q)
  | 4 => Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r) (sourceRoofFamily q)
  | 5 => Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r)
      (hammockHomFamily (weakEquivalences C) X)

variable [IsCofibrant X]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
include cof in
/-- 概要：同じ全自然変換の全成分自身は弱ホモトピー同値。
方針：同じ混合比較・実 roof・元の弱単位の反転性を使う。
規約：第一分解と指定 right frame。使われ方：coherent な全族の反転判定。 -/
lemma rightFrameHammockFamilyEdge_weak (i : Fin 6) (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((rightFrameHammockFamilyEdge q r i).app Y)
```

### [RightFrameHammockUnitComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameHammockUnitComparison.lean)

OE03、122原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHammockUnitComparison`。

概要：同じ六辺から選択した実比較の零単体を元の hammock 射へ照合する。
方針：全段階の同じ単位点を Ex∞ 自然性で送り、指定逆の単位で合成する。
規約：元の射・元の比較・選択した逆を保持する。
使われ方：指定局所化の二胞体による共役公式への入力。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.point_inverse_Q`。

```lean
universe u v w

lemma point_inverse_Q {A B T : SSet.{w}} [Quasicategory A] [Quasicategory B]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A B) (a : T ⟶ A) (b : T ⟶ B)
    (h : AnodyneHomotopy.anodyneQ.map a ≫ AnodyneHomotopy.anodyneQ.map e.hom =
      AnodyneHomotopy.anodyneQ.map b) :
    AnodyneHomotopy.anodyneQ.map b ≫ AnodyneHomotopy.anodyneQ.map e.inv =
      AnodyneHomotopy.anodyneQ.map a
```

### [RightFrameHammockUnitPoints.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameHammockUnitPoints.lean)

OE03、162原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHammockUnitPoints`。

概要：元の通常射を六辺の全比較の各段階で同じ零単体の点として追跡する。
方針：同じ augmentation の前後合成と実 roof の単位収縮を使う。
規約：同じ元の射・同じ六辺を保持し、逆比較の選択と切り離さない。
使われ方：実比較の零単体の正規化と指定二胞体の共役式への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.unitHom_eq_const`。

```lean
universe u v w

lemma unitHom_eq_const {K : SSet.{w}} (f : 𝟙_ SSet.{w} ⟶ K) :
    f = SSet.const (f.app (op ⦋0⦌) PUnit.unit)
```

### [RightFrameHomBifunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameHomBifunctor.lean)

OE03、56原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHomBifunctor`。

概要：元のright frame Homを始域にも反変な全関手としてまとめる。
方針：既存のcoyonedaと元のright frame図式へのwhiskeringを合成する。
規約：IS-W2 R02〜R03の既存Hom構成の全係数表示。元のframe・射を変更しない。
使われ方：固定始域ごとの比較と、始域の作用を区別して全自然性を照合する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightFrameHomBifunctor`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

def rightFrameHomBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v}
```

### [RightFrameHomInfinity.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameHomInfinity.lean)

OE03、51原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHomInfinity`。

概要：right frame の終端から指定局所化の正本共変 Hom への全標的同型。
方針：同じ原本 Yoneda 全比較を代入し、同じ K・二胞体の全族輸送へ合成する。
規約：追加の Yoneda 存在入力も SSet のモデル構造も要求しない。
使われ方：Sp の β6 f4d の全標的自然性と任意図式への制限。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightFrameTerminalHomIso`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {Q : SSet.{max u v}} [Quasicategory Q]
  {G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category ⟶ Q}
  (c : CoherentLocalizationComparison (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) G)

def rightFrameTerminalHomIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (rightFrameHammockCoherentDiagram q r 6)
      (SSet.uliftFunctor.{max u v + 1, max u v}.map G ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))))
```

### [RightFrameHomInfinityNormalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameHomInfinityNormalization.lean)

OE03、70原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHomInfinityNormalization`。

概要：同じ全 Hom 比較の合成と指定二胞体による元の局所化辺の回収。
方針：実終端・同じ原本 Yoneda・同じ K 輸送を露出し、元の三角形の自然性を使う。
規約：全同型とは別の局所化比較や二胞体を選び直さない。
使われ方：Sp が全図式比較と元の辺の零単体の正規化を同時に合成する入口。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightFrameTerminalHomIso_hom`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {Q : SSet.{max u v}} [Quasicategory Q]
  {G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category ⟶ Q}
  (c : CoherentLocalizationComparison (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) G)

lemma rightFrameTerminalHomIso_hom :
    (rightFrameTerminalHomIso q r c).hom =
      (rightFrameHammockTerminalRealizationIso q r).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
          (kanHammockHomInfinityIso (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))
          (SSet.uliftFunctor.{max u v + 1, max u v}.map
            (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)))).hom ≫
        (c.homInfinityTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))).hom
```

### [RightFrameRoofComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameRoofComparison.lean)

OE03、75原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameRoofComparison`。

概要：元の right frame の全単体を同じ右屋根の全圏と弱比較する。
方針：反対圏の同じ解像の固定右対象比較と全単体の明示的 comma 表示を合成する。
規約：中間射を変更せず、完全な hammock への比較とは区別する。
使われ方：一般モデル圏における frame から三本矢への比較の右屋根段階。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightFrameRoofCategory`。

```lean
universe u v w
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

abbrev rightFrameRoofCategory (X Y : C)
```

### [RightFrameSpecifiedLocalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameSpecifiedLocalization.lean)

OE03、73原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameSpecifiedLocalization`。

概要：同じ全圏 hammock の局所化普遍性を明示入力にした指定局所化の比較。
方針：元の六辺の全 coherent 比較と指定二胞体の端点輸送を合成する。
規約：この補助入口の普遍性入力は ModelRightFrameComparison の主入口で放電する。
使われ方：指定 K・二胞体を保つ主入口の構成。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightFrameSpecifiedLocalizationData`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C} [IsCofibrant X]
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  {Q : SSet.{max u v}} [Quasicategory Q]
  (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category ⟶ Q)
  (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)))
  (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C))
    (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)))
  (K : kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) ⟶ Q)
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) ≫ K) G)

def rightFrameSpecifiedLocalizationData :
    CoherentLocalizationComparison (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) G
```

### [RightFrameSpecifiedUnit.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameSpecifiedUnit.lean)

OE03、98原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameSpecifiedUnit`。

概要：指定局所化への実 frame 比較は元の局所化射の同じ零単体を保持する。
方針：同じ六辺の単位公式を元の AsSmall 射へ回収し、指定二胞体の比較を後合成する。
規約：指定 K と二胞体を保持し、生の辺の厳密化を要求しない。
使われ方：Sp の元の射・端点成分による共役の照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightFrameHammockPinchedEquivalence_unit_arrow_Q`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C} [IsCofibrant X]
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex) (f : X ⟶ Y)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

lemma rightFrameHammockPinchedEquivalence_unit_arrow_Q :
    AnodyneHomotopy.anodyneQ.map
      (rightFrameHammockUnitPoint q r f 0 ≫
        (rightFrameHammockPinchedEquivalence q r cof Y).hom) =
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).weakEquivalences (AsSmall.up.map f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫ kanHammockHomPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y))
```

### [RightFrameTerminalHomReduction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameTerminalHomReduction.lean)

OE03、46原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameTerminalHomReduction`。

概要：同じ終端図式から指定局所化の正本 Hom 図式への比較を Yoneda の一入力へ還元する。
方針：構成済みの実終端同型・全 Yoneda 比較・同じ K と全二胞体の輸送を合成する。
規約：Yoneda 入力は原本の供給待ちであり、この補助入口だけで完成としない。
使われ方：Ind-S (8) の公開全図式比較の直接代入。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightFrameTerminalHomIso_of_yonedaIso`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {Q : SSet.{max u v}} [Quasicategory Q]
  {G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category ⟶ Q}
  (c : CoherentLocalizationComparison (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) G)

def rightFrameTerminalHomIso_of_yonedaIso
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (kanHammockHomCoherent (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant ((hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)).app
        (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (rightFrameHammockCoherentDiagram q r 6)
      (SSet.uliftFunctor.{max u v + 1, max u v}.map G ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (G.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))))
```

### [RightFrameTerminalRealization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightFrameTerminalRealization.lean)

OE03、51原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameTerminalRealization`。

概要：元の right frame 全比較の終端を同じ hammock 豊穣 Hom の実現へ同定する。
方針：元の AsSmall 全自然同型と元の源関手での全図式等式を合成する。
規約：終端の元の七段階図式を変更せず、点ごとの弱同値を使用しない。
使われ方：原本の Yoneda 全比較と指定局所化の全二胞体の代入。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightFrameHammockTerminalRealizationIso`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

def rightFrameHammockTerminalRealizationIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (rightFrameHammockCoherentDiagram q r 6)
      (SSet.uliftFunctor.{max u v + 1, max u v}.map
        (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) ≫
          kanHammockHomCoherent (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X))
```

### [RightMixedBifunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/RightMixedBifunctor.lean)

OE03、83原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightMixedBifunctor`。

概要：元の混合frame比較の両変数の自然性を、一つの自然変換として束ねる。
方針：同じ関手的source frameの写像による前合成と、元のaugmentationを使う。
規約：IS-W2 R02〜R03の既存構成の自然性・合成則。新しいframeや比較は選ばない。
使われ方：全joint Hom比較の最初の二辺に、固定始域の比較をそのまま使う。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.rightMixedBifunctor`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (q : CofibrantResolutionFamily (C := C) simplex)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

def rightMixedBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v}
```

### [SimplexTerminalEquivalence.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/SimplexTerminalEquivalence.lean)

OE03、65原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalEquivalence`。

# 任意の単体集合での終端 augmentation の反転性

概要：反対要素圏の元の終端 augmentation は全単体集合で anodyne 反転後に可逆。
方針：元の標準単体の収縮から境界の貼り合わせと実際の骨格余極限で拡張する。
規約：標準単体だけの結論ではなく任意の単体集合を扱い、単体集合モデルは要求しない。
使われ方：Dwyer–Kan §7 の共通比較の frame 側の反転可能な左射。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.augmentation_localized_isIso`。

```lean
universe v uH vH

lemma augmentation_localized_isIso (K : SSet.{v}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (augmentation.app K))
```

### [SimplexTerminalFunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/SimplexTerminalFunctor.lean)

OE03、70原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalFunctor`。

# 反対要素圏の nerve の関手と余連続性

概要：終端 augmentation の始域を同じ全単体の関手へ束ねる。
方針：既存の反対 nerve の自然な同型で通常の要素圏の nerve の反転と比較する。
規約：三本矢の共通比較と同じ反対要素圏を保持する。
使われ方：任意の単体集合での augmentation の反転性の cellular な証明。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.functor`。

```lean
universe v

def functor : SSet.{v} ⥤ SSet.{v}
```

### [SimplexTerminalStandard.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/SimplexTerminalStandard.lean)

OE03、61原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalStandard`。

# 標準単体上の終端 augmentation の実際の反転性

概要：反対要素圏の終端 augmentation は標準単体上で anodyne 反転後に可逆。
方針：元の標準単体と同じ反対要素圏の終射を実際の収縮で反転する。
規約：単体集合のモデル構造を要求しない。全単体集合の定理は後続。
使われ方：cellular な比較の反転性の標準単体の入力。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.standardIsTerminal`。

```lean
universe v uH vH
variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

def standardIsTerminal (n : SimplexCategory) :
    IsTerminal (Opposite.op (SerrePositivity.SimplicialModel.SimplexNerve.standardInitial.{v} n))
```

### [SmallCommaContraction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/SmallCommaContraction.lean)

OE03、57原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallCommaContraction`。

# 同じ宇宙へ持ち上げた関手の全 comma 圏の可縮性

概要：元の comma 圏の可縮性を AsSmall の関手の同じ終射へ移す。
方針：元の nerve の ULift 比較と comma の実際の圏同値を合成する。
規約：終点も同じ元の対象の up として保持する。
使われ方：分解図式への F1b の Quillen A の適用。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.AsSmallComma.terminal_localized_isIso`。

```lean
universe u v u' v' w
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (d : D)

lemma terminal_localized_isIso
    (h : IsIso (AnodyneHomotopy.anodyneQ.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow F d))))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AsSmallComma.smallFunctor.{u, v, u', v', w} F) (AsSmall.up.obj d)))))
```

### [SmallCommaGrothendieck.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/SmallCommaGrothendieck.lean)

OE03、86原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallCommaGrothendieck`。

# 小さい全図式から元の comma への明示的な回収

概要：対象・射の宇宙を揃えた両関手の全図式から、元の両関手の comma を回収する。
方針：元の対象・中間射・左右の射を down し、同じデータの up を逆に使う。
規約：出力も AsSmall で同じ宇宙に揃える。元の中間射を保持する。
使われ方：元の Map^h の小さい全図式から元の三本矢の nerve への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck.smallFunctor`。

```lean
universe u v w
variable {K J C : Type u} [Category.{v} K] [Category.{v} J] [Category.{v} C]
  (Q : K ⥤ C) (R : J ⥤ C)

abbrev smallFunctor (F : K ⥤ C) : AsSmall.{w} K ⥤ AsSmall.{w} C
```

### [SmallCosimplicialHomElements.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/SmallCosimplicialHomElements.lean)

OE03、83原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallCosimplicialHomElements`。

# 同じ宇宙の小圏に揃えた元の Hom と comma の比較

概要：元の Hom の反対要素圏と分解の comma 圏を、同じ上限の小圏で比較する。
方針：元の次数と射を up/down する明示的な順逆を作る。
規約：対象・元の射・全作用素を保持し、同値の逆の代表を選ばない。
使われ方：元の全右脚の小さい図式への fiber の不変性の適用。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.smallDiagram`。

```lean
universe u v w
variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C) (V : C)

abbrev smallDiagram : AsSmall.{max w u v} SimplexCategory ⥤ AsSmall.{max w u v} C
```

### [SmallNerveInvariance.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/SmallNerveInvariance.lean)

OE03、49原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallNerveInvariance`。

# 元の nerve の反転性を同じ小圏の比較へ移す

概要：元の関手の nerve の反転性は、対象・射の宇宙を揃えても保存される。
方針：元の射列の up/down の同型と同じ宇宙拡大の自然性を使う。
規約：同じ関手と全単体作用素を保持し、大きい宇宙にもモデル構造を置かない。
使われ方：元の Hom の反対要素圏の不変性を小さい分解の図式へ移す。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.SmallNerve.functor`。

```lean
universe u v w
variable {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D)

abbrev functor : AsSmall.{w} C ⥤ AsSmall.{w} D
```

### [SourceFrameArrowElements.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/SourceFrameArrowElements.lean)

OE03、65原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SourceFrameArrowElements`。

概要：関手的source frameの全Hom単体を一つの要素圏にし、同じ両端と射を記録する。
方針：既存のresolutionHomを二度uncurryし、既存の要素圏の射の等式を使う。
規約：IS-W2 R03dの元の構成の全係数表示と合成則。frameや射を選び直さない。
使われ方：元の全source frameの射を、同じ両端が変数の屋根比較へ送る。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.sourceFrameArrowCoefficients`。

```lean
universe u v
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)

def sourceFrameArrowCoefficients :
    ((Cᵒᵖ × C) × SimplexCategoryᵒᵖ) ⥤ Type v
```

### [SourceRoofFamily.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/SourceRoofFamily.lean)

OE03、63原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SourceRoofFamily`。

概要：固定 source frame の実二列 roof 比較を全標的で自然な一つの族にする。
方針：元の要素圏の作用と元の hammock の後合成を関手に束ねる。
規約：同じ augmentation・全単体・全標的射を保持する。
使われ方：right frame との混合比較から全局所化 Hom 族への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.hammockHomFamily`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X : C)

def hammockHomFamily : C ⥤ SSet.{max u v}
```

### [SourceRoofUnitNormalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/SourceRoofUnitNormalization.lean)

OE03、80原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SourceRoofUnitNormalization`。

概要：source augmentation で表された元の射の実二列 roof を元の hammock 射へ正規化する。
方針：同じ augmentation を二列の縦射にした実ホモトピーを使う。
規約：元の射・元の roof と同じ単体的円柱を保持する。
使われ方：right frame の零単体比較と指定局所化の二胞体の照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.sourceFrameUnitElement`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}
  (q : CofibrantResolution (C := C) simplex X) (n : SimplexCategory) (f : X ⟶ Y)

def sourceFrameUnitElement :
    ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ
```

### [TerminalFiberBaseHomotopy.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/TerminalFiberBaseHomotopy.lean)

OE03、59原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.TerminalFiberBaseHomotopy`。

# 終対象 fiber への実評価の全底ホモトピーと一意性

概要：元の実評価の円柱を底へ射影し、終対象に定値な全関手への唯一の射と比較する。
方針：同じ fiber 包含の底の式と全関手圏の点ごとの終対象性を使う。
規約：元の全円柱を保ち、パラメータ空間への条件は付けない。
使われ方：実屋根三角形の左脚と標準評価との全関手圏での同定。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.terminalFiberBaseHomotopy`。

```lean
universe u
variable {E B S : SSet.{u}} (p : E ⟶ B) (t : B _⦋0⦌)
  (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofTerminalEvaluation p t) (g : S ⟶ E)

def terminalFiberBaseHomotopy : SSet.Homotopy (g ≫ p) (SSet.const (X := S) t)
```

### [TerminalFiberEvaluationWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/TerminalFiberEvaluationWeak.lean)

OE03、39原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.TerminalFiberEvaluationWeak`。

# 終対象 fiber への実全体評価の弱同値性

概要：同じ終対象 fiber への全体評価は、その実ホモトピーを保って弱同値となる。
方針：fiber 包含の right cofinal 性と、恒等射からの実ホモトピーを反転する。
規約：元の評価・包含を使う。全空間の Kan 性や単体集合モデル構造は要求しない。
使われ方：実屋根 corner から指定次数の Kan Hom への比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.terminalFiberEvaluation_weak`。

```lean
universe u

lemma terminalFiberEvaluation_weak {E B : SSet.{u}} [SSet.Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (t : B.obj (Opposite.op ⦋0⦌))
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex t) (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofTerminalEvaluation p t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence R.evaluation
```

### [ThomasonInversion.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ThomasonInversion.lean)

OE03、53原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonInversion`。

# 元の Thomason 比較射の反転性

概要：同じ宇宙の小圏の Cat 値図式で、元の Thomason 射を局所化で反転する。
方針：comma 図式の射影・移送の成分不変性・元の自然性の正方形を合成する。
規約：単体集合モデル・fiber の Kan 性・比較の弱同値性は入力しない。
使われ方：元の固定右脚から三本矢の全図式の nerve への比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.Thomason.map_localized_isIso`。

```lean
universe u
variable {D : Type u} [Category.{u} D] (G : D ⥤ Cat.{u, u})

lemma map_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (map G))
```

### [ThomasonNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ThomasonNaturality.lean)

OE03、53原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonNaturality`。

# Thomason 比較の元の係数自然性

概要：Cat 値図式の比較を、同じ bar と全図式の nerve の可換正方形へ送る。
方針：各対角頂点と元の移送の射を評価し、等式による移送を合成する。
規約：元の自然変換からの Grothendieck.map の射そのものを使う。
使われ方：固定右脚の図式から全左脚への比較との厳密な整合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.Thomason.nerveComparison`。

```lean
universe uD vD uC vC
variable {D : Type uD} [Category.{vD} D] {G H : D ⥤ Cat.{vC, uC}}

abbrev nerveComparison (α : G ⟶ H) : nerveDiagram G ⟶ nerveDiagram H
```

### [ThomasonNerveMap.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ThomasonNerveMap.lean)

OE03、58原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonNerveMap`。

# bar から Grothendieck 全図式の nerve への元の比較射

概要：元の二方向の射列の対角から、全図式の nerve への実際の射を構成する。
方針：全作用素での単体の交換を使い、同じ fiber 包含との厳密な整合を示す。
規約：値と添字の宇宙は独立。構成だけから弱同値性は主張しない。
使われ方：Low 定理1.6 の比較と元の固定右脚の nerve の射の照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.Thomason.map`。

```lean
universe uD vD uC vC
variable {D : Type uD} [Category.{vD} D] (G : D ⥤ Cat.{vC, uC})

def map : (BarConstruction.functor D).obj (nerveDiagram G) ⟶
    nerve (Grothendieck G)
```

### [ThomasonSimplex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/ThomasonSimplex.lean)

OE03、74原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonSimplex`。

# bar の同じ射列から Grothendieck 全図式の射列へ

概要：Cat 値図式の nerve の bar の単体を、元の全図式の単体に送る。
方針：基底の第 j 頂点で fiber の第 j 頂点を取り、元の移送と fiber の射を合成。
規約：基底と fiber の対象・射を保持する。反転性は別途証明する。
使われ方：Low 定理1.6 の Thomason 比較の実際の単体と全作用素の照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.Thomason.nerveDiagram`。

```lean
universe uD vD uC vC
variable {D : Type uD} [Category.{vD} D] (G : D ⥤ Cat.{vC, uC})

abbrev nerveDiagram : D ⥤ SSet.{max uC vC}
```

### [TotalElementsNativeClassification.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/TotalElementsNativeClassification.lean)

OE03、61原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.TotalElementsNativeClassification`。

概要：元の全係数と元の全要素圏のnative分類を、同じ単位とaugmentationで比較する。
方針：Homの持ち上げの全自然同型を外し、元の全要素augmentationの比較を合成する。
規約：底全体のFunctorIsoであり、固定始域のroofとの等式は別に確認する。
使われ方：全source frameの同じ係数からnativeな全分類への移送。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.totalElementsNerveCoefficientIso`。

```lean
universe u
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

def totalElementsNerveCoefficientIso :
    simplicialElementsCatDiagram F ⋙ nerveFunctor ≅ simplexElementsNerveDiagram F
```

### [UnitComparisonTransport.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/UnitComparisonTransport.lean)

OE03、73原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.UnitComparisonTransport`。

概要：同じ単位と弱な全 pinched 族による判定を、指定した同型で両端輸送する。
方針：元の全族三角形を同じ定値射と区間作用の公式で輸送する。
規約：単位比較自身・実関手・全パラメータを保持する。
使われ方：元の局所化源単位から既存の標準単位比較への弱同値性の移送。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.unitComparisonTransport_weak`。

```lean
universe u

lemma unitComparisonTransport_weak {K C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (U : C ⟶ D) {a b c d : C.obj (Opposite.op ⦋0⦌)}
    {z x : D.obj (Opposite.op ⦋0⦌)} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a b) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso c d)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso z x)
    (η : (HomotopyCategory.mk x : hoFunctor.obj D) ⟶
      HomotopyCategory.mk (U.app (Opposite.op ⦋0⦌) a))
    (ν : (HomotopyCategory.mk z : hoFunctor.obj D) ⟶
      HomotopyCategory.mk (U.app (Opposite.op ⦋0⦌) b))
    (p : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom b c) (r : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z (U.app (Opposite.op ⦋0⦌) c))
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence p) (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence r)
    (hu : s.hom ≫ η ≫ (hoFunctor.map U).toFunctor.map e.hom = ν)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K ν ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom
      (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap U b c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap U a d ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (U.app (Opposite.op ⦋0⦌) d) η)
```

### [UnitComparisonWeakDetection.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/UnitComparisonWeakDetection.lean)

OE03、41原行。配置：`SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.UnitComparisonWeakDetection`。

# 弱な probe の全族比較から元の単位比較への弱同値性の反映

概要：元の区間写像を弱な probe で調べ、同じ全族を表す弱な pinched 基準射から反映する。
方針：全 h Fun の射の一致を実ホモトピーに戻し、anodyne 局所化と二対三則を使う。
規約：検査対象の射自身の弱同値性や各頂点上だけの一致は仮定しない。
使われ方：標準単位比較に元の全要素族を代入する際の、Derived に依存しない最終判定。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.unitComparison_weak_of_probe_family`。

```lean
universe u

lemma unitComparison_weak_of_probe_family {K D X : SSet.{u}} [Quasicategory X]
    {x y : X.obj (Opposite.op (SimplexCategory.mk 0))}
    (f : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (p : K ⟶ D) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence p) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence g)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (p ≫ f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f
```

### [AnodyneWeakDetection.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/AnodyneWeakDetection.lean)

OE03、93原行。配置：`SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection`。

# 元の anodyne 局所化の同型から Kan 標的による弱同値への判定

概要：元の反転性を F1b の弱ホモトピー同値と弱可縮性へ移す。
方針：全 Kan 標的への内部 Hom の π₀ を反変関手とし、局所化の普遍性で反転する。
規約：元の始域・終域に Kan 性や単体集合モデルを要求しない。
使われ方：分解の comma の可縮性と Quillen A の条件の接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.homComponents`。

```lean
universe v

def homComponents (Z : SSet.{v}) : SSet.{v}ᵒᵖ ⥤ Type v
```

### [AnodyneFamilyHomotopy.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/FrameHom/AnodyneFamilyHomotopy.lean)

OE03、59原行。配置：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.AnodyneFamilyHomotopy`。

# anodyne 局所化の全族の等式から実ホモトピーと全区間族の射を回収する

概要：Kan 標的への全写像の局所化内の等式を、同じ全パラメータの実ホモトピーへ反映する。
方針：Kan 標的の写像空間の全連結成分を反変関手として局所化の普遍性に通す。
規約：各点の π₀ だけで代用せず、始域の Kan 性を仮定しない。
使われ方：native roof の pinched 族と保存済み基準射の全区間三角形の比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.FrameHom.map_eq_of_anodyneQ_eq`。

```lean
universe u v w

lemma map_eq_of_anodyneQ_eq {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) {A B : SSet.{u}} (f g : A ⟶ B)
    (h : AnodyneHomotopy.anodyneQ.map f = AnodyneHomotopy.anodyneQ.map g) :
    L.map f = L.map g
```

### [ComparisonEnrichedFunctors.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ComparisonEnrichedFunctors.lean)

OE04、43原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ComparisonEnrichedFunctors`。

# 元の自由 hammock 対角の左右比較の実豊穣関手

概要：同じ両比較射を単位・合成を保つ豊穣関手へ束ねる。
方針：元の対角の空語の単位と全合成の正方形を使う。
規約：各 Hom の写像は既存の左右比較射そのもの。
使われ方：同じ Ex∞ を通す実 coherent nerve の比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockAugmentationEnriched`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def freeHammockAugmentationEnriched :
    EnrichedFunctor SSet.{u} (FreeHammockObjects C) (HammockObjects C)
```

### [ComparisonEnrichment.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ComparisonEnrichment.lean)

OE04、70原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ComparisonEnrichment`。

# 元の自由 hammock 対角と hammock の実単体的豊穣圏

概要：元の対角の空語の単位と連結合成を全公理のある豊穣圏へ束ねる。
方針：各次数の実点の単位・結合則を使用する。
規約：元の圏の通常の Category instance を変更しない。
使われ方：元の左右比較を実際の豊穣関手にする。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.HammockObjects`。

```lean
universe u

def HammockObjects (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) : Type u
```

### [ComponentCategory.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ComponentCategory.lean)

OE04、105原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ComponentCategory`。

# 単体的局所化の連結成分の圏

概要：Dwyer–Kan の実際の Hom の π₀ を射とする圏を構成する。
方針：辺の合成で元の合成を二重商へ降ろし、全法則を元の零単体で照合する。
規約：元の Hom の全単体は保持し、π₀ の圏は比較のために別に構成する。
使われ方：普通の局所化と DK Hom の π₀ の同値の証明。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationHomEdgeComposition`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def localizationHomEdgeComposition {X Y Z : C.category}
    {f f' : (localizationHom C X Y) _⦋0⦌} {g g' : (localizationHom C Y Z) _⦋0⦌}
    (e : (localizationHom C X Y).Edge f f') (e' : (localizationHom C Y Z).Edge g g') :
    (localizationHom C X Z).Edge (f ≫ g) (f' ≫ g')
```

### [ComponentsEquivalence.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ComponentsEquivalence.lean)

OE04、127原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ComponentsEquivalence`。

# DK の連結成分の圏と普通の局所化の同値

概要：Dwyer–Kan の実際の Hom の π₀ と普通の局所化の Hom を同じ augmentation で比較する。
方針：構成的な lift の一意性と零次の全射の連結成分関手で両逆則を証明する。
規約：高次の Hom の弱同値や ∞ 局所化の普遍性とは区別する。
使われ方：既存 Map^h の π₀ 同定との元の射に関する正規化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationZeroHom_augmentation`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

lemma localizationZeroHom_augmentation {X Y : C.category}
    (f : C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj X) ⟶
      C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj Y)) :
    (localizationHomAugmentation C X Y).app (op ⦋0⦌) (localizationZeroHom C f) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences)).map f
```

### [ComponentsLocalizationLift.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ComponentsLocalizationLift.lean)

OE04、90原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ComponentsLocalizationLift`。

# 普通の局所化から DK の連結成分の圏への持ち上げ

概要：元の指定弱同値を反転する同じ生成関手を普通の局所化へ延長する。
方針：零次の局所化の可逆性を連結成分へ送り、構成的な lift を使う。
規約：元の局所化と元の生成射の類を保持する。
使われ方：DK Hom の π₀ と普通の局所化 Hom の比較の逆関手。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsQ_inverts`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

lemma localizationComponentsQ_inverts :
    C.weakEquivalences.IsInvertedBy (localizationComponentsQ C)
```

### [DKHammockCoefficientComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/DKHammockCoefficientComparison.lean)

OE04、61原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.DKHammockCoefficientComparison`。

# DK Hom と hammock の比較同型の係数自然性

概要：元の左右弱比較の同じ span は全相対関手に自然な高次比較を与える。
方針：左右の可換式を anodyne 局所化へ送り、元の右射を消去する。
規約：元の全単体を保ち、両端点の高次自然性はここで仮定しない。
使われ方：実 DK Hom と既存 Map^h の全自然比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.dkHammockComparisonIso`。

```lean
universe u

def dkHammockComparisonIso (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    AnodyneHomotopy.anodyneQ.obj (localizationHom C X Y) ≅
      AnodyneHomotopy.anodyneQ.obj (Hammock.reducedSimplicialSet C.weakEquivalences X Y)
```

### [DKHammockComponentsValue.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/DKHammockComponentsValue.lean)

OE04、52原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.DKHammockComponentsValue`。

# native DK/hammock 高次比較の誘導する π₀ と元の augmentation

概要：元の高次比較を π₀ へ送り、以前の局所化 Hom 同値と一致させる。
方針：同じ左右の因子化と元の右比較の π₀ の全射性で全類を回収する。
規約：元の比較同型・全語・同じ通常の局所化を保持する。
使われ方：実 DK/Map^h 比較の以前の π₀ 同値との一致。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.dkHammockComparisonIso_components_value`。

```lean
universe u

lemma dkHammockComparisonIso_components_value (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (z : SSet.π₀ (localizationHom C X Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.toComponents
        (Zigzag.Value.reducedValue C.weakEquivalences.Q C.weakEquivalences.Q_inverts X Y)
        ((AnodyneComponents.iso (dkHammockComparisonIso C X Y)).hom z) =
      localizationHomPiZeroEquiv C X Y z
```

### [DKHammockCompositionComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/DKHammockCompositionComparison.lean)

OE04、104原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.DKHammockCompositionComparison`。

# 元の DK hammock 比較の積と合成の正方形

概要：元の左右 span とその積は anodyne 局所化内で同じ合成を回収する。
方針：元の右射とその積を反転し、証明済みの二つの合成正方形を使う。
規約：局所化関手の積保存や元の射の零単体の厳密な合成保存を仮定しない。
使われ方：元の代数射に沿う両端点の高次自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.dkHammockColimitComparisonIso`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def dkHammockColimitComparisonIso (X Y : C.category) :
    AnodyneHomotopy.anodyneQ.obj (localizationHom C X Y) ≅
      AnodyneHomotopy.anodyneQ.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y)
```

### [DKHammockEndpointNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/DKHammockEndpointNaturality.lean)

OE04、53原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.DKHammockEndpointNaturality`。

# 元の射に沿う DK hammock 比較の両端点自然性

概要：元の射の点による前後合成を anodyne 局所化内の同じ比較が保つ。
方針：共通始域の左右の正方形を送り、元の右弱比較を消去する。
規約：原圏上の生の DK Hom の厳密な双関手は仮定しない。
使われ方：既存 Map^h の高次比較の両端点自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.dkHammockColimitComparisonIso_postcompose`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

lemma dkHammockColimitComparisonIso_postcompose (X : C.category) {Y Z : C.category}
    (g : Y ⟶ Z) :
    AnodyneHomotopy.anodyneQ.map (localizationPostcompose C X g) ≫
        (dkHammockColimitComparisonIso C X Z).hom =
      (dkHammockColimitComparisonIso C X Y).hom ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences g))
```

### [DKReducedHammockEndpointNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/DKReducedHammockEndpointNaturality.lean)

OE04、54原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.DKReducedHammockEndpointNaturality`。

# 元の射に沿う既存の reduced DK 比較の自然性

概要：既存の reduced 比較は元の射による前後合成を保つ。
方針：同じ正規化との因子化へ証明済みの元の余極限の自然性を移す。
規約：既存の比較同型を変更せず、元の生成射と全単体を保持する。
使われ方：実 DK Hom と既存 Map^h の比較の両端点自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.dkHammockComparisonIso_postcompose`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

lemma dkHammockComparisonIso_postcompose (X : C.category) {Y Z : C.category} (g : Y ⟶ Z) :
    AnodyneHomotopy.anodyneQ.map (localizationPostcompose C X g) ≫
        (dkHammockComparisonIso C X Z).hom =
      (dkHammockComparisonIso C X Y).hom ≫
        AnodyneHomotopy.anodyneQ.map (reducedPostcomposeMap C.weakEquivalences X g)
```

### [EnrichedMap.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/EnrichedMap.lean)

OE04、76原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.EnrichedMap`。

# 相対関手の単体的局所化への延長

概要：Dwyer–Kan の単体的局所化に元の相対関手を豊穣関手として送る。
方針：全局所化解像の係数射と対象表示の保存を固定 Hom へ代入する。
規約：全次数の元の射・単位・合成を保持する。
使われ方：Kan 化と coherent nerve の後の ∞ 関手。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationHomMap`。

```lean
universe u

def localizationHomMap {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) (X Y : C.category) :
    localizationHom C X Y ⟶ localizationHom D (F.functor.obj X) (F.functor.obj Y)
```

### [Enrichment.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/Enrichment.lean)

OE04、85原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.Enrichment`。

# 固定対象を持つ Dwyer–Kan の単体的豊穣圏

概要：Dwyer–Kan の Hom の単体集合と次数ごとの合成を厳密な豊穣圏へ束ねる。
方針：単位則と結合則を各次数の元の局所化圏の公理で照合する。
規約：Hom の Kan 性と元の Map^h との比較は後続で証明する。
使われ方：Kan 化と coherent nerve による CAlg_R の構成。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.LocalizationObjects`。

```lean
universe u

def LocalizationObjects (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) : Type u
```

### [FreeHammockArrowAugmentation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockArrowAugmentation.lean)

OE04、54原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockArrowAugmentation`。

# 共通始域の元の射の左比較による回収

概要：元の一文字の自由射は左比較で同じ hammock の一列へ戻る。
方針：元の余単位と固定端点の相対写像の一列への作用を使う。
規約：元の射と元の両端点を保持する。
使われ方：DK と hammock の比較の元の射への整合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionArrowZero_augmentation`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}

lemma freeResolutionArrowZero_augmentation (f : X ⟶ Y) :
    eqToHom (freeResolutionObject_augmentation C (op ⦋0⦌) X).symm ≫
        ((freeResolutionAugmentationNatTrans C).app (op ⦋0⦌)).functor.map
          (freeResolutionArrowZero C f) ≫
      eqToHom (freeResolutionObject_augmentation C (op ⦋0⦌) Y) = f
```

### [FreeHammockArrowPoint.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockArrowPoint.lean)

OE04、59原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockArrowPoint`。

# 元の射の点を同じ自由 hammock 比較で回収する

概要：共通始域の零単体を単位からの点にし、元の両比較で同じ点を回収する。
方針：単位からの写像と零単体の標準同値を使う。
規約：元の DK 生成射・元の hammock 射を保持する。
使われ方：高次比較の元の射への整合と前後合成の自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.unitPointMap_comp`。

```lean
universe u

lemma unitPointMap_comp {K L : SSet.{u}} (p : K _⦋0⦌) (f : K ⟶ L) :
    (SSet.unitHomEquiv K).symm p ≫ f = (SSet.unitHomEquiv L).symm (f.app _ p)
```

### [FreeHammockArrowZero.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockArrowZero.lean)

OE04、48原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockArrowZero`。

# 元の射を自由 hammock 対角の零単体へ持ち上げる

概要：元の一文字の自由射を共通始域の同じ一列へ送る。
方針：元の自由対象の表示を移し、元の局所化評価で生成射を回収する。
規約：元の射と元の両端点を保持する。
使われ方：DK と hammock の比較の元の射への整合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionArrowZero`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}

def freeResolutionArrowZero (f : X ⟶ Y) :
    freeResolutionObject C (op ⦋0⦌) X ⟶ freeResolutionObject C (op ⦋0⦌) Y
```

### [FreeHammockAugmentation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockAugmentation.lean)

OE04、41原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockAugmentation`。

# 元の自由解像の hammock 図式から元の hammock への augmentation

概要：同じ自由相対 augmentation は、全語の図式と元の余極限の比較を与える。
方針：元の対象表示の augmentation の等式を一般の固定対象の比較へ代入する。
規約：全単体作用素に自然な実際の射を構成する。弱同値性は後続。
使われ方：DK 命題2.2の左比較の元の対角前の射。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockGraphAugmentation`。

```lean
universe u

def freeHammockGraphAugmentation (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    (freeHammockWordDiagram C X Y).flip ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram C.weakEquivalences X Y)
```

### [FreeHammockAugmentationValue.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockAugmentationValue.lean)

OE04、107原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockAugmentationValue`。

# 元の自由 hammock と DK augmentation の同じ局所化への評価

概要：左右の実比較を、元の通常の局所化への同じ評価で結ぶ。
方針：各自由次数の全語の値を比較し、共同全射性で元の対角へ移す。
規約：元の augmentation・元の対象移送・全語と全単体を保持する。
使われ方：実 DK/Map^h 高次比較の誘導する π₀ の正規化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockValue_augmentation`。

```lean
universe u

lemma freeHammockValue_augmentation (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n : SimplexCategoryᵒᵖ)
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag ((freeResolution C).obj n).weakEquivalences w
      (freeResolutionObject C n X) (freeResolutionObject C n Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value C.weakEquivalences.Q C.weakEquivalences.Q_inverts
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolutionAugmentationNatTrans C).app n)
          (freeResolutionObject_augmentation C n X)
          (freeResolutionObject_augmentation C n Y)).obj S) =
      (localizationHomAugmentation C X Y).app n
        ((freeHammockLocalizationObjects C).value n S)
```

### [FreeHammockComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockComparison.lean)

OE04、45原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockComparison`。

# 元の自由 hammock の対角から既存 DK Hom への右比較

概要：元の各自由次数の zigzag の局所化評価から DK 命題2.2の右射を構成する。
方針：全語の余極限からの自然な評価へ実際の自由対象の表示を代入し、対角を取る。
規約：既存 localizationHom の全作用素と同じ対象移送を使う。弱同値性は後続。
使われ方：元の hammock と既存 DK Hom の高次比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockHomComparison`。

```lean
universe u

def freeHammockHomComparison (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    freeHammockResolution C X Y ⟶ localizationHom C X Y ⋙ Functor.const SimplexCategoryᵒᵖ
```

### [FreeHammockComparisonWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockComparisonWeak.lean)

OE04、33原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockComparisonWeak`。

# 元の全自由次数の既存 DK Hom への右比較射の弱同値性

概要：同じ自由 hammock の各自由次数から既存 DK Hom への元の右射は弱同値。
方針：元の自由圏の局所化評価へ全自由次数を代入し、元の端点移送同型を合成する。
規約：元の freeHammockHomComparison 自身の成分を結論とする。
使われ方：DK 命題2.2の対角の右比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockHomComparison_app_isWeakHomotopyEquivalence`。

```lean
universe u

lemma freeHammockHomComparison_app_isWeakHomotopyEquivalence (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
    (X Y : C.category) (n : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((freeHammockHomComparison C X Y).app n)
```

### [FreeHammockComposition.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockComposition.lean)

OE04、105原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockComposition`。

# 元の自由 hammock の対角の合成

概要：元の全自由次数の合成を同じ対角の合成へ移す。
方針：固定対象の全図式の自然な合成と対角の積との同型を使う。
規約：元の各次数の合成を保持する。
使われ方：DK の左右比較の合成保存と両端点の高次自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockResolutionComposition`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y Z : C.category)

def freeHammockResolutionComposition :
    freeHammockResolution C X Y ⊗ freeHammockResolution C Y Z ⟶
      freeHammockResolution C X Z
```

### [FreeHammockDiagonal.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockDiagonal.lean)

OE04、48原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockDiagonal`。

# 元の自由相対解像の hammock の対角と左比較

概要：DK 命題2.2の元の対角 hammock と、元の hammock 余極限への射を構成する。
方針：元の二重単体的図式と augmentation に同じ対角関手を適用する。
規約：元の全次数・全作用素・元の左射を保持する。弱同値性は後続。
使われ方：元の DK Hom と hammock の高次比較の共通始域。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockDiagonal`。

```lean
universe u

def freeHammockDiagonal (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) : SSet.{u}
```

### [FreeHammockDiagonalComparisonWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockDiagonalComparisonWeak.lean)

OE04、31原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockDiagonalComparisonWeak`。

# 元の自由 hammock の対角から既存 DK Hom への右比較射の弱同値性

概要：DK 命題2.2の元の右比較射自身は弱ホモトピー同値となる。
方針：各自由次数の元の右比較にモデル不要の対角定理を適用する。
規約：元の対角と既存 DK Hom の同じ離散対角同型を保持する。
使われ方：元の hammock と既存 DK Hom の高次比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence`。

```lean
universe u

lemma freeHammockDiagonalComparison_isWeakHomotopyEquivalence (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
    (X Y : C.category) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeHammockDiagonalComparison C X Y)
```

### [FreeHammockDiagonalReductionWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockDiagonalReductionWeak.lean)

OE04、70原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockDiagonalReductionWeak`。

# 元の自由 hammock 対角の左比較射自身の弱同値性

概要：元の全語の比較を proper 余極限と同じ対角・余極限の交換で移す。
方針：各標準射で元の augmentation の可換式を証明し、同じ比較射を回収する。
規約：全語の filtered 性や各自由次数の通常の hammock 比較の弱同値性は仮定しない。
使われ方：DK命題2.2の実際の左右比較を完成する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockDiagonalColimitIso`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeHammockDiagonalColimitIso :
    colimit (freeHammockWordDiagram C X Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor) ≅ freeHammockDiagonal C X Y
```

### [FreeHammockDiagram.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockDiagram.lean)

OE04、37原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockDiagram`。

# 元の自由相対解像の固定対象の hammock の二重単体的図式

概要：各自由次数の元の hammock graph の余極限を、全単体作用素に沿う図式にする。
方針：元の固定対象表示を全語の二方向の図式へ代入し、語方向で余極限を取る。
規約：元の自由解像・全語・全作用素・元の余極限を保持する。
使われ方：DK 命題2.2の対角 hammock と左右の比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockWordDiagram`。

```lean
universe u

def freeHammockWordDiagram (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SimplexCategoryᵒᵖ ⥤ SSet.{u}
```

### [FreeHammockGeneratorWords.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockGeneratorWords.lean)

OE04、42原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockGeneratorWords`。

# 元の自由 hammock の全次数の非指定生成文字列

概要：各自由次数の元の全語の余極限を、同じ次数の非指定生成文字列へ評価する。
方針：元の最外層の生成圏と既存の固定対象へ、全語に不変な評価を代入する。
規約：元の各語の標準射による回収式を保持する。次数を跨ぐ不変性は要求しない。
使われ方：Dwyer–Kan 比較補題2.3の各自由次数の hammock の分解。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockGeneratorWordValue`。

```lean
universe u

def freeHammockGeneratorWordValue (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) :
    (freeHammockResolution C X Y).obj n ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj
        (List (Quiver.Total (freeResolutionGeneratorBase C n).category))
```

### [FreeHammockLocalizedObjects.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockLocalizedObjects.lean)

OE04、42原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockLocalizedObjects`。

# 自由 hammock と既存 DK Hom の対象表示の照合

概要：局所化前の自由対象の像が、既存 DK Hom の固定対象に一致することを証明する。
方針：両側の標準生成対象による表示を照合する。
規約：対象の一致と全単体作用素への自然性は証明し、追加の入力にしない。
使われ方：自由 hammock の局所化 Hom への評価への実際のデータの代入。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionObject_localized`。

```lean
universe u

lemma freeResolutionObject_localized (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    (X : C.category) :
    ((freeResolution C).obj n).weakEquivalences.Q.obj (freeResolutionObject C n X) =
      localizedFreeResolutionObject C n X
```

### [FreeHammockMap.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockMap.lean)

OE04、63原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockMap`。

# 元の自由 hammock の係数写像

概要：元の相対関手を自由 hammock の全語・全次数・対角へ移す。
方針：証明済みの選択対象の自然性を一般の固定対象写像へ代入する。
規約：元の自由解像と全語の余極限を保持する。
使われ方：DK の左右比較射の係数自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockWordMap`。

```lean
universe u
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)

def freeHammockWordMap (X Y : C.category) : freeHammockWordDiagram C X Y ⟶
    freeHammockWordDiagram D (F.functor.obj X) (F.functor.obj Y)
```

### [FreeHammockMapAugmentation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockMapAugmentation.lean)

OE04、89原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockMapAugmentation`。

# 元の自由 hammock の左比較の係数自然性

概要：元の自由解像の augmentation の正方形を全 zigzag と全語へ移す。
方針：固定端点関手の合成と元の相対関手の自然性を使う。
規約：元の左比較射と元の係数写像を保持する。
使われ方：DK の高次比較の係数自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockFixedFunctor_augmentation`。

```lean
universe u
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)

lemma freeHammockFixedFunctor_augmentation (X Y : C.category) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (n : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := w) ((freeResolutionMap F).app n)
        (freeResolutionMap_object F n X) (freeResolutionMap_object F n Y) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolutionAugmentationNatTrans D).app n)
        (freeResolutionObject_augmentation D n (F.functor.obj X))
        (freeResolutionObject_augmentation D n (F.functor.obj Y)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolutionAugmentationNatTrans C).app n)
        (freeResolutionObject_augmentation C n X) (freeResolutionObject_augmentation C n Y) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F
```

### [FreeHammockMapComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockMapComparison.lean)

OE04、96原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockMapComparison`。

# 元の自由 hammock の右比較の係数自然性

概要：元の zigzag の局所化評価と実際の DK Hom の係数写像を照合する。
方針：元の Q の自然性と全端点移送を同じ値の等式で相殺する。
規約：全語・全次数と元の右比較射を保持する。
使われ方：DK と hammock の高次比較の係数自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockValue_map`。

```lean
universe u
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)

lemma freeHammockValue_map (X Y : C.category) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n : SimplexCategoryᵒᵖ)
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag ((freeResolution C).obj n).weakEquivalences w
      (freeResolutionObject C n X) (freeResolutionObject C n Y)) :
    (freeHammockLocalizationObjects D).value n
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolutionMap F).app n)
          (freeResolutionMap_object F n X) (freeResolutionMap_object F n Y)).obj S) =
      (localizationHomMap F X Y).app n ((freeHammockLocalizationObjects C).value n S)
```

### [FreeHammockObjectMap.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockObjectMap.lean)

OE04、40原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockObjectMap`。

# 元の自由解像の選択対象の係数自然性

概要：元の自由解像の係数写像が同じ固定対象の表示を保つ。
方針：実際の augmentation の対象単射性と係数自然性を使う。
規約：元の対象表示の自然性を仮定せず証明する。
使われ方：自由 hammock の全係数写像と比較射の自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionMap_object`。

```lean
universe u

lemma freeResolutionMap_object {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) (X : C.category) :
    ((freeResolutionMap F).app n).functor.obj (freeResolutionObject C n X) =
      freeResolutionObject D n (F.functor.obj X)
```

### [FreeHammockObjects.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockObjects.lean)

OE04、65原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockObjects`。

# 自由相対解像の固定対象の表示

概要：局所化する前の元の自由相対解像で、固定対象と全作用素の対象上の等式を得る。
方針：元の augmentation の対象上の全単射性を使い、標準生成対象とも照合する。
規約：元の全単体作用素の保存を証明し、対象の同一性を仮定しない。
使われ方：自由相対解像の固定した両対象の hammock の二重単体的図式。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionObjectEquiv`。

```lean
universe u

def freeResolutionObjectEquiv (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    ((freeResolution C).obj n).category ≃ C.category
```

### [FreeHammockPostcompose.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockPostcompose.lean)

OE04、66原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockPostcompose`。

# 元の射による自由 hammock の後合成と両比較の自然性

概要：元の射の同じ持ち上げ点を合成へ代入する。
方針：合成保存と元の点の回収の二つの厳密な等式を使う。
規約：元の射・全単体・元の両比較を保持する。
使われ方：DK と hammock の高次比較の終域変数の自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockPostcompose`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category) {Y Z : C.category}

def freeHammockPostcompose (g : Y ⟶ Z) :
    freeHammockDiagonal C X Y ⟶ freeHammockDiagonal C X Z
```

### [FreeHammockPrecompose.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockPrecompose.lean)

OE04、65原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockPrecompose`。

# 元の射による自由 hammock の前合成と両比較の自然性

概要：元の射の同じ持ち上げ点を合成の左へ代入する。
方針：合成保存と元の点の回収の二つの厳密な等式を使う。
規約：元の射・全単体・元の両比較を保持する。
使われ方：DK と hammock の高次比較の始域変数の自然性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockPrecompose`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category} (Z : C.category)

def freeHammockPrecompose (f : X ⟶ Y) :
    freeHammockDiagonal C Y Z ⟶ freeHammockDiagonal C X Z
```

### [FreeHammockUnit.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeHammockUnit.lean)

OE04、93原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockUnit`。

# 元の自由 hammock 対角の空語の単位

概要：元の各自由次数の実単位点を同じ対角の単体写像へ束ねる。
方針：元の相対作用素の固定端点の単位保存と内側の全作用素の自然性を使う。
規約：原圏の恒等射の自由な生成射へ置き換えない。
使われ方：左右比較を同じ単位を保つ豊穣関手にする。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeHammockResolution_map`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category)

lemma freeHammockResolution_map {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    (freeHammockResolution C X X).map θ =
      Relative.fixedColimitMap ((freeResolution C).map θ)
        (freeResolutionObject_naturality C θ X) (freeResolutionObject_naturality C θ X)
```

### [FreeResolution.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolution.lean)

OE04、83原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolution`。

# Dwyer–Kan の自由相対圏の全単体的解像

概要：Dwyer–Kan の自由相対圏 comonad を通常の単体圏上の解像へ代入する。
方針：既存の汎用 comonad 解像の六つの関係式と単体圏表示同値を使う。
規約：全単体作用素は実際の相対関手で、各次数の指定矢を保つ。
使われ方：各次数の普通の局所化から単体的局所化を構成する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeComonadPower_eq`。

```lean
universe u

lemma freeComonadPower_eq (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : ℕ) :
    ComonadResolutionOperators.power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C n = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freePower n).obj C
```

### [FreeResolutionCanonicalMarkedHom.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionCanonicalMarkedHom.lean)

OE04、62原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionCanonicalMarkedHom`。

# 元の選択対象による指定 Hom の弱比較

概要：元の自由解像の固定 Hom augmentation を一列の比較へ接続する。
方針：同じ対象の表示を移す同型と元の augmentation の可換式を使う。
規約：元の比較射自身の弱同値性を証明する。
使われ方：DK5.7の全語の帰納の基底。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionCanonicalMarkedHom`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeResolutionCanonicalMarkedHom : SSet.{u}
```

### [FreeResolutionFunctoriality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionFunctoriality.lean)

OE04、52原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionFunctoriality`。

# 自由相対圏の全解像の係数関手性

概要：Dwyer–Kan の自由解像に相対関手を全次数で送る。
方針：一般の comonad 解像の係数自然性へ同じ自由 comonad を代入する。
規約：元の解像・全作用素・augmentation を保持する。
使われ方：単体的局所化の係数関手の構成。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionMap`。

```lean
universe u

def freeResolutionMap {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    freeResolution C ⟶ freeResolution D
```

### [FreeResolutionGeneratorBlocks.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionGeneratorBlocks.lean)

OE04、52原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionGeneratorBlocks`。

# 元の自由解像の全次数の交互標準形

概要：元の各自由次数の射と圏を、指定・非指定の生成矢の交互標準形へ同定する。
方針：元の最外層の生成圏に正規化の全単射と圏同値を代入する。
規約：元の全対象・射列・合成・恒等文字を保持する。hammock の弱比較は後続。
使われ方：元の自由解像の各 hammock の行の分解。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionBlockEquiv`。

```lean
universe u

def freeResolutionBlockEquiv (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    (X Y : ((freeResolution C).obj n).category) :
    (X ⟶ Y) ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal (freeResolutionGeneratorBase C n).weakEquivalences X Y
```

### [FreeResolutionGeneratorHom.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionGeneratorHom.lean)

OE04、61原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionGeneratorHom`。

# 元の標準生成対象の表示による自由解像の Hom

概要：元の自由解像の同じ Hom を標準生成対象の表示で扱う。
方針：証明済みの元の対象表示の等式から全作用素での自然性を回収する。
規約：元の全作用素を変更せず、追加退化の計算だけに標準表示を使う。
使われ方：元の Hom augmentation の収縮。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionHomObject`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def freeResolutionHomObject (n : SimplexCategoryᵒᵖ) (X : C.category) :
    ((freeResolution C).obj n).category
```

### [FreeResolutionGeneratorHomOperators.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionGeneratorHomOperators.lean)

OE04、50原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionGeneratorHomOperators`。

# 元の標準 Hom の全生成作用素の回収

概要：標準 Hom の面・退化・augmentation を元の余モナドの同じ射作用へ戻す。
方針：元の固定対象の端点移送だけを異種等式で消去する。
規約：元の作用素と元の各射を保持する。
使われ方：元の一文字の列による追加退化の恒等式。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.generatorHom_face_heq`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}

lemma generatorHom_face_heq (n : ℕ) (i : Fin (n + 2))
    (f : (freeResolutionGeneratorHom C X Y) _⦋n + 1⦌) :
    HEq ((freeResolutionGeneratorHom C X Y).δ i f)
      ((face _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1) i).functor.map f)
```

### [FreeResolutionGeneratorPartition.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionGeneratorPartition.lean)

OE04、55原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionGeneratorPartition`。

# 元の自由解像の全次数の指定生成矢と自由積の普遍性

概要：指定生成矢の自由圏と二つの生成部分の普遍性を、元の自由解像の各次数へ代入する。
方針：最外層の自由相対圏の元の生成圏と W.paths をそのまま使う。
規約：零次と全単体次数を含み、恒等文字も保持する。高次比較の弱同値性は後続。
使われ方：Dwyer–Kan 比較補題2.3の各自由次数への適用。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionGeneratorBase`。

```lean
universe u u' v'

def freeResolutionGeneratorBase (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}
```

### [FreeResolutionHomContraction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionHomContraction.lean)

OE04、64原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionHomContraction`。

# 元の自由解消 Hom augmentation の収縮

概要：元の圏の Hom へ向かう自由解消 augmentation は弱ホモトピー同値。
方針：一文字の追加退化の全恒等式から実際の区間収縮を構成する。
規約：単体集合のモデル構造と標的の Kan 性は仮定しない。
使われ方：DK ホモトピー補題2.4の底の Hom の入力。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionGeneratorHomAugmented`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeResolutionGeneratorHomAugmented : SimplicialObject.Augmented (Type u)
```

### [FreeResolutionHomExtra.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionHomExtra.lean)

OE04、45原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionHomExtra`。

# 元の自由 Hom の一文字の列による追加退化

概要：元の射を一文字の列へ送り、同じ Hom の次数を一つ上げる。
方針：標準生成対象の再帰表示で元の Quiver.Hom.toPath をそのまま使う。
規約：恒等射も一文字として保持し、圏の関手だとは仮定しない。
使われ方：元の Hom augmentation の実際の収縮。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.generatorHomSection`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}

def generatorHomSection (f : X ⟶ Y) : (freeResolutionGeneratorHom C X Y) _⦋0⦌
```

### [FreeResolutionHomExtraNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionHomExtraNaturality.lean)

OE04、108原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionHomExtraNaturality`。

# 一文字の追加退化と元の全作用素の整合性

概要：追加退化と全ての正の面・退化の交換則を証明する。
方針：自由関手の一文字の列への作用と元の端点移送を照合する。
規約：元の作用素・augmentation と同じ射を保持する。
使われ方：元の自由 Hom の追加退化と収縮。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.singlePath_conjugate_heq`。

```lean
universe u

lemma singlePath_conjugate_heq {V : Type u} [Category.{u} V] {A A' B B' : V}
    (hA : A' = A) (hB : B = B') (f : A ⟶ B) :
    HEq (Quiver.Hom.toPath (V := V) (eqToHom hA ≫ f ≫ eqToHom hB))
      (Quiver.Hom.toPath (V := V) f)
```

### [FreeResolutionHomRepresentation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionHomRepresentation.lean)

OE04、60原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionHomRepresentation`。

# 元の選択対象による Hom への収縮の移送

概要：標準生成対象による追加退化の結論を元の固定 Hom augmentation 自身へ戻す。
方針：同じ二つの対象表示の等式を使う単体同型と augmentation の可換式を構成する。
規約：元の augmentation を別の弱同値で置き換えない。
使われ方：DK ホモトピー補題2.4に使う元の Hom の弱比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionHomRepresentationIso`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeResolutionHomRepresentationIso :
    freeResolutionHom C X Y ≅ freeResolutionGeneratorHom C X Y
```

### [FreeResolutionMarkedHom.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionMarkedHom.lean)

OE04、58原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionMarkedHom`。

# 元の指定射からなる自由解消 Hom

概要：自由解消の指定射の Hom と元の指定射への augmentation を構成する。
方針：元の指定射の述語を全単体作用素で保つ部分単体集合として扱う。
規約：指定射は元の相対圏の同じ射の類であり、飽和性を要求しない。
使われ方：DK ホモトピー補題2.4の指定射の Hom の入力。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionMarkedHomSubcomplex`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeResolutionMarkedHomSubcomplex : (freeResolutionGeneratorHom C X Y).Subcomplex
```

### [FreeResolutionMarkedHomContraction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionMarkedHomContraction.lean)

OE04、66原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionMarkedHomContraction`。

# 元の指定 Hom augmentation の収縮

概要：指定射の自由解消から元の指定 Hom への augmentation は弱ホモトピー同値。
方針：元の一文字の追加退化を指定射の部分単体集合へ制限する。
規約：元の全単体作用素と指定射の類を保持する。
使われ方：DK ホモトピー補題2.4の二つ目の入力。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionMarkedHomAugmented`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeResolutionMarkedHomAugmented : SimplicialObject.Augmented (Type u)
```

### [FreeResolutionNativeMarkedHom.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionNativeMarkedHom.lean)

OE04、67原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionNativeMarkedHom`。

# 元の指定部分圏の固定 Hom と augmentation

概要：元の指定部分圏の単体的図式を作り、固定 Hom と元の指定 Hom への射を構成する。
方針：元の標準生成対象の表示と対象保存の等式を wide 部分圏へ送る。
規約：部分圏の Hom は Mathlib の元の Hom 構造体であり、代替の射集合ではない。
使われ方：DK2.4の指定部分圏についての実際の Hom 弱比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionMarkedDiagram`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def freeResolutionMarkedDiagram : SimplicialObject Cat.{u, u}
```

### [FreeResolutionNativeMarkedHomWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionNativeMarkedHomWeak.lean)

OE04、92原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionNativeMarkedHomWeak`。

# 元の指定部分圏の Hom augmentation 自身の弱同値性

概要：wide 部分圏の Hom と指定射の部分単体集合を同型で照合し、同じ射の弱比較を得る。
方針：元の射と指定性を保つ往復と、augmentation の可換式を証明する。
規約：元の部分圏の Hom 構造体・全作用素・augmentation を保持する。
使われ方：DK2.4の元の指定部分圏の入力。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.marked_eqToHom_hom`。

```lean
universe u

lemma marked_eqToHom_hom {C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}}
    {X Y : WideSubcategory C.weakEquivalences} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg WideSubcategory.obj h)
```

### [FreeResolutionUnderlyingHom.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeResolutionUnderlyingHom.lean)

OE04、60原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionUnderlyingHom`。

# 元の自由相対解像の底の固定 Hom と augmentation

概要：局所化前の元の自由解像の固定 Hom と元の圏の Hom への全次数の評価を作る。
方針：元の対象表示と元の augmentation を固定 Hom の係数自然変換へ代入する。
規約：元の全作用素と元の対象移送を保持する。
使われ方：DK ホモトピー補題2.4の底の圏の弱比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionUnderlyingDiagram`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def freeResolutionUnderlyingDiagram : SimplicialObject Cat.{u, u}
```

### [FreeWordDiagonalBackwardWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeWordDiagonalBackwardWeak.lean)

OE04、51原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeWordDiagonalBackwardWeak`。

# 元の自由解像の backward 一列の左比較の弱同値性

概要：元の backward 一列の augmentation 自身が弱同値である。
方針：実際の指定部分圏の Hom augmentation と端点表示の同型を使う。
規約：元の全列・全縦射と元の比較射を保持する。
使われ方：DK5.7の全語の帰納の基底。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeWordDiagonalAugmentation_backward_square`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

lemma freeWordDiagonalAugmentation_backward_square :
    (freeWordDiagonalAugmentation C X Y).app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) ≫
      BackwardZigzag.graphValue =
    singleBackwardDiagonalEvaluation (freeResolution C) (freeResolutionObject C)
      (fun θ X => freeResolutionObject_naturality C θ X) X Y ≫
        freeResolutionCanonicalMarkedHomAugmentation C Y X
```

### [FreeWordDiagonalEmptyWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeWordDiagonalEmptyWeak.lean)

OE04、29原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeWordDiagonalEmptyWeak`。

# 元の自由解像の空語の左比較射の弱同値性

概要：元の固定端点と全単体作用素を保持する。
方針：一頂点の一意性と実際の相対関手・対角比較を使う。
規約：通常の hammock augmentation の弱同値性を仮定しない。
使われ方：DK5.7の全語の帰納基底。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeWordDiagonalAugmentation_empty_weak`。

```lean
universe u

lemma freeWordDiagonalAugmentation_empty_weak (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((freeWordDiagonalAugmentation C X Y).app _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty)
```

### [FreeWordDiagonalForwardWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeWordDiagonalForwardWeak.lean)

OE04、49原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeWordDiagonalForwardWeak`。

# 元の自由解像の forward 一列の左比較の弱同値性

概要：元の自由解像の固定 Hom augmentation を一列の比較へ接続する。
方針：同じ対象の表示を移す同型と元の augmentation の可換式を使う。
規約：元の比較射自身の弱同値性を証明する。
使われ方：DK5.7の全語の帰納の基底。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeWordDiagonalAugmentation`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeWordDiagonalAugmentation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordDiagonalDiagram (freeResolution C) C (freeResolutionObject C)
      (fun θ X => freeResolutionObject_naturality C θ X) X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram C.weakEquivalences X Y
```

### [FreeWordDiagonalWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/FreeWordDiagonalWeak.lean)

OE04、67原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeWordDiagonalWeak`。

# 元の全語の自由対角 augmentation の弱同値性

概要：任意の向き付き語で元の左比較射自身が弱同値となる。
方針：空語・一列の基底と、元の四つの先頭方向の帰納段階を長さ帰納で結ぶ。
規約：元の全対象・全語・全単体作用素と同じ augmentation を保持する。
使われ方：DK5.7の元の全語の余極限への移送。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeWordDiagonalAugmentation_weak`。

```lean
universe u

lemma freeWordDiagonalAugmentation_weak (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((freeWordDiagonalAugmentation C X Y).app w)
```

### [HammockInvertsEdges.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/HammockInvertsEdges.lean)

OE04、39原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockInvertsEdges`。

# 元の W の辺を反転する実 hammock nerve 関手

概要：元の通常圏の指定射が表す辺の集合と、その反転証明を供給する。
方針：元の射からの coherent な辺との一致と既存の往復ホモトピーを使う。
規約：指定辺集合は元の W だけから定義し、局所化の普遍性とは分ける。
使われ方：全反転関手 ∞ 圏への実際の前合成写像。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.weakNerveEdges`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def weakNerveEdges : Set ((nerve C.category) _⦋1⦌)
```

### [HammockSourceFunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/HammockSourceFunctor.lean)

OE04、47原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockSourceFunctor`。

# 元の通常圏から実 hammock 豊穣圏への関手

概要：元の任意の射を同じ一定単体の hammock 射へ送り、厳密な通常関手を得る。
方針：同じ arrowMap の恒等・合成保存と ForgetEnrichment の元の同値を使う。
規約：元の対象と元の通常の Category instance を保持する。
使われ方：元の通常圏から Kan hammock nerve への局所化関手。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.HammockCategory`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

abbrev HammockCategory
```

### [Hom.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/Hom.lean)

OE04、65原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.Hom`。

# 固定対象の Dwyer–Kan Hom の単体集合

概要：Dwyer–Kan の次数ごとの局所化の射を固定した両対象の単体集合へ束ねる。
方針：元の対象表示と全作用素との自然性を固定 Hom の一般構成へ代入する。
規約：合成と単位は各次数の局所化圏の同じもの。
使われ方：厳密な単体的豊穣圏の構成と Hom の Kan 化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationHom`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def localizationHom (X Y : C.category) : SSet.{u}
```

### [HomAugmentation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/HomAugmentation.lean)

OE04、117原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HomAugmentation`。

# 単体的局所化の Hom から普通の局所化 Hom への比較

概要：Dwyer–Kan の全解像の augmentation を固定 Hom の比較へ束ねる。
方針：同じ対象表示と augmentation を固定 Hom の係数自然性へ代入する。
規約：比較先だけを定値にし、元の Hom の全単体を保持する。
使われ方：DK と元の Map^h の比較の零次の正規化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionAugmentation_object`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

lemma localizedFreeResolutionAugmentation_object (n : SimplexCategoryᵒᵖ) (X : C.category) :
    ((localizedFreeResolutionAugmentation C).app n).toFunctor.obj
        (localizedFreeResolutionObject C n X) = C.weakEquivalences.Q.obj X
```

### [HomMapLaws.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/HomMapLaws.lean)

OE04、103原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HomMapLaws`。

# 単体的局所化の係数射の恒等・合成則

概要：Dwyer–Kan の固定 Hom と豊穣係数射の厳密な関手則を証明する。
方針：全解像の係数関手の恒等・合成を各 Hom に移して対象移送を相殺する。
規約：元の係数射と同じ対象表示を保持する。
使われ方：Kan 化と coherent nerve での係数関手性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationHomMap_id`。

```lean
universe u

lemma localizationHomMap_id (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    localizationHomMap (𝟙 C) X Y = 𝟙 (localizationHom C X Y)
```

### [KanComparisonEnrichedFunctors.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanComparisonEnrichedFunctors.lean)

OE04、45原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanComparisonEnrichedFunctors`。

# 元の自由 hammock の左右比較の実 Kan 豊穣関手

概要：元の比較関手を同じ Ex∞ で Kan 化する。
方針：構成済みの monoidal 移送を両比較へ適用する。
規約：元の Hom 射への Ex∞ の像を全 Hom で回収する。
使われ方：元の coherent nerve の比較と ∞ 局所化関手の構成。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.KanHammockObjects`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

abbrev KanHammockObjects
```

### [KanComparisonNerves.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanComparisonNerves.lean)

OE04、95原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanComparisonNerves`。

# 元の Kan 自由 hammock の左右比較の実 coherent nerve 同値

概要：同じ豊穣関手を元の coherent nerve 間の実同値へ移す。
方針：全 Kan Hom 上の同値から充満忠実性、同じ対象写像から本質的全射性を得る。
規約：元の localizationNerve と両比較を保持する。局所化の普遍性は別に証明する。
使われ方：元の通常圏から実 DK nerve への局所化関手の構成。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.KanHammockCategory`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

abbrev KanHammockCategory
```

### [KanComparisonWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanComparisonWeak.lean)

OE04、47原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanComparisonWeak`。

# 元の Kan 豊穣比較の各 Hom の同値性

概要：元の弱比較を同じ Ex∞ で送り、実 Kan Hom 間の圏同値を得る。
方針：構成済みの両弱比較・Ex∞ の弱同値保存・Kan Whitehead を使用する。
規約：元の比較の Hom 射そのものを保持する。
使われ方：元の coherent nerve の実比較の充満忠実性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanFreeHammockAugmentationEnriched_map_weak`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : KanFreeHammockObjects C)

lemma kanFreeHammockAugmentationEnriched_map_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((kanFreeHammockAugmentationEnriched C).map X Y)
```

### [KanComponents.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanComponents.lean)

OE04、66原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanComponents`。

# Kan 化した DK Hom の連結成分と普通の局所化

概要：同じ Ex∞ の単位を通して実際の Kan Hom の π₀ を普通の局所化と同定する。
方針：元の単位の anodyne 性から π₀ の全単射を取り、元の augmentation の同値と合成する。
規約：単体集合のモデル構造や元の Hom の Kan 性を入力しない。
使われ方：CAlg_R の構成に使う Kan Hom と元の Map^h の零次比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationHomKanUnitPiZeroEquiv`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def localizationHomKanUnitPiZeroEquiv (X Y : C.category) :
    SSet.π₀ (localizationHom C X Y) ≃ SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (localizationHom C X Y))
```

### [KanEnrichedMap.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanEnrichedMap.lean)

OE04、72原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanEnrichedMap`。

# 単体的局所化の係数射の Kan 化

概要：Dwyer–Kan の豊穣係数関手を同じ有限積保存 Ex∞ で送る。
方針：元の Hom 作用を Ex∞ で送り、tensorator の自然性で合成則を照合する。
規約：対象と元の係数関手を保持し、単体集合モデルを入力しない。
使われ方：coherent nerve の間の係数 ∞ 関手。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationEnrichedMap`。

```lean
universe u

def kanLocalizationEnrichedMap {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    EnrichedFunctor SSet.{u} (KanLocalizationObjects C) (KanLocalizationObjects D)
```

### [KanEnrichment.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanEnrichment.lean)

OE04、106原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanEnrichment`。

# Ex∞ による単体的局所化の Hom の Kan 化

概要：Dwyer–Kan の厳密な単体的局所化の Hom を同じ有限積保存 Ex∞ で Kan 化する。
方針：実際の monoidal 関手で豊穣構造を移し、元の単位の monoidal 性を使う。
規約：単体集合のモデル構造を入力せず、元の豊穣合成を保持する。
使われ方：局所 Kan な単体的圏の coherent nerve。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.KanLocalizationObjects`。

```lean
universe u

abbrev KanLocalizationObjects (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
```

### [KanHammockArrowNormalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanHammockArrowNormalization.lean)

OE04、43原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockArrowNormalization`。

概要：元の hammock 射の pinched 零単体は元の局所化辺そのもの。
方針：原本の coherent 零単体公式へ元の豊穣源関手の射を代入する。
規約：原本を読み取り専用で再利用し、元の射と端点を変更しない。
使われ方：全 frame 比較の零単体と指定二胞体の共役の接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanHammockHomPinchedMap_arrow_zero`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}

lemma kanHammockHomPinchedMap_arrow_zero (f : X ⟶ Y) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫
      kanHammockHomPinchedMap C X Y).app (op ⦋0⦌) PUnit.unit)).val =
      (hammockLocalizationNerveMap C).app (op ⦋1⦌) (ComposableArrows.mk₁ f)
```

### [KanHammockHomCoherent.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanHammockHomCoherent.lean)

OE04、80原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockHomCoherent`。

概要：元の strict Kan hammock Hom 図式を同じ豊穣 Hom 関手の coherent 実現へ同定する。
方針：元の Ex∞ 単位と lax monoidal 後合成の等式を全自然性に使う。
規約：点ごとの Hom 同値を使わず、全図式の厳密な等式を構成する。
使われ方：Yoneda 側の全比較を S (6) の終端へ代入する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanHammock_sHomWhiskerLeft`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category)

lemma kanHammock_sHomWhiskerLeft {Y Z : C.category} (f : Y ⟶ Z) :
    eHomWhiskerLeft SSet ((kanHammockSourceFunctor C).obj X)
      ((kanHammockSourceFunctor C).map f) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f))
```

### [KanHammockHomInfinity.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanHammockHomInfinity.lean)

OE04、35原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockHomInfinity`。

概要：元の Kan hammock Hom の全実現を正本の共変 Hom 全図式へ送る。
方針：原本 Yoneda の一つの全比較に同じ局所化頂点を代入する。
規約：点ごとの Hom 同値や新たな存在仮定で置き換えない。
使われ方：right frame の終端から指定局所化への全標的比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanHammockHomInfinityIso`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category)

def kanHammockHomInfinityIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (kanHammockHomCoherent C X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant ((hammockLocalizationNerveMap C).app
        (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)))
```

### [KanHammockHomPinched.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanHammockHomPinched.lean)

OE04、57原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockHomPinched`。

# 元の Kan hammock Hom から同じ局所化頂点の pinched Hom への弱比較

概要：元の Ex∞ hammock Hom を、同じ qX・qY の実写像空間へ送る。
方針：Hom の自明な宇宙持ち上げを全単体で往復し、元の coherent 比較を使う。
規約：元の enriched Hom・元の Ex∞・実際の q の頂点を保持する。
使われ方：元の source frame の弱な基準射を実屋根の Hom 比較へ接続する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanHammockHomLiftIso`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def kanHammockHomLiftIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y) ≅
    SSet.uliftFunctor.{u, u}.obj (SimplicialCategory.sHom
      ((kanHammockSourceFunctor C).obj X) ((kanHammockSourceFunctor C).obj Y))
```

### [KanHammockHomPinchedValue.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanHammockHomPinchedValue.lean)

OE04、36原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockHomPinchedValue`。

# 同じ Kan hammock Hom 比較の元の coherent 単体の値

概要：元の端点輸送を通した pinched 比較は元の coherent Hom 単体をそのまま保つ。
方針：元の全単体の値に関する端点輸送の式を使う。
規約：元の Hom・元の局所化頂点・同じ単体を保持する。
使われ方：native roof prism の実一端。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanHammockHomPinchedMap_app_val`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

lemma kanHammockHomPinchedMap_app_val {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y)) _⦋n⦌) :
    ((kanHammockHomPinchedMap C X Y).app (Opposite.op ⦋n⦌) s).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (show (SimplicialCategory.sHom
        ((kanHammockSourceFunctor C).obj X) ((kanHammockSourceFunctor C).obj Y)) _⦋n⦌ from s)
```

### [KanHammockPinchedSimplexValue.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanHammockPinchedSimplexValue.lean)

OE04、49原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockPinchedSimplexValue`。

概要：元のKan hammockのpinched比較の同じ全単体の値に名前を付ける。
方針：既存のcoherent単体を一般の相対圏で定義し、元の評価式をそのまま記録する。
規約：elaborationの分割のみ。元のHom単体・局所化頂点・値を変更しない。
使われ方：複雑なBEの係数への特殊化でも同じ全単体の式を検査する。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanHammockPinchedSimplexValue`。

```lean
universe u
variable (C : RelativeCategory.{u}) (X Y : C.category)

def kanHammockPinchedSimplexValue {n : ℕ}
    (s : (exInfinity.obj (colimitGraph C.weakEquivalences X Y)) _⦋n⦌) :
    (kanHammockNerve C) _⦋n + 1⦌
```

### [KanHammockPrecompose.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanHammockPrecompose.lean)

OE04、57原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockPrecompose`。

# 元の前合成の Kan 化と同じ豊穣合成の一致

概要：元の通常射による前合成の Ex∞ 像を同じ Kan hammock の豊穣合成へ戻す。
方針：有限積保存・単位の monoidal 性・元の点の自然性を使う。
規約：元の通常射・同じ Ex∞・同じ豊穣 Hom と合成を保持する。
使われ方：native roof prism の 00 と 01 の豊穣合成条件。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanHammockSource_precompose`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category} (f : X ⟶ Y) (Z : C.category)

lemma kanHammockSource_precompose :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f) Z) =
    lift (toUnit _ ≫ ForgetEnrichment.homTo SSet.{u} ((kanHammockSourceFunctor C).map f))
      (𝟙 _) ≫ eComp SSet ((kanHammockSourceFunctor C).obj X)
        ((kanHammockSourceFunctor C).obj Y) ((kanHammockSourceFunctor C).obj Z)
```

### [KanHammockSourceFunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanHammockSourceFunctor.lean)

OE04、60原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockSourceFunctor`。

# 元の通常圏から実 Kan hammock nerve への関手

概要：元の通常関手を同じ Ex∞ 単位と既存の nerveToCoherent で送る。
方針：通常関手の全単体への nerve と元の単体的圏の比較を合成する。
規約：元の通常圏・同じ射・同じ頂点を保持する。
使われ方：元の実 DK nerve への局所化関手の供給。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanHammockSourceFunctor`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def kanHammockSourceFunctor : C.category ⥤ KanHammockCategory C
```

### [KanHammockWeakArrows.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanHammockWeakArrows.lean)

OE04、110原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockWeakArrows`。

# 元の指定射の Kan hammock nerve 内での反転

概要：元の backward hammock を逆辺とし、既存の二つの往復ホモトピーを送る。
方針：同じ Ex∞ 単位への後合成と coherent Hom の連結成分比較を使う。
規約：元の W の射と実際の通常関手の像を保持する。
使われ方：元の通常圏からの ∞ 局所化関手の反転条件。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanHammockBackward`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category} (f : X ⟶ Y)
  (hf : C.weakEquivalences f)

def kanHammockBackward : (kanHammockSourceFunctor C).obj Y ⟶
    (kanHammockSourceFunctor C).obj X
```

### [KanHammockYonedaNormalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanHammockYonedaNormalization.lean)

OE04、69原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockYonedaNormalization`。

概要：全 Yoneda 比較に使う同じ恒等係数を元の hammock 零単体へ回収する。
方針：原本の全 coslice 比較の恒等点公式と同じ源関手の恒等射保存を合成する。
規約：原本の全比較と異なる恒等点を選ばない。
使われ方：全図式 Yoneda 比較と元の局所化辺の零単体照合を結ぶ。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanHammockYonedaIdentity_zero`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category)

lemma kanHammockYonedaIdentity_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.representableHomIdentity
      (D := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift (KanHammockCategory C))
      (ULift.up ((kanHammockSourceFunctor C).obj X)) =
    SSet.unitHomEquiv _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences (𝟙 X) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X X))
```

### [KanMapLaws.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/KanMapLaws.lean)

OE04、70原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanMapLaws`。

# Kan 化した単体的局所化の係数関手則

概要：同じ Ex∞ による Kan 化が係数射の恒等・合成を保つことを証明する。
方針：元の固定 Hom の係数関手則を Ex∞ の関手則で送る。
規約：対象と元の Hom 作用を変更しない。
使われ方：coherent nerve の全係数関手性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationEnrichedMap_id`。

```lean
universe u

lemma kanLocalizationEnrichedMap_id (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    kanLocalizationEnrichedMap (𝟙 C) = EnrichedFunctor.id SSet (KanLocalizationObjects C)
```

### [LocalizationNervePrecomposition.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/LocalizationNervePrecomposition.lean)

OE04、37原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationNervePrecomposition`。

# 元の反転関手圏への全前合成と既存 nerve の比較

概要：既存 localizationNerve への写像の普遍性を実 hammock 側へ還元する。
方針：同じ指定辺集合への前合成を、元の Kan nerve 同値の前合成で厳密に因子化する。
規約：全 quasicategory 標的と全部分関手圏を扱う。普遍性自体は未供給。
使われ方：実 hammock の ∞ 局所化を既存 CAlg_R へ移す最終工程。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationNerveSourceMap_precomposition`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

lemma localizationNerveSourceMap_precomposition (E : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (localizationNerveSourceMap C) (weakNerveEdges C)
        (localizationNerveSourceMap_inverts C) E =
      (pre (kanHammockLocalizationEquivalence C).hom).app E ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (hammockLocalizationNerveMap C) (weakNerveEdges C)
          (hammockLocalizationNerveMap_inverts C) E
```

### [LocalizationNerveSource.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/LocalizationNerveSource.lean)

OE04、85原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationNerveSource`。

# 元の通常圏から既存の局所化 nerve への関手

概要：元の Kan hammock 比較の左逆を通じて既存 localizationNerve へ送る。
方針：実際の左右の nerve 同値を合成し、その元の可逆二胞体を保持する。
規約：選択した逆の頂点作用を恒等とは仮定しない。元の頂点との比較を供給する。
使われ方：元の指定射を反転する CAlg_R への関手と ∞ 局所化の普遍性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanHammockLocalizationEquivalence`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def kanHammockLocalizationEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (kanHammockNerve C) (localizationNerve C)
```

### [LocalizedFreeResolution.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/LocalizedFreeResolution.lean)

OE04、42原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizedFreeResolution`。

# 自由単体的相対圏の次数ごとの厳密な局所化

概要：Dwyer–Kan の自由解像を全単体作用素に沿って次数ごとに局所化する。
方針：自由相対圏の全単体的解像に厳密な局所化関手を後合成する。
規約：各次数の指定矢は元の弱同値だけからなる列。
使われ方：固定対象を持つ単体的圏とその Kan 化の構成。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolution`。

```lean
universe u

def localizedFreeResolution (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) : SimplicialObject Cat.{u, u}
```

### [LocalizedResolutionFunctoriality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/LocalizedResolutionFunctoriality.lean)

OE04、88原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizedResolutionFunctoriality`。

# 局所化した自由解像の係数関手と対象表示

概要：Dwyer–Kan の全局所化解像へ相対関手を送り、同じ対象表示を保つ。
方針：全自由解像の係数射を厳密に局所化し、augmentation の自然性を使う。
規約：単体作用素と係数の両方に自然な元の対象表示を保持する。
使われ方：固定対象の Hom の間の単体写像の構成。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionMap`。

```lean
universe u

def localizedFreeResolutionMap {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    localizedFreeResolution C ⟶ localizedFreeResolution D
```

### [ModelBifibrantFramePinchedWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantFramePinchedWeak.lean)

OE04、117原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantFramePinchedWeak`。

概要：元の ambient Hom 単体を同じ bifibrant 局所化の pinched Hom へ弱比較する。
方針：元の Hom の包みを戻し、実二列比較と AsSmall の同じ全語同型を合成する。
規約：元の単体・全作用素・局所化頂点を保持する。
使われ方：実屋根の全次数の弱な pinched 基準族。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceFrameIndexIso`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)

def modelBifibrantSourceFrameIndexIso :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementCategory X Y q) ≅
      nerve (ULiftHom.{max u v}
        ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrame X q)).obj Y).Elements)ᵒᵖ))
```

### [ModelBifibrantFrameRightKanCofinality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantFrameRightKanCofinality.lean)

OE04、77原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantFrameRightKanCofinality`。

# 元の source frame 次数比較の実右 Kan cofinal 性

概要：元の実屋根の cofinal 性から同じ次数比較の left cofinal 性を得る。
方針：全 Quillen A slice を元の実屋根へ戻し、全 coslice 値の始対象性を使う。
規約：全矢図式へ置き換えず、元の次数比較を保持する。
使われ方：局所右 Kan 極限と標準右 Kan 錐。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceFrameRawRoofMap_isLeftCofinal`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [(HomotopicalAlgebra.cofibrations C).HasFunctorialFactorization
    (HomotopicalAlgebra.trivialFibrations C)]
  (X : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (r : SerrePositivity.Reedy.CofibrantResolutionFamily (C := Cᵒᵖ) SerrePositivity.Reedy.simplex)

lemma modelBifibrantSourceFrameRawRoofMap_isLeftCofinal (Y : HomotopicalAlgebra.BifibrantObject C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rawRoofFunctorMap
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q))
      (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y))))
```

### [ModelBifibrantFrameRoof.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantFrameRoof.lean)

OE04、68原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantFrameRoof`。

概要：元の bifibrant source frame の全単体から実 hammock の屋根比較を作る。
方針：同じ要素圏の実同型と元の raw roof 比較を合成する。
規約：元の射と全次数射影を保持する。
使われ方：実 right Kan 次数比較の余終性判定。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceFrameRoofMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)

def modelBifibrantSourceFrameRoofMap : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementCategory X Y q) ⟶
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)) ≫
        hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q) ≫
        hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
```

### [ModelBifibrantFrameRoofWeak.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantFrameRoofWeak.lean)

OE04、69原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantFrameRoofWeak`。

概要：元の bifibrant frame の実二列比較自身を hammock の弱同値へ接続する。
方針：元の包含像の全射等式と ambient frame 比較を、同じ包含の Hom 弱比較で反映する。
規約：第一の関手的分解と指定 right frame のみを使う。
使われ方：実 right Kan 次数比較の余終性への入力。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantFrameLeftRoofColimitMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)

def modelBifibrantFrameLeftRoofColimitMap :
    nerve (ULiftHom.{max u v}
      ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantFrame X q)).obj Y).Elements)ᵒᵖ)) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRawBifibrantWeak (C := C)) X Y
```

### [ModelBifibrantLocalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantLocalization.lean)

OE04、108原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantLocalization`。

概要：一般モデル圏の bifibrant hammock 自身の局所化普遍性。
方針：元の native roof の余終性を三つの right Kan 判定入力へ代入する。
規約：第一の関手的分解と指定 right frame を使い、SSet モデルは仮定しない。
使われ方：cofibrant 部分圏・全圏への変形と指定局所化との coherent 比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelSourceFrameFamily`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

def modelSourceFrameFamily : CofibrantResolutionFamily (C := C) simplex
```

### [ModelBifibrantRightKanReduction.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantRightKanReduction.lean)

OE04、338原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantRightKanReduction`。

概要：同じ bifibrant frame の余終性を三つの実 right Kan 判定入力に還元する。
方針：代数版の元の極限・標準錐・指定単位の証明を一般モデル圏へ移す。
規約：余終性は未証明の明示入力として残し、局所化普遍性の完成と扱わない。
使われ方：一般モデルの frame→hammock 比較から局所化普遍性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantHammockObject`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (q : ∀ X : BifibrantObject C, CofibrantResolution (C := C) simplex X.obj)
  (hcofinal : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (modelBifibrantFrameRightKanMap X (q X)))

def modelBifibrantHammockObject
    (z : (kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) _⦋0⦌) : BifibrantObject C
```

### [ModelBifibrantRightKanShape.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantRightKanShape.lean)

OE04、89原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantRightKanShape`。

概要：任意モデル圏の元の bifibrant frame から実 right Kan 形状への次数比較を作る。
方針：元の augmentation の全成分を同時に反転する実関手同型を使う。
規約：同じ局所化頂点と全次数の射影を保持し、余終性は後続で証明する。
使われ方：代数版の三つの局所化判定入力の一般化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantHammockVertex`。

```lean
universe u v w
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)

def modelBifibrantHammockVertex : (kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) _⦋0⦌
```

### [ModelBifibrantSourceFrameGraph.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceFrameGraph.lean)

OE04、51原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceFrameGraph`。

概要：元の bifibrant source frame の弱比較を同じ二列 graph の実射として露出する。
方針：元の全 Hom 同型、二列比較、AsSmall 全語同型を同じ順序で読む。
規約：元の全単体・両端点・元の余極限標準射を保持する。
使われ方：実 comma augmentation roof と同じ弱基準族の照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceFrameGraphMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)

def modelBifibrantSourceFrameGraphMap :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementCategory X Y q) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
```

### [ModelBifibrantSourceRoofAugmentationImage.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofAugmentationImage.lean)

OE04、66原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofAugmentationImage`。

概要：元の comma augmentation roof は同じ弱な balanced frame 比較の全族である。
方針：元の全単体の三頂点・二射と全縦射を厳密に照合する。
規約：包含の逆の選択や別の代表族を使わない。
使われ方：指定次数の native roof と同じ弱基準射の照合。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaAugmentationRoofGraphMap_image`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofProductCommaAugmentationRoofGraphMap_image :
    modelBifibrantSourceRoofProductCommaAugmentationRoofGraphMap X Y q b =
      modelBifibrantSourceRoofProductCommaFirstNerve X Y q b ≫
        modelBifibrantSourceFrameGraphMap X Y q
```

### [ModelBifibrantSourceRoofBaseEvaluation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofBaseEvaluation.lean)

OE04、113原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofBaseEvaluation`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaOver`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

abbrev modelBifibrantSourceRoofProductCommaOver
```

### [ModelBifibrantSourceRoofCornerEvaluation.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofCornerEvaluation.lean)

OE04、93原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofCornerEvaluation`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofDegreeObject`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

abbrev modelBifibrantSourceRoofDegreeObject : HomotopicalAlgebra.BifibrantObject C
```

### [ModelBifibrantSourceRoofCornerOver.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofCornerOver.lean)

OE04、84原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofCornerOver`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofDegreeTransportIso_inv_over`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofDegreeTransportIso_inv_over :
    (modelBifibrantSourceRoofDegreeTransportIso X Y q b).inv ≫ pullback.snd _ _ =
      pullback.snd _ _
```

### [ModelBifibrantSourceRoofDegreeModel.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofDegreeModel.lean)

OE04、101原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofDegreeModel`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductElements`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

abbrev modelBifibrantSourceRoofProductElements
```

### [ModelBifibrantSourceRoofEvaluationHomotopy.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofEvaluationHomotopy.lean)

OE04、87原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofEvaluationHomotopy`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaEvaluationHomotopy`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

def modelBifibrantSourceRoofProductCommaEvaluationHomotopy : SSet.Homotopy
    (nerveMap (modelBifibrantSourceRoofProductCommaDiagram X Y q b) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    (SSet.const (X := nerve (modelBifibrantSourceRoofProductComma X Y q b))
      (modelBifibrantHammockVertex (modelBifibrantSourceRoofDegreeObject X Y q b)))
```

### [ModelBifibrantSourceRoofGeometricLeftCell.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofGeometricLeftCell.lean)

OE04、111原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofGeometricLeftCell`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductGeometricLeftCell_eq`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofProductGeometricLeftCell_eq :
    modelBifibrantSourceRoofProductGeometricLeftCell X Y q b =
      (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom
```

### [ModelBifibrantSourceRoofGeometricRightCell.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofGeometricRightCell.lean)

OE04、82原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofGeometricRightCell`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductGeometricRightHomotopy_h`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofProductGeometricRightHomotopy_h :
    (modelBifibrantSourceRoofProductGeometricRightHomotopy X Y q b).h =
      (modelBifibrantSourceRoofProductCommaRightHomotopy X Y q b).h
```

### [ModelBifibrantSourceRoofNativePinchedReference.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofNativePinchedReference.lean)

OE04、117原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofNativePinchedReference`。

概要：元の指定次数の native roof を同じ balanced pinched 基準族と全体で同定する。
方針：元の四列比較と augmentation roof の全等式を同じ余極限で合成する。
規約：全パラメータを保持し、点ごとの類の一致へ置き換えない。
使われ方：実 interval 族の全合成三角形と roof 余終性の接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaDegreeHammockMap_transport`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofProductCommaDegreeHammockMap_transport :
    (modelBifibrantSourceRoofProductCommaIso X Y q b).inv ≫
      modelBifibrantSourceRoofProductDegreeHammockMap X Y q b =
        modelBifibrantSourceRoofProductCommaFirstNerve X Y q b ≫
          modelBifibrantSourceFrameColimitMap X Y q ≫
            modelBifibrantSourceRoofDegreePrecompose X Y q b
```

### [ModelBifibrantSourceRoofNativePrism.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofNativePrism.lean)

OE04、89原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofNativePrism`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativeSimplex_naturality`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofProductCommaNativeSimplex_naturality {m n : ℕ}
    (Γ : Fin (n + 1) ⥤ modelBifibrantSourceRoofProductComma X Y q b)
    (t : Fin (n + 1) →o Fin 2) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).op
      (modelBifibrantSourceRoofProductCommaNativeSimplex X Y q b Γ t) =
    modelBifibrantSourceRoofProductCommaNativeSimplex X Y q b
      (α.toOrderHom.monotone.functor ⋙ Γ) (t.comp α.toOrderHom)
```

### [ModelBifibrantSourceRoofNativePrismOne.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofNativePrismOne.lean)

OE04、107原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismOne`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativeSimplex_one`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofProductCommaNativeSimplex_one {n : ℕ}
    (Γ : Fin (n + 1) ⥤ modelBifibrantSourceRoofProductComma X Y q b) :
    modelBifibrantSourceRoofProductCommaNativeSimplex X Y q b Γ (OrderHom.const _ 1) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex
      (C := KanHammockCategory (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
      (X := (kanHammockSourceFunctor (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)).obj
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C (modelBifibrantSourceRoofDegreeObject X Y q b)))
      (Y := (kanHammockSourceFunctor (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)).obj
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y))
      ((modelBifibrantSourceRoofProductCommaNativeFamilyMap X Y q b).app (Opposite.op ⦋n⦌) Γ)
```

### [ModelBifibrantSourceRoofNativePrismProjection.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofNativePrismProjection.lean)

OE04、66原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismProjection`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativePrism_projection`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofProductCommaNativePrism_projection :
    modelBifibrantSourceRoofProductCommaNativePrism X Y q b ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (modelBifibrantHammockVertex Y)) =
    (β_ (Δ[1] : SSet.{max u v}) (nerve (modelBifibrantSourceRoofProductComma X Y q b))).hom ≫
      (modelBifibrantSourceRoofProductCommaEvaluationHomotopy X Y q b).h
```

### [ModelBifibrantSourceRoofNativePrismZero.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofNativePrismZero.lean)

OE04、87原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofNativePrismZero`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativePrism_zero_uncurry`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofProductCommaNativePrism_zero_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ modelBifibrantSourceRoofProductCommaNativePrism X Y q b) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (Cocone.mk
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
        (modelBifibrantSourceRoofProductCommaRightLeg X Y q b))).val ≫
      hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
```

### [ModelBifibrantSourceRoofNativeRoofComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofNativeRoofComparison.lean)

OE04、115原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofNativeRoofComparison`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaDiagram_map_weak`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofProductCommaDiagram_map_weak
    {s t : modelBifibrantSourceRoofProductComma X Y q b} (f : s ⟶ t) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
      ((modelBifibrantSourceRoofProductCommaDiagram X Y q b).map f)
```

### [ModelBifibrantSourceRoofNativeSimplex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofNativeSimplex.lean)

OE04、73原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofNativeSimplex`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativeSimplex`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

def modelBifibrantSourceRoofProductCommaNativeSimplex {n : ℕ}
    (Γ : Fin (n + 1) ⥤ modelBifibrantSourceRoofProductComma X Y q b)
    (t : Fin (n + 1) →o Fin 2) :
    (kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) _⦋n + 1⦌
```

### [ModelBifibrantSourceRoofNativeTriangle.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofNativeTriangle.lean)

OE04、78原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofNativeTriangle`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNative_triangle`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)

lemma modelBifibrantSourceRoofProductCommaNative_triangle
    (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌) :
    (modelBifibrantSourceRoofProductCommaEvaluationIso X Y q b).hom ≫
      modelBifibrantSourceRoofProductCommaNativeIntervalCell X Y q b =
        modelBifibrantSourceRoofProductCommaRightCell X Y q b
```

### [ModelBifibrantSourceRoofPrefixHomotopy.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofPrefixHomotopy.lean)

OE04、68原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofPrefixHomotopy`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaPrefixHomotopy`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)
  (s : modelBifibrantSourceRoofProductComma X Y q b)

def modelBifibrantSourceRoofProductCommaPrefixHomotopy : SSet.Homotopy
    (toUnit (nerve (Under s)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
      ((modelBifibrantSourceRoofProductCommaRightLeg X Y q b).app s))
    (nerveMap (Under.forget s) ≫ modelBifibrantSourceRoofProductCommaEvaluationRoofMap X Y q b ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
        ((modelBifibrantSourceRoofProductCommaEvaluation X Y q b).app s))
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y))
```

### [ModelBifibrantSourceRoofPrefixNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofPrefixNaturality.lean)

OE04、46原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofPrefixNaturality`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaPrefixHomotopy_underMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofProductCommaPrefixHomotopy_underMap
    {s t : modelBifibrantSourceRoofProductComma X Y q b} (a : s ⟶ t) :
    (nerveMap (Under.map a) ▷ (Δ[1] : SSet.{max u v})) ≫
      (modelBifibrantSourceRoofProductCommaPrefixHomotopy X Y q b s).h =
    (modelBifibrantSourceRoofProductCommaPrefixHomotopy X Y q b t).h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
        ((modelBifibrantSourceRoofProductCommaDiagram X Y q b).map a))
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
```

### [ModelBifibrantSourceRoofPrefixPath.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofPrefixPath.lean)

OE04、78原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofPrefixPath`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaNativeFamilyMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

def modelBifibrantSourceRoofProductCommaNativeFamilyMap :
    nerve (modelBifibrantSourceRoofProductComma X Y q b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C (modelBifibrantSourceRoofDegreeObject X Y q b))
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y))
```

### [ModelBifibrantSourceRoofProductCone.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofProductCone.lean)

OE04、149原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofProductCone`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductComma`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

abbrev modelBifibrantSourceRoofProductComma
```

### [ModelBifibrantSourceRoofProductCornerProjection.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofProductCornerProjection.lean)

OE04、136原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofProductCornerProjection`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofDegreeTransportIso_inv_source`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofDegreeTransportIso_inv_source :
    (modelBifibrantSourceRoofDegreeTransportIso X Y q b).inv ≫ pullback.fst _ _ =
      pullback.fst _ _
```

### [ModelBifibrantSourceRoofProductFunctorCell.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofProductFunctorCell.lean)

OE04、121原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofProductFunctorCell`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaEvaluationIso`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

def modelBifibrantSourceRoofProductCommaEvaluationIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (nerveMap (modelBifibrantSourceRoofProductCommaDiagram X Y q b) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    (SSet.const (X := nerve (modelBifibrantSourceRoofProductComma X Y q b))
      (modelBifibrantHammockVertex (modelBifibrantSourceRoofDegreeObject X Y q b)))
```

### [ModelBifibrantSourceRoofProductGeometricTriangle.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofProductGeometricTriangle.lean)

OE04、98原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofProductGeometricTriangle`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductGeometricLeftHomotopy`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

def modelBifibrantSourceRoofProductGeometricLeftHomotopy : SSet.Homotopy
    (nerveMap (modelBifibrantSourceRoofProductCommaDiagram X Y q b) ≫
      SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
    (SSet.const (X := nerve (modelBifibrantSourceRoofProductComma X Y q b))
      (modelBifibrantHammockVertex (modelBifibrantSourceRoofDegreeObject X Y q b)))
```

### [ModelBifibrantSourceRoofProductIntervalCriterion.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofProductIntervalCriterion.lean)

OE04、111原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofProductIntervalCriterion`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCommaHomMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

def modelBifibrantSourceRoofProductCommaHomMap :
  nerve (modelBifibrantSourceRoofProductComma X Y q b) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (modelBifibrantHammockVertex (modelBifibrantSourceRoofDegreeObject X Y q b))
      (modelBifibrantHammockVertex Y)
```

### [ModelBifibrantSourceRoofProductReference.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofProductReference.lean)

OE04、133原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofProductReference`。

概要：元の積単体の全族から指定次数の同じ pinched Hom への弱な基準射を作る。
方針：元の第一射影、実 frame の弱比較、同じ augmentation の前合成を合成する。
規約：同じ balanced hammock 内で全比較を行い、包含の逆を選ばない。
使われ方：実 roof の全 slice の同じ弱基準族。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductFirstNerve_weak`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceRoofProductFirstNerve_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (modelBifibrantSourceRoofProductFirstNerve X Y q b)
```

### [ModelBifibrantSourceRoofRightSlice.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofRightSlice.lean)

OE04、105原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofRightSlice`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceFrameRoofMap_normalizedOver`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

lemma modelBifibrantSourceFrameRoofMap_normalizedOver :
    modelBifibrantSourceFrameRoofMap X Y q ≫ pullback.fst _ _ ≫
      (roofTargetSlicePointIso (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementsDKNerveIso X Y q).hom ≫
      frameRoofRightSliceMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)
        (SimplicialLocalization.hammockLocalizationNerveMap
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C))
```

### [ModelBifibrantSourceRoofSliceCriterion.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofSliceCriterion.lean)

OE04、66原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofSliceCriterion`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofProductCornerMap`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

def modelBifibrantSourceRoofProductCornerMap :
  nerve (modelBifibrantSourceRoofProductElements X Y q b) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (modelBifibrantSourceRoofProjection X Y q)
```

### [ModelBifibrantSourceRoofSliceFibration.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofSliceFibration.lean)

OE04、172原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofSliceFibration`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofDegreeTransportIso`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

def modelBifibrantSourceRoofDegreeTransportIso :
    pullback (modelBifibrantSourceFrameRoofMap X Y q ≫ modelBifibrantSourceRoofProjection X Y q)
      (nerveMap (Over.forget (modelBifibrantSourceRoofDegree X Y q b))) ≅
        modelBifibrantSourceRoofDegreeModel X Y q b
```

### [ModelBifibrantSourceRoofSlices.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSourceRoofSlices.lean)

OE04、147原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofSlices`。

概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSourceRoofTarget`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)

abbrev modelBifibrantSourceRoofTarget
```

### [ModelBifibrantSpecifiedLocalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelBifibrantSpecifiedLocalization.lean)

OE04、53原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSpecifiedLocalization`。

概要：一般モデルの bifibrant hammock を指定された同じ弱同値の ∞ 局所化へ送る。
方針：実 right Kan 判定で得た普遍性を既存の局所化比較へ代入する。
規約：指定比較関手と指定二胞体を保持し、厳密な等式へ置き換えない。
使われ方：全 frame 比較の指定 pinched Hom への輸送と dg 代数への特殊化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelBifibrantSpecifiedLocalizationComparison`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {Q : SSet.{max u v}} [Quasicategory Q]
  (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category ⟶ Q)
  (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)))
  (K : kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ⟶ Q)
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C) ≫ K) G)

def modelBifibrantSpecifiedLocalizationComparison :
    FrameHom.CoherentLocalizationComparison
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) G
```

### [ModelCofibrantRightKanShape.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelCofibrantRightKanShape.lean)

OE04、99原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelCofibrantRightKanShape`。

概要：任意モデル圏の元の cofibrant frame から実 right Kan 形状への次数比較を作る。
方針：元の augmentation の全成分を同時に反転する実関手同型を使う。
規約：同じ局所化頂点と全次数の射影を保持し、余終性は後続で証明する。
使われ方：代数版の三つの局所化判定入力の一般化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelFrameIndex_weaklyContractible`。

```lean
universe u v w

lemma modelFrameIndex_weaklyContractible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve (AsSmall.{w} SimplexCategory))
```

### [ModelHammockLocalization.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelHammockLocalization.lean)

OE04、116原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelHammockLocalization`。

概要：実 bifibrant hammock の局所化普遍性を同じ cofibrant 部分圏と全モデル圏へ戻す。
方針：Ind-S (6) の源移送を元の弱単位・余単位へ適用し、同じ hammock nerve 同値を消去する。
規約：第一の関手的分解と指定 right frame のみを使い、元の源写像を保持する。
使われ方：全 C または cofibrant 部分圏の指定局所化への比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.relativeNerve_mapsWeak`。

```lean
universe u v w

lemma relativeNerve_mapsWeak {A B : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{w}}
    (F : LocalizerMorphism A.weakEquivalences B.weakEquivalences)
    (s : (nerve A.category) _⦋1⦌) (hs : s ∈ weakNerveEdges A) :
    (nerveMap F.functor).app (Opposite.op ⦋1⦌) s ∈ weakNerveEdges B
```

### [ModelHammockNerveEquivalence.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelHammockNerveEquivalence.lean)

OE04、66原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelHammockNerveEquivalence`。

概要：同じ bifibrant・cofibrant・全圏の実 hammock 比較を全 coherent nerve の同値へ上げる。
方針：元の全 Hom の弱比較と同じ弱単位または余単位を使う。
規約：全圏との比較には第一の関手的分解を明示する。
使われ方：bifibrant 中継から指定された全圏の局所化へ戻る比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelCofibrantToBifibrant_nerve_isQCatEquivalence`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

lemma modelCofibrantToBifibrant_nerve_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (relativeKanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToBifibrantRelative r))
```

### [ModelRightFrameComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelRightFrameComparison.lean)

OE04、132原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelRightFrameComparison`。

概要：一般モデル圏の実 right frame と指定された全圏の ∞ 局所化の写像空間比較。
方針：同じ bifibrant からの源移送で全圏普遍性を放電し、同じ六辺と指定二胞体を使う。
規約：第一の関手的分解と指定 right frame だけを追加し、全標的と元の単位を保持する。
使われ方：Sp の実 dg 代数モデルへの追加仮定のない特殊化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelRightFrameLocalizationComparison`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {Q : SSet.{max u v}} [Quasicategory Q]
  (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category ⟶ Q)
  (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)))

def modelRightFrameLocalizationComparison :
    FrameHom.CoherentLocalizationComparison
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)) G
```

### [ModelRightFrameSpecifiedInput.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ModelRightFrameSpecifiedInput.lean)

OE04、55原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelRightFrameSpecifiedInput`。

概要：指定 right frame と第一分解から指定局所化比較への残る入力を全圏普遍性一つに絞る。
方針：第一分解から source frame を選び、同じ六辺と同じ指定二胞体へ代入する。
規約：全圏の hammock 普遍性は Ind-S (6) の源移送を待つ明示入力である。
使われ方：その公開定理を代入した条件なしの主入口の構成。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.modelRightFrameHammockCoherentComparison`。

```lean
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  {Q : SSet.{max u v}} [Quasicategory Q]
  (G : nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category ⟶ Q)
  (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)))
  (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C))
    (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)))
  (K : kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) ⟶ Q)
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C) ≫ K) G)
  (X : C) [IsCofibrant X]

def modelRightFrameHammockCoherentComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (FrameHom.rightFrameHammockCoherentDiagram
        ((modelSourceFrameFamily (C := C)).atObject X) r 0)
      (FrameHom.rightFrameHammockCoherentDiagram
        ((modelSourceFrameFamily (C := C)).atObject X) r 6)
```

### [Nerve.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/Nerve.lean)

OE04、50原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.Nerve`。

# Kan 化した単体的局所化の coherent nerve

概要：Dwyer–Kan の具体的な単体的局所化から coherent nerve を構成する。
方針：実際の局所 Kan な豊穣圏に HTT 1.1.5.10 の既存の定理を適用する。
規約：Mathlib の SimplicialNerve を使い、局所 Kan 性は構成から供給する。
使われ方：CAlg_R の具体的な quasicategory とその頂点。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationNerve`。

```lean
universe u

def localizationNerve (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) : SSet.{u}
```

### [NerveFunctor.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/NerveFunctor.lean)

OE04、59原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.NerveFunctor`。

# 相対圏から局所化の coherent nerve への関手

概要：Dwyer–Kan の同じ局所化 nerve の係数射を厳密な関手に束ねる。
方針：Kan 化した豊穣係数関手の恒等・合成を coherent nerve の後合成で送る。
規約：対象・Hom・単位・合成を元の構成のまま保持する。
使われ方：忘却や離散対象の ∞ 関手の合成の整合性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationNerveMap_id`。

```lean
universe u

lemma localizationNerveMap_id (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    localizationNerveMap (𝟙 C) = 𝟙 (localizationNerve C)
```

### [NerveMap.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/NerveMap.lean)

OE04、51原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.NerveMap`。

# 相対関手が誘導する局所化の coherent nerve の射

概要：Dwyer–Kan の相対係数関手を局所化の quasicategory の間の射へ送る。
方針：同じ Kan 豊穣係数関手に既存の coherent nerve の後合成を使う。
規約：頂点での作用は元の相対関手の対象写像そのもの。
使われ方：E 代数の忘却関手や離散対象関手の ∞ 関手化。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationNerveMap`。

```lean
universe u

def localizationNerveMap {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (F : C ⟶ D) :
    localizationNerve C ⟶ localizationNerve D
```

### [NerveWeakVertexIso.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/NerveWeakVertexIso.lean)

OE04、44原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.NerveWeakVertexIso`。

# 元の弱同値射の局所化 nerve の頂点同型

概要：元の指定弱同値は同じ局所化 nerve の元の対象頂点を同型にする。
方針：同じ反転辺の homMk と全頂点比較を使う。
規約：元の局所化写像と頂点同値を変更しない。
使われ方：具体的 CAlg_R の任意頂点の実代数表示。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationNerveVertexIsoOfWeak`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def localizationNerveVertexIsoOfWeak {X Y : C.category} (f : X ⟶ Y)
    (hf : C.weakEquivalences f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (localizationNerveVertexEquiv C X) (localizationNerveVertexEquiv C Y)
```

### [RelativeHammockEnriched.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RelativeHammockEnriched.lean)

OE04、84原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RelativeHammockEnriched`。

概要：元の相対関手の全 hammock Hom 射を一つの豊穣関手と coherent nerve 射へ束ねる。
方針：元の単位と全合成の保存を使い、同じ Ex∞ で Kan 化する。
規約：点ごとの逆の選択を使わず、元の相対関手と全 Hom 射を保持する。
使われ方：bifibrant 中継から同じ cofibrant 局所化へ戻す全図式比較。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.relativeHammockEnriched`。

```lean
universe u
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}}
  (F : LocalizerMorphism C.weakEquivalences D.weakEquivalences)

def relativeHammockEnriched : EnrichedFunctor SSet.{u} (HammockObjects C) (HammockObjects D)
```

### [RelativeHammockNerveEquivalence.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RelativeHammockNerveEquivalence.lean)

OE04、96原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RelativeHammockNerveEquivalence`。

概要：同じ相対変形による hammock 比較を全 coherent nerve の同値へ上げる。
方針：全 Hom の弱比較から充満忠実性、元の弱単位から本質的全射性を得る。
規約：元の全関手と指定単位を保持する。
使われ方：bifibrant 部分圏から同じ cofibrant 局所化への復帰。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.relativeKanHammockNerve_essentiallySurjective`。

```lean
universe u
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}}
  (F : LocalizerMorphism C.weakEquivalences D.weakEquivalences)
  (G : LocalizerMorphism D.weakEquivalences C.weakEquivalences)
  (η : 𝟭 D.category ⟶ G.functor ⋙ F.functor)
  (hη : ∀ Y, D.weakEquivalences (η.app Y))

lemma relativeKanHammockNerve_essentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (relativeKanHammockNerve F)
```

### [RelativeHammockSourceComparison.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RelativeHammockSourceComparison.lean)

OE04、75原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RelativeHammockSourceComparison`。

概要：同じ相対関手の全 hammock 比較は元の局所化源の射と整合する。
方針：元の通常射の一定単体と Ex∞ 単位の自然性を使う。
規約：全関手の等式と同じ零単体・辺を保持する。
使われ方：指定局所化三角形の二胞体への接続。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.relativeHammockEnriched_arrowMap`。

```lean
universe u
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}}
  (F : LocalizerMorphism C.weakEquivalences D.weakEquivalences)

lemma relativeHammockEnriched_arrowMap {X Y : C.category} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f ≫ Relative.colimitMap F X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap D.weakEquivalences (F.functor.map f)
```

### [ResolutionFaces.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ResolutionFaces.lean)

OE04、86原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ResolutionFaces`。

# 自由単体的局所化の一次の二面

概要：Dwyer–Kan の標準射の一次単体の二面を元の自由圏の射で計算する。
方針：各面の厳密な局所化の因子化を Hom に評価し、対象移送を相殺する。
規約：一次の外側合成と内側合成を区別して保持する。
使われ方：元の射の連結成分の恒等・合成則。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationResolutionHom_delta_zero`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

lemma localizationResolutionHom_delta_zero {X Y : C.category}
    (f : freeResolutionGeneratorObject C 2 X ⟶ freeResolutionGeneratorObject C 2 Y) :
    (localizationHom C X Y).δ 0 (localizationResolutionHom C 1 f) =
      localizationResolutionHom C 0 ((pathComposition (Paths C.category)).map f)
```

### [ResolutionGenerators.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ResolutionGenerators.lean)

OE04、94原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ResolutionGenerators`。

# 自由単体的局所化の元の射の零単体

概要：Dwyer–Kan の自由解像の零次に元の圏の射を一文字の列として送る。
方針：同じ augmentation の対象単射性で標準生成対象と固定対象表示を同定する。
規約：零次の生成写像自体には合成保存を仮定しない。
使われ方：連結成分の圏と普通の局所化との比較の逆写像。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionObject_zero`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

lemma localizedFreeResolutionObject_zero (X : C.category) :
    localizedFreeResolutionObject C (op ⦋0⦌) X =
      C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj X)
```

### [ResolutionObjects.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ResolutionObjects.lean)

OE04、121原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ResolutionObjects`。

# 局所化した自由解像の固定対象の表示

概要：Dwyer–Kan の次数ごとの局所化の対象を元の相対圏の対象で表示する。
方針：augmentation の対象写像の全単射性と全単体作用素への自然性を使う。
規約：対象の表示の単体作用素との両立を証明して保持する。
使われ方：固定対象の Hom を単体集合へ束ねる。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeRelativeCounit_obj_bijective`。

```lean
universe u

lemma freeRelativeCounit_obj_bijective (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeCounit.app C).functor.obj
```

### [ResolutionRepresentatives.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ResolutionRepresentatives.lean)

OE04、111原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ResolutionRepresentatives`。

# 自由解像の全次数の標準対象と射の表示

概要：Dwyer–Kan の反復自由圏の元の対象と射を同じ固定 Hom へ送る。
方針：元の対象を反復して自由圏へ送り、augmentation の対象単射性で表示を同定する。
規約：元の自由解像・局所化・固定対象表示を保持する。
使われ方：一次の辺の二面による生成射の恒等・合成則。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionGeneratorObject`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def freeResolutionGeneratorObject : (n : ℕ) → C.category → (power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C n).category
  | 0, X => X
  | n + 1, X => (Paths.of _).obj (freeResolutionGeneratorObject n X)

/-- 概要：標準生成対象の augmentation は元の対象（Dwyer–Kan）。
方針：列の合成の対象写像が恒等であることを反復する。
規約：元の comonad の同じ augmentation。
使われ方：局所化した標準対象と固定表示の同定。 -/
lemma freeResolutionGeneratorObject_augmentation (n : ℕ) (X : C.category) :
    (augmentation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C n).functor.obj (freeResolutionGeneratorObject C n X) =
      X
```

### [ResolutionWordEdge.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ResolutionWordEdge.lean)

OE04、94原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ResolutionWordEdge`。

# 自由な列とその合成の一文字の列を結ぶ辺

概要：Dwyer–Kan の一次の自由解像が与える元の列の関係を辺として構成する。
方針：内側の列を外側の一文字にし、二つの面の既存の式を使う。
規約：元の列・元の合成・元の局所化を保持する。
使われ方：元の射の類の恒等・合成保存と普通の局所化の逆関手。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationResolutionWordEdge`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def localizationResolutionWordEdge {X Y : C.category}
    (p : (Paths.of C.category).obj X ⟶ (Paths.of C.category).obj Y) :
    (localizationHom C X Y).Edge (localizationArrowZero C (composePath p))
      (localizationResolutionHom C 0 p)
```

### [RoofPrefixColumnRoof.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixColumnRoof.lean)

OE04、118原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixColumnRoof`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.inv_arrow_eq`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (V : I ⥤ C.category) {X Y : C.category} (p : V ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (s : V ⟶ (Functor.const I).obj Y)
  (hV : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (V.map a))

lemma inv_arrow_eq {D : Type*} [Category* D] {a b a' b' : D}
    (f : a ⟶ b) (g : a' ⟶ b') [IsIso f] [IsIso g]
    (h : Arrow.mk f = Arrow.mk g) : Arrow.mk (inv f) = Arrow.mk (inv g)
```

### [RoofPrefixFamilyTriangle.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixFamilyTriangle.lean)

OE04、170原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixFamilyTriangle`。

module docstringなし。実際の型とimportを参照。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.coherentPinchedFamily`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

def coherentPinchedFamily : nerve I ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj Y))
```

### [RoofPrefixPath.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixPath.lean)

OE04、89原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPath`。

# 元の最大座標 prefix 写像を同じ Kan hammock Hom へ送る

概要：元の全 path 写像を元の Ex∞ 単位で送り、全合成・面と退化・両端を保つ。
方針：同じ単位の自然性と元の prefix 全円柱の等式を使う。
規約：元の相対圏・同じ Hom・同じ源関手の通常射を保持する。
使われ方：native roof prism の最後の頂点への豊穣 Hom の作用。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.familyMap`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

def familyMap : nerve I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y)
```

### [RoofPrefixPathComposition.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixPathComposition.lean)

OE04、69原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPathComposition`。

# 元の prefix path 写像の実 Kan 豊穣合成則

概要：元の通常射と prefix path の合成、および時刻一への切替を同じ豊穣合成で計算する。
方針：元の augmentation の自然性と Ex∞ の前合成・豊穣合成の厳密な一致を使う。
規約：全 path・時間・通常射・元の Kan Hom を保持する。
使われ方：native roof prism の 00 と 01 合成条件。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.pathMap_comp_enriched`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

lemma pathMap_comp_enriched {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    eComp SSet (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ ≫ pathMap C U p hp σ hU Γ t i =
    lift (toUnit _ ≫ ForgetEnrichment.homTo SSet.{u}
      ((kanHammockSourceFunctor C).map (U.map (Γ.map (homOfLE hij)))))
      (snd _ _ ≫ pathMap C U p hp σ hU Γ t j) ≫
        eComp SSet ((kanHammockSourceFunctor C).obj (U.obj (Γ.obj i)))
          ((kanHammockSourceFunctor C).obj (U.obj (Γ.obj j)))
          ((kanHammockSourceFunctor C).obj Y)
```

### [RoofPrefixPrismCompatibility.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixPrismCompatibility.lean)

OE04、98原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismCompatibility`。

# 混合 coherent 錐の最後 Hom の元の合成条件

概要：通常の評価円柱の射と時刻で切り替えた最後 Hom の全合成を照合する。
方針：00・01 は元の path 合成式、11 は最大座標の合成則と豊穣単位を使う。
規約：元の全時間・全 path・全 Kan Hom を保持する。
使われ方：native roof の混合 coherent 図式の EnrichedFunctor 条件。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.lastHom_comp`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

lemma lastHom_comp {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    eComp SSet (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex.{u} i.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex j.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex (Fin.last (n + 1))) ≫
      lastHom C U p hp σ hU Γ t i =
    lift (toUnit _ ≫ eHomEquiv SSet ((frontDiagram C U p Γ t).map (homOfLE hij)))
      (snd _ _ ≫ lastHom C U p hp σ hU Γ t j) ≫
        eComp SSet ((frontDiagram C U p Γ t).obj i) ((frontDiagram C U p Γ t).obj j)
          ((kanHammockSourceFunctor C).obj Y)
```

### [RoofPrefixPrismFront.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixPrismFront.lean)

OE04、98原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismFront`。

# native roof の混合円柱の元の通常の前面

概要：元の評価自然変換の通常の円柱を同じ Kan 源関手で送る。
方針：元の二値時間と単体図式を uncurry 関手へ代入する。
規約：00 は元の図式の射、01 は元の評価、11 は同じ対象の恒等射。
使われ方：mixed coherent 図式の非終点間の全 Hom。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.frontRaw`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X : C.category} (p : U ⟶ (Functor.const I).obj X)

def frontRaw {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2) :
    Fin (n + 1) ⥤ C.category
```

### [RoofPrefixPrismLast.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixPrismLast.lean)

OE04、61原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismLast`。

# 混合 coherent 錐の元の最後への Hom

概要：時刻零の始点では元の prefix path Hom、時刻一では同じ native roof 全族を使う。
方針：元の通常円柱の対象と同じ端点へ等号で輸送する。
規約：元の全 path・時間・Kan Hom を保持する。
使われ方：native roof 全三角形の mixed coherent 図式。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.lastHom`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

def lastHom {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) :
    SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex.{u} i.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex (Fin.last (n + 1))) ⟶
      SimplicialCategory.sHom ((frontDiagram C U p Γ t).obj i)
        ((kanHammockSourceFunctor C).obj Y)
```

### [RoofPrefixPrismNaturality.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixPrismNaturality.lean)

OE04、67原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismNaturality`。

# 元の混合 coherent 単体の全ての面と退化への自然性

概要：元の前面と最後 Hom の自然性を混合単体の全 Hom へ接続する。
方針：全豊穣関手の外延性と同じ端点正規化を使う。
規約：任意の単体圏の射・全 path・元の図式と時間を保持する。
使われ方：native roof 全三角形の実 slice prism。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.simplex_naturality`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

lemma simplex_naturality {m n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (kanHammockNerve C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).op (simplex C U p hp σ hU Γ t) =
      simplex C U p hp σ hU (α.toOrderHom.monotone.functor ⋙ Γ) (t.comp α.toOrderHom)
```

### [RoofPrefixPrismOne.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixPrismOne.lean)

OE04、47原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismOne`。

# 元の混合 coherent 単体の一端は同じ native Hom 比較

概要：時刻一の全単体を同じ native family の元の coherent Hom 比較単体へ同定する。
方針：通常前面の全恒等と最後 Hom の最大座標公式を使う。
規約：元の全 path・元の Kan Hom・同じ familyMap を保持する。
使われ方：native roof prism の一端の全 pinched 族への同定。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.simplex_one`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

lemma simplex_one {n : ℕ} (Γ : Fin (n + 1) ⥤ I) :
    simplex C U p hp σ hU Γ (OrderHom.const _ 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex ((familyMap C U p hp σ hU).app (Opposite.op ⦋n⦌) Γ)
```

### [RoofPrefixPrismProjection.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixPrismProjection.lean)

OE04、58原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismProjection`。

# 元の native roof 全 prism の底は標準評価円柱

概要：元の slice prism の前面を評価自然変換の元の全円柱へ同定する。
方針：全 coherent 前面と同じ nerve 自然変換円柱を全単体で照合する。
規約：元の時間・図式・Kan 源関手・局所化射を保持する。
使われ方：native roof 全三角形の元の左脚。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.simplex_front`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

lemma simplex_front {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2) :
    (kanHammockNerve C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op (simplex C U p hp σ hU Γ t) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (KanHammockCategory C)).app (Opposite.op ⦋n⦌)
        (frontDiagram C U p Γ t)
```

### [RoofPrefixPrismReindex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixPrismReindex.lean)

OE04、69原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismReindex`。

# 元の混合前面と最後 Hom の全添字変換

概要：元の通常前面と時刻で切り替えた最後 Hom が全ての面・退化と整合する。
方針：同じ最大座標の自然性・元の prefix path の自然性・端点の正規化を使う。
規約：元の図式・時間・全 path・同じ Kan Hom を保持する。
使われ方：mixed coherent 単体を全 slice prism に束ねる。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.frontDiagram_reindex`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

lemma frontDiagram_reindex {m n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    frontDiagram C U p (α.toOrderHom.monotone.functor ⋙ Γ) (t.comp α.toOrderHom) =
      α.toOrderHom.monotone.functor ⋙ frontDiagram C U p Γ t
```

### [RoofPrefixPrismSimplex.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixPrismSimplex.lean)

OE04、56原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismSimplex`。

# native roof の元の混合 coherent 単体

概要：元の前面と最後 Hom を全豊穣関手へ組み、同じ終点上の錐単体へ送る。
方針：検証済みの全合成式と豊穣単位則を使う。
規約：任意の時間単体・元の全 path・元の Kan Hom を保持する。
使われ方：native roof 全三角形の slice prism の各単体。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.mixedDiagram`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

def mixedDiagram {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (t : Fin (n + 1) →o Fin 2) :
    EnrichedFunctor SSet.{u} (SimplicialThickening (ULift.{u} (Fin (n + 2))))
      (KanHammockCategory C)
```

### [RoofPrefixPrismZero.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixPrismZero.lean)

OE04、70原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismZero`。

# 元の混合 coherent 単体の零端は通常の右余錐

概要：時刻零の全単体を元の通常右余錐の coherent 表示へ同定する。
方針：全前面と最後 Hom の通常射の定値公式を使う。
規約：同じ元の右脚を持つ余錐を保持する。
使われ方：native roof prism の零端条件 hb。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.rightCocone`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

def rightCocone : Cocone (U ⋙ kanHammockSourceFunctor C)
```

### [RoofPrefixPrismZeroSlice.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/RoofPrefixPrismZeroSlice.lean)

OE04、90原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismZeroSlice`。

# 元の native prism の零端と通常右余錐の全円柱

概要：全混合単体の零端を元の通常右余錐の slice へ同定する。
方針：同じ通常余錐の有限単体表示と curry の厳密な逆性を使う。
規約：元の通常右脚の全円柱を保持する。
使われ方：native roof 全三角形の零端条件 hb。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix.simplex_zero_join`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

lemma simplex_zero_join {n : ℕ} (Γ : Fin (n + 1) ⥤ I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
      (simplex C U p hp σ hU Γ (OrderHom.const _ 0)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm (show (nerve I) _⦋n⦌ from Γ)) (𝟙 (Δ[0] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (rightCocone C U σ)).val ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (KanHammockCategory C)
```

### [SourceHom.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/SourceHom.lean)

OE04、201原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.SourceHom`。

# 単体的局所化での厳密な射の代表

## 概要
普通の局所化において厳密射で表せる射を、
同じ厳密射による ∞ 局所化の辺の類で表す。

## 方針
Dwyer–Kan の比較で生成射を共通の自由 hammock の射に持ち上げ、
両側で評価する。

## 規約
同じ相対圏と同じ局所化源を使う。

## 使われ方
HA §3.2.2 の Barratt–Eccles 忘却関手の保存性。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationStrictHom`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def kanLocalizationStrictHom {X Y : C.category} (f : X ⟶ Y) :
    (show KanLocalizationCategory C from X) ⟶ (show KanLocalizationCategory C from Y)
```

### [WeakNerveInverts.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/WeakNerveInverts.lean)

OE04、44原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.WeakNerveInverts`。

# 元の弱同値射の反転から全指定辺の反転へ

概要：通常の各指定射の反転を元の全弱同値辺集合の反転として束ねる。
方針：同じ通常の辺の二つの表示をそのまま同定する。
規約：元の相対圏と全辺を変更しない。
使われ方：具体的な大きい忘却源への計算上限内の代入。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.weakNerveEdges_inverts_of_arrows`。

```lean
universe u

lemma weakNerveEdges_inverts_of_arrows (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {E : SSet.{u}}
    (F : nerve C.category ⟶ E)
    (h : ∀ {X Y : C.category} (f : X ⟶ Y), C.weakEquivalences f →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk f).map F).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (weakNerveEdges C)
```

### [ZeroLevelComponents.lean](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68/SerrePositivity/EInfinity/SimplicialLocalization/ZeroLevelComponents.lean)

OE04、94原行。配置：`SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ZeroLevelComponents`。

# 零次の局所化から連結成分の圏への関手

概要：Dwyer–Kan の零次の局所化の全射を同じ Hom の連結成分へ送る。
方針：標準対象の同じ表示で射を移し、元の単位・合成を商へ降ろす。
規約：形式逆も含む零次の全ての射を扱う。
使われ方：弱同値の反転と普通の局所化との比較の逆関手。

主宣言（基準の完全名）：`SerrePositivity.EInfinity.SimplicialLocalization.localizationZeroHom`。

```lean
universe u
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def localizationZeroHom {X Y : C.category}
    (f : C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj X) ⟶
      C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj Y)) :
    (localizationHom C X Y) _⦋0⦌
```

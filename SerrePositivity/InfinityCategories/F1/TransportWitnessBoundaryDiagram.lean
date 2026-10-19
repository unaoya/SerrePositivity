module

public import SerrePositivity.InfinityCategories.F1.TransportWitnessDiagram
public import SerrePositivity.InfinityCategories.F1.SmallCartesianRepresentationExtension
public import SerrePositivity.InfinityCategories.F1.SmallFiberCartesianExtension
public import SerrePositivity.InfinityCategories.Core.FixedDiagramVertexEquiv

/-!
概要：指定境界を固定した表現空間から境界固定の分類図式空間へ写す。
方針：表現の図式射影と cartesian 制限の自然性を fiber へ制限する。
規約：固定境界は全高次単体で保持する。
使われ方：可縮な表現の延長空間から変換の相対的な比較を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：cartesian 制限の図式射影は底の前合成と可換。
方針：表現空間の包含後に周囲の四角形の公式を使う。
規約：全高次の射の等式。
使われ方：境界固定 fiber の分類図式への射。 -/
lemma transportWitnessPre_diagram {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) :
    transportWitnessPre f hf ≫ transportWitnessDiagram p.hom =
      transportWitnessDiagram q.hom ≫ (pre f.right).app SpaceInfinity := by
  rw [transportWitnessDiagram, ← Category.assoc, transportWitnessPre_ι,
    Category.assoc, transportSquarePre_diagram]
  rfl

/-- 概要：境界の表現を固定した空間から境界固定の図式空間への射。
方針：図式射影を固定頂点の fiber へ持ち上げる。
規約：底の境界図式の射も厳密に固定する。
使われ方：表現空間の可縮性を固定端点の変換へ移す。 -/
def transportWitnessBoundaryDiagram {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) (S : LeftTransportRepresentation p.hom) :
    vertexFiber (transportWitnessPre f hf) (transportWitnessVertex S) ⟶
      vertexFiber ((pre f.right).app SpaceInfinity) (functorVertex S.diagram) :=
  vertexFiberLift _ _
    (vertexFiberι (transportWitnessPre f hf) (transportWitnessVertex S) ≫
      transportWitnessDiagram q.hom) (by
        rw [Category.assoc, ← transportWitnessPre_diagram f hf, ← Category.assoc,
          vertexFiberι_comp, SSet.const_comp, transportWitnessDiagram_vertex])

/-- 概要：指定境界へ制限される表現を境界固定空間の頂点にする。
方針：cartesian 制限の頂点公式を固定条件に使う。
規約：表現の実際の等式を要求する。
使われ方：共通境界の二つの表現の比較。 -/
def transportWitnessBoundaryVertex {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) (S : LeftTransportRepresentation p.hom)
    (R : LeftTransportRepresentation q.hom) (hR : R.cartesianRestrict f.left f.right hf = S) :
    (vertexFiber (transportWitnessPre f hf) (transportWitnessVertex S)) _⦋0⦌ :=
  ⟨transportWitnessVertex R, by
    rw [transportWitnessPre_cartesianRestrict_vertex, hR, pinchedConstant_zero]⟩

/-- 概要：境界固定空間の図式射影は元の表現の分類図式を回収する。
方針：fiber の部分型の値で図式射影の頂点公式を使う。
規約：境界条件の証明は cartesian 制限の等式から得る。
使われ方：実際の二つの分類図式の固定境界での比較。 -/
lemma transportWitnessBoundaryDiagram_vertex {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) (S : LeftTransportRepresentation p.hom)
    (R : LeftTransportRepresentation q.hom) (hR : R.cartesianRestrict f.left f.right hf = S) :
    (transportWitnessBoundaryDiagram f hf S).app _
      (transportWitnessBoundaryVertex f hf S R hR) =
      fixedDiagramVertex f.right S.diagram R.diagram
        (congrArg LeftTransportRepresentation.diagram hR) := by
  apply Subtype.ext
  exact transportWitnessDiagram_vertex R

/-- 概要：小さい全空間の共通境界を保つ二表現の図式は境界固定空間内で同型。
方針：制限の trivial Kan fibration の fiber の可縮性を図式射影で写す。
規約：同型は全体の関手空間より強い固定境界の fiber 内に置く。
使われ方：coherent な変換と復元した変換の比較。 -/
def smallFiberTransportRepresentation_fixedDiagramIso {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom]
    (hq : HasSmallSimplexFibers q.hom) (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) [Mono f.right]
    (S : LeftTransportRepresentation p.hom) (R T : LeftTransportRepresentation q.hom)
    (hR : R.cartesianRestrict f.left f.right hf = S)
    (hT : T.cartesianRestrict f.left f.right hf = S) :
    VertexIso (X := vertexFiber ((pre f.right).app SpaceInfinity) (functorVertex S.diagram))
      (fixedDiagramVertex f.right S.diagram R.diagram
        (congrArg LeftTransportRepresentation.diagram hR))
      (fixedDiagramVertex f.right S.diagram T.diagram
        (congrArg LeftTransportRepresentation.diagram hT)) := by
  have := smallFiberTransportWitnessPre_trivialKanFibration hq f hf
  have h := (vertexFiber_isContractibleKan (transportWitnessPre f hf)
    (transportWitnessVertex S)).vertexIso (transportWitnessBoundaryVertex f hf S R hR)
    (transportWitnessBoundaryVertex f hf S T hT)
  have e := VertexIso.map h (transportWitnessBoundaryDiagram f hf S)
  rw [transportWitnessBoundaryDiagram_vertex, transportWitnessBoundaryDiagram_vertex] at e
  exact e


/-- 概要：小さい全空間の固定境界比較は次数 fiber の一般の比較に従う。
方針：全空間の小ささを元の射影の次数 fiber へ渡す。
規約：従来の小さい全空間の界面を保つ。
使われ方：小さい底の変換の比較。 -/
def smallTransportRepresentation_fixedDiagramIso {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] [∀ n, Small.{u} (q.left.obj n)]
    (f : p ⟶ q) (hf : IsPullback f.left p.hom q.hom f.right) [Mono f.right]
    (S : LeftTransportRepresentation p.hom) (R T : LeftTransportRepresentation q.hom)
    (hR : R.cartesianRestrict f.left f.right hf = S)
    (hT : T.cartesianRestrict f.left f.right hf = S) :
    VertexIso (X := vertexFiber ((pre f.right).app SpaceInfinity) (functorVertex S.diagram))
      (fixedDiagramVertex f.right S.diagram R.diagram
        (congrArg LeftTransportRepresentation.diagram hR))
      (fixedDiagramVertex f.right S.diagram T.diagram
        (congrArg LeftTransportRepresentation.diagram hT)) := by
  exact smallFiberTransportRepresentation_fixedDiagramIso
    (hasSmallSimplexFibers_of_small_total q.hom) f hf S R T hR hT

/-- 概要：固定する境界図式の等式は同じ全体図式の頂点を保つ。
方針：境界図式の等式を消去する。
規約：図式の等式に沿う標準の移送。
使われ方：両端の和の図式との同一視。 -/
lemma fixedDiagramVertex_transport {A D X : SSet.{u}} (i : D ⟶ A)
    {b c : D ⟶ X} (h : b = c) (F : A ⟶ X) (hF : i ≫ F = b) :
    (eqToHom (congrArg (fun d ↦ vertexFiber ((pre i).app X) (functorVertex d)) h)).app _
      (fixedDiagramVertex i b F hF) = fixedDiagramVertex i c F (hF.trans h) := by
  subst c
  rfl

/-- 概要：cartesian 制限の等式は二つの実際の射の境界条件と同値。
方針：分類図式と pointed space への射による表現の外延性を使う。
規約：比較射の同値類の条件に弱めない。
使われ方：指定両端の表現を共通境界 fiber の頂点に戻す。 -/
lemma LeftTransportRepresentation.cartesianRestrict_eq_iff {E F B D : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ D} [LeftFibration p] [LeftFibration q]
    (R : LeftTransportRepresentation p) (S : LeftTransportRepresentation q)
    (e : F ⟶ E) (g : D ⟶ B) (h : IsPullback e q p g) :
    R.cartesianRestrict e g h = S ↔
      g ≫ R.diagram = S.diagram ∧ e ≫ R.pointedMap = S.pointedMap := by
  constructor
  · intro he
    exact ⟨congrArg LeftTransportRepresentation.diagram he,
      (R.cartesianRestrict_pointedMap e g h).symm.trans
        (congrArg LeftTransportRepresentation.pointedMap he)⟩
  · rintro ⟨hd, hp⟩
    exact LeftTransportRepresentation.ext _ _ hd ((R.cartesianRestrict_pointedMap e g h).trans hp)

end SerrePositivity.InfinityCategories

module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinInitialBoundary
public import SerrePositivity.InfinityCategories.Stable.RelativeInitialVertices

/-!
概要：各 fiber の全図式に余極限があると、相対 join の普遍余錐全体からの射は自明 Kan fibration。
方針：各頂点で余極限を選び、正次元の充填を相対始対象性で補う。
規約：底と標的は quasicategory、元の射は cocartesian fibration。
使われ方：Kan 拡張の coherent な存在と選択の一意性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：関手の族の頂点が表す、その射影の fiber 上の図式。
方針：fiber の関手空間の同型の逆で取り出し、関手の頂点を射に戻す。
規約：元の射と値域の充填性は不要。
使われ方：対象の族の各頂点だけに余極限の存在を課す。 -/
def kanFiberwiseHomVertexDiagram {K C D : SSet.{u}} (p : K ⟶ C)
    (y : (SerrePositivity.InfinityCategories.fiberwiseHom p D) _⦋0⦌) :
    vertexFiber p ((SerrePositivity.InfinityCategories.fiberwiseHomProjection p D).app (Opposite.op ⦋0⦌) y) ⟶ D :=
  let c := (SerrePositivity.InfinityCategories.fiberwiseHomProjection p D).app (Opposite.op ⦋0⦌) y
  let yf : (vertexFiber (SerrePositivity.InfinityCategories.fiberwiseHomProjection p D) c) _⦋0⦌ :=
    ⟨y, by rw [pinchedConstant_zero]⟩
  (functorVertexEquiv (vertexFiber p c) D).symm
    ((SerrePositivity.InfinityCategories.fiberwiseHomFiberIso p c D).inv.app (Opposite.op ⦋0⦌) yf)

/-- 概要：指定した図式の余極限から、対応する族の頂点に相対始対象の逆像を選べる。
方針：fiber の関手空間の同型で図式を取り出し、その余極限余錐を戻す。
規約：指定された y が表す fiber の図式だけに余極限を要求する。
使われ方：普遍余錐全体からの射の零次元の持ち上げ。 -/
lemma exists_kanRelativeJoin_initial_vertex_of_colimit {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (y : (SerrePositivity.InfinityCategories.fiberwiseHom p D) _⦋0⦌)
    (hcol : ∃ z : JoinCocone (kanFiberwiseHomVertexDiagram p y), IsColimitCone z) :
    ∃ x : (SerrePositivity.InfinityCategories.fiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) D) _⦋0⦌,
      (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)).app (Opposite.op ⦋0⦌) x = y ∧
        InitialBoundaryLifting (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)) x := by
  let c := (SerrePositivity.InfinityCategories.fiberwiseHomProjection p D).app (Opposite.op ⦋0⦌) y
  let yf : (vertexFiber (SerrePositivity.InfinityCategories.fiberwiseHomProjection p D) c) _⦋0⦌ :=
    ⟨y, by rw [pinchedConstant_zero]⟩
  let v := (SerrePositivity.InfinityCategories.fiberwiseHomFiberIso p c D).inv.app (Opposite.op ⦋0⦌) yf
  let d := kanFiberwiseHomVertexDiagram p y
  have hd : functorVertex d = v := (functorVertexEquiv (vertexFiber p c) D).apply_symm_apply v
  obtain ⟨z, hz⟩ := hcol
  let x := (kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
    (functorVertex z.val)
  refine ⟨x.val, ?_, kanRelativeJoinCocone_initialBoundary p c hz⟩
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (kanRelativeJoinCoconeFiberIso_restriction (D := D) p c)
      (Opposite.op ⦋0⦌)) (functorVertex z.val)
  have hzv : (coconeRestriction (vertexFiber p c) D).app (Opposite.op ⦋0⦌)
      (functorVertex z.val) = functorVertex d := by
    change functorVertex (joinInl (vertexFiber p c) Δ[0] ≫ z.val) = _
    rw [z.property]
  change (SerrePositivity.InfinityCategories.fiberwiseHomPreFiber (D := D) (kanRelativeJoinInlOver p) c).app
    (Opposite.op ⦋0⦌) x = (SerrePositivity.InfinityCategories.fiberwiseHomFiberIso p c D).hom.app
      (Opposite.op ⦋0⦌) ((coconeRestriction (vertexFiber p c) D).app
        (Opposite.op ⦋0⦌) (functorVertex z.val)) at h
  rw [hzv, hd] at h
  have hi := ConcreteCategory.congr_hom
    (NatTrans.congr_app (SerrePositivity.InfinityCategories.fiberwiseHomFiberIso p c D).inv_hom_id (Opposite.op ⦋0⦌)) yf
  change (SerrePositivity.InfinityCategories.fiberwiseHomFiberIso p c D).hom.app (Opposite.op ⦋0⦌) v = yf at hi
  have he := congrArg Subtype.val (h.trans hi)
  exact he

/-- 概要：各 fiber の全図式に余極限があれば、任意の族の頂点に相対始対象が存在する。
方針：頂点が表す一つの図式に仮定を適用する。
規約：一つの図式への弱い仮定は単数形の補題で扱う。
使われ方：普遍余錐全体からの射の零次元の持ち上げ。 -/
lemma exists_kanRelativeJoin_initial_vertex_of_colimits {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (hcol : ∀ (c : C _⦋0⦌) (d : vertexFiber p c ⟶ D),
      ∃ z : JoinCocone d, IsColimitCone z)
    (y : (SerrePositivity.InfinityCategories.fiberwiseHom p D) _⦋0⦌) :
    ∃ x : (SerrePositivity.InfinityCategories.fiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) D) _⦋0⦌,
      (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)).app (Opposite.op ⦋0⦌) x = y ∧
        InitialBoundaryLifting (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) (kanRelativeJoinInlOver p)) x :=
  exists_kanRelativeJoin_initial_vertex_of_colimit p y (hcol _ (kanFiberwiseHomVertexDiagram p y))

/-- 概要：各 fiber に必要な余極限があれば、相対始対象全体からの制限射は自明 Kan fibration。
方針：頂点での全射性と正次元の相対始点境界充填を合わせる。
規約：主張は全ての単射に対する右持ち上げ性。
使われ方：相対 join の普遍余錐の族の coherent な選択。 -/
lemma kanRelativeJoinColimitProjection_trivialKanFibration {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (hcol : ∀ (c : C _⦋0⦌) (d : vertexFiber p c ⟶ D),
      ∃ z : JoinCocone d, IsColimitCone z) :
    TrivialKanFibration (relativeInitialProjection
      (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) (kanRelativeJoinInlOver p))) := by
  apply relativeInitialProjection_trivialKanFibration
  intro y
  obtain ⟨x, hxy, hx⟩ := exists_kanRelativeJoin_initial_vertex_of_colimits p hcol y
  refine ⟨⟨x, ?_⟩, hxy⟩
  intro v
  have hv : v = 𝟙 _ := Subsingleton.elim _ _
  simpa only [hv, op_id, Functor.map_id_apply] using hx

end SerrePositivity.InfinityCategories.F1B

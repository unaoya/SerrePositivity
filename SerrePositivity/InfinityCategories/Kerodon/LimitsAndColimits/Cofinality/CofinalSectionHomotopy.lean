module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFunctorVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalComposition
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FiberwiseHomotopy

/-!
概要：相対関手空間の cofinality の検査から、切断と底を固定した収縮を取り出す。
方針：恒等写像の頂点を相対制限の同値で戻し、同じ Kan fiber 内の辺を uncurry する。
規約：底の quasicategory 性は不要。底との可換性は厳密な等式で保持する。
使われ方：Kerodon Corollary 7.2.1.15（Tag 02NE）、cofinal な fibration の fiber の可縮性。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：切断と底を固定した恒等射から切断への収縮のデータ。
方針：切断の等式、実際のホモトピー、その底への像を保持する。
規約：p 自体の充填性はフィールドに含めない。
使われ方：cofinal な左右 fibration の各頂点 fiber への制限。 -/
structure CofinalSectionHomotopy {E B : SSet.{u}} (p : E ⟶ B) where
  /-- 厳密な切断。 -/
  sectionMap : B ⟶ E
  /-- 切断と射影の合成は恒等射。 -/
  section_comp : sectionMap ≫ p = 𝟙 B
  /-- 底の上での収縮。 -/
  homotopy : SSet.Homotopy (𝟙 E) (p ≫ sectionMap)
  /-- 収縮の底は区間に依存しない。 -/
  homotopy_comp : homotopy.h ≫ p = fst E (Δ[1] : SSet.{u}) ≫ p
  /-- 逆向きにも選んだ底上の収縮。 -/
  reverseHomotopy : SSet.Homotopy (p ≫ sectionMap) (𝟙 E)
  /-- 逆向きの収縮も底の上にある。 -/
  reverseHomotopy_comp : reverseHomotopy.h ≫ p = fst E (Δ[1] : SSet.{u}) ≫ p

/-- 概要：p 自身による相対関手の制限が同値なら底上の収縮を持つ切断が存在する。
方針：恒等写像の連結成分を戻し、相対関手空間内の同型の代表辺を選ぶ。
規約：必要な二つの相対関手空間の Kan 性だけを仮定する。
使われ方：左右 cofinal な fibration に共通する構成。 -/
lemma nonempty_cofinalSectionHomotopy {E B : SSet.{u}} (p : E ⟶ B)
    [KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p (𝟙 B))]
    [KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p (p ≫ 𝟙 B))]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre p (𝟙 B) p)) :
    Nonempty (CofinalSectionHomotopy p) := by
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorVertex p (p ≫ 𝟙 B) (𝟙 E) (by simp)
  obtain ⟨a, ha⟩ := hp.mapPiZero_bijective.surjective (SSet.π₀.mk v)
  obtain ⟨u, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨s, hs, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.exists_cofinalFunctorVertex p (𝟙 B) u
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.nonempty_vertexIso_of_piZero_eq ha
  obtain ⟨k, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ e.inv
  let e' : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom E).obj E))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ s)) :=
    k.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom E).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ 𝟙 B))))
  have he' : ((ihom E).map p).app (Opposite.op ⦋1⦌) e'.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom E).obj B))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ 𝟙 B))).edge := by
    change ((ihom E).map p).app (Opposite.op ⦋1⦌) k.edge.val = _
    have hk := k.edge.property
    change ((ihom E).map p).app (Opposite.op ⦋1⦌) k.edge.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ 𝟙 B)) 1 at hk
    exact hk.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _)
  obtain ⟨l, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ e.hom
  let e'' : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom E).obj E))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ s)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 E)) :=
    l.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom E).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ 𝟙 B))))
  have he'' : ((ihom E).map p).app (Opposite.op ⦋1⦌) e''.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom E).obj B))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ 𝟙 B))).edge := by
    change ((ihom E).map p).app (Opposite.op ⦋1⦌) l.edge.val = _
    have hl := l.edge.property
    change ((ihom E).map p).app (Opposite.op ⦋1⦌) l.edge.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ 𝟙 B)) 1 at hl
    exact hl.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _)
  refine ⟨⟨s, hs, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e', ?_,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e'', ?_⟩⟩
  · simpa only [Category.comp_id] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.simplicialHomotopyOfFunctorEdge_comp_eq_constant p (p ≫ 𝟙 B) e' he'
  · simpa only [Category.comp_id] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.simplicialHomotopyOfFunctorEdge_comp_eq_constant p (p ≫ 𝟙 B) e'' he''

/-- 概要：left cofinal な left fibration は底上の収縮を持つ切断を持つ。
方針：p 自身を left fibration の検査対象に取る。
規約：底は任意の単体集合。
使われ方：cofinal left fibration の全境界充填への還元。 -/
lemma IsLeftCofinal.nonempty_sectionHomotopy {E B : SSet.{u}} {p : E ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal p) : Nonempty (CofinalSectionHomotopy p) :=
  nonempty_cofinalSectionHomotopy p (hp E p)

/-- 概要：right cofinal な right fibration は底上の収縮を持つ切断を持つ。
方針：p 自身を right fibration の検査対象に取る。
規約：底は任意の単体集合。
使われ方：cofinal right fibration の全境界充填への還元。 -/
lemma IsRightCofinal.nonempty_sectionHomotopy {E B : SSet.{u}} {p : E ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal p) : Nonempty (CofinalSectionHomotopy p) :=
  nonempty_cofinalSectionHomotopy p (hp E p)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

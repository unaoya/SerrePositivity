module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.EnrichedFunctors.ConeEdgeFunctoriality

/-! # 引き戻し四角形の指定射と fiber 比較

概要：四角形の下辺・左辺を標準 cospan の複体へ正規化し、比較射と二射影の合成に同定する。
方針：slice の比較三角形と標準錐の脚の arrow の等式を使う。
規約：端点の等式による移送だけを加え、射のホモトピー類は変えない。
使われ方：D6a の指定四辺による三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory SSet DifferentialGraded

open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

/-- 概要：cospan の左頂点を選ぶ。
方針：左の辺の始点を評価する。
規約：四角形では右下の頂点。使われ方：第一脚の添字。 -/
abbrev derivedCospanBottomVertex : (horn 2 2 : SSet.{u}) _⦋0⦌ :=
  SSet.yonedaEquiv (stdSimplex.δ 1 ≫ horn₂₂.ι₀₂)

/-- 概要：cospan の右頂点を選ぶ。
方針：右の辺の始点を評価する。
規約：四角形では左上の頂点。使われ方：第二脚の添字。 -/
abbrev derivedCospanLeftVertex : (horn 2 2 : SSet.{u}) _⦋0⦌ :=
  SSet.yonedaEquiv (stdSimplex.δ 1 ≫ horn₂₂.ι₁₂)

variable (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)

/-- 概要：四角形の左下の複体。
方針：錐の頂点の唯一の対象を取る。
規約：semifree 証明を除いた複体。使われ方：fiber 列の始域。 -/
abbrev derivedSquareCornerComplex : Complex S := ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex.obj 0).val

/-- 概要：標準 fiber 錐の頂点をそのまま複体として読む。
方針：標準四角形の join 錐の頂点を評価する。
規約：標準 fiber との等式を後で与える。使われ方：端点の正規化。 -/
abbrev derivedSquareRawFiberVertex : Complex S :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F)).vertex.obj 0).val

/-- 概要：標準 cospan の指定頂点の複体。
方針：cospan を頂点で評価する。
規約：元の四角形と cospan は等しい。使われ方：錐の脚の終域。 -/
abbrev derivedSquareRawDiagramVertex (v : (horn 2 2 : SSet.{u + 1}) _⦋0⦌) : Complex S :=
  (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F)).app _ v).obj 0).val

/-- 概要：頂点を移送する前の比較辺の鎖写像。
方針：slice の比較辺を射影して全複体へ包含する。
規約：終域は標準錐の実際の頂点。使われ方：脚との合成三角形。 -/
abbrev derivedSquareRawComparison :
    derivedSquareCornerComplex F ⟶ derivedSquareRawFiberVertex F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareComparisonSliceEdge F).map ((truncation 2).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F))))).map
      ((truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))

/-- 概要：元の四角形の錐の指定脚の鎖写像。
方針：同じ cospan への読み替えた錐の脚を包含する。
規約：所属証明と rebase は一単体を変えない。使われ方：指定された下辺・左辺。 -/
abbrev derivedSquareRawLeg (v : (horn 2 2 : SSet.{u + 1}) _⦋0⦌) :
    derivedSquareCornerComplex F ⟶ derivedSquareRawDiagramVertex F v :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareComparisonCone F) v).map
    ((truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))

/-- 概要：標準 fiber 錐の指定脚の鎖写像。
方針：標準錐の脚を全複体へ包含する。
規約：端点は標準錐の実際の頂点のまま。使われ方：二射影との比較。 -/
abbrev derivedSquareRawFiberLeg (v : (horn 2 2 : SSet.{u + 1}) _⦋0⦌) :
    derivedSquareRawFiberVertex F ⟶ derivedSquareRawDiagramVertex F v :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F)) v).map
    ((truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))

/-- 概要：標準錐の実際の頂点の複体は標準 fiber である。
方針：D4 の頂点の等式を複体として評価する。
規約：同型ではなく等式。使われ方：比較射の終域の正規化。 -/
lemma derivedSquareRawFiberVertex_eq :
    derivedSquareRawFiberVertex F = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareStandardFiber F).val :=
  congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) 0 => (s.obj 0).val)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_vertex F)

/-- 概要：左 cospan 頂点の複体は抽出した左対象である。
方針：第一脚の arrow の等式の終域を取る。
規約：四角形の下辺の終点。使われ方：下辺の正規化。 -/
lemma derivedSquareRawBottomVertex_eq :
    derivedSquareRawDiagramVertex F derivedCospanBottomVertex = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation
      F).leftObj :=
  congrArg (fun a : Arrow (Complex S) => a.right) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberCone_bottom_arrow F)

/-- 概要：右 cospan 頂点の複体は抽出した右対象である。
方針：第二脚の arrow の等式の終域を取る。
規約：四角形の左辺の終点。使われ方：左辺の正規化。 -/
lemma derivedSquareRawLeftVertex_eq :
    derivedSquareRawDiagramVertex F derivedCospanLeftVertex = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation
      F).rightObj :=
  congrArg (fun a : Arrow (Complex S) => a.right) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberCone_left_arrow F)

/-- 概要：四角形の下辺を抽出した左対象への鎖写像として読む。
方針：脚の鎖写像の終域だけを等式で同定する。
規約：元の下辺のホモトピー類。使われ方：fiber 列の第一成分。 -/
def derivedSquareBottomMap :
    derivedSquareCornerComplex F ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftObj :=
  derivedSquareRawLeg F derivedCospanBottomVertex ≫ eqToHom (derivedSquareRawBottomVertex_eq F)

/-- 概要：四角形の左辺を抽出した右対象への鎖写像として読む。
方針：脚の鎖写像の終域だけを等式で同定する。
規約：元の左辺のホモトピー類。使われ方：fiber 列の第二成分。 -/
def derivedSquareLeftMap :
    derivedSquareCornerComplex F ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightObj :=
  derivedSquareRawLeg F derivedCospanLeftVertex ≫ eqToHom (derivedSquareRawLeftVertex_eq F)

/-- 概要：比較射と標準脚の合成は元の脚の鎖写像にホモトピックである。
方針：slice の比較三角形を包含し、N3 の合成関係を複体ホモトピー圏へ移す。
規約：任意の図式の指定頂点で成り立つ。使われ方：二射影への正規化。 -/
lemma derivedSquareRawComparison_leg (v : (horn 2 2 : SSet.{u + 1}) _⦋0⦌) :
    (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map
      (derivedSquareRawComparison F ≫ derivedSquareRawFiberLeg F v) =
      (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map (derivedSquareRawLeg F v) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_edgeChainMap_comp ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLegCompStruct (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareComparisonSliceEdge F) v).map
    ((truncation 2).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))

private lemma arrow_eq_square {V : Type*} [Category V] {X Y X' Y' : V}
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : Arrow.mk f = Arrow.mk g) :
    eqToHom (congrArg (fun a : Arrow V => a.left) h) ≫ g =
      f ≫ eqToHom (congrArg (fun a : Arrow V => a.right) h) := by
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  subst X' Y'
  simp_all

private lemma edgeChainMap_map_transportTarget {X : SSet.{u + 1}} {x y z : X _⦋0⦌}
    (h : y = z) (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (q : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeTransportTarget h e).map ((truncation 2).map q)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (e.map ((truncation 2).map q)) ≫
        eqToHom (congrArg (fun v : X _⦋0⦌ => (q.app _ v).obj 0) h) := by
  cases h
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeTransportTarget, eqToHom_refl, Category.comp_id]

/-- 概要：D4 の比較射は、移送前の比較射の終域を標準 fiber に同定したものである。
方針：辺の終点の移送を鎖写像の後合成へ読み替える。
規約：D4 の比較射自体を使う。使われ方：射影との合成の正規化。 -/
lemma derivedSquareRawComparison_eq :
    derivedSquareRawComparison F ≫ eqToHom (derivedSquareRawFiberVertex_eq F) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison F := by
  exact (edgeChainMap_map_transportTarget (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare_vertex F)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareComparisonSliceEdge F).map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberSquare F)))))
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion).symm

/-- 概要：第一脚の端点を正規化すると標準第一射影になる。
方針：第一脚の arrow の等式を可換な四角形として読む。
規約：始域と終域の両方を同定する。使われ方：比較射の第一成分。 -/
lemma derivedSquareRawFiberLeg_bottom_eq :
    eqToHom (derivedSquareRawFiberVertex_eq F) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation
        F).rightMap =
      derivedSquareRawFiberLeg F derivedCospanBottomVertex ≫
        eqToHom (derivedSquareRawBottomVertex_eq F) := by
  exact arrow_eq_square _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberCone_bottom_arrow F)

/-- 概要：第二脚の端点を正規化すると標準第二射影になる。
方針：第二脚の arrow の等式を可換な四角形として読む。
規約：始域と終域の両方を同定する。使われ方：比較射の第二成分。 -/
lemma derivedSquareRawFiberLeg_left_eq :
    eqToHom (derivedSquareRawFiberVertex_eq F) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation
        F).rightMap =
      derivedSquareRawFiberLeg F derivedCospanLeftVertex ≫
        eqToHom (derivedSquareRawLeftVertex_eq F) := by
  exact arrow_eq_square _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberCone_left_arrow F)

/-- 概要：D4 の比較射と第一射影の合成は元の下辺にホモトピックである。
方針：比較三角形の合成関係を端点の同定で正規化する。
規約：四角形の極限性は不要。使われ方：指定下辺による三角形の第一射。 -/
lemma derivedSquareFiberComparison_bottom :
    (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison F ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation
          F).rightMap) =
      (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map (derivedSquareBottomMap F) := by
  rw [← derivedSquareRawComparison_eq, Category.assoc, derivedSquareRawFiberLeg_bottom_eq,
    ← Category.assoc]
  simpa only [Functor.map_comp, derivedSquareBottomMap] using
    congrArg (fun k => k ≫ (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map
      (eqToHom (derivedSquareRawBottomVertex_eq F)))
        (derivedSquareRawComparison_leg F derivedCospanBottomVertex)

/-- 概要：D4 の比較射と第二射影の合成は元の左辺にホモトピックである。
方針：比較三角形の合成関係を端点の同定で正規化する。
規約：四角形の極限性は不要。使われ方：指定左辺による三角形の第一射。 -/
lemma derivedSquareFiberComparison_left :
    (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberComparison F ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation
          F).rightMap) =
      (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map (derivedSquareLeftMap F) := by
  rw [← derivedSquareRawComparison_eq, Category.assoc, derivedSquareRawFiberLeg_left_eq,
    ← Category.assoc]
  simpa only [Functor.map_comp, derivedSquareLeftMap] using
    congrArg (fun k => k ≫ (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map
      (eqToHom (derivedSquareRawLeftVertex_eq F)))
        (derivedSquareRawComparison_leg F derivedCospanLeftVertex)

/-- 概要：元の四角形の錐を包含した写像は、包含した四角形の錐の写像である。
方針：錐の写像の結合則を用いる。
規約：図式の rebase は写像を変更しない。使われ方：指定四辺との一致。 -/
lemma derivedSquareComparisonCone_inclusion_val :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedConePostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareComparisonCone F) _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)).val := by
  exact Category.assoc _ _ _

/-- 概要：正規化した下辺は、元の四角形の指定下辺と同じ一単体を与える。
方針：鎖写像と辺の読み戻し、錐の包含、下辺の幾何学的同定を使う。
規約：追加の整合条件なし。使われ方：D5d の H⁰ の射との一致。 -/
lemma derivedSquareBottomMap_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (derivedSquareBottomMap F)).edge =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomEdge ≫ (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)) := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (derivedSquareRawLeg F derivedCospanBottomVertex)).edge :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_comp_eqToHom _ _
    _ = _ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_complexEdge_edgeChainMap _
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedConeLeg_postcomp_edge _ _ _
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedConeLeg_edge_eq_of_val_eq _ _ (derivedSquareComparisonCone_inclusion_val F) _
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedConeLeg_pullback_bottom _

/-- 概要：正規化した左辺は、元の四角形の指定左辺と同じ一単体を与える。
方針：鎖写像と辺の読み戻し、錐の包含、左辺の幾何学的同定を使う。
規約：追加の整合条件なし。使われ方：D5d の H⁰ の射との一致。 -/
lemma derivedSquareLeftMap_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (derivedSquareLeftMap F)).edge =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftEdge ≫ (F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)) := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (derivedSquareRawLeg F derivedCospanLeftVertex)).edge :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_comp_eqToHom _ _
    _ = _ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_complexEdge_edgeChainMap _
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedConeLeg_postcomp_edge _ _ _
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedConeLeg_edge_eq_of_val_eq _ _ (derivedSquareComparisonCone_inclusion_val F) _
    _ = _ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedConeLeg_pullback_left _

end SerrePositivity.InfinityCategories.Project.DerivedCategories

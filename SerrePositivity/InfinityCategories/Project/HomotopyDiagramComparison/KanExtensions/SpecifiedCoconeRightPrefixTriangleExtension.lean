module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.SpecifiedCoconeLeftTriangleExtension

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionComparisonNaturality
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRightPrefixTriangle
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentTransportTriangleVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionHomotopyEdge
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.RelativeExtensionHomotopy

/-!
概要：指定した実際の右初面三角形と標準輸送三角形を、同じ底・始点の延長空間へ置く。
方針：実際の二図式を頂点として保持し、長辺の制限が比較同型を保つことを示す。
規約：元の native 二単体と始点を固定する。使われ方：指定境界路の右初面部分の高次照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "σ" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "β" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σ)
local notation "i₀" => stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3)
local notation "v" => SSet.yonedaEquiv.symm c
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC
local notation "T" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex q σ
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex c) rfl)

/-- 実際の右初面三角形の長辺の始点は、元の共通余錐の同じ点。 -/
lemma specifiedCoconeRightPrefixTriangleExtension_initial : i₀ ≫ L = v := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleLongInitial_firstVertex, ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleFirstInitial_firstVertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_initial hp p c hc dB dC

/-- 同じ native 三角形上で固定する初期図式は、元の共通余錐の底を持つ。 -/
lemma specifiedCoconeRightPrefixTriangleExtension_initial_base : v ≫ q = i₀ ≫ β :=
  (congrArg (fun z ↦ z ≫ q)
    (specifiedCoconeRightPrefixTriangleExtension_initial hp p c hc dB dC).symm).trans
      ((Category.assoc _ _ _).trans (congrArg (fun z ↦ i₀ ≫ z)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_projection hp p c hc dB dC)))

local notation "hv" => specifiedCoconeRightPrefixTriangleExtension_initial_base hp p c hc dB dC
local notation "S" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace q β i₀ v hv

/-- 元の二単体と共通余錐を厳密に固定する、同じ三角形の持ち上げの空間。 -/
def specifiedCoconeRightPrefixTriangleExtensionSpace : SSet.{u + 1} := S

/-- この三角形の持ち上げの空間は、全高次の比較を含めて可縮な Kan 複体。 -/
lemma specifiedCoconeRightPrefixTriangleExtensionSpace_isContractibleKan :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (specifiedCoconeRightPrefixTriangleExtensionSpace hp p c hc dB dC) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleLongInitial_firstVertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne 2

/-- 実際の右初面三角形を、同じ底・初期値の延長空間の頂点として保持する。 -/
def specifiedCoconeRightPrefixActualTriangleExtensionVertex : (S) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv q β i₀ v hv
    ⟨L, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_projection hp p c hc dB dC,
      specifiedCoconeRightPrefixTriangleExtension_initial hp p c hc dB dC⟩

omit [Mono g] in
/-- 標準輸送三角形の初期値も、元の共通余錐の同じ点。 -/
lemma specifiedCoconeRightPrefixStandardTriangleExtension_initial : i₀ ≫ T = v := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleLongInitial_firstVertex, ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleFirstInitial_firstVertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_initial q σ _

/-- 標準輸送三角形も、同じ底・初期値の延長空間の頂点。 -/
def specifiedCoconeRightPrefixStandardTriangleExtensionVertex : (S) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv q β i₀ v hv
    ⟨T, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_projection q σ _,
      specifiedCoconeRightPrefixStandardTriangleExtension_initial hp p c hc dB dC⟩

/-- 同じ初期図式を保ち、三角形の全持ち上げを元の長辺へ制限する。 -/
def specifiedCoconeRightPrefixTriangleLongRestriction :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRestriction q β (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 2)) v hv

/-- 実際の右初面三角形の制限は、その同じ三角形の長辺を表す頂点そのもの。 -/
lemma specifiedCoconeRightPrefixActualTriangleExtensionVertex_long :
    (specifiedCoconeRightPrefixTriangleLongRestriction hp p c hc dB dC).app _
        (specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv q (stdSimplex.δ (1 : Fin 3) ≫ β)
        (stdSimplex.δ (1 : Fin 2)) v ((hv).trans (Category.assoc _ _ _))
        ⟨stdSimplex.δ (1 : Fin 3) ≫ L,
          (Category.assoc _ _ _).trans (congrArg (fun z ↦ stdSimplex.δ (1 : Fin 3) ≫ z)
            (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_projection hp p c hc dB dC)),
          (Category.assoc _ _ _).symm.trans
            (specifiedCoconeRightPrefixTriangleExtension_initial hp p c hc dB dC)⟩ :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRestriction_vertex q β _ _ v hv L
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_projection hp p c hc dB dC)
    (specifiedCoconeRightPrefixTriangleExtension_initial hp p c hc dB dC)

/-- 標準輸送側の制限も、同じ native 二単体の標準三角形の長辺そのもの。 -/
lemma specifiedCoconeRightPrefixStandardTriangleExtensionVertex_long :
    (specifiedCoconeRightPrefixTriangleLongRestriction hp p c hc dB dC).app _
        (specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv q (stdSimplex.δ (1 : Fin 3) ≫ β)
        (stdSimplex.δ (1 : Fin 2)) v ((hv).trans (Category.assoc _ _ _))
        ⟨stdSimplex.δ (1 : Fin 3) ≫ T,
          (Category.assoc _ _ _).trans (congrArg (fun z ↦ stdSimplex.δ (1 : Fin 3) ≫ z)
            (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_projection q σ _)),
          (Category.assoc _ _ _).symm.trans
            (specifiedCoconeRightPrefixStandardTriangleExtension_initial hp p c hc dB dC)⟩ :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRestriction_vertex q β _ _ v hv T
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_projection q σ _)
    (specifiedCoconeRightPrefixStandardTriangleExtension_initial hp p c hc dB dC)

/-- 三角形の同じ二頂点の比較を、元の長辺の延長空間へ写した同型。 -/
def specifiedCoconeRightPrefixTriangleLongComparisonIso :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
    ((specifiedCoconeRightPrefixTriangleExtensionSpace_isContractibleKan hp p c hc dB dC).vertexIso
      (specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC)
      (specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC))
    (specifiedCoconeRightPrefixTriangleLongRestriction hp p c hc dB dC)

/-- 元の二単体の比較を制限した同型は、同じ長辺の延長空間の指定比較と一致する。 -/
lemma specifiedCoconeRightPrefixTriangleLongComparisonIso_eq :
    specifiedCoconeRightPrefixTriangleLongComparisonIso hp p c hc dB dC =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan q (stdSimplex.δ (1 : Fin 3) ≫ β)
        (stdSimplex.δ (1 : Fin 2)) (by
          rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeInitial_firstVertex]
          exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne 1) v ((hv).trans (Category.assoc _ _ _))).vertexIso
        ((specifiedCoconeRightPrefixTriangleLongRestriction hp p c hc dB dC).app _
          (specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC))
        ((specifiedCoconeRightPrefixTriangleLongRestriction hp p c hc dB dC).app _
          (specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRestriction_vertexIso_map
  · exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleLongInitial_leftAnodyne
  · exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeInitial_leftAnodyne

/-- 元の二つの三角形を、底と初期値を固定して結ぶ実際の円柱。 -/
structure SpecifiedCoconeRightPrefixTriangleComparison where
  homotopy : SSet.Homotopy L T
  projection : homotopy.h ≫ q = fst (Δ[2] : SSet.{u + 1}) Δ[1] ≫ β
  initial : (i₀ ▷ (Δ[1] : SSet.{u + 1})) ≫ homotopy.h = fst Δ[0] Δ[1] ≫ v

/-- 元の二三角形の底と始点を同時に保つ、同じ相対比較を構成する。 -/
def specifiedCoconeRightPrefixTriangleComparison :
    SpecifiedCoconeRightPrefixTriangleComparison hp p c hc dB dC :=
  Classical.choice (by
    obtain ⟨H, hH, hI⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_homotopy_over_fixed_extension q β i₀
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleLongInitial_leftAnodyne v hv L T
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_projection hp p c hc dB dC)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_projection q σ _)
      (specifiedCoconeRightPrefixTriangleExtension_initial hp p c hc dB dC)
      (specifiedCoconeRightPrefixStandardTriangleExtension_initial hp p c hc dB dC)
    exact ⟨⟨H, hH, hI⟩⟩)

/-- 同じ実際の円柱を、元の二単体と始点の延長空間の辺として保持する。 -/
def specifiedCoconeRightPrefixTriangleComparisonExtensionEdge : (S).Edge
    (specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC)
    (specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge q β i₀ v hv
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle_projection hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleVertex_projection q σ _)
    (specifiedCoconeRightPrefixTriangleExtension_initial hp p c hc dB dC)
    (specifiedCoconeRightPrefixStandardTriangleExtension_initial hp p c hc dB dC)
    (specifiedCoconeRightPrefixTriangleComparison hp p c hc dB dC).homotopy
    (specifiedCoconeRightPrefixTriangleComparison hp p c hc dB dC).projection
    (specifiedCoconeRightPrefixTriangleComparison hp p c hc dB dC).initial

/-- 延長空間の辺を展開すると、選択済みの同じ相対円柱を回収する。 -/
lemma specifiedCoconeRightPrefixTriangleComparisonExtensionEdge_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (SSet.yonedaEquiv.symm
      (specifiedCoconeRightPrefixTriangleComparisonExtensionEdge hp p c hc dB dC).edge ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι q β i₀ v hv) =
      (specifiedCoconeRightPrefixTriangleComparison hp p c hc dB dC).homotopy.h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionHomotopyEdge_uncurry _ _ _ _ _ _ _ _ _ _ _ _

/-- 長辺への制限を展開しても、元の実際の円柱を同じ長辺へ制限した射を保持する。 -/
lemma specifiedCoconeRightPrefixTriangleComparisonExtensionEdge_long_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (SSet.yonedaEquiv.symm
      (specifiedCoconeRightPrefixTriangleComparisonExtensionEdge hp p c hc dB dC).edge ≫
        specifiedCoconeRightPrefixTriangleLongRestriction hp p c hc dB dC ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι q (stdSimplex.δ (1 : Fin 3) ≫ β)
            (stdSimplex.δ (1 : Fin 2)) v ((hv).trans (Category.assoc _ _ _))) =
      (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (specifiedCoconeRightPrefixTriangleComparison hp p c hc dB dC).homotopy.h :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRestriction_uncurry q β _ _ v hv (SSet.yonedaEquiv.symm
    (specifiedCoconeRightPrefixTriangleComparisonExtensionEdge hp p c hc dB dC).edge)).trans
      (congrArg (fun z ↦ (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ z)
        (specifiedCoconeRightPrefixTriangleComparisonExtensionEdge_uncurry hp p c hc dB dC))

/-- 同じ円柱の長辺制限の類は、元の長辺の比較同型の射そのもの。 -/
lemma specifiedCoconeRightPrefixTriangleComparisonExtensionEdge_long_homMk :
    SSet.Truncated.HomotopyCategory.homMk
        (((specifiedCoconeRightPrefixTriangleComparisonExtensionEdge hp p c hc dB dC).map
          (specifiedCoconeRightPrefixTriangleLongRestriction hp p c hc dB dC)).toTruncated) =
      (specifiedCoconeRightPrefixTriangleLongComparisonIso hp p c hc dB dC).hom := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRestriction_edge_homMk q β
    (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 2)) v hv
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleLongInitial_leftAnodyne _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeInitial_leftAnodyne
    (specifiedCoconeRightPrefixTriangleComparisonExtensionEdge hp p c hc dB dC)
  exact h.trans (congrArg Iso.hom
    (specifiedCoconeRightPrefixTriangleLongComparisonIso_eq hp p c hc dB dC)).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

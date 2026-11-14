module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorResolvedInput
public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.ContractingElementCriterion

/-!
概要：resolved 商の実 thick 平坦核から固定 S 内の零化四角形を構成する。
方針：D-16 の同じ零対象核から収縮元を選び、Sp 正本の全対象商の構成へ渡す。
規約：元対角始域との比較・零角の Perf 零性・長方形全体は別に照合する。
使われ方：K-10 d④ の resolved 射影を持つ実面の供給。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal_isExactFunctor R d
local notation "P" => dgQuotientImage R
  (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R (DGOdotGluing R d) (P)
local notation "T" => DGCategoryCellResolution.Source R (DGOdotGluing R d)
local notation "Q" => DGQuotient.QuotientObject (T)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d) (P))
local notation "j" => DGQuotient.inclusion R (T)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d) (P))

/-- 概要：同じ実 thick 平坦核を固定 S の対象にする。
方針：元の全 Hom を保つ宇宙持ち上げ。
規約：元対角の始域と同一視しない。使われ方：resolved 零化面の左端。 -/
def dgOdotMilnorFlatKernelInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, u + 1, u + 1} R (K)

/-- 概要：同じ平坦核包含を固定 S の実辺にする。
方針：D-16 の strict dg 包含をそのまま持ち上げる。
規約：生成対象集合だけで thick 核を置換しない。使われ方：零化面の下辺。 -/
def dgOdotMilnorFlatKernelInputMap :
    dgOdotMilnorFlatKernelInput R d ⟶ dgOdotMilnorCellInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R (DGOdotGluing R d) (P)))

/-- 概要：元 gluing 内で実平坦核の本質像は元対角の本質像と一致する。
方針：同じ resolved 射影の D-16 と Milnor の二つの零対象反映を照合する。
規約：S 内の比較関手の存在とは区別する。使われ方：元対角始域を保持する比較境界。 -/
lemma dgOdotMilnorFlatKernel_image_eq_diagonal (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    {b : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d)) _⦋0⦌ |
      ∃ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (K)) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickKernelInclusion R (DGOdotGluing R d) (P))).app
            (Opposite.op ⦋0⦌) a) b)} =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal R d) := by
  ext b
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_zero_iff_thickEssentialImage R
    (DGOdotGluing R d) (P) b).symm.trans (dgOdotMilnorNativeKernel R d h b)

/-- 概要：同じ thick 核の各対象の商像には実際の収縮元がある。
方針：D-16 の零対象反映と D の収縮元判定を使う。
規約：対象ごとの収縮を自然変換とは扱わない。使われ方：全対象商からの延長。 -/
lemma dgOdotMilnorFlatKernelImage_contractible (x : K) :
    ∃ h : GradedHom R ((j).obj x.val) ((j).obj x.val) (-1),
      (homObject R (Q) ((j).obj x.val) ((j).obj x.val)).d (-1) 0 h =
        (unitElement R ((j).obj x.val)).val := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isZeroVertex_iff_contractingElement _).mp
  have hx := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection_vertex_isZero_iff_thick
    R (DGOdotGluing R d) (P) x.val).2 x.property
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (j)).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x.val)) at hx
  rwa [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at hx

/-- 概要：resolved 商合成に同じ実核の収縮を指定する。
方針：対象ごとの証明済み収縮を選び全対象商の入力に束ねる。
規約：固定 S 内の自然な収縮を仮定しない。使われ方：Sp の実零化四角形構成。 -/
def dgOdotMilnorFlatKernelContracted :
    DGQuotient.ContractedFunctor R (dgOdotMilnorFlatKernelInput R d) Set.univ
      (dgOdotMilnorResolvedInput R d) where
  toDGFunctor := (dgOdotMilnorFlatKernelInputMap R d).down.comp
    (dgOdotMilnorCellProjectionInputMap R d).down
  homotopy x := (dgOdotMilnorFlatKernelImage_contractible R d x.val.label.down).choose
  d_homotopy x := (dgOdotMilnorFlatKernelImage_contractible R d x.val.label.down).choose_spec

/-- 概要：同じ平坦核包含・resolved 商包含を全一単体で保つ実 S 四角形。
方針：Sp の全対象商を通る厳密合成の構成を適用する。
規約：元対角始域との比較と零角の Perf 零性はここでは結論しない。
使われ方：ofSquare に渡す前の具体的な resolved 零化面。 -/
theorem exists_dgOdotMilnorFlatKernelNullSquare :
    ∃ F : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorCellProjectionInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := dgOdotMilnorFlatKernelInput R d))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))).edge :=
  exists_dgFixedNullSquare R (dgOdotMilnorFlatKernelInputMap R d)
    (dgOdotMilnorCellProjectionInputMap R d) (dgOdotMilnorFlatKernelContracted R d) rfl

end SerrePositivity.KST.SConstruction

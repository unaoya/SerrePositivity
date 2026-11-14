module
public import SerrePositivity.KST.NonConnective.DGKappaSplitModuleEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquareData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Triangles.DGModuleTriangleComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.TriangleExt

/-!
概要：同じラベル作用の閉分裂四角形を、D-12 用の実加群二胞体として保持する。
方針：元の四辺と零対角、零の全 dg 自然ホモトピーから四角形データを作る。
規約：汎用分裂 cofiber 判定を新設せず、その供給だけを明示入力とする。
使われ方：D-12 の判定を元の native Perf 分裂四角形へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (X : PresentedPerfectDGObject R (DGKappaCone R D I))

/-- 元の閉四辺と零の二胞体成分を保持した、D 正本の実加群四角形。 -/
def dgKappaSplitModuleSquareData (Z : DGKappaZeroInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData R (DGKappaCone R D I)
      ((dgKappaModuleLabelAction R D I X).onClosed.obj
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (A := R) (DGKappaCone R D I))))
      ((dgKappaModuleLabelAction R D I X).onClosed.obj
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgKappaSwindleSource R D I)))
      ((dgKappaModuleLabelAction R D I X).onClosed.obj
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgKappaZeroFunctor R D I Z)))
      ((dgKappaModuleLabelAction R D I X).onClosed.obj
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgKappaConeCountableSum R D I))) where
  bottom := (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitHead R D I)
  right := (dgKappaModuleLabelAction R D I X).onClosed.map (dgKappaSplitTailProjection R D I)
  left := 0
  top := 0
  diagonal := 0
  lowerHomotopy := 0
  upperHomotopy := 0
  lowerEquation := by rw [dgKappaSplitModule_head_tail, sub_self]; exact map_zero _
  upperEquation := by rw [zero_comp, sub_self]; exact map_zero _

/-- 元の実零自己関手の同じ加群ラベル作用は、閉圏で零対象を返す。 -/
theorem dgKappaSplitModule_zero_isZero (Z : DGKappaZeroInput R D I) :
    IsZero ((dgKappaModuleLabelAction R D I X).onClosed.obj
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgKappaZeroFunctor R D I Z))) :=
  (dgKappaModuleLabelAction R D I X).onClosed.map_isZero
    (dgKappaZeroFunctor_isZero R D I Z)

/-- D-12 に渡す元の零角は、同じ実右 dg 加群 nerve の零頂点。 -/
theorem dgKappaSplitModule_zero_isZeroVertex (Z : DGKappaZeroInput R D I) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R (DGKappaCone R D I))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((dgKappaModuleLabelAction R D I X).obj (dgKappaZeroFunctor R D I Z))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isZeroVertex_of_closed_isZero _ (dgKappaSplitModule_zero_isZero R D I X Z)

/-- 元の下側閉二単体の全ラベル作用は、指定した零原始元の実加群二胞体に等しい。 -/
theorem dgKappaSplitModuleSquareData_lower (Z : DGKappaZeroInput R D I) :
    (dgKappaSplitModuleSquareData R D I X Z).lowerTriangle =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex ((dgKappaSplitClosedLower R D I) ⋙
        (dgKappaModuleLabelAction R D I X).onClosed) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i
    fin_cases i <;> rfl
  · rfl
  · rfl
  · change HEq _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom
      ((dgKappaModuleLabelAction R D I X).onClosed.map
        (dgKappaSplitHead R D I ≫ dgKappaSplitTailProjection R D I)) 0)
    rw [dgKappaSplit_head_tail, CategoryTheory.Functor.map_zero]
    rfl
  · rfl

/-- 元の上側閉二単体の全ラベル作用も、同じ零角と零原始元の実二胞体に等しい。 -/
theorem dgKappaSplitModuleSquareData_upper (Z : DGKappaZeroInput R D I) :
    (dgKappaSplitModuleSquareData R D I X Z).upperTriangle =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex ((dgKappaSplitClosedUpper R D I Z) ⋙
        (dgKappaModuleLabelAction R D I X).onClosed) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i
    fin_cases i <;> rfl
  · change HEq _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((dgKappaModuleLabelAction R D I X).onClosed.map 0) 0)
    rw [CategoryTheory.Functor.map_zero]
    rfl
  · change HEq _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((dgKappaModuleLabelAction R D I X).onClosed.map 0) 0)
    rw [CategoryTheory.Functor.map_zero]
    rfl
  · change HEq _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((dgKappaModuleLabelAction R D I X).onClosed.map (0 ≫ 0)) 0)
    rw [zero_comp, CategoryTheory.Functor.map_zero]
    rfl
  · rfl

/-- D-12 用の全二胞体データは、元の点ごとの native 四角形の実加群像そのもの。 -/
theorem dgKappaSplitModuleSquareData_square (Z : DGKappaZeroInput R D I) :
    (dgKappaSplitModuleSquareData R D I X Z).square =
      dgKappaSplitModuleSquare R D I X Z := by
  rw [dgKappaSplitModuleSquare_closed]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_upper, dgKappaSplitModuleSquareData_upper]
    simp only [← Category.assoc, dgKappaSplitClosedSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc]
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
    rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData.square_lower, dgKappaSplitModuleSquareData_lower]
    simp only [← Category.assoc, dgKappaSplitClosedSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc]
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
    rfl

/-- D-12 の供給待ちの、元のラベルごとの指定二胞体に対する cofiber 入力。
対象と射の存在は既存の明示入力のまま保持し、汎用判定の証明を含めない。 -/
structure DGKappaSplitCofiberInput : Prop where
  isPushout (Z : DGKappaZeroInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgKappaSplitModuleSquareData R D I X Z).square

/-- D-12 用の同じ実加群四角形の判定を、元の native Perf 四角形へ反映する。 -/
theorem dgKappaSplitPerfPointwiseSquare_isPushout_of_input
    (H : DGKappaSplitCofiberInput R D I X) (Z : DGKappaZeroInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgKappaSplitPerfPointwiseSquare R D I X Z) := by
  apply dgKappaSplitPerfPointwiseSquare_isPushout_of_module R D I X Z
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgKappaSplitModuleSquare R D I X Z)
  rw [← dgKappaSplitModuleSquareData_square]
  exact H.isPushout Z

/-- 同じ点ごとの零三角形は、D-12 の明示入力の下で cofiber 列となる。 -/
theorem dgKappaSplitPerfPointwiseZeroTriangle_isCofiber_of_input
    (H : DGKappaSplitCofiberInput R D I X) (Z : DGKappaZeroInput R D I) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence (dgKappaSplitPerfPointwiseZeroTriangle R D I X Z) :=
  dgKappaSplitPerfPointwiseSquare_isPushout_of_input R D I X H Z

end SerrePositivity.KST.NonConnective

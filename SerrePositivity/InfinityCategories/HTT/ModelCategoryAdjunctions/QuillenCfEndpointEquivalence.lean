module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfEndpointFiber

/-!
概要：cf 対応圏の両端 fiber を、元の C・D の cf 対象圏の nerve と同型で同定する。
方針：各段の対象と元の cf 対象を厳密に往復させ、Hom の恒等写像で豊穣化。
規約：同型の全空間への合成は元の包含。使われ方：HTT 5.2.4.6 の cf 圏上の随伴。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable {D : Type v} [Category.{u} D] [SimplicialCategory D]
  [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C)
/-- 反対の段の元の対象は指定端点の部分圏に属さない。 -/
lemma quillenCfCollageTop_not_bottomEndpoint (X : D)
    (hX : HomotopicalAlgebra.IsCofibrant X ∧ HomotopicalAlgebra.IsFibrant X) :
    ¬ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfEndpointObjects R 0 ⟨.inr X, hX⟩ := by
  intro h
  change (ULift.up (1 : Fin 2) : ULift.{max u v} _) = ULift.up 0 at h
  exact (by decide : (1 : Fin 2) ≠ 0) (congrArg ULift.down h)

/-- 元の cf 対象から、同じ対象・Hom を持つ端点部分圏への豊穣関手。 -/
def quillenCfBottomToEndpoint :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfEndpointCategory R 0) where
  obj X := ⟨(_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj X, rfl⟩
  map := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).map
  map_id := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).map_id
  map_comp := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).map_comp

/-- 指定段の端点部分圏から元の cf 対象圏へ戻す豊穣関手。 -/
def quillenCfBottomFromEndpoint :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfEndpointCategory R 0) (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) where
  obj X := by
    rcases X with ⟨⟨X, hX⟩, hS⟩
    rcases X with X | X
    · exact ⟨X, hX⟩
    · exact False.elim (quillenCfCollageTop_not_bottomEndpoint R X hX hS)
  map X Y := by
    rcases X with ⟨⟨X, hX⟩, hS⟩
    rcases Y with ⟨⟨Y, hY⟩, hT⟩
    rcases X with X | X <;> rcases Y with Y | Y
    all_goals first
      | exact False.elim (quillenCfCollageTop_not_bottomEndpoint R X hX hS)
      | exact False.elim (quillenCfCollageTop_not_bottomEndpoint R Y hY hT)
      | exact 𝟙 _
  map_id X := by
    rcases X with ⟨⟨X, hX⟩, hS⟩
    rcases X with X | X
    all_goals first
      | exact False.elim (quillenCfCollageTop_not_bottomEndpoint R X hX hS)
      | exact Category.comp_id _
  map_comp X Y Z := by
    rcases X with ⟨⟨X, hX⟩, hS⟩
    rcases Y with ⟨⟨Y, hY⟩, hT⟩
    rcases Z with ⟨⟨Z, hZ⟩, hU⟩
    rcases X with X | X <;> rcases Y with Y | Y <;> rcases Z with Z | Z
    all_goals first
      | exact False.elim (quillenCfCollageTop_not_bottomEndpoint R X hX hS)
      | exact False.elim (quillenCfCollageTop_not_bottomEndpoint R Y hY hT)
      | exact False.elim (quillenCfCollageTop_not_bottomEndpoint R Z hZ hU)
      | (simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]; rfl)

/-- 元の cf 対象圏から端点部分圏への往復は恒等豊穣関手。 -/
lemma quillenCfBottomToFromEndpoint :
    (quillenCfBottomToEndpoint R).comp SSet (quillenCfBottomFromEndpoint R) =
      EnrichedFunctor.id SSet (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  simp [quillenCfBottomToEndpoint, quillenCfBottomFromEndpoint,
        EnrichedFunctor.comp, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom]

/-- 端点部分圏から元の cf 対象圏への往復も恒等豊穣関手。 -/
lemma quillenCfBottomFromToEndpoint :
    (quillenCfBottomFromEndpoint R).comp SSet (quillenCfBottomToEndpoint R) =
      EnrichedFunctor.id SSet (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfEndpointCategory R 0) := by
  apply EnrichedFunctor.ext SSet
  case h_obj =>
    rintro ⟨⟨X, hX⟩, hS⟩
    rcases X with X | X
    all_goals first
      | exact False.elim (quillenCfCollageTop_not_bottomEndpoint R X hX hS)
      | rfl
  case h_map =>
    rintro ⟨⟨X, hX⟩, hS⟩ ⟨⟨Y, hY⟩, hT⟩
    rcases X with X | X <;> rcases Y with Y | Y
    all_goals first
      | exact False.elim (quillenCfCollageTop_not_bottomEndpoint R X hX hS)
      | exact False.elim (quillenCfCollageTop_not_bottomEndpoint R Y hY hT)
      | (simp [quillenCfBottomToEndpoint, quillenCfBottomFromEndpoint,
        EnrichedFunctor.comp, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom]; rfl)

/-- 元の cf 対象圏の nerve と指定段の部分圏の nerve の厳密な同型。 -/
def quillenCfBottomEndpointNerveIso :
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) ≅
      SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfEndpointCategory R 0) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (quillenCfBottomToEndpoint R)
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (quillenCfBottomFromEndpoint R)
  hom_inv_id := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, quillenCfBottomToFromEndpoint, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_id]
  inv_hom_id := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, quillenCfBottomFromToEndpoint, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_id]

/-- 元の cf 対象圏の coherent nerve と、元の区間射影の端点 fiber の同型。 -/
def quillenCfBottomFiberIso :
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
  quillenCfBottomEndpointNerveIso R ≪≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfEndpointFiberIso R 0

/-- 反対の段の元の対象は指定端点の部分圏に属さない。 -/
lemma quillenCfTopEndpoint_wrong (X : C)
    (hX : HomotopicalAlgebra.IsCofibrant X ∧ HomotopicalAlgebra.IsFibrant X) :
    ¬ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfEndpointObjects R 1 ⟨.inl X, hX⟩ := by
  intro h
  change (ULift.up (0 : Fin 2) : ULift.{max u v} _) = ULift.up 1 at h
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down h)

/-- 元の cf 対象から、同じ対象・Hom を持つ端点部分圏への豊穣関手。 -/
def quillenCfTopToEndpoint :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfEndpointCategory R 1) where
  obj X := ⟨(_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj X, rfl⟩
  map := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).map
  map_id := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).map_id
  map_comp := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).map_comp

/-- 指定段の端点部分圏から元の cf 対象圏へ戻す豊穣関手。 -/
def quillenCfTopFromEndpoint :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfEndpointCategory R 1) (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) where
  obj X := by
    rcases X with ⟨⟨X, hX⟩, hS⟩
    rcases X with X | X
    · exact False.elim (quillenCfTopEndpoint_wrong R X hX hS)
    · exact ⟨X, hX⟩
  map X Y := by
    rcases X with ⟨⟨X, hX⟩, hS⟩
    rcases Y with ⟨⟨Y, hY⟩, hT⟩
    rcases X with X | X <;> rcases Y with Y | Y
    all_goals first
      | exact False.elim (quillenCfTopEndpoint_wrong R X hX hS)
      | exact False.elim (quillenCfTopEndpoint_wrong R Y hY hT)
      | exact 𝟙 _
  map_id X := by
    rcases X with ⟨⟨X, hX⟩, hS⟩
    rcases X with X | X
    all_goals first
      | exact False.elim (quillenCfTopEndpoint_wrong R X hX hS)
      | exact Category.comp_id _
  map_comp X Y Z := by
    rcases X with ⟨⟨X, hX⟩, hS⟩
    rcases Y with ⟨⟨Y, hY⟩, hT⟩
    rcases Z with ⟨⟨Z, hZ⟩, hU⟩
    rcases X with X | X <;> rcases Y with Y | Y <;> rcases Z with Z | Z
    all_goals first
      | exact False.elim (quillenCfTopEndpoint_wrong R X hX hS)
      | exact False.elim (quillenCfTopEndpoint_wrong R Y hY hT)
      | exact False.elim (quillenCfTopEndpoint_wrong R Z hZ hU)
      | (simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]; rfl)

/-- 元の cf 対象圏から端点部分圏への往復は恒等豊穣関手。 -/
lemma quillenCfTopToFromEndpoint :
    (quillenCfTopToEndpoint R).comp SSet (quillenCfTopFromEndpoint R) =
      EnrichedFunctor.id SSet (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  simp [quillenCfTopToEndpoint, quillenCfTopFromEndpoint,
        EnrichedFunctor.comp, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop]

/-- 端点部分圏から元の cf 対象圏への往復も恒等豊穣関手。 -/
lemma quillenCfTopFromToEndpoint :
    (quillenCfTopFromEndpoint R).comp SSet (quillenCfTopToEndpoint R) =
      EnrichedFunctor.id SSet (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfEndpointCategory R 1) := by
  apply EnrichedFunctor.ext SSet
  case h_obj =>
    rintro ⟨⟨X, hX⟩, hS⟩
    rcases X with X | X
    all_goals first
      | exact False.elim (quillenCfTopEndpoint_wrong R X hX hS)
      | rfl
  case h_map =>
    rintro ⟨⟨X, hX⟩, hS⟩ ⟨⟨Y, hY⟩, hT⟩
    rcases X with X | X <;> rcases Y with Y | Y
    all_goals first
      | exact False.elim (quillenCfTopEndpoint_wrong R X hX hS)
      | exact False.elim (quillenCfTopEndpoint_wrong R Y hY hT)
      | (simp [quillenCfTopToEndpoint, quillenCfTopFromEndpoint,
        EnrichedFunctor.comp, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop]; rfl)

/-- 元の cf 対象圏の nerve と指定段の部分圏の nerve の厳密な同型。 -/
def quillenCfTopEndpointNerveIso :
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) ≅
      SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfEndpointCategory R 1) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (quillenCfTopToEndpoint R)
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (quillenCfTopFromEndpoint R)
  hom_inv_id := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, quillenCfTopToFromEndpoint, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_id]
  inv_hom_id := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, quillenCfTopFromToEndpoint, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_id]

/-- 元の cf 対象圏の coherent nerve と、元の区間射影の端点 fiber の同型。 -/
def quillenCfTopFiberIso :
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
  quillenCfTopEndpointNerveIso R ≪≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfEndpointFiberIso R 1

/-- 端点部分圏への豊穣関手と包含の合成は元の段の包含。 -/
lemma quillenCfBottomToEndpoint_inclusion :
    (quillenCfBottomToEndpoint R).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryInclusion (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfEndpointObjects R 0)) =
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  simp [quillenCfBottomToEndpoint, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryInclusion, EnrichedFunctor.comp]

/-- cf 圏と端点 fiber の同型は、全空間への元の包含に厳密に一致する。 -/
lemma quillenCfBottomFiberIso_hom_ι :
    (quillenCfBottomFiberIso R).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (quillenCfBottomToEndpoint R) ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfEndpointFiberIso R 0).hom) ≫ _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfEndpointFiberIso_hom_ι]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (quillenCfBottomToEndpoint R) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryInclusion _) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, quillenCfBottomToEndpoint_inclusion]
  rfl

/-- 端点部分圏への豊穣関手と包含の合成は元の段の包含。 -/
lemma quillenCfTopToEndpoint_inclusion :
    (quillenCfTopToEndpoint R).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryInclusion (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfEndpointObjects R 1)) =
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  simp [quillenCfTopToEndpoint, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryInclusion, EnrichedFunctor.comp]

/-- cf 圏と端点 fiber の同型は、全空間への元の包含に厳密に一致する。 -/
lemma quillenCfTopFiberIso_hom_ι :
    (quillenCfTopFiberIso R).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (quillenCfTopToEndpoint R) ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfEndpointFiberIso R 1).hom) ≫ _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfEndpointFiberIso_hom_ι]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (quillenCfTopToEndpoint R) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryInclusion _) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, quillenCfTopToEndpoint_inclusion]
  rfl

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.2.4.6" (partial := stronger-hyp) "仮定：二つの単体模型圏と単体的 Quillen 随伴（Lean が強い：固定 tensor/cotensor、固定 SM7、Hom 随伴の合成互換、および関手的な両側の分解を明示入力）。結論：原典と同じ cf 対応の射影が Cartesian かつ coCartesian で、両端ファイバーが元の cf nerve と同型（この入力の下で一致）。具体例に使う ModelCategory instance なし：SSet の Kan–Quillen 入力は sorry に依存し、本行でそれを実在する instance としては数えない。"] _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso
attribute [cite HTT "5.2.4.6" (partial := stronger-hyp) "仮定：二つの単体模型圏と単体的 Quillen 随伴（Lean が強い：固定 tensor/cotensor、固定 SM7、Hom 随伴の合成互換、および関手的な両側の分解を明示入力）。結論：原典と同じ cf 対応の射影が Cartesian かつ coCartesian で、両端ファイバーが元の cf nerve と同型（この入力の下で一致）。具体例に使う ModelCategory instance なし：SSet の Kan–Quillen 入力は sorry に依存し、本行でそれを実在する instance としては数えない。"] _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso

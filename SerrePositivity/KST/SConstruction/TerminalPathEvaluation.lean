module
public import SerrePositivity.KST.SConstruction.TerminalPathSpace
public import SerrePositivity.KST.Comparison.PointedUnitEvaluation
public import SerrePositivity.KST.Spectra.PointedMappingParameters

/-! # 終点固定 path の族と元の始点評価
概要：終点を基点に送る元の区間族を path 空間へ curry し、始点評価を厳密に計算する。
方針：点つき内部 Hom の包含と、点つき単位の非基点評価を使う。
規約：元の区間の向きと任意のパラメータを保つ。使われ方：零行収縮による fiber ホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

/-- 終点固定 path の始点評価は通常の指数の頂点零での評価。 -/
lemma terminalPathStart_evaluation (B : PointedSimplicialSet.{u}) :
    (terminalPathStart B).right = PointedObject.basedHomι terminalPointedInterval B ≫
      Spectra.KanPath.evaluation B.right 0 := by
  rw [terminalPathStart, Under.comp_right, Comparison.pointedUnitIso_evaluation]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre terminalIntervalStart B ≫
    (PointedObject.basedHomι (𝟙_ PointedSimplicialSet.{u}) B ≫
      (MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶
        (𝟙_ PointedSimplicialSet.{u}).right)).app B.right ≫
          (MonoidalClosed.unitIsoSelf (X := B.right)).hom) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, Category.assoc]
  have he : (MonoidalClosed.pre terminalIntervalStart.right).app B.right ≫
      (MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶
        (𝟙_ PointedSimplicialSet.{u}).right)).app B.right =
      (MonoidalClosed.pre (Spectra.KanPath.endpoint 0)).app B.right := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, terminalIntervalStart_inl]
    rfl
  change PointedObject.basedHomι terminalPointedInterval B ≫
    (MonoidalClosed.pre terminalIntervalStart.right).app B.right ≫
    (MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶
      (𝟙_ PointedSimplicialSet.{u}).right)).app B.right ≫
      (MonoidalClosed.unitIsoSelf (X := B.right)).hom = _
  rw [← Category.assoc _ _ (MonoidalClosed.unitIsoSelf (X := B.right)).hom, he]
  rfl

/-- 終点が基点の区間族は終点基点の区間からの写像族の条件を満たす。 -/
lemma terminalPathFamily_basepoint {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right)
    (h₁ : SSet.ι₁ ≫ h = toUnit A ≫ B.hom) :
    terminalPointedInterval.hom ▷ A ≫ (β_ (Δ[1] : SSet.{u}) A).hom ≫ h =
      toUnit ((𝟙_ SSet.{u}) ⊗ A) ≫ B.hom := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro p
  exact congrArg (fun k => k.app d p.2) h₁

/-- 終点を基点に送る元の区間族の点つき curry。 -/
def terminalPathFamily {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right)
    (h₁ : SSet.ι₁ ≫ h = toUnit A ≫ B.hom) : A ⟶ (terminalPathSpace B).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry terminalPointedInterval B
    ((β_ (Δ[1] : SSet.{u}) A).hom ≫ h) (terminalPathFamily_basepoint B h h₁)

/-- 終点固定 path の族の通常の指数への包含。 -/
lemma terminalPathFamily_ι {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₁) :
    terminalPathFamily B h h₁ ≫ PointedObject.basedHomι terminalPointedInterval B =
      curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ h) :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι ..

/-- 終点固定 path の族を始点で評価すると元の区間族の始点を回収する。 -/
lemma terminalPathFamily_start {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₁) :
    terminalPathFamily B h h₁ ≫ (terminalPathStart B).right = SSet.ι₀ ≫ h := by
  rw [terminalPathStart_evaluation, ← Category.assoc, terminalPathFamily_ι,
    Spectra.KanPath.evaluation, ← Category.assoc, curry_pre_app,
    Spectra.KanPath.curry_unit_evaluation]
  have he : (λ_ A).inv ≫ Spectra.KanPath.endpoint 0 ▷ A ≫
      (β_ (Δ[1] : SSet.{u}) A).hom = SSet.ι₀ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  simpa only [Category.assoc] using congrArg (fun f => f ≫ h) he

end SerrePositivity.KST.SConstruction

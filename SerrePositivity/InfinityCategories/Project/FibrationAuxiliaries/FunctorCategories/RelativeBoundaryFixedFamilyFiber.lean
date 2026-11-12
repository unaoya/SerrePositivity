module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeBoundaryFamilySpace

/-!
概要：動く分類図式の境界固定 lift 空間と、動く底の四角形空間の境界 fiber の同型。
方針：底と境界の二つの固定条件を引き戻しと頂点 fiber に並べ直す。
規約：底の族全体を保ち境界だけを定値に固定する。
使われ方：実際の区間族の相対 lift を円柱の両端制限 fiber へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：定値な境界を持つ族の lift 空間は動く底の全四角形の境界 fiber と同型。
方針：二つの普遍性で互いに逆の射を作る。
規約：分類図式の族 a は任意で定値性を要求しない。
使われ方：円柱の実際の境界制限の fiber との同定の一般形。 -/
def relativeBoundaryFixedFamilyFiberIso {A C E B L : SSet.{u}}
    (i : C ⟶ A) (p : E ⟶ B) (r : internalHom.PullbackObjObj i p)
    (v : C ⟶ E) (a : L ⟶ (ihom A).obj B)
    (h : (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v) : L ⟶ _) ≫ (ihom C).map p = a ≫ (pre i).app B) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilySpace r
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData i p r (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) a h) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.fst ((ihom A).map p) a ≫ (pre i).app E) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v) := by
  let d := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData i p r (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) a h
  let S := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilySpace r d
  let cS := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyCurry r d
  let pS := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyProjection r d
  let Q := pullback ((ihom A).map p) a
  let q₀ : Q ⟶ (ihom A).obj E := pullback.fst _ _
  let q₁ : Q ⟶ L := pullback.snd _ _
  let ρ := q₀ ≫ (pre i).app E
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ρ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)
  let ιT := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ρ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)
  have hc : cS ≫ (ihom A).map p = pS ≫ a := by
    have hd := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData_snd i p r (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) a h
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyCurry_base r d).trans (congrArg (fun w ↦ pS ≫ w) hd)
  have hb : cS ≫ (pre i).app E = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v) := by
    have hd := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData_fst i p r (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) a h
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyCurry_boundary r d).trans
      ((congrArg (fun w ↦ pS ≫ w) hd).trans (SSet.comp_const _ _))
  let F₀ : S ⟶ Q := pullback.lift cS pS hc
  have hF₀ : F₀ ≫ q₀ = cS := pullback.lift_fst _ _ _
  have hF₁ : F₀ ≫ q₁ = pS := pullback.lift_snd _ _ _
  have hFρ : F₀ ≫ ρ = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v) := by
    change F₀ ≫ q₀ ≫ (pre i).app E = _
    rw [← Category.assoc, hF₀]
    exact hb
  let F : S ⟶ T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift ρ _ F₀ hFρ
  have hF : F ≫ ιT = F₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hGcond : (ιT ≫ q₀) ≫ r.π = (ιT ≫ q₁) ≫ d := by
    apply r.hom_ext
    · rw [Category.assoc, r.π_fst, Category.assoc]
      change (ιT ≫ q₀) ≫ (pre i).app E = (ιT ≫ q₁) ≫ d ≫ r.fst
      have hd := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData_fst i p r (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) a h
      rw [hd, SSet.comp_const, Category.assoc]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp ρ _
    · rw [Category.assoc, r.π_snd, Category.assoc]
      change (ιT ≫ q₀) ≫ (ihom A).map p = (ιT ≫ q₁) ≫ d ≫ r.snd
      have hd := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData_snd i p r (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) a h
      rw [hd, Category.assoc]
      change ιT ≫ pullback.fst ((ihom A).map p) a ≫ (ihom A).map p = _
      rw [pullback.condition]
      exact (Category.assoc ιT q₁ a).symm
  let G : T ⟶ S := pullback.lift (ιT ≫ q₀) (ιT ≫ q₁) hGcond
  have hG₀ : G ≫ cS = ιT ≫ q₀ := pullback.lift_fst _ _ _
  have hG₁ : G ≫ pS = ιT ≫ q₁ := pullback.lift_snd _ _ _
  refine { hom := F, inv := G, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply pullback.hom_ext
    · change (F ≫ G) ≫ cS = (𝟙 S) ≫ cS
      rw [Category.assoc, hG₀, ← Category.assoc, hF, hF₀, Category.id_comp]
    · change (F ≫ G) ≫ pS = (𝟙 S) ≫ pS
      rw [Category.assoc, hG₁, ← Category.assoc, hF, hF₁, Category.id_comp]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ρ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)
    apply pullback.hom_ext
    · change ((G ≫ F) ≫ ιT) ≫ q₀ = ((𝟙 T) ≫ ιT) ≫ q₀
      rw [Category.assoc G F ιT, hF, Category.assoc, hF₀, hG₀, Category.id_comp]
    · change ((G ≫ F) ≫ ιT) ≫ q₁ = ((𝟙 T) ≫ ιT) ≫ q₁
      rw [Category.assoc G F ιT, hF, Category.assoc, hF₁, hG₁, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

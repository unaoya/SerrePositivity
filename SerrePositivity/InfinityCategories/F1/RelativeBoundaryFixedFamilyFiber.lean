module

public import SerrePositivity.InfinityCategories.F1.RelativeBoundaryFamilySpace

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
namespace SerrePositivity.InfinityCategories

/-- 概要：定値な境界を持つ族の lift 空間は動く底の全四角形の境界 fiber と同型。
方針：二つの普遍性で互いに逆の射を作る。
規約：分類図式の族 a は任意で定値性を要求しない。
使われ方：円柱の実際の境界制限の fiber との同定の一般形。 -/
def relativeBoundaryFixedFamilyFiberIso {A C E B L : SSet.{u}}
    (i : C ⟶ A) (p : E ⟶ B) (r : internalHom.PullbackObjObj i p)
    (v : C ⟶ E) (a : L ⟶ (ihom A).obj B)
    (h : (SSet.const (functorVertex v) : L ⟶ _) ≫ (ihom C).map p = a ≫ (pre i).app B) :
    relativeBoundaryFamilySpace r
      (relativeBoundaryFamilyData i p r (SSet.const (functorVertex v)) a h) ≅
      vertexFiber (pullback.fst ((ihom A).map p) a ≫ (pre i).app E) (functorVertex v) := by
  let d := relativeBoundaryFamilyData i p r (SSet.const (functorVertex v)) a h
  let S := relativeBoundaryFamilySpace r d
  let cS := relativeBoundaryFamilyCurry r d
  let pS := relativeBoundaryFamilyProjection r d
  let Q := pullback ((ihom A).map p) a
  let q₀ : Q ⟶ (ihom A).obj E := pullback.fst _ _
  let q₁ : Q ⟶ L := pullback.snd _ _
  let ρ := q₀ ≫ (pre i).app E
  let T := vertexFiber ρ (functorVertex v)
  let ιT := vertexFiberι ρ (functorVertex v)
  have hc : cS ≫ (ihom A).map p = pS ≫ a := by
    have hd := relativeBoundaryFamilyData_snd i p r (SSet.const (functorVertex v)) a h
    exact (relativeBoundaryFamilyCurry_base r d).trans (congrArg (fun w ↦ pS ≫ w) hd)
  have hb : cS ≫ (pre i).app E = SSet.const (functorVertex v) := by
    have hd := relativeBoundaryFamilyData_fst i p r (SSet.const (functorVertex v)) a h
    exact (relativeBoundaryFamilyCurry_boundary r d).trans
      ((congrArg (fun w ↦ pS ≫ w) hd).trans (SSet.comp_const _ _))
  let F₀ : S ⟶ Q := pullback.lift cS pS hc
  have hF₀ : F₀ ≫ q₀ = cS := pullback.lift_fst _ _ _
  have hF₁ : F₀ ≫ q₁ = pS := pullback.lift_snd _ _ _
  have hFρ : F₀ ≫ ρ = SSet.const (functorVertex v) := by
    change F₀ ≫ q₀ ≫ (pre i).app E = _
    rw [← Category.assoc, hF₀]
    exact hb
  let F : S ⟶ T := vertexFiberLift ρ _ F₀ hFρ
  have hF : F ≫ ιT = F₀ := vertexFiberLift_ι _ _ _ _
  have hGcond : (ιT ≫ q₀) ≫ r.π = (ιT ≫ q₁) ≫ d := by
    apply r.hom_ext
    · rw [Category.assoc, r.π_fst, Category.assoc]
      change (ιT ≫ q₀) ≫ (pre i).app E = (ιT ≫ q₁) ≫ d ≫ r.fst
      have hd := relativeBoundaryFamilyData_fst i p r (SSet.const (functorVertex v)) a h
      rw [hd, SSet.comp_const, Category.assoc]
      exact vertexFiberι_comp ρ _
    · rw [Category.assoc, r.π_snd, Category.assoc]
      change (ιT ≫ q₀) ≫ (ihom A).map p = (ιT ≫ q₁) ≫ d ≫ r.snd
      have hd := relativeBoundaryFamilyData_snd i p r (SSet.const (functorVertex v)) a h
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
  · apply vertexFiber_hom_ext ρ (functorVertex v)
    apply pullback.hom_ext
    · change ((G ≫ F) ≫ ιT) ≫ q₀ = ((𝟙 T) ≫ ιT) ≫ q₀
      rw [Category.assoc G F ιT, hF, Category.assoc, hF₀, hG₀, Category.id_comp]
    · change ((G ≫ F) ≫ ιT) ≫ q₁ = ((𝟙 T) ≫ ιT) ≫ q₁
      rw [Category.assoc G F ιT, hF, Category.assoc, hF₁, hG₁, Category.id_comp]

end SerrePositivity.InfinityCategories

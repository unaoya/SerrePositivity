module

public import SerrePositivity.InfinityCategories.F2.Presentable.RightKanDensityRestriction
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafDensityLeftKanCriterion
public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalentConeRestriction
public import SerrePositivity.InfinityCategories.Core.CatInfinity.ConeValEquality
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RightCanonicalMapping

/-!
概要：反対前層圏の密度錐の保存から元の反対 Yoneda の右 Kan 条件を導く。
方針：小さい elements 比較を反転し、標準右 Kan 錐を同じ密度錐の像へ制限する。
規約：標的の全小極限や表現可能性は仮定しない。
使われ方：連続な前層の Yoneda 制限からの全自然な復元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {A : SSet.{u}} [Quasicategory A] {E : SSet.{u + 1}} [Quasicategory E]

/-- 概要：小さい元の圏の反転から反対 Yoneda の右 Kan 添字への比較。
方針：元の elements 比較の反転に局所形状の反転同型を合成する。
規約：元の前層 P の頂点を反転して保持する。
使われ方：右 Kan の標準錐を小さい密度錐へ制限する。 -/
def presheafElementsRightKanComparison
    (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u}) :
    ((SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening P)).op ⟶
      rightKanShape (SSet.opFunctor.map (yonedaInfinityMap A))
        (SSet.opObjEquiv.symm (functorVertex P)) :=
  SSet.opFunctor.map (presheafElementsLeftKanComparison P) ≫
    (F1B.kanLeftKanShapeOpIso (yonedaInfinityMap A) (functorVertex P)).hom

local instance (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u}) :
    RightFibration (leftKanProjection (yonedaInfinityMap A) (functorVertex P)) :=
  ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p :=
    sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex P))))⟩

local instance (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u}) :
    Quasicategory (leftKanShape (yonedaInfinityMap A) (functorVertex P)) :=
  quasicategory_of_innerFibration (leftKanProjection (yonedaInfinityMap A) (functorVertex P))

local instance (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u}) :
    Quasicategory (rightKanShape (SSet.opFunctor.map (yonedaInfinityMap A))
      (SSet.opObjEquiv.symm (functorVertex P))) :=
  quasicategory_of_innerFibration
    (F1B.kanLeftKanShapeOpIso (yonedaInfinityMap A) (functorVertex P)).inv

omit [Quasicategory E] in
/-- 概要：反対密度の小さい元の圏と標準右 Kan 添字の比較は全同値。
方針：元の elements 比較の同値を反転し、形状の同型を合成する。
規約：実際の比較写像自身の同値性。
使われ方：元の標準右 Kan 錐の極限性の検出。 -/
lemma presheafElementsRightKanComparison_isQCatEquivalence
    (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence (presheafElementsRightKanComparison P) :=
  (presheafElementsLeftKanComparison_isQCatEquivalence P).opposite.comp
    (qCatEquivalenceOfIso (F1B.kanLeftKanShapeOpIso
      (yonedaInfinityMap A) (functorVertex P))).isQCatEquivalence

omit [Quasicategory E] in
/-- 概要：標準右 Kan 錐の小さい制限は同じ反対密度錐の像。
方針：標準局所錐の反転の等式と元の密度全余錐の等式を合成する。
規約：全錐の射として一致し、頂点だけの比較にはしない。
使われ方：密度錐の保存から標準右 Kan 極限条件への移送。 -/
lemma presheafRightKanCanonicalCone_restrict_val
    (F : (PresheafInfinity A).op ⟶ E)
    (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u}) :
    (restrictJoinCone (rightKanCanonicalCone (SSet.opFunctor.map (yonedaInfinityMap A)) F
      (SSet.opObjEquiv.symm (functorVertex P))) (presheafElementsRightKanComparison P)).val =
        (mapJoinCone F (F1B.coconeReverseCone (presheafDensityCocone P))).val := by
  have h := rightKanCanonicalCone_op_restrict_val (yonedaInfinityMap A) (functorVertex P)
    (presheafElementsLeftKanComparison P)
  have hd := presheafLeftKanCanonicalCocone_restrict_val (𝟙 (PresheafInfinity A)) P
  change _ = (presheafDensityCocone P).val ≫ 𝟙 _ at hd
  have hd₀ : ((leftKanCanonicalCocone (yonedaInfinityMap A) (𝟙 _) (functorVertex P)).restrict
      (presheafElementsLeftKanComparison P)).val = (presheafDensityCocone P).val :=
    hd.trans (Category.comp_id _)
  have hr : (F1B.coconeReverseCone ((leftKanCanonicalCocone (yonedaInfinityMap A)
      (𝟙 _) (functorVertex P)).restrict (presheafElementsLeftKanComparison P))).val =
      (F1B.coconeReverseCone (presheafDensityCocone P)).val := by
    rw [F1B.coconeReverseCone_val, F1B.coconeReverseCone_val]
    exact congrArg (fun g ↦ joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 _) ≫
      (stableJoinReverseIso _ Δ[0]).inv ≫ SSet.opFunctor.map g) hd₀
  exact (Category.assoc _ _ F).symm.trans ((congrArg (fun g ↦ g ≫ F) h).trans
    (congrArg (fun g ↦ g ≫ F) hr))

/-- 概要：反対密度錐を保つ関手の全標準右 Kan 錐は極限。
方針：同値な小さい元の圏へ制限し、指定した密度錐の像の普遍性を移す。
規約：元の関手 F の値と元の全標準錐を保持する。
使われ方：連続な前層の反対 Yoneda からの右 Kan 復元。 -/
lemma presheaf_oppositeDensityImages_canonicalLimits
    (F : (PresheafInfinity A).op ⟶ E)
    (hF : ∀ P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u},
      IsLimitCone (mapJoinCone F (F1B.coconeReverseCone (presheafDensityCocone P))))
    (v : (PresheafInfinity A).op _⦋0⦌) :
    IsLimitCone (rightKanCanonicalCone (SSet.opFunctor.map (yonedaInfinityMap A)) F v) := by
  obtain ⟨P, hP⟩ := (presheafInfinityObjectEquiv A).surjective (SSet.opObjEquiv v)
  change functorVertex P = SSet.opObjEquiv v at hP
  have hv : v = SSet.opObjEquiv.symm (functorVertex P) := by rw [hP]; rfl
  rw [hv]
  apply (isLimitCone_iff_restrict_equivalentShape (presheafElementsRightKanComparison P)
    (presheafElementsRightKanComparison_isQCatEquivalence P) _).mpr
  exact (F2.isLimitCone_iff_of_cone_val_eq _ _
    (presheafRightKanCanonicalCone_restrict_val F P)).mpr (hF P)

/-- 概要：反対密度錐を保つ関手は反対 Yoneda による制限上の同型から復元できる。
方針：右 Kan の Hom 全単射で順射と逆射を構成し、その制限で両逆を検出する。
規約：元の関手間の全自然同型を構成する。
使われ方：小余極限を小極限へ送る前層の表現同型の構成。 -/
def presheafOppositeDensityIsoOfYoneda
    {F G : (PresheafInfinity A).op ⟶ E}
    (hF : ∀ P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u},
      IsLimitCone (mapJoinCone F (F1B.coconeReverseCone (presheafDensityCocone P))))
    (hG : ∀ P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u},
      IsLimitCone (mapJoinCone G (F1B.coconeReverseCone (presheafDensityCocone P))))
    (e : FunctorIso (SSet.opFunctor.map (yonedaInfinityMap A) ≫ F)
      (SSet.opFunctor.map (yonedaInfinityMap A) ≫ G)) : FunctorIso F G := by
  let δ := SSet.opFunctor.map (yonedaInfinityMap A)
  let T := (hoFunctor.map ((pre δ).app E)).toFunctor
  have hf := F1B.kanRightCanonicalHomMap_bijective δ F
    (presheaf_oppositeDensityImages_canonicalLimits F hF)
  have hg := F1B.kanRightCanonicalHomMap_bijective δ G
    (presheaf_oppositeDensityImages_canonicalLimits G hG)
  let f := ((hg F).surjective e.hom).choose
  have hfe := ((hg F).surjective e.hom).choose_spec
  let g := ((hf G).surjective e.inv).choose
  have hge := ((hf G).surjective e.inv).choose_spec
  refine ⟨f, g, ?_, ?_⟩
  · apply (hf F).injective
    change T.map (f ≫ g) = T.map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, hfe, hge, e.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  · apply (hg G).injective
    change T.map (g ≫ f) = T.map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, hge, hfe, e.inv_hom_id, CategoryTheory.Functor.map_id]
    rfl

end SerrePositivity.InfinityCategories.F2.Presentable

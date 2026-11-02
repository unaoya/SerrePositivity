module
public import SerrePositivity.InfinityCategories.Derived.DGProjectiveModules
public import SerrePositivity.InfinityCategories.Derived.DGModuleCoproductStandardFan
public import SerrePositivity.InfinityCategories.Derived.DGStandardClosedPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteHomColimits
public import SerrePositivity.DifferentialGraded.Derived.Functor
/-!
概要：射影的 dg 加群の同じ直和と包含を coherent nerve の余積余錐へ送る。
方針：実 Hom の標準 DK 積表示と離散形状の豊穣余極限判定を使う。
規約：対象の Small 性や通常の compact 性を仮定しない。
使われ方：D-8 c5 の元の直和の native 余極限比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DoldKanComparison SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
variable {J : Type u}
local instance : SimplicialCategory (ClosedCategory R (ProjectiveDGModules R D)) :=
  doldKanSimplicialCategory
local instance : SimplicialCategory (ClosedCategory R (ProjectiveDGModules R D))ᵒᵖ :=
  EnrichedOrdinaryCategory.opposite SSet

abbrev dgProjectiveCoproductUnderlying (M : J → ProjectiveDGModules R D) :
    J → ModuleCategory R D := fun j => ForgetEnrichment.of (Complex R) (M j).val

def dgProjectiveCoproductObject (M : J → ProjectiveDGModules R D) :
    ProjectiveDGModules R D :=
  ⟨ForgetEnrichment.to (Complex R) (∐ dgProjectiveCoproductUnderlying R D M),
    moduleCoproduct_homotopicallyProjective R D _ (fun j => (M j).property)⟩

def dgProjectiveCoproductCofan (M : J → ProjectiveDGModules R D) :
    Cofan (fun j => ForgetEnrichment.of (Complex R) (M j)) :=
  Cofan.mk (ForgetEnrichment.of (Complex R) (dgProjectiveCoproductObject R D M))
    (fun j => ForgetEnrichment.homOf (Complex R)
      (ForgetEnrichment.homTo (Complex R) (Sigma.ι (dgProjectiveCoproductUnderlying R D M) j)))

lemma dgProjectiveCoproductHomProjection (M : J → ProjectiveDGModules R D)
    (N : ProjectiveDGModules R D) (j : J) :
    (HomotopyLimits.simplicialHomCone (dgProjectiveCoproductCofan R D M).op
      (Opposite.op (ForgetEnrichment.of (Complex R) N))).π.app ⟨j⟩ =
    dgStandardHomChainMap (eHomWhiskerRight (Complex R)
      (Sigma.ι (dgProjectiveCoproductUnderlying R D M) j)
      (ForgetEnrichment.of (Complex R) N.val)) := by
  ext n s
  change standardAW s ((standardHomSpace (R := R) (D := ProjectiveDGModules R D)
    (M j) (dgProjectiveCoproductObject R D M)).map
    (SimplexCategory.const ⦋n.unop.len⦌ ⦋0⦌ 0).op
      (closedStandardVertexEquiv (R := R) (D := ProjectiveDGModules R D)
        (M j) (dgProjectiveCoproductObject R D M)
        ((dgProjectiveCoproductCofan R D M).inj j))) = _
  rw [dgStandardClosedConstant_eq]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨L, k⟩, hL, hk⟩
  change (awData s.val
    (standardConstant (closedHomEquiv R (ProjectiveDGModules R D) _ _
      ((dgProjectiveCoproductCofan R D M).inj j)) _).val).component L k hL hk =
    (dgStandardSimplexMap _ s).val.component L k hL hk
  rw [awData_closed_pre_component, dgStandardSimplexMap_component]
  exact (dgGluingHomWhiskerRight_f R (RightModule R D)
    (x := (M j).val) (y := (dgProjectiveCoproductObject R D M).val) (z := N.val)
    (Sigma.ι (dgProjectiveCoproductUnderlying R D M) j) k
    (s.val.component L k hL hk)).symm

/-- 次数評価後の離散直積比較から、同じ型値錐の極限を組み立てる。 -/
def dgProjectiveCoproductTypeConeIsLimit {J : Type u} {F : (Discrete J)ᵒᵖ ⥤ Type u}
    (c : Cone F) (h : Function.Bijective (fun t : c.pt => fun j : J => c.π.app (Opposite.op ⟨j⟩) t)) :
    IsLimit c := by
  let e := Equiv.ofBijective _ h
  refine { lift := fun s => ↾fun t => e.symm (fun j => s.π.app (Opposite.op ⟨j⟩) t)
           fac := ?_, uniq := ?_ }
  · intro s j
    rcases j with ⟨⟨j⟩⟩
    apply ConcreteCategory.hom_ext
    intro t
    exact congrFun (e.apply_symm_apply (fun j => s.π.app (Opposite.op ⟨j⟩) t)) j
  · intro s m hm
    apply ConcreteCategory.hom_ext
    intro t
    apply e.injective
    funext j
    exact (ConcreteCategory.congr_hom (hm (Opposite.op ⟨j⟩)) t).trans
      (congrFun (e.apply_symm_apply (fun j => s.π.app (Opposite.op ⟨j⟩) t)) j).symm

-- 全 Hom と反対豊穣の次数評価を同時に照合するため、局所的に elaboration 上限を増やす。
set_option maxHeartbeats 400000 in
def dgProjectiveCoproductCoconeHom_isLimit (M : J → ProjectiveDGModules R D)
    (N : ProjectiveDGModules R D) :
    IsLimit (HomotopyLimits.simplicialHomCone
      (CategoryTheory.Limits.Cocone.op (dgProjectiveCoproductCofan R D M))
      (Opposite.op (ForgetEnrichment.of (Complex R) N))) := by
  apply evaluationJointlyReflectsLimits
  intro n
  let c := ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n).mapCone
    (HomotopyLimits.simplicialHomCone
      (CategoryTheory.Limits.Cocone.op (dgProjectiveCoproductCofan R D M))
      (Opposite.op (ForgetEnrichment.of (Complex R) N)))
  have h : Function.Bijective (fun s : c.pt => fun j : J =>
      c.π.app (Opposite.op ⟨j⟩) s) := by
    have hp := dgModuleCoproductStandard_bijective R D
      (dgProjectiveCoproductUnderlying R D M) (ForgetEnrichment.of (Complex R) N.val)
      n.unop.len
    have heq : (fun s : c.pt => fun j : J => c.π.app (Opposite.op ⟨j⟩) s) =
        (fun s => fun j => dgStandardSimplexMap
          (eHomWhiskerRight (Complex R)
            (Sigma.ι (dgProjectiveCoproductUnderlying R D M) j)
            (ForgetEnrichment.of (Complex R) N.val)) s) := by
      funext s j
      exact congrArg (fun f => f.app n s) (dgProjectiveCoproductHomProjection R D M N j)
    rw [heq]
    exact hp
  exact dgProjectiveCoproductTypeConeIsLimit c h

lemma dgProjectiveCoproductCofan_isColimitCone (M : J → ProjectiveDGModules R D) :
    IsColimitCone (HomotopyLimits.strictNativeCocone (dgProjectiveCoproductCofan R D M)) :=
  HomotopyLimits.strictNativeCocone_isColimit_of_isDiscrete_homLimit _ (fun N =>
    dgProjectiveCoproductCoconeHom_isLimit R D M
      (ForgetEnrichment.to (Complex R) N.unop))

end SerrePositivity.InfinityCategories

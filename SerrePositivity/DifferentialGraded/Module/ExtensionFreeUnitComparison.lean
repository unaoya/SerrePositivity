module
public import SerrePositivity.DifferentialGraded.Module.ExtensionFreeAdjunction
public import SerrePositivity.DifferentialGraded.Module.FreeRestrictionComparison
/-!
概要：実自由延長同型の随伴射を、元の Hom 鎖写像による制限比較へ同定する。
方針：自由評価の Hom 同値で両射を比較し、随伴一意性の特徴式を用いる。
規約：元の実延長同型と、各成分が恒等 tensor Hom 写像である閉射を保持する。
使われ方：c′ の全シフト自由閉射の端点同型付き延長比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

set_option maxRecDepth 1024 in
lemma dgModuleExtensionFreeAtIso_adjunct (x : D) (K : Complex R) :
    (dgModuleExtensionRestrictionAdjunction R D E F).homEquiv ((freeAt x).obj K)
      ((freeAt (F.obj x)).obj K) (dgModuleExtensionFreeAtIso R D E F x K).hom =
    freeRestrictionComparison R D E F x K := by
  apply (freeHomEquiv R D x K
    ((moduleRestriction R D E F.op).obj ((freeAt (F.obj x)).obj K))).injective
  have h := dgModuleExtensionFreeAtIso_homEquiv R D E F x K
    ((freeAt (F.obj x)).obj K) (𝟙 _)
  simp only [Category.comp_id] at h
  rw [dgModuleExtensionFreeAdjunction_homEquiv] at h
  have h' := freeRestrictionComparison_freeHomEquiv R D E F x K
  apply h.trans
  simpa only [freeEvaluationAdjunction, Adjunction.mkOfHomEquiv_homEquiv] using h'.symm

end SerrePositivity.DifferentialGraded

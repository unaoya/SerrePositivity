module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeBiprodQuasiIso
/-!
概要：一般 dg 関手の実出力分解 Hom から実入力 Hom への射影が準同型であること。
方針：実差を二成分 desc と同定し、半自由始域の第二 Hom 準同型を短完全列へ接続する。
規約：出力の射影性は仮定しない。使われ方：出力分解 dg 圏から入力 nerve への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R C (RightModule R E)) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
/-- 同じ実差写像は、元の実二成分の desc と厳密に一致する。 -/
lemma dgModuleFunctorResolutionDifference_eq_desc :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R C E F X Y = biprod.desc
      (F.map X.source Y.source ≫ eHomWhiskerRight (Complex R) X.augmentation
        (ForgetEnrichment.of (Complex R) (F.obj Y.source)))
      (-(eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) X.replacement.val) Y.augmentation)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference, biprod.desc_eq,
    Preadditive.comp_neg, sub_eq_add_neg]
/-- 全 Hom 複体の実入力射影は、全次数で準同型。 -/
lemma dgModuleFunctorResolutionSourceHomMap_quasiIso :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R C E F X Y) := by
  let q := eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) X.replacement.val) Y.augmentation
  have hq : QuasiIso q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolution_secondHomMap_quasiIso R C E F X Y
  have hn : QuasiIso (-q) := by
    have hi : IsIso (-𝟙 (moduleHom R E X.replacement.val (F.obj Y.source))) := by
      change IsIso ((-Iso.refl _).hom)
      infer_instance
    have hnq : QuasiIso (-𝟙 (moduleHom R E X.replacement.val (F.obj Y.source))) :=
      quasiIso_of_isIso _
    have h := quasiIso_comp q
      (-𝟙 (moduleHom R E X.replacement.val (F.obj Y.source))) (hφ := hq) (hφ' := hnq)
    simpa only [Preadditive.comp_neg, Preadditive.neg_comp, Category.comp_id] using! h
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeProjection_quasiIso_of_eq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R C E F X Y) _ (-q)
    (dgModuleFunctorResolutionDifference_eq_desc R C E F X Y) hn
end SerrePositivity.InfinityCategories.Project.DerivedCategories

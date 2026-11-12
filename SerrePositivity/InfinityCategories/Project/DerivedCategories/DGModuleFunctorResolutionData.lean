module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeHomComplexInfinity
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
/-!
概要：射影的加群を保つとは限らない dg 関手に対し、実入力と半自由出力分解を併せる。
方針：入力の全 Hom と、実分解の比較正方形の差を一つの鎖写像に保持する。
規約：現段階は実対象・差の鎖写像・準同型性。分解 dg 圏と nerve 比較は別工程。
使われ方：β5 の一般右導来 Hom を、出力の射影性の偽の仮定なしに構成する入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R C (RightModule R E))
/-- 同じ実入力と、その実像への次数別全射な半自由分解を保持する対象。 -/
structure DGModuleFunctorResolutionObject where
  source : C
  replacement : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E
  augmentation : ForgetEnrichment.of (Complex R) replacement.val ⟶
    ForgetEnrichment.of (Complex R) (F.obj source)
  surjective : moduleDegreewiseSurjective R E augmentation
  quasiIso : moduleQuasiIso R E augmentation
/-- 任意の実入力は、出力の射影性を仮定せず分解対象へ持ち上がる。 -/
lemma dgModuleFunctorResolutionObject_source_surjective :
    Function.Surjective (DGModuleFunctorResolutionObject.source (R := R) (C := C) (E := E)
      (F := F)) := by
  intro x
  obtain ⟨P, π, hs, hq⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_resolution_exists R E (F.obj x)
  exact ⟨⟨x, P, π, hs, hq⟩, rfl⟩
variable (X Y : DGModuleFunctorResolutionObject R C E F)
/-- 比較正方形の差を取る、同じ全 Hom end 間の実鎖写像。 -/
def dgModuleFunctorResolutionDifference :
    (homObject R C X.source Y.source ⊞ moduleHom R E X.replacement.val Y.replacement.val) ⟶
      moduleHom R E X.replacement.val (F.obj Y.source) :=
  biprod.fst ≫ F.map X.source Y.source ≫
    eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) (F.obj Y.source)) -
    biprod.snd ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) X.replacement.val) Y.augmentation
/-- 差の第二成分を与える実鎖写像は、半自由な実始域によって準同型になる。 -/
lemma dgModuleFunctorResolution_secondHomMap_quasiIso :
    QuasiIso (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) X.replacement.val) Y.augmentation) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTarget_quasiIso R E X.replacement Y.augmentation Y.quasiIso
end SerrePositivity.InfinityCategories.Project.DerivedCategories

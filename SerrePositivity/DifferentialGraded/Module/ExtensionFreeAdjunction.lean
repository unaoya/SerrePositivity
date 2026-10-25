module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Module.TensorAdjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
/-!
概要：実 dg 加群延長と任意複体で生成する自由加群の比較を、随伴の一意性で構成する。
方針：自由・評価随伴と延長・制限随伴を合成し、制限後の評価を同じ標的評価へ戻す。
規約：生成複体の全射に自然な実同型を構成し、元の shift 比較は変更しない。
使われ方：c′ のシフト自由閉射と実延長の端点比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
private lemma extensionFreeComparison_homEquiv
    {C₀ C₁ : Type*} [Category C₀] [Category C₁]
    {L L' : C₀ ⥤ C₁} {H : C₁ ⥤ C₀} (adj : L ⊣ H) (adj' : L' ⊣ H)
    (x : C₀) (M : C₁) (g : L'.obj x ⟶ M) :
    adj.homEquiv x M ((Adjunction.leftAdjointUniq adj adj').hom.app x ≫ g) =
      adj'.homEquiv x M g := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  exact (adj'.homEquiv_unit x M g).symm

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

def dgModuleExtensionFreeAdjunction (x : D) :
    freeAt (A := R) x ⋙ (dgModuleExtension R D E F).onClosed ⊣
      moduleEvaluation R E (F.obj x) :=
  (((freeEvaluationAdjunction R D x).comp (dgModuleExtensionRestrictionAdjunction R D E F)).ofNatIsoRight
    (moduleRestrictionEvaluationIso R D E F.op x))

def dgModuleExtensionFreeFunctorIso (x : D) :
    freeAt (A := R) x ⋙ (dgModuleExtension R D E F).onClosed ≅ freeAt (A := R) (F.obj x) :=
  Adjunction.leftAdjointUniq (dgModuleExtensionFreeAdjunction R D E F x)
    (freeEvaluationAdjunction R E (F.obj x))

lemma dgModuleExtensionFreeAdjunction_homEquiv (x : D) (K : Complex R)
    (M : ModuleCategory R E)
    (g : (dgModuleExtension R D E F).onClosed.obj ((freeAt x).obj K) ⟶ M) :
    (dgModuleExtensionFreeAdjunction R D E F x).homEquiv K M g =
    freeHomEquiv R D x K ((moduleRestriction R D E F.op).obj M)
      ((dgModuleExtensionRestrictionAdjunction R D E F).homEquiv ((freeAt x).obj K) M g) := by
  rw [dgModuleExtensionFreeAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [Adjunction.comp_homEquiv]
  simp only [freeEvaluationAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    moduleRestrictionEvaluationIso, NatIso.ofComponents_hom_app, Iso.refl_hom, Category.comp_id]
  rfl

def dgModuleExtensionFreeAtIso (x : D) (K : Complex R) :
    (dgModuleExtension R D E F).onClosed.obj ((freeAt x).obj K) ≅ (freeAt (F.obj x)).obj K :=
  (dgModuleExtensionFreeFunctorIso R D E F x).app K

lemma dgModuleExtensionFreeAtIso_naturality (x : D) {K L : Complex R} (g : K ⟶ L) :
    (dgModuleExtension R D E F).onClosed.map ((freeAt x).map g) ≫
      (dgModuleExtensionFreeAtIso R D E F x L).hom =
    (dgModuleExtensionFreeAtIso R D E F x K).hom ≫ (freeAt (F.obj x)).map g :=
  (dgModuleExtensionFreeFunctorIso R D E F x).hom.naturality g

set_option maxRecDepth 1024 in
lemma dgModuleExtensionFreeAtIso_homEquiv (x : D) (K : Complex R)
    (M : ModuleCategory R E) (g : (freeAt (F.obj x)).obj K ⟶ M) :
    (dgModuleExtensionFreeAdjunction R D E F x).homEquiv K M
      ((dgModuleExtensionFreeAtIso R D E F x K).hom ≫ g) =
    (freeEvaluationAdjunction R E (F.obj x)).homEquiv K M g :=
  extensionFreeComparison_homEquiv (dgModuleExtensionFreeAdjunction R D E F x)
    (freeEvaluationAdjunction R E (F.obj x)) K M g

end SerrePositivity.DifferentialGraded

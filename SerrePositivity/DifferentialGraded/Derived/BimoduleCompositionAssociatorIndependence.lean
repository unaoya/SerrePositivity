module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociator
public import SerrePositivity.DifferentialGraded.Derived.BimoduleResolutionLift

/-! # 全導来結合同型の任意解像度計算と選択独立性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

lemma derivedBimoduleAssociatorBaseIso_resolution (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom =
      (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom := by
  let s : rightKFlatResolutionObj A C E hE Q ⟶ S :=
    ⟨bimoduleCanonicalResolutionLift A C E q hq⟩
  let t : rightKFlatResolutionObj A E F hF R ⟶ T :=
    ⟨bimoduleCanonicalResolutionLift A E F r hr⟩
  have h := derivedBimoduleAssociatorResolutionIso_naturality A B C E F hE hF
    (rightKFlatResolutionObj A C E hE Q) S (rightKFlatResolutionObj A E F hF R) T
    (bimoduleCanonicalSemifreeResolution A C E Q).π q
    (bimoduleCanonicalSemifreeResolution A E F R).π r
    (bimoduleCanonicalSemifreeResolution A C E Q).quasiIso hq
    (bimoduleCanonicalSemifreeResolution A E F R).quasiIso hr (𝟙 Q) (𝟙 R) s t
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
      (bimoduleCanonicalResolutionLift_fac A C E q hq).symm)
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using
      (bimoduleCanonicalResolutionLift_fac A E F r hr).symm)
  simpa only [derivedBimoduleAssociatorBaseIso, derivedBimoduleComposePairMap,
    derivedBimoduleComposeInnerMap,
    CategoryTheory.Functor.map_id, whiskerRight_id', whiskerLeft_id',
    Category.id_comp, Category.comp_id, NatTrans.id_app] using h.symm

/-- 全因子に自然な結合同型は、任意の指定右K-flat解像度で計算できる。 -/
lemma derivedBimoduleAssociatorIso_resolution_app (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (((derivedBimoduleAssociatorIso A B C E F hE hF).app
      ((bimoduleToDerived A E F).obj R)).app ((bimoduleToDerived A C E).obj Q)).hom =
      (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom :=
  (derivedBimoduleAssociatorIso_base_app A B C E F hE hF Q R).trans
    (derivedBimoduleAssociatorBaseIso_resolution A B C E F hE hF Q R S T q r hq hr)

lemma derivedBimoduleAssociatorIso_resolution_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (((derivedBimoduleAssociatorIso A B C E F hE hF).app
      ((bimoduleToDerived A E F).obj R)).app ((bimoduleToDerived A C E).obj Q)).hom ≫
        (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q R S T q r hq hr).hom =
      (derivedBimoduleComposePairResolutionIso A B C E F hE hF Q R S T q r hq hr).hom ≫
        (rightKFlatDerivedAssociator A B C E F S T).hom := by
  rw [derivedBimoduleAssociatorIso_resolution_app, derivedBimoduleAssociatorResolutionIso_fac]

end SerrePositivity.DifferentialGraded.BimoduleTensor

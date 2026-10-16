module
public import SerrePositivity.DifferentialGraded.Module.Ring
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 一対象環Aの右dg加群と主dg複体圏の実際のdg比較

既存のHom endの評価同型を逆に使い、複体から一対象dg加群への全Hom関手を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable (A : Type u) [CommRing A]

/-- Hom評価同型の逆は閉零単位を保つ。評価後に既存の単位保存式を使う。 -/
lemma ringConstantHomInv_identity (P : Complex A) :
    identity P ≫ (ringConstantHomIso A P P).inv = moduleIdentity A PUnit.{1} (ringModule A P) := by
  apply (cancel_mono (ringConstantHomIso A P P).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (moduleIdentity_π A PUnit.{1} (ringModule A P) PUnit.unit).symm

/-- Hom評価同型の逆は全次数の豊穣合成を保つ。評価の合成保存とtensorの逆同型を使う。 -/
lemma ringConstantHomInv_comp (P Q R : Complex A) :
    enrichedComposition P Q R ≫ (ringConstantHomIso A P R).inv =
    ((ringConstantHomIso A P Q).inv ⊗ₘ (ringConstantHomIso A Q R).inv) ≫
      moduleComposition A PUnit.{1} (ringModule A P) (ringModule A Q) (ringModule A R) := by
  apply (cancel_mono (ringConstantHomIso A P R).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change enrichedComposition P Q R =
    ((ringConstantHomIso A P Q).inv ⊗ₘ (ringConstantHomIso A Q R).inv) ≫
      moduleComposition A PUnit.{1} (ringModule A P) (ringModule A Q) (ringModule A R) ≫
      moduleHomπ A PUnit.{1} (ringModule A P) (ringModule A R) PUnit.unit
  rw [moduleComposition_π, tensorHom_comp_tensorHom_assoc]
  change enrichedComposition P Q R =
    (((ringConstantHomIso A P Q).inv ≫ (ringConstantHomIso A P Q).hom) ⊗ₘ
      ((ringConstantHomIso A Q R).inv ≫ (ringConstantHomIso A Q R).hom)) ≫
      enrichedComposition P Q R
  simp only [Iso.inv_hom_id, tensorHom_id, id_whiskerRight, Category.id_comp]

/-- 複体を一対象環の右dg加群へ送る、全Hom評価の逆による実際のdg関手。 -/
def ringConstantDG : DGFunctor A (Complex A) (RightModule A PUnit.{1}) where
  obj := ringModule A
  map P Q := (ringConstantHomIso A P Q).inv
  map_id := ringConstantHomInv_identity A
  map_comp := ringConstantHomInv_comp A

/-- 定数一対象dg加群を評価すると、全Homの射を含めて元のdg複体関手へ戻る。 -/
lemma ringConstantDG_comp_evaluation :
    DGFunctor.comp (ringConstantDG A) (moduleEvaluationDG A PUnit.{1} PUnit.unit) =
      DGFunctor.id (A := A) (Complex A) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := DGFunctor.comp (ringConstantDG A) (moduleEvaluationDG A PUnit.{1} PUnit.unit))
    (G := DGFunctor.id (A := A) (Complex A)) (fun _ => rfl)
  intro P Q
  change ((ringConstantHomIso A P Q).inv ≫ (ringConstantHomIso A P Q).hom) ≫ 𝟙 _ = 𝟙 _
  exact (Category.comp_id _).trans (ringConstantHomIso A P Q).inv_hom_id

/-- 一対象dg加群はその値から厳密に復元されるので、定数dg関手のH⁰は本質的全射である。 -/
instance ringConstantDGHomotopyEssSurj : (ringConstantDG A).onHomotopy.EssSurj where
  mem_essImage X := by
    let M : RightModule A PUnit.{1} := ForgetEnrichment.to (Complex A) X.as
    refine ⟨(toHomotopy A (Complex A)).obj
      (ForgetEnrichment.of (Complex A) (M.obj (op PUnit.unit))), ⟨eqToIso ?_⟩⟩
    exact congrArg (fun N => (toHomotopy A (RightModule A PUnit.{1})).obj
      (ForgetEnrichment.of (Complex A) N)) (ringModule_recover A M)

/-- 主複体圏から一対象dg加群への関手は準同値。各Hom写像は実際に同型である。 -/
lemma ringConstantDG_quasiEquivalence : QuasiEquivalence (ringConstantDG A) := by
  refine ⟨?_, inferInstance⟩
  intro P Q
  change QuasiIso (ringConstantHomIso A P Q).inv
  infer_instance

/-- 一対象加群の評価のH⁰は本質的全射。任意の複体をその定数加群から得る。 -/
instance ringEvaluationDGHomotopyEssSurj :
    (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy.EssSurj where
  mem_essImage X :=
    ⟨(toHomotopy A (RightModule A PUnit.{1})).obj
      (ForgetEnrichment.of (Complex A) (ringModule A (ForgetEnrichment.to (Complex A) X.as))),
      ⟨Iso.refl _⟩⟩

/-- 一対象dg加群の評価も準同値。全Hom endの評価がchain isoである既存の証明を使う。 -/
lemma ringEvaluationDG_quasiEquivalence :
    QuasiEquivalence (moduleEvaluationDG A PUnit.{1} PUnit.unit) := by
  refine ⟨?_, inferInstance⟩
  intro M N
  change QuasiIso (moduleHomπ A PUnit.{1} M N PUnit.unit)
  infer_instance

end SerrePositivity.DifferentialGraded

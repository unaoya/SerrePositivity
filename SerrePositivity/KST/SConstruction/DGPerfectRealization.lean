module
public import SerrePositivity.KST.SConstruction.PerfectDGExtension
public import SerrePositivity.DifferentialGraded.Tensor.Fubini

/-! # 元の perfect 値 dg 関手による実加群の tensor 評価
概要：小さい dg 圏の perfect 値関手を双加群にし、元の代表加群をその実像へ戻す。
方針：既存の tensor 合成と同じ右単位同型・全 Hom 自然性を使う。
規約：全 perfect 加群圏の Small 性は仮定しない。使われ方：小終域 cone の元の終域での評価。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (PerfectDGModule R E))

/-- 元の実 perfect 像をそのまま値に持つ評価双加群。 -/
def dgPerfectRealizationKernel : Bimodule R E C :=
  F.comp (perfectDGModuleInclusion R E Set.univ)

/-- 元の評価双加群との tensor で定める実加群上の dg 関手。 -/
def dgPerfectRealization : DGFunctor R (RightModule R C) (RightModule R E) :=
  (BimoduleTensor.compose R E C (RightModule R C) (dgPerfectRealizationKernel R C E F)
    (DGFunctor.id (RightModule R C))).toFunctor

/-- 同じ元の代表加群の評価は、元の指定 perfect 像の実加群と同型。 -/
def dgPerfectRealizationRepresentableIso (b : C) :
    ForgetEnrichment.of (Complex R)
      ((dgPerfectRealization R C E F).obj (representable R b)) ≅
        ForgetEnrichment.of (Complex R) (F.obj b).val :=
  BimoduleTensor.rightUnitIso R E C (dgPerfectRealizationKernel R C E F) b

/-- 代表加群間の元の全 Hom を評価すると、同じ対角 tensor の作用を回収する。 -/
lemma dgPerfectRealization_yoneda_map (x y : C) :
    yonedaHom R C x y ≫ (dgPerfectRealization R C E F).map
        (representable R x) (representable R y) =
      (BimoduleTensor.compose R E C C (dgPerfectRealizationKernel R C E F)
        (Bimodule.diagonal R C)).toFunctor.map x y := by
  apply moduleHom_ext
  intro t
  have h₁ := BimoduleTensor.compose_leftMap_π R E C (RightModule R C)
    (dgPerfectRealizationKernel R C E F) (DGFunctor.id _) (representable R x)
      (representable R y) t
  have h₂ := BimoduleTensor.compose_leftMap_π R E C C
    (dgPerfectRealizationKernel R C E F) (Bimodule.diagonal R C) x y t
  simp only [DGFunctor.id, EnrichedFunctor.id_map] at h₁
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => yonedaHom R C x y ≫ k) h₁).trans h₂.symm)

/-- 同じ元の代表評価同型は、元の小圏の全 Hom 複体について自然。 -/
lemma dgPerfectRealizationRepresentableIso_naturality (x y : C) :
    yonedaHom R C x y ≫ (dgPerfectRealization R C E F).map
        (representable R x) (representable R y) ≫
        moduleHomPostcompose R E _ _ _ (dgPerfectRealizationRepresentableIso R C E F y).hom =
      (dgPerfectRealizationKernel R C E F).map x y ≫
        moduleHomPrecompose R E _ _ _ (dgPerfectRealizationRepresentableIso R C E F x).hom := by
  rw [← Category.assoc, dgPerfectRealization_yoneda_map]
  exact BimoduleTensor.rightUnitIso_naturality R E C (dgPerfectRealizationKernel R C E F) x y

end SerrePositivity.KST.SConstruction

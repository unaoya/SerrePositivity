module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedGenerators
public import SerrePositivity.DifferentialGraded.Functor.HomIso
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # U13の指定enhancementと全加群内のEndの照合 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

/-- U13のenhancement内のEndを、実際の右加群の全Endへ送る。 -/
def perfectEndomorphismUnderlying :
    DGFunctor A (EndomorphismObject E) (EndomorphismObject E.val) :=
  endomorphismMap A (perfectDGModuleInclusion A D S) E

/-- U13は充満dg部分圏なので、比較は全Hom複体上の恒等写像。 -/
lemma perfectEndomorphismUnderlying_map (x y : EndomorphismObject E) :
    (perfectEndomorphismUnderlying A D S E).map x y = 𝟙 _ := rfl

lemma perfectEndomorphismUnderlying_homQuasiIso :
    HomQuasiIso (perfectEndomorphismUnderlying A D S E) := by
  intro x y
  rw [perfectEndomorphismUnderlying_map]
  infer_instance

/-- H⁰の本質的全射性はHomの擬同型とは別の証拠として保持する。 -/
lemma perfectEndomorphismUnderlying_essSurj :
    (perfectEndomorphismUnderlying A D S E).onHomotopy.EssSurj where
  mem_essImage X := by
    refine ⟨(toHomotopy A (EndomorphismObject E)).obj
      (ForgetEnrichment.of (Complex A) .point), ⟨?_⟩⟩
    obtain ⟨X⟩ := X
    obtain ⟨X⟩ := X
    exact Iso.refl _

/-- 二つのEndの比較は準同値。thick生成の仮定は不要。 -/
lemma perfectEndomorphismUnderlying_quasiEquivalence :
    QuasiEquivalence (perfectEndomorphismUnderlying A D S E) :=
  ⟨perfectEndomorphismUnderlying_homQuasiIso A D S E,
    perfectEndomorphismUnderlying_essSurj A D S E⟩

/-- 指定enhancementから、実際のEのEndに値を持つHom関手。 -/
def perfectEndomorphismModuleHom :
    DGFunctor A (PerfectDGModuleOver A D S) (RightModule A (EndomorphismObject E.val)) :=
  (perfectDGModuleInclusion A D S).comp (endomorphismModuleHom A D E.val)

/-- enhancement内のHom(E,M)は、Endの比較に沿った実際の加群Homの制限と一致する。 -/
lemma perfectEndomorphismHomRight_comparison (M : PerfectDGModuleOver A D S) :
    endomorphismHomRight A (PerfectDGModuleOver A D S) E M =
      restrictModule A (EndomorphismObject E) (EndomorphismObject E.val)
        (perfectEndomorphismUnderlying A D S E).op
        ((perfectEndomorphismModuleHom A D S E).obj M) := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]

/-- U13の指定対象に対する再構成導来随伴。射影性は対象の証拠から取る。 -/
def perfectEndomorphismDerivedAdjunction :
    endomorphismDerivedTensor A D E.val ⊣ endomorphismDerivedHom A D E.val E.property.1 :=
  endomorphismDerivedAdjunction A D E.val E.property.1

end SerrePositivity.DifferentialGraded

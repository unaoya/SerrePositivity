module
public import SerrePositivity.KST.SConstruction.DGHomGluingTargetCone
public import SerrePositivity.KST.SConstruction.DGGluingRightAxis
public import SerrePositivity.DifferentialGraded.Module.ConeDesc

/-! # 元の零左成分を持つ gluing の終域 cone の厳密比較
概要：実閉零対象を左成分とする同じ cone を、元の右対象の代表加群と同定する。
方針：元の標準 cone 包含・零合成延長を順逆とし、評価で二つの逆律を示す。
規約：同型の類ではなく実加群同型。使われ方：⊙ の指定商対象の End 比較。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits HomologicalComplex CochainComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type z) [DGCategory R E] [Small.{u} E]

/-- 元の閉零加群を始域とする標準 cone は、元の終域加群と実際に同型。 -/
def dgHomGluingModuleConeZeroSourceIso {L N : ModuleCategory R E}
    (f : L ⟶ N) (hz : IsZero L) : moduleCone R E f ≅ N where
  hom := moduleConeDesc R E f (𝟙 N) (hz.eq_of_src _ _)
  inv := moduleConeInr R E f
  hom_inv_id := by
    apply moduleMorphism_ext
    intro x
    apply HomologicalComplex.Hom.ext
    funext n
    simp only [CategoryTheory.Functor.map_comp, moduleConeInr_eval,
      CategoryTheory.Functor.map_id, HomologicalComplex.id_f]
    apply mappingCone.ext_from ((moduleEvaluation R E x).map f) (n + 1) n rfl
    · exact ((HomologicalComplex.eval (ModuleCat R) (.up ℤ) (n + 1)).map_isZero
        ((moduleEvaluation R E x).map_isZero hz)).eq_of_src _ _
    · have hc := congrArg (fun k => ((moduleEvaluation R E x).map k).f n)
        (moduleConeDesc_inr R E f (𝟙 N) (hz.eq_of_src _ _))
      simp only [CategoryTheory.Functor.map_comp, moduleConeInr_eval,
        CategoryTheory.Functor.map_id, HomologicalComplex.id_f] at hc
      change (mappingCone.inr ((moduleEvaluation R E x).map f)).f n ≫
        ((moduleEvaluation R E x).map (moduleConeDesc R E f (𝟙 N) (hz.eq_of_src _ _))).f n =
          𝟙 _ at hc
      change (mappingCone.inr ((moduleEvaluation R E x).map f)).f n ≫
        (((moduleEvaluation R E x).map (moduleConeDesc R E f (𝟙 N) (hz.eq_of_src _ _))).f n ≫
          (mappingCone.inr ((moduleEvaluation R E x).map f)).f n) =
        (mappingCone.inr ((moduleEvaluation R E x).map f)).f n ≫ 𝟙 _
      erw [← Category.assoc, hc, Category.id_comp]
  inv_hom_id := moduleConeDesc_inr R E f (𝟙 N) (hz.eq_of_src _ _)

variable (C : Type v) [DGCategory R C] [Small.{u} C] (D : Type w) [DGCategory R D]
  (p : DGFunctor R C E) (q : DGFunctor R D E)

/-- 元の右軸対象 (z,d,0) の同じ終域 cone は、元の q(d) の代表加群と実際に同型。 -/
def dgHomGluingRightConeIso (z : C) (hz : IsZero (ForgetEnrichment.of (Complex R) z)) (d : D) :
    ForgetEnrichment.of (Complex R)
      (dgHomGluingTargetCone R C D E p q
        (dgGluingRightAxisObject R C D (dgHomGluingBimodule R C D E p q) z d)).val ≅
    ForgetEnrichment.of (Complex R) (representable R (q.obj d)) :=
  dgHomGluingModuleConeZeroSourceIso R E _
    ((dgYoneda R E).onClosed.map_isZero (p.onClosed.map_isZero hz))

end SerrePositivity.KST.SConstruction

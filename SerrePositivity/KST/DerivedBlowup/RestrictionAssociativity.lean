module

public import SerrePositivity.KST.DerivedBlowup.RestrictionComposition

/-!
概要：KST §3.1 の三段階の係数制限の dg 合成比較の結合整合性。
方針：どの合成比較も Hom の各次数で恒等関数なので、二経路の dg 関手を外延性で比較する。
規約：環射の合成の括弧は定義上の結合性で同定する。
使われ方：全有限チャート dg 図式の高次の係数制限整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open SerrePositivity.DifferentialGraded.ScalarExtension

variable {A B C E : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing E]

/-- 概要：三段の係数制限をまとめる二経路の dg 関手は一致する。
方針：対象写像は恒等、Hom の成分は両経路とも恒等関数なので各次数で比較する。
規約：KST §3.1。使われ方：係数制限の合成比較の結合整合性。 -/
theorem restrictionCompositionDGFunctor_assoc (φ : A →+* B) (ψ : B →+* C) (χ : C →+* E)
    (D : Type v) [DifferentialGraded.DGCategory E D] :
    EnrichedFunctor.comp (DifferentialGraded.Complex A)
      (restrictionCompositionDGFunctor φ ψ (DGRestriction χ D))
      (restrictionCompositionDGFunctor (ψ.comp φ) χ D) =
    EnrichedFunctor.comp (DifferentialGraded.Complex A)
      (restrictDGFunctor φ (restrictionCompositionDGFunctor ψ χ D))
      (restrictionCompositionDGFunctor φ (χ.comp ψ) D) := by
  refine EnrichedFunctor.ext (DifferentialGraded.Complex A)
    (F := EnrichedFunctor.comp (DifferentialGraded.Complex A)
      (restrictionCompositionDGFunctor φ ψ (DGRestriction χ D))
      (restrictionCompositionDGFunctor (ψ.comp φ) χ D))
    (G := EnrichedFunctor.comp (DifferentialGraded.Complex A)
      (restrictDGFunctor φ (restrictionCompositionDGFunctor ψ χ D))
      (restrictionCompositionDGFunctor φ (χ.comp ψ) D)) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

end SerrePositivity.KST.DerivedBlowup

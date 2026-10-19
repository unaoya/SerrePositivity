module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeIdentityApex
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeInitialConstant

/-!
概要：恒等射の coslice 点への前合成を、標準の Hom 比較と同定する。
方針：恒等射の全退化単体を定値 coherent simplex として読み、始点置換の計算を使う。
規約：全 Hom パラメータでの射の厳密な等式で、Kan 性を要求しない。
使われ方：錐全体上の明示的な Hom の族の頂点評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 恒等射の coslice 点の全ての退化は、定値の coherent simplex に対応する。 -/
lemma cosliceInitialCoordinates_identity (z : C) {n : ℕ}
    (t : (Δ[0] : SSet.{max u v}) _⦋n⦌) :
    cosliceInitialCoordinates z
        ((cosliceIdentityPoint (coherentNerveVertex z)).app (Opposite.op ⦋n⦌) t) =
      (⟨PinchedHom.constant (coherentNerveVertex z) (n + 1), rfl⟩ :
        fixedInitialSimplex z n) := by
  apply Subtype.ext
  change SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
    (joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm t) ≫
      (coneIdentityFold ≫ SSet.yonedaEquiv.symm (coherentNerveVertex z)))) = _
  rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const, SSet.comp_const]
  rfl

/-- 前合成の族を恒等射の点で始めると、標準の Hom 比較の包含になる。 -/
lemma coherentCosliceSourcePrecomposition_identity (x z : C) :
    lift (SSet.const (SSet.yonedaEquiv (cosliceIdentityPoint (coherentNerveVertex z))))
        (𝟙 ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op)) ≫
      coherentCosliceSourcePrecomposition x z =
    coherentCosliceFiberComparison x z ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (coherentNerveVertex z) := by
  erw [← weightedConstantCosliceFiberMap_eq
    ((Functor.const (Discrete PUnit.{u + 1})).obj z) x ⟨PUnit.unit⟩,
    weightedConstantCosliceFiberMap, vertexFiberLift_ι]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  apply Subtype.ext
  change (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (coneInitialFixedSimplex x
        (cosliceInitialCoordinates z
          ((SSet.const (SSet.yonedaEquiv
            (cosliceIdentityPoint (coherentNerveVertex z))) :
            (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶ _).app
              (Opposite.op ⦋n⦌) (ULift.up s))) (SSet.yonedaEquiv.symm s)) =
    (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (weightedConeSimplex ((Functor.const (Discrete PUnit.{u + 1})).obj z) x
        (weightedNerveConstantDiagram
          (simplicialHomDiagram ((Functor.const (Discrete PUnit.{u + 1})).obj z) x ⋙
            SSet.opFunctor) ⟨PUnit.unit⟩ s))
  have hc : (SSet.const (SSet.yonedaEquiv (cosliceIdentityPoint (coherentNerveVertex z))) :
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶ _) =
      (stdSimplex.isTerminalObj₀.from _) ≫ cosliceIdentityPoint (coherentNerveVertex z) := by
    have h := SSet.yonedaEquiv_symm_zero
      (SSet.yonedaEquiv (cosliceIdentityPoint (coherentNerveVertex z)))
    rw [Equiv.symm_apply_apply] at h
    rw [h, SSet.comp_const, SSet.yonedaEquiv_const]
  rw [hc]
  erw [cosliceInitialCoordinates_identity]
  change (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
    (coneInitialSimplex x (PinchedHom.constant (coherentNerveVertex z) (n + 1))
      (SSet.yonedaEquiv.symm s)) = _
  rw [coneInitialSimplex_constant]

end
end SerrePositivity.InfinityCategories.HomotopyLimits

module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorEnrichment

/-!
概要：固定 ε を持つ商パラメータ延長の、元の単位・tensor 縦合成の厳密保存。
方針：延長後の実自然性から ε 整合の閉性を導き、同じ対象成分で延長を同定する。
規約：ε 整合を省かず、任意複体パラメータと全整数次数を保持する。
使われ方：D-S 工程2の商関手圏への豊穣延長の単位・合成則。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory MonoidalCategory HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
open KST.SConstruction
variable (R : Type u) [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory R E]

/-- 同じ閉単位の全次数成分は、指定された同じ ε と整合する。 -/
lemma parameterExtension_identity_epsilon (C : _root_.SerrePositivity.DifferentialGraded.DGQuotient.ContractedFunctor R D S E)
    (b : S) (k : ℤ) (t : (𝟙_ (_root_.SerrePositivity.DifferentialGraded.Complex R)).X k) :
    _root_.SerrePositivity.DifferentialGraded.forward R (C.homotopy b)
        (((dgFunctorParamIdentity R D E C.toDGFunctor).app b.val).f k t) rfl =
      (k * (-1)).negOnePow • _root_.SerrePositivity.DifferentialGraded.forward R
        (((dgFunctorParamIdentity R D E C.toDGFunctor).app b.val).f k t)
        (C.homotopy b) (by omega) :=
  _root_.SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension_epsilon_necessary R C C
    (dgFunctorParamIdentity R D E C.toDGFunctor)
    (dgFunctorParamIdentity R (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D S) E (_root_.SerrePositivity.DifferentialGraded.DGQuotient.extension R C))
    (fun _ => rfl) b k t

/-- 元の同じ単位は、商上でも同じ単位そのものに延長される。 -/
lemma parameterExtension_identity (C : _root_.SerrePositivity.DifferentialGraded.DGQuotient.ContractedFunctor R D S E) :
    _root_.SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension R C C (dgFunctorParamIdentity R D E C.toDGFunctor)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.parameterExtension_identity_epsilon R C) =
      dgFunctorParamIdentity R (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D S) E (_root_.SerrePositivity.DifferentialGraded.DGQuotient.extension R C) := by
  apply GradedNatTrans.ext
  funext x
  rfl

variable (C₀ C₁ C₂ : _root_.SerrePositivity.DifferentialGraded.DGQuotient.ContractedFunctor R D S E) {K L : _root_.SerrePositivity.DifferentialGraded.Complex R}
  (τ : DGFunctorParamTrans R D E K C₀.toDGFunctor C₁.toDGFunctor)
  (σ : DGFunctorParamTrans R D E L C₁.toDGFunctor C₂.toDGFunctor)
  (hτ : ∀ (b : S) (k : ℤ) (t : K.X k),
    _root_.SerrePositivity.DifferentialGraded.forward R (C₀.homotopy b) ((τ.app b.val).f k t) rfl =
      (k * (-1)).negOnePow • _root_.SerrePositivity.DifferentialGraded.forward R ((τ.app b.val).f k t) (C₁.homotopy b) (by omega))
  (hσ : ∀ (b : S) (k : ℤ) (t : L.X k),
    _root_.SerrePositivity.DifferentialGraded.forward R (C₁.homotopy b) ((σ.app b.val).f k t) rfl =
      (k * (-1)).negOnePow • _root_.SerrePositivity.DifferentialGraded.forward R ((σ.app b.val).f k t) (C₂.homotopy b) (by omega))

include hτ hσ in
/-- 固定 ε との全次数整合は、元の tensor パラメータの縦合成について閉じる。 -/
lemma parameterExtension_composition_epsilon
    (b : S) (k : ℤ) (t : (K ⊗ L).X k) :
    _root_.SerrePositivity.DifferentialGraded.forward R (C₀.homotopy b)
        (((dgFunctorParamCompose R D E τ σ).app b.val).f k t) rfl =
      (k * (-1)).negOnePow • _root_.SerrePositivity.DifferentialGraded.forward R
        (((dgFunctorParamCompose R D E τ σ).app b.val).f k t)
        (C₂.homotopy b) (by omega) := by
  exact _root_.SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension_epsilon_necessary R C₀ C₂
    (dgFunctorParamCompose R D E τ σ)
    (dgFunctorParamCompose R (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D S) E
      (_root_.SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension R C₀ C₁ τ hτ) (_root_.SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension R C₁ C₂ σ hσ))
    (fun _ => rfl) b k t

/-- 同じ全パラメータを持つ縦合成は、元の二延長の合成そのものである。 -/
lemma parameterExtension_composition :
    _root_.SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension R C₀ C₂ (dgFunctorParamCompose R D E τ σ)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.parameterExtension_composition_epsilon R C₀ C₁ C₂ τ σ hτ hσ) =
      dgFunctorParamCompose R (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D S) E
        (_root_.SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension R C₀ C₁ τ hτ) (_root_.SerrePositivity.DifferentialGraded.DGQuotient.parameterExtension R C₁ C₂ σ hσ) := by
  apply GradedNatTrans.ext
  funext x
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact

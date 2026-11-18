module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeNegativeHomDecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedFreeHomZeroEvaluation
public import SerrePositivity.HomologicalAlgebra.ComplexLimits.TruncationInclusionComponents

/-!
概要：実標準Homの指定自由負次数逆随伴を全次数で評価する。
方針：同じΓの射影評価と延長切断包含の成分則を使う。
規約：零次数のcycles包含を通したまま、実最上位成分に同定する既存評価則。
使われ方：HA 1.2.4、IS-W2 B02の実AW合成と自由鎖AWの全成分照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory AlgebraicTopology HomologicalComplex MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 同じ切断包含の正次数の項同型は指定connective Homの項同型。 -/
theorem connectiveHom_negative_inclusion (x y : D) (n : ℕ) :
    (((homObject R D x y).truncLE' (ComplexShape.embeddingUpIntLE 0)).extendXIso
      ComplexShape.embeddingDownNat (i := n + 1) (i' := -(n + 1 : ℤ)) (by simp)).inv ≫
      (_root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape R ComplexShape.embeddingDownNat
        _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero (homObject R D x y)).f (-(n + 1 : ℤ)) =
      (connectiveHomComplex_positiveIso (R := R) x y n).hom := by
  have h (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
      (he : e = ComplexShape.embeddingUpIntLE 0)
      (hi : e.f (n + 1) = -(n + 1 : ℤ)) :
      (((homObject R D x y).truncLE' (ComplexShape.embeddingUpIntLE 0)).extendXIso
        e hi).inv ≫
        (_root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape R e he (homObject R D x y)).f
          (-(n + 1 : ℤ)) = (connectiveHomComplex_positiveIso (R := R) x y n).hom := by
    subst e
    exact extendedTruncationInclusion_nonboundary (homObject R D x y)
      (ComplexShape.embeddingUpIntLE 0) hi
      (by rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]; omega)
  exact h _ _ _

/-- 指定自由負次数逆随伴の射影生成元は、元の実標準Homの最上位成分。 -/
theorem freeNegativeStandardHom_generator_eval (S : SSet.{u}) (x y : D)
    (f : S ⟶ standardHomSpace (R := R) x y) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n⦌)) :
    (((freeNegativeChainsAdjunction R).homEquiv S (homObject R D x y)).symm
      (f ≫ standardDoldKanSpaceMap x y)).f (-(n : ℤ))
        (freeNegativeGenerator S n s) =
      standardTopEval (R := R) x y n (f.app _ s) := by
  cases n with
  | zero =>
    have h := freeNegativeChainsAdjunction_symm_generator_eval R S (homObject R D x y)
      (f ≫ standardDoldKanSpaceMap x y) 0 s
    rw [mooreProjection_zero_eq] at h
    have he := _root_.SerrePositivity.ComplexLimits.standardDoldKanModuleIso_zero_raw (R := R) x y (f.app _ s)
    exact h.trans he
  | succ n =>
    have h := freeNegativeChainsAdjunction_symm_generator_eval R S (homObject R D x y)
      (f ≫ standardDoldKanSpaceMap x y) (n + 1) s
    have hc := connectiveHom_negative_inclusion (R := R) x y n
    have he := ConcreteCategory.congr_hom
      (standardDoldKanModuleIso_positive_projected_eval (R := R) x y n) (f.app _ s)
    simp only [ModuleCat.comp_apply] at he
    dsimp only [standardDoldKanSpaceMap, NatTrans.comp_app, Functor.whiskerRight_app] at h
    refine h.trans ?_
    have hv := congrArg (fun t => t
      (((DoldKan.PInftyToNormalizedMooreComplex
        (Abelian.DoldKan.Γ.obj (connectiveHomComplex (R := R) x y))).f (n + 1) ≫
        (Abelian.DoldKan.equivalence.counitIso.hom.app
          (connectiveHomComplex (R := R) x y)).f (n + 1))
            ((standardDoldKanModuleIso (R := R) x y).hom.app
              (Opposite.op ⦋n + 1⦌) (f.app _ s)))) hc
    exact hv.trans he

/-- 実標準AW合成の負次数逆随伴は全次数で同じ全切断和を返す。 -/
theorem freeNegativeStandardAW_generator_eval (S T : SSet.{u}) (x y z : D)
    (g : S ⟶ standardHomSpace (R := R) y z)
    (f : T ⟶ standardHomSpace (R := R) x y) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n⦌)) (t : T.obj (Opposite.op ⦋n⦌)) :
    let h := (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := R) x y z
    (((freeNegativeChainsAdjunction R).homEquiv (S ⊗ T) (homObject R D x z)).symm
      (h ≫ standardDoldKanSpaceMap x z)).f (-(n : ℤ))
        (freeNegativeGenerator (S ⊗ T) n (s, t)) =
      ∑ c : (Finset.univ : Finset (Fin (n + 1))),
        awTerm (g.app _ s).val (f.app _ t).val Finset.univ c (-(n : ℤ)) (by simp) := by
  let h := (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := R) x y z
  have he := freeNegativeStandardHom_generator_eval (S ⊗ T) x z h n (s, t)
  exact he.trans (by rfl)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

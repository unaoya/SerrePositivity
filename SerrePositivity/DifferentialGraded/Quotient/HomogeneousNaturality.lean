module
public import SerrePositivity.DifferentialGraded.Functor.HomogeneousNaturality
public import SerrePositivity.DifferentialGraded.Quotient.EpsilonHomogeneousExt
public import SerrePositivity.DifferentialGraded.Quotient.PathCochainExt
public import SerrePositivity.DifferentialGraded.Quotient.PathGeneration

/-!
概要：実 Drinfeld 商の全次数自然性は元 Hom と指定 ε で判定できる。
方針：同じ有限 path の生成式と任意次数 cochain の判定を使う。
規約：ε に関する自然性を落とさず、元 Hom の自然性だけから延長しない。
使われ方：D-8 e の同じ収縮・商の全パラメータ作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (S : Set D) {E : Type w} [DGCategory R E]

lemma homogeneousNaturality_of_generators
    (F G : DGFunctor R (QuotientObject D S) E) {k : ℤ}
    (a : ∀ x, GradedHom R (F.obj x) (G.obj x) k)
    (ho : ∀ (x y : D) (p : ℤ) (f : GradedHom R x y p),
      homogeneousNaturalityAt R F G a (x := ⟨x⟩) (y := ⟨y⟩)
        ((originalHomInclusion R D S x y).f p f))
    (he : ∀ b : S, homogeneousNaturalityAt R F G a
      (x := ⟨b.val⟩) (y := ⟨b.val⟩) (p := -1) (epsilonElement R D S b)) :
    ∀ (x y : QuotientObject D S) (p : ℤ) (f : GradedHom R x y p),
      homogeneousNaturalityAt R F G a f := by
  let L (x y : D) := homogeneousNaturalityLeftCochain R F G a ⟨x⟩ ⟨y⟩
  let T (x y : D) := homogeneousNaturalityRightCochain R F G a ⟨x⟩ ⟨y⟩
  have hw (w : Word S) (x y : D) :
      (Cochain.ofHom (ι R D S x y w)).comp (L x y) (zero_add k) =
        (Cochain.ofHom (ι R D S x y w)).comp (T x y) (zero_add k) := by
    induction w generalizing x y with
    | nil =>
      apply Cochain.ext
      intro p n hpn
      subst n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
      exact ho x y p f
    | cons b w ih =>
      apply epsilonMiddleCochain_ext R
      intro p q n m hn hm f t
      subst m
      subst n
      simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
      change homogeneousNaturalityAt R F G a ((ι R D S x y (b :: w)).f (p + (-1 + q))
        (ιTensorObj (homObject R D x b.val) (epsilonComplex R ⊗ term R D w b.val y)
          p (-1 + q) (p + (-1 + q)) rfl
          (f ⊗ₜ[R] ιTensorObj (epsilonComplex R) (term R D w b.val y)
            (-1) q (-1 + q) rfl
            ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} R))).inv (1 : R) ⊗ₜ[R] t))))
      rw [path_inclusion_generator]
      have ht := congrArg (fun z => z t) (Cochain.congr_v (ih b.val y) q (q + k) rfl)
      simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at ht
      have htail : homogeneousNaturalityAt R F G a
          (x := ⟨b.val⟩) (y := ⟨y⟩) (p := q) ((ι R D S b.val y w).f q t) := ht
      exact homogeneousNaturalityAt_forward R F G a _ _ (ho x b.val p f)
        (homogeneousNaturalityAt_forward R F G a _ _ (he b) htail)
  intro x y p f
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  have h : L x y = T x y := pathCochain_ext R D S x y k (L x y) (T x y) (fun w => hw w x y)
  exact (homogeneousNaturalityAt_iff_cochain R F G a ⟨x⟩ ⟨y⟩).2 h p f

end SerrePositivity.DifferentialGraded.DGQuotient

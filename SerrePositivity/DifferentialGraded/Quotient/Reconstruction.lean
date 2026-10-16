module
public import SerrePositivity.DifferentialGraded.Quotient.Extension
public import SerrePositivity.DifferentialGraded.Quotient.PathGeneration
public import SerrePositivity.DifferentialGraded.Quotient.EpsilonCochainExt

/-! # 商dg関手を制限データのpath評価から再構成する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 商dg関手のHom写像を内部微分の始域上の次数0 cochainとして読む。 -/
def restrictionHomCochain (G : DGFunctor A (QuotientObject D S) E) (x y : D) :
    Cochain (internalHom A D S x y) (homObject A E (G.obj ⟨x⟩) (G.obj ⟨y⟩)) 0 :=
  Cochain.ofHoms (fun i => (G.map ⟨x⟩ ⟨y⟩).f i)

lemma restrictionHomCochain_path (G : DGFunctor A (QuotientObject D S) E)
    (w : Word S) (x y : D) :
    (Cochain.ofHom (ι A D S x y w)).comp (restrictionHomCochain A G x y) (zero_add 0) =
      pathEvaluation A (restrictContractedFunctor A D S G) w x y := by
  induction w generalizing x with
  | nil =>
    apply Cochain.ext₀
    intro i
    simp only [pathEvaluation_nil, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      restrictionHomCochain, Cochain.ofHoms_v]
    rfl
  | cons b w ih =>
    apply epsilonMiddleCochain_ext₀ A
    intro p q n hn a t
    have h := congrArg (fun v : (quotientHom A D S x y).X n => (G.map ⟨x⟩ ⟨y⟩).f n v)
      (path_inclusion_generator A D b w x y p q n hn a t)
    rw [DGFunctor.map_forward A G (x := ⟨x⟩) (y := ⟨b.val⟩) (z := ⟨y⟩),
      DGFunctor.map_forward A G (x := ⟨b.val⟩) (y := ⟨b.val⟩) (z := ⟨y⟩)] at h
    have ht := congrArg (fun f : Cochain (term A D w b.val y)
        (homObject A E (G.obj ⟨b.val⟩) (G.obj ⟨y⟩)) 0 =>
      f.v q q (add_zero q) t) (ih b.val)
    rw [cochain_ofHom_comp_apply, restrictionHomCochain, Cochain.ofHoms_v] at ht
    have htail := congrArg (fun z : (homObject A E (G.obj ⟨b.val⟩) (G.obj ⟨y⟩)).X q =>
      forward A
        ((G.map ⟨x⟩ ⟨b.val⟩).f p ((originalHomInclusion A D S x b.val).f p a))
        (forward A ((G.map ⟨b.val⟩ ⟨b.val⟩).f (-1) (epsilonElement A D S b)) z rfl)
        hn) ht
    let v : (term A D (b :: w) x y).X n :=
      ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        p ((-1) + q) n hn (a ⊗ₜ[A]
          ιTensorObj (epsilonComplex A) (term A D w b.val y) (-1) q ((-1) + q) rfl
            ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))
    have he := cochain_ofHom_comp_apply (ι A D S x y (b :: w))
      (restrictionHomCochain A G x y) (add_zero n) v
    rw [restrictionHomCochain, Cochain.ofHoms_v] at he
    have hr := pathEvaluation_cons_generator A (restrictContractedFunctor A D S G)
      b w x y p q n hn a t
    exact he.trans (h.trans (htail.trans hr.symm))

lemma restrictionHomCochain_eq_internalEvaluation (G : DGFunctor A (QuotientObject D S) E)
    (x y : D) :
    restrictionHomCochain A G x y =
      internalEvaluation A (restrictContractedFunctor A D S G) x y := by
  apply pathCochain_ext A D S x y 0
  intro w
  rw [restrictionHomCochain_path, internalEvaluation_precomp]

lemma extension_restrict (G : DGFunctor A (QuotientObject D S) E) :
    extension A (restrictContractedFunctor A D S G) = G := by
  apply EnrichedFunctor.ext (Complex A)
    (F := extension A (restrictContractedFunctor A D S G)) (G := G) (fun _ => rfl)
  intro x y
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      change quotientEvaluation A (restrictContractedFunctor A D S G) x y ≫
        eqToHom (by rfl) = G.map ⟨x⟩ ⟨y⟩
      rw [eqToHom_refl, Category.comp_id]
      apply HomologicalComplex.Hom.ext
      funext i
      rw [quotientEvaluation_f]
      have h := congrArg (fun f : Cochain (internalHom A D S x y)
          (homObject A E (G.obj ⟨x⟩) (G.obj ⟨y⟩)) 0 =>
        f.v i i (add_zero i)) (restrictionHomCochain_eq_internalEvaluation A G x y).symm
      simpa only [restrictionHomCochain, Cochain.ofHoms_v] using h

end SerrePositivity.DifferentialGraded.DGQuotient

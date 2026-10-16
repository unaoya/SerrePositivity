module
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import SerrePositivity.DifferentialGraded.Complexes.RightTripleCochainExt
public import SerrePositivity.DifferentialGraded.Complexes.TensorCompositionAssociativity

/-! # 前方二因子の写像による合成と後方cochainの評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 前方の合成を保つ写像と結合的な後方作用による、任意次数0 cochainの評価式。 -/
lemma tensorJoin_evaluation (U V W U' V' W' R T Y Z : Complex A)
    (F : U ⟶ U') (G : V ⟶ V') (H : W ⟶ W')
    (c : U ⊗ V ⟶ W) (c' : U' ⊗ V' ⟶ W')
    (d : W' ⊗ T ⟶ Z) (e : V' ⊗ T ⟶ Y) (k : U' ⊗ Y ⟶ Z)
    (hc : c ≫ H = (F ⊗ₘ G) ≫ c')
    (ha : (c' ▷ T) ≫ d = (α_ U' V' T).hom ≫ U' ◁ e ≫ k)
    (r : Cochain R T 0) :
    (Cochain.ofHom ((α_ U V R).inv ≫ c ▷ R)).comp
      ((tensorZeroCochain (Cochain.ofHom H) r).comp (Cochain.ofHom d) (zero_add 0))
      (zero_add 0) =
    (tensorZeroCochain (Cochain.ofHom F)
      ((tensorZeroCochain (Cochain.ofHom G) r).comp (Cochain.ofHom e) (zero_add 0))).comp
        (Cochain.ofHom k) (zero_add 0) := by
  apply rightTripleCochain_ext₀
  intro i j l a ha' x y z
  simp only [cochain_ofHom_comp_apply, chain_comp_apply, associator_inv_apply,
    whiskerRight_apply, cochain_comp_ofHom_apply, tensorZeroCochain_apply,
    Cochain.ofHom_v]
  have hmap := congrArg (fun f : U ⊗ V ⟶ W' =>
    f.f (i + j) (ιTensorObj U V i j (i + j) rfl (x ⊗ₜ[A] y))) hc
  simp only [chain_comp_apply, tensorMap_apply] at hmap
  rw [hmap]
  exact tensorComposition_assoc_apply U' V' T W' Y Z c' d e k ha i j l a (by omega)
    (F.f i x) (G.f j y) (r.v l l (add_zero l) z)

end SerrePositivity.DifferentialGraded

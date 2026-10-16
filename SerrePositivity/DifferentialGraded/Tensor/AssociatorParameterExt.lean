module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorElements

/-! # 三重生成元によるパラメータ付きHomの自然性の判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

lemma associatorLeft_homMap_post_pre_eq (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) {K U V T : Complex A}
    (a : K ⟶ homComplex A ((compose A B E F (compose A B C E P Q) R).value b f) U)
    (d : K ⟶ homComplex A V T) (h : U ⟶ T)
    (g : (compose A B E F (compose A B C E P Q) R).value b f ⟶ V)
    (heq : ∀ (p : ℤ) (x : K.X p) (c : C) (e : E) (k r s i m n : ℤ)
      (hi : r + s = i) (hm : k + i = m) (hn : m + p = n)
      (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s),
      h.f n (((a.f p x).v m n hn)
        (associatorLeftElement A B C E F P Q R b c e f t q v hi hm)) =
      (d.f p x).v m n hn
        (g.f m (associatorLeftElement A B C E F P Q R b c e f t q v hi hm))) :
    a ≫ homPostcompose _ h = d ≫ homPrecompose g T := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (homPostcompose _ h).f p (a.f p x) = (homPrecompose g _).f p (d.f p x)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply associatorLeft_cochain_element_ext A B C E F P Q R b f
  intro c e k r s i m n hi hm hn t q v
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v]
  exact heq p x c e k r s i m n hi hm hn t q v

end SerrePositivity.DifferentialGraded.BimoduleTensor

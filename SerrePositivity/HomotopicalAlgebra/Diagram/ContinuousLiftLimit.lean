module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousLiftSystem

/-! # Extending coherent lifts at a continuous limit stage -/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.DiagramModel.ContinuousLifts
variable {J : Type w} [LinearOrder J] {C : Type u} [Category.{v} C]
  {D U V : J ⥤ C} {p : U ⟶ V} {b : D ⟶ V} {j : J}

namespace Limit
variable (s : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ system p b).sections)

def lowerHom (i : J) (hi : i < j) : D.obj i ⟶ U.obj i :=
  (s.val (Opposite.op ⟨i, hi⟩)).hom i le_rfl

lemma lowerHom_eq (i : J) (hi : i < j) (k : J) (hk : k ≤ i) :
    lowerHom s k (hk.trans_lt hi) = (s.val (Opposite.op ⟨i, hi⟩)).hom k hk := by
  have h := s.property (homOfLE (show (⟨k, hk.trans_lt hi⟩ : Set.Iio j) ≤ ⟨i, hi⟩ from hk)).op
  change (s.val (Opposite.op ⟨i, hi⟩)).restrict hk = s.val (Opposite.op ⟨k, hk.trans_lt hi⟩) at h
  exact (congrArg (fun x => x.hom k le_rfl) h).symm

lemma lowerHom_naturality {i k : J} (hik : i ≤ k) (hk : k < j) :
    D.map (homOfLE hik) ≫ lowerHom s k hk =
      lowerHom s i (hik.trans_lt hk) ≫ U.map (homOfLE hik) := by
  rw [lowerHom_eq s k hk i hik]
  exact (s.val (Opposite.op ⟨k, hk⟩)).naturality hik le_rfl

lemma lowerHom_fac (i : J) (hi : i < j) : lowerHom s i hi ≫ p.app i = b.app i :=
  (s.val (Opposite.op ⟨i, hi⟩)).fac i le_rfl

def cocone : Cocone ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor ⋙ D) where
  pt := U.obj j
  ι := {
    app i := lowerHom s i.val i.property ≫ U.map (homOfLE i.property.le)
    naturality i k f := by
      change D.map (homOfLE (leOfHom f)) ≫
          (lowerHom s k.val k.property ≫ U.map (homOfLE k.property.le)) =
        (lowerHom s i.val i.property ≫ U.map (homOfLE i.property.le)) ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc, lowerHom_naturality s (leOfHom f) k.property,
        Category.assoc, ← U.map_comp]
      rfl }

variable [D.IsWellOrderContinuous] (hj : Order.IsSuccLimit j)

def topHom : D.obj j ⟶ U.obj j := (D.isColimitOfIsWellOrderContinuous j hj).desc (cocone s)

@[reassoc]
lemma map_topHom (i : J) (hi : i < j) :
    D.map (homOfLE hi.le) ≫ topHom s hj = lowerHom s i hi ≫ U.map (homOfLE hi.le) :=
  (D.isColimitOfIsWellOrderContinuous j hj).fac (cocone s) ⟨i, hi⟩

lemma topHom_fac : topHom s hj ≫ p.app j = b.app j := by
  apply (D.isColimitOfIsWellOrderContinuous j hj).hom_ext
  intro i
  change D.map (homOfLE i.property.le) ≫ (topHom s hj ≫ p.app j) =
    D.map (homOfLE i.property.le) ≫ b.app j
  rw [map_topHom_assoc s hj i.val i.property, p.naturality, ← Category.assoc,
    lowerHom_fac s i.val i.property, b.naturality]

def hom (i : J) (hi : i ≤ j) : D.obj i ⟶ U.obj i := by
  classical
  by_cases h : i < j
  · exact lowerHom s i h
  · have he : i = j := le_antisymm hi (le_of_not_gt h)
    exact eqToHom (congrArg D.obj he) ≫ topHom s hj ≫ eqToHom (congrArg U.obj he.symm)

lemma hom_of_lt (i : J) (hi : i ≤ j) (h : i < j) : hom s hj i hi = lowerHom s i h := by
  simp only [hom, dite_eq_left h]

lemma hom_top (h : j ≤ j) : hom s hj j h = topHom s hj := by simp [hom]

def extend : Partial p b j where
  hom := hom s hj
  naturality {i k} hik hk := by
    by_cases hk₀ : k < j
    · rw [hom_of_lt s hj k hk hk₀, hom_of_lt s hj i _ (hik.trans_lt hk₀)]
      exact lowerHom_naturality s hik hk₀
    · have hk₁ : k = j := le_antisymm hk (le_of_not_gt hk₀)
      subst k
      by_cases hi₀ : i < j
      · rw [hom_top s hj, hom_of_lt s hj i _ hi₀]
        exact map_topHom s hj i hi₀
      · have hi₁ : i = j := le_antisymm hik (le_of_not_gt hi₀)
        subst i
        simp only [homOfLE_refl, D.map_id, U.map_id, Category.id_comp, Category.comp_id]
  fac i hi := by
    by_cases hi₀ : i < j
    · rw [hom_of_lt s hj i hi hi₀]
      exact lowerHom_fac s i hi₀
    · have hi₁ : i = j := le_antisymm hi (le_of_not_gt hi₀)
      subst i
      rw [hom_top s hj]
      exact topHom_fac s hj

lemma restrict_extend (i : J) (hi : i < j) :
    (extend s hj).restrict hi.le = s.val (Opposite.op ⟨i, hi⟩) := by
  apply Partial.ext
  funext k hk
  change hom s hj k (hk.trans hi.le) = _
  rw [hom_of_lt s hj k _ (hk.trans_lt hi)]
  exact lowerHom_eq s i hi k hk

end Limit
end SerrePositivity.DiagramModel.ContinuousLifts

module

public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # The universal Yoneda copower diagram

At (k,l) the diagram is the coproduct of X over actual arrows l → k.
Its colimit is the constant X diagram. Evaluating at l gives the actual
free diagram at l, with no assumption on cofibrancy of the constant diagram.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.DiagramModel.YonedaWeights
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [HasCoproducts.{w} C] (X : C)

def family : K ⥤ Kᵒᵖ ⥤ C where
  obj k :=
    { obj := fun l => ∐ (fun _ : l.unop ⟶ k => X)
      map := fun f => Sigma.map' (fun h => f.unop ≫ h) (fun _ => 𝟙 X)
      map_id := by intros; apply Sigma.hom_ext; intro h; simp
      map_comp := by intros; apply Sigma.hom_ext; intro h; simp [Category.assoc] }
  map g :=
    { app := fun l => Sigma.map' (fun h : l.unop ⟶ _ => h ≫ g) (fun _ => 𝟙 X)
      naturality := by intros; apply Sigma.hom_ext; intro h; simp [Category.assoc] }
  map_id k := by
    apply NatTrans.ext
    funext l
    apply Sigma.hom_ext
    intro h
    simp
  map_comp f g := by
    apply NatTrans.ext
    funext l
    apply Sigma.hom_ext
    intro h
    simp [Category.assoc]

def evaluationIso (l : Kᵒᵖ) :
    family K X ⋙ (evaluation Kᵒᵖ C).obj l ≅ (evaluationLeftAdjoint C l.unop).obj X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro k k' f
    apply Sigma.hom_ext
    intro h
    simp [family, evaluationLeftAdjoint])

def opCopowerIso (k : K) (l : Kᵒᵖ) :
    (∐ fun _ : l.unop ⟶ k => X) ≅ (∐ fun _ : Opposite.op k ⟶ l => X) where
  hom := Sigma.map' (fun h : l.unop ⟶ k => h.op) (fun _ => 𝟙 X)
  inv := Sigma.map' (fun h : Opposite.op k ⟶ l => h.unop) (fun _ => 𝟙 X)
  hom_inv_id := by apply Sigma.hom_ext; intro h; simp
  inv_hom_id := by apply Sigma.hom_ext; intro h; simp

def freeWeightIso (k : K) :
    (family K X).obj k ≅ (evaluationLeftAdjoint C (Opposite.op k)).obj X :=
  NatIso.ofComponents (fun l => opCopowerIso K X k l) (by
    intro l l' f
    apply Sigma.hom_ext
    intro h
    simp [family, evaluationLeftAdjoint, opCopowerIso])

def augmentation : family K X ⟶ (Functor.const K).obj ((Functor.const Kᵒᵖ).obj X) where
  app k :=
    { app := fun _ => Sigma.desc (fun _ => 𝟙 X)
      naturality := by intros; apply Sigma.hom_ext; intro h; simp [family] }
  naturality k k' f := by
    apply NatTrans.ext
    funext l
    apply Sigma.hom_ext
    intro h
    simp [family]

def cocone : Cocone (family K X) :=
  Cocone.mk ((Functor.const Kᵒᵖ).obj X) (augmentation K X)

def isColimit : IsColimit (cocone K X) := by
  apply evaluationJointlyReflectsColimits
  intro l
  refine
    { desc := fun c => Sigma.ι (fun _ : l.unop ⟶ l.unop => X) (𝟙 l.unop) ≫ c.ι.app l.unop
      fac := ?_
      uniq := ?_ }
  · intro c k
    apply Sigma.hom_ext
    intro h
    have hw := congrArg (fun z => Sigma.ι (fun _ : l.unop ⟶ l.unop => X) (𝟙 l.unop) ≫ z)
      (c.w h)
    simpa [family, cocone, augmentation] using hw.symm
  · intro c f hf
    have hw := congrArg (fun z => Sigma.ι (fun _ : l.unop ⟶ l.unop => X) (𝟙 l.unop) ≫ z)
      (hf l.unop)
    change Sigma.ι (fun _ : l.unop ⟶ l.unop => X) (𝟙 l.unop) ≫
      (Sigma.desc (fun _ : l.unop ⟶ l.unop => 𝟙 X) ≫ f) = _ at hw
    have he : Sigma.ι (fun _ : l.unop ⟶ l.unop => X) (𝟙 l.unop) ≫
        Sigma.desc (fun _ : l.unop ⟶ l.unop => 𝟙 X) = 𝟙 X := Sigma.ι_comp_desc _ _
    exact (Category.id_comp f).symm.trans
      ((congrArg (fun z => z ≫ f) he.symm).trans ((Category.assoc _ _ _).trans hw))

def colimitIso [HasColimit (family K X)] :
    colimit (family K X) ≅ (Functor.const Kᵒᵖ).obj X :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimit K X)

end SerrePositivity.DiagramModel.YonedaWeights

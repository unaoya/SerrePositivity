module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ExtraDegeneracyInterval
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # Extra degeneracies give interval contractions and localized augmentation isomorphisms -/

@[expose] public section
universe v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.ExtraDegeneracyContraction
open ExtraDegeneracyInterval
variable {A : SimplicialObject.Augmented (Type v)}
  (ed : SimplicialObject.Augmented.ExtraDegeneracy A)

lemma intervalMap_zero : SSet.ι₀ ≫ intervalMap ed = A.hom ≫ ed.section_ := by
  ext n x
  change A.left.map (SimplexPrefix.cut n.unop (SimplexPrefix.endpoint n.unop 0)).op
      (ed.s n.unop.len x) =
    A.left.map (SimplexCategory.isTerminalZero.from n.unop).op (ed.s' (A.hom.app n x))
  rw [SimplexPrefix.cut_zero_factor]
  simp only [op_comp, A.left.map_comp]
  have hs := types_congr_hom ((extra ed).naturality (SimplexPrefix.zeroVertex n.unop).op) x
  change ed.s 0 (A.left.map (SimplexPrefix.zeroVertex n.unop).op x) =
    A.left.map (SimplexPrefix.functor.map (SimplexPrefix.zeroVertex n.unop)).op
      (ed.s n.unop.len x) at hs
  have he := types_congr_hom ed.s₀_comp_δ₁
    (A.left.map (SimplexPrefix.zeroVertex n.unop).op x)
  change A.left.map (SimplexCategory.δ (1 : Fin 2)).op
      (ed.s 0 (A.left.map (SimplexPrefix.zeroVertex n.unop).op x)) =
    ed.s' (A.hom.app (Opposite.op (SimplexCategory.mk 0))
      (A.left.map (SimplexPrefix.zeroVertex n.unop).op x)) at he
  have ha := types_congr_hom (A.hom.naturality (SimplexPrefix.zeroVertex n.unop).op) x
  change A.hom.app (Opposite.op (SimplexCategory.mk 0))
    (A.left.map (SimplexPrefix.zeroVertex n.unop).op x) = A.hom.app n x at ha
  change A.left.map (SimplexCategory.isTerminalZero.from n.unop).op
      (A.left.map (SimplexCategory.δ (1 : Fin 2)).op
        (A.left.map (SimplexPrefix.functor.map (SimplexPrefix.zeroVertex n.unop)).op
          (ed.s n.unop.len x))) = _
  rw [← hs, he, ha]

lemma intervalMap_one : SSet.ι₁ ≫ intervalMap ed = 𝟙 A.left := by
  ext n x
  change A.left.map (SimplexPrefix.cut n.unop (SimplexPrefix.endpoint n.unop 1)).op
    (ed.s n.unop.len x) = x
  rw [SimplexPrefix.cut_one]
  exact types_congr_hom (ed.s_comp_δ₀ n.unop.len) x

def contraction : SSet.Homotopy (A.hom ≫ ed.section_) (𝟙 A.left) where
  h := intervalMap ed
  h₀ := intervalMap_zero ed
  h₁ := intervalMap_one ed
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
def comparisonIso : L.obj A.left ≅ L.obj ((SimplicialObject.const (Type v)).obj A.right) where
  hom := L.map A.hom
  inv := L.map ed.section_
  hom_inv_id := (L.map_comp _ _).symm.trans
    ((AnodyneHomotopy.map_homotopy_eq L hL (contraction ed)).trans (L.map_id _))
  inv_hom_id := (L.map_comp _ _).symm.trans
    ((congrArg L.map ed.section_comp_hom).trans (L.map_id _))

include ed in
lemma localized_augmentation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map A.hom) :=
  (comparisonIso ed AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)).isIso_hom

end SerrePositivity.SimplicialModel.ExtraDegeneracyContraction

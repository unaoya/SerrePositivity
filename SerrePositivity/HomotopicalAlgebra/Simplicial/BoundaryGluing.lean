module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-! # Gluing prescribed simplicial faces from their actual intersections

The boundary map is constructed from a compatible family of facet maps.
Compatibility on actual subcomplex intersections is retained, so previously
chosen lower-dimensional comparisons can be prescribed before filling.
The construction is model independent and also works in dimension zero.
-/

@[expose] public section
universe v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SubcomplexGluing
variable {X P : SSet.{v}} {I : Type w} (A : X.Subcomplex) (U : I → X.Subcomplex)
  (hU : ⨆ i, U i = A)

abbrev diagram : SSet.Subcomplex.MulticoequalizerDiagram A U (fun i j => U i ⊓ U j) :=
  ⟨hU, fun _ _ => rfl⟩

def desc (f : ∀ i, (U i).toSSet ⟶ P)
    (hf : ∀ i j, SSet.Subcomplex.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      SSet.Subcomplex.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) : A.toSSet ⟶ P :=
  Multicofork.IsColimit.desc (diagram A U hU).isColimit f (fun ij => hf ij.1 ij.2)

@[reassoc]
lemma desc_fac (f : ∀ i, (U i).toSSet ⟶ P)
    (hf : ∀ i j, SSet.Subcomplex.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      SSet.Subcomplex.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) (i : I) :
    SSet.Subcomplex.homOfLE (show U i ≤ A from hU ▸ le_iSup U i) ≫ desc A U hU f hf = f i :=
  Multicofork.IsColimit.fac (diagram A U hU).isColimit f (fun ij => hf ij.1 ij.2) i

lemma hom_ext {f g : A.toSSet ⟶ P}
    (h : ∀ i, SSet.Subcomplex.homOfLE (show U i ≤ A from hU ▸ le_iSup U i) ≫ f =
      SSet.Subcomplex.homOfLE (show U i ≤ A from hU ▸ le_iSup U i) ≫ g) : f = g :=
  Multicofork.IsColimit.hom_ext (diagram A U hU).isColimit h

end SerrePositivity.SimplicialModel.SubcomplexGluing

namespace SerrePositivity.SimplicialModel.BoundaryGluing

abbrev facet (n : ℕ) (i : Fin (n + 1)) :
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n)).Subcomplex :=
  SSet.stdSimplex.face {i}ᶜ

abbrev Compatible {P : SSet.{v}} {n : ℕ} (f : ∀ i, (facet n i).toSSet ⟶ P) : Prop :=
  ∀ i j, SSet.Subcomplex.homOfLE (inf_le_left : facet n i ⊓ facet n j ≤ facet n i) ≫ f i =
    SSet.Subcomplex.homOfLE (inf_le_right : facet n i ⊓ facet n j ≤ facet n j) ≫ f j

def desc {P : SSet.{v}} {n : ℕ} (f : ∀ i, (facet n i).toSSet ⟶ P) (hf : Compatible f) :
    (SSet.boundary.{v} n).toSSet ⟶ P :=
  SubcomplexGluing.desc (SSet.boundary n) (facet n) (SSet.boundary_eq_iSup n).symm f hf

@[reassoc]
lemma desc_fac {P : SSet.{v}} {n : ℕ} (f : ∀ i, (facet n i).toSSet ⟶ P) (hf : Compatible f)
    (i : Fin (n + 1)) : SSet.boundary.faceι i ≫ desc f hf = f i :=
  SubcomplexGluing.desc_fac (SSet.boundary n) (facet n) (SSet.boundary_eq_iSup n).symm f hf i

abbrev standardDiagram (n : ℕ) : SSet.Subcomplex.MulticoequalizerDiagram (SSet.boundary.{v} n)
    (facet n) (fun i j => SSet.stdSimplex.face {i, j}ᶜ) where
  iSup_eq := (SSet.boundary_eq_iSup n).symm
  eq_inf i j := by
    rw [SSet.stdSimplex.face_inter_face]
    congr
    aesop

/-- The usual face identities, for a boundary in dimension at least two. -/
abbrev StandardCompatible {P : SSet.{v}} {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)) ⟶ P)) : Prop :=
  ∀ (j k : Fin (n + 3)) (hjk : j < k),
    SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j =
      SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
def standardCofork {P : SSet.{v}} {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)) ⟶ P))
    (hf : StandardCompatible f) :
    Multicofork ((standardDiagram.{v} (n + 2)).multispanIndex.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ P (fun j => (SSet.stdSimplex.faceSingletonComplIso j).inv ≫ f j) (by
    rintro ⟨⟨j, k⟩, hjk : j < k⟩
    dsimp
    rw [SSet.stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred_assoc
      _ _ hjk,
      SSet.stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred_assoc
        _ _ hjk, hf j k hjk])

def standardDesc {P : SSet.{v}} {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)) ⟶ P))
    (hf : StandardCompatible f) : (SSet.boundary.{v} (n + 2)).toSSet ⟶ P :=
  ((standardDiagram.{v} (n + 2)).isColimit').desc (standardCofork f hf)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
lemma standardDesc_fac {P : SSet.{v}} {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)) ⟶ P))
    (hf : StandardCompatible f) (k : Fin (n + 3)) :
    SSet.boundary.ι k ≫ standardDesc f hf = f k := by
  rw [← cancel_epi (SSet.stdSimplex.faceSingletonComplIso k).inv]
  simpa [standardDesc, standardCofork] using!
    ((standardDiagram.{v} (n + 2)).isColimit').fac (standardCofork f hf) (.right k)

end SerrePositivity.SimplicialModel.BoundaryGluing

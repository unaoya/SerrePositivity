module
public import SerrePositivity.DifferentialGraded.Quotient.Reconstruction

/-! # 指定収縮データ付きdg関手に関する明示的商の厳密普遍性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商からのdg関手は、元のdg関手と選択済み収縮データと一対一に対応する。 -/
def universalEquiv (S : Set D) (E : Type w) [DGCategory A E] :
    DGFunctor A (QuotientObject D S) E ≃ ContractedFunctor A D S E where
  toFun := restrictContractedFunctor A D S
  invFun := extension A
  left_inv := extension_restrict A
  right_inv := restrict_extension A

variable {D} {S : Set D} {E : Type w} [DGCategory A E]

lemma extension_unique (G : DGFunctor A (QuotientObject D S) E)
    (C : ContractedFunctor A D S E) (h : restrictContractedFunctor A D S G = C) :
    G = extension A C := by
  rw [← h, extension_restrict]

lemma existsUnique_extension (C : ContractedFunctor A D S E) :
    ∃! G : DGFunctor A (QuotientObject D S) E, restrictContractedFunctor A D S G = C := by
  refine ⟨extension A C, restrict_extension A C, ?_⟩
  intro G hG
  exact extension_unique A G C hG

variable {T : Type t} [DGCategory A T]

lemma restrictContractedFunctor_comp (G : DGFunctor A (QuotientObject D S) E)
    (H : DGFunctor A E T) :
    restrictContractedFunctor A D S (G.comp H) =
      (restrictContractedFunctor A D S G).postcomp A H := by
  apply ContractedFunctor.ext A
  · apply EnrichedFunctor.ext (Complex A)
      (F := (restrictContractedFunctor A D S (G.comp H)).toDGFunctor)
      (G := ((restrictContractedFunctor A D S G).postcomp A H).toDGFunctor) (fun _ => rfl)
    intro x y
    change (originalHomInclusion A D S x y ≫ (G.map ⟨x⟩ ⟨y⟩ ≫
        H.map (G.obj ⟨x⟩) (G.obj ⟨y⟩))) ≫ eqToHom (by rfl) =
      (originalHomInclusion A D S x y ≫ G.map ⟨x⟩ ⟨y⟩) ≫ H.map (G.obj ⟨x⟩) (G.obj ⟨y⟩)
    rw [eqToHom_refl, Category.comp_id, Category.assoc]
  · exact heq_of_eq (funext (fun _ => rfl))

lemma extension_postcomp (C : ContractedFunctor A D S E) (H : DGFunctor A E T) :
    extension A (C.postcomp A H) = (extension A C).comp H := by
  apply (universalEquiv A D S T).injective
  change restrictContractedFunctor A D S (extension A (C.postcomp A H)) =
    restrictContractedFunctor A D S ((extension A C).comp H)
  rw [restrict_extension, restrictContractedFunctor_comp, restrict_extension]

end SerrePositivity.DifferentialGraded.DGQuotient

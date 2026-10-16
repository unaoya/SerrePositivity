module
public import SerrePositivity.DifferentialGraded.Quotient.EpsilonContraction
public import SerrePositivity.DifferentialGraded.Functor.ContractingElements

/-! # 指定収縮データを持つdg関手と商からの制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- Sの各対象の像に、選択した次数−1の収縮元を持つdg関手。 -/
structure ContractedFunctor (S : Set D) (E : Type w) [DGCategory A E] where
  toDGFunctor : DGFunctor A D E
  homotopy : ∀ b : S, GradedHom A (toDGFunctor.obj b.val) (toDGFunctor.obj b.val) (-1)
  d_homotopy : ∀ b : S,
    (homObject A E (toDGFunctor.obj b.val) (toDGFunctor.obj b.val)).d (-1) 0 (homotopy b) =
      (unitElement A (toDGFunctor.obj b.val)).val

variable {D} {E : Type w} [DGCategory A E] {T : Type t} [DGCategory A T]

/-- 指定収縮データをdg関手で後合成する。 -/
def ContractedFunctor.postcomp {S : Set D} (C : ContractedFunctor A D S E)
    (G : DGFunctor A E T) : ContractedFunctor A D S T where
  toDGFunctor := C.toDGFunctor.comp G
  homotopy b := (G.map (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val)).f (-1) (C.homotopy b)
  d_homotopy b := G.map_contractingElement A (C.toDGFunctor.obj b.val)
    (C.homotopy b) (C.d_homotopy b)

variable (D) [Small.{u} D]

/-- 商の包含と指定εは、選択済み収縮データを持つ。 -/
def canonicalContractedFunctor (S : Set D) : ContractedFunctor A D S (QuotientObject D S) where
  toDGFunctor := inclusion A D S
  homotopy b := epsilonElement A D S b
  d_homotopy b := differential_epsilonElement A D S b

/-- 商からのdg関手を制限し、指定εの像を収縮として保持する。 -/
def restrictContractedFunctor (S : Set D) (G : DGFunctor A (QuotientObject D S) E) :
    ContractedFunctor A D S E := (canonicalContractedFunctor A D S).postcomp A G

lemma restrictContractedFunctor_homotopy (S : Set D)
    (G : DGFunctor A (QuotientObject D S) E) (b : S) :
    (restrictContractedFunctor A D S G).homotopy b =
      (G.map ⟨b.val⟩ ⟨b.val⟩).f (-1) (epsilonElement A D S b) := rfl

end SerrePositivity.DifferentialGraded.DGQuotient

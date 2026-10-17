module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryFaces
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathAction
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainInterchange

/-! # 指定境界の挿入と後方の次数+1 cochainの反交換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

/-- 指定境界への置換と後方作用の順序を交換すると負号が付く。
生成元の次数は任意で、両作用素の次数+1からこの負号が出る。 -/
lemma replaceMiddle_tail_anticommute (i : I) (K P Q : Complex A) (f : Cochain P Q 1) :
    (C.replaceMiddle A D I i K P).comp
      ((tensorLeftHom K _ _).f 1
        ((tensorLeftHom (homObject A D (C.source i) (C.target i)) P Q).f 1 f))
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom K _ _).f 1
      ((tensorLeftHom (C.generator A D I i) P Q).f 1 f)).comp
      (C.replaceMiddle A D I i K Q) (show (1 : ℤ) + 1 = 2 by omega)) :=
  tensorLeftHom_cochain_anticommute K _ _ _ _ 1 1 2 (by omega) (by omega) _ _ _ _
    (tensorCochain_odd_anticommute (C.generator A D I i)
      (homObject A D (C.source i) (C.target i)) P Q (C.boundaryCochain A D I i) f)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family

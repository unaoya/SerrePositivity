module
public import SerrePositivity.KST.Fibration.RelativeSKernelSquare
public import SerrePositivity.KST.SConstruction.CoreAdditivity

/-! # 元の相対 S の商射影と商の core S 実現の厳密な因子化 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の core 包含の後の相対商射影は、同じ完全商関手の core S 写像そのもの。 -/
theorem relativeSimplicialQuotientMap_core {B C : StableCategory.{u}}
    (q : ExactMap B C) :
    relativeSimplicialSConstructionCoreInclusion q.hom ≫ relativeSimplicialQuotientMap q =
      coreSExactMap q := by
  apply NatTrans.ext
  funext n
  exact relativeSQuotientMap_core q n.unop.len

/-- 同じ商の core 実現射を、元の相対 S 実現を通る厳密な因子化として保持する。 -/
theorem relativeSQuotientRealization_core {B C : StableCategory.{u}}
    (q : ExactMap B C) :
    simplicialDiagonalFunctor.map (relativeSimplicialSConstructionCoreInclusion q.hom) ≫
        simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q) =
      simplicialDiagonalFunctor.map (coreSExactMap q) := by
  rw [← Functor.map_comp, relativeSimplicialQuotientMap_core]

end SerrePositivity.KST.Fibration

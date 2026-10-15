module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalRepresentables
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AdjunctionHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.QuillenStandardFrame

/-! # Rows of the actual diagonal right adjoint are internal Homs

The representable computation, the closed adjunction, and the actual
standard-simplex Yoneda isomorphism identify each row naturally in both
its simplicial operators and the target. No model hypotheses are used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.BisimplicialModel

abbrev tensorFrame (n : SimplexCategory) : SimplexCategory ⥤ SSet.{v} :=
  SSet.stdSimplex ⋙ tensorLeft (SSet.stdSimplex.obj n)

/-- Identify an entire row, with both inner-simplex and target naturality. -/
def rightAdjointRowTensorIso (n : SimplexCategory) :
    rightAdjoint.{v} ⋙ (CategoryTheory.evaluation SimplexCategoryᵒᵖ SSet.{v}).obj
      (Opposite.op n) ≅ cosimplicialHom (tensorFrame n) :=
  NatIso.ofComponents (fun Z => NatIso.ofComponents
    (fun m => Equiv.toIso (rightAdjointValueEquiv Z n m.unop)) (by
      intro m l g
      ext x
      exact rightAdjointValueEquiv_inner Z n g.unop x)) (by
    intro Z Z' h
    ext m x
    exact rightAdjointValueEquiv_target h n m.unop x)

/-- The actual right Kan extension row is the actual closed internal Hom. -/
def rightAdjointRowInternalHomIso (n : SimplexCategory) :
    rightAdjoint.{v} ⋙ (CategoryTheory.evaluation SimplexCategoryᵒᵖ SSet.{v}).obj
      (Opposite.op n) ≅ ihom (SSet.stdSimplex.obj n) :=
  rightAdjointRowTensorIso n ≪≫
    adjunctionHomIsoSameUniverse (ihom.adjunction (SSet.stdSimplex.obj n)) SSet.stdSimplex ≪≫
    Functor.isoWhiskerLeft _ QuillenStandardFrame.homIso ≪≫ Functor.rightUnitor _

@[simp]
lemma rightAdjointRowInternalHomIso_formula (Z : SSet.{v}) (n m : SimplexCategory)
    (x : ((rightAdjoint.obj Z).obj (Opposite.op n)).obj (Opposite.op m)) :
    ((rightAdjointRowInternalHomIso n).hom.app Z).app (Opposite.op m) x =
      SSet.yonedaEquiv ((ihom.adjunction (SSet.stdSimplex.obj n)).homEquiv
        (SSet.stdSimplex.obj m) Z (rightAdjointValueEquiv Z n m x)) := rfl

lemma rightAdjointRowInternalHomIso_outer (Z : SSet.{v}) {n' n : SimplexCategory}
    (g : n' ⟶ n) :
    (rightAdjoint.obj Z).map g.op ≫ (rightAdjointRowInternalHomIso n').hom.app Z =
      (rightAdjointRowInternalHomIso n).hom.app Z ≫
        (MonoidalClosed.internalHom.map (SSet.stdSimplex.map g).op).app Z := by
  ext m x
  let adj := MonoidalClosed.internalHomAdjunction₂ (C := SSet.{v})
  let h := rightAdjointValueEquiv Z n m.unop x
  let p := (MonoidalClosed.internalHom.map (SSet.stdSimplex.map g).op).app Z
  change ((rightAdjointRowInternalHomIso n').hom.app Z).app m
      (((rightAdjoint.obj Z).map g.op).app m x) =
    p.app m (((rightAdjointRowInternalHomIso n).hom.app Z).app m x)
  calc
    _ = SSet.yonedaEquiv ((ihom.adjunction (SSet.stdSimplex.obj n')).homEquiv
        (SSet.stdSimplex.obj m.unop) Z
          (rightAdjointValueEquiv Z n' m.unop (((rightAdjoint.obj Z).map g.op).app m x))) :=
      rightAdjointRowInternalHomIso_formula _ _ _ _
    _ = SSet.yonedaEquiv ((ihom.adjunction (SSet.stdSimplex.obj n')).homEquiv
        (SSet.stdSimplex.obj m.unop) Z
          ((SSet.stdSimplex.map g ▷ SSet.stdSimplex.obj m.unop) ≫ h)) :=
      congrArg (fun k => SSet.yonedaEquiv ((ihom.adjunction (SSet.stdSimplex.obj n')).homEquiv
        (SSet.stdSimplex.obj m.unop) Z k)) (rightAdjointValueEquiv_outer Z g m.unop x)
    _ = SSet.yonedaEquiv (adj.homEquiv h ≫ p) :=
      congrArg SSet.yonedaEquiv (adj.homEquiv_naturality_one (SSet.stdSimplex.map g) h)
    _ = p.app m (SSet.yonedaEquiv (adj.homEquiv h)) := SSet.yonedaEquiv_comp _ _
    _ = _ := congrArg (fun k => p.app m k)
      (rightAdjointRowInternalHomIso_formula Z n m.unop x).symm

/-- The explicit internal-Hom family, in all outer degrees. -/
abbrev internalHomRight : SSet.{v} ⥤ SimplexCategoryᵒᵖ ⥤ SSet.{v} :=
  (SSet.stdSimplex.op ⋙ MonoidalClosed.internalHom).flip

/-- The actual right Kan extension is naturally the standard-simplex internal Hom. -/
def rightAdjointInternalHomIso : rightAdjoint.{v} ≅ internalHomRight.{v} :=
  NatIso.ofComponents (fun Z => NatIso.ofComponents
    (fun n => (rightAdjointRowInternalHomIso n.unop).app Z) (by
      intro n m g
      exact rightAdjointRowInternalHomIso_outer Z g.unop)) (by
    intro Z Z' h
    apply NatTrans.ext
    funext n
    exact (rightAdjointRowInternalHomIso n.unop).hom.naturality h)

/-- The diagonal adjunction with the now explicit internal-Hom right adjoint. -/
def diagonalInternalHomAdjunction : diagonal.{v} ⊣ internalHomRight.{v} :=
  diagonalAdjunction.ofNatIsoRight rightAdjointInternalHomIso

instance internalHomRight_isRightAdjoint : internalHomRight.{v}.IsRightAdjoint :=
  diagonalInternalHomAdjunction.isRightAdjoint

end SerrePositivity.BisimplicialModel

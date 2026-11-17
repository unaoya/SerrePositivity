module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowMaps
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAdjunction

/-!
概要：元のbarの二重単体集合の対角を、指定されたsimplicial replacementへ厳密に同定する。
方針：同じ基底射列を保持し、係数の単体のYoneda表示だけを変える。
規約：元の係数射の像についても同じ同型との自然性を示す。
使われ方：IS-W2 R03f.2の対角のleft anodyne性の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.BisimplicialModel
variable {I : Type u} [SmallCategory I]

/-- 同じ基底射列の係数を、その同じ単体のYoneda表示にする全写像。 -/
def simplicialReplacementDiagonalHom (F : I ⥤ SSet.{u}) :
    diagonal.obj (simplicialReplacementRows F) ⟶ simplicialReplacement F where
  app q := ↾fun s => ⟨s.1,
    (SSet.yonedaEquiv (X := F.obj (s.1.obj 0)) (n := q.unop)).symm s.2⟩
  naturality q r α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ,x⟩
    refine Sigma.ext (show α.unop.toOrderHom.monotone.functor ⋙ σ =
      α.unop.toOrderHom.monotone.functor ⋙ σ from rfl) ?_
    apply heq_of_eq
    change (SSet.yonedaEquiv (X := F.obj (σ.obj (α.unop.toOrderHom 0))) (n := r.unop)).symm
      ((F.obj (σ.obj (α.unop.toOrderHom 0))).map α
        ((F.map (σ.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0))))).app q x)) =
      stdSimplex.map α.unop ≫
        (SSet.yonedaEquiv (X := F.obj (σ.obj 0)) (n := q.unop)).symm x ≫
          F.map (σ.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0))))
    exact (SSet.yonedaEquiv_symm_naturality_left (X := F.obj (σ.obj (α.unop.toOrderHom 0)))
      α.unop ((F.map (σ.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0))))).app q x)).symm.trans
        (congrArg (fun z => stdSimplex.map α.unop ≫ z)
          (SSet.yonedaEquiv_symm_comp x
            (F.map (σ.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0)))))).symm)

/-- 元の対角と指定されたsimplicial replacementの同型。 -/
def simplicialReplacementDiagonalIso (F : I ⥤ SSet.{u}) :
    diagonal.obj (simplicialReplacementRows F) ≅ simplicialReplacement F := by
  letI : ∀ q, IsIso ((simplicialReplacementDiagonalHom F).app q) := fun q =>
    (CategoryTheory.isIso_iff_bijective _).mpr
      ((Equiv.sigmaCongrRight (fun σ : ComposableArrows I q.unop.len =>
        (SSet.yonedaEquiv (X := F.obj (σ.obj 0)) (n := q.unop)).symm)).bijective)
  letI : IsIso (simplicialReplacementDiagonalHom F) :=
    (NatTrans.isIso_iff_isIso_app _).mpr (fun _ => inferInstance)
  exact asIso (simplicialReplacementDiagonalHom F)

/-- 元の係数射の対角は、指定された同じsimplicialReplacementMapに厳密に一致する。 -/
theorem simplicialReplacementDiagonalIso_naturality {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    diagonal.map (simplicialReplacementRowsMap η) ≫ (simplicialReplacementDiagonalIso G).hom =
      (simplicialReplacementDiagonalIso F).hom ≫ simplicialReplacementMap η := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  rintro ⟨σ,x⟩
  refine Sigma.ext (show σ = σ from rfl) ?_
  apply heq_of_eq
  change (SSet.yonedaEquiv (X := G.obj (σ.obj 0)) (n := q.unop)).symm
    ((η.app (σ.obj 0)).app q x) =
      (SSet.yonedaEquiv (X := F.obj (σ.obj 0)) (n := q.unop)).symm x ≫ η.app (σ.obj 0)
  rw [SSet.yonedaEquiv_symm_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

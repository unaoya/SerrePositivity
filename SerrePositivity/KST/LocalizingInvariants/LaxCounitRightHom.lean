module

public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyRightHom
public import SerrePositivity.KST.LocalizingInvariants.LaxCounitCComparison

/-!
概要：D 余単位の元の cofiber 右辺と、その第一射影の可逆性。
方針：同じ cofiber 四角形の右辺を使い、第一射影が零始点を持つことを使う。
規約：既存の比較同型とは独立に右辺を固定する。使われ方：C 単位を保つ比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

def rightHom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 (laxCategory p q).obj) (cofiber p q) :=
  eqToHom (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (arrow_target p q).symm) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.rightHom (laxCategory p q).obj (arrow p q)

lemma rightHom_fst_isIso : IsIso (homPost (laxFst p q).hom (rightHom p q)) := by
  have h := CofiberFamily.rightHom_post_isIso_of_zeroSource
    (laxCategory p q).obj (arrow p q) (laxFst p q).hom (by
      intro x
      let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiberSquareAt (laxCategory p q).obj (arrow p q) x
      rw [show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squareAt (laxCategory p q).obj (arrow p q) x = s.square from rfl,
        s.source_vertex]
      have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.intervalFunctorVertexTypedEdge
        ((arrow p q).app (Opposite.op ⦋0⦌) x)).src_eq
      change (laxCategory p q).obj.δ 1
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((arrow p q).app (Opposite.op ⦋0⦌) x)) = _ at hs
      rw [hs]
      have hz := fst_arrow_source_zero p q x
      change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((arrow p q ≫ (ihom (Δ[1] : SSet.{u})).map
        (laxFst p q).hom) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) x) at hz
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.arrowMap_evaluation] at hz
      exact hz)
  have := h
  unfold rightHom
  rw [homPost_homComp]
  have h₀ : IsIso (homPost (laxFst p q).hom
      (eqToHom (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
        (arrow_target p q).symm))) := by
    unfold homPost
    infer_instance
  exact IsIso.comp_isIso

def rightFstIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (laxFst p q).hom
    (cofiber p q ≫ (laxFst p q).hom) := by
  let α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 (laxCategory p q).obj ≫ (laxFst p q).hom)
      (cofiber p q ≫ (laxFst p q).hom) := homPost (laxFst p q).hom (rightHom p q)
  have : IsIso α := rightHom_fst_isIso p q
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (𝟙 (laxCategory p q).obj ≫ (laxFst p q).hom)
    (cofiber p q ≫ (laxFst p q).hom)
  exact asIso α

end SerrePositivity.KST.LocalizingInvariants.LaxCounit

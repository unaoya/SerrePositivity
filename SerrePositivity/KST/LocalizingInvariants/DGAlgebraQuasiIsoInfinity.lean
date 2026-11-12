module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneralLocalization
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomology

/-!
概要：実 dg 代数の準同型を反転した ∞ 圏を、既存の辺局所化の特殊化として定める。
方針：Hom の宇宙を上げた実代数圏の nerve で、底の複体が準同型である辺を指定する。
規約：通常の QuasiIsoLocalization と D(A) の加群 ∞ 圏は変更しない。
使われ方：平方零微分摂動による Postnikov 拡大の ∞ 普遍性を述べる値域。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

abbrev InfinityPresentation := ULiftHom.{u+1} (Mon (Complex R))

def infinityPresentationFunctor : Mon (Complex R) ⥤ InfinityPresentation R := ULiftHom.up

def quasiIsoInfinityEdges : Set ((nerve (InfinityPresentation R)) _⦋1⦌) :=
  {e | QuasiIso e.hom.down.hom}

def quasiIsoInfinity : SSet.{u+1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization (nerve (InfinityPresentation R)) (quasiIsoInfinityEdges R)

def quasiIsoInfinityMap : nerve (InfinityPresentation R) ⟶ quasiIsoInfinity R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalizationMap (nerve (InfinityPresentation R)) (quasiIsoInfinityEdges R)

instance quasiIsoInfinity_quasicategory : Quasicategory (quasiIsoInfinity R) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization_quasicategory _ _

lemma quasiIsoInfinity_isLocalization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (quasiIsoInfinityMap R) (quasiIsoInfinityEdges R) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization_isLocalization _ _

lemma quasiIsoInfinityMap_inverts {A B : Mon (Complex R)} (f : A ⟶ B) (hf : QuasiIso f.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk ((infinityPresentationFunctor R).map f)).map (quasiIsoInfinityMap R)).toTruncated := by
  have he : (nerve.edgeMk ((infinityPresentationFunctor R).map f)).edge ∈ quasiIsoInfinityEdges R := hf
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization_inverts (nerve (InfinityPresentation R)) (quasiIsoInfinityEdges R)) he
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (nerve.edgeMk ((infinityPresentationFunctor R).map f)).edge).map
      ((truncation 2).map (quasiIsoInfinityMap R)))
    (f := ((nerve.edgeMk ((infinityPresentationFunctor R).map f)).map (quasiIsoInfinityMap R)).toTruncated) rfl).mp hi

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

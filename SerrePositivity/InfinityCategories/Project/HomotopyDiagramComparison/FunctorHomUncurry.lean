module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：二重の関手単体集合の二胞体を、同じ直積パラメータの二胞体へ移す。
方針：同じ標準単位の式と、直積パラメータ上の Hom 全単射を照合する。
規約：添字の quasicategory 性を仮定しない。使われ方：一般 coherent 極限の保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 内部 uncurry は頂点上で元の関手の uncurry と一致する。 -/
lemma ihomUncurry_functorVertex {K A X : SSet.{u}} (U : A ⟶ (ihom K).obj X) :
    (ihomCurryIso K A X).inv.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (uncurry U) := by rfl

/-- 元の二胞体を、直積パラメータ上の同じ端点を持つ二胞体へ移す。 -/
def functorHomUncurry {K A X : SSet.{u}} {U V : A ⟶ (ihom K).obj X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (uncurry U) (uncurry V) :=
  (hoFunctor.map (ihomCurryIso K A X).inv).toFunctor.map α

/-- uncurry による元の Hom の写像は、パラメータの充填性なしに全単射。 -/
lemma functorHomUncurry_bijective {K A X : SSet.{u}} [Quasicategory X]
    (U V : A ⟶ (ihom K).obj X) : Function.Bijective
      (functorHomUncurry : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V → _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (uncurry U) (uncurry V)) := by
  have hf := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (ihomCurryIso K A X).symm).isFullyFaithful
  exact hf.homotopyCategoryMap_bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)

/-- 二胞体の uncurry は、元の縦合成を保つ。 -/
lemma functorHomUncurry_comp {K A X : SSet.{u}} {U V W : A ⟶ (ihom K).obj X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V W) :
    functorHomUncurry (α ≫ β) = functorHomUncurry α ≫ functorHomUncurry β :=
  CategoryTheory.Functor.map_comp _ _ _

/-- 二胞体の uncurry は、元の標的関手による後合成と可換。 -/
lemma functorHomUncurry_postcomp {K A X Y : SSet.{u}} [Quasicategory X]
    {U V : A ⟶ (ihom K).obj X} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (G : X ⟶ Y) :
    functorHomUncurry (K := K) (A := A) (X := Y)
      (U := U ≫ (ihom K).map G) (V := V ≫ (ihom K).map G)
      ((hoFunctor.map ((ihom A).map ((ihom K).map G))).toFunctor.map α) =
      (hoFunctor.map ((ihom (K ⊗ A)).map G)).toFunctor.map (functorHomUncurry α) := by
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ α
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

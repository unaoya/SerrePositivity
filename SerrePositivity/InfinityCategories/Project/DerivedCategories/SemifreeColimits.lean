module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullCofiberSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeClosure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeSubcategory

/-! # Semifree 複体の標準 cofiber 押し出し

概要：Semifree 複体の span に対する標準 cofiber 四角形を部分圏内で構成する。
方針：二項直和・mapping cone の semifree 閉性と充満部分圏による押し出し性の反映を使う。
規約：非有界複体、任意の可換環。使われ方：D(S) の cofiber の存在。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- Span の標準 cofiber は semifree。 -/
lemma complexSemifree_pushoutCofiber (f : A ⟶ B) (g : A ⟶ C)
    (hA : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S A) (hB : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S B) (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S C) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g) hA
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_binaryBiproduct S hB hC)

/-- Semifree 内の標準 cofiber 四角形。 -/
def semifreeCofiberSquare (f : A ⟶ B) (g : A ⟶ C)
    (hA : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S A) (hB : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S B) (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S C) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S) f g hA hB hC
    (complexSemifree_pushoutCofiber f g hA hB hC)

/-- Semifree 内の標準 cofiber 四角形は ∞ 押し出し。 -/
lemma semifreeCofiberSquare_isPushout (f : A ⟶ B) (g : A ⟶ C)
    (hA : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S A) (hB : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S B) (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (semifreeCofiberSquare f g hA hB hC) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare_isPushout (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S) f g hA hB hC
    (complexSemifree_pushoutCofiber f g hA hB hC)

/-- Semifree 四角形の包含像は全複体の標準四角形。 -/
lemma semifreeCofiberSquare_inclusion (f : A ⟶ B) (g : A ⟶ C)
    (hA : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S A) (hB : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S B) (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S C) :
    semifreeCofiberSquare f g hA hB hC ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare_inclusion (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S) f g hA hB hC
    (complexSemifree_pushoutCofiber f g hA hB hC)

end SerrePositivity.InfinityCategories.Project.DerivedCategories

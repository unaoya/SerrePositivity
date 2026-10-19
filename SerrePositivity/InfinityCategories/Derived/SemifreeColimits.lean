module
public import SerrePositivity.InfinityCategories.Derived.FullCofiberSquare
public import SerrePositivity.InfinityCategories.Derived.SemifreeClosure
public import SerrePositivity.InfinityCategories.Derived.SemifreeSubcategory

/-! # Semifree 複体の標準 cofiber 押し出し

概要：Semifree 複体の span に対する標準 cofiber 四角形を部分圏内で構成する。
方針：二項直和・mapping cone の semifree 閉性と充満部分圏による押し出し性の反映を使う。
規約：非有界複体、任意の可換環。使われ方：D(S) の cofiber の存在。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- Span の標準 cofiber は semifree。 -/
lemma complexSemifree_pushoutCofiber (f : A ⟶ B) (g : A ⟶ C)
    (hA : complexSemifree S A) (hB : complexSemifree S B) (hC : complexSemifree S C) :
    complexSemifree S (pushoutCofiber f g) :=
  complexSemifree_mappingCone (cofiberDifference f g) hA
    (complexSemifree_binaryBiproduct S hB hC)

/-- Semifree 内の標準 cofiber 四角形。 -/
def semifreeCofiberSquare (f : A ⟶ B) (g : A ⟶ C)
    (hA : complexSemifree S A) (hB : complexSemifree S B) (hC : complexSemifree S C) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve S (Semifree S) :=
  fullCofiberSquare (complexSemifree S) f g hA hB hC
    (complexSemifree_pushoutCofiber f g hA hB hC)

/-- Semifree 内の標準 cofiber 四角形は ∞ 押し出し。 -/
lemma semifreeCofiberSquare_isPushout (f : A ⟶ B) (g : A ⟶ C)
    (hA : complexSemifree S A) (hB : complexSemifree S B) (hC : complexSemifree S C) :
    IsPushoutSquare (semifreeCofiberSquare f g hA hB hC) :=
  fullCofiberSquare_isPushout (complexSemifree S) f g hA hB hC
    (complexSemifree_pushoutCofiber f g hA hB hC)

/-- Semifree 四角形の包含像は全複体の標準四角形。 -/
lemma semifreeCofiberSquare_inclusion (f : A ⟶ B) (g : A ⟶ C)
    (hA : complexSemifree S A) (hB : complexSemifree S B) (hC : complexSemifree S C) :
    semifreeCofiberSquare f g hA hB hC ≫
      dgNerve.map (dgFullSubcategoryInclusion S (Complex S) (complexSemifree S)) =
      standardCofiberSquare f g :=
  fullCofiberSquare_inclusion (complexSemifree S) f g hA hB hC
    (complexSemifree_pushoutCofiber f g hA hB hC)

end SerrePositivity.InfinityCategories

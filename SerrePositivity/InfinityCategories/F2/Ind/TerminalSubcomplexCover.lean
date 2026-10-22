module

public import SerrePositivity.InfinityCategories.F2.Ind.TerminalSubcomplexEnlargement
public import SerrePositivity.InfinityCategories.F2.Ind.SmallSubcomplexFamilyColimit

/-!
概要：小さい終頂点付き部分複体の包含順は κ-filtered な被覆を与える。
方針：証明済みの同じ部分複体の拡大を部分族の一般的な被覆判定に適用する。
規約：実際の cofinal map は別工程。この段階では包含余錐の通常の余極限性を示す。
使われ方：cofinal な通常の poset の構成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ単体集合の終頂点付き部分複体であるという条件。 -/
def terminalSubcomplexPredicate (X : SSet.{u}) (A : X.Subcomplex) : Prop :=
  ∃ x : A.toSSet _⦋0⦌, IsTerminalVertex x

variable {κ : Cardinal.{u}} [Fact κ.IsRegular]
  {C : SSet.{u}} [Quasicategory C] [IsKappaFiltered κ C]
  {T : Type u} (hT : κ ≤ Cardinal.mk T)
include hT

/-- 同じ小さい終頂点付き部分複体の族は、包含順で通常の κ-filtered poset。 -/
lemma terminalSubcomplexFamily_isCardinalFiltered :
    IsCardinalFiltered (SmallSubcomplexFamily κ (C ⊗ nerve (Codiscrete T))
      (terminalSubcomplexPredicate _)) κ :=
  smallSubcomplexFamily_isCardinalFiltered (exists_small_terminalSubcomplex Fact.out hT)

/-- 同じ小さい終頂点付き部分複体の族は、元の積全体を被覆する。 -/
lemma iSup_terminalSubcomplexFamily :
    ⨆ A : SmallSubcomplexFamily κ (C ⊗ nerve (Codiscrete T))
      (terminalSubcomplexPredicate _), A.val = ⊤ :=
  iSup_smallSubcomplexFamily (exists_small_terminalSubcomplex Fact.out hT)

/-- 同じ部分族の元の包含余錐は、元の積を頂点とする通常の余極限。 -/
def terminalSubcomplexFamilyCocone_isColimit :
    IsColimit (smallSubcomplexFamilyCocone κ (C ⊗ nerve (Codiscrete T))
      (terminalSubcomplexPredicate _)) :=
  smallSubcomplexFamilyCocone_isColimit _ _ _ (exists_small_terminalSubcomplex Fact.out hT)

end SerrePositivity.InfinityCategories.F2.Ind

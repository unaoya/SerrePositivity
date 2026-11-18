module

public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveSieveIndex
public import SerrePositivity.InfinityCategories.Sheaves.RestrictionConeVertex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.EmptyShapeCone
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty

/-!
概要：空族の生成篩の元の指定制限錐は、同じ頂点の終対象性で判定できる。
方針：底篩の圏には対象がないことを示し、既存の空形状の全錐の判定を使う。
  文献対応：HTT 6.2.2.6 の空被覆、Kerodon §7.1（Tag 02H1）の空積。
規約：非空族の star の membership を空族で仮定しない。
使われ方：S1 の extensive 位相の有限積保存の空族の枝。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 底篩の元の持ち上げた制限形状は初期単体集合。 -/
def bottomSieveShape_isInitial (U : C) :
    IsInitial (presheafShape (sieveCategory (⊥ : Sieve U))) :=
  SSet.isInitialOfNotNonempty (by
    rintro ⟨a⟩
    let s : sieveCategory (⊥ : Sieve U) := (nerveEquiv a.down).unop
    exact s.property)

/-- 底篩の同じ制限錐の極限性は、元の F(U) の終対象性と同値。 -/
lemma restrictionCone_bot_isLimit_iff (F : Presheaf C E) (U : C) :
    IsLimitCone (restrictionCone F (⊥ : Sieve U)) ↔
      IsTerminalVertex (F.app _ (ULift.up (nerveVertex (Opposite.op U)))) := by
  simpa only [restrictionCone_vertex] using
    (isLimitCone_iff_terminal_of_initialShape (bottomSieveShape_isInitial U)
      (restrictionCone F (⊥ : Sieve U)))

/-- 空族から生成した同じ篩は底篩である。 -/
lemma cofanGeneratedSieve_eq_bot {ι : Type u} [IsEmpty ι] {B : ι → C} (c : Cofan B) :
    cofanGeneratedSieve c = ⊥ := by
  ext V f
  constructor
  · intro h
    obtain ⟨i, g, hg⟩ := (Sieve.mem_ofArrows_iff B c.inj f).mp h
    exact isEmptyElim i
  · intro h
    exact False.elim h

end SerrePositivity.InfinityCategories.Sheaves

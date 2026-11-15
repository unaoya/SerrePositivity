module

public import SerrePositivity.InfinityCategories.Sheaves.SheafCondition

/-!
概要：最大篩の射の圏は恒等射を終対象に持つ。
方針：Overの終対象への射を充満部分圏へ読み、その一意性を保つ。
使われ方：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の最大篩の層条件。
規約：制限図式はこの圏の反対を使う。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- 最大篩の恒等射として指定した対象。 -/
def topSieveIdentity (U : C) : sieveCategory (⊤ : Sieve U) :=
  ⟨Over.mk (𝟙 U), by trivial⟩

/-- 同じ指定対象への射は、元のOver圏の終対象への射そのもの。 -/
def topSieveIdentityIsTerminal (U : C) : IsTerminal (topSieveIdentity U) :=
  IsTerminal.ofUniqueHom
    (fun x => ObjectProperty.homMk (Over.mkIdTerminal.from x.obj))
    (fun x f => by
      apply ObjectProperty.hom_ext
      exact Over.mkIdTerminal.hom_ext _ _)

end SerrePositivity.InfinityCategories.Sheaves

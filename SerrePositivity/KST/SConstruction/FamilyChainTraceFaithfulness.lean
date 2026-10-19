module
public import SerrePositivity.KST.SConstruction.FamilyChainTraceSplitting
public import SerrePositivity.KST.SConstruction.FamilyChainCompositeOperations

/-! # 元の全 trace による実補正列の忠実な回収
概要：同じ両端を持つ二つの補正列は、元の全区間が一致すれば実列として一致する。
方針：各元の円柱の終面から中間族を回収し、全区間に帰納する。
規約：区間数・順序・全時刻の射が同じことを要求し、成分の一致では代用しない。
使われ方：実比較複体から取り出した辺路を元の射影補正列と照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 同じ両端の実列は元の全 trace で一意に決まる。 -/
lemma familyHomotopyChainTrace_injective {U E : SSet.{u}} {f g : U ⟶ E} :
    Function.Injective (familyHomotopyChainTrace (f := f) (g := g)) := by
  intro c d ht
  induction c with
  | nil f =>
      cases d with
      | nil => rfl
      | cons K rest => cases ht
  | @cons f h g H tail ih =>
      cases d with
      | nil => cases ht
      | @cons f h' g K rest =>
          have he : H.h = K.h := (List.cons.inj ht).1
          have hb : h = h' := by
            calc
              h = SSet.ι₁ ≫ H.h := H.h₁.symm
              _ = SSet.ι₁ ≫ K.h := congrArg (SSet.ι₁ ≫ ·) he
              _ = h' := K.h₁
          cases hb
          have hh : H = K := SSet.RelativeMorphism.Homotopy.ext he
          cases hh
          exact congrArg (FamilyHomotopyChain.cons H) (ih (List.cons.inj ht).2)

/-- 同じ全 trace で照合した実列は、元の全区間の同じ合成を表す。 -/
lemma familyChainCompositeClass_eq_of_trace {U E : SSet.{u}} {f g : U ⟶ E}
    (c d : FamilyHomotopyChain f g)
    (ht : familyHomotopyChainTrace c = familyHomotopyChainTrace d) :
    familyChainCompositeClass c = familyChainCompositeClass d :=
  congrArg familyChainCompositeClass (familyHomotopyChainTrace_injective ht)

end SerrePositivity.KST.SConstruction

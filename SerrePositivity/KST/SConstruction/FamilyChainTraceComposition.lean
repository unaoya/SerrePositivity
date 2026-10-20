module
public import SerrePositivity.KST.SConstruction.FamilyChainTraceFaithfulness

/-! # 全 trace の一致に沿った辺路の合成関係の移送
概要：実比較複体の二辺路の合成式を、同じ全 trace を持つ元の二列へ移す。
方針：非空の全 trace から両端の実等号を回収し、実列の忠実性を使う。
規約：元の全区間・順序を要求し、端点だけの一致から移送しない。
使われ方：元の次段射影と前段構造射像の全列の構造適合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 非空の同じ全区間列は、その実始点も厳密に決める。 -/
lemma familyHomotopyChainTrace_source_eq {U E : SSet.{u}} {f g f' g' : U ⟶ E}
    (c : FamilyHomotopyChain f g) (d : FamilyHomotopyChain f' g')
    (ht : familyHomotopyChainTrace c = familyHomotopyChainTrace d)
    (hne : familyHomotopyChainTrace c ≠ []) : f = f' := by
  cases c with
  | nil => exact False.elim (hne rfl)
  | cons H tail =>
      cases d with
      | nil => cases ht
      | cons K rest =>
          calc
            _ = SSet.ι₀ ≫ H.h := H.h₀.symm
            _ = SSet.ι₀ ≫ K.h := congrArg (SSet.ι₀ ≫ ·) (List.cons.inj ht).1
            _ = _ := K.h₀

/-- 実辺路の合成関係を、同じ全 trace を持つ元の二つの実列へ移す。 -/
lemma familyChainCompositeClass_transfer {U E : SSet.{u}} {a b f g : U ⟶ E}
    (c d : FamilyHomotopyChain a b) (c' d' : FamilyHomotopyChain f g)
    (hc : familyHomotopyChainTrace c = familyHomotopyChainTrace c')
    (hd : familyHomotopyChainTrace d = familyHomotopyChainTrace d')
    (hne : familyHomotopyChainTrace c ≠ [])
    (h : familyChainCompositeClass c = familyChainCompositeClass d) :
    familyChainCompositeClass c' = familyChainCompositeClass d' := by
  have ha : a = f := familyHomotopyChainTrace_source_eq c c' hc hne
  have hb : b = g := familyHomotopyChainTrace_target_eq c c' hc hne
  cases ha
  cases hb
  have hec : c = c' := familyHomotopyChainTrace_injective hc
  have hed : d = d' := familyHomotopyChainTrace_injective hd
  exact hec ▸ hed ▸ h

end SerrePositivity.KST.SConstruction

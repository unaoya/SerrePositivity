module

public import SerrePositivity.KST.DerivedGeometry.ComplexProductHomotopy

/-!
概要：ホモトピー圏の積を複体の次数ごとの積で構成する。
方針：射の代表を積に持ち上げ、成分ごとのホモトピーで一意性を証明する。
規約：積の完全性は要求しない。
使われ方：TT §3・§8、Toën §3.2、Stacks 19.13 の導来積。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} (P : ι → CochainComplex C ℤ) [HasProductsOfShape ι C]

/--
概要：複体の積のホモトピー圏での錐。
方針：積の射影をホモトピー商に送る。
規約：因子は複体のホモトピー対象。
使われ方：TT §3、Stacks 19.13 の積の構成。
-/
def homotopyProductFan : Fan (fun a => (HomotopyCategory.quotient C (.up ℤ)).obj (P a)) :=
  Fan.mk ((HomotopyCategory.quotient C (.up ℤ)).obj (complexProduct P))
    (fun a => (HomotopyCategory.quotient C (.up ℤ)).map (complexProductπ P a))

/--
概要：次数ごとの積はホモトピー圏でも積となる。
方針：射の代表の持ち上げと積へのホモトピーの組立てで普遍性を示す。
規約：有界性を要求しない。
使われ方：TT §3・§8、Toën §3.2、Stacks 19.13.4。
-/
def homotopyProductIsLimit : IsLimit (homotopyProductFan P) := by
  let Q := HomotopyCategory.quotient C (.up ℤ)
  let hL := HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor P)
  refine Fan.IsLimit.mk _ (fun s => Q.map (hL.lift
    (Fan.mk s.pt.as (fun a => (s.π.app ⟨a⟩).out)))) ?_ ?_
  · intro s a
    change Q.map _ ≫ Q.map (complexProductπ P a) = _
    rw [← Q.map_comp]
    have hf := hL.fac (Fan.mk s.pt.as (fun a => (s.π.app ⟨a⟩).out)) ⟨a⟩
    change _ ≫ complexProductπ P a = _ at hf
    rw [hf]
    exact HomotopyCategory.quotient_map_out _
  · intro s m hm
    conv_lhs => rw [← HomotopyCategory.quotient_map_out m]
    apply HomotopyCategory.eq_of_homotopy m.out
    apply homotopyIntoComplexProduct P
    intro a
    apply HomotopyCategory.homotopyOfEq
    change Q.map (m.out ≫ complexProductπ P a) = _
    rw [Q.map_comp, HomotopyCategory.quotient_map_out]
    change m ≫ (homotopyProductFan P).π.app ⟨a⟩ = _
    have hma := hm a
    change m ≫ (homotopyProductFan P).π.app ⟨a⟩ = _ at hma
    have hf := hL.fac (Fan.mk s.pt.as (fun a => (s.π.app ⟨a⟩).out)) ⟨a⟩
    change _ ≫ complexProductπ P a = _ at hf
    rw [hma, hf]
    exact (HomotopyCategory.quotient_map_out _).symm

/--
概要：基礎圏に積があれば非有界ホモトピー圏にも積がある。
方針：各ホモトピー対象の複体代表に対する積を使う。
規約：任意の小さい添字集合を許す。
使われ方：TT §3、Toën §3.2 の導来積と切断塔。
-/
instance homotopyCategory_hasProducts [HasProducts.{w} C] :
    HasProducts.{w} (HomotopyCategory C (.up ℤ)) :=
  hasProducts_of_limit_fans
    (fun P => homotopyProductFan (fun a => (P a).as))
    (fun P => homotopyProductIsLimit (fun a => (P a).as))

end SerrePositivity.KST.DerivedGeometry

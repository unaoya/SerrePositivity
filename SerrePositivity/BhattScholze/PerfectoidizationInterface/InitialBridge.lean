module

public import SerrePositivity.BhattScholze.PerfectoidizationInterface.Interface
public import SerrePositivity.InfinityCategories.Core.InitialCofinality

/-! # 指定された普遍 perfectoid 化と標的圏の始対象

概要：任意に与えた普遍単位を、同じ宇宙の標的圏の始対象として使う。
方針：環の一意因子分解を under 圏の射の一意性へ移す。
規約：普遍環の存在は仮定せず、指定された単位の普遍性だけを引数に取る。
使われ方：指定極限錐を始対象の値と比較する橋の通常圏側。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits
variable (p : ℕ) [Fact p.Prime]

/-- 指定された普遍単位を、制限した標的圏の対象として保持する。 -/
def specifiedTarget (S : CommRingCat.{u}) {C : Type u} [CommRing C]
    (η : S →+* C) (hC : IsPerfectoidization p η) : PerfUnder_u p S :=
  ⟨Under.mk (CommRingCat.ofHom η), hC.1⟩

/-- 環の普遍性から得る、指定標的から任意の perfectoid 標的への射。 -/
def specifiedTargetTo (S : CommRingCat.{u}) {C : Type u} [CommRing C]
    (η : S →+* C) (hC : IsPerfectoidization p η) (T : PerfUnder_u p S) :
    specifiedTarget p S η hC ⟶ T :=
  ObjectProperty.homMk (Under.homMk
    (CommRingCat.ofHom (hC.2 T.obj.right T.property T.obj.hom.hom).choose)
    (CommRingCat.hom_ext (hC.2 T.obj.right T.property T.obj.hom.hom).choose_spec.1))

/-- 同じ Type u の全 perfectoid 標的に対する環の普遍性は、始対象性そのもの。 -/
def specifiedTarget_isInitial (S : CommRingCat.{u}) {C : Type u} [CommRing C]
    (η : S →+* C) (hC : IsPerfectoidization p η) : IsInitial (specifiedTarget p S η hC) := by
  letI (T : PerfUnder_u p S) : Unique (specifiedTarget p S η hC ⟶ T) :=
    { default := specifiedTargetTo p S η hC T
      uniq := fun f => by
        ext1
        ext1
        apply CommRingCat.hom_ext
        apply (hC.2 T.obj.right T.property T.obj.hom.hom).choose_spec.2
        exact congrArg (fun (g : S ⟶ T.obj.right) => g.hom) (Under.w f.hom) }
  exact IsInitial.ofUnique _

end SerrePositivity.BhattScholze.PerfectoidizationInterface

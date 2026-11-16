module
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorHomTensor

/-!
概要：二つの全関手同型を、同じパラメーターを持つ直積値の全関手同型にする。
方針：既存のh Funの二胞体の直積分解と合成則で、同じ順逆の二成分を組にする。
規約：元の二つの同型を保ち、パラメーターの充填性は要求しない。
使われ方：元の全source-frameの始域・標的の二つの比較をまとめる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open CategoryTheory MonoidalClosed MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 二つの元の全関手同型の同じ順逆を、直積値の全関手同型にする。 -/
def functorIsoPair {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : T ⟶ X} {h k : T ⟶ Y} (e : FunctorIso f g) (d : FunctorIso h k) :
    FunctorIso (lift f h) (lift g k) := by
  let F := lift f h
  let G := lift g k
  let e₁ : FunctorIso (F ≫ fst X Y) (G ≫ fst X Y) := by
    simpa only [F, G, lift_fst] using e
  let e₂ : FunctorIso (F ≫ snd X Y) (G ≫ snd X Y) := by
    simpa only [F, G, lift_snd] using d
  refine { hom := (functorHomTensorEquiv F G).symm (e₁.hom, e₂.hom)
           inv := (functorHomTensorEquiv G F).symm (e₁.inv, e₂.inv)
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · apply (functorHomTensorEquiv F F).injective
    rw [functorHomTensorEquiv_comp]
    simp only [Equiv.apply_symm_apply, Iso.hom_inv_id]
    rw [functorHomTensorEquiv_apply]
    apply Prod.ext
    · exact ((hoFunctor.map ((ihom T).map (fst X Y))).toFunctor.map_id (HomotopyCategory.mk (functorVertex F))).symm
    · exact ((hoFunctor.map ((ihom T).map (snd X Y))).toFunctor.map_id (HomotopyCategory.mk (functorVertex F))).symm
  · apply (functorHomTensorEquiv G G).injective
    rw [functorHomTensorEquiv_comp]
    simp only [Equiv.apply_symm_apply, Iso.inv_hom_id]
    rw [functorHomTensorEquiv_apply]
    apply Prod.ext
    · exact ((hoFunctor.map ((ihom T).map (fst X Y))).toFunctor.map_id (HomotopyCategory.mk (functorVertex G))).symm
    · exact ((hoFunctor.map ((ihom T).map (snd X Y))).toFunctor.map_id (HomotopyCategory.mk (functorVertex G))).symm
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

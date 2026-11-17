module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorIsoPairing
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom

/-!
概要：元の全関手同型の組の二射影は、元の同型そのもの。
方針：元の直積の全単射の順逆の公式を使う。
規約：端点と元の二つの同型を保持する。
使われ方：全補正比較の元の二つの端点同型の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
/-- 元の同型の組の第一射影は、同じ第一の全関手同型になる。 -/
lemma functorIsoPair_postcomp_fst {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : T ⟶ X} {h k : T ⟶ Y} (e : FunctorIso f g) (d : FunctorIso h k) :
    (functorIsoPair e d).postcomp (fst X Y) = e := by
  apply Iso.ext
  have ht : functorHomTensorEquiv (lift f h) (lift g k)
      ((functorIsoPair e d).hom) = (e.hom, d.hom) := by
    change (functorHomTensorEquiv (lift f h) (lift g k))
      ((functorHomTensorEquiv (lift f h) (lift g k)).symm (e.hom, d.hom)) = _
    rw [Equiv.apply_symm_apply]
  have hh := congrArg Prod.fst ht
  rw [functorHomTensorEquiv_apply] at hh
  rw [functorIso_postcomp_hom]
  exact hh

/-- 元の同型の組の第二射影は、同じ第二の全関手同型になる。 -/
lemma functorIsoPair_postcomp_snd {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : T ⟶ X} {h k : T ⟶ Y} (e : FunctorIso f g) (d : FunctorIso h k) :
    (functorIsoPair e d).postcomp (snd X Y) = d := by
  apply Iso.ext
  have ht : functorHomTensorEquiv (lift f h) (lift g k)
      ((functorIsoPair e d).hom) = (e.hom, d.hom) := by
    change (functorHomTensorEquiv (lift f h) (lift g k))
      ((functorHomTensorEquiv (lift f h) (lift g k)).symm (e.hom, d.hom)) = _
    rw [Equiv.apply_symm_apply]
  have hh := congrArg Prod.snd ht
  rw [functorHomTensorEquiv_apply] at hh
  rw [functorIso_postcomp_hom]
  exact hh

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

end

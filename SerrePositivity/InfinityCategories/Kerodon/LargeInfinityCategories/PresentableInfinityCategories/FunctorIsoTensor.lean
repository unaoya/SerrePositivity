module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPair
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TensorAdjunction

/-!
概要：元の全関手同型の直積と、二つの反映の直積の余単位同型を構成する。
方針：第一・第二成分を順に変える全関手空間の組の写像で元の同型を送る。
規約：同じ元の関手と元の全同型を保持する。
使われ方：積の反映模型からの compact 生成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：第一成分を固定して第二成分の元の全関手同型を組へ送る。
方針：元の第一成分を固定した既存の組を直積の対称性で戻す。
規約：元の全関手の組を保持する。
使われ方：全関手同型の直積の第二段。 -/
def functorIsoLiftLeft {P A B : SSet.{u}} (f : P ⟶ A) {g h : P ⟶ B}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (lift f g) (lift f h) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIsoLiftRight e f).postcomp (β_ B A).hom
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (lift f g) (lift f h) at he
  exact he

/-- 概要：元の二つの全関手同型は元の直積関手の全同型を与える。
方針：元の二つの射影で前合成し、二成分を順に変える。
規約：関手同値の各点族へは弱めない。
使われ方：反映像の積の余単位の可逆性。 -/
def functorIsoTensor {X Y X' Y' : SSet.{u}} {F G : X ⟶ Y} {F' G' : X' ⟶ Y'}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F' G') : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ⊗ₘ F') (G ⊗ₘ G') := by
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIsoLiftRight (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e (fst X X')) (snd X X' ≫ F')
  have h₂ := functorIsoLiftLeft (fst X X' ≫ G) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e' (snd X X'))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ⊗ₘ F') (G ⊗ₘ F') at h₁
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ⊗ₘ F') (G ⊗ₘ G') at h₂
  exact h₁ ≪≫ h₂

/-- 概要：二つの反映の可逆な全余単位から、直積の可逆な全余単位を構成する。
方針：元の二つの同型を直積へ写し、直積関手の合成を同定する。
規約：随伴関手定理は使わない。
使われ方：直積の反映像の accessibility。 -/
def tensorReflectionCounitIso {C D C' D' : SSet.{u}}
    {L : C ⟶ D} {R : D ⟶ C} {L' : C' ⟶ D'} {R' : D' ⟶ C'}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (R ≫ L) (𝟙 D)) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (R' ≫ L') (𝟙 D')) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((R ⊗ₘ R') ≫ (L ⊗ₘ L')) (𝟙 (D ⊗ D')) := by
  rw [tensorHom_comp_tensorHom]
  simpa only [id_tensorHom_id] using functorIsoTensor e e'

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

module
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import Mathlib.Logic.Small.Basic
/-!
概要：二つの小さい dg 対象型の間の厳密 dg 関手型も同じ宇宙で小さいことを示す。
方針：対象写像と全 Hom 鎖写像の依存対へ埋め込み、圏法則の証明を無視する。
規約：元の対象宇宙は独立でよい。全加群圏を小さいとは仮定しない。
使われ方：小さい出発提示を大きい対象宇宙の小 dg 圏へ送るラベル型の評価。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (C : Type v) (D : Type w)
  [DGCategory R C] [DGCategory R D] [Small.{u} C] [Small.{u} D]

lemma dgFunctor_small : Small.{u} (DGFunctor R C D) := by
  let data := fun F : DGFunctor R C D =>
    (⟨F.obj, F.map⟩ : Σ f : C → D, ∀ x y, homObject R C x y ⟶ homObject R D (f x) (f y))
  apply small_of_injective (f := data)
  rintro ⟨fo, fm, fi, fc⟩ ⟨go, gm, gi, gc⟩ h
  have ho : fo = go := congrArg Sigma.fst h
  subst go
  have hm : fm = gm := eq_of_heq ((Sigma.mk.inj_iff.mp h).2)
  subst gm
  rfl

attribute [instance] dgFunctor_small

end SerrePositivity.DifferentialGraded

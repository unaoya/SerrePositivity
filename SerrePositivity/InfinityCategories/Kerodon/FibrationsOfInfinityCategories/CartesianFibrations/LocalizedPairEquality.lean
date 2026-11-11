module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor

/-! # anodyne 局所化で等しい射の射対への挿入

局所化の関手普遍性で等式を直積関手へ移し、
片方を固定した元の Cartesian 射対の局所化像の等号を導く。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
universe u uH vH
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open _root_.SerrePositivity.KST.Fibration

/-- anodyne を反転する任意の関手は、元の anodyne 局所化での射の等号を保存する。 -/
lemma map_eq_of_anodyneQ_eq {H : Type uH} [Category.{vH} H] (L : SSet.{u} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) {X Y : SSet.{u}} {f g : X ⟶ Y}
    (h : AnodyneHomotopy.anodyneQ.map f = AnodyneHomotopy.anodyneQ.map g) :
    L.map f = L.map g := by
  let G := Localization.lift L hL AnodyneHomotopy.anodyneQ
  let e := Localization.fac L hL AnodyneHomotopy.anodyneQ
  apply (cancel_epi (e.hom.app X)).1
  rw [← e.hom.naturality f, ← e.hom.naturality g]
  exact congrArg (· ≫ e.hom.app Y) (congrArg G.map h)

/-- 局所化射の等号は、任意の固定対象との直積で保たれる。 -/
lemma whiskerLeft_eq_of_anodyneQ_eq {X Y : SSet.{u}} {f g : X ⟶ Y}
    (h : AnodyneHomotopy.anodyneQ.map f = AnodyneHomotopy.anodyneQ.map g)
    (A : SSet.{u}) :
    AnodyneHomotopy.anodyneQ.map (A ◁ f) = AnodyneHomotopy.anodyneQ.map (A ◁ g) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.map_eq_of_anodyneQ_eq (tensorLeft A ⋙ AnodyneHomotopy.anodyneQ) _ h
  intro U V i hi
  exact Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
    (hi.whiskerLeft A)

/-- 片方を固定した元の射対は、他方の局所化射の等号を保つ。 -/
lemma pair_right_eq_of_anodyneQ_eq {X Y Z : SSet.{u}} (f : X ⟶ Y) {g h : X ⟶ Z}
    (he : AnodyneHomotopy.anodyneQ.map g = AnodyneHomotopy.anodyneQ.map h) :
    AnodyneHomotopy.anodyneQ.map (lift f g) =
      AnodyneHomotopy.anodyneQ.map (lift f h) := by
  have hg : lift f (𝟙 X) ≫ (Y ◁ g) = lift f g := by
    rw [lift_whiskerLeft, Category.id_comp]
  have hh : lift f (𝟙 X) ≫ (Y ◁ h) = lift f h := by
    rw [lift_whiskerLeft, Category.id_comp]
  rw [← hg, ← hh, Functor.map_comp, Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.whiskerLeft_eq_of_anodyneQ_eq he Y]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.map_eq_of_anodyneQ_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.map_eq_of_anodyneQ_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pair_right_eq_of_anodyneQ_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pair_right_eq_of_anodyneQ_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.whiskerLeft_eq_of_anodyneQ_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.whiskerLeft_eq_of_anodyneQ_eq

module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization

/-! # Unique discrete-valued extension through the actual Kan replacement

Uniqueness makes the extensions natural over arbitrary large base categories.
No model structure on simplicial sets is used.
-/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.DiscreteKanExtension
open PiZeroConstant
variable {A B : SSet.{w}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i) {T : Type w}

include hi in
lemma pre_injective : Function.Injective (fun g : B ⟶ discrete T => i ≫ g) := by
  intro f g h
  apply homEquiv.injective
  have hc : HomotopyClasses.mk f = HomotopyClasses.mk g :=
    (KanHomotopyClasses.pre_bijective i hi (discrete_terminal_rlp T)).injective
      (congrArg HomotopyClasses.mk h)
  exact congrArg PiZeroLocalization.classEquiv hc

def extension (f : A ⟶ discrete T) : B ⟶ discrete T :=
  (KanHomotopyExtension.exists_extension i hi (discrete_terminal_rlp T) f).choose

lemma extension_fac (f : A ⟶ discrete T) : i ≫ extension i hi f = f :=
  (KanHomotopyExtension.exists_extension i hi (discrete_terminal_rlp T) f).choose_spec

lemma extension_unique (f : A ⟶ discrete T) (g : B ⟶ discrete T) (hg : i ≫ g = f) :
    g = extension i hi f := pre_injective i hi (hg.trans (extension_fac i hi f).symm)

variable {D : Type uD} [Category.{vD} D] {F : D ⥤ SSet.{w}} {T : D ⥤ Type w}
  (a : F ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ)

def naturalExtension : F ⋙ AnodyneKanReplacement.functor ⟶
    T ⋙ Functor.const SimplexCategoryᵒᵖ where
  app d := extension (AnodyneKanReplacement.unit.app (F.obj d))
    (AnodyneKanReplacement.unit_anodyne (F.obj d)) (a.app d)
  naturality {d e} f := by
    apply pre_injective (AnodyneKanReplacement.unit.app (F.obj d))
      (AnodyneKanReplacement.unit_anodyne (F.obj d))
    change AnodyneKanReplacement.unit.app (F.obj d) ≫
        (AnodyneKanReplacement.functor.map (F.map f) ≫ _) =
      AnodyneKanReplacement.unit.app (F.obj d) ≫ (_ ≫ _)
    rw [← Category.assoc, ← AnodyneKanReplacement.unit.naturality,
      Category.assoc, extension_fac, ← Category.assoc, extension_fac]
    exact a.naturality f

lemma naturalExtension_fac : Functor.whiskerLeft F AnodyneKanReplacement.unit ≫
    naturalExtension a = a := by
  apply NatTrans.ext
  funext d
  exact extension_fac _ (AnodyneKanReplacement.unit_anodyne (F.obj d)) (a.app d)

lemma naturalExtension_unique
    (b : F ⋙ AnodyneKanReplacement.functor ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ)
    (hb : Functor.whiskerLeft F AnodyneKanReplacement.unit ≫ b = a) :
    b = naturalExtension a := by
  apply NatTrans.ext
  funext d
  exact extension_unique _ (AnodyneKanReplacement.unit_anodyne (F.obj d))
    (a.app d) (b.app d) (congr_app hb d)

end SerrePositivity.SimplicialModel.DiscreteKanExtension

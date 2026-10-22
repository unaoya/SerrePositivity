module

public import SerrePositivity.KST.LocalizingInvariants.ProFullyFaithfulReflection
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
概要：加法群への忘却後の pro 同型から、元の加群の実線形 pro 逆を構成する。
方針：二段目の pro 逆で遷移を元の線形射の像へ入れ、スカラー整合性を回収する。
規約：逆射の線形性を追加入力しない。使われ方：π₀ の群比較を零切断の比較へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable (R : Type u) [Ring R] {X Y : Tower (ModuleCat.{u} R)} (f : LevelHom X Y)

lemma proIso_of_module_forget
    (hf : IsProIso (f.map (forget₂ (ModuleCat R) AddCommGrpCat))) : IsProIso f := by
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat
  let f' := f.map F
  intro n
  obtain ⟨m, hn, g, hg, gh⟩ := hf n
  obtain ⟨k, hm, h, hh, hh'⟩ := hf m
  let g₀ : (Y.obj m) →+ (X.obj n) := g.hom
  let h₀ : (Y.obj k) →+ (X.obj m) := h.hom
  let a : (Y.obj k) →+ (X.obj n) :=
    g₀.comp ((Y.transition hm).hom.toAddMonoidHom)
  have hfactor (y : Y.obj k) : (Y.transition hm).hom y = (f.app m).hom (h₀ y) :=
    (congrArg (fun q => q.hom y) hh').symm
  have hcomp (x : X.obj m) : g₀ ((f.app m).hom x) = (X.transition hn).hom x :=
    congrArg (fun q => q.hom x) hg
  have ha (y : Y.obj k) : a y = (X.transition hn).hom (h₀ y) := by
    change g₀ ((Y.transition hm).hom y) = _
    rw [hfactor]
    exact hcomp _
  let b : Y.obj k ⟶ X.obj n := ModuleCat.ofHom
    { toFun := a
      map_add' := a.map_add
      map_smul' := by
        intro r y
        change g₀ ((Y.transition hm).hom (r • y)) = r • a y
        calc
          _ = g₀ (r • (Y.transition hm).hom y) := by rw [(Y.transition hm).hom.map_smul]
          _ = g₀ ((f.app m).hom (r • h₀ y)) := by rw [hfactor, (f.app m).hom.map_smul]
          _ = (X.transition hn).hom (r • h₀ y) := hcomp _
          _ = r • (X.transition hn).hom (h₀ y) := map_smul _ _ _
          _ = r • a y := congrArg (fun z => r • z) (ha y).symm }
  have hb : F.map b = (Y.map F).transition hm ≫ g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro y
    rfl
  refine ⟨k, hn.trans hm, b, ?_, ?_⟩
  · apply F.map_injective
    rw [F.map_comp, hb]
    change f'.app k ≫ ((Y.map F).transition hm ≫ g) =
      (X.map F).transition (hn.trans hm)
    rw [← Category.assoc, ← f'.naturality hm, Category.assoc, hg,
      (X.map F).transition_comp]
  · apply F.map_injective
    rw [F.map_comp, hb]
    change ((Y.map F).transition hm ≫ g) ≫ f'.app n =
      (Y.map F).transition (hn.trans hm)
    rw [Category.assoc, gh, (Y.map F).transition_comp]

lemma proIso_of_module_groups
    (hf : IsProIso (f.map (forget₂ (ModuleCat R) AddCommGrpCat ⋙ AddCommGrpCat.toCommGrp))) :
    IsProIso f := by
  have : AddCommGrpCat.toCommGrp.IsEquivalence :=
    commGroupAddCommGroupEquivalence.symm.isEquivalence_functor
  apply proIso_of_module_forget R f
  exact proIso_of_fullyFaithful AddCommGrpCat.toCommGrp
    (f.map (forget₂ (ModuleCat R) AddCommGrpCat)) hf

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram

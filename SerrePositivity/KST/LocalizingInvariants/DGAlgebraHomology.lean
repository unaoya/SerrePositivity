module

public import SerrePositivity.DifferentialGraded.Complexes.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
概要：実際の非可換 dg 代数の整数次数群 H⁻ʲ と、射の連結度条件を構成する。
方針：複体のモノイド対象の忘却関手と実ホモロジー関手を合成する。
規約：積の可換性は要求しない。使われ方：dg 増強流の k-connective 条件と Tor 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R]

def complexGroups (j : ℤ) : Complex R ⥤ CommGrpCat.{u} :=
  homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (-j) ⋙
    forget₂ (ModuleCat R) AddCommGrpCat ⋙ AddCommGrpCat.toCommGrp

def groups (j : ℤ) : Mon (Complex R) ⥤ CommGrpCat.{u} :=
  Mon.forget (Complex R) ⋙ complexGroups R j

def IsConnective (B : Mon (Complex R)) : Prop := B.X.IsLE 0

def IsConnected {B C : Mon (Complex R)} (f : B ⟶ C) (n : ℤ) : Prop :=
  (∀ j : ℤ, j < n → Function.Injective ((groups R j).map f).hom) ∧
    ∀ j : ℤ, j ≤ n → Function.Surjective ((groups R j).map f).hom

lemma groups_map_bijective_iff {B C : Mon (Complex R)} (f : B ⟶ C) (j : ℤ) :
    Function.Bijective ((groups R j).map f).hom ↔ QuasiIsoAt f.hom (-j) := by
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  rfl

lemma groups_map_isIso_of_quasiIso {B C : Mon (Complex R)} (f : B ⟶ C)
    (hf : QuasiIso f.hom) (j : ℤ) : IsIso ((groups R j).map f) := by
  haveI : QuasiIso f.hom := hf
  change IsIso (AddCommGrpCat.toCommGrp.map
    ((forget₂ (ModuleCat R) AddCommGrpCat).map (homologyMap f.hom (-j))))
  infer_instance

lemma connected_of_quasiIso {B C : Mon (Complex R)} (f : B ⟶ C)
    (hf : QuasiIso f.hom) (n : ℤ) : IsConnected R f n := by
  have hb (j : ℤ) : Function.Bijective ((groups R j).map f).hom := by
    haveI := groups_map_isIso_of_quasiIso R f hf j
    exact ConcreteCategory.bijective_of_isIso ((groups R j).map f)
  exact ⟨fun j _ ↦ (hb j).1, fun j _ ↦ (hb j).2⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

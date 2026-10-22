module

public import SerrePositivity.KST.LocalizingInvariants.ZeroComplexHomology
public import SerrePositivity.KST.LocalizingInvariants.ProModuleReflection

/-!
概要：零集中複体の元の H⁰ 群の pro 同型から、元の複体の実 pro 逆を構成する。
方針：群の逆を線形に補正し、零集中複体上の元の H⁰ 関手の充満忠実性で戻す。
規約：元の添字とレベル射を保持。使われ方：零 Postnikov 代数の pro 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable (R : Type u) [CommRing R] {X Y : Tower (Complex R)} (f : LevelHom X Y)
  (hX : ∀ i, (zeroComplexProperty R) (X.obj i))
  (hY : ∀ i, (zeroComplexProperty R) (Y.obj i))

include hX hY in
lemma proIso_of_zeroComplex_homology
    (hf : IsProIso (f.map (homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0))) :
    IsProIso f := by
  intro n
  obtain ⟨m, hn, g, hg, gh⟩ := hf n
  let E := zeroComplexHomology R
  let b : (⟨Y.obj m, hY m⟩ : ZeroComplex R) ⟶ ⟨X.obj n, hX n⟩ := E.preimage g
  refine ⟨m, hn, b.hom, ?_, ?_⟩
  · have he : (ObjectProperty.homMk (f.app m) :
        (⟨X.obj m, hX m⟩ : ZeroComplex R) ⟶ ⟨Y.obj m, hY m⟩) ≫ b =
        ObjectProperty.homMk (X.transition hn) := by
      apply E.map_injective
      rw [E.map_comp, E.map_preimage]
      exact hg
    exact congrArg (fun z => z.hom) he
  · have he : b ≫ (ObjectProperty.homMk (f.app n) :
        (⟨X.obj n, hX n⟩ : ZeroComplex R) ⟶ ⟨Y.obj n, hY n⟩) =
        ObjectProperty.homMk (Y.transition hn) := by
      apply E.map_injective
      rw [E.map_comp, E.map_preimage]
      exact gh
    exact congrArg (fun z => z.hom) he

include hX hY in
lemma proIso_of_zeroComplex_groups (hf : IsProIso (f.map (DGAlgebra.complexGroups R 0))) :
    IsProIso f := by
  apply proIso_of_zeroComplex_homology R f hX hY
  exact proIso_of_module_groups R
    (f.map (homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0)) hf

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram

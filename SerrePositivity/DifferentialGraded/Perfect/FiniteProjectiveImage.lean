module
public import SerrePositivity.DifferentialGraded.Perfect.Triangulated
public import SerrePositivity.PerfectComplex.KoszulLength
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # 有限射影加群の像のperfect性

既存の有限自由加群へのretractを再利用する。有限和は主Perfの充満部分圏で取り、
その包含によるbiproduct比較で主導来圏へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定生成集合の主Perfは有限biproductで閉じる。 -/
lemma modulePerfectOver_biproduct (S : Set D) {J : Type} [Finite J]
    (X : J → DerivedModuleCategory A D) (hX : ∀ j, modulePerfectOver A D S (X j)) :
    modulePerfectOver A D S (⨁ X) := by
  let Y : J → PerfectModuleCategoryOver A D S := fun j => ⟨X j, hX j⟩
  let e : (perfectModuleInclusion A D S).obj (⨁ Y) ≅ ⨁ X :=
    (perfectModuleInclusion A D S).mapBiproduct Y
  exact (modulePerfectOver A D S).prop_of_iso e (⨁ Y).property

/-- 加法的関手がAをperfect対象へ送れば、任意の有限射影A加群もperfect対象へ送る。 -/
lemma modulePerfectOver_image_finiteProjective (S : Set D)
    (F : ModuleCat.{u} A ⥤ DerivedModuleCategory A D) [F.Additive]
    (hA : modulePerfectOver A D S (F.obj (ModuleCat.of A A)))
    (M : ModuleCat.{u} A) [Module.Finite A M] [Module.Projective A M] :
    modulePerfectOver A D S (F.obj M) := by
  obtain ⟨n, ⟨r⟩⟩ := SerrePositivity.finiteProjective_exists_retract M
  let X : Fin n → ModuleCat.{u} A := fun _ => ModuleCat.of A A
  let e : F.obj (ModuleCat.of A (Fin n → A)) ≅ ⨁ (fun j => F.obj (X j)) :=
    F.mapIso (ModuleCat.biproductIsoPi X).symm ≪≫ F.mapBiproduct X
  have hfree := (modulePerfectOver A D S).prop_of_iso e.symm
    (modulePerfectOver_biproduct A D S (fun j => F.obj (X j)) (fun _ => hA))
  exact modulePerfectOver_of_retract A D (r.map F) hfree

end SerrePositivity.DifferentialGraded

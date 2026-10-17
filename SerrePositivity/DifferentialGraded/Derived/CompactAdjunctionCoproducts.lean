module
public import SerrePositivity.DifferentialGraded.Endomorphism.CompactHomDetectsIso
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseTelescope
public import SerrePositivity.DifferentialGraded.Derived.CoproductProjection
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # dg加群導来圏のcompact保存左随伴に対する右随伴の余積保存

## 概要
dg加群導来圏のcompact保存左随伴に対する右随伴の余積保存。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  (R : DerivedModuleCategory A E ⥤ DerivedModuleCategory A D) [L.Additive] [R.Additive]
  (adj : L ⊣ R)
variable {J : Type u} (G : J → DerivedModuleCategory A E)

lemma derivedAdjunction_sigmaComparison_projection (i : J) :
    sigmaComparison R G ≫ R.map (moduleDerivedCoproductProjection A E G i) =
      moduleDerivedCoproductProjection A D (fun j => R.obj (G j)) i := by
  apply Sigma.hom_ext
  intro j
  rw [ι_comp_sigmaComparison_assoc, ← CategoryTheory.Functor.map_comp]
  by_cases hji : j = i
  · subst j
    rw [moduleDerivedCoproductProjection_self, CategoryTheory.Functor.map_id,
      moduleDerivedCoproductProjection_self]
  · rw [moduleDerivedCoproductProjection_ne A E G j i hji, Functor.map_zero,
      moduleDerivedCoproductProjection_ne A D _ j i hji]

lemma derivedAdjunction_sigmaHom_injective (P : DerivedModuleCategory A D)
    (hP : moduleCompact A D P) :
    Function.Injective (fun f : P ⟶ ∐ fun j => R.obj (G j) => f ≫ sigmaComparison R G) := by
  intro f g hfg
  change f ≫ sigmaComparison R G = g ≫ sigmaComparison R G at hfg
  apply sub_eq_zero.mp
  apply moduleCompact_hom_ext_zero A D hP _ (f - g)
  intro i
  rw [← derivedAdjunction_sigmaComparison_projection A D E R G i,
    sub_comp, ← Category.assoc, ← Category.assoc, hfg, sub_self]

include adj

omit [R.Additive] in
lemma derivedAdjunction_sigmaHom_surjective (P : DerivedModuleCategory A D)
    (hLP : moduleCompact A E (L.obj P)) :
    Function.Surjective (fun f : P ⟶ ∐ fun j => R.obj (G j) => f ≫ sigmaComparison R G) := by
  classical
  intro f
  obtain ⟨t, g, hg⟩ := hLP J G ((adj.homEquiv P (∐ G)).symm f)
  refine ⟨∑ j ∈ t, adj.homEquiv P (G j) (g j) ≫
    Sigma.ι (fun j => R.obj (G j)) j, ?_⟩
  dsimp only
  rw [sum_comp]
  have he := congrArg (adj.homAddEquiv P (∐ G)) hg
  have hx : (adj.homAddEquiv P (∐ G)) ((adj.homEquiv P (∐ G)).symm f) = f :=
    (adj.homEquiv P (∐ G)).apply_symm_apply f
  rw [hx] at he
  simp only [map_sum] at he
  calc
    _ = ∑ j ∈ t, adj.homEquiv P (∐ G) (g j ≫ Sigma.ι G j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Category.assoc, ι_comp_sigmaComparison]
      exact (adj.homEquiv_naturality_right (g j) (Sigma.ι G j)).symm
    _ = f := he

lemma derivedAdjunction_sigmaComparison_isIso
    (hcompact : ∀ P : DerivedModuleCategory A D, moduleCompact A D P →
      moduleCompact A E (L.obj P)) : IsIso (sigmaComparison R G) := by
  apply moduleDerived_isIso_of_compact_hom_bijective A D
  intro P hP
  exact ⟨derivedAdjunction_sigmaHom_injective A D E R G P hP,
    derivedAdjunction_sigmaHom_surjective A D E L R adj G P (hcompact P hP)⟩

lemma derivedAdjunction_rightAdjoint_preservesCoproduct
    (hcompact : ∀ P : DerivedModuleCategory A D, moduleCompact A D P →
      moduleCompact A E (L.obj P)) : PreservesColimit (Discrete.functor G) R := by
  let := derivedAdjunction_sigmaComparison_isIso A D E L R adj G hcompact
  exact PreservesCoproduct.of_iso_comparison _ G

end SerrePositivity.DifferentialGraded

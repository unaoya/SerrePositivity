module
public import SerrePositivity.DifferentialGraded.Morita.CriterionDerivedCoproducts
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseTelescope

/-! # compact始域に対するHom比較の余積閉性

各生成元のcompact性だけを使い、生成族全体の直和をcompactとは仮定しない。
一般の導来右随伴は使わない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E) [T.Additive]
  {J : Type u} (F : J → DerivedModuleCategory A D) (X : DerivedModuleCategory A D)

/-- compactな始域からのHom比較の単射性は、終域のu-small余積で保たれる。 -/
lemma criterionDerivedHom_coproduct_injective (hX : moduleCompact A D X)
    (hF : ∀ j, Function.Injective (fun f : X ⟶ F j => T.map f)) :
    Function.Injective (fun f : X ⟶ ∐ F => T.map f) := by
  intro f g hfg
  change T.map f = T.map g at hfg
  apply sub_eq_zero.mp
  apply moduleCompact_hom_ext_zero A D hX F (f - g)
  intro j
  apply hF j
  change T.map ((f - g) ≫ moduleDerivedCoproductProjection A D F j) = T.map 0
  rw [CategoryTheory.Functor.map_comp, Functor.map_sub, hfg, sub_self,
    zero_comp, Functor.map_zero]

/-- compactな像と余積保存から、終域の余積へのHom比較の全射性を得る。 -/
lemma criterionDerivedHom_coproduct_surjective
    [PreservesColimit (Discrete.functor F) T]
    (hTX : moduleCompact A E (T.obj X))
    (hF : ∀ j, Function.Surjective (fun f : X ⟶ F j => T.map f)) :
    Function.Surjective (fun f : X ⟶ ∐ F => T.map f) := by
  classical
  intro f
  let e := PreservesCoproduct.iso T F
  obtain ⟨s, g, hg⟩ := hTX J (fun j => T.obj (F j)) (f ≫ e.hom)
  let a (j : J) : X ⟶ F j := (hF j (g j)).choose
  have ha (j : J) : T.map (a j) = g j := (hF j (g j)).choose_spec
  refine ⟨∑ j ∈ s, a j ≫ Sigma.ι F j, ?_⟩
  calc
    _ = ∑ j ∈ s, g j ≫ T.map (Sigma.ι F j) := by
      simp only [Functor.map_sum, CategoryTheory.Functor.map_comp, ha]
    _ = (∑ j ∈ s, g j ≫ Sigma.ι (fun j => T.obj (F j)) j) ≫
        sigmaComparison T F := by
      simp only [sum_comp, Category.assoc, ι_comp_sigmaComparison]
    _ = (f ≫ e.hom) ≫ e.inv := congrArg (fun k => k ≫ e.inv) hg
    _ = f := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- 各compact生成元について使う、Hom比較の全単射性の余積閉性。 -/
lemma criterionDerivedHom_coproduct_bijective
    [PreservesColimit (Discrete.functor F) T]
    (hX : moduleCompact A D X) (hTX : moduleCompact A E (T.obj X))
    (hF : ∀ j, Function.Bijective (fun f : X ⟶ F j => T.map f)) :
    Function.Bijective (fun f : X ⟶ ∐ F => T.map f) :=
  ⟨criterionDerivedHom_coproduct_injective A D E T F X hX (fun j => (hF j).1),
    criterionDerivedHom_coproduct_surjective A D E T F X hTX (fun j => (hF j).2)⟩

omit [T.Additive]

/-- 始域の余積については、各因子でのHom比較の単射性だけを使う。 -/
lemma criterionDerivedHom_sourceCoproduct_injective (Y : DerivedModuleCategory A D)
    (hF : ∀ j, Function.Injective (fun f : F j ⟶ Y => T.map f)) :
    Function.Injective (fun f : ∐ F ⟶ Y => T.map f) := by
  intro f g hfg
  change T.map f = T.map g at hfg
  apply Sigma.hom_ext
  intro j
  apply hF j
  change T.map (Sigma.ι F j ≫ f) = T.map (Sigma.ι F j ≫ g)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hfg]

/-- 始域の余積での全射性は、余積保存と各因子の全射性から得る。compact性は不要。 -/
lemma criterionDerivedHom_sourceCoproduct_surjective (Y : DerivedModuleCategory A D)
    [PreservesColimit (Discrete.functor F) T]
    (hF : ∀ j, Function.Surjective (fun f : F j ⟶ Y => T.map f)) :
    Function.Surjective (fun f : ∐ F ⟶ Y => T.map f) := by
  classical
  intro f
  let a (j : J) : F j ⟶ Y := (hF j (T.map (Sigma.ι F j) ≫ f)).choose
  have ha (j : J) : T.map (a j) = T.map (Sigma.ι F j) ≫ f :=
    (hF j (T.map (Sigma.ι F j) ≫ f)).choose_spec
  refine ⟨Sigma.desc a, ?_⟩
  apply (cancel_epi (sigmaComparison T F)).1
  apply Sigma.hom_ext
  intro j
  rw [ι_comp_sigmaComparison_assoc, ι_comp_sigmaComparison_assoc,
    ← CategoryTheory.Functor.map_comp, Sigma.ι_comp_desc, ha]

/-- 始域の余積でのHom比較の全単射性。生成族の直和のcompact性は要求しない。 -/
lemma criterionDerivedHom_sourceCoproduct_bijective (Y : DerivedModuleCategory A D)
    [PreservesColimit (Discrete.functor F) T]
    (hF : ∀ j, Function.Bijective (fun f : F j ⟶ Y => T.map f)) :
    Function.Bijective (fun f : ∐ F ⟶ Y => T.map f) :=
  ⟨criterionDerivedHom_sourceCoproduct_injective A D E T F Y (fun j => (hF j).1),
    criterionDerivedHom_sourceCoproduct_surjective A D E T F Y (fun j => (hF j).2)⟩

end SerrePositivity.DifferentialGraded.Morita

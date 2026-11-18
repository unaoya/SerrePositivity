module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.TensorComponents

/-!
# 三重テンソルの結合子と次数射影

概要：AW の余結合性を成分から鎖写像へ移すための結合子の公式を証明する。
方針：三つの次数の直和への包含で検査する。
規約：自然数鎖複体と既存のモノイダル結合子を使う。
使われ方：Berger–Fresse §1.1.4 の余結合的 AW 対角。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

private lemma leftInclusion_reindex (K L M : ChainComplex (ModuleCat.{u} A) ℕ)
    (a b c s n : ℕ) (hs : a + b = s) (hn : s + c = n) :
    (ιTensorObj K L a b (a + b) rfl ▷ M.X c) ≫
        ιTensorObj (HomologicalComplex.tensorObj K L) M (a + b) c n (by omega) =
      (ιTensorObj K L a b s hs ▷ M.X c) ≫
        ιTensorObj (HomologicalComplex.tensorObj K L) M s c n hn := by
  subst s
  rfl

private lemma rightInclusion_reindex (K L M : ChainComplex (ModuleCat.{u} A) ℕ)
    (a b c s n : ℕ) (hs : b + c = s) (hn : a + s = n) :
    (K.X a ◁ ιTensorObj L M b c (b + c) rfl) ≫
        ιTensorObj K (HomologicalComplex.tensorObj L M) a (b + c) n (by omega) =
      (K.X a ◁ ιTensorObj L M b c s hs) ≫
        ιTensorObj K (HomologicalComplex.tensorObj L M) a s n hn := by
  subst s
  rfl

/-- 概要：結合子は三つの次数への射影と可換（Berger–Fresse §1.1.4 の成分比較）。
方針：三重直和への包含で検査し、一致する三次数だけを残す。
規約：鎖複体と加群の標準の結合子を用いる。
使われ方：成分の余結合性を鎖写像の余結合性へ移す。 -/
lemma tensorAssociator_projection (K L M : ChainComplex (ModuleCat.{u} A) ℕ)
    (p q r : ℕ) :
    (HomologicalComplex.associator K L M).hom.f (p + q + r) ≫
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K (HomologicalComplex.tensorObj L M)
          (p + q + r) p (q + r) (by omega) ≫
        (K.X p ◁ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection L M (q + r) q r rfl) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection (HomologicalComplex.tensorObj K L) M
          (p + q + r) (p + q) r rfl ≫
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L (p + q) p q rfl ▷ M.X r) ≫
        (α_ (K.X p) (L.X q) (M.X r)).hom := by
  apply mapBifunctor₁₂.hom_ext
  intro a b c habc
  change a + b + c = p + q + r at habc
  change mapBifunctor₁₂.ι _ _ K L M (.down ℕ) (.down ℕ) a b c _ habc ≫
    (mapBifunctorAssociatorX (curriedAssociatorNatIso (ModuleCat A)) K L M
      (.down ℕ) (.down ℕ) (.down ℕ) _).hom ≫ _ = _
  rw [ι_mapBifunctorAssociatorX_hom_assoc]
  rw [mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ _ _ _ _ _ rfl habc]
  rw [mapBifunctor₂₃.ι_eq _ _ _ _ _ _ _ _ _ _ _ _ _ rfl (by dsimp at habc ⊢; omega)]
  change (α_ (K.X a) (L.X b) (M.X c)).hom ≫
      (K.X a ◁ ιTensorObj L M b c (b + c) rfl) ≫
      ιTensorObj K (HomologicalComplex.tensorObj L M) a (b + c) _ (by omega) ≫
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K (HomologicalComplex.tensorObj L M) _ p (q + r) (by omega) ≫
      (K.X p ◁ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection L M (q + r) q r rfl) =
    (ιTensorObj K L a b (a + b) rfl ▷ M.X c) ≫
      ιTensorObj (HomologicalComplex.tensorObj K L) M (a + b) c _ habc ≫
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection (HomologicalComplex.tensorObj K L) M _ (p + q) r rfl ≫
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L (p + q) p q rfl ▷ M.X r) ≫
      (α_ (K.X p) (L.X q) (M.X r)).hom
  by_cases hc : c = r
  · subst c
    have hab : a + b = p + q := by omega
    rw [← Category.assoc (ιTensorObj K L a b (a + b) rfl ▷ M.X r),
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.leftInclusion_reindex K L M a b r (p + q) _ hab rfl]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_assoc (HomologicalComplex.tensorObj K L) M]
    by_cases ha : a = p
    · subst a
      have hb : b = q := by omega
      subst b
      rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_assoc K (HomologicalComplex.tensorObj L M)]
      simp only [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.comp_whiskerRight_assoc,
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection, MonoidalCategory.whiskerLeft_id,
        MonoidalCategory.id_whiskerRight, Category.id_comp, Category.comp_id]
    · rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne_assoc _ _ _ _ _ _ _ _ _ (by
        intro e
        exact ha (congrArg Prod.fst e))]
      rw [← MonoidalCategory.comp_whiskerRight_assoc,
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne _ _ _ _ _ _ _ _ _ (by
          intro e
          exact ha (congrArg Prod.fst e))]
      simp
  · rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne_assoc (HomologicalComplex.tensorObj K L) M
      _ _ _ _ _ _ _ (by
        intro e
        exact hc (congrArg Prod.snd e))]
    by_cases ha : a = p
    · subst a
      have hbc : b + c = q + r := by omega
      rw [← Category.assoc (K.X p ◁ ιTensorObj L M b c (b + c) rfl),
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.rightInclusion_reindex K L M p b c (q + r) _ hbc (by omega)]
      simp only [Category.assoc]
      rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_assoc K (HomologicalComplex.tensorObj L M)]
      rw [← MonoidalCategory.whiskerLeft_comp,
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne _ _ _ _ _ _ _ _ _ (by
          intro e
          exact hc (congrArg Prod.snd e))]
      simp
    · rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne_assoc _ _ _ _ _ _ _ _ _ (by
        intro e
        exact ha (congrArg Prod.fst e))]
      simp

end SerrePositivity.SimplicialChains.AlexanderWhitney

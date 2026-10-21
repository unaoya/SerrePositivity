module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedCompositionCore
/-!
概要：元の指定合成子から、入力切断前の三項経路を取り出す。
方針：型輸送を一段ずつ除き、同じ全関手同型の前合成を比較する。
規約：元の指定合成子の定義を変更しない。使われ方：raw factor 計算への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
private lemma mp_heq_iff {α β γ : Sort u} (h : α = β) (a : α) (c : γ) :
    HEq (Eq.mp h a) c ↔ HEq a c := by
  cases h
  rfl
private lemma mpr_heq_iff {α β γ : Sort u} (h : α = β) (b : β) (c : γ) :
    HEq (Eq.mpr h b) c ↔ HEq b c := by
  cases h
  rfl
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E K : Type v) [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
  (F : DGFunctor R C (RightModule R E))
  (H : DGFunctor R (RightModule R E) (RightModule R K))
/-- 元の指定合成子は、同じ入力切断による指定三項経路の前合成である。 -/
lemma dgModuleResolvedInfinity_compositionIso_core_heq
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    HEq (dgModuleResolvedInfinity_compositionIso R C E K F H hq)
      ((dgModuleResolvedCompositionCoreIso R C E K F H hq).precomp
        (dgModuleResolvedSourceSectionEquivalence R C E F).hom) := by
  dsimp -zeta only [dgModuleResolvedInfinity_compositionIso]
  extract_lets T I P G S hs hc0 hc1 e a hsp q
  have ha : HEq a (dgModuleResolvedCompositionCoreIso R C E K F H hq) := by
    apply heq_of_eq
    dsimp only [a, dgModuleResolvedCompositionCoreIso]
  have hp := F2.functorIso_precomp_heq_of_heq
    (dgModuleResolvedCompositionCoreIso R C E K F H hq) a rfl rfl ha S
  rw [mpr_heq_iff, mpr_heq_iff, mp_heq_iff]
  exact hp
end SerrePositivity.InfinityCategories

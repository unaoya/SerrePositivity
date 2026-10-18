module

public import SerrePositivity.KST.ProExcision.FlatBaseChange

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 完全列における pro-零性

概要：複体のホモロジーの pro-零性と完全列による有限拡張を扱う。
方針：ホモロジーはサイクルの部分商であり、零射を保つことを使う。
規約：完全性は実際の射に対して指定する。
使われ方：KST Lemma 4.10 の頁比較。局所係数つき Claim 4.18 の構成は別工程。
-/

universe u v w w'

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-- 概要：関手間の自然変換は像の塔のレベル射を与える。
方針：各段で自然変換を評価する。規約：自然性をそのまま使用。
使われ方：スペクトル系列の次頁とホモロジーの比較。 -/
def Tower.mapNatTrans {C : Type u} [Category.{v} C] {D : Type w} [Category.{w'} D]
    (X : Tower C) {F G : C ⥤ D} (τ : F ⟶ G) : LevelHom (X.map F) (X.map G) where
  app n := τ.app (X.obj n)
  naturality h := τ.naturality (X.transition h)

variable {R : Type u} [CommRing R]

/-- 概要：当該項で零となる複体射はその次数のホモロジー上でも零。
方針：サイクルへの制限とホモロジーへの全射を使う。
規約：隣接する項での零性は不要。使われ方：KST Lemma 4.10 の頁の pro-零性保存。 -/
theorem homologyMap_zero_of_component_zero {I : Type w} {c : ComplexShape I}
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L) (i : I)
    (hf : f.f i = 0) : homologyMap f i = 0 := by
  have hc : cyclesMap f i = 0 := by
    rw [← cancel_mono (L.iCycles i), cyclesMap_i, hf, comp_zero, zero_comp]
  rw [← cancel_epi (K.homologyπ i), comp_zero, homologyπ_naturality, hc, zero_comp]

/-- 概要：複体の塔の一つの項が pro-零なら、その次数のホモロジーも pro-零。
方針：零になる成分から零になるホモロジー遷移を得る。
規約：全次数一様の消滅は要求しない。使われ方：KST Lemma 4.10 の頁移行。 -/
theorem homology_proZero_of_component {I : Type w} {c : ComplexShape I}
    (X : Tower (HomologicalComplex (ModuleCat.{u} R) c)) (i : I)
    (hX : IsProZero (X.map (eval _ _ i))) :
    IsProZero (X.map (homologyFunctor _ _ i)) := by
  intro n
  obtain ⟨m, h, hz⟩ := hX n
  exact ⟨m, h, homologyMap_zero_of_component_zero (X.transition h) i hz⟩

/-- 概要：完全列の両端が pro-零なら中央も pro-零。
方針：右の遷移を零化して左から持ち上げ、左の遷移を零化する。
規約：各レベルでの短完全性ではなく中央での完全性だけが必要。
使われ方：KST Lemma 4.10 の収束濾過の有限拡張。 -/
theorem proZero_of_exact {A B C : Tower (ModuleCat.{u} R)}
    (f : LevelHom A B) (g : LevelHom B C)
    (hex : ∀ n, Function.Exact (f.app n).hom (g.app n).hom)
    (hA : IsProZero A) (hC : IsProZero C) : IsProZero B := by
  intro n
  obtain ⟨s, hns, hs⟩ := hA n
  obtain ⟨t, hst, ht⟩ := hC s
  refine ⟨t, hns.trans hst, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hz : (g.app s).hom ((B.transition hst).hom x) = 0 := by
    rw [g.naturality_apply, ht]
    exact LinearMap.zero_apply _
  obtain ⟨y, hy⟩ := (hex s _).mp hz
  change (B.transition (hns.trans hst)).hom x = 0
  rw [← B.transition_apply hst hns x, ← hy, ← f.naturality_apply, hs]
  simp

/-- 概要：レベル単射の余核が pro-零なら、その射は pro 同型。
方針：核条件は単射性、余核条件は遷移の零化から得る。
規約：右の射の全射性は要求しない。使われ方：KST Lemma 4.10 の edge 射の比較。 -/
theorem proIso_of_injective_exact_proZero {A B C : Tower (ModuleCat.{u} R)}
    (f : LevelHom A B) (g : LevelHom B C)
    (hinj : ∀ n, Function.Injective (f.app n).hom)
    (hex : ∀ n, Function.Exact (f.app n).hom (g.app n).hom)
    (hC : IsProZero C) : IsProIso f := by
  apply isProIso_of_mono_epi
  · intro n
    refine ⟨n, le_refl n, fun x hx ↦ ?_⟩
    have hz : x = 0 := hinj n (hx.trans (map_zero _).symm)
    rw [hz, map_zero]
  · intro n
    obtain ⟨m, h, hz⟩ := hC n
    refine ⟨m, h, fun y ↦ ?_⟩
    apply (hex n _).mp
    rw [g.naturality_apply, hz]
    exact LinearMap.zero_apply _

/-- 概要：有限個の pro-零な商による拡張は pro-零。
方針：完全列の両端から中央の零化を帰納的に得る。
規約：商の同定や収束濾過は入力として具体的な射と完全性を指定する。
使われ方：KST Lemma 4.10 の有限収束後の濾過の組み立て。 -/
theorem proZero_finite_extension (A Q : ℕ → Tower (ModuleCat.{u} R))
    (f : ∀ j, LevelHom (A j) (A (j + 1)))
    (g : ∀ j, LevelHom (A (j + 1)) (Q j))
    (hex : ∀ j n, Function.Exact ((f j).app n).hom ((g j).app n).hom)
    (hA : IsProZero (A 0)) (k : ℕ) (hQ : ∀ j, j < k → IsProZero (Q j)) :
    IsProZero (A k) := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    exact proZero_of_exact (f k) (g k) (hex k)
      (ih (fun j hj ↦ hQ j (Nat.lt_succ_of_lt hj))) (hQ k (Nat.lt_succ_self k))

end SerrePositivity.KST.ProExcision

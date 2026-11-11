module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory の右 pinched 写像空間は Kan 複体。
方針：右ホーンの面を元の単体集合の内ホーンへ読み直し、A3b の Kan 判定を適用する。
規約：N レーンの pinchedHom 自体を扱い、Kan 性を別の構造に仮定しない。
使われ方：HTT Proposition 1.2.2.3、Kerodon Proposition 4.6.5.5（Tag 01L0）。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：全ての右ホーンを充填できる単体集合は Kan 複体。
方針：内ホーンの充填と、全ての辺の最後の外側ホーンの充填から A3b を適用する。
規約：右ホーンは次数一以上、添字は正。
使われ方：HTT Proposition 1.2.5.1 の (3)⇒(4)、写像空間の Kan 性。 -/
lemma kanComplex_of_rightHornFillers (X : SSet.{u})
    (hf : ∀ (n : ℕ) (i : Fin (n + 2)), 0 < i →
      ∀ σ : (horn (n + 1) i : SSet.{u}) ⟶ X,
        ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (horn (n + 1) i).ι ≫ F = σ) : KanComplex X := by
  have hQC : Quasicategory X :=
    ⟨fun {n i} σ h₀ _ ↦ by
      obtain ⟨F, hF⟩ := hf (n + 1) i h₀ σ
      exact ⟨F, hF.symm⟩⟩
  have hG : IsGroupoid (hoFunctor.obj X) := by
    constructor
    intro a b f
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y f
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers e
    intro n σ _
    exact hf (n + 1) (Fin.last (n + 2)) (by change 0 < n + 2; omega) σ
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_of_isGroupoid X

/-- 概要：面写像の最終点固定延長は同じ位置の面写像。
方針：最終点とそれ以外の点に分けて有限順序写像を計算する。
規約：元の面の添字 i は Fin(n+2)、延長後は i.castSucc。
使われ方：HTT Proposition 1.2.2.3 のホーンの次元を一つ増す計算。 -/
lemma pinchedExtend_δ {n : ℕ} (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ i) = SimplexCategory.δ i.castSucc := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro k
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom (SimplexCategory.δ i).toOrderHom k = i.castSucc.succAbove k
  refine Fin.lastCases ?_ (fun j ↦ ?_) k
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last]
    exact (Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i)).symm
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc]
    change (i.succAbove j).castSucc = i.castSucc.succAbove j.castSucc
    by_cases h : j.castSucc < i
    · rw [Fin.succAbove_of_castSucc_lt _ _ h,
        Fin.succAbove_of_castSucc_lt _ _ (show j.castSucc.castSucc < i.castSucc from h)]
    · have h' : i ≤ j.castSucc := le_of_not_gt h
      rw [Fin.succAbove_of_le_castSucc _ _ h',
        Fin.succAbove_of_le_castSucc _ _ (show i.castSucc ≤ j.castSucc.castSucc from h')]
      rfl

/-- 概要：右 pinched 写像空間の正の添字のホーンの面を充填できる。
方針：元の X で最終面を x に定数として加え、一つ高い次数の内ホーンを充填する。
規約：欠ける面の添字は i.castSucc で、0<i なら内点。
使われ方：HTT Proposition 1.2.2.3、Kerodon Proposition 4.6.5.5（Tag 01L0）。 -/
lemma pinchedHom_rightHornFilling {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌)
    (n : ℕ) (i : Fin (n + 2)) (hi : 0 < i)
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)
    (hf : horn.IsCompatible f) :
    ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y,
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ F = f j hj := by
  let fs : ∀ (j : Fin (n + 3)) (_ : j ≠ i.castSucc), (Δ[n + 1] : SSet.{u}) ⟶ X :=
    fun j ↦ Fin.lastCases (fun _ ↦ SSet.const x)
      (fun j hj ↦ SSet.yonedaEquiv.symm
        (SSet.yonedaEquiv (f j (fun h ↦ hj (congrArg Fin.castSucc h)))).val) j
  have hfs : horn.IsCompatible fs := by
    intro j k hj hk hjk
    induction k using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact False.elim ((lt_irrefl _) hjk)
      | cast j =>
        apply SSet.yonedaEquiv.injective
        have hpred : (Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hjk) = Fin.last (n + 1) := rfl
        have hcast : j.castSucc.castPred (Fin.ne_last_of_lt hjk) = j := rfl
        rw [hpred, hcast]
        dsimp only [fs]
        rw [Fin.lastCases_castSucc, Fin.lastCases_last,
          stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply,
          SSet.comp_const]
        change X.δ (Fin.last (n + 1))
          (SSet.yonedaEquiv (f j (fun h ↦ hj (congrArg Fin.castSucc h)))).val =
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n
        have hs := (SSet.yonedaEquiv (f j
          (fun h ↦ hj (congrArg Fin.castSucc h)))).source
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_eq_δ] at hs
        exact hs
    | cast k =>
      induction j using Fin.lastCases with
      | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) hjk)
      | cast j =>
        have hj' : j ≠ i := fun h ↦ hj (congrArg Fin.castSucc h)
        have hk' : k ≠ i := fun h ↦ hk (congrArg Fin.castSucc h)
        have hjk' : j < k := hjk
        cases n with
        | zero =>
          fin_cases i <;> fin_cases j <;> fin_cases k <;> first
            | exact (hj' rfl).elim
            | exact (hk' rfl).elim
            | exact False.elim ((show ¬ _ from by decide) hjk')
        | succ n =>
          have h := congrArg (fun F : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ↦
            (SSet.yonedaEquiv F).val) (hf.δ_pred_comp j k hj' hk' hjk')
          simp only [stdSimplex.yonedaEquiv_δ_comp] at h
          change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk')))).op
              (SSet.yonedaEquiv (f j hj')).val =
            X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk')))).op
              (SSet.yonedaEquiv (f k hk')).val at h
          rw [pinchedExtend_δ, pinchedExtend_δ] at h
          apply SSet.yonedaEquiv.injective
          have hpred : k.castSucc.pred (Fin.ne_zero_of_lt hjk) =
              (k.pred (Fin.ne_zero_of_lt hjk')).castSucc := by apply Fin.ext; rfl
          have hcast : j.castSucc.castPred (Fin.ne_last_of_lt hjk) =
              (j.castPred (Fin.ne_last_of_lt hjk')).castSucc := by apply Fin.ext; rfl
          rw [hpred, hcast]
          dsimp only [fs]
          rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc,
            stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
            SSet.yonedaEquiv.apply_symm_apply, SSet.yonedaEquiv.apply_symm_apply]
          exact h
  obtain ⟨σ, hσ⟩ := hfs.exists_desc
  have hi₀ : (0 : Fin (n + 3)) < i.castSucc := hi
  have hi₁ : i.castSucc < Fin.last (n + 2) := Fin.castSucc_lt_last i
  obtain ⟨F, hF⟩ := Quasicategory.hornFilling hi₀ hi₁ σ
  have hface (j : Fin (n + 3)) (hj : j ≠ i.castSucc) :
      stdSimplex.δ j ≫ F = fs j hj := by
    rw [← horn.ι_ι_assoc i.castSucc j hj, ← hF]
    exact hσ j hj
  have hFcast (j : Fin (n + 2)) (hj : j ≠ i) :
      stdSimplex.δ j.castSucc ≫ F = SSet.yonedaEquiv.symm
        (SSet.yonedaEquiv (f j hj)).val := by
    simpa only [fs, Fin.lastCases_castSucc] using
      hface j.castSucc (fun h ↦ hj (Fin.castSucc_injective _ h))
  have hFlast : stdSimplex.δ (Fin.last (n + 2)) ≫ F = SSet.const x := by
    simpa only [fs, Fin.lastCases_last] using
      hface (Fin.last (n + 2)) (Fin.castSucc_ne_last i).symm
  let s := SSet.yonedaEquiv F
  have hlast : X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front (n + 1)).op s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x (n + 1) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_eq_δ]
    change X.δ (Fin.last (n + 2)) (SSet.yonedaEquiv F) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, hFlast]
    rfl
  have htgt : X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex (n + 1)).op s = y := by
    have hzero : (0 : Fin (n + 2)) ≠ i := ne_of_lt hi
    have hfront : X.δ (0 : Fin (n + 3)) s =
        (SSet.yonedaEquiv (f 0 hzero)).val := by
      have h0 : stdSimplex.δ (0 : Fin (n + 3)) ≫ F =
          SSet.yonedaEquiv.symm (SSet.yonedaEquiv (f 0 hzero)).val := by
        simpa only [Fin.castSucc_zero] using hFcast 0 hzero
      rw [← stdSimplex.yonedaEquiv_δ_comp, h0]
      exact SSet.yonedaEquiv.apply_symm_apply _
    have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex_extend (SimplexCategory.δ (0 : Fin (n + 2)))
    rw [pinchedExtend_δ] at hl
    rw [← hl, op_comp, CategoryTheory.Functor.map_comp_apply]
    change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op (X.δ 0 s) = y
    rw [hfront]
    exact (SSet.yonedaEquiv (f 0 hzero)).target
  let t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋n + 1⦌ := ⟨s, hlast, htgt⟩
  refine ⟨SSet.yonedaEquiv.symm t, ?_⟩
  intro j hj
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ j)).op s =
    (SSet.yonedaEquiv (f j hj)).val
  rw [pinchedExtend_δ]
  change X.δ j.castSucc (SSet.yonedaEquiv F) = _
  rw [← stdSimplex.yonedaEquiv_δ_comp, hFcast j hj]
  exact SSet.yonedaEquiv.apply_symm_apply _

/-- 概要：quasicategory の右 pinched 写像空間は Kan 複体。
方針：正の添字の全ホーンを充填し、A3b の Kan 判定を適用する。
規約：前提は X の quasicategory 性だけ。
使われ方：HTT Proposition 1.2.2.3、Kerodon Proposition 4.6.5.5（Tag 01L0）。 -/
@[kerodon 01JC, kerodon 01L0]
instance pinchedHom_kanComplex {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) := by
  apply kanComplex_of_rightHornFillers
  intro n i hi σ
  obtain ⟨F, hF⟩ := pinchedHom_rightHornFilling x y n i hi
    (fun j hj ↦ horn.ι i j hj ≫ σ) (horn.IsCompatible.of_hom σ)
  exact ⟨F, horn.hom_ext' hF⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
